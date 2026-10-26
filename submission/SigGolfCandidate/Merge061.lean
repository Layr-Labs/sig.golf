import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge049
import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge060

-- ==== merged from T3M_Expand_Layer ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (NODE NOUT)
theorem bc_remaining {s : MachineState} {hh j : Nat} (hj : j < hh) (hh' : hh ≤ 12)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    BCBlocks.remaining s = BitVec.ofNat 64 (hh - j - 1) := by
  unfold BCBlocks.remaining
  rw [h15, h20, BitVec.ofNat_sub_ofNat_of_le hh j (by omega) (by omega)]
  change BitVec.ofNat 64 (hh - j) - BitVec.ofNat 64 1 = _
  exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chain chainInput shortHash pad64 zero16 header chainCount height
  width maxDigit route recoverLayer leafHash nodeHash)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
set_option autoImplicit false
theorem chainCount_ne0 : ∀ l : Layer, l ≠ 0 → chainCount l = 43 := by decide
theorem chainCount_cases' (lay : Layer) : chainCount lay = 51 ∨ chainCount lay = 43 := by
  fin_cases lay <;> simp [chainCount]

theorem height_le (lay : Layer) : height lay ≤ 12 := by
  fin_cases lay <;> simp [height]
theorem csN4_le (lay : Layer) : csN4 lay ≤ chainCount lay := by
  unfold csN4; split_ifs with h
  · subst h; simp [chainCount]
  · omega
theorem endpoint_eq (lay : Layer) (i : Nat) : maxDigit lay i = endpoint lay i (csN4 lay) := by
  unfold maxDigit endpoint
  split_ifs <;> rfl

/-- T51: the top leaf is `end_0 | tweak | end_1 .. end_50` (endpad), the same shape as a lower leaf. -/
theorem leafInput_words' (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length = chainCount lay) :
    wordsOf (pad64 (T3.leafInput lay tree leaf ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++ [T3.hyperWord lay.val (tree * 2 ^ height lay + leaf), 0] ++
        wordsOf ((ends.drop 1).flatMap (bytesLE 16)) := by
  unfold T3.leafInput T3.leafTweak
  rw [ite_self]
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (chainCount lay - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen, Nat.mul_comm]
  have hal : (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (0#64 ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) ++
      (ends.drop 1).flatMap (bytesLE 16)).length % 64 = 0 := by
    simp only [List.length_append, bytesLE_length, hfl]
    rcases chainCount_cases' lay with h | h <;> rw [h]
  rw [pad64_of_aligned _ hal,
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length] <;> omega),
    wordsOf_append _ _ (by simp only [bytesLE_length] <;> omega), wordsOf_bytesLE16 (_ ++ _),
    T3.append64_low, BitVec.extractLsb'_append_eq_left]
  rfl

def leafBlocks' (lay : Layer) : Nat := (16 * (chainCount lay + 1) + 63) / 64
theorem leafInput_length' (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length = chainCount lay) :
    (pad64 (T3.leafInput lay tree leaf ends)).length = 64 * leafBlocks' lay := by
  unfold T3.leafInput leafBlocks'
  rw [ite_self]
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (chainCount lay - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen, Nat.mul_comm]
  rw [pad64_length]
  simp only [List.length_append, bytesLE_length, hfl]
  rcases chainCount_cases' lay with h | h <;> rw [h]

theorem leafBlocks'_cases (lay : Layer) : leafBlocks' lay = 13 ∧ chainCount lay = 51 ∨
    leafBlocks' lay = 11 ∧ chainCount lay = 43 := by
  unfold leafBlocks'; rcases chainCount_cases' lay with h | h <;> rw [h] <;> simp
def sideOff (leaf j : Nat) : Nat := if leaf / 2 ^ j % 2 = 1 then 0 else 48
def RlScratch (A : Nat) : Prop :=
  A = CHAIN + 16 ∨ A = CHAIN + 24 ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112) ∨ (LEAFPK ≤ A ∧ A < LEAFPK + 896) ∨
  A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
  (NOUT ≤ A ∧ A < NOUT + 32) ∨ A = ENC ∨ A = ENC + 8 ∨ (0x66700 ≤ A ∧ A < 0x66760) ∨
  (0xA0000 ≤ A ∧ A < 0xA0768)
def RlWit (lay : Layer) (leaf WC WM : Nat) (A : Nat) : Prop :=
  (∃ i < chainCount lay, A = WC - 64 * i + 48 ∨ A = WC - 64 * i + 56) ∨
  (∃ j < height lay, A = WM - 64 * j + sideOff leaf j ∨ A = WM - 64 * j + sideOff leaf j + 8)
def rlRegs : List Reg :=
  [.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x28, .x29, .x30, .x31]
structure RlPre (s : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (P WC WM ret : Nat) : Prop where
  pc : s.pc = pcOf 997
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 (route index lay).2
  x18 : s.getReg .x18 = BitVec.ofNat 64 (route index lay).1
  x15 : s.getReg .x15 = BitVec.ofNat 64 (height lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 lay)
  x16 : s.getReg .x16 = BitVec.ofNat 64 P
  x23 : s.getReg .x23 = BitVec.ofNat 64 WC
  x24 : s.getReg .x24 = BitVec.ofNat 64 WM
  hidx : index < 2 ^ 31
  hP : 0x7000 ≤ P
  hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616
  hP8 : P % 8 = 0
  hWC8 : WC % 8 = 0
  hWM8 : WM % 8 = 0
  hWM : 0x800 + 64 * (height lay - 1) ≤ WM
  hWMC : WM + 64 + 64 * (chainCount lay - 1) ≤ WC
  hWC : WC + 64 ≤ 0x7000
  dbytes : ∀ i < chainCount lay, s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (digits.getD i 0)
  hdig : ∀ i < chainCount lay, digits.getD i 0 ≤ maxDigit lay i
  vals : ∀ i (h : i < chainCount lay), DigAt s (P + 16 * i) ((sig.layers lay).values ⟨i, h⟩)
  path : ∀ j (h : j < height lay), DigAt s (P + 16 * chainCount lay + 16 * j) ((sig.layers lay).path ⟨j, h⟩)
  c0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  c8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  n32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
theorem route_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ height lay := by
  unfold route; exact Nat.mod_lt _ (by positivity)
theorem route_routed (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  unfold route
  dsimp only
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.div_add_mod']
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
theorem route_tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  unfold route
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
def lval (sig : Signature) (lay : Layer) (i : Nat) : Digest :=
  if h : i < chainCount lay then (sig.layers lay).values ⟨i, h⟩ else 0
def lpath (sig : Signature) (lay : Layer) (j : Nat) : Digest :=
  if h : j < height lay then (sig.layers lay).path ⟨j, h⟩ else 0
theorem slotOff_lt (lay : Layer) {i n : Nat} (hi : i < n) : slotOff lay i + 16 ≤ 16 * (n + 2) := by
  unfold slotOff; split_ifs <;> omega
theorem slotOff_ne (lay : Layer) {i j : Nat} (h : i ≠ j) :
    slotOff lay i + 16 ≤ slotOff lay j ∨ slotOff lay j + 16 ≤ slotOff lay i := by
  unfold slotOff; split_ifs <;> omega
section phase
variable {sk : BitVec 256}
/-- C2 (FULL) + C4: offset of the current value in the 32-byte node output at level `j`: the high half when the
current node is a left child below the root (every layer; C4 adds the top), the low half for a right child and for
the root (`j = height lay`, heap 1). -/
def curOff (lay : Layer) (leaf j : Nat) : Nat :=
  if ClaudeWCT.WCT9.lowerHigh lay.val (leaf / 2 ^ j) && decide (j < height lay) then 16 else 0
theorem curOff_le (lay : Layer) (leaf j : Nat) : curOff lay leaf j ≤ 16 := by unfold curOff; split_ifs <;> omega
theorem curOff_bit0 (lay : Layer) {leaf j : Nat} (h : leaf / 2 ^ j % 2 = 0) (hj : j < height lay) :
    curOff lay leaf j = hiOff lay.val := by
  have hl := lay.isLt
  unfold curOff hiOff ClaudeWCT.WCT9.lowerHigh
  simp [h, hj, hl]
theorem curOff_bit1 (lay : Layer) {leaf j : Nat} (h : ¬ leaf / 2 ^ j % 2 = 0) : curOff lay leaf j = 0 := by
  unfold curOff ClaudeWCT.WCT9.lowerHigh; simp [h]
/-- C4: the root (level `height lay`) keeps the low half. -/
theorem curOff_root (lay : Layer) (leaf : Nat) : curOff lay leaf (height lay) = 0 := by
  unfold curOff; simp
theorem height_pos' (lay : Layer) : 0 < height lay := by fin_cases lay <;> decide
theorem curOff_zero (lay : Layer) (leaf : Nat) :
    curOff lay leaf 0 = if ClaudeWCT.WCT9.lowerHigh lay.val leaf then 16 else 0 := by
  unfold curOff; rw [Nat.pow_zero, Nat.div_one]; simp [height_pos' lay]
theorem digAt_half (t : MachineState) (a : BitVec 256) (B : Nat) (h12 : t.getReg .x12 = BitVec.ofNat 64 B)
    (hB : B + 32 < 2 ^ 64) (b : Bool) :
    DigAt (writeHash t a) (B + if b then 16 else 0) (ClaudeWCT.WCT9.halfOf b a) := by
  cases b
  · simpa using DigAt.writeHash_lo t a B h12 hB
  · simpa using DigAt.writeHash_hi t a B h12 hB
theorem block4_length (l r : Digest) (T : BitVec 128) : (bytesLE 16 l ++ bytesLE 16 T ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem wordsOf_block4 (l r : Digest) (T : BitVec 128) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 T ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, T.extractLsb' 0 64, T.extractLsb' 64 64, 0, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
    wordsOf_bytesLE16]
  rfl
def mkRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x17, .x20, .x22, .x24, .x28, .x29, .x30, .x31]
def MkW (leaf WM j : Nat) (A : Nat) : Prop :=
  A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
  (NOUT ≤ A ∧ A < NOUT + 32) ∨ (∃ j' < j, A = WM - 64 * j' + sideOff leaf j' ∨ A = WM - 64 * j' + sideOff leaf j' + 8) ∨
  (0x66700 ≤ A ∧ A < 0x66760)
structure MkInv (tc : MachineState) (sig : Signature) (lay : Layer) (leaf P WM j : Nat) (value : Digest)
    (u : MachineState) : Prop where
  pc : u.pc = pcOf 1076
  x20 : u.getReg .x20 = BitVec.ofNat 64 j
  x22 : u.getReg .x22 = BitVec.ofNat 64 (P + 16 * chainCount lay + 16 * j)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (WM - 64 * j)
  hj : j ≤ height lay
  val : DigAt u (NOUT + curOff lay leaf j) value
  wit : ∀ j' < j, DigAt u (WM - 64 * j' + sideOff leaf j') (lpath sig lay j')
  regs : RegsExcept tc u mkRegs
  frame : Frame tc u (MkW leaf WM j)
theorem sideOff_le (leaf j : Nat) : sideOff leaf j ≤ 48 := by unfold sideOff; split_ifs <;> omega
theorem not_MkW_of {leaf WM j A : Nat} (hA1 : WM + 64 ≤ A) (hA2 : A < NODE ∨ NODE + 64 ≤ A)
    (hA3 : A < NOUT ∨ NOUT + 32 ≤ A) (hA4 : A < 0x66700 := by omega) : ¬ MkW leaf WM j A := by
  unfold MkW
  rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
    first | (simp only [NODE, NOUT] at h hA2 hA3; omega) | (have := sideOff_le leaf j'; omega) | omega
theorem mkW_of {leaf WM j A : Nat} (h : A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨
    A = NODE + 56 ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ (0x66700 ≤ A ∧ A < 0x66760)) : MkW leaf WM j A := by
  unfold MkW
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
theorem mkW_wit {leaf WM j j' A : Nat} (hj : j' < j)
    (h : A = WM - 64 * j' + sideOff leaf j' ∨ A = WM - 64 * j' + sideOff leaf j' + 8) : MkW leaf WM j A := by
  unfold MkW
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j', hj, h⟩)))))))
theorem frame_readWordsL {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWordsL h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
/-- img-v6 (topfold-v6): cycles of one top node below the root at level `j` (height `j + 1`): the node step with
the nonce search, at most `topNonceCap (j + 1) - 1` failed trials of 22 cycles each. -/
def topNodeW (j : Nat) : Nat := 123 + 22 * (T3.topNonceCap (j + 1) - 1)
/-- Cycles of the node climb (img-v6: the hook 1139 adds 4 (lower) / 6 (top root) cycles per plain node, 81 total;
the 11 top nodes below the root take `topNodeW`). -/
def climbW (lay : Layer) : Nat :=
  if lay = 0 then ((List.range' 0 11).map topNodeW).sum + 81 else height lay * 81
def rlCost (lay : Layer) : Nat := hpK lay + chainCount lay * 461 + 10 + 8 * leafBlocks' lay + 13 + climbW lay
/-- The top layer's 11 node nonces at `0x66700 + 8 k` and the leaf at `0x66758` (read by the pad writer). -/
def NoncesAt (t : MachineState) (nonces : List Nat) (leaf : Nat) : Prop :=
  nonces.length = 11 ∧ (∀ k < 11, t.getMem (BitVec.ofNat 64 (0x66700 + 8 * k)) = BitVec.ofNat 64 (nonces.getD k 0)) ∧
    t.getMem (BitVec.ofNat 64 0x66758) = BitVec.ofNat 64 leaf
def RlPost (s0 : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat) (root : Digest)
    (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t ENC root ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval sig lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath sig lay j)) ∧
    RegsExcept s0 t rlRegs ∧ Frame s0 t (fun A => RlScratch A ∨ RlWit lay (route index lay).1 WC WM A)
/-- img-v6: one step of the top path with the node nonce search (`WCT9.topStepN`). -/
def topStepP (sig : Signature) (index : Nat) (lay : Layer) (acc : Digest × List Nat) (j : Fin (height lay)) :
    T3.M (Digest × List Nat) := do
  let other := (sig.layers lay).path j
  let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (acc.1, other) else (other, acc.1)
  let found ← T3.topNodeAt (j.val + 1) (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
    pair.1 pair.2
  pure (found.2, acc.2 ++ [found.1])
/-- The fold invariant of the top path with nonces: `MkInv` plus the nonces recorded so far. -/
def TopInv (tc : MachineState) (sig : Signature) (lay : Layer) (leaf P WM : Nat) (j : Nat) (acc : Digest × List Nat)
    (w : MachineState) : Prop :=
  MkInv tc sig lay leaf P WM j acc.1 w ∧ acc.2.length = j ∧
    (∀ k < j, w.getMem (BitVec.ofNat 64 (0x66700 + 8 * k)) = BitVec.ofNat 64 (acc.2.getD k 0)) ∧
    (0 < j → w.getMem (BitVec.ofNat 64 0x66758) = BitVec.ofNat 64 leaf)
/-- img-v6: the top layer's recovery (`WCT9.topFoldN` then the root node): `((v, nonces), root)`. -/
def topProg (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) (h11 : 11 < height lay) :
    T3.M ((Digest × List Nat) × Digest) :=
  ((List.finRange (chainCount lay)).mapM fun i => SigGolfCandidate.T3.layChain lay (route index lay).2
      (route index lay).1 i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      ((sig.layers lay).values i)) >>= fun ends =>
    SigGolfCandidate.T3.leafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
    ((List.finRange (height lay)).take 11).foldlM (topStepP sig index lay) (value, []) >>= fun vn =>
    (let other := (sig.layers lay).path ⟨11, h11⟩
     let pair := if (route index lay).1 / 2 ^ 11 % 2 = 0 then (vn.1, other) else (other, vn.1)
     SigGolfCandidate.T3.nodeHash 3 lay.val (route index lay).2
       (2 ^ (height lay - 11 - 1) + (route index lay).1 / 2 ^ (11 + 1)) pair.1 pair.2) >>= fun root =>
    pure (vn, root)
/-- The top layer's last hashed block: level-11 node `v` and the stored top sibling. -/
def TopBlkG (sig : Signature) (index : Nat) (lay : Layer) (v : Digest) (t : MachineState) : Prop :=
  t.readWords (BitVec.ofNat 64 NODE) 8 =
    wordsOf (bytesLE 16 (if (route index lay).1 / 2 ^ 11 % 2 = 0 then v else lpath sig lay 11) ++
      bytesLE 16 (T3.nodeTweak 3 lay.val (route index lay).2 (2 ^ (height lay - 11 - 1) + (route index lay).1 / 2 ^ (11 + 1))) ++
      zero16 ++ bytesLE 16 (if (route index lay).1 / 2 ^ 11 % 2 = 0 then lpath sig lay 11 else v))
end phase
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
theorem rl1117_continue (s : MachineState) (hpc : s.pc = pcOf 1117)
    (lay tree leaf hh j : Nat) (hlay : lay < 4) (htree : tree < 2 ^ 32)
    (hl : leaf < 2 ^ 32) (hj : j < hh) (hh' : hh ≤ 12) (hc : j + 1 < hh ∨ lay = 0)
    (htopl : lay = 0 → leaf < 2 ^ hh)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t k, Steps im s k k t ∧ k ≤ 37 ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 64 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  have he := bc_remaining hj hh' h15 h20
  have hcont : BCBlocks.remaining s ≠ 0 ∨ s.getReg .x8 = 0 := by
    rcases hc with hc | hc
    · left
      rw [he]
      intro hz
      have := congrArg BitVec.toNat hz
      change (hh - j - 1) % 2 ^ 64 = 0 at this
      rw [Nat.mod_eq_of_lt (show hh - j - 1 < 2 ^ 64 by omega)] at this
      omega
    · right; rw [h8, hc]; rfl
  obtain ⟨u, k, su, hk, up, u28, ur, uf⟩ := BCBlocks.continue_spec (im := im) s hpc hcont
  obtain ⟨t, ut, tp, m16, m24, t10, t11, t12, tr, tf⟩ := rl1119_spec (im := im) u up lay tree leaf hh j
    hlay htree hl hj hh' htopl
    (by rw [ur.get (by decide)]; exact h8) (by rw [ur.get (by decide)]; exact h9)
    (by rw [ur.get (by decide)]; exact h18) (by rw [ur.get (by decide)]; exact h15)
    (by rw [ur.get (by decide)]; exact h20) (u28.trans he)
  refine ⟨t, k + hdrK lay, su.trans ut, by unfold hdrK; split_ifs <;> omega, tp, m16, m24, t10, t11, t12, ?_, ?_⟩
  · exact (ur.trans tr).mono (by decide)
  · exact (uf.trans tf).mono (by intro A hA h; simpa using h)

theorem rl_chains {s0 t1 : MachineState} {sig : Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 sig index lay digits P WC WM ret)
    (r1 : RegsExcept s0 t1 [.x6, .x7, .x19, .x28, .x30])
    (f1 : Frame s0 t1 (fun A => A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24))
    (hI0 : ChainsInv t1 lay (route index lay).2 (route index lay).1 P WC (chainCount lay) (csN4 lay)
      (lval sig lay) [] t1) :
    TBSim im sk t1 (chainCount lay * 461)
      ((List.finRange (chainCount lay)).mapM fun i => ClaudeWCT.WCT9.chainW lay (route index lay).2 (route index lay).1 i.val
        (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i))
      (fun ends u => ends.length = chainCount lay ∧ ChainsInv t1 lay (route index lay).2 (route index lay).1 P WC
        (chainCount lay) (csN4 lay) (lval sig lay) ends u) := by
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hpre.hidx
  have hN := chainCount_cases' lay
  have hH := height_le lay
  have hPb := hpre.hP'
  have hWC := hpre.hWC
  have hWMC := hpre.hWMC
  have hWM := hpre.hWM
  have hP0 := hpre.hP
  refine tb_mapM_finRange (chainCount lay) _ 461 _ (fun i pre t hlen hI => ?_) hI0
  have hi := i.isLt
  have hfr : Frame s0 t (fun A => (A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨ ChW lay WC pre.length A) :=
    f1.trans hI.frame
  have g : ∀ r, r ∉ oneRegs → r ∉ [Reg.x6, .x7, .x19, .x28, .x30] → t.getReg r = s0.getReg r :=
    fun r h1 h2 => by rw [hI.regs.get h1, r1.get h2]
  have h26 : t.getReg .x26 = BitVec.ofNat 64 (chainCount lay) := by
    rw [g _ (by decide) (by decide), hpre.x26]
  have h27 : t.getReg .x27 = BitVec.ofNat 64 (csN4 lay) := by rw [g _ (by decide) (by decide), hpre.x27]
  have h16 : t.getReg .x16 = BitVec.ofNat 64 P := by rw [g _ (by decide) (by decide), hpre.x16]
  have h23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * i.val) := by rw [hI.x23, hlen]
  have hv : DigAt t (P + 16 * i.val) ((sig.layers lay).values i) :=
    (hpre.vals i.val hi).frame hfr (by omega)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK] at h; omega
          · exact not_ChW_of (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega) h)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK] at h; omega
          · exact not_ChW_of (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega) h)
  have hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i.val)) = BitVec.ofNat 8 (digits.getD i.val 0) := by
    rw [Frame.getByte hfr (by simp only [DIGITS]; omega)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK, DIGITS] at h; omega
          · exact not_ChW_of (by omega) (by simp only [DIGITS]; omega) (by simp only [CHAIN, DIGITS]; omega)
              (by simp only [LEAFPK, DIGITS]; omega) h)]
    exact hpre.dbytes i.val hi
  have hd : digits.getD i.val 0 ≤ endpoint lay i.val (csN4 lay) := by
    have := hpre.hdig i.val hi; rwa [endpoint_eq] at this
  have hc : ChainCtx lay.val tree leaf i.val t := hlen ▸ hI.ctx
  have hone := rl_one (im := im) (sk := sk) lay tree leaf i.val (digits.getD i.val 0) P (WC - 64 * i.val) (chainCount lay)
    (csN4 lay) (by
      have hidx := hpre.hidx
      dsimp [tree, leaf]
      fin_cases lay <;> norm_num [route, height] at * <;> omega)
    (route_lt index lay) hi (by omega) (fun hl => by subst hl; simp [chainCount] at hi; omega) (csN4_le lay) hpre.hP (by omega) hpre.hP8
    (by have := hpre.hWC8; omega) (by omega) (by omega) hd (le_of_eq (endpoint_eq lay i.val).symm)
    ((sig.layers lay).values i) t hI.pc hc h26 h27 h16 h23 hv
    hdig
  rw [endpoint_eq]
  refine hone.mono le_rfl (fun d u hu => ?_)
  obtain ⟨upc, u19, u23, uc, uslot, uval, ur, uf⟩ := hu
  have hl1 : (pre ++ [d]).length = i.val + 1 := by simp [hlen]
  refine ⟨upc, hl1 ▸ uc, ?_, ?_, ?_, (hI.regs.trans ur).mono (fun r hr => by
    rcases List.mem_append.mp hr with h | h <;> exact h), (hI.frame.trans uf).mono (fun A _ h => ?_)⟩
  · rw [u23, hl1, Nat.mul_succ, Nat.sub_sub]
  · intro j hj
    rw [hl1] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hs := hI.slots j (by omega)
      rw [List.getD_append _ _ _ _ (by omega)]
      have hne := slotOff_ne lay (show j ≠ i.val by omega)
      have hlt := slotOff_lt lay (show j < chainCount lay by omega)
      exact hs.frame uf (by simp only [LEAFPK]; omega)
        (by unfold OneW StepW; simp only [LEAFPK, CHAIN]; omega)
        (by unfold OneW StepW; simp only [LEAFPK, CHAIN]; omega)
    · rw [List.getD_append_right _ _ _ _ (by omega), show i.val - pre.length = 0 by omega]
      simpa using uslot
  · intro j hj
    rw [hl1] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hw := hI.wvals j (by omega)
      exact hw.frame uf (by omega) (by unfold OneW StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega)
        (by unfold OneW StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega)
    · have : lval sig lay i.val = (sig.layers lay).values i := by unfold lval; rw [dif_pos hi]
      rw [this]
      exact uval
  · rw [hl1]
    unfold ChW
    rcases h with h | h
    · rw [hlen] at h
      rcases h with h | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨c, by omega, h⟩)
      · exact Or.inr (Or.inr ⟨c, by omega, h⟩)
    · unfold OneW at h
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨i.val, by omega, Or.inl h⟩)
      · exact Or.inr (Or.inl ⟨i.val, by omega, Or.inr h⟩)
      · exact Or.inr (Or.inr ⟨i.val, by omega, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨i.val, by omega, Or.inr h⟩)
/-- C2 (FULL): offset of the current value in the 32-byte node output at level `j` (high half for lower layers when
the current node is a left child). -/

theorem rl_mk_step {tc : MachineState} {sig : Signature} {lay : Layer} {tree leaf P WM j : Nat}
    {value : Digest} {u : MachineState} (hj : j < height lay) (hc : j + 1 < height lay ∨ lay = 0) (htree : tree < 2 ^ 32) (hleaf : leaf < 2 ^ height lay)
    (hP0 : 0x7000 ≤ P) (hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hWM8 : WM % 8 = 0) (hWM : 0x800 + 64 * (height lay - 1) ≤ WM) (hWM' : WM + 64 ≤ 0x7000)
    (c5 : tc.getReg .x5 = 0) (c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val)
    (c9 : tc.getReg .x9 = BitVec.ofNat 64 tree) (c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf)
    (c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay))
    (cpath : DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j))
    (cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0) (cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (hI : MkInv tc sig lay leaf P WM j value u) (hskip : lay ≠ 0 ∨ 11 ≤ j) :
    TBSim im sk u 81 (let other := (sig.layers lay).path ⟨j, hj⟩
        let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
        ClaudeWCT.WCT9.lowerNodeHash lay.val tree (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2)
      (fun v' u' => MkInv tc sig lay leaf P WM (j + 1) v' u' ∧
        u'.readWords (BitVec.ofNat 64 NODE) 8 =
          wordsOf (bytesLE 16 (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ++
            bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1))) ++
            zero16 ++ bytesLE 16 (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value)) ∧
        (∀ A, 0x66700 ≤ A → A < 0x66760 → u'.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A))) := by
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
  obtain ⟨t4, k4, s4, hk4, p4, h16, h24', h10, h11, h12, r4, f4⟩ := rl1117_continue (im := im) t3 p3 lay.val tree leaf (height lay) j
    (by omega) htree (by omega) hj hH (by simpa using hc) (fun _ => hleaf)
    (by rw [g3 _ (by decide)]; exact c8) (by rw [g3 _ (by decide)]; exact c9)
    (by rw [g3 _ (by decide)]; exact c18) (by rw [g3 _ (by decide)]; exact c15)
    (by rw [r3.get (by decide), ru2.get (by decide)]; exact hI.x20)
  set heap := 2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 32 := by
    have : 2 ^ (height lay - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : leaf / 2 ^ (j + 1) ≤ leaf := Nat.div_le_self _ _
    omega
  set L := if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j with hL
  set R := if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value with hR
  have f34 : ∀ A, A < 2 ^ 64 → A ≠ NODE + 16 → A ≠ NODE + 24 → t4.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => f4.get hA (by rintro (h | h) <;> contradiction)
  have hblk4 : t4.readWords (BitVec.ofNat 64 NODE) 8 =
      wordsOf (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++ zero16 ++ bytesLE 16 R) := by
    rw [wordsOf_block4, readWords_eight, f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), h16, h24',
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), nl.1, nl.2,
      show NODE + 48 + 8 = NODE + 56 from rfl, nr.1, nr.2,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn32,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn40]
  have hq : hashInput t4 = toQ (pad64 (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++
      zero16 ++ bytesLE 16 R)) := by
    rw [pad64_of_aligned _ (by rw [block4_length])]
    exact hashInput_toQ t4 _ 0 NODE (block4_length _ _ _) h10 (by decide) (by decide) h11 (by decide) hblk4
  have hv : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NODE 64 NOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r34 : RegsExcept t2 t4 ([.x6, .x7, .x29, .x30] ++ [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30]) := r3.trans r4
  have h5 : t4.getReg .x5 = 0 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c5
  have hprog : (let other := (sig.layers lay).path ⟨j, hj⟩
      let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
      ClaudeWCT.WCT9.lowerNodeHash lay.val tree (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2) =
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.lowerHigh lay.val heap)
        (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++ zero16 ++ bytesLE 16 R) >>= pure) := by
    have e : (sig.layers lay).path ⟨j, hj⟩ = lpath sig lay j := by unfold lpath; rw [dif_pos hj]
    rw [bind_pure, e]
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · simp only [hL, hR, hb, ↓reduceIte, hheap]; rfl
    · simp only [hL, hR, hb, ↓reduceIte, hheap]; rfl
  rw [hprog]
  refine (TBSim.steps (s1.trans (s2.trans (s3.trans s4))) (tb_halfHash_bind' (im := im) (W := 10) _ (fetch_1138 (im := im) t4 p4) h5 hv hq
    (fun a => ?_))).mono ?_ (fun _ _ h => h)
  rotate_left
  · rw [pad64_of_aligned _ (by rw [block4_length]), blocks_toQ ⟨by rw [block4_length]; omega,
      by rw [block4_length]⟩, block4_length]; omega
  have p5 : (writeHash t4 a).pc = pcOf 1139 := by rw [pc_writeHash, p4, pcOf_add4]
  have hskip' : height lay ≠ 12 ∨ 11 ≤ j := by
    rcases hskip with h | h
    · left; intro he; apply h; fin_cases lay <;> simp_all [height]
    · right; exact h
  obtain ⟨t6, k6, s6, hk6, p6, x22', x24', x20', r6, f6⟩ := skip_spec (im := im) (writeHash t4 a) p5 (height lay) j P' M
    (by omega) (by omega) (by omega) (by omega) hskip'
    (by rw [getReg_writeHash, r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c15)
    (by rw [getReg_writeHash, r34.get (by decide), ru2.get (by decide)]; exact hI.x20)
    (by rw [getReg_writeHash, r34.get (by decide)]; exact h22) (by rw [getReg_writeHash, r34.get (by decide)]; exact h24)
  have fw := Frame.writeHash t4 a NOUT h12 (by decide)
  have hd := digAt_half t4 a NOUT h12 (by decide) (ClaudeWCT.WCT9.lowerHigh lay.val heap)
  have hoff : (NOUT + if ClaudeWCT.WCT9.lowerHigh lay.val heap then 16 else 0) = NOUT + curOff lay leaf (j + 1) := by
    by_cases hlt : j + 1 < height lay
    · have hhi : ClaudeWCT.WCT9.lowerHigh lay.val heap = ClaudeWCT.WCT9.lowerHigh lay.val (leaf / 2 ^ (j + 1)) := by
        rw [hheap]; exact ClaudeWCT.WCT9.lowerHigh_heap (by omega)
      unfold curOff; rw [hhi]; simp [hlt]
    · have he : j + 1 = height lay := by omega
      have h1 : heap = 1 := by
        rw [hheap, show height lay - j - 1 = 0 by omega, Nat.pow_zero, he,
          Nat.div_eq_of_lt hleaf]
      rw [h1, ClaudeWCT.WCT9.lowerHigh_one, he, curOff_root]
      rfl
  have f36 : Frame t3 t6 (fun A => (A = NODE + 16 ∨ A = NODE + 24) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) :=
    ((f4.trans fw).trans f6).mono (fun A _ h => by rcases h with (h | h) | h; exact Or.inl h; exact Or.inr h; exact h.elim)
  have f46 : Frame t4 t6 (fun A => (NOUT ≤ A ∧ A < NOUT + 32) ∨ False) := fw.trans f6
  refine (TBSim.steps s6 (TBSim.pure ⟨⟨p6, x20', by rw [x22']; congr 1, by rw [x24', hMdef, Nat.mul_succ, Nat.sub_sub],
    by omega, by rw [← hoff]; exact hd.frame f6 (by split_ifs <;> decide) (by simp) (by simp), ?_, ?_, ?_⟩, ?_, ?_⟩)).mono
    (by omega) (fun _ _ h => h)
  · intro j' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
    · have hw := hI.wit j' hj'
      have hs1 := sideOff_le leaf j'
      have hs2 := sideOff_le leaf j
      have hne : WM - 64 * j' + sideOff leaf j' + 16 ≤ M + sideOff leaf j ∨ M + 64 ≤ WM - 64 * j' + sideOff leaf j' := by
        unfold sideOff at hs1 hs2 ⊢; split_ifs <;> omega
      refine ((hw.frame fu2 (by omega) (by simp) (by simp)).frame f3 (by omega) ?_ ?_).frame f36 (by omega) ?_ ?_
      · simp only [NODE]; omega
      · simp only [NODE]; omega
      · simp only [NODE, NOUT]; omega
      · simp only [NODE, NOUT]; omega
    · have hs2 := sideOff_le leaf j'
      exact wsib.frame f36 (by omega) (by simp only [NODE, NOUT]; omega) (by simp only [NODE, NOUT]; omega)
  · have rw0 : RegsExcept t4 (writeHash t4 a) [] := fun r _ => getReg_writeHash t4 a r
    exact (((g3'.trans r4).trans rw0).trans r6).mono (by decide)
  · have fall := ((hI.frame.trans fu2).trans f3).trans f36
    refine fall.mono (fun A _ h => ?_)
    unfold MkW at h ⊢
    rcases h with ((h | h) | h) | h
    · rcases h with h | h | h | h | h | h | h | ⟨j', hj', h⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j', by omega, h⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · exact h.elim
    · rcases h with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, by omega, Or.inl h⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, by omega, Or.inr h⟩)))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · rcases h with (h | h) | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · rw [frame_readWordsL f46 NODE 8 (by decide) (fun i hi h => by
      rcases h with h | h
      · simp only [NODE, NOUT] at h; omega
      · exact h)]
    simpa only [hL, hR, hheap] using hblk4
  · intro A hA1 hA2
    have fu6 := ((fu2.trans f3).trans f4).trans f46
    rw [fu6.get (by omega) (by
      have := sideOff_le leaf j
      have hMb : M ≤ WM := by rw [hMdef]; exact Nat.sub_le _ _
      intro hx; simp only [NODE, NOUT, false_or, or_false] at hx; omega)]

theorem tb_foldlM_valsW {γ : Type} {n : Nat} (f : γ → Fin n → T3.M γ) (W : Nat → Nat)
    (Inv : Nat → γ → MachineState → Prop) (B : Nat)
    (hbody : ∀ (i : Fin n) acc t, i.val < B → Inv i.val acc t → TBSim im sk t (W i.val) (f acc i) (Inv (i.val + 1))) :
    ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      k + xs.length ≤ B → Inv k acc t →
      TBSim im sk t (((List.range' k xs.length).map W).sum) (xs.foldlM f acc) (Inv (k + xs.length)) := by
  intro xs
  induction xs with
  | nil => intro k acc t _ _ ht; simpa using TBSim.pure (image := im) (sk := sk) ht
  | cons x xs ih =>
    intro k acc t hidx hB ht
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    simp only [List.length_cons] at hB
    rw [List.foldlM_cons, List.length_cons, List.range'_succ, List.map_cons, List.sum_cons]
    have h1 := hbody x acc t (by rw [hidx.1]; omega) (by rw [hidx.1]; exact ht)
    rw [hidx.1] at h1
    refine TBSim.bind h1 (fun acc' t' ht' => ?_)
    have := ih (k + 1) acc' t' (by simpa using hidx.2) (by omega) ht'
    rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this

/-- img-v6: a top node below the root (level `j < 11`, height `j + 1`) with the nonce search (hook 1139). -/
theorem rl_mk_stepN {tc : MachineState} {sig : Signature} {lay : Layer} {tree leaf P WM j : Nat}
    {value : Digest} {u : MachineState} (htop : lay = 0) (hj11 : j < 11) (hj : j < height lay) (htree : tree < 2 ^ 32)
    (hleaf : leaf < 2 ^ height lay)
    (hP0 : 0x7000 ≤ P) (hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hWM8 : WM % 8 = 0) (hWM : 0x800 + 64 * (height lay - 1) ≤ WM) (hWM' : WM + 64 ≤ 0x7000)
    (c5 : tc.getReg .x5 = 0) (c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val)
    (c9 : tc.getReg .x9 = BitVec.ofNat 64 tree) (c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf)
    (c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay))
    (cpath : DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j))
    (cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0) (cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (hI : MkInv tc sig lay leaf P WM j value u) :
    TBSim im sk u (topNodeW j) (let other := (sig.layers lay).path ⟨j, hj⟩
        let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
        T3.topNodeAt (j + 1) (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2)
      (fun res u' => MkInv tc sig lay leaf P WM (j + 1) res.2 u' ∧
        u'.getMem (BitVec.ofNat 64 (0x66700 + 8 * j)) = BitVec.ofNat 64 res.1 ∧
        u'.getMem (BitVec.ofNat 64 0x66758) = BitVec.ofNat 64 leaf ∧
        (∀ A, 0x66700 ≤ A → A < 0x66760 → A ≠ 0x66758 → A ≠ 0x66700 + 8 * j →
          u'.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A))) := by
  have hc : j + 1 < height lay ∨ lay = 0 := Or.inr htop
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
  obtain ⟨t4, k4, s4, hk4, p4, h16, h24', h10, h11, h12, r4, f4⟩ := rl1117_continue (im := im) t3 p3 lay.val tree leaf (height lay) j
    (by omega) htree (by omega) hj hH (by simpa using hc) (fun _ => hleaf)
    (by rw [g3 _ (by decide)]; exact c8) (by rw [g3 _ (by decide)]; exact c9)
    (by rw [g3 _ (by decide)]; exact c18) (by rw [g3 _ (by decide)]; exact c15)
    (by rw [r3.get (by decide), ru2.get (by decide)]; exact hI.x20)
  set heap := 2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 32 := by
    have : 2 ^ (height lay - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : leaf / 2 ^ (j + 1) ≤ leaf := Nat.div_le_self _ _
    omega
  set L := if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j with hL
  set R := if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value with hR
  have f34 : ∀ A, A < 2 ^ 64 → A ≠ NODE + 16 → A ≠ NODE + 24 → t4.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => f4.get hA (by rintro (h | h) <;> contradiction)
  have hblk4 : t4.readWords (BitVec.ofNat 64 NODE) 8 =
      wordsOf (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++ zero16 ++ bytesLE 16 R) := by
    rw [wordsOf_block4, readWords_eight, f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), h16, h24',
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), nl.1, nl.2,
      show NODE + 48 + 8 = NODE + 56 from rfl, nr.1, nr.2,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn32,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn40]
  have hq : hashInput t4 = toQ (pad64 (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++
      zero16 ++ bytesLE 16 R)) := by
    rw [pad64_of_aligned _ (by rw [block4_length])]
    exact hashInput_toQ t4 _ 0 NODE (block4_length _ _ _) h10 (by decide) (by decide) h11 (by decide) hblk4
  have hv : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NODE 64 NOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r34 : RegsExcept t2 t4 ([.x6, .x7, .x29, .x30] ++ [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30]) := r3.trans r4
  have h5 : t4.getReg .x5 = 0 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c5
  have hl0 : lay.val = 0 := by rw [htop]; rfl
  have hH12 : height lay = 12 := by subst htop; rfl
  have hheap1 : 1 ≤ heap := by rw [hheap]; exact le_trans Nat.one_le_two_pow (Nat.le_add_right _ _)
  have hheap2 : heap < 4096 := by
    have e : 2 ^ height lay = 2 ^ (j + 1) * 2 ^ (height lay - j - 1) := by rw [← Nat.pow_add]; congr 1; omega
    have hq : leaf / 2 ^ (j + 1) < 2 ^ (height lay - j - 1) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← e]; exact hleaf
    have hp : 2 ^ (height lay - j - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h11 : (2 : Nat) ^ 11 = 2048 := by norm_num
    rw [hheap]
    rw [h11] at hp
    generalize 2 ^ (height lay - j - 1) = X at hq hp ⊢
    generalize leaf / 2 ^ (j + 1) = Y at hq ⊢
    omega
  have hpar : leaf / 2 ^ (j + 1) % 2 = heap % 2 := by
    rw [hheap, hH12]
    obtain ⟨e, he⟩ : ∃ e, 12 - j - 1 = e + 1 := ⟨10 - j, by omega⟩
    rw [he, pow_succ]; omega
  have ht : T3.nodeTweak 3 0 0 heap = T3.nodeTweak 3 0 tree heap := by unfold T3.nodeTweak; simp
  have hin : topNodeInput heap 0 L R =
      bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++ zero16 ++ bytesLE 16 R := by
    rw [hl0, ClaudeWCT.WCT9.merkleTweak_top]
    unfold topNodeInput
    rw [ne_nonceBytes_zero, ht]
  have hq' : hashInput t4 = toQ (pad64 (topNodeInput heap 0 L R)) := by rw [hin]; exact hq
  obtain ⟨w16, w24⟩ := merkleTweak_words_top tree heap hheap1 hheap2
  have hn32' : t4.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [f34 _ (by decide) (by decide) (by decide),
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn32]
  have hn40' : t4.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [f34 _ (by decide) (by decide) (by decide),
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn40]
  have F : NFacts t4 heap leaf j P' M L R := {
    x5 := h5
    x12 := h12
    x15 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide), c15, hH12]
    x18 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c18
    x20 := by rw [r34.get (by decide), ru2.get (by decide)]; exact hI.x20
    x22 := by rw [r34.get (by decide)]; exact h22
    x24 := by rw [r34.get (by decide)]; exact h24
    w0 := by rw [f34 _ (by decide) (by decide) (by decide)]; exact nl.1
    w8 := by rw [f34 _ (by decide) (by decide) (by decide)]; exact nl.2
    w16 := by rw [h16, hl0]; exact w16
    w24 := by rw [h24', hl0]; exact w24
    w32 := hn32'
    w40 := hn40'
    w48 := by rw [f34 _ (by decide) (by decide) (by decide)]; exact nr.1
    w56 := by rw [f34 _ (by decide) (by decide) (by decide)]; exact nr.2
    h1 := hheap1
    h2 := hheap2
    hj := hj11
    hpar := hpar
    hl := by omega
    hM := by rw [hMdef]; omega
    hM' := by omega }
  have e : (sig.layers lay).path ⟨j, hj⟩ = lpath sig lay j := by unfold lpath; rw [dif_pos hj]
  have hprog : (let other := (sig.layers lay).path ⟨j, hj⟩
      let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
      T3.topNodeAt (j + 1) (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2) =
      T3.publicHash (topNodeInput heap 0 L R) >>= fun a =>
        neTrialTail (j + 1) heap L R (topNonceCap (j + 1) - 1) 0 (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
    rw [e]
    unfold T3.topNodeAt
    rw [ne_topNonceSearch_eq, ne_topNodeHashN_bind]
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · (simp only [hL, hR, hb, ↓reduceIte, hheap]) <;> rfl
    · (simp only [hL, hR, hb, ↓reduceIte, hheap]) <;> rfl
  rw [hprog]
  refine (TBSim.steps (s1.trans (s2.trans (s3.trans s4))) (ne_tb_publicHash_bind (fetch_1138 (im := im) t4 p4) h5 hv hq'
    (W := 32 + (22 * (topNonceCap (j + 1) - 1) + 20))
    (fun a => (nonce_run (im := im) sk F p4 a).mono le_rfl (fun res w hw => ?_)))).mono
    (by rw [ne_topNodeInput_blocks] <;> unfold topNodeW <;> omega) (fun _ _ h => h)
  have fw : Frame t3 w (fun A => (A = NODE + 16 ∨ A = NODE + 24) ∨ NExitW j A) := f4.trans hw.frame
  have hco : NOUT + 16 - 16 * (heap % 2) = NOUT + curOff lay leaf (j + 1) := by
    unfold curOff ClaudeWCT.WCT9.lowerHigh
    rw [hl0, hH12, ← hpar]
    rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ (j + 1)) with hb | hb <;>
      simp [hb, show j + 1 < 12 by omega]
  have hnx : ∀ A, A < 0x7000 → ¬ ((A = NODE + 16 ∨ A = NODE + 24) ∨ NExitW j A) := by
    intro A hA h; unfold NExitW at h; simp only [NODE, NOUT] at h; omega
  refine ⟨⟨hw.pc, hw.x20, by rw [hw.x22]; congr 1, by rw [hw.x24, hMdef, Nat.mul_succ, Nat.sub_sub],
    by omega, by rw [← hco]; exact hw.out, ?_, ?_, ?_⟩, hw.nonceAt, hw.leafAt, ?_⟩
  · intro j' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
    · have hw' := hI.wit j' hj'
      have hs1 := sideOff_le leaf j'
      have hs2 := sideOff_le leaf j
      have hne : WM - 64 * j' + sideOff leaf j' + 16 ≤ M + sideOff leaf j ∨ M + 64 ≤ WM - 64 * j' + sideOff leaf j' := by
        unfold sideOff at hs1 hs2 ⊢; split_ifs <;> omega
      refine ((hw'.frame fu2 (by omega) (by simp) (by simp)).frame f3 (by omega) ?_ ?_).frame fw (by omega)
        (hnx _ (by omega)) (hnx _ (by omega))
      · simp only [NODE]; omega
      · simp only [NODE]; omega
    · have hs2 := sideOff_le leaf j'
      exact wsib.frame fw (by omega) (hnx _ (by omega)) (hnx _ (by omega))
  · exact ((g3'.trans r4).trans hw.regs).mono (by decide)
  · refine (((hI.frame.trans fu2).trans f3).trans fw).mono (fun A _ h => ?_)
    rcases h with ((h | h) | h) | h
    · unfold MkW at h
      rcases h with h | h | h | h | h | h | h | ⟨j', hj', h⟩ | h
      all_goals first
        | exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
        | exact mkW_of (by omega)
        | exact mkW_wit (by omega : j' < j + 1) h
    · exact h.elim
    · rcases h with h | h | h | h | h | h
      · exact mkW_wit (by omega : j < j + 1) (Or.inl h)
      · exact mkW_wit (by omega : j < j + 1) (Or.inr h)
      all_goals exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
    · unfold NExitW at h
      exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
  · intro A h1 h2 h3 h4
    have fall := (fu2.trans f3).trans fw
    rw [fall.get (by omega) (by
      have := sideOff_le leaf j
      have hMb : M ≤ WM := by rw [hMdef]; exact Nat.sub_le _ _
      unfold NExitW; intro hx; simp only [NODE, NOUT, false_or, or_false] at hx; omega)]

theorem recoverTop_tbsim {s0 : MachineState} {sig : Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 sig index lay digits P WC WM ret) (htop : lay = 0) (hT11 : 11 < height lay) :
    TBSim im sk s0 (rlCost lay) (topProg sig index lay digits hT11)
      (fun r t => RlPost s0 sig index lay WC WM ret r.2 t ∧ TopBlkG sig index lay r.1.1 t ∧
        NoncesAt t r.1.2 (route index lay).1) := by
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
  have hH12 : height lay = 11 + 1 := by subst htop; rfl
  have hl0 : lay.val = 0 := by rw [htop]; rfl
  unfold topProg
  have htr0 : (route index lay).2 = 0 := by rw [htop]; exact Nat.div_eq_of_lt hpre.hidx
  have hchW : ∀ (lf i d c : Nat) (v : Digest), SigGolfCandidate.T3.layChain lay (route index lay).2 lf i d c v =
      ClaudeWCT.WCT9.chainW lay (route index lay).2 lf i d c v := fun lf i d c v => by
    rw [htr0, htop, SigGolfCandidate.T3.layChain_top, ClaudeWCT.WCT9.chainW_top_eq]
  have hnW : ∀ (tr heap : Nat) (l r : Digest), SigGolfCandidate.T3.nodeHash 3 lay.val tr heap l r =
      ClaudeWCT.WCT9.lowerNodeHash lay.val tr heap l r := fun tr heap l r => by
    rw [hl0, ClaudeWCT.WCT9.lowerNodeHash_top]
  simp only [hchW, hnW]
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
  have hhd16 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inl rfl) (by omega)), l16]
  have hhd24 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inr rfl) (by omega)), l24]
  -- T51 endpad: `end_0 | tweak | end_1 .. end_50` (the top slots are the lower ones).
  have hw : v2.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks' lay) =
      wordsOf (pad64 (T3.leafInput lay tree leaf ends)) := by
    rw [leafInput_words' lay tree leaf ends hlen]
    have h0 : DigAt v2 LEAFPK (ends.getD 0 0) := by
      have := (hC.slots 0 (by omega)).frame fu2 (by simp only [slotOff]; decide) (by simp) (by simp)
      simpa [slotOff] using this
    have hrest : DigsAt v2 (LEAFPK + 32) (ends.drop 1) := by
      intro c hc
      simp only [List.length_drop] at hc
      have := (hC.slots (c + 1) (by omega)).frame fu2 (by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega)
        (by simp) (by simp)
      simp only [slotOff, if_neg (show c + 1 ≠ 0 by omega)] at this
      rw [show LEAFPK + 32 + 16 * c = LEAFPK + (16 * (c + 1) + 16) by ring]
      simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
    have hhd : v2.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
        [T3.hyperWord lay.val (tree * 2 ^ height lay + leaf), 0] := by
      rw [readWords_two, hhd16, show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, hhd24]
    have hb : 8 * leafBlocks' lay = 2 + (2 + 2 * (ends.drop 1).length) := by
      have hn51 : chainCount lay = 51 := by rw [htop]; rfl
      simp only [List.length_drop, hlen, leafBlocks', hn51]
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
  unfold leafHash
  rw [← ClaudeWCT.WCT9.halfHash_eq_projHash]
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
  have hM0 : MkInv tc sig lay leaf P WM 0 (ClaudeWCT.WCT9.halfOf (T3.leafHalfHigh lay leaf) a) v4 := by
    refine ⟨pv4, x20, by rw [x22]; congr 1, ?_, by omega, ?_, fun j hj => absurd hj (by omega), rv4.mono (by decide),
      fv4.mono (fun _ _ h => h.elim)⟩
    · rw [rv4.get (by decide), rtc.get (by decide), hpre.x24]; congr 1
    · have hlh : T3.leafHalfHigh lay leaf = ClaudeWCT.WCT9.lowerHigh lay.val leaf := by
        rw [htop, ← ClaudeWCT.WCT9.lowerHigh_top_eq_leafHalfHigh]
      rw [curOff_zero, hlh]
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
  have hmap : ((List.finRange (height lay)).take 11).map Fin.val =
      List.range' 0 ((List.finRange (height lay)).take 11).length := by subst htop; decide
  have hlen11 : ((List.finRange (height lay)).take 11).length = 11 := by subst htop; decide
  have hbody : ∀ (i : Fin (height lay)) (acc : Digest × List Nat) (w : MachineState), i.val < 11 →
      TopInv tc sig lay leaf P WM i.val acc w →
      TBSim im sk w (topNodeW i.val) (topStepP sig index lay acc i) (TopInv tc sig lay leaf P WM (i.val + 1)) := by
    intro i acc w hi hw
    obtain ⟨hI, hlen, hn, hlf⟩ := hw
    have e : topStepP sig index lay acc i = (T3.topNodeAt (i.val + 1)
        (2 ^ (height lay - i.val - 1) + leaf / 2 ^ (i.val + 1))
        (if leaf / 2 ^ i.val % 2 = 0 then (acc.1, (sig.layers lay).path ⟨i.val, i.isLt⟩)
          else ((sig.layers lay).path ⟨i.val, i.isLt⟩, acc.1)).1
        (if leaf / 2 ^ i.val % 2 = 0 then (acc.1, (sig.layers lay).path ⟨i.val, i.isLt⟩)
          else ((sig.layers lay).path ⟨i.val, i.isLt⟩, acc.1)).2 >>= fun found =>
        pure (found.2, acc.2 ++ [found.1])) := rfl
    rw [e]
    refine (TBSim.bind (W₂ := 0) (rl_mk_stepN (im := im) (sk := sk) htop hi i.isLt htree hleaf hpre.hP hpre.hP'
      hpre.hP8 hpre.hWM8 hpre.hWM (by omega) c5 c8 c9 c18 c15 (cpath i.val i.isLt) cn32 cn40 hI)
      (fun res w' h => TBSim.pure ⟨h.1, ?_, ?_, ?_⟩)).mono (by omega) (fun _ _ h => h)
    · simp [hlen]
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [h.2.2.2 (0x66700 + 8 * k) (by omega) (by omega) (by omega) (by omega), hn k hk,
          List.getD_append _ _ _ _ (by omega)]
      · rw [h.2.1, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self] <;> rfl
    · intro _; exact h.2.2.1
  have hfold := tb_foldlM_valsW (im := im) (sk := sk) (topStepP sig index lay) topNodeW
    (TopInv tc sig lay leaf P WM) 11 hbody
    ((List.finRange (height lay)).take 11) 0 (ClaudeWCT.WCT9.halfOf (T3.leafHalfHigh lay leaf) a, []) v4 hmap
    (by rw [hlen11]) ⟨hM0, rfl, fun k hk => absurd hk (by omega), fun h => absurd h (by omega)⟩
  rw [hlen11] at hfold
  refine (TBSim.steps sv4 (TBSim.bind (W₂ := 81 + 10) hfold (fun vn w0 hw0 => ?_))).mono
    (by unfold climbW; rw [if_pos htop]; omega) (fun _ _ h => h)
  obtain ⟨hw0, hlen0, hn0, hlf0⟩ := hw0
  refine (TBSim.bind (W₂ := 10) (rl_mk_step (im := im) hT11 (Or.inr htop) htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM
      (by omega) c5 c8 c9 c18 c15 (cpath 11 hT11) cn32 cn40 (by simpa using hw0) (Or.inr le_rfl)) (fun root w hw' => ?_)).mono
    (by omega) (fun _ _ h => h)
  obtain ⟨hw, hblkw, hkeep⟩ := hw'
  rw [show (11 + 1 : Nat) = height lay from hH12.symm] at hw
  obtain ⟨wx1, swx1, pwx1, rwx1, fwx1⟩ := rl1076_spec (im := im) w hw.pc (height lay) (height lay) (by omega) (by omega)
    hw.x20 (by rw [hw.regs.get (by decide)]; exact c15)
  rw [if_pos (le_refl _)] at pwx1
  have rsw : RegsExcept s0 wx1 rlRegs := ((rtc.trans hw.regs).trans rwx1).mono (by decide)
  obtain ⟨t, st, pt, e0, e8, rt, ft⟩ := rl1143_spec (im := im) wx1 pwx1 ret (by rw [rsw.get (by decide), hpre.x1])
  have fw1 : Frame w wx1 (fun _ => False) := fwx1
  refine TBSim.steps (swx1.trans st) (TBSim.pure ⟨⟨pt, ?_, ?_, ?_, ((rsw.trans rt).mono (by decide)), ?_⟩, ?_, ?_⟩)
  · have hv0 := hw.val
    rw [curOff_root, Nat.add_zero] at hv0
    refine ⟨e0.trans ?_, e8.trans ?_⟩
    · rw [fw1.get (by decide) (by simp)]; exact hv0.1
    · rw [fw1.get (by decide) (by simp)]; exact hv0.2
  · intro i hi
    have hv := hC.wvals i (by omega)
    have hWi : WM + 64 ≤ WC - 64 * i + 48 := by omega
    refine (((hv.frame fu2 (by omega) (by simp) (by simp)).frame fwc (by omega) (by simp only [NOUT]; omega)
      (by simp only [NOUT]; omega)).frame hw.frame (by omega) (not_MkW_of (by omega) (by simp only [NODE]; omega)
      (by simp only [NOUT]; omega)) (not_MkW_of (by omega) (by simp only [NODE]; omega)
      (by simp only [NOUT]; omega))).frame (fw1.trans ft) (by omega) ?_ ?_
    · rintro (h | h | h) <;> first | exact h | (simp only [ENC] at h; omega)
    · rintro (h | h | h) <;> first | exact h | (simp only [ENC] at h; omega)
  · intro j hj
    have hs := sideOff_le leaf j
    exact (hw.wit j hj).frame (fw1.trans ft) (by omega)
      (by rintro (h | h | h) <;> first | exact h | (simp only [ENC] at h; omega))
      (by rintro (h | h | h) <;> first | exact h | (simp only [ENC] at h; omega))
  · have fall := ((ftc.trans hw.frame).trans fw1).trans ft
    refine fall.mono (fun A _ h => ?_)
    unfold RlScratch RlWit
    rcases h with ((((((hX | hC) | hF) | hN) | hM) | hF2) | hE)
    · rcases hX with h | h | h | h <;>
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [LEAFPK] at h ⊢; omega)))))
    · unfold ChW StepW at hC
      rcases hC with (h | h) | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
      · exact Or.inl (by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · have hlt := slotOff_lt lay (show c < chainCount lay by omega)
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [LEAFPK] at h ⊢; omega)))))
      · exact Or.inr (Or.inl ⟨c, by omega, h⟩)
    · exact hF.elim
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hN)))))))))))
    · unfold MkW at hM
      rcases hM with h | h | h | h | h | h | h | ⟨j', hj', h⟩ | h
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl h)))))))))))
      · exact Or.inr (Or.inr ⟨j', hj', h⟩)
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))
    · exact hF2.elim
    · rcases hE with h | h
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl h))))))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl h)))))))))))))
  · unfold TopBlkG
    rw [frame_readWordsL (fw1.trans ft) NODE 8 (by decide) (fun i hi h => by
      rcases h with h | h | h
      · exact h
      · simp only [NODE, ENC] at h; omega
      · simp only [NODE, ENC] at h; omega)]
    rw [hblkw, hl0, ClaudeWCT.WCT9.merkleTweak_top]
  · have fwt : Frame w t (fun A => False ∨ (A = ENC ∨ A = ENC + 8)) := fw1.trans ft
    have hkt : ∀ A, 0x66700 ≤ A → A < 0x66760 → t.getMem (BitVec.ofNat 64 A) = w0.getMem (BitVec.ofNat 64 A) :=
      fun A h1 h2 => by rw [fwt.get (by omega) (by intro hx; simp only [ENC, false_or] at hx; omega), hkeep A h1 h2]
    refine ⟨by simpa using hlen0, fun k hk => ?_, ?_⟩
    · rw [hkt (0x66700 + 8 * k) (by omega) (by omega)]; exact hn0 k (by omega)
    · rw [hkt 0x66758 (by omega) (by omega)]; exact hlf0 (by omega)


end SigGolfCandidate.T3M.Expand.SharedRecover
end
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
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutBlock ====
section

/-! # Pairing stage 1: the leaf / digest layout block (expand words 48100 .. 49225)

Entered by `43953: jal 48100` (after `43472..43476`), it copies the staged rho / digest counter (32 bytes at 23008) to
the witness tail at 26112, clears `[23008, 26112)` (388 words), then fills the four leaf buffers: 180 chunks (T51; #938 had 183)
`lui a0; addi a0,S; ld t1,0(a0); sd t1,X(a1); ld t1,8(a0); sd t1,X+8(a1)`, each group preceded by `li a1,D`
(D = 23008 / 23744 / 24480 / 25232), and returns through the straight tail `cRet` (49207 .. 49225: #938's
items 180..182 without their stores, then `jal 43500`). Sources `S` (chain values in the final paired
layout) lie below 23008. -/

namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
def chunkRes (S X p : Nat) : Result :=
  ⟨⟨(RegFile.init.set .x6 (E.ld (.c (BitVec.ofNat 64 (S + 8))))).set .x10 (.c (BitVec.ofNat 64 S)),
    [(⟨some (.reg .x11), BitVec.ofNat 64 (X + 8)⟩, E.ld (.c (BitVec.ofNat 64 (S + 8)))),
     (⟨some (.reg .x11), BitVec.ofNat 64 X⟩, E.ld (.c (BitVec.ofNat 64 S)))],
    [.valid ⟨some (.reg .x11), BitVec.ofNat 64 (X + 8)⟩ 8, .ne ⟨none, BitVec.ofNat 64 (S + 8)⟩
      ⟨some (.reg .x11), BitVec.ofNat 64 X⟩, .valid ⟨some (.reg .x11), BitVec.ofNat 64 X⟩ 8]⟩,
    .c (pcOf (p + 6)), .endOfCode, 6, 6⟩
theorem run_chunk (k : Nat) (hk : k < 180) :
    symRun cfgC (lbCodes.getD k []) (pcOf (pcK k)) 40 = some (chunkRes (sK k) (xK k) (pcK k)) := by
  interval_cases k <;> kernel_rfl
def headRes (D p : Nat) : Result := ⟨⟨RegFile.init.set .x11 (.c (BitVec.ofNat 64 D)), [], []⟩, .c (pcOf (p + 2)),
  .endOfCode, 2, 2⟩
theorem run_head (g : Nat) (hg : g < 4) :
    symRun cfgC (lbHeadCodes.getD g []) (pcOf (lbHeadPc.getD g 0)) 40 =
      some (headRes ([23008, 23744, 24480, 25232].getD g 0) (lbHeadPc.getD g 0)) := by
  interval_cases g <;> kernel_rfl
sym_block RTop := symRun cfgC cTop (pcOf 48100) 40
sym_block RClr0 := symRun cfgC cClr0 (pcOf 48112) 40
sym_block RClrL := symRun cfgC cClrL (pcOf 48116) 40
sym_block RRet := symRun cfgC cRet (pcOf 49207) 40

theorem slot_mono : ∀ k j, k < j → j < 180 → slotK k + 16 ≤ slotK j := by
  intro k j hkj hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hadj := tab_facts.2.2.2.2.2.1 j (by omega)
    by_cases h : k = j
    · subst h; exact hadj
    · have := ih (by omega) (by omega); omega
def hitVal (M : Nat → Word) (j A : Nat) : Word :=
  match (List.range j).find? (fun k => decide (slotK k ≤ A ∧ A < slotK k + 16)) with
  | some k => M (sK k + (A - slotK k))
  | none => 0
/-- Memory after the tail copy, the clear and the first `j` leaf-slot items. -/
def itMem (M : Nat → Word) (j A : Nat) : Word :=
  if 26112 ≤ A ∧ A < 26144 ∧ A % 8 = 0 then M (A - 3104)
  else if 23008 ≤ A ∧ A < 26112 ∧ A % 8 = 0 then hitVal M j A
  else M A
/-- The memory after the whole layout block. -/
def lbMem (M : Nat → Word) (A : Nat) : Word := itMem M 180 A
theorem hitVal_succ (M : Nat → Word) (j A : Nat) (hj : j < 180) :
    hitVal M (j + 1) A = if slotK j ≤ A ∧ A < slotK j + 16 then M (sK j + (A - slotK j)) else hitVal M j A := by
  unfold hitVal
  rw [List.range_succ, List.find?_append]
  by_cases hA : slotK j ≤ A ∧ A < slotK j + 16
  · have hnone : (List.range j).find? (fun k => decide (slotK k ≤ A ∧ A < slotK k + 16)) = none := by
      rw [List.find?_eq_none]
      intro k hk
      have := slot_mono k j (List.mem_range.mp hk) hj
      simp only [decide_eq_true_eq]; omega
    rw [hnone, if_pos hA]
    simp [hA]
  · rw [if_neg hA]
    cases h : (List.range j).find? (fun k => decide (slotK k ≤ A ∧ A < slotK k + 16)) with
    | some k => rfl
    | none => simp [hA]
theorem chunk_regs (S X p : Nat) (u : MachineState) : RegsExcept u ((chunkRes S X p).toState u) [.x6, .x10] := by
  intro r hr; simp at hr; cases r <;> simp_all [chunkRes, rv_simp] <;> rfl
def topM (M : Nat → Word) (A : Nat) : Word :=
  if 26112 ≤ A ∧ A < 26144 ∧ A % 8 = 0 then M (A - 3104) else M A
def clrM (M : Nat → Word) (i A : Nat) : Word :=
  if 23008 ≤ A ∧ A < 23008 + 8 * i ∧ A % 8 = 0 then 0 else topM M A
theorem itMem_zero (M : Nat → Word) (A : Nat) : clrM M 388 A = itMem M 0 A := by
  unfold clrM itMem topM hitVal
  simp only [List.range_zero, List.find?_nil]
  split_ifs <;> first | rfl | omega
def itemsLen (j : Nat) : Nat := ((List.range j).map itemLen).sum
theorem itemsLen_succ (j : Nat) : itemsLen (j + 1) = itemsLen j + itemLen j := by
  unfold itemsLen; rw [List.range_succ, List.map_append, List.sum_append]; simp
theorem itemsLen_all : itemsLen 180 = 1088 := by decide
section
variable {im : Image} (hc : Code im)
include hc
theorem item_spec (k : Nat) (hk : k < 180) (M : Nat → Word) (s : MachineState) (hpc : s.pc = pcOf (itemPc k))
    (h11 : hdK k = false → s.getReg .x11 = BitVec.ofNat 64 (dK k))
    (hm : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = itMem M k A) :
    ∃ t, Steps im s (itemLen k) (itemLen k) t ∧ t.pc = pcOf (pcK k + 6) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dK k) ∧ RegsExcept s t [.x6, .x10, .x11] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = itMem M (k + 1) A := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨hS8, hS, hX8, hX, hD8, hD⟩ := tab_facts.2.2.2.2.2.2.2.2 k hk
  have hsl := slot_mono 0 k
  have hsl0 := tab_facts.2.2.2.2.2.2.1
  have hslE : slotK k + 16 ≤ 26112 := by
    by_cases h : k = 179
    · subst h; exact tab_facts.2.2.2.2.2.2.2.1
    · have := slot_mono k 179 (by omega) (by omega); have := tab_facts.2.2.2.2.2.2.2.1; omega
  -- reach the chunk with x11 = dK k
  obtain ⟨u, su, pu, u11, ru, fu, hlen⟩ : ∃ u, Steps im s (itemLen k - 6) (itemLen k - 6) u ∧ u.pc = pcOf (pcK k) ∧
      u.getReg .x11 = BitVec.ofNat 64 (dK k) ∧ RegsExcept s u [.x11] ∧ Frame s u (fun _ => False) ∧
      itemLen k = (itemLen k - 6) + 6 := by
    cases hh : hdK k
    · refine ⟨s, by simpa [itemLen, hh] using Steps.refl s, by rw [hpc]; simp [itemPc, hh], h11 hh,
        RegsExcept.refl _ _, Frame.refl _ _, by simp [itemLen, hh]⟩
    · have hg : grpK k < 4 := by unfold grpK; split_ifs <;> omega
      have hpcg := tab_facts.2.2.2.1 k hk hh
      have hD : [23008, 23744, 24480, 25232].getD (grpK k) 0 = dK k := by
        unfold hdK at hh; simp only [Bool.or_eq_true, beq_iff_eq] at hh
        rcases hh with ((h | h) | h) | h <;> subst h <;> decide
      have hrun := run_head (grpK k) hg
      have h2 : 2 ≤ pcK k := by
        unfold hdK at hh; simp only [Bool.or_eq_true, beq_iff_eq] at hh
        rcases hh with ((h | h) | h) | h <;> subst h <;> decide
      refine ⟨_, (symRun_sound hrun (hc.head _ hg) s (by rw [hpc, hpcg]; simp [itemPc, hh])
        (by simp [headRes, rv_simp])).of_eq (by simp [itemLen, hh, headRes]) (by simp [itemLen, hh, headRes]),
        ?_, ?_, ?_, ?_, by simp [itemLen, hh]⟩
      · simp only [Result.toState_pc, headRes, E.eval, hpcg]
        rw [show pcK k - 2 + 2 = pcK k by omega]
      · simp only [Result.toState_getReg, headRes, rv_simp, hD]; rfl
      · intro r hr; simp at hr; cases r <;> simp_all [headRes, rv_simp] <;> rfl
      · intro A _ _; rfl
  have hdk0 : 23008 ≤ slotK k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact hsl0
    · have := slot_mono 0 k h hk; omega
  have hmu : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = itMem M k A := fun A hA => by
    rw [fu.get hA (by simp), hm A hA]
  have srcM : ∀ x, x < 16 → u.getMem (BitVec.ofNat 64 (sK k + x)) = M (sK k + x) := fun x hx => by
    rw [hmu _ (by omega)]; unfold itMem; rw [if_neg (by omega), if_neg (by omega)]
  have hobl : Oblig.all u (chunkRes (sK k) (xK k) (pcK k)).st.obl := by
    simp [chunkRes, rv_simp, accessValid_iff, u11, BitVec.toNat_ofNat, ofNat_add_ofNat]
    simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, hM]; unfold slotK at *; omega
  have sc := symRun_sound (run_chunk k hk) (hc.chunk k hk) u pu hobl
  refine ⟨_, (su.trans sc).of_eq (by show (itemLen k - 6) + 6 = itemLen k; omega)
    (by show (itemLen k - 6) + 6 = itemLen k; omega), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, chunkRes, E.eval]
  · simp only [Result.toState_getReg, chunkRes, rv_simp]; rw [← u11]; rfl
  · exact (ru.trans (chunk_regs _ _ _ u)).mono (by simp)
  · intro A hA
    have k0 := ofNat_inj hA (show slotK k < 2 ^ 64 by omega)
    have k8 := ofNat_inj hA (show slotK k + 8 < 2 ^ 64 by omega)
    have e8 : BitVec.ofNat 64 (dK k + (xK k + 8)) = BitVec.ofNat 64 (slotK k + 8) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; unfold slotK at *; omega
    have e0 : BitVec.ofNat 64 (dK k + xK k) = BitVec.ofNat 64 (slotK k) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; unfold slotK at *; omega
    simp only [Result.toState_getMem, chunkRes, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, u11,
      ofNat_add_ofNat, e8, e0, k0, k8]
    rw [srcM 8 (by omega), show sK k = sK k + 0 from rfl, srcM 0 (by omega), hmu A hA]
    unfold itMem
    rw [hitVal_succ M k A hk]
    by_cases a8 : A = slotK k + 8
    · subst a8; rw [if_pos rfl, if_neg (by omega), if_pos ⟨by omega, by omega, by unfold slotK; omega⟩,
        if_pos ⟨by omega, by omega⟩]
      simp
    rw [if_neg a8]
    by_cases a0 : A = slotK k
    · subst a0; rw [if_pos rfl, if_neg (by omega), if_pos ⟨by omega, by omega, by unfold slotK; omega⟩,
        if_pos ⟨le_rfl, by omega⟩]
      simp
    rw [if_neg a0]
    by_cases ht : 26112 ≤ A ∧ A < 26144 ∧ A % 8 = 0
    · rw [if_pos ht, if_pos ht]
    rw [if_neg ht, if_neg ht]
    by_cases hb : 23008 ≤ A ∧ A < 26112 ∧ A % 8 = 0
    · rw [if_pos hb, if_pos hb, if_neg (by unfold slotK at *; omega)]
    · rw [if_neg hb, if_neg hb]

set_option maxRecDepth 200000 in
theorem top_spec (s : MachineState) (hpc : s.pc = pcOf 48100) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 48112 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = topM (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  refine ⟨_, symRun_sound RTop hc.top s hpc (by simp [RTop.res, rv_simp]), ?_, ?_⟩
  · simp only [Result.toState_pc, RTop.res, E.eval]
  · intro A hA
    have key : ∀ c : Nat, c < 2 ^ 64 → (BitVec.ofNat 64 A = BitVec.ofNat 64 c ↔ A = c) := fun c hc => ofNat_inj hA hc
    simp only [Result.toState_getMem, RTop.res, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval,
      key 26136 (by norm_num), key 26128 (by norm_num), key 26120 (by norm_num), key 26112 (by norm_num)]
    unfold topM
    by_cases h : 26112 ≤ A ∧ A < 26144 ∧ A % 8 = 0
    · rw [if_pos h]
      rcases (show A = 26112 ∨ A = 26120 ∨ A = 26128 ∨ A = 26136 by omega) with rfl | rfl | rfl | rfl <;> rfl
    · rw [if_neg h, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem clr_iter (s : MachineState) (hpc : s.pc = pcOf 48116) (i : Nat) (hi : i < 388)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (23008 + 8 * i)) (h11 : s.getReg .x11 = BitVec.ofNat 64 26112) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if i + 1 < 388 then pcOf 48116 else pcOf 48119) ∧
      t.getReg .x10 = BitVec.ofNat 64 (23008 + 8 * (i + 1)) ∧ t.getReg .x11 = BitVec.ofNat 64 26112 ∧
      RegsExcept s t [.x10] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = 23008 + 8 * i then 0 else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound RClrL hc.clrL s hpc (by
    simp [RClrL.res, rv_simp, accessValid_iff, h10, BitVec.toNat_ofNat]; omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RClrL.res, E.eval, CmpOp.eval, BinOp.eval, h10, h11, ofNat_add_ofNat]
    have he : BitVec.ult (BitVec.ofNat 64 (23008 + 8 * i + 8)) (BitVec.ofNat 64 26112) = decide (i + 1 < 388) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [decide_eq_decide]; omega
    rw [he]
    by_cases h : i + 1 < 388 <;> simp [h]
  · rw [show 23008 + 8 * (i + 1) = 23008 + 8 * i + 8 by ring]; simp [RClrL.res, rv_simp, h10, ofNat_add_ofNat]
  · simp [RClrL.res, rv_simp, h11]
  · intro r hr; simp at hr; cases r <;> simp_all [RClrL.res, rv_simp] <;> rfl
  · intro A hA
    have key := ofNat_inj hA (show 23008 + 8 * i < 2 ^ 64 by omega)
    simp only [Result.toState_getMem, RClrL.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h10,
      BitVec.add_zero, key]
    rfl
theorem clr_loop (s : MachineState) (hpc : s.pc = pcOf 48116) (M : Nat → Word)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 23008) (h11 : s.getReg .x11 = BitVec.ofNat 64 26112)
    (hm : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = topM M A) :
    ∀ i, 0 < i → i ≤ 388 → ∃ t, Steps im s (3 * i) (3 * i) t ∧
      t.pc = (if i < 388 then pcOf 48116 else pcOf 48119) ∧
      t.getReg .x10 = BitVec.ofNat 64 (23008 + 8 * i) ∧ t.getReg .x11 = BitVec.ofNat 64 26112 ∧
      RegsExcept s t [.x10] ∧ ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = clrM M i A := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hi
    obtain ⟨t, st, pt, t10, t11, rt, mt⟩ : ∃ t, Steps im s (3 * i) (3 * i) t ∧ t.pc = pcOf 48116 ∧
        t.getReg .x10 = BitVec.ofNat 64 (23008 + 8 * i) ∧ t.getReg .x11 = BitVec.ofNat 64 26112 ∧
        RegsExcept s t [.x10] ∧ ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = clrM M i A := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        exact ⟨s, Steps.refl s, hpc, by simpa using h10, h11, RegsExcept.refl _ _, fun A hA => by
          rw [hm A hA]; unfold clrM; rw [if_neg (by omega)]⟩
      · obtain ⟨t, st, pt, t10, t11, rt, mt⟩ := ih h0 (by omega)
        exact ⟨t, st, by rw [pt, if_pos (by omega)], t10, t11, rt, mt⟩
    obtain ⟨u, su, pu, u10, u11, ru, mu⟩ := clr_iter hc t pt i (by omega) t10 t11
    refine ⟨u, (st.trans su).of_eq (by omega) (by omega), pu,
      u10, u11, (rt.trans ru).mono (by simp), fun A hA => ?_⟩
    rw [mu A hA, mt A hA]
    unfold clrM
    by_cases ha : A = 23008 + 8 * i
    · subst ha; rw [if_pos rfl, if_pos (by omega)]
    · rw [if_neg ha]
      by_cases h1 : 23008 ≤ A ∧ A < 23008 + 8 * i ∧ A % 8 = 0
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
theorem items_loop (M : Nat → Word) (s : MachineState) (hpc : s.pc = pcOf 48119)
    (hm : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = itMem M 0 A) :
    ∀ j, j ≤ 180 → ∃ t, Steps im s (itemsLen j) (itemsLen j) t ∧
      t.pc = pcOf (if j < 180 then itemPc j else 49207) ∧
      (0 < j → j < 180 → hdK j = false → t.getReg .x11 = BitVec.ofNat 64 (dK j)) ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = itMem M j A := by
  intro j
  induction j with
  | zero => intro _; exact ⟨s, Steps.refl s, by rw [hpc, if_pos (by omega)]; rfl,
      fun h => absurd h (by omega), hm⟩
  | succ j ih =>
    intro hj
    obtain ⟨t, st, pt, t11, mt⟩ := ih (by omega)
    rw [if_pos (by omega)] at pt
    obtain ⟨u, su, pu, u11, ru, mu⟩ := item_spec hc j (by omega) M t pt
      (fun hh => t11 (tab_facts.2.2.2.2.1 j (by omega) hh).1 (by omega) hh) mt
    refine ⟨u, (st.trans su).of_eq (itemsLen_succ j).symm (itemsLen_succ j).symm, ?_, ?_, mu⟩
    · by_cases hj' : j + 1 < 180
      · rcases (tab_facts.1 j (by omega)) with h | h
        · rw [pu, h, if_pos hj']
        · omega
      · have : j = 179 := by omega
        subst this; rw [pu, if_neg (by omega), tab_facts.2.1]
    · intro _ hj' hh
      rw [u11, (tab_facts.2.2.2.2.1 (j + 1) hj' hh).2, Nat.add_sub_cancel]
/-- Pairing stage 1: the whole layout block, 48100 -> 43500 in 2287 steps. -/
theorem layout_spec (s : MachineState) (hpc : s.pc = pcOf 48100) :
    ∃ t, Steps im s 2287 2287 t ∧ t.pc = pcOf 43500 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = lbMem (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨t1, s1, p1, m1⟩ := top_spec hc s hpc
  obtain ⟨t2, s2, p2, x10, x11, f2⟩ : ∃ t, Steps im t1 4 4 t ∧ t.pc = pcOf 48116 ∧
      t.getReg .x10 = BitVec.ofNat 64 23008 ∧ t.getReg .x11 = BitVec.ofNat 64 26112 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = t1.getMem (BitVec.ofNat 64 A) := by
    refine ⟨_, symRun_sound RClr0 hc.clr0 t1 p1 (by simp [RClr0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, RClr0.res, E.eval]
    · simp [RClr0.res, rv_simp]
    · simp [RClr0.res, rv_simp]
    · intro A _; simp [RClr0.res, rv_simp]
  obtain ⟨t3, s3, p3, _, _, _, m3⟩ := clr_loop hc t2 p2 _ x10 x11 (fun A hA => by rw [f2 A hA, m1 A hA]) 388
    (by omega) le_rfl
  rw [if_neg (by omega)] at p3
  obtain ⟨t4, s4, p4, _, m4⟩ := items_loop hc _ t3 p3 (fun A hA => by rw [m3 A hA, itMem_zero]) 180 le_rfl
  rw [if_neg (by omega)] at p4
  refine ⟨_, ((((s1.trans s2).trans s3).trans s4).trans (symRun_sound RRet hc.ret t4 p4
    (by simp [RRet.res, rv_simp]))).of_eq (by rw [itemsLen_all]; simp [RRet.res]) (by rw [itemsLen_all]; simp [RRet.res]),
    ?_, fun A hA => ?_⟩
  · simp [Result.toState_pc, RRet.res, E.eval]
  · rw [show ((RRet.res).toState t4).getMem (BitVec.ofNat 64 A) = t4.getMem (BitVec.ofNat 64 A) by
      simp [RRet.res, rv_simp], m4 A hA]
    rfl
end
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Final ====
section

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
def WIT : Nat := 0x800
def SNAP2 : Nat := 0x310000
/-- Nested FTS (r1-1): the final witness base (the frontier's was `WIT`). Witness trim: `0x520` (was `0x4c0`). -/
def WOUT : Nat := 0xB58
/-- Witness trim: the compactor's zeroing loop still starts at the old base `0x4c0` (unchanged machine word); the
96 bytes `[0x4c0, 0x520)` are scratch below the witness. -/
def WZ : Nat := 0x480
def copyRegs (src dst n ret : Nat) : RegFile :=
  (((RegFile.init.set .x1 (.c (pcOf ret))).set .x10 (.c (BitVec.ofNat 64 src))).set .x11
    (.c (BitVec.ofNat 64 dst))).set .x12 (.c (BitVec.ofNat 64 n))
def zeroRegs (dst n ret : Nat) : RegFile :=
  ((RegFile.init.set .x1 (.c (pcOf ret))).set .x11 (.c (BitVec.ofNat 64 dst))).set .x12 (.c (BitVec.ofNat 64 n))
theorem run_snap : symRun cfgC cSnap (pcOf 42142) 40 =
    some ⟨⟨copyRegs WIT SNAP2 2729 42149, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
theorem run_zero2 : symRun cfgC cZero2 (pcOf 42149) 40 =
    some ⟨⟨zeroRegs WZ 3124 42154, [], []⟩, .c (pcOf 42137), .jump, 5, 5⟩ := by kernel_rfl
theorem run_hdr : symRun cfgC cHdr (pcOf 42154) 40 =
    some ⟨⟨RegFile.init, [], []⟩, .c (pcOf 33117), .jump, 1, 1⟩ := by kernel_rfl
theorem run_ctr : symRun cfgC cCtr (pcOf 33117) 40 =
    some ⟨⟨copyRegs (SNAP2 + 32) 1184 2 (33117 + 5), [], []⟩, .c (pcOf 42130), .jump, 5, 5⟩ := by kernel_rfl
theorem run_preg (c : Nat) (hc : c < 9) : symRun cfgC (cPReg c) (pcOf (pregAt c)) 40 =
    some ⟨⟨copyRegs (SNAP2 + 64 + 896 * c) (10152 - 896 * c) 112 (pregAt c + 6), [], []⟩, .c (pcOf 42130), .jump,
      6, 6⟩ := by
  interval_cases c <;> kernel_rfl
theorem run_pend : symRun cfgC cPEnd (pcOf 33284) 40 =
    some ⟨⟨RegFile.init, [], []⟩, .c (pcOf 42224), .jump, 1, 1⟩ := by kernel_rfl
/-- Nested FTS (r1-1): hold placement of coordinate `c` stores its top sibling at `hdst c + 144 flag` (r3w: store
immediates `-48 (6 - c)` for `c < 6`; the FTS content of these slots is dead, zeroed by the finish pass). -/
def hdst (c : Nat) : Nat := 8384 - 896 * c - 48 * (6 - c)
def hfE (c : Nat) : E := E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c + 16)))
def hbE (c : Nat) : E := .bin .add (.bin .sll (hfE c) (.c 7#64)) (.bin .sll (hfE c) (.c 4#64))
def holdRegs (c : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (.c (BitVec.ofNat 64 (8384 - 896 * c)))).set .x13
    (.bin .add (hbE c) (.c (BitVec.ofNat 64 (8384 - 896 * c))))).set .x28 (.c 0x380000#64)).set .x29
    (E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c))))).set .x30 (E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c + 8))))).set
    .x31 (.bin .sll (hfE c) (.c 4#64))
def holdSym (c : Nat) : SymMem :=
  [(⟨some (hbE c), BitVec.ofNat 64 (hdst c + 8)⟩, E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c + 8)))),
    (⟨some (hbE c), BitVec.ofNat 64 (hdst c)⟩, E.ld (.c (BitVec.ofNat 64 (Compact.holdAt c))))]
def holdObl (c : Nat) : List Oblig :=
  [.valid ⟨some (hbE c), BitVec.ofNat 64 (hdst c + 8)⟩ 8, .valid ⟨some (hbE c), BitVec.ofNat 64 (hdst c)⟩ 8]
theorem run_hold (c : Nat) (hc : c < 9) : symRun cfgC (cHold c) (pcOf (holdPc c)) 40 =
    some ⟨⟨holdRegs c, holdSym c, holdObl c⟩, .c (pcOf (holdPc c + 12)), .endOfCode, 12, 12⟩ := by
  interval_cases c <;> kernel_rfl
theorem run_top : symRun cfgC cTop (pcOf 42224) 40 =
    some ⟨⟨copyRegs (SNAP2 + 8136) (WIT + 8952) 528 42231, [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩ := by kernel_rfl
def chAt (lay : Nat) : Nat := if lay = 1 then 42235 else if lay = 2 then 42408 else 42557
def cCh (lay : Nat) : List (BitVec 32) := if lay = 1 then cCh1 else if lay = 2 then cCh2 else cCh3
def chSrc (lay : Nat) : Nat := SNAP2 + 8136 + 64 * (if lay = 1 then 66 + 7 else if lay = 2 then 116 + 6 else 165 + 6)
def chDst (lay : Nat) : Nat := lvDst lay + 16 * (if lay = 1 then 25 else 20)
theorem run_ch (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : symRun cfgC (cCh lay) (pcOf (chAt lay)) 40 =
    some ⟨⟨copyRegs (chSrc lay) (chDst lay) 344 (chAt lay + 7), [], []⟩, .c (pcOf 48000), .jump, 7, 7⟩ := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> kernel_rfl
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC copied zeroed copy_spec zero_spec)
set_option linter.unusedSimpArgs false
theorem and_mask (a m : Nat) (_hm : m ≤ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a % 2 ^ m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
  by_cases h : i < m <;> simp [h]
theorem copySet_spec {im : Image} {code : List (BitVec 32)} {p src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + 7), [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 src ∧
      t.getReg .x11 = BitVec.ofNat 64 dst ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧ t.getReg .x1 = pcOf (p + 7) ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h10, h11, h12⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
theorem copySetQ_spec {im : Image} {code : List (BitVec 32)} {p q src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + 7), [], []⟩, .c (pcOf q), .jump, 7, 7⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf q ∧ t.getReg .x10 = BitVec.ofNat 64 src ∧
      t.getReg .x11 = BitVec.ofNat 64 dst ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧ t.getReg .x1 = pcOf (p + 7) ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h10, h11, h12⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
theorem copySetL_spec {im : Image} {code : List (BitVec 32)} {p L src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + L), [], []⟩, .c (pcOf 42130), .jump, L, L⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s L L t ∧ t.pc = pcOf 42130 ∧ t.getReg .x10 = BitVec.ofNat 64 src ∧
      t.getReg .x11 = BitVec.ofNat 64 dst ∧ t.getReg .x12 = BitVec.ofNat 64 n ∧ t.getReg .x1 = pcOf (p + L) ∧
      RegsExcept s t [.x1, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hrun hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [copyRegs, rv_simp, RegFile.set, RegFile.get]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h10, h11, h12⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
theorem zeroSet_spec {im : Image} (hcode : CodeAt im (pcOf 42149) cZero2) (s : MachineState)
    (hpc : s.pc = pcOf 42149) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 42137 ∧ t.getReg .x11 = BitVec.ofNat 64 WZ ∧
      t.getReg .x12 = BitVec.ofNat 64 3124 ∧ t.getReg .x1 = pcOf 42154 ∧
      RegsExcept s t [.x1, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound run_zero2 hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [zeroRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [zeroRegs, rv_simp, RegFile.set, RegFile.get]
  · simp [zeroRegs, rv_simp, RegFile.set, RegFile.get]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h11, h12⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
theorem idx_spec {im : Image} (hcode : CodeAt im (pcOf 42231) cIdx) (s : MachineState) (hpc : s.pc = pcOf 42231) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 42235 ∧
      t.getReg .x22 = s.getMem (BitVec.ofNat 64 0x60) >>> 33 ∧ t.getReg .x18 = BitVec.ofNat 64 LPLAN ∧
      RegsExcept s t [.x18, .x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound RIdx (by exact hcode) s hpc (by simp [RIdx.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, RIdx.res, E.eval]
  · simp [RIdx.res, rv_simp]
  · simp [RIdx.res, rv_simp, LPLAN]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h18, h22⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
def rowAt (lay : Nat) : Nat := if lay = 1 then 42242 else if lay = 2 then 42415 else 42564
def rowLen (lay : Nat) : Nat := if lay = 1 then 5 else if lay = 2 then 4 else 3
def cRowL (lay : Nat) : List (BitVec 32) := if lay = 1 then cRow1 else if lay = 2 then cRow2 else cRow3
def lroute (lay idx : Nat) : Nat := if lay = 1 then idx / 2 ^ 12 % 128 else if lay = 2 then idx / 2 ^ 6 % 64 else idx % 64
theorem lroute_lt (lay idx : Nat) : lroute lay idx < 2 ^ lvH lay := by
  unfold lroute lvH; split_ifs <;> simp_all <;> exact Nat.mod_lt _ (by norm_num)
set_option maxRecDepth 20000 in
theorem row1_spec {im : Image} (hcode : CodeAt im (pcOf (rowAt 1)) (cRowL 1)) (s : MachineState)
    (hpc : s.pc = pcOf (rowAt 1)) (idx : Nat) (hidx : idx < 2 ^ 31) (h22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 LPLAN) :
    ∃ t, Steps im s (rowLen 1) (rowLen 1) t ∧ t.pc = pcOf (rowAt 1 + rowLen 1) ∧
      t.getReg .x19 = BitVec.ofNat 64 (lroute 1 idx) ∧
      t.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 1 (lroute 1 idx)) ∧
      RegsExcept s t [.x19, .x20] ∧ Frame s t (fun _ => False) := by
  have hi : idx < 2 ^ 64 := by omega
  have e19 : (RRow1.res.toState s).getReg .x19 = BitVec.ofNat 64 (lroute 1 idx) := by
    simp only [Result.toState_getReg, RRow1.res, RegFile.get, E.eval, BinOp.eval, h22]
    rw [show (12#64 : Word) = BitVec.ofNat 64 12 from rfl, ofNat_shr', show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      and_mask _ 7 (by norm_num)]
    unfold lroute
    simp only [if_true]
    rw [Nat.mod_eq_of_lt hi]; norm_num
  have e20 : (RRow1.res.toState s).getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 1 (lroute 1 idx)) := by
    have : (RRow1.res.toState s).getReg .x20 = (BitVec.ofNat 64 (lroute 1 idx) <<< ((3#64 : Word).toNat % 64)) +
        BitVec.ofNat 64 LPLAN + 512#64 := by
      rw [← e19]; simp only [Result.toState_getReg, RRow1.res, RegFile.get, E.eval, BinOp.eval, h18]
    rw [this, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shl, show (512#64 : Word) = BitVec.ofNat 64 512 from rfl, ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1; unfold lvRow; simp only [if_true]; ring
  refine ⟨_, symRun_sound RRow1 hcode s hpc (by simp [RRow1.res, rv_simp]), ?_, e19, e20, ?_, ?_⟩
  · rw [show rowAt 1 + rowLen 1 = 42247 by decide]; simp [Result.toState_pc, RRow1.res, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
set_option maxRecDepth 20000 in
theorem row2_spec {im : Image} (hcode : CodeAt im (pcOf (rowAt 2)) (cRowL 2)) (s : MachineState)
    (hpc : s.pc = pcOf (rowAt 2)) (idx : Nat) (hidx : idx < 2 ^ 31) (h22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 LPLAN) :
    ∃ t, Steps im s (rowLen 2) (rowLen 2) t ∧ t.pc = pcOf (rowAt 2 + rowLen 2) ∧
      t.getReg .x19 = BitVec.ofNat 64 (lroute 2 idx) ∧
      t.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 2 (lroute 2 idx)) ∧
      RegsExcept s t [.x19, .x20] ∧ Frame s t (fun _ => False) := by
  have hi : idx < 2 ^ 64 := by omega
  have e19 : (RRow2.res.toState s).getReg .x19 = BitVec.ofNat 64 (lroute 2 idx) := by
    simp only [Result.toState_getReg, RRow2.res, RegFile.get, E.eval, BinOp.eval, h22]
    rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, ofNat_shr', show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      and_mask _ 6 (by norm_num)]
    unfold lroute
    simp only [show (2 : Nat) ≠ 1 by decide, if_true, if_false]
    rw [Nat.mod_eq_of_lt hi]; norm_num
  have e20 : (RRow2.res.toState s).getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 2 (lroute 2 idx)) := by
    have : (RRow2.res.toState s).getReg .x20 = (BitVec.ofNat 64 (lroute 2 idx) <<< ((3#64 : Word).toNat % 64)) +
        BitVec.ofNat 64 LPLAN := by
      rw [← e19]; simp only [Result.toState_getReg, RRow2.res, RegFile.get, E.eval, BinOp.eval, h18]
    rw [this, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shl, ofNat_add_ofNat]
    congr 1; unfold lvRow; simp only [show (2 : Nat) ≠ 1 by decide, if_false]; ring
  refine ⟨_, symRun_sound RRow2 hcode s hpc (by simp [RRow2.res, rv_simp]), ?_, e19, e20, ?_, ?_⟩
  · rw [show rowAt 2 + rowLen 2 = 42419 by decide]; simp [Result.toState_pc, RRow2.res, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
set_option maxRecDepth 20000 in
theorem row3_spec {im : Image} (hcode : CodeAt im (pcOf (rowAt 3)) (cRowL 3)) (s : MachineState)
    (hpc : s.pc = pcOf (rowAt 3)) (idx : Nat) (hidx : idx < 2 ^ 31) (h22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 LPLAN) :
    ∃ t, Steps im s (rowLen 3) (rowLen 3) t ∧ t.pc = pcOf (rowAt 3 + rowLen 3) ∧
      t.getReg .x19 = BitVec.ofNat 64 (lroute 3 idx) ∧
      t.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 3 (lroute 3 idx)) ∧
      RegsExcept s t [.x19, .x20] ∧ Frame s t (fun _ => False) := by
  have hi : idx < 2 ^ 64 := by omega
  have e19 : (RRow3.res.toState s).getReg .x19 = BitVec.ofNat 64 (lroute 3 idx) := by
    simp only [Result.toState_getReg, RRow3.res, RegFile.get, E.eval, BinOp.eval, h22]
    rw [show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      and_mask _ 6 (by norm_num)]
    unfold lroute
    simp only [show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, if_false]
    norm_num
  have e20 : (RRow3.res.toState s).getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow 3 (lroute 3 idx)) := by
    have : (RRow3.res.toState s).getReg .x20 = (BitVec.ofNat 64 (lroute 3 idx) <<< ((3#64 : Word).toNat % 64)) +
        BitVec.ofNat 64 LPLAN := by
      rw [← e19]; simp only [Result.toState_getReg, RRow3.res, RegFile.get, E.eval, BinOp.eval, h18]
    rw [this, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shl, ofNat_add_ofNat]
    congr 1; unfold lvRow; simp only [show (3 : Nat) ≠ 1 by decide, if_false]; ring
  refine ⟨_, symRun_sound RRow3 hcode s hpc (by simp [RRow3.res, rv_simp]), ?_, e19, e20, ?_, ?_⟩
  · rw [show rowAt 3 + rowLen 3 = 42567 by decide]; simp [Result.toState_pc, RRow3.res, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · intro A _ _; rfl
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
theorem copyPhase {code : List (BitVec 32)} {p src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + 7), [], []⟩, .c (pcOf 42130), .jump, 7, 7⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) (hn : 0 < n) (hn' : n < 2 ^ 32) (hs : src % 8 = 0)
    (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∃ t, Steps im s (7 + (6 * n + 1)) (7 + (6 * n + 1)) t ∧ t.pc = pcOf (p + 7) ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if dst ≤ A ∧ A < dst + 8 * n ∧ (A - dst) % 8 = 0 then s.getMem (BitVec.ofNat 64 (src + (A - dst)))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u10, u11, u12, u1, ru, fu⟩ := copySet_spec hcode hrun s hpc
  obtain ⟨t, st, pt, rt, mt⟩ := copy_spec hc u pu src dst n (p + 7) u10 u11 u12 u1 hn hn' hs hs' hd hd' hov
  refine ⟨t, su.trans st, pt, (ru.trans rt).mono (by decide), fun A hA => ?_⟩
  rw [mt A hA]
  unfold copied
  split
  · rw [fu _ (by omega) (fun h => h)]
  · rw [fu _ hA (fun h => h)]
/-- Pairing stage 1: a lower layer's chain area is written by the pair copy block 48000 (called with `jal ra`). -/
theorem pairPhase {code : List (BitVec 32)} {p src dst : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst 344 (p + 7), [], []⟩, .c (pcOf 48000), .jump, 7, 7⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) (hs : src % 8 = 0) (hs' : src + 128 * 22 ≤ MEMORY_BYTES)
    (hd : dst % 8 = 0) (hov : dst + 104 * 22 ≤ src) :
    ∃ t, Steps im s (7 + 258) (7 + 258) t ∧ t.pc = pcOf (p + 7) ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        PairCopy.pairCopyMem (fun B => s.getMem (BitVec.ofNat 64 B)) src dst A := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u10, u11, u12, u1, ru, fu⟩ := copySetQ_spec hcode hrun s hpc
  obtain ⟨t, st, pt, rt, mt⟩ := PairCopy.pairCopy_spec hc.pair u pu src dst (p + 7) u10 u11 u1 hs hs' hd hov
  refine ⟨t, su.trans st, pt, (ru.trans rt).mono (by decide), fun A hA => ?_⟩
  rw [mt A hA]
  have hso : PairCopy.srcOff ((A - dst) % 104) ≤ 120 := by unfold PairCopy.srcOff; split_ifs <;> omega
  unfold PairCopy.pairCopyMem PairCopy.pcMem
  split_ifs <;> (beta_reduce; rw [fu _ (by omega) (fun h => h)])
theorem copyPhaseL {code : List (BitVec 32)} {p L src dst n : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 =
      some ⟨⟨copyRegs src dst n (p + L), [], []⟩, .c (pcOf 42130), .jump, L, L⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) (hn : 0 < n) (hn' : n < 2 ^ 32) (hs : src % 8 = 0)
    (hs' : src + 8 * n ≤ MEMORY_BYTES) (hd : dst % 8 = 0) (hd' : dst + 8 * n ≤ MEMORY_BYTES)
    (hov : dst ≤ src ∨ src + 8 * n ≤ dst) :
    ∃ t, Steps im s (L + (6 * n + 1)) (L + (6 * n + 1)) t ∧ t.pc = pcOf (p + L) ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if dst ≤ A ∧ A < dst + 8 * n ∧ (A - dst) % 8 = 0 then s.getMem (BitVec.ofNat 64 (src + (A - dst)))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  obtain ⟨u, su, pu, u10, u11, u12, u1, ru, fu⟩ := copySetL_spec hcode hrun s hpc
  obtain ⟨t, st, pt, rt, mt⟩ := copy_spec hc u pu src dst n (p + L) u10 u11 u12 u1 hn hn' hs hs' hd hd' hov
  refine ⟨t, su.trans st, pt, (ru.trans rt).mono (by decide), fun A hA => ?_⟩
  rw [mt A hA]
  unfold copied
  split
  · rw [fu _ (by omega) (fun h => h)]
  · rw [fu _ hA (fun h => h)]
theorem jump1_spec {code : List (BitVec 32)} {p q : Nat} (hcode : CodeAt im (pcOf p) code)
    (hrun : symRun cfgC code (pcOf p) 40 = some ⟨⟨RegFile.init, [], []⟩, .c (pcOf q), .jump, 1, 1⟩)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf q ∧ RegsExcept s t [] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound hrun hcode s hpc (by simp [rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · intro r _; rw [Result.toState_getReg]; cases r <;> rfl
  · intro A; simp [rv_simp]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem hold_spec (c : Nat) (hc9 : c < 9) (s : MachineState) (hpc : s.pc = pcOf (holdPc c)) (f : Nat) (hf2 : f < 2)
    (hf : s.getMem (BitVec.ofNat 64 (Compact.holdAt c + 16)) = BitVec.ofNat 64 f) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf (holdPc c + 12) ∧ RegsExcept s t [.x6, .x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = hdst c + 144 * f + 8 then s.getMem (BitVec.ofNat 64 (Compact.holdAt c + 8))
        else if A = hdst c + 144 * f then s.getMem (BitVec.ofNat 64 (Compact.holdAt c))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hb : (hbE c).eval s = BitVec.ofNat 64 (144 * f) := by
    simp only [hbE, hfE, E.eval, BinOp.eval, hf]
    rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl <;> decide
  have hd : hdst c + 160 ≤ 9472 ∧ 1216 ≤ hdst c ∧ hdst c % 16 = 0 := by unfold hdst; omega
  have hv : ∀ x, x + 8 ≤ 16777216 → x % 8 = 0 → accessValid (BitVec.ofNat 64 x) 8 = true := by
    intro x h1 h2
    rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by rw [hM]; omega, h2⟩
  have hobl : Oblig.all s (holdObl c) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [holdObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat]; exact hv _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat]; exact hv _ (by omega) (by omega)
  refine ⟨_, symRun_sound (run_hold c hc9) (code_cHold hc c hc9) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h6, h13, h28, h29, h30, h31⟩ := hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    simp only [Result.toState_getMem, holdSym, memEval_cons, memEval_nil, Addr.eval, hb, E.eval, ofNat_add_ofNat]
    have hX1 : 144 * f + (hdst c + 8) < 2 ^ 64 := by omega
    have hX0 : 144 * f + hdst c < 2 ^ 64 := by omega
    by_cases e1 : A = hdst c + 144 * f + 8
    · rw [if_pos (by rw [e1]; congr 1; omega), if_pos e1]
    · rw [if_neg (fun h => e1 (by have := (ofNat_inj hA hX1).mp h; omega)), if_neg e1]
      by_cases e2 : A = hdst c + 144 * f
      · rw [if_pos (by rw [e2]; congr 1; omega), if_pos e2]
      · rw [if_neg (fun h => e2 (by have := (ofNat_inj hA hX0).mp h; omega)), if_neg e2]
end
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
def sibS (lay r j : Nat) : Nat := 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2)
def padS (lay r j : Nat) : Nat := 16 * plan lay r j + 32
theorem sibOff_eq (b : Nat) (hb : b < 2) : SigGolfCandidate.T3M.sibOff b = 48 * (1 - b) := by
  unfold SigGolfCandidate.T3M.sibOff; split <;> omega
theorem lv_disj (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (r : Nat) (hr : r < 2 ^ lvH lay) (j j' : Nat)
    (hj : j < lvH lay) (hj' : j' < lvH lay) (hne : j ≠ j') :
    sibS lay r j ≠ sibS lay r j' ∧ sibS lay r j ≠ padS lay r j' ∧ padS lay r j ≠ padS lay r j' := by
  obtain ⟨h1, h4⟩ := hl
  have hb : ∀ i, r / 2 ^ i % 2 < 2 := fun i => Nat.mod_lt _ (by norm_num)
  have key : ∀ L : SigGolfCandidate.T3.Layer, L.val = lay → L.val ≠ 0 →
      SigGolfCandidate.T3.height L = lvH lay → (∀ i, plan lay r i = (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan L r).getD i 0) →
      sibS lay r j ≠ sibS lay r j' ∧ sibS lay r j ≠ padS lay r j' ∧ padS lay r j ≠ padS lay r j' := by
    intro L hL hL0 hH hP
    have hr' : r < 2 ^ SigGolfCandidate.T3.height L := by rw [hH]; exact hr
    have hj1 : j < SigGolfCandidate.T3.height L := by rw [hH]; exact hj
    have hj2 : j' < SigGolfCandidate.T3.height L := by rw [hH]; exact hj'
    have d1 := ClaudeWCT.W9.Machine.Expand.OldW.lower_sib_disjoint L hL0 r hr' j hj1 j' hj2 hne
    have d2 := ClaudeWCT.W9.Machine.Expand.OldW.lower_pad_disjoint L hL0 r hr' j' hj2 j hj1
    have d3 := ClaudeWCT.W9.Machine.Expand.OldW.lower_pad_pad_disjoint L hL0 r hr' j hj1 j' hj2 hne
    unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot at d1 d2
    rw [sibOff_eq _ (hb j), sibOff_eq _ (hb j')] at d1
    rw [sibOff_eq _ (hb j)] at d2
    unfold sibS padS
    rw [hP j, hP j']
    refine ⟨?_, ?_, ?_⟩ <;> omega
  interval_cases lay
  · exact key 1 rfl (by decide) rfl (fun i => rfl)
  · exact key 2 rfl (by decide) rfl (fun i => rfl)
  · exact key 3 rfl (by decide) rfl (fun i => rfl)
def lvHit (lay r j p : Nat) : Prop :=
  p = sibS lay r j ∨ p = sibS lay r j + 8 ∨ p = padS lay r j ∨ p = padS lay r j + 8
instance (lay r j p : Nat) : Decidable (lvHit lay r j p) := by unfold lvHit; infer_instance
def lvsMem (M : Nat → Word) (lay r L : Nat) (A : Nat) : Word :=
  if lvDst lay ≤ A then
    match (List.range L).find? (fun j => decide (lvHit lay r j (A - lvDst lay))) with
    | some j => M (lvSrc lay j + (A - lvDst lay - 16 * plan lay r j))
    | none => M A
  else M A
theorem lvs_find_some {p : Nat → Bool} {L l : Nat} (h : (List.range L).find? p = some l) : l < L ∧ p l = true :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), List.find?_some h⟩
theorem lvs_find_succ (p : Nat → Bool) (L : Nat) :
    (List.range (L + 1)).find? p = match (List.range L).find? p with
      | some l => some l
      | none => if p L then some L else none := by
  rw [List.range_succ, List.find?_append]
  cases h : (List.range L).find? p with
  | some l => rfl
  | none => simp only [List.find?_cons, List.find?_nil, Option.none_or]; cases hp : p L <;> simp [hp]
theorem plan_mod16 (lay r j : Nat) : sibS lay r j % 16 = 0 ∧ padS lay r j % 16 = 0 := by
  unfold sibS padS
  have : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  constructor <;> omega
theorem sibS_ne_padS (lay r j : Nat) : sibS lay r j ≠ padS lay r j := by
  unfold sibS padS
  have : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega
theorem lvsMem_succ (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (r : Nat) (hr : r < 2 ^ lvH lay)
    (L : Nat) (hL : L < lvH lay) (A : Nat) :
    lvsMem M lay r (L + 1) A =
      if A = lvDst lay + sibS lay r L + 8 then M (lvSrc lay L + 48 * (1 - r / 2 ^ L % 2) + 8)
      else if A = lvDst lay + sibS lay r L then M (lvSrc lay L + 48 * (1 - r / 2 ^ L % 2))
      else if A = lvDst lay + padS lay r L + 8 then M (lvSrc lay L + 40)
      else if A = lvDst lay + padS lay r L then M (lvSrc lay L + 32)
      else lvsMem M lay r L A := by
  have hm := plan_mod16 lay r L
  have hsp := sibS_ne_padS lay r L
  unfold lvsMem
  by_cases hA : lvDst lay ≤ A
  · rw [if_pos hA, if_pos hA, lvs_find_succ]
    cases h : (List.range L).find? (fun j => decide (lvHit lay r j (A - lvDst lay))) with
    | some l =>
      obtain ⟨hl', hp⟩ := lvs_find_some h
      have hp' : lvHit lay r l (A - lvDst lay) := of_decide_eq_true hp
      unfold lvHit at hp'
      have hd := lv_disj lay hl r hr l L (by omega) hL (by omega)
      have hd' := lv_disj lay hl r hr L l hL (by omega) (by omega)
      have hml := plan_mod16 lay r l
      simp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    | none =>
      simp only
      by_cases q1 : A = lvDst lay + sibS lay r L + 8
      · rw [if_pos (decide_eq_true (by unfold lvHit; omega)), if_pos q1]
        simp only
        congr 1; unfold sibS at q1; omega
      · rw [if_neg q1]
        by_cases q2 : A = lvDst lay + sibS lay r L
        · rw [if_pos (decide_eq_true (by unfold lvHit; omega)), if_pos q2]
          simp only
          congr 1; unfold sibS at q2; omega
        · rw [if_neg q2]
          by_cases q3 : A = lvDst lay + padS lay r L + 8
          · rw [if_pos (decide_eq_true (by unfold lvHit; omega)), if_pos q3]
            simp only
            congr 1; unfold padS at q3; omega
          · rw [if_neg q3]
            by_cases q4 : A = lvDst lay + padS lay r L
            · rw [if_pos (decide_eq_true (by unfold lvHit; omega)), if_pos q4]
              simp only
              congr 1; unfold padS at q4; omega
            · rw [if_neg q4, if_neg (show ¬ decide (lvHit lay r L (A - lvDst lay)) = true from fun h => by have := of_decide_eq_true h; unfold lvHit at this; omega)]
  · rw [if_neg hA, if_neg hA, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
def pathTop (lay : Nat) : Nat := 16 * (if lay = 1 then 25 else 20)
theorem sibS_padS_lt (lay r j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay) (hj : j < lvH lay) :
    sibS lay r j + 16 ≤ pathTop lay ∧ padS lay r j + 16 ≤ pathTop lay := by
  have h := (plan_ok lay r j hl hr hj).2
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold sibS padS pathTop; split_ifs at h ⊢ <;> constructor <;> omega
theorem pathTop_le (lay : Nat) : pathTop lay ≤ 16 * 25 := by unfold pathTop; split_ifs <;> omega
theorem lvsMem_out (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (r : Nat) (hr : r < 2 ^ lvH lay)
    (L : Nat) (hL : L ≤ lvH lay) (A : Nat) (hA : A < lvDst lay ∨ lvDst lay + pathTop lay ≤ A) :
    lvsMem M lay r L A = M A := by
  unfold lvsMem
  split
  · cases h : (List.range L).find? (fun j => decide (lvHit lay r j (A - lvDst lay))) with
    | none => rfl
    | some l =>
      obtain ⟨hl', hp⟩ := lvs_find_some h
      have hp' : lvHit lay r l (A - lvDst lay) := of_decide_eq_true hp
      unfold lvHit at hp'
      have := sibS_padS_lt lay r l hl hr (by omega)
      omega
  · rfl
theorem lvsMem_zero (M : Nat → Word) (lay r A : Nat) : lvsMem M lay r 0 A = M A := by
  unfold lvsMem; split <;> rfl
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem lvs_spec (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (u : MachineState) (M0 : Nat → Word)
    (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A) (hpc : u.pc = pcOf (lvAt lay 0)) (r : Nat)
    (hr : r < 2 ^ lvH lay) (h19 : u.getReg .x19 = BitVec.ofNat 64 r)
    (h20 : u.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt u) :
    ∀ L ≤ lvH lay - 1, ∃ t, Steps im u (23 * L) (23 * L) t ∧ t.pc = pcOf (lvAt lay L) ∧
      RegsExcept u t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = lvsMem M0 lay r L A := by
  have hD : 0x800 + 11648 ≤ lvDst lay ∧ lvDst lay + 16 * 25 ≤ 0x800 + 20944 := by
    unfold lvDst; split_ifs <;> omega
  have hLP : LPLAN = 0xff9400 := rfl
  intro L hL
  induction L with
  | zero => exact ⟨u, Steps.refl u, by simpa [lvAt] using hpc, RegsExcept.refl u _, fun A hA => by
      rw [hM A hA, lvsMem_zero]⟩
  | succ L ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hpt : LPlanAt t := fun k hk => by
      have := pathTop_le lay
      rw [mt _ (by omega), lvsMem_out M0 lay hl r hr L (by omega) _ (Or.inr (by omega)), ← hM _ (by omega)]
      exact hp k hk
    obtain ⟨t', st', pt', rt', mt'⟩ := lv_spec hc lay L hl (by omega) t pt r hr
      (by rw [rt.get (by decide), h19]) (by rw [rt.get (by decide), h20]) hpt
    have hS : 0x310000 ≤ lvSrc lay L ∧ lvSrc lay L + 64 ≤ 0x310000 + 21832 := by
      unfold lvSrc; unfold lvH at hL; split_ifs at * <;> omega
    have hb : r / 2 ^ L % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hpt23 := pathTop_le lay
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), by rw [pt']; unfold lvAt; split_ifs <;> ring_nf,
      (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    rw [mt' A hA, lvsMem_succ M0 lay hl r hr L (by omega) A]
    have e1 := mt (lvSrc lay L + 48 * (1 - r / 2 ^ L % 2) + 8) (by omega)
    have e2 := mt (lvSrc lay L + 48 * (1 - r / 2 ^ L % 2)) (by omega)
    have e3 := mt (lvSrc lay L + 40) (by omega)
    have e4 := mt (lvSrc lay L + 32) (by omega)
    rw [lvsMem_out M0 lay hl r hr L (by omega) _ (Or.inr (by omega))] at e1 e2 e3 e4
    rw [e1, e2, e3, e4, mt A hA]
    unfold sibS padS
    simp only [Nat.add_assoc, Nat.reduceAdd]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC copied zeroed copy_spec zero_spec)
set_option linter.unusedSimpArgs false
/-- Slot of coordinate `c`'s top sibling (flag clamped to `0, 1`; the honest flag is `1 - bit6`). -/
def hslot (M : Nat → Word) (c : Nat) : Nat := hdst c + 144 * min (M (Compact.holdAt c + 16)).toNat 1
/-- Memory after the first `Q` hold placements over `M` (hold slots read from `M`). -/
def plMem (M : Nat → Word) : Nat → Nat → Word
  | 0, A => M A
  | Q + 1, A => if A = hslot M Q + 8 then M (Compact.holdAt Q + 8)
      else if A = hslot M Q then M (Compact.holdAt Q) else plMem M Q A
theorem hslot_bound (M : Nat → Word) (c : Nat) : hdst c ≤ hslot M c ∧ hslot M c ≤ hdst c + 144 := by
  unfold hslot; have := Nat.min_le_right (M (Compact.holdAt c + 16)).toNat 1; constructor <;> omega
theorem plMem_out (M : Nat → Word) (Q : Nat) (hQ : Q ≤ 9) (A : Nat) (hA : A < 1152 ∨ 11048 ≤ A) :
    plMem M Q A = M A := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    have hb := hslot_bound M Q
    have hd : hdst Q + 160 ≤ 9472 ∧ 1216 ≤ hdst Q := by unfold hdst; omega
    simp only [plMem]
    rw [if_neg (by omega), if_neg (by omega), ih (by omega)]
/-- The nine region copies of P_final: region `c` (112 words) from the staging snapshot to `10152 - 896 c`. -/
def regsMem (M : Nat → Word) (Q : Nat) (A : Nat) : Word :=
  if 0 < Q ∧ 11048 - 896 * Q ≤ A ∧ A < 11048 ∧ A % 8 = 0 then
    M (SNAP2 + 64 + 896 * ((11047 - A) / 896) + (A - (10152 - 896 * ((11047 - A) / 896))))
  else M A
theorem regsMem_succ (M : Nat → Word) (Q : Nat) (hQ : Q < 9) (A : Nat) :
    (if 10152 - 896 * Q ≤ A ∧ A < 10152 - 896 * Q + 8 * 112 ∧ (A - (10152 - 896 * Q)) % 8 = 0 then
      M (SNAP2 + 64 + 896 * Q + (A - (10152 - 896 * Q))) else regsMem M Q A) = regsMem M (Q + 1) A := by
  unfold regsMem
  by_cases h1 : 10152 - 896 * Q ≤ A ∧ A < 10152 - 896 * Q + 8 * 112 ∧ (A - (10152 - 896 * Q)) % 8 = 0
  · rw [if_pos h1, if_pos (by omega), show (11047 - A) / 896 = Q by omega]
  · rw [if_neg h1]
    by_cases h2 : 0 < Q ∧ 11048 - 896 * Q ≤ A ∧ A < 11048 ∧ A % 8 = 0
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]
def ctrMem (M : Nat → Word) (A : Nat) : Word :=
  if 1184 ≤ A ∧ A < 1184 + 8 * 2 ∧ (A - 1184) % 8 = 0 then M (SNAP2 + 32 + (A - 1184)) else M A
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem pregs_spec (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (pregAt 0)) :
    ∀ Q ≤ 9, ∃ t, Steps im u (679 * Q) (679 * Q) t ∧ t.pc = pcOf (pregAt Q) ∧
      RegsExcept u t [.x1, .x6, .x10, .x11, .x12] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = regsMem M0 Q A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  intro Q hQ
  induction Q with
  | zero => exact ⟨u, Steps.refl u, by simpa using hpc, RegsExcept.refl u _, fun A hA => by
      rw [hM A hA]; unfold regsMem; rw [if_neg (by omega)]⟩
  | succ Q ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    have hrun := run_preg Q (by omega)
    obtain ⟨t', st', pt', rt', mt'⟩ := copyPhaseL hc (code_cPReg hc Q (by omega)) hrun t pt
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), by rw [pt']; unfold pregAt; congr 1,
      (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    rw [mt' A hA, ← regsMem_succ M0 Q (by omega) A]
    by_cases h1 : 10152 - 896 * Q ≤ A ∧ A < 10152 - 896 * Q + 8 * 112 ∧ (A - (10152 - 896 * Q)) % 8 = 0
    · rw [if_pos h1, if_pos h1, mt _ (by omega)]
      unfold regsMem
      rw [if_neg (by omega)]
    · rw [if_neg h1, if_neg h1, mt A hA]
set_option maxRecDepth 20000 in
theorem holds_spec (u : MachineState) (M0 : Nat → Word) (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A)
    (hpc : u.pc = pcOf (holdPc 0)) (hfl : ∀ c < 9, ∃ f < 2, M0 (Compact.holdAt c + 16) = BitVec.ofNat 64 f) :
    ∀ Q ≤ 9, ∃ t, Steps im u (12 * Q) (12 * Q) t ∧ t.pc = pcOf (holdPc Q) ∧
      RegsExcept u t [.x6, .x13, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = plMem M0 Q A := by
  intro Q hQ
  induction Q with
  | zero => exact ⟨u, Steps.refl u, by simpa using hpc, RegsExcept.refl u _, fun A hA => hM A hA⟩
  | succ Q ih =>
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    obtain ⟨f, hf2, hf⟩ := hfl Q (by omega)
    have hH : Compact.holdAt Q = 0x380000 + 32 * Q := rfl
    have hth : ∀ j < 24, t.getMem (BitVec.ofNat 64 (Compact.holdAt Q + j)) = M0 (Compact.holdAt Q + j) :=
      fun j hj => by rw [mt _ (by omega), plMem_out M0 Q (by omega) _ (Or.inr (by omega))]
    have hth0 : t.getMem (BitVec.ofNat 64 (Compact.holdAt Q)) = M0 (Compact.holdAt Q) := by
      rw [mt _ (by omega), plMem_out M0 Q (by omega) _ (Or.inr (by omega))]
    obtain ⟨t', st', pt', rt', mt'⟩ := hold_spec hc Q (by omega) t pt f hf2 (by rw [hth 16 (by omega), hf])
    have hs : hslot M0 Q = hdst Q + 144 * f := by
      unfold hslot; rw [hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; congr 2; omega
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), by rw [pt']; unfold holdPc; congr 1,
      (rt.trans rt').mono (by decide), fun A hA => ?_⟩
    rw [mt' A hA, hth 8 (by omega), hth0, mt A hA]
    simp only [plMem, hs]
end
/-- Pairing stage 1: the lower chain area after the pair copy block (writes only in `[chDst, chDst + 2248)`). -/
def chMem (M : Nat → Word) (lay : Nat) (A : Nat) : Word := PairCopy.pairCopyMem M (chSrc lay) (chDst lay) A
theorem chMem_out (M : Nat → Word) (lay A : Nat) (h : A < chDst lay ∨ chDst lay + 2248 ≤ A) : chMem M lay A = M A := by
  simp only [chMem, PairCopy.pairCopyMem, PairCopy.pcMem]
  split_ifs <;> first | rfl | omega
/-- C3 (FULL, E6): offset of the root window's tweak high word (LE64 1) in a lower path area. -/
def rootOff (lay r : Nat) : Nat := 16 * plan lay r (rootJ lay) + 24
theorem rootOff_lt (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (r : Nat) (hr : r < 2 ^ lvH lay) :
    rootOff lay r + 8 ≤ pathTop lay ∧ rootOff lay r % 8 = 0 := by
  have hj : rootJ lay < lvH lay := by obtain ⟨h1, h4⟩ := hl; unfold rootJ lvH; split_ifs <;> omega
  have h := (plan_ok lay r (rootJ lay) hl hr hj).2
  unfold rootOff pathTop; split_ifs at h ⊢ <;> omega
def layMem (M : Nat → Word) (lay idx : Nat) (A : Nat) : Word :=
  if A = lvDst lay + rootOff lay (lroute lay idx) then 1#64
  else lvsMem (chMem M lay) lay (lroute lay idx) (lvH lay) A
def layLen (lay : Nat) : Nat := 265 + rowLen lay + 23 * lvH lay + 4
theorem chDst_eq (lay : Nat) : chDst lay = lvDst lay + pathTop lay := by unfold chDst pathTop; rfl
theorem layMem_out (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (idx A : Nat)
    (hA : A < lvDst lay ∨ chDst lay + 2248 ≤ A) : layMem M lay idx A = M A := by
  have hA' := hA
  have hce := chDst_eq lay
  have hro := rootOff_lt lay hl (lroute lay idx) (lroute_lt lay idx)
  rw [chDst_eq] at hA'
  unfold layMem
  rw [if_neg (by omega), lvsMem_out _ lay hl _ (lroute_lt lay idx) _ le_rfl _ (by omega)]
  rw [chMem_out _ _ _ (by omega)]
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem layer_spec (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (u : MachineState) (M0 : Nat → Word)
    (hM : ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = M0 A) (hpc : u.pc = pcOf (chAt lay)) (idx : Nat)
    (hidx : idx < 2 ^ 31) (h22 : u.getReg .x22 = BitVec.ofNat 64 idx) (h18 : u.getReg .x18 = BitVec.ofNat 64 LPLAN)
    (hp : LPlanAt u) :
    ∃ t, Steps im u (layLen lay) (layLen lay) t ∧ t.pc = pcOf (lvAt lay (lvH lay)) ∧
      RegsExcept u t [.x1, .x6, .x10, .x11, .x12, .x19, .x20, .x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = layMem M0 lay idx A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hLP : LPLAN = 0xff9400 := rfl
  obtain ⟨h1, h4⟩ := hl
  have hcode : CodeAt im (pcOf (chAt lay)) (cCh lay) := by
    interval_cases lay
    · exact code_cCh1 hc
    · exact code_cCh2 hc
    · exact code_cCh3 hc
  have hsrc : chSrc lay % 8 = 0 ∧ 0x310000 + 8136 ≤ chSrc lay ∧ chSrc lay + 2752 ≤ 0x310000 + 21832 := by
    interval_cases lay <;> decide
  have hdst : chDst lay % 8 = 0 ∧ chDst lay + 2248 ≤ 0x800 + 20960 ∧
      lvDst lay % 8 = 0 ∧ 0x800 + 13176 ≤ lvDst lay := by
    interval_cases lay <;> decide
  obtain ⟨u1, s1, p1, r1, m1⟩ := pairPhase hc hcode (run_ch lay ⟨h1, h4⟩) u hpc hsrc.1 (by omega) hdst.1
    (by omega)
  have hm1 : ∀ A < 2 ^ 64, u1.getMem (BitVec.ofNat 64 A) = chMem M0 lay A := fun A hA => by
    rw [m1 A hA]
    have hso : PairCopy.srcOff ((A - chDst lay) % 104) ≤ 120 := by unfold PairCopy.srcOff; split_ifs <;> omega
    simp only [chMem, PairCopy.pairCopyMem, PairCopy.pcMem]
    split_ifs <;> rw [hM _ (by omega)]
  have hp1 : LPlanAt u1 := fun k hk => by
    rw [hm1 _ (by omega), chMem_out _ _ _ (Or.inr (by unfold LPLAN; omega)), ← hM _ (by omega)]; exact hp k hk
  have hrow : ∀ u1 : MachineState, u1.pc = pcOf (chAt lay + 7) → u1.getReg .x22 = BitVec.ofNat 64 idx →
      u1.getReg .x18 = BitVec.ofNat 64 LPLAN →
      ∃ t, Steps im u1 (rowLen lay) (rowLen lay) t ∧ t.pc = pcOf (rowAt lay + rowLen lay) ∧
        t.getReg .x19 = BitVec.ofNat 64 (lroute lay idx) ∧
        t.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay (lroute lay idx)) ∧
        RegsExcept u1 t [.x19, .x20] ∧ Frame u1 t (fun _ => False) := by
    intro u1 hp1 h22' h18'
    interval_cases lay
    · exact row1_spec (code_cRow1 hc) u1 (by rw [hp1]; rfl) idx hidx h22' h18'
    · exact row2_spec (code_cRow2 hc) u1 (by rw [hp1]; rfl) idx hidx h22' h18'
    · exact row3_spec (code_cRow3 hc) u1 (by rw [hp1]; rfl) idx hidx h22' h18'
  obtain ⟨u2, s2, p2, x19, x20, r2, f2⟩ := hrow u1 p1 (by rw [r1.get (by decide), h22])
    (by rw [r1.get (by decide), h18])
  have hm2 : ∀ A < 2 ^ 64, u2.getMem (BitVec.ofNat 64 A) = chMem M0 lay A := fun A hA => by
    rw [f2 A hA (fun h => h), hm1 A hA]
  have hp2 : LPlanAt u2 := fun k hk => by rw [f2 _ (by unfold LPLAN; omega) (fun h => h)]; exact hp1 k hk
  obtain ⟨u3, s3, p3, r3, m3⟩ := lvs_spec hc lay ⟨h1, h4⟩ u2 (chMem M0 lay) hm2
    (by rw [p2]; interval_cases lay <;> rfl) (lroute lay idx) (lroute_lt lay idx) x19 x20 hp2 (lvH lay - 1) le_rfl
  have hjr : rootJ lay = lvH lay - 1 := by unfold rootJ lvH; split_ifs <;> omega
  have hH1 : 1 ≤ lvH lay := by unfold lvH; split_ifs <;> omega
  have hDu : lvDst lay ≤ 0x800 + 18392 := by unfold lvDst; split_ifs <;> omega
  have hr := lroute_lt lay idx
  have hpt := pathTop_le lay
  have hpt3 : LPlanAt u3 := fun k hk => by
    rw [m3 _ (by omega), lvsMem_out _ lay ⟨h1, h4⟩ _ hr _ (by omega) _ (Or.inr (by unfold LPLAN; omega)), ← hm2 _ (by omega)]
    exact hp2 k hk
  obtain ⟨u4, s4, p4, r4, m4⟩ := lvRoot_spec hc lay ⟨h1, h4⟩ u3 (by rw [p3, hjr]) (lroute lay idx) hr
    (by rw [r3.get (by decide), x19]) (by rw [r3.get (by decide), x20]) hpt3
  refine ⟨u4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold layLen; omega) (by unfold layLen; omega),
    by rw [p4, hjr]; congr 1; unfold lvAt; split_ifs <;> omega,
    (((r1.trans r2).trans r3).trans r4).mono (by decide), fun A hA => ?_⟩
  rw [← hjr] at m3
  have hS : 0x310000 ≤ lvSrc lay (rootJ lay) ∧ lvSrc lay (rootJ lay) + 64 ≤ 0x310000 + 21832 := by
    unfold lvSrc rootJ; split_ifs <;> omega
  have hb : lroute lay idx / 2 ^ rootJ lay % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have e1 := m3 (lvSrc lay (rootJ lay) + 48 * (1 - lroute lay idx / 2 ^ rootJ lay % 2) + 8) (by omega)
  have e2 := m3 (lvSrc lay (rootJ lay) + 48 * (1 - lroute lay idx / 2 ^ rootJ lay % 2)) (by omega)
  have e3 := m3 (lvSrc lay (rootJ lay) + 40) (by omega)
  have e4 := m3 (lvSrc lay (rootJ lay) + 32) (by omega)
  rw [lvsMem_out _ lay ⟨h1, h4⟩ _ hr _ (by omega) _ (Or.inr (by omega))] at e1 e2 e3 e4
  have hsucc := lvsMem_succ (chMem M0 lay) lay ⟨h1, h4⟩ _ hr (rootJ lay) (by omega) A
  rw [show rootJ lay + 1 = lvH lay by omega] at hsucc
  rw [m4 A hA, e1, e2, e3, e4, m3 A hA]
  unfold layMem rootOff
  rw [hsucc]
  unfold sibS padS
  simp only [Nat.add_assoc, Nat.reduceAdd]
end
/-- Pairing stage 1: the staged rho / digest-counter words now sit 16 bytes higher (abs 23008 .. 23040). -/
def tailMem (M : Nat → Word) (A : Nat) : Word :=
  if A = WIT + 20984 then LoadKind.wu.fromWord (M (SNAP2 + 16)) 0
  else if A = WIT + 20976 then 0
  else if A = WIT + 20968 then M (SNAP2 + 8)
  else if A = WIT + 20960 then M SNAP2
  else M A
set_option maxRecDepth 20000 in
theorem tail_spec {im : Image} (hcode : CodeAt im (pcOf 42705) cTail) (s : MachineState) (hpc : s.pc = pcOf 42705) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 42716 ∧ RegsExcept s t [.x5, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = tailMem (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  refine ⟨_, symRun_sound RTail hcode s hpc (by simp [RTail.res, rv_simp]), ?_, ?_, fun A hA => ?_⟩
  · simp [Result.toState_pc, RTail.res, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, e⟩ := hr
    rw [Result.toState_getReg]; cases r <;> first | rfl | (exfalso; simp_all)
  · have key : ∀ c : Nat, c < 2 ^ 64 → (BitVec.ofNat 64 A = BitVec.ofNat 64 c ↔ A = c) := fun c hc => ofNat_inj hA hc
    simp only [Result.toState_getMem, RTail.res, memEval_cons, memEval_nil, Addr.eval, E.eval, UnOp.eval,
      key 23032 (by norm_num), key 23024 (by norm_num), key 23016 (by norm_num), key 23008 (by norm_num)]
    unfold tailMem
    simp only [show WIT = 0x800 from rfl, show SNAP2 = 0x310000 from rfl, Nat.reduceAdd]
    rfl
def snapMem (M : Nat → Word) (A : Nat) : Word :=
  if SNAP2 ≤ A ∧ A < SNAP2 + 8 * 2729 ∧ (A - SNAP2) % 8 = 0 then M (WIT + (A - SNAP2)) else M A
/-- Zeroing of 3124 words from `WZ` (to `WIT + 19248`; everything above is rewritten by the layer-3 chain copy
and the tail). -/
def zMem (M : Nat → Word) (A : Nat) : Word :=
  if WZ ≤ A ∧ A < WZ + 8 * 3124 ∧ (A - WZ) % 8 = 0 then 0 else M A
def topMem (M : Nat → Word) (A : Nat) : Word :=
  if WIT + 8952 ≤ A ∧ A < WIT + 8952 + 8 * 528 ∧ (A - (WIT + 8952)) % 8 = 0 then M (SNAP2 + 8136 + (A - (WIT + 8952)))
  else M A
/-- Nested FTS (r1-1): memory after the zeroing, the L3 counter copy, the nine region copies and the nine hold
placements of P_final. -/
def stMem (M : Nat → Word) (A : Nat) : Word := plMem (regsMem (ctrMem (zMem (snapMem M))) 9) 9 A
def run2Mem (M : Nat → Word) (idx : Nat) (A : Nat) : Word :=
  tailMem (layMem (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) 3 idx) A
theorem stMem_out (M : Nat → Word) (A : Nat) (hA : A < WZ ∨ SNAP2 + 8 * 2729 ≤ A) : stMem M A = M A := by
  have hW : WZ = 0x480 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (by omega)]
  unfold regsMem ctrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem stMem_snap (M : Nat → Word) (x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    stMem M (SNAP2 + x) = M (WIT + x) := by
  have hW : WZ = 0x480 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  unfold stMem
  rw [plMem_out _ 9 le_rfl _ (by omega)]
  unfold regsMem ctrMem zMem snapMem
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), show SNAP2 + x - SNAP2 = x by omega]
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem run2_spec (s : MachineState) (hpc : s.pc = pcOf 42142) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hix : s.getMem (BitVec.ofNat 64 0x60) >>> 33 = BitVec.ofNat 64 idx) (hp : LPlanAt s)
    (hfl : ∀ c < 9, ∃ f < 2, s.getMem (BitVec.ofNat 64 (Compact.holdAt c + 16)) = BitVec.ofNat 64 f) :
    ∃ t, Steps im s 39570 39570 t ∧ t.pc = pcOf 42716 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = run2Mem (fun B => s.getMem (BitVec.ofNat 64 B)) idx A := by
  have hM' : MEMORY_BYTES = 16777216 := rfl
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0xB58 := rfl
  have hWZ : WZ = 0x480 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  have hLP : LPLAN = 0xff9400 := rfl
  obtain ⟨u1, s1, p1, r1, m1⟩ := copyPhase hc (code_cSnap hc) run_snap s hpc (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have e1 : ∀ A < 2 ^ 64, u1.getMem (BitVec.ofNat 64 A) = snapMem (fun B => s.getMem (BitVec.ofNat 64 B)) A :=
    fun A hA => by rw [m1 A hA]; rfl
  obtain ⟨u2a, s2a, p2a, x11, x12, x1, r2a, f2a⟩ := zeroSet_spec (code_cZero2 hc) u1 (by rw [p1])
  obtain ⟨u2, s2, p2, r2, m2⟩ := ClaudeWCT.W9.Machine.Expand.Compact.zero_spec hc u2a p2a WZ 3124 42154 x11 x12 x1 (by norm_num) (by norm_num)
    (by omega) (by omega)
  have e2 : ∀ A < 2 ^ 64, u2.getMem (BitVec.ofNat 64 A) =
      zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B))) A := fun A hA => by
    rw [m2 A hA]; unfold zeroed zMem; split
    · rfl
    · rw [f2a A hA (fun h => h), e1 A hA]
  obtain ⟨u3a, s3a, p3a, r3a, m3a⟩ := jump1_spec hc (code_cHdr hc) run_hdr u2 p2
  obtain ⟨u3, s3, p3, r3, m3⟩ := copyPhaseL hc (code_cCtr hc) run_ctr u3a p3a (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have e3 : ∀ A < 2 ^ 64, u3.getMem (BitVec.ofNat 64 A) =
      ctrMem (zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B)))) A := fun A hA => by
    rw [m3 A hA]; unfold ctrMem; split
    · rw [m3a, e2 _ (by omega)]
    · rw [m3a, e2 A hA]
  obtain ⟨u4, s4, p4, r4, m4⟩ := pregs_spec hc u3 _ e3 (by rw [p3]; rfl) 9 le_rfl
  have hfl' : ∀ c < 9, ∃ f < 2,
      regsMem (ctrMem (zMem (snapMem (fun B => s.getMem (BitVec.ofNat 64 B))))) 9 (Compact.holdAt c + 16) =
        BitVec.ofNat 64 f := by
    intro c hc9
    obtain ⟨f, hf2, hf⟩ := hfl c hc9
    have hH : Compact.holdAt c = 0x380000 + 32 * c := rfl
    refine ⟨f, hf2, ?_⟩
    unfold regsMem ctrMem zMem snapMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hf
  obtain ⟨u5, s5, p5, r5, m5⟩ := holds_spec hc u4 _ m4 (by rw [p4]; rfl) hfl' 9 le_rfl
  obtain ⟨u5b, s5b, p5b, r5b, m5b⟩ := jump1_spec hc (code_cPEnd hc) run_pend u5 (by rw [p5]; rfl)
  obtain ⟨u6a, s6a, p6a, r6a, m6a⟩ := copyPhase hc (code_cTop hc) run_top u5b (by rw [p5b]) (by norm_num)
    (by norm_num) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have e5 : ∀ A < 2 ^ 64, u6a.getMem (BitVec.ofNat 64 A) =
      topMem (stMem (fun B => s.getMem (BitVec.ofNat 64 B))) A := fun A hA => by
    rw [m6a A hA]; unfold topMem; split
    · rw [m5b, m5 _ (by omega)]; rfl
    · rw [m5b, m5 A hA]; rfl
  obtain ⟨u6, s6, p6, x22, x18, r6, f6⟩ := idx_spec (code_cIdx hc) u6a p6a
  have hp6 : LPlanAt u6 := fun k hk => by
    rw [f6 _ (by omega) (fun h => h), e5 _ (by omega)]
    unfold topMem
    rw [if_neg (by omega), stMem_out _ _ (Or.inr (by omega))]
    exact hp k hk
  have x22' : u6.getReg .x22 = BitVec.ofNat 64 idx := by
    rw [x22, show (96#64 : Word) = BitVec.ofNat 64 0x60 from rfl, e5 _ (by omega)]
    unfold topMem
    rw [if_neg (by omega), stMem_out _ _ (Or.inl (by omega))]
    exact hix
  have e6 : ∀ A < 2 ^ 64, u6.getMem (BitVec.ofNat 64 A) =
      topMem (stMem (fun B => s.getMem (BitVec.ofNat 64 B))) A := fun A hA => by
    rw [f6 A hA (fun h => h), e5 A hA]
  obtain ⟨u7, s7, p7, r7, m7⟩ := layer_spec hc 1 (by omega) u6 _ e6 (by rw [p6]; rfl) idx hidx x22' x18 hp6
  have hp7 : LPlanAt u7 := fun k hk => by
    rw [m7 _ (by omega), layMem_out _ 1 (by omega) idx _ (Or.inr (by unfold chDst lvDst; simp; omega)),
      ← e6 _ (by omega)]
    exact hp6 k hk
  obtain ⟨u8, s8, p8, r8, m8⟩ := layer_spec hc 2 (by omega) u7 _ m7 (by rw [p7]; rfl) idx hidx
    (by rw [r7.get (by decide), x22']) (by rw [r7.get (by decide), x18]) hp7
  have hp8 : LPlanAt u8 := fun k hk => by
    rw [m8 _ (by omega), layMem_out _ 2 (by omega) idx _ (Or.inr (by unfold chDst lvDst; simp; omega)),
      ← m7 _ (by omega)]
    exact hp7 k hk
  obtain ⟨u9, s9, p9, r9, m9⟩ := layer_spec hc 3 (by omega) u8 _ m8 (by rw [p8]; rfl) idx hidx
    (by rw [r8.get (by decide), r7.get (by decide), x22']) (by rw [r8.get (by decide), r7.get (by decide), x18]) hp8
  obtain ⟨u10, s10, p10, r10, m10⟩ := tail_spec (code_cTail hc) u9 (by rw [p9]; rfl)
  refine ⟨u10, (((((((((((((s1.trans s2a).trans s2).trans s3a).trans s3).trans s4).trans s5).trans s5b).trans
    s6a).trans s6).trans s7).trans s8).trans s9).trans s10).of_eq (by unfold layLen rowLen lvH; norm_num)
    (by unfold layLen rowLen lvH; norm_num), p10, fun A hA => ?_⟩
  rw [m10 A hA]
  unfold run2Mem tailMem
  beta_reduce
  have g : ∀ B < 2 ^ 64, u9.getMem (BitVec.ofNat 64 B) =
      layMem (layMem (layMem (topMem (stMem (fun B => s.getMem (BitVec.ofNat 64 B)))) 1 idx) 2 idx) 3 idx B := m9
  rw [g _ (by omega), g _ (by omega), g _ (by omega), g A hA]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
def zoneLay (o : Nat) : Nat := if o < 15824 then 1 else if o < 18392 then 2 else 3
def pathOut (M : Nat → Word) (lay r p : Nat) : Word :=
  if p = rootOff lay r then 1#64 else
  match (List.range (lvH lay)).find? (fun j => decide (lvHit lay r j p)) with
  | some j => M (lvSrc lay j - SNAP2 + WIT + (p - 16 * plan lay r j))
  | none => 0
/-- Pairing stage 1: word `q` (from `chDst`) of a lower chain area after the pair copy and the zero fill. -/
def chOut (M : Nat → Word) (lay q : Nat) : Word :=
  if q < 2184 ∧ PairCopy.isVal (q % 104) then
    M (chSrc lay - SNAP2 + WIT + (128 * (q / 104) + PairCopy.srcOff (q % 104)))
  else if q = 2232 ∨ q = 2240 then M (chSrc lay - SNAP2 + WIT + (2688 + (q - 2184)))
  else 0
/-- Output word at staging-relative offset `o` (`WIT + o`) after the constructor's front part (pairing stage 1: top
region `[8952, 13176)`, lower regions to `20960`, staged rho/counter at `20960 .. 20984`). -/
def out2old (M : Nat → Word) (idx o : Nat) : Word :=
  if o < 8952 then M (WIT + o)
  else if o < 13176 then M (WIT + (o - 816))
  else if o < 20960 then
    (if o - (lvDst (zoneLay o) - WIT) < pathTop (zoneLay o) then
      pathOut M (zoneLay o) (lroute (zoneLay o) idx) (o - (lvDst (zoneLay o) - WIT))
    else chOut M (zoneLay o) (o - (chDst (zoneLay o) - WIT)))
  else if o = 20960 then M WIT
  else if o = 20968 then M (WIT + 8)
  else if o = 20976 then 0
  else LoadKind.wu.fromWord (M (WIT + 16)) 0
/-- Output word at offset `o` from the final witness base `WOUT` (pairing stage 1: `WOUT = WIT + 856`; below 8096 the
P_final memory). -/
def out2 (M : Nat → Word) (idx o : Nat) : Word :=
  if o < 8096 then stMem M (WOUT + o) else out2old M idx (o + 856)
theorem lay_consts : lvDst 1 = 0x800 + 13176 ∧ lvDst 2 = 0x800 + 15824 ∧ lvDst 3 = 0x800 + 18392 ∧
    chDst 1 = 0x800 + 13176 + 400 ∧ chDst 2 = 0x800 + 15824 + 320 ∧ chDst 3 = 0x800 + 18392 + 320 := by
  unfold lvDst chDst; decide
theorem snap_read (M : Nat → Word) (idx x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    (layMem (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) 3 idx) (SNAP2 + x) = M (WIT + x) := by
  have hS : SNAP2 = 0x310000 := rfl
  have hW : WIT = 0x800 := rfl
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  rw [layMem_out _ 3 (by omega) idx (SNAP2 + x) (Or.inr (by omega)),
    layMem_out _ 2 (by omega) idx (SNAP2 + x) (Or.inr (by omega)),
    layMem_out _ 1 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]
  unfold topMem
  rw [if_neg (by omega), stMem_snap M x hx h8]
theorem lays_low (M : Nat → Word) (idx A : Nat) (hA : A < WIT + 13176) :
    (layMem (layMem (layMem M 1 idx) 2 idx) 3 idx) A = M A := by
  have hW : WIT = 0x800 := rfl
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  rw [layMem_out _ 3 (by omega) idx A (Or.inl (by omega)),
    layMem_out _ 2 (by omega) idx A (Or.inl (by omega)),
    layMem_out _ 1 (by omega) idx A (Or.inl (by omega))]
theorem pre_low (M : Nat → Word) (A : Nat) (hA : WIT + 13176 ≤ A) (hA' : A < WIT + 20960) (h8 : (A - WIT) % 8 = 0) :
    topMem (stMem M) A = 0 := by
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0xB58 := rfl
  have hWZ : WZ = 0x480 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  unfold topMem
  rw [if_neg (by omega)]
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (by omega)]
  unfold regsMem ctrMem zMem
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
theorem pre_snap (M : Nat → Word) (x : Nat) (hx : x < 8 * 2729) (h8 : x % 8 = 0) :
    topMem (stMem M) (SNAP2 + x) = M (WIT + x) := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  unfold topMem
  rw [if_neg (by omega), stMem_snap M x hx h8]
set_option maxRecDepth 200000 in
theorem chMem_at (P M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4)
    (hP : ∀ x < 8 * 2729, x % 8 = 0 → P (SNAP2 + x) = M (WIT + x)) (q : Nat) (hZ : P (chDst lay + q) = 0)
    (hq : q < 2248) (h8 : q % 8 = 0) : chMem P lay (chDst lay + q) = chOut M lay q := by
  have hS : SNAP2 = 0x310000 := rfl
  have hW : WIT = 0x800 := rfl
  have hsrc : 0x310000 + 8136 ≤ chSrc lay ∧ chSrc lay + 2752 ≤ 0x310000 + 21832 ∧ chSrc lay % 8 = 0 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hso : PairCopy.srcOff (q % 104) ≤ 120 ∧ PairCopy.srcOff (q % 104) % 8 = 0 := by
    unfold PairCopy.srcOff; split_ifs <;> omega
  have key : ∀ y, chSrc lay ≤ y → y < chSrc lay + 2752 → y % 8 = 0 → P y = M (y - SNAP2 + WIT) := by
    intro y h1 h2 h3
    have := hP (y - SNAP2) (by omega) (by omega)
    rw [show SNAP2 + (y - SNAP2) = y by omega] at this
    rw [this]; apply congrArg M; omega
  unfold chMem PairCopy.pairCopyMem PairCopy.pcMem chOut
  rw [Nat.add_sub_cancel_left]
  unfold PairCopy.isVal at *
  split_ifs <;> first
    | exact hZ
    | (rw [key _ (by omega) (by omega) (by omega)]; apply congrArg M; omega)
    | omega
theorem layMem_zone (P : Nat → Word) (M : Nat → Word) (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (idx : Nat)
    (hP : ∀ x < 8 * 2729, x % 8 = 0 → P (SNAP2 + x) = M (WIT + x))
    (hZ : ∀ A, lvDst lay ≤ A → A < chDst lay + 2248 → (A - WIT) % 8 = 0 → P A = 0)
    (o : Nat) (h1 : lvDst lay - WIT ≤ o) (h2 : o < chDst lay - WIT + 2248) (h8 : o % 8 = 0) :
    layMem P lay idx (WIT + o) =
      if o - (lvDst lay - WIT) < pathTop lay then pathOut M lay (lroute lay idx) (o - (lvDst lay - WIT))
      else chOut M lay (o - (chDst lay - WIT)) := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  have hce := chDst_eq lay
  have hD : 0x800 + 13176 ≤ lvDst lay ∧ lvDst lay % 8 = 0 ∧ lvDst lay + pathTop lay + 2248 ≤ 0x800 + 20960 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hsrc : 0x310000 + 8136 ≤ chSrc lay ∧ chSrc lay + 2752 ≤ 0x310000 + 21832 ∧ chSrc lay % 8 = 0 := by
    obtain ⟨a, b⟩ := hl; interval_cases lay <;> decide
  have hr := lroute_lt lay idx
  have hpt : pathTop lay % 16 = 0 := by unfold pathTop; split <;> omega
  have hro := rootOff_lt lay hl (lroute lay idx) hr
  unfold layMem
  by_cases hp : o - (lvDst lay - WIT) < pathTop lay
  · rw [if_pos hp]
    by_cases hrt : o - (lvDst lay - WIT) = rootOff lay (lroute lay idx)
    · unfold pathOut
      rw [if_pos (by omega), if_pos hrt]
    rw [if_neg (show ¬ WIT + o = lvDst lay + rootOff lay (lroute lay idx) by omega)]
    unfold lvsMem pathOut
    rw [if_neg hrt, if_pos (by omega), show WIT + o - lvDst lay = o - (lvDst lay - WIT) by omega]
    cases h : (List.range (lvH lay)).find? (fun j => decide (lvHit lay (lroute lay idx) j (o - (lvDst lay - WIT)))) with
    | none =>
      simp only
      rw [chMem_out _ _ _ (Or.inl (by omega))]
      exact hZ _ (by omega) (by omega) (by omega)
    | some j =>
      simp only
      obtain ⟨hj, hp'⟩ := lvs_find_some h
      have hh : lvHit lay (lroute lay idx) j (o - (lvDst lay - WIT)) := of_decide_eq_true hp'
      unfold lvHit at hh
      have hsp := sibS_padS_lt lay (lroute lay idx) j hl hr hj
      have hm := plan_mod16 lay (lroute lay idx) j
      have hls : 0x310000 + 8136 ≤ lvSrc lay j ∧ lvSrc lay j + 64 ≤ 0x310000 + 21832 ∧ lvSrc lay j % 8 = 0 := by
        unfold lvSrc; unfold lvH at hj; split_ifs at * <;> omega
      have hpl : 16 * plan lay (lroute lay idx) j ≤ sibS lay (lroute lay idx) j ∧
          sibS lay (lroute lay idx) j + 16 ≤ 16 * plan lay (lroute lay idx) j + 64 ∧
          padS lay (lroute lay idx) j = 16 * plan lay (lroute lay idx) j + 32 := by
        unfold sibS padS
        have : lroute lay idx / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
        omega
      rw [chMem_out _ _ _ (Or.inr (by omega))]
      have := hP (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) (by omega)
        (by omega)
      rw [show SNAP2 + (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) =
        lvSrc lay j + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j) by omega] at this
      rw [this, show WIT + (lvSrc lay j - SNAP2 + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j)) =
        lvSrc lay j - SNAP2 + WIT + (o - (lvDst lay - WIT) - 16 * plan lay (lroute lay idx) j) by omega]
  · rw [if_neg hp, if_neg (show ¬ WIT + o = lvDst lay + rootOff lay (lroute lay idx) by omega),
      lvsMem_out _ lay hl _ hr _ le_rfl _ (Or.inr (by omega))]
    rw [show WIT + o = chDst lay + (o - (chDst lay - WIT)) by omega]
    exact chMem_at P M lay hl hP _ (hZ _ (by omega) (by omega) (by omega)) (by omega) (by omega)
theorem run2_zone_old (M : Nat → Word) (idx o : Nat) (hlo : 8952 ≤ o) (ho : o < 20992) (h8 : o % 8 = 0) :
    run2Mem M idx (WIT + o) = out2old M idx o := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x310000 := rfl
  have hTs : ∀ x < 8 * 2729, x % 8 = 0 → topMem (stMem M) (SNAP2 + x) = M (WIT + x) :=
    fun x hx h => pre_snap M x hx h
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  unfold run2Mem tailMem out2old
  by_cases ht : 20960 ≤ o
  · have hs := fun x hx h => snap_read M idx x hx h
    rcases (show o = 20960 ∨ o = 20968 ∨ o = 20976 ∨ o = 20984 by omega) with rfl | rfl | rfl | rfl
    · simp only [show ¬ (WIT + 20960 = WIT + 20984) by omega, show ¬ (WIT + 20960 = WIT + 20976) by omega,
        show ¬ (WIT + 20960 = WIT + 20968) by omega, if_false, if_true, show ¬ (20960 < 8952) by omega,
        show ¬ (20960 < 13176) by omega, show ¬ (20960 < 20960) by omega]
      have := hs 0 (by omega) (by omega); simpa using this
    · simp only [show ¬ (WIT + 20968 = WIT + 20984) by omega, show ¬ (WIT + 20968 = WIT + 20976) by omega,
        if_false, if_true, show ¬ (20968 < 8952) by omega, show ¬ (20968 < 13176) by omega,
        show ¬ (20968 < 20960) by omega, show ¬ (20968 = 20960) by omega]
      exact hs 8 (by omega) (by omega)
    · simp only [show ¬ (WIT + 20976 = WIT + 20984) by omega, if_false, if_true, show ¬ (20976 < 8952) by omega,
        show ¬ (20976 < 13176) by omega, show ¬ (20976 < 20960) by omega, show ¬ (20976 = 20960) by omega,
        show ¬ (20976 = 20968) by omega]
    · simp only [if_true, show ¬ (20984 < 8952) by omega, show ¬ (20984 < 13176) by omega,
        show ¬ (20984 < 20960) by omega, show ¬ (20984 = 20960) by omega, show ¬ (20984 = 20968) by omega,
        show ¬ (20984 = 20976) by omega, if_false]
      rw [hs 16 (by omega) (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (show ¬ o < 8952 by omega)]
    by_cases hl : o < 13176
    · rw [lays_low _ idx (WIT + o) (by omega), if_pos hl]
      unfold topMem
      rw [if_pos (by omega), show SNAP2 + 8136 + (WIT + o - (WIT + 8952)) = SNAP2 + (8136 + (o - 8952)) by omega,
        stMem_snap M _ (by omega) (by omega), show WIT + (8136 + (o - 8952)) = WIT + (o - 816) by omega]
    · rw [if_neg hl, if_pos (by omega)]
      have hZ1 : ∀ A, lvDst 1 ≤ A → A < chDst 1 + 2248 → (A - WIT) % 8 = 0 →
          topMem (stMem M) A = 0 := fun A h1 h2 h3 =>
        pre_low M A (by omega) (by omega) h3
      by_cases hz1 : o < 15824
      · have hzl : zoneLay o = 1 := by unfold zoneLay; rw [if_pos hz1]
        rw [hzl, layMem_out _ 3 (by omega) idx (WIT + o) (Or.inl (by omega)),
          layMem_out _ 2 (by omega) idx (WIT + o) (Or.inl (by omega))]
        exact layMem_zone (topMem (stMem M)) M 1 (by omega) idx hTs hZ1 o (by omega)
          (by omega) h8
      · have hP2 : ∀ x < 8 * 2729, x % 8 = 0 → layMem (topMem (stMem M)) 1 idx
            (SNAP2 + x) = M (WIT + x) := fun x hx h => by
          rw [layMem_out _ 1 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]; exact hTs x hx h
        have hZ2 : ∀ A, lvDst 2 ≤ A → A < chDst 2 + 2248 → (A - WIT) % 8 = 0 →
            layMem (topMem (stMem M)) 1 idx A = 0 := fun A h1 h2 h3 => by
          rw [layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
          exact pre_low M A (by omega) (by omega) h3
        by_cases hz2 : o < 18392
        · have hzl : zoneLay o = 2 := by unfold zoneLay; rw [if_neg hz1, if_pos hz2]
          rw [hzl, layMem_out _ 3 (by omega) idx (WIT + o) (Or.inl (by omega))]
          exact layMem_zone (layMem (topMem (stMem M)) 1 idx) M 2 (by omega) idx hP2 hZ2 o (by omega)
            (by omega) h8
        · have hzl : zoneLay o = 3 := by unfold zoneLay; rw [if_neg hz1, if_neg hz2]
          have hP3 : ∀ x < 8 * 2729, x % 8 = 0 → layMem (layMem (topMem (stMem M))
              1 idx) 2 idx (SNAP2 + x) = M (WIT + x) := fun x hx h => by
            rw [layMem_out _ 2 (by omega) idx (SNAP2 + x) (Or.inr (by omega))]; exact hP2 x hx h
          have hZ3 : ∀ A, lvDst 3 ≤ A → A < chDst 3 + 2248 → (A - WIT) % 8 = 0 →
              layMem (layMem (topMem (stMem M)) 1 idx) 2 idx A = 0 := fun A h1 h2 h3 => by
            rw [layMem_out _ 2 (by omega) idx A (Or.inr (by omega)), layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
            exact pre_low M A (by omega) (by omega) h3
          rw [hzl]
          exact layMem_zone (layMem (layMem (topMem (stMem M)) 1 idx) 2 idx) M 3 (by omega) idx hP3 hZ3 o
            (by omega) (by omega) h8
/-- Pairing stage 1: final words below `WOUT + 20136` (the staged rho / counter ends at L3's leaf buffer + 32). -/
theorem run2_zone (M : Nat → Word) (idx o : Nat) (ho : o < 20136) (h8 : o % 8 = 0) :
    run2Mem M idx (WOUT + o) = out2 M idx o := by
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0xB58 := rfl
  have hWZ : WZ = 0x480 := rfl
  unfold out2
  by_cases hl : o < 8096
  · rw [if_pos hl]
    unfold run2Mem tailMem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), lays_low _ idx _ (by omega)]
    unfold topMem
    rw [if_neg (by omega)]
  · rw [if_neg hl, show WOUT + o = WIT + (o + 856) by omega]
    exact run2_zone_old M idx (o + 856) (by omega) (by omega) (by omega)
end ClaudeWCT.W9.Machine.Expand.Compact2
end


namespace ClaudeWCT.W9.Machine.Expand.Compact2.Buffer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
/-- Pairing stage 1: physical memory after the buffer pass: `43472` writes LE64(1) at 1240 (scratch below the
witness), then the layout block 48100 (`Layout.lbMem`). -/
def bufferMem (M : Nat → Word) (A : Nat) : Word :=
  if A = 1240 then 1#64 else Layout.lbMem M A

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
def cEntry : List (BitVec 32) := [0x34c0106f]
def cInitJ : List (BitVec 32) := [2287988847]
def cETail : List (BitVec 32) := [1052307,1305492515,25911,2634351891,2000683119]
/-- Pairing stage 1: `43953: jal 48100` (was the old buffer expansion). -/
def cInitB : List (BitVec 32) := [0x0cc0406f]
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem code_cEntry : CodeAt im (pcOf 42716) cEntry := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cInitJ : CodeAt im (pcOf 43951) cInitJ := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cETail : CodeAt im (pcOf 43472) cETail := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cInitB : CodeAt im (pcOf 43953) cInitB := codeAt_of_compact_window hc (by decide) (by decide +kernel)
end
sym_block REntry := symRun cfgC cEntry (pcOf 42716) 40
sym_block RInitJ := symRun cfgC cInitJ (pcOf 43951) 40
sym_block RETail := symRun cfgC cETail (pcOf 43472) 40
sym_block RInitB := symRun cfgC cInitB (pcOf 43953) 40
def MemEq (M N : Nat → Word) : Prop := ∀ A < 2^64, M A=N A
theorem lbS_low : ∀ k < 180, 1256 ≤ Layout.sK k := by decide
theorem lbMem_congr (M N : Nat → Word) (h : ∀ B, B ≠ 1240 → M B = N B) (A : Nat) (hA : A ≠ 1240) :
    Layout.lbMem M A = Layout.lbMem N A := by
  unfold Layout.lbMem Layout.itMem Layout.hitVal
  split_ifs with h1 h2
  · exact h _ (by omega)
  · cases hf : (List.range 180).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) with
    | none => rfl
    | some k =>
      have hk := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have := lbS_low k hk
      exact h _ (by omega)
  · exact h _ hA
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
/-- Pairing stage 1: the buffer pass from 42716 to the top-path post-pass at 43500 (1 + 1 + 5 + 1 + 2287 steps). -/
theorem buffer_spec (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 2295 2295 t ∧ t.pc=pcOf 43500 ∧
      MemEq (fun A=>t.getMem (BitVec.ofNat 64 A)) (bufferMem (fun A=>s.getMem (BitVec.ofNat 64 A))) := by
  have s0 := symRun_sound REntry (code_cEntry hc) s hpc (by simp [REntry.res, rv_simp])
  set u0 := REntry.res.toState s
  have p0 : u0.pc = pcOf 43951 := by simp [u0, REntry.res, E.eval]
  have s1 := symRun_sound RInitJ (code_cInitJ hc) u0 p0 (by simp [RInitJ.res, rv_simp])
  set u1 := RInitJ.res.toState u0
  have p1 : u1.pc = pcOf 43472 := by simp [u1, RInitJ.res, E.eval]
  have s2 := symRun_sound RETail (code_cETail hc) u1 p1 (by simp [RETail.res, rv_simp])
  set u2 := RETail.res.toState u1
  have p2 : u2.pc = pcOf 43953 := by simp [u2, RETail.res, E.eval]
  have s3 := symRun_sound RInitB (code_cInitB hc) u2 p2 (by simp [RInitB.res, rv_simp])
  set u3 := RInitB.res.toState u2
  have p3 : u3.pc = pcOf 48100 := by simp [u3, RInitB.res, E.eval]
  have m3 : ∀ B < 2 ^ 64, u3.getMem (BitVec.ofNat 64 B) = if B = 1240 then 1#64 else s.getMem (BitVec.ofNat 64 B) := by
    intro B hB
    have key := ofNat_inj hB (show 1240 < 2 ^ 64 by norm_num)
    simp only [u3, u2, u1, u0, Result.toState_getMem, RInitB.res, RETail.res, RInitJ.res, REntry.res,
      memEval_cons, memEval_nil, Addr.eval, E.eval, BitVec.add_zero, key]
  obtain ⟨t, st, pt, mt⟩ := Layout.layout_spec hc.layout u3 p3
  refine ⟨t, ((((s0.trans s1).trans s2).trans s3).trans st).of_eq (by simp [REntry.res, RInitJ.res, RETail.res,
    RInitB.res]) (by simp [REntry.res, RInitJ.res, RETail.res, RInitB.res]), pt, fun A hA => ?_⟩
  beta_reduce
  rw [mt A hA]
  unfold bufferMem
  by_cases h : A = 1240
  · subst h
    rw [if_pos rfl]
    unfold Layout.lbMem Layout.itMem
    rw [if_neg (by omega), if_neg (by omega)]
    simpa using m3 1240 (by norm_num)
  · rw [if_neg h]
    have hB : ∀ B, B ≠ 1240 → B < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 B) = s.getMem (BitVec.ofNat 64 B) :=
      fun B hb hB' => by rw [m3 B hB', if_neg hb]
    unfold Layout.lbMem Layout.itMem Layout.hitVal
    have hlt : ∀ k < 180, Layout.sK k + 16 ≤ 23008 := fun k hk => (Layout.tab_facts.2.2.2.2.2.2.2.2 k hk).2.1
    split_ifs with h1 h2
    · exact hB _ (by omega) (by omega)
    · cases hf : (List.range 180).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) with
      | none => rfl
      | some k =>
        have hk := List.mem_range.mp (List.mem_of_find?_eq_some hf)
        have := lbS_low k hk
        have := hlt k hk
        exact hB _ (by omega) (by omega)
    · exact hB _ h hA
theorem buffer_prefix_spec (s : MachineState) (hpc : s.pc=pcOf 42716) :
    ∃ t, Steps im s 2295 2295 t ∧ t.pc=pcOf 43500 ∧
      MemEq (fun A=>t.getMem (BitVec.ofNat 64 A)) (bufferMem (fun A=>s.getMem (BitVec.ofNat 64 A))) :=
  buffer_spec hc s hpc
end

def clearMem (M : Nat → Word) (dst i A : Nat) : Word :=
  if dst  ≤  A ∧ A < dst+8*i ∧ (A-dst)%8=0 then 0 else M A
/-! ### C4: the top-path post-pass (words 43500..43763, entered from the layout block's `jal 43500`)

After the buffer pass the top path area `[11000, 11768)` still holds the old layout: level `j`'s sibling at
`11704 - 64 j` (`+48` when bit `j` of the top leaf is 0). The post-pass copies the twelve siblings to a scratch
area at `0x40000`, zeroes the 768-byte area, and stores sibling `j` at slot `ppSlot leaf j` read from the plan
table (`TOPA`/`TOPB`). -/
namespace Post
def ppBit (leaf j : Nat) : Nat := leaf / 2 ^ j % 2
theorem ppBit_lt (leaf j : Nat) : ppBit leaf j < 2 := Nat.mod_lt _ (by norm_num)
/-- Old address of the level-`j` top sibling. -/
def ppOld (leaf j : Nat) : Nat := 11704 - 64 * j + 48 * (1 - ppBit leaf j)
/-- Plan slot of the level-`j` top sibling (the table byte). -/
def ppSlot (leaf j : Nat) : Nat := if j < 6 then slotA (leaf % 64) j else slotB (leaf / 64) (j - 6)
def ppNew (leaf j : Nat) : Nat := 11000 + 16 * ppSlot leaf j
def SCR : Nat := 0x40000
/-- Memory after the first `L` placements, over the memory `M` at the hook (scratch excluded). -/
def ppPlace (M : Nat → Word) (leaf : Nat) : Nat → Nat → Word
  | 0, A => if 11000 ≤ A ∧ A < 11768 ∧ (A - 11000) % 8 = 0 then 0 else M A
  | L + 1, A => if A = ppNew leaf L + 8 then M (ppOld leaf L + 8)
      else if A = ppNew leaf L then M (ppOld leaf L) else ppPlace M leaf L A
/-- Memory after the first `L` gather blocks. -/
def gMemF (M : Nat → Word) (leaf L A : Nat) : Word :=
  if SCR ≤ A ∧ A < SCR + 16 * L ∧ (A - SCR) % 8 = 0 then M (ppOld leaf ((A - SCR) / 16) + (A - SCR) % 16) else M A
theorem ppOld_lt (leaf j : Nat) : ppOld leaf j + 16 ≤ 11768 ∧ ppOld leaf j % 8 = 0 := by
  have := ppBit_lt leaf j; unfold ppOld; omega
theorem ppSlot_le (leaf j : Nat) (hj : j < 12) (hl : leaf < 4096) : ppSlot leaf j ≤ 47 := by
  unfold ppSlot
  split
  · exact (slots_ok.1 _ (Nat.mod_lt _ (by norm_num)) j (by omega)).2
  · have := slots_ok.2.1 (leaf / 64) (by omega) (j - 6) (by omega); omega
def cPost : List (BitVec 32) := [100676355,54743827,263863,218003,1307539,1295251,5479955,4428691,29590451,15927,3683520019,8261171,933507,9322243,30847011,31896611,1266579,1307539,1295251,5479955,4428691,29590451,15927,3616411155,8261171,933507,9322243,30849059,31898659,2315155,1307539,1295251,5479955,4428691,29590451,15927,3549302291,8261171,933507,9322243,64401443,65451043,3363731,1307539,1295251,5479955,4428691,29590451,15927,3482193427,8261171,933507,9322243,64403491,65453091,4412307,1307539,1295251,5479955,4428691,29590451,15927,3415084563,8261171,933507,9322243,97955875,99005475,5460883,1307539,1295251,5479955,4428691,29590451,15927,3347975699,8261171,933507,9322243,97957923,99007523,6509459,1307539,1295251,5479955,4428691,29590451,15927,3280866835,8261171,933507,9322243,131510307,132559907,7558035,1307539,1295251,5479955,4428691,29590451,15927,3213757971,8261171,933507,9322243,131512355,132561955,8606611,1307539,1295251,5479955,4428691,29590451,15927,3146649107,8261171,933507,9322243,165064739,166114339,9655187,1307539,1295251,5479955,4428691,29590451,15927,3079540243,8261171,933507,9322243,165066787,166116387,10703763,1307539,1295251,5479955,4428691,29590451,15927,3012431379,8261171,933507,9322243,198619171,199668771,11752339,1307539,1295251,5479955,4428691,29590451,15927,2945322515,8261171,933507,9322243,198621219,199670819,13751,2944763283,13879,3750102547,372771,8750483,4274384099,16780855,3087928851,66286483,3380115,8258867,6509459,3380115,8258995,537232787,13879,2944796179,344963,4428691,12813235,441987,8830723,30650403,31700003,1393539,4428691,12813235,17219203,25607939,30650403,31700003,2442115,4428691,12813235,33996419,42385155,30650403,31700003,3490691,4428691,12813235,50773635,59162371,30650403,31700003,4539267,4428691,12813235,67550851,75939587,30650403,31700003,5587843,4428691,12813235,84328067,92716803,30650403,31700003,377731,4428691,12813235,101105283,109494019,30650403,31700003,1426307,4428691,12813235,117882499,126271235,30650403,31700003,2474883,4428691,12813235,134659715,143048451,30650403,31700003,3523459,4428691,12813235,151436931,159825667,30650403,31700003,4572035,4428691,12813235,168214147,176602883,30650403,31700003,5620611,4428691,12813235,184991363,193380099,30650403,31700003,616575087,1299,115]
def cPro : List (BitVec 32) := cPost.take 3
def cG (j : Nat) : List (BitVec 32) := (cPost.drop (3 + 13 * j)).take 13
def cZs : List (BitVec 32) := (cPost.drop 159).take 4
def cZl : List (BitVec 32) := (cPost.drop 163).take 3
def cTs : List (BitVec 32) := (cPost.drop 166).take 11
def cP (j : Nat) : List (BitVec 32) := (cPost.drop (177 + 7 * j)).take 7
def cFin : List (BitVec 32) := cPost.drop 261
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem code_cPro : CodeAt im (pcOf 43500) cPro := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZs : CodeAt im (pcOf 43659) cZs := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZl : CodeAt im (pcOf 43663) cZl := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cTs : CodeAt im (pcOf 43666) cTs := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cG (j : Nat) (hj : j < 12) : CodeAt im (pcOf (43503 + 13 * j)) (cG j) := by
  interval_cases j <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cP (j : Nat) (hj : j < 12) : CodeAt im (pcOf (43677 + 7 * j)) (cP j) := by
  interval_cases j <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
end
sym_block RPro := symRun cfgC cPro (pcOf 43500) 40
sym_block RZs := symRun cfgC cZs (pcOf 43659) 40
sym_block RZl := symRun cfgC cZl (pcOf 43663) 40
sym_block RTs := symRun cfgC cTs (pcOf 43666) 40
def gBit (j : Nat) : E := .bin .xor (.bin .and (.bin .srl (.reg .x6) (.c (BitVec.ofNat 64 j))) (.c 1#64)) (.c 1#64)
def gOff (j : Nat) : E := .bin .add (.bin .sll (gBit j) (.c 4#64)) (.bin .sll (gBit j) (.c 5#64))
def gOld (j k : Nat) : E := .bin .add (gOff j) (.c (BitVec.ofNat 64 (11704 - 64 * j + k)))
def gRes (j : Nat) : Result :=
  ⟨⟨(((RegFile.init.set .x7 (gOff j)).set .x28 (gOld j 0)).set .x29 (.ld (gOld j 0))).set .x30 (.ld (gOld j 8)),
    [(⟨some (.reg .x13), BitVec.ofNat 64 (16 * j + 8)⟩, .ld (gOld j 8)),
     (⟨some (.reg .x13), BitVec.ofNat 64 (16 * j)⟩, .ld (gOld j 0))],
    [.valid ⟨some (.reg .x13), BitVec.ofNat 64 (16 * j + 8)⟩ 8, .valid ⟨some (.reg .x13), BitVec.ofNat 64 (16 * j)⟩ 8,
     .valid ⟨some (gOff j), BitVec.ofNat 64 (11704 - 64 * j + 8)⟩ 8,
     .valid ⟨some (gOff j), BitVec.ofNat 64 (11704 - 64 * j)⟩ 8]⟩,
   .c (pcOf (43503 + 13 * (j + 1))), .endOfCode, 13, 13⟩
set_option maxRecDepth 20000 in
theorem run_g (j : Nat) (hj : j < 12) : symRun cfgC (cG j) (pcOf (43503 + 13 * j)) 40 = some (gRes j) := by
  interval_cases j <;> kernel_rfl
def pRow (j : Nat) : Reg := if j < 6 then .x10 else .x11
def pSlot (j : Nat) : E := .bin .add (.bin .sll (.un (.ld .bu (j % 6)) (.ld (.reg (pRow j)))) (.c 4#64)) (.reg .x12)
def pScr (k : Nat) : E := if k = 0 then .reg .x13 else .bin .add (.reg .x13) (.c (BitVec.ofNat 64 k))
def pRes (j : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x7 (pSlot j)).set .x29 (.ld (pScr (16 * j)))).set .x30 (.ld (pScr (16 * j + 8))),
    [(⟨some (pSlot j), 8#64⟩, .ld (pScr (16 * j + 8))), (⟨some (pSlot j), 0#64⟩, .ld (pScr (16 * j)))],
    [.valid ⟨some (pSlot j), 8#64⟩ 8, .valid ⟨some (pSlot j), 0#64⟩ 8,
     .valid ⟨some (.reg .x13), BitVec.ofNat 64 (16 * j + 8)⟩ 8, .valid ⟨some (.reg .x13), BitVec.ofNat 64 (16 * j)⟩ 8,
     .align8 (.reg (pRow j)), .valid ⟨some (.reg (pRow j)), BitVec.ofNat 64 (j % 6)⟩ 1]⟩,
   .c (pcOf (43677 + 7 * (j + 1))), .endOfCode, 7, 7⟩
set_option maxRecDepth 20000 in
theorem run_p (j : Nat) (hj : j < 12) : symRun cfgC (cP j) (pcOf (43677 + 7 * j)) 40 = some (pRes j) := by
  interval_cases j <;> kernel_rfl
end Post

namespace Post
theorem gOff_eval {s : MachineState} {leaf : Nat} (j : Nat) (hj : j < 64) (h6 : s.getReg .x6 = BitVec.ofNat 64 leaf)
    (hl : leaf < 2 ^ 64) : (gOff j).eval s = BitVec.ofNat 64 (48 * (1 - ppBit leaf j)) := by
  have hs : (BitVec.ofNat 64 j).toNat % 64 = j := by rw [toNat_ofNat_lt (by omega)]; omega
  simp only [gOff, gBit, E.eval, BinOp.eval, h6, hs, ofNat_shr _ _ hl, ofNat_and1]
  unfold ppBit
  rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ j) with h | h <;> rw [h] <;> decide
theorem ofNat_and63 (a : Nat) (ha : a < 2 ^ 64) : BitVec.ofNat 64 a &&& 63#64 = BitVec.ofNat 64 (a % 64) := by
  apply BitVec.eq_of_toNat_eq
  have h63 : (63#64 : Word).toNat = 2 ^ 6 - 1 := rfl
  rw [BitVec.toNat_and, h63, toNat_ofNat_lt ha, toNat_ofNat_lt (show a % 64 < 2 ^ 64 by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod a 6
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem pro_spec (s : MachineState) (hpc : s.pc = pcOf 43500) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 43503 ∧ t.getReg .x6 = s.getMem (BitVec.ofNat 64 96) >>> 52 ∧
      t.getReg .x13 = BitVec.ofNat 64 SCR ∧ RegsExcept s t [.x6, .x13] ∧ ∀ a, t.getMem a = s.getMem a := by
  refine ⟨_, symRun_sound RPro (code_cPro hc) s hpc (by simp [RPro.res, rv_simp, accessValid_iff]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [RPro.res, rv_simp]
  · simp [RPro.res, rv_simp]
  · simp [RPro.res, rv_simp, SCR]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro a; rfl
theorem g_spec (j : Nat) (hj : j < 12) (s : MachineState) (hpc : s.pc = pcOf (43503 + 13 * j)) (leaf : Nat)
    (hl : leaf < 4096) (h6 : s.getReg .x6 = BitVec.ofNat 64 leaf) (h13 : s.getReg .x13 = BitVec.ofNat 64 SCR) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf (43503 + 13 * (j + 1)) ∧ RegsExcept s t [.x7, .x28, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = SCR + 16 * j + 8 then s.getMem (BitVec.ofNat 64 (ppOld leaf j + 8))
        else if A = SCR + 16 * j then s.getMem (BitVec.ofNat 64 (ppOld leaf j))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hb := ppBit_lt leaf j
  have hS : SCR = 0x40000 := rfl
  have ho := gOff_eval (s := s) j (by omega) h6 (by omega)
  have hO : ∀ k, (gOld j k).eval s = BitVec.ofNat 64 (ppOld leaf j + k) := fun k => by
    simp only [gOld, E.eval, BinOp.eval, ho, ofNat_add_ofNat]; congr 1; unfold ppOld; omega
  have hobl : (gRes j).obligs s := by
    show Oblig.all s _
    rw [Oblig.all_iff]
    intro o ho'
    simp only [gRes, List.mem_cons, List.not_mem_nil, or_false] at ho'
    rcases ho' with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, E.eval, h13, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, h13, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ho, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ho, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
  refine ⟨_, symRun_sound (run_g j hj) (code_cG hc j hj) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gRes, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    have hO8 := hO 8
    have hO0 := hO 0
    rw [Nat.add_zero] at hO0
    simp only [Result.toState_getMem, gRes, memEval_cons, memEval_nil, Addr.eval, E.eval, h13, ofNat_add_ofNat,
      hO8, hO0]
    rw [show SCR + (16 * j + 8) = SCR + 16 * j + 8 by omega]
    by_cases q1 : A = SCR + 16 * j + 8
    · rw [if_pos (by rw [q1]), if_pos q1]
    · rw [if_neg (fun h => q1 ((ofNat_inj hA (by omega)).mp h)), if_neg q1]
      by_cases q2 : A = SCR + 16 * j
      · rw [if_pos (by rw [q2]), if_pos q2]
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), if_neg q2]
theorem g_loop (s : MachineState) (hpc : s.pc = pcOf 43503) (leaf : Nat) (hl : leaf < 4096)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 leaf) (h13 : s.getReg .x13 = BitVec.ofNat 64 SCR) :
    ∀ L ≤ 12, ∃ t, Steps im s (13 * L) (13 * L) t ∧ t.pc = pcOf (43503 + 13 * L) ∧
      RegsExcept s t [.x7, .x28, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = gMemF (fun B => s.getMem (BitVec.ofNat 64 B)) leaf L A := by
  have hS : SCR = 0x40000 := rfl
  intro L
  induction L with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, by simpa using hpc, RegsExcept.refl s _, fun A _ => ?_⟩
    unfold gMemF; rw [if_neg (by omega)]
  | succ L ih =>
    intro hL
    obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
    obtain ⟨u, su, pu, ru, mu⟩ := g_spec hc L (by omega) t pt leaf hl (by rw [rt.get (by decide)]; exact h6)
      (by rw [rt.get (by decide)]; exact h13)
    refine ⟨u, (st.trans su).of_eq (by ring) (by ring), pu, (rt.trans ru).mono (by decide), fun A hA => ?_⟩
    have hp := ppOld_lt leaf L
    rw [mu A hA]
    unfold gMemF
    by_cases q1 : A = SCR + 16 * L + 8
    · subst q1
      rw [if_pos rfl, mt _ (by omega)]
      unfold gMemF
      rw [if_neg (by omega), if_pos (by omega), show (SCR + 16 * L + 8 - SCR) / 16 = L by omega,
        show (SCR + 16 * L + 8 - SCR) % 16 = 8 by omega]
    · rw [if_neg q1]
      by_cases q2 : A = SCR + 16 * L
      · subst q2
        rw [if_pos rfl, mt _ (by omega)]
        unfold gMemF
        rw [if_neg (by omega), if_pos (by omega), show (SCR + 16 * L - SCR) / 16 = L by omega,
          show (SCR + 16 * L - SCR) % 16 = 0 by omega, Nat.add_zero]
      · rw [if_neg q2, mt A hA]
        unfold gMemF
        by_cases q3 : SCR ≤ A ∧ A < SCR + 16 * L ∧ (A - SCR) % 8 = 0
        · rw [if_pos q3, if_pos (by omega)]
        · rw [if_neg q3, if_neg (by omega)]
theorem zs_spec (s : MachineState) (hpc : s.pc = pcOf 43659) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 43663 ∧ t.getReg .x11 = BitVec.ofNat 64 11000 ∧
      t.getReg .x12 = BitVec.ofNat 64 (11000 + 8 * 96) ∧ RegsExcept s t [.x11, .x12] ∧ ∀ a, t.getMem a = s.getMem a := by
  refine ⟨_, symRun_sound RZs (code_cZs hc) s hpc (by simp [RZs.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [RZs.res, rv_simp]
  · simp [RZs.res, rv_simp]
  · simp [RZs.res, rv_simp]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro a; rfl
theorem z_iter (s : MachineState) (hpc : s.pc = pcOf 43663) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (dst + 8 * (n + 1)))
    (hd : dst % 8 = 0) (hbound : dst + 8 * (n + 1) ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if n = 0 then pcOf 43666 else pcOf 43663) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst + 8) ∧ t.getReg .x12 = BitVec.ofNat 64 (dst + 8 * (n + 1)) ∧
      RegsExcept s t [.x11] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = if A = dst then 0 else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  refine ⟨_, symRun_sound RZl (code_cZl hc) s hpc (by
    simp [RZl.res, rv_simp, accessValid_iff, h11, BitVec.toNat_ofNat]
    omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, RZl.res, E.eval, CmpOp.eval, BinOp.eval, h11, h12, ofNat_add_ofNat]
    have he : BitVec.ult (BitVec.ofNat 64 (dst + 8)) (BitVec.ofNat 64 (dst + 8 * (n + 1))) = decide (n ≠ 0) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show dst + 8 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show dst + 8 * (n + 1) < 2 ^ 64 by omega)]
      simp only [decide_eq_decide]
      omega
    rw [he]
    by_cases hn : n = 0 <;> simp [hn]
  · simp [RZl.res, rv_simp, h11, ofNat_add_ofNat]
  · simp [RZl.res, rv_simp, h12]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    have key := ofNat_inj hA (show dst < 2 ^ 64 by omega)
    simp only [Result.toState_getMem, RZl.res, memEval_cons, memEval_nil, Addr.eval, E.eval, h11,
      BitVec.add_zero, key]
    rfl
theorem z_loop (s : MachineState) (hpc : s.pc = pcOf 43663) (dst n : Nat)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 dst) (h12 : s.getReg .x12 = BitVec.ofNat 64 (dst + 8 * n))
    (hn : 0 < n) (hd : dst % 8 = 0) (hbound : dst + 8 * n ≤ MEMORY_BYTES) :
    ∀ i, i ≤ n → ∃ t, Steps im s (3 * i) (3 * i) t ∧
      t.pc = (if i < n then pcOf 43663 else pcOf 43666) ∧
      t.getReg .x11 = BitVec.ofNat 64 (dst + 8 * i) ∧ t.getReg .x12 = BitVec.ofNat 64 (dst + 8 * n) ∧
      RegsExcept s t [.x11] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = clearMem (fun B => s.getMem (BitVec.ofNat 64 B)) dst i A := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, by simpa [hn] using hpc, by simpa using h11, h12, RegsExcept.refl s _, ?_⟩
    intro A _; unfold clearMem; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, pt, t11, t12, rt, mt⟩ := ih (by omega)
    obtain ⟨u, su, pu, u11, u12, ru, mu⟩ := z_iter hc t (by rw [pt, if_pos (by omega)])
      (dst + 8 * i) (n - i - 1) t11 (by rw [t12]; congr 1 <;> omega) (by omega) (by omega)
    refine ⟨u, (st.trans su).of_eq (by omega) (by omega), ?_, ?_, ?_, (rt.trans ru).mono (by decide), ?_⟩
    · rw [pu]; by_cases hz : n - i - 1 = 0
      · rw [if_pos hz, if_neg (by omega)]
      · rw [if_neg hz, if_pos (by omega)]
    · rw [u11]; congr 1 <;> omega
    · rw [u12]; congr 1 <;> omega
    · intro A hA
      rw [mu A hA, mt A hA]
      unfold clearMem
      by_cases ha : A = dst + 8 * i
      · subst A; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg ha]
        by_cases hin : dst ≤ A ∧ A < dst + 8 * i ∧ (A - dst) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
theorem ts_spec (s : MachineState) (hpc : s.pc = pcOf 43666) (leaf : Nat) (hl : leaf < 4096)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 43677 ∧ t.getReg .x10 = BitVec.ofNat 64 (TOPA + 8 * (leaf % 64)) ∧
      t.getReg .x11 = BitVec.ofNat 64 (TOPB + 8 * (leaf / 64)) ∧ t.getReg .x12 = BitVec.ofNat 64 11000 ∧
      RegsExcept s t [.x7, .x10, .x11, .x12, .x28] ∧ ∀ a, t.getMem a = s.getMem a := by
  have h3 : (3#64 : Word).toNat % 64 = 3 := rfl
  have h6' : (6#64 : Word).toNat % 64 = 6 := rfl
  refine ⟨_, symRun_sound RTs (code_cTs hc) s hpc (by simp [RTs.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [RTs.res, rv_simp]
  · simp only [Result.toState_getReg, RTs.res, rv_simp, E.eval, BinOp.eval, h6, h3, ofNat_and63 _ (by omega : leaf < 2 ^ 64),
      ofNat_shl, ofNat_add_ofNat]
    congr 1; unfold TOPA; omega
  · simp only [Result.toState_getReg, RTs.res, rv_simp, E.eval, BinOp.eval, h6, h3, h6',
      ofNat_shr _ _ (by omega : leaf < 2 ^ 64), ofNat_shl, ofNat_add_ofNat]
    congr 1; unfold TOPB; omega
  · simp [RTs.res, rv_simp]
  · c_regs RTs.res
  · intro a; rfl
end
end Post

namespace Post
theorem pSlot_eval {s : MachineState} {leaf : Nat} (j : Nat) (hj : j < 12) (hl : leaf < 4096)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (TOPA + 8 * (leaf % 64)))
    (h11 : s.getReg .x11 = BitVec.ofNat 64 (TOPB + 8 * (leaf / 64)))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 11000) (ht : TopTabAt s) :
    (pSlot j).eval s = BitVec.ofNat 64 (ppNew leaf j) := by
  have h4 : (4#64 : Word).toNat % 64 = 4 := rfl
  have hw : LoadKind.bu.fromWord (s.getMem (s.getReg (pRow j))) (j % 6) = BitVec.ofNat 64 (ppSlot leaf j) := by
    unfold pRow ppSlot
    by_cases h6 : j < 6
    · simp only [h6, if_true]
      rw [h10, ht.1 _ (Nat.mod_lt _ (by norm_num)), Nat.mod_eq_of_lt h6]
      exact topA_ok _ (Nat.mod_lt _ (by norm_num)) j h6
    · simp only [h6, if_false]
      rw [h11, ht.2 _ (by omega), show j % 6 = j - 6 by omega]
      exact topB_ok _ (by omega) (j - 6) (by omega)
  simp only [pSlot, E.eval, UnOp.eval, BinOp.eval]
  rw [hw, h4, ofNat_shl, h12, ofNat_add_ofNat]
  unfold ppNew; congr 1; ring
theorem ppPlace_out (M : Nat → Word) (leaf : Nat) (hl : leaf < 4096) (L : Nat) (hL : L ≤ 12) (A : Nat)
    (hA : A < 11000 ∨ 11768 ≤ A) : ppPlace M leaf L A = M A := by
  induction L with
  | zero => unfold ppPlace; rw [if_neg (by omega)]
  | succ L ih =>
    have := ppSlot_le leaf L (by omega) hl
    unfold ppPlace; unfold ppNew
    rw [if_neg (by omega), if_neg (by omega)]
    exact ih (by omega)
theorem gMemF_scr (M : Nat → Word) (leaf L k : Nat) (hk : k < L) (d : Nat) (hd : d = 0 ∨ d = 8) :
    gMemF M leaf L (SCR + 16 * k + d) = M (ppOld leaf k + d) := by
  unfold gMemF
  rw [if_pos (by omega), show (SCR + 16 * k + d - SCR) / 16 = k by omega, show (SCR + 16 * k + d - SCR) % 16 = d by omega]
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem p_spec (j : Nat) (hj : j < 12) (s : MachineState) (hpc : s.pc = pcOf (43677 + 7 * j)) (leaf : Nat)
    (hl : leaf < 4096) (h10 : s.getReg .x10 = BitVec.ofNat 64 (TOPA + 8 * (leaf % 64)))
    (h11 : s.getReg .x11 = BitVec.ofNat 64 (TOPB + 8 * (leaf / 64)))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 11000) (h13 : s.getReg .x13 = BitVec.ofNat 64 SCR) (ht : TopTabAt s) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf (43677 + 7 * (j + 1)) ∧ RegsExcept s t [.x7, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = ppNew leaf j + 8 then s.getMem (BitVec.ofNat 64 (SCR + 16 * j + 8))
        else if A = ppNew leaf j then s.getMem (BitVec.ofNat 64 (SCR + 16 * j))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hS : SCR = 0x40000 := rfl
  have hTA : TOPA = 16776064 := rfl
  have hTB : TOPB = 16776576 := rfl
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hsl := ppSlot_le leaf j hj hl
  have hp := pSlot_eval j hj hl h10 h11 h12 ht
  have hscr : ∀ k, (pScr k).eval s = BitVec.ofNat 64 (SCR + k) := fun k => by
    unfold pScr
    split
    · rename_i hk; subst hk; simp only [E.eval, h13, Nat.add_zero]
    · simp only [E.eval, BinOp.eval, h13, ofNat_add_ofNat]
  have hobl : (pRes j).obligs s := by
    show Oblig.all s _
    rw [Oblig.all_iff]
    intro o ho'
    simp only [pRes, List.mem_cons, List.not_mem_nil, or_false] at ho'
    rcases ho' with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hp, ofNat_add_ofNat]
      exact valid8 _ (by unfold ppNew; omega) (by unfold ppNew; omega)
    · simp only [Oblig.holds, Addr.eval, hp, BitVec.add_zero]
      exact valid8 _ (by unfold ppNew; omega) (by unfold ppNew; omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, h13, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, h13, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, E.eval, pRow]
      split
      · rw [h10, toNat_ofNat_lt (by omega)]; omega
      · rw [h11, toNat_ofNat_lt (by omega)]; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, pRow]
      split
      · rw [h10, ofNat_add_ofNat, accessValid_iff, toNat_ofNat_lt (by omega)]
        exact ⟨by omega, Nat.mod_one _⟩
      · rw [h11, ofNat_add_ofNat, accessValid_iff, toNat_ofNat_lt (by omega)]
        exact ⟨by omega, Nat.mod_one _⟩
  refine ⟨_, symRun_sound (run_p j hj) (code_cP hc j hj) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pRes, E.eval]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [Result.toState_getReg]
    cases r <;> first | exact absurd rfl hr.1 | exact absurd rfl hr.2.1 | exact absurd rfl hr.2.2 | rfl
  · intro A hA
    have e8 := hscr (16 * j + 8)
    have e0 := hscr (16 * j)
    simp only [Result.toState_getMem, pRes, memEval_cons, memEval_nil, Addr.eval, E.eval, hp, e8, e0,
      ofNat_add_ofNat, BitVec.add_zero]
    rw [show SCR + (16 * j + 8) = SCR + 16 * j + 8 by omega]
    have hn : ppNew leaf j + 8 < 2 ^ 64 := by unfold ppNew; omega
    by_cases q1 : A = ppNew leaf j + 8
    · rw [if_pos (by rw [q1]), if_pos q1]
    · rw [if_neg (fun h => q1 ((ofNat_inj hA hn).mp h)), if_neg q1]
      by_cases q2 : A = ppNew leaf j
      · rw [if_pos (by rw [q2]), if_pos q2]
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), if_neg q2]
/-- The common post-pass: from 43500 to word 43761 (546 steps). Outside the scratch area the
memory is `ppPlace M leaf 12`. -/
theorem post_prefix_spec (s : MachineState) (hpc : s.pc = pcOf 43500) (leaf : Nat) (hl : leaf < 4096)
    (hix : s.getMem (BitVec.ofNat 64 96) >>> 52 = BitVec.ofNat 64 leaf) (ht : TopTabAt s) :
    ∃ t, Steps im s 546 546 t ∧ t.pc = pcOf 43761 ∧
      ∀ A < 2 ^ 64, ¬ (SCR ≤ A ∧ A < SCR + 192) →
        t.getMem (BitVec.ofNat 64 A) = ppPlace (fun B => s.getMem (BitVec.ofNat 64 B)) leaf 12 A := by
  have hS : SCR = 0x40000 := rfl
  have hTA : TOPA = 16776064 := rfl
  have hTB : TOPB = 16776576 := rfl
  obtain ⟨s1, h1, p1, r1, m1⟩ : ∃ t, Steps im s 0 0 t ∧ t.pc = pcOf 43500 ∧ RegsExcept s t [] ∧
      ∀ a, t.getMem a = s.getMem a := ⟨s, Steps.refl s, hpc, RegsExcept.refl s _, fun _ => rfl⟩
  obtain ⟨s2, h2, p2, x6, x13, r2, m2⟩ := pro_spec hc s1 p1
  have x6' : s2.getReg .x6 = BitVec.ofNat 64 leaf := by rw [x6, m1, hix]
  have e2 : (fun B => s2.getMem (BitVec.ofNat 64 B)) = (fun B => s.getMem (BitVec.ofNat 64 B)) :=
    funext fun B => by rw [m2, m1]
  obtain ⟨s3, h3, p3, r3, m3⟩ := g_loop hc s2 p2 leaf hl x6' x13 12 le_rfl
  rw [e2] at m3
  obtain ⟨s4, h4, p4, x11, x12, r4, m4⟩ := zs_spec hc s3 (by simpa using p3)
  obtain ⟨s5, h5, p5, y11, y12, r5, m5⟩ := z_loop hc s4 p4 11000 96 x11 x12 (by norm_num) (by norm_num) (by decide)
    96 le_rfl
  rw [if_neg (by omega)] at p5
  have x6'' : s5.getReg .x6 = BitVec.ofNat 64 leaf := by
    rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), x6']
  obtain ⟨s6, h6, p6, z10, z11, z12, r6, m6⟩ := ts_spec hc s5 p5 leaf hl x6''
  have z13 : s6.getReg .x13 = BitVec.ofNat 64 SCR := by
    rw [r6.get (by decide), r5.get (by decide), r4.get (by decide), r3.get (by decide), x13]
  set M := fun B => s.getMem (BitVec.ofNat 64 B) with hM
  have hm6 : ∀ A < 2 ^ 64, s6.getMem (BitVec.ofNat 64 A) =
      if SCR ≤ A ∧ A < SCR + 192 ∧ (A - SCR) % 8 = 0 then gMemF M leaf 12 A else ppPlace M leaf 0 A := by
    intro A hA
    rw [m6, m5 A hA]
    unfold clearMem
    have e4 : (fun B => s4.getMem (BitVec.ofNat 64 B)) = (fun B => s3.getMem (BitVec.ofNat 64 B)) :=
      funext fun B => by rw [m4]
    rw [e4]
    unfold ppPlace
    by_cases hz : 11000 ≤ A ∧ A < 11000 + 8 * 96 ∧ (A - 11000) % 8 = 0
    · rw [if_pos hz, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg hz]
      simp only
      rw [m3 A hA]
      by_cases hs : SCR ≤ A ∧ A < SCR + 192 ∧ (A - SCR) % 8 = 0
      · rw [if_pos hs]
      · rw [if_neg hs, if_neg (by omega)]
        unfold gMemF; rw [if_neg (by omega)]
  have place : ∀ L ≤ 12, ∃ t, Steps im s6 (7 * L) (7 * L) t ∧ t.pc = pcOf (43677 + 7 * L) ∧
      RegsExcept s6 t [.x7, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if SCR ≤ A ∧ A < SCR + 192 ∧ (A - SCR) % 8 = 0 then gMemF M leaf 12 A else ppPlace M leaf L A := by
    intro L
    induction L with
    | zero => intro _; exact ⟨s6, Steps.refl s6, by simpa using p6, RegsExcept.refl s6 _, hm6⟩
    | succ L ih =>
      intro hL
      obtain ⟨t, st, pt, rt, mt⟩ := ih (by omega)
      have htt : TopTabAt t := by
        refine ⟨fun k hk => ?_, fun k hk => ?_⟩
        · rw [mt _ (by omega), if_neg (by omega), ppPlace_out M leaf hl L (by omega) _ (by omega)]
          exact ht.1 k hk
        · rw [mt _ (by omega), if_neg (by omega), ppPlace_out M leaf hl L (by omega) _ (by omega)]
          exact ht.2 k hk
      have hsl := ppSlot_le leaf L (by omega) hl
      obtain ⟨u, su, pu, ru, mu⟩ := p_spec hc L (by omega) t pt leaf hl
        (by rw [rt.get (by decide), z10]) (by rw [rt.get (by decide), z11]) (by rw [rt.get (by decide), z12])
        (by rw [rt.get (by decide), z13]) htt
      refine ⟨u, (st.trans su).of_eq (by ring) (by ring), pu, (rt.trans ru).mono (by decide),
        fun A hA => ?_⟩
      rw [mu A hA]
      by_cases q1 : A = ppNew leaf L + 8
      · rw [if_pos q1, mt _ (by omega), if_pos (by omega), gMemF_scr M leaf 12 L (by omega) 8 (Or.inr rfl)]
        rw [if_neg (by unfold ppNew at q1; omega)]
        unfold ppPlace; rw [if_pos q1]
      · rw [if_neg q1]
        by_cases q2 : A = ppNew leaf L
        · rw [if_pos q2, mt _ (by omega), if_pos (by omega)]
          have := gMemF_scr M leaf 12 L (by omega) 0 (Or.inl rfl)
          rw [Nat.add_zero, Nat.add_zero] at this
          rw [this, if_neg (by unfold ppNew at q2; omega)]
          unfold ppPlace; rw [if_neg q1, if_pos q2]
        · rw [if_neg q2, mt A hA]
          by_cases hs : SCR ≤ A ∧ A < SCR + 192 ∧ (A - SCR) % 8 = 0
          · rw [if_pos hs, if_pos hs]
          · rw [if_neg hs, if_neg hs]
            conv_rhs => unfold ppPlace
            rw [if_neg q1, if_neg q2]
  obtain ⟨s7, h7, p7, r7, m7⟩ := place 12 le_rfl
  refine ⟨s7, (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))).of_eq
    (by norm_num) (by norm_num), by simpa using p7, fun A hA hn => ?_⟩
  rw [m7 A hA, if_neg (by omega)]

end
end Post

namespace Post
theorem ppSlot_inj (leaf : Nat) (hl : leaf < 4096) (j L : Nat) (hj : j < 12) (hL : L < 12)
    (h : ppSlot leaf j = ppSlot leaf L) : j = L := by
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hr' : leaf / 64 < 64 := by omega
  unfold ppSlot at h
  by_cases h6 : j < 6 <;> by_cases h6' : L < 6
  · rw [if_pos h6, if_pos h6'] at h; exact slots_ok.2.2.1 _ hr j h6 L h6' h
  · rw [if_pos h6, if_neg h6'] at h
    have := (slots_ok.1 _ hr j h6).1; have := slots_ok.2.1 _ hr' (L - 6) (by omega); omega
  · rw [if_neg h6, if_pos h6'] at h
    have := (slots_ok.1 _ hr L h6').1; have := slots_ok.2.1 _ hr' (j - 6) (by omega); omega
  · rw [if_neg h6, if_neg h6'] at h
    have := slots_ok.2.2.2 _ hr' (j - 6) (by omega) (L - 6) (by omega) h; omega
/-- A placed sibling: the word `d ∈ {0, 8}` of slot `ppSlot leaf j` holds the old sibling's word. -/
theorem ppPlace_hit (M : Nat → Word) (leaf : Nat) (hl : leaf < 4096) (j : Nat) (hj : j < 12) (d : Nat)
    (hd : d = 0 ∨ d = 8) : ppPlace M leaf 12 (ppNew leaf j + d) = M (ppOld leaf j + d) := by
  have key : ∀ L, j < L → L ≤ 12 → ppPlace M leaf L (ppNew leaf j + d) = M (ppOld leaf j + d) := by
    intro L
    induction L with
    | zero => intro h; omega
    | succ L ih =>
      intro h1 h2
      unfold ppPlace
      by_cases hL : L = j
      · subst hL
        rcases hd with rfl | rfl
        · rw [if_neg (by omega), if_pos (by omega), Nat.add_zero]
        · rw [if_pos rfl]
      · have hne : ppSlot leaf j ≠ ppSlot leaf L := fun h => hL (ppSlot_inj leaf hl j L hj (by omega) h).symm
        unfold ppNew
        rw [if_neg (by omega), if_neg (by omega)]
        exact ih (by omega) (by omega)
  exact key 12 hj le_rfl
/-- An unplaced word of the area is zero. -/
theorem ppPlace_miss (M : Nat → Word) (leaf : Nat) (q : Nat) (hq : q < 96)
    (hm : ∀ j < 12, ¬ (16 * ppSlot leaf j ≤ 8 * q ∧ 8 * q < 16 * ppSlot leaf j + 16)) :
    ppPlace M leaf 12 (11000 + 8 * q) = 0 := by
  have key : ∀ L ≤ 12, ppPlace M leaf L (11000 + 8 * q) = 0 := by
    intro L
    induction L with
    | zero => intro _; unfold ppPlace; rw [if_pos (by omega)]
    | succ L ih =>
      intro hL
      have := hm L (by omega)
      unfold ppPlace; unfold ppNew
      rw [if_neg (by omega), if_neg (by omega)]
      exact ih (by omega)
  exact key 12 le_rfl
end Post
namespace Post
theorem ppPlace_congr (M M' : Nat → Word) (h : ∀ B < 2 ^ 64, M B = M' B) (leaf : Nat) (hl : leaf < 4096) :
    ∀ L ≤ 12, ∀ A < 2 ^ 64, ppPlace M leaf L A = ppPlace M' leaf L A := by
  intro L
  induction L with
  | zero => intro _ A hA; unfold ppPlace; split_ifs <;> first | rfl | exact h A hA
  | succ L ih =>
    intro hL A hA
    have := ppOld_lt leaf L
    unfold ppPlace
    split_ifs
    · exact h _ (by omega)
    · exact h _ (by omega)
    · exact ih (by omega) A hA
end Post
/-- Pairing stage 1: the buffer pass (layout block), then the top-path post-pass (2295 + 546 steps, to 43761). -/
theorem bufferPost_prefix_spec {im : Image} (hc : CompactCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 42716)
    (leaf : Nat) (hl : leaf < 4096) (hix : s.getMem (BitVec.ofNat 64 96) >>> 52 = BitVec.ofNat 64 leaf)
    (ht : TopTabAt s) :
    ∃ t, Steps im s 2841 2841 t ∧ t.pc = pcOf 43761 ∧
      ∀ A < 2 ^ 64, ¬ (Post.SCR ≤ A ∧ A < Post.SCR + 192) →
        t.getMem (BitVec.ofNat 64 A) = Post.ppPlace (bufferMem (fun B => s.getMem (BitVec.ofNat 64 B))) leaf 12 A := by
  have hTA : TOPA = 16776064 := rfl
  have hTB : TOPB = 16776576 := rfl
  obtain ⟨q, sq, pq, mq0⟩ := buffer_spec hc s hpc
  have mq : ∀ A < 2 ^ 64, q.getMem (BitVec.ofNat 64 A) = bufferMem (fun B => s.getMem (BitVec.ofNat 64 B)) A :=
    fun A hA => mq0 A hA
  have hout : ∀ A, A < 23008 ∨ 26144 ≤ A → A ≠ 1240 → bufferMem (fun B => s.getMem (BitVec.ofNat 64 B)) A =
      s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    unfold bufferMem Layout.lbMem Layout.itMem
    rw [if_neg h1]
    split_ifs with h2 h3 <;> first | rfl | omega
  have hq96 : q.getMem (BitVec.ofNat 64 96) = s.getMem (BitVec.ofNat 64 96) := by
    rw [mq 96 (by norm_num), hout 96 (by omega) (by omega)]
  have hqt : TopTabAt q := by
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [mq _ (by omega), hout _ (by omega) (by omega)]; exact ht.1 k hk
    · rw [mq _ (by omega), hout _ (by omega) (by omega)]; exact ht.2 k hk
  obtain ⟨t, st, pt, mt⟩ := Post.post_prefix_spec hc q pq leaf hl (by rw [hq96]; exact hix) hqt
  refine ⟨t, (sq.trans st).of_eq (by norm_num) (by norm_num), pt, fun A hA hn => ?_⟩
  rw [mt A hA hn]
  exact Post.ppPlace_congr _ _ (fun B hB => mq B hB) leaf hl 12 le_rfl A hA

end ClaudeWCT.W9.Machine.Expand.Compact2.Buffer
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Wit ====
section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer height chainCount LayerSignature route readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap window_flatMap_const
  window_full window_zeros window_take zeros wordsOf layerBytes layerBytes_length layerBytes_merkle layerBytes_chain)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Expand.OldW (headerBytes wctBytes regionBytes layerRegion tailBytes lowerPathBytes headerBytes_length
  regionBytes_length regionLen regionCell regionCell_length
  wct_prefix wctBytes_length layers_length tailBytes_length)
open ClaudeWCT.W9.Machine.Expand (witListV6 wctBytesV6 layerRegionV6 layerBytesBCV6 bcTopBlockV6 wctBytesV6_length
  witListV6_length layerRegionV6_length layersV6_length headerBytesV5 headerBytesV5_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
open ClaudeWCT.W9.Machine.Expand.OldW (pathSlots layerBase layerBase_ge layerEnd_le layerRegion_length layer_prefix)
theorem window_window' (L : List UInt8) (o m a n : Nat) (h : a + n ≤ m) :
    window (window L o m) a n = window L (o + a) n := by
  unfold window
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
section
variable (N : HashOutput) (w : WCT9.Witness)
theorem v6_head (o : Nat) (h : o + 8 ≤ 64) : window (witListV6 N w) o 8 = window (headerBytesV5 w) o 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_left _ _ _ _ (by rw [headerBytesV5_length]; omega)]
def layOffV6 (lay : Layer) : Nat := (![0, 4224, 7424, 10560] : Layer → Nat) lay
theorem v6_layer (lay : Layer) (j : Nat) (hj : j + 8 ≤ 64 * (height lay + ClaudeWCT.W9.Machine.Expand.chainSlotsV6 lay)) :
    window (witListV6 N w) (8136 + layOffV6 lay + j) 8 = window (layerRegionV6 N w lay) j 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_right (headerBytesV5 w) _ _ _ (by rw [headerBytesV5_length]; omega), headerBytesV5_length,
    window_append_right (wctBytesV6 N w.signature) _ _ _ (by rw [wctBytesV6_length]; omega), wctBytesV6_length,
    window_append_right (zeros 8) _ _ _ (by simp [zeros]; omega), show (zeros 8).length = 8 by simp [zeros]]
  have hlen : ((List.finRange 4)[lay.val]'(by simp)) = lay := by simp
  have key := window_flatMap (List.finRange 4) (layerRegionV6 N w) lay.val (by simp) j 8
    (by rw [hlen, layerRegionV6_length]; omega)
  have hpre : (((List.finRange 4).take lay.val).map fun l => (layerRegionV6 N w l).length).sum = layOffV6 lay := by
    simp only [layerRegionV6_length]
    fin_cases lay <;> decide
  rw [hpre, hlen] at key
  rw [show 8136 + layOffV6 lay + j - 64 - 8064 - 8 = layOffV6 lay + j by omega, key]

end
section lower
variable {lay : Layer} (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32)
def canon (j : Fin (height lay)) (d : Nat) : List UInt8 :=
  if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) then window (bytesLE 16 (ls.path j)) 0 8
  else if d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 then window (bytesLE 16 (ls.path j)) 8 8
  else if d = 32 ∧ j.val = height lay - 1 then bytesLE 4 ctr ++ zeros 4
  else zeros 8
theorem sibOff_vals (b : Nat) : SigGolfCandidate.T3M.sibOff b = 0 ∨ SigGolfCandidate.T3M.sibOff b = 48 := by
  unfold SigGolfCandidate.T3M.sibOff; split <;> simp
theorem win8_of_16 (L : List UInt8) (x a : Nat) (ha : a + 8 ≤ 16) :
    window L (x + a) 8 = window (window L x 16) a 8 := (window_window' L x 16 a 8 ha).symm
theorem block_win (P : List UInt8) (hP : P.length = 16) (b : Bool) (d : Nat) (hd : d % 8 = 0) (hd' : d + 8 ≤ 64) :
    window (if b then P ++ zeros 48 else zeros 48 ++ P) d 8 =
      if d = (if b then 0 else 48) then window P 0 8 else if d = (if b then 0 else 48) + 8 then window P 8 8
      else zeros 8 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    by_cases h48 : 48 ≤ d
    · rw [window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 48).length = 48 by simp [zeros]]
      rcases (show d = 48 ∨ d = 56 by omega) with rfl | rfl
      · simp
      · simp
    · rw [window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega),
        if_neg (by omega), if_neg (by omega)]
  · simp only [if_true]
    by_cases h16 : d < 16
    · rw [window_append_left _ _ _ _ (by rw [hP]; omega)]
      rcases (show d = 0 ∨ d = 8 by omega) with rfl | rfl
      · simp
      · simp
    · rw [window_append_right _ _ _ _ (by rw [hP]; omega), hP, window_zeros _ _ _ (by omega),
        if_neg (by omega), if_neg (by omega)]
end lower
section lowerAB
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
theorem window_drop (L : List UInt8) (k x n : Nat) : window (L.drop k) x n = window L (k + x) n := by
  unfold window; rw [List.drop_drop]
theorem v6_block (j : Fin (height lay)) (d : Nat) (hd : d % 8 = 0) (hd' : d + 8 ≤ 64)
    (hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) ∨
      d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 ∨ d = 32 ∨ d = 40) :
    window (layerBytesBCV6 lay leaf ls ctr) (64 * (height lay - 1 - j.val) + d) 8 = canon leaf ls ctr j d := by
  have hj := j.isLt
  have hs := sibOff_vals (leaf / 2 ^ j.val % 2)
  unfold layerBytesBCV6
  by_cases htop : j.val = height lay - 1
  · rw [show 64 * (height lay - 1 - j.val) + d = d by rw [htop]; simp,
      window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega)]
    have hT : WCT9.topLevel lay = j := Fin.ext (by unfold WCT9.topLevel; simp [htop])
    unfold bcTopBlockV6 canon
    rw [hT, ← htop]
    unfold SigGolfCandidate.T3M.sibOff at hdv ⊢
    split
    · rename_i hb
      simp only [hb, if_true] at hdv ⊢
      rcases hdv with rfl | rfl | rfl | rfl
      · simp only [if_true]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length])]
      · simp only [show (0 : Nat) + 8 = 8 from rfl, show (8 : Nat) ≠ 0 by decide, if_true, if_false]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_left _ _ _ _ (by simp [zeros, bytesLE_length])]
      · simp only [show (32 : Nat) ≠ 0 by decide, show (32 : Nat) ≠ 0 + 8 by decide, if_false, true_and, if_true]
        rw [show bytesLE 16 (ls.path j) ++ zeros 16 ++ bytesLE 4 ctr ++ zeros 28 =
          (bytesLE 16 (ls.path j) ++ zeros 16) ++ (bytesLE 4 ctr ++ zeros 28) by simp [List.append_assoc],
          window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 32 - (bytesLE 16 (ls.path j) ++ zeros 16).length = 0 by simp [zeros, bytesLE_length]]
        unfold window
        simp only [List.drop_zero, List.append_assoc]
        rw [show 8 = (bytesLE 4 ctr).length + 4 by rw [bytesLE_length], List.take_append]
        simp [zeros]
      · simp only [show (40 : Nat) ≠ 0 by decide, show (40 : Nat) ≠ 0 + 8 by decide, if_false,
          show (40 : Nat) ≠ 32 by decide, false_and]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 40 - (bytesLE 16 (ls.path j) ++ zeros 16 ++ bytesLE 4 ctr).length = 4 by simp [zeros, bytesLE_length],
          window_zeros _ _ _ (by omega)]
    · rename_i hb
      simp only [hb, if_false] at hdv ⊢
      rcases hdv with rfl | rfl | rfl | rfl
      · simp only [if_true]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 48 - (zeros 32 ++ bytesLE 4 ctr ++ zeros 12).length = 0 by simp [zeros, bytesLE_length]]
      · simp only [show (48 : Nat) + 8 ≠ 48 by decide, if_true, if_false]
        rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 48 + 8 - (zeros 32 ++ bytesLE 4 ctr ++ zeros 12).length = 8 by simp [zeros, bytesLE_length]]
      · simp only [show (32 : Nat) ≠ 48 by decide, show (32 : Nat) ≠ 48 + 8 by decide, if_false, true_and, if_true]
        rw [show zeros 32 ++ bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path j) =
          zeros 32 ++ (bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path j)) by simp [List.append_assoc],
          window_append_right _ _ _ _ (by simp [zeros]), show 32 - (zeros 32).length = 0 by simp [zeros]]
        unfold window
        simp only [List.drop_zero, List.append_assoc]
        rw [show 8 = (bytesLE 4 ctr).length + 4 by rw [bytesLE_length], List.take_append]
        simp [zeros]
      · simp only [show (40 : Nat) ≠ 48 by decide, show (40 : Nat) ≠ 48 + 8 by decide, if_false,
          show (40 : Nat) ≠ 32 by decide, false_and]
        rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]),
          window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]),
          show 40 - (zeros 32 ++ bytesLE 4 ctr).length = 4 by simp [zeros, bytesLE_length],
          window_zeros _ _ _ (by omega)]
  · have hjl : j.val + 1 < height lay := by omega
    rw [window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega),
      ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length, window_drop,
      show 64 + (64 * (height lay - 1 - j.val) + d - 64) = 64 * (height lay - 1 - j.val) + (d - d % 16) + d % 16 by
        omega,
      win8_of_16 _ _ _ (by omega), layerBytes_merkle lay leaf ls j (d - d % 16) (by omega),
      window_window' _ _ _ _ _ (by omega), show d - d % 16 + d % 16 = d by omega]
    have hbk := block_win (bytesLE 16 (ls.path j)) (bytesLE_length _ _) (decide (leaf / 2 ^ j.val % 2 = 1)) d hd hd'
    simp only [decide_eq_true_eq] at hbk
    rw [hbk]
    unfold canon SigGolfCandidate.T3M.sibOff
    by_cases hb : leaf / 2 ^ j.val % 2 = 1
    · simp only [hb, if_true]
      rw [if_neg (show ¬ (d = 32 ∧ j.val = height lay - 1) by omega)]
    · simp only [hb, if_false]
      rw [if_neg (show ¬ (d = 32 ∧ j.val = height lay - 1) by omega)]
end lowerAB
section lowerBC
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
theorem window_split (L : List UInt8) (o a b : Nat) :
    window L o (a + b) = window L o a ++ window L (o + a) b := by
  unfold window
  rw [List.take_add, List.drop_drop]
include hlay hleaf
theorem v7_block (j : Fin (height lay)) (d : Nat) (hd' : d + 8 ≤ 64)
    (hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) ∨
      d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 ∨ d = 32 ∨ d = 40) :
    window (lowerPathBytes lay leaf ls ctr) (16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + d) 8 =
      canon leaf ls ctr j d := by
  have hj := j.isLt
  have hs := sibOff_vals (leaf / 2 ^ j.val % 2)
  have hsib := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_sib hlay hleaf ls ctr j
  unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot at hsib
  unfold canon
  rcases hdv with h | h | h | h
  · subst h
    rw [if_pos rfl, show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) = 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 0 from rfl, win8_of_16 _ _ _ (by omega), hsib]
  · subst h
    rw [if_neg (by omega), if_pos rfl, show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 +
      (SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8) = 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 +
      SigGolfCandidate.T3M.sibOff (leaf / 2 ^ j.val % 2) + 8 by omega, win8_of_16 _ _ _ (by omega), hsib]
  · subst h
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases htop : j.val = height lay - 1
    · rw [if_pos ⟨rfl, htop⟩]
      have hc := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_ctr hlay hleaf ls ctr
      have hr := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_rowPad hlay hleaf ls ctr
      unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerCtrSlot at hc hr
      rw [← htop] at hc hr
      rw [show (8 : Nat) = 4 + 4 from rfl, window_split, hc,
        show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 4 =
          16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 4 + 0 from rfl,
        ← window_window' _ _ 12 0 4 (by omega), hr, window_zeros _ _ _ (by omega)]
    · rw [if_neg (by omega)]
      have hp := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_pad hlay hleaf ls ctr (j := j.val) (by omega)
      rw [show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 =
        16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 0 from rfl, win8_of_16 _ _ _ (by omega), hp,
        window_zeros _ _ _ (by omega)]
  · subst h
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    by_cases htop : j.val = height lay - 1
    · have hr := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_rowPad hlay hleaf ls ctr
      unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerCtrSlot at hr
      rw [← htop] at hr
      rw [show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 40 =
          16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 4 + 4 by omega,
        ← window_window' _ _ 12 4 8 (by omega), hr, window_zeros _ _ _ (by omega)]
    · have hp := ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_pad hlay hleaf ls ctr (j := j.val) (by omega)
      rw [show 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 40 =
        16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 + 8 by omega, win8_of_16 _ _ _ (by omega), hp,
        window_zeros _ _ _ (by omega)]
end lowerBC
section lowerC
variable {lay : Layer} (hlay : lay.val ≠ 0) {leaf : Nat} (hleaf : leaf < 2 ^ height lay) (ls : LayerSignature lay)
  (ctr : BitVec 32)
include hlay hleaf
theorem v7_free (p : Nat) (hp8 : p % 8 = 0) (hp' : p + 8 ≤ 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots lay)
    (hnot : ∀ j : Fin (height lay), p ≠ ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot lay leaf j.val ∧
      p ≠ ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot lay leaf j.val + 8 ∧
      p ≠ 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 32 ∧
      p ≠ 16 * (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay leaf).getD j.val 0 + 40)
    (hhi : p ≠ ClaudeWCT.W9.Machine.Expand.OldW.lowerHiSlot lay leaf) :
    window (lowerPathBytes lay leaf ls ctr) p 8 = zeros 8 := by
  have hsl : ∀ j : Fin (height lay), ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot lay leaf j.val % 16 = 0 := fun j => by
    unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot
    rcases sibOff_vals (leaf / 2 ^ j.val % 2) with h | h <;> rw [h] <;> omega
  have hh : 1 ≤ height lay := ClaudeWCT.W9.Machine.Expand.OldW.height_pos' lay
  unfold lowerPathBytes
  rw [ClaudeWCT.W9.Machine.Expand.OldW.window_map_range _ _ _ _ hp']
  have hz : ∀ i ∈ List.range 8, ClaudeWCT.W9.Machine.Expand.OldW.lowerPathByte lay leaf ls ctr (p + i) = (fun _ => (0 : UInt8)) i := by
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [ClaudeWCT.W9.Machine.Expand.OldW.lowerPathByte_free ls ctr (fun j => by
      have := hnot j; have := hsl j; omega)]
    have hc := hnot ⟨height lay - 1, by omega⟩
    simp only at hc
    unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerCtrSlot
    unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerHiSlot at hhi ⊢
    rw [if_neg (by omega), if_neg (by omega)]
  rw [List.map_congr_left hz]
  simp [zeros, List.map_const']
end lowerC
theorem wordsOf_getD' (L : List UInt8) (m : Nat) (hL : L.length = 8 * m) (i : Nat) (hi : i < m) :
    (wordsOf L).getD i 0 = BitVec.ofNat 64 (readLE (window L (8 * i) 8)) := by
  rw [SigGolfCandidate.T3M.wordsOf_eq_range m L hL, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hw : readLE (window L (8 * i) 8) < 2 ^ 64 := by
    have := SigGolfCandidate.T3M.readLE_lt (window L (8 * i) 8)
    have hl : (window L (8 * i) 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L (8 * i) 8) < 256 ^ (window L (8 * i) 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hw, show 2 ^ (64 * i) = 256 ^ (8 * i) by rw [pow_mul, pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop, show 2 ^ 64 = 256 ^ 8 by norm_num, SigGolfCandidate.T3M.readLE_take]
  rfl
section ident
variable (N : HashOutput) (w : WCT9.Witness)
def v6M (B : Nat) : Word := (wordsOf (witListV6 N w)).getD ((B - WIT) / 8) 0
theorem v6M_eq (x : Nat) (hx : x % 8 = 0) (hx' : x + 8 ≤ 21832) :
    v6M N w (WIT + x) = BitVec.ofNat 64 (readLE (window (witListV6 N w) x 8)) := by
  unfold v6M
  rw [show (WIT + x - WIT) / 8 = x / 8 by omega, wordsOf_getD' _ 2729 (by rw [witListV6_length]) _ (by omega),
    show 8 * (x / 8) = x by omega]
theorem lroute_eq (lay : Layer) (hl : lay.val ≠ 0) (idx : Nat) :
    lroute lay.val idx = (route idx lay).1 := by
  unfold lroute route
  fin_cases lay <;> simp_all [height]
theorem plan_eq (lay : Layer) (r j : Nat) : plan lay.val r j = (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan lay r).getD j 0 := by
  unfold plan; congr 2; ext; simp [Nat.mod_eq_of_lt lay.isLt]
theorem lvSrc_eq (lay : Layer) (hl : lay.val ≠ 0) (j : Nat) (hj : j < height lay) :
    lvSrc lay.val j - SNAP2 = 8136 + layOffV6 lay + 64 * (height lay - 1 - j) := by
  unfold lvSrc SNAP2 layOffV6
  fin_cases lay <;> simp_all [height] <;> omega
theorem lvH_eq (lay : Layer) (hl : lay.val ≠ 0) : lvH lay.val = height lay := by
  unfold lvH; fin_cases lay <;> simp_all [height]
theorem lvDst_eq (lay : Layer) (hl : lay.val ≠ 0) : lvDst lay.val - WIT = ClaudeWCT.W9.Machine.Expand.OldW.layerBase lay + 856 ∧
    pathTop lay.val = 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots lay ∧
    chDst lay.val - WIT = ClaudeWCT.W9.Machine.Expand.OldW.layerBase lay + 856 + 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots lay ∧
    chSrc lay.val - SNAP2 = 8136 + layOffV6 lay + 64 * height lay := by
  unfold chDst chSrc pathTop
  unfold lvDst WIT SNAP2 layOffV6 ClaudeWCT.W9.Machine.Expand.OldW.layerBase ClaudeWCT.W9.Machine.Expand.OldW.pathSlots
  fin_cases lay <;> simp_all [height]
end ident
theorem wu_small (X : Nat) (hX : X < 2 ^ 32) : LoadKind.wu.fromWord (BitVec.ofNat 64 X) 0 = BitVec.ofNat 64 X := by
  apply BitVec.eq_of_toNat_eq
  simp only [LoadKind.fromWord, extractWord32, Nat.zero_div, Nat.zero_mul, BitVec.ushiftRight_zero,
    BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : X < 2 ^ 64), Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt (by omega : X < 2 ^ 64)]
section ident2
variable (N : HashOutput) (w : WCT9.Witness)
/-- C4: past the 768-byte path area the top region holds the chain blocks in both layouts. -/
theorem layerRegion_top_tail (p : Nat) (hp : 768 ≤ p) (n : Nat) :
    window (layerRegion N w 0) p n = window (layerRegionV6 N w 0) p n := by
  unfold layerRegion layerRegionV6 ClaudeWCT.W9.Machine.Expand.layerBytesV6
  have h63 : 64 * (height (0 : Layer) + chainCount (0 : Layer)) = 4032 := rfl
  have htl : ((layerBytes 0 (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)).take 768).length = 768 := by
    rw [List.length_take, layerBytes_length, h63]; omega
  rw [if_pos (show (0 : Layer).val = 0 from rfl), if_pos (show (0 : Layer).val = 0 from rfl),
    if_pos (show (0 : Layer).val = 0 from rfl), List.append_assoc,
    window_append_right (ClaudeWCT.W9.Machine.Expand.OldW.topPathBytes _ _) _ _ _
      (by rw [ClaudeWCT.W9.Machine.Expand.OldW.topPathBytes_length]; exact hp),
    window_append_right (List.take 768 _) _ _ _ (by rw [htl]; exact hp),
    ClaudeWCT.W9.Machine.Expand.OldW.topPathBytes_length, htl, ClaudeWCT.W9.Machine.Expand.OldW.pathSlots_top,
    ClaudeWCT.W9.Machine.Expand.OldW.height_top]
theorem rootOff_eq_hi (L : Layer) (hL : L.val ≠ 0) (idx : Nat) :
    rootOff L.val (lroute L.val idx) = ClaudeWCT.W9.Machine.Expand.OldW.lowerHiSlot L (route idx L).1 := by
  unfold rootOff ClaudeWCT.W9.Machine.Expand.OldW.lowerHiSlot
  rw [plan_eq, lroute_eq L hL]
  congr 3
  unfold rootJ; fin_cases L <;> simp_all [height]
end ident2
theorem ofNat_readLE_zeros8 : BitVec.ofNat 64 (readLE (zeros 8)) = 0 := by decide
section chainarea
variable (N : HashOutput) (w : WCT9.Witness)
theorem lower_cc (L : Layer) (hL : L.val ≠ 0) : chainCount L = 43 := by
  fin_cases L <;> simp_all [chainCount]
theorem lower_area (L : Layer) (hL : L.val ≠ 0) : ClaudeWCT.W9.Machine.Expand.OldW.chainArea L = 2248 := by
  unfold ClaudeWCT.W9.Machine.Expand.OldW.chainArea; rw [if_neg hL]
/-- Pairing stage 1: the value of chain `42 - b` (staging chain block `b`) as staged at `WIT`. -/
theorem v6_chainval (L : Layer) (hL : L.val ≠ 0) (b : Nat) (hb : b < 43) (d : Nat) (hd : d = 0 ∨ d = 8) :
    v6M N w (WIT + (8136 + layOffV6 L + 64 * height L + (64 * b + 48 + d))) =
      BitVec.ofNat 64 (readLE (window (bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue (w.signature.layers L) (42 - b))) d 8)) := by
  have hcc := lower_cc L hL
  have hcs := ClaudeWCT.W9.Machine.Expand.chainSlotsV6_lower L hL
  have hlo : 8136 + layOffV6 L + 64 * (height L + chainCount L) ≤ 21832 ∧ layOffV6 L % 64 = 0 := by
    fin_cases L <;> decide
  have hh1 := ClaudeWCT.W9.Machine.Expand.OldW.height_pos' L
  rw [v6M_eq N w _ (by omega) (by omega),
    show 8136 + layOffV6 L + 64 * height L + (64 * b + 48 + d) =
      8136 + layOffV6 L + (64 * height L + (64 * b + 48 + d)) by omega,
    v6_layer N w L _ (by omega)]
  unfold layerRegionV6 layerBytesBCV6
  rw [if_neg hL, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length]; omega),
    ClaudeWCT.W9.Machine.Expand.bcTopBlockV6_length, window_drop,
    show 64 + (64 * height L + (64 * b + 48 + d) - 64) =
      (64 * height L + 64 * (chainCount L - 1 - (42 - b)) + 48) + d by rw [hcc]; omega,
    win8_of_16 _ _ _ (by omega),
    SigGolfCandidate.T3M.layerBytes_chain L _ _ ⟨42 - b, by omega⟩ 48 (by omega),
    window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
    window_full _ _ (bytesLE_length _ _)]
  unfold ClaudeWCT.W9.Machine.Expand.OldW.lsValue
  rw [dif_pos (by omega)]
/-- Pairing stage 1: an 8-byte word of a pair block of a lower chain area. -/
theorem lc_word {lay : Layer} (ls : LayerSignature lay) (m r : Nat) (hm : m < 21) (hr : r < 104) (h8 : r % 8 = 0) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes ls) (104 * m + r) 8 =
      if r = 16 ∨ r = 24 then window (bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls (2 * (20 - m) + 1))) (r - 16) 8
      else if r = 88 ∨ r = 96 then window (bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls (2 * (20 - m) + 2))) (r - 88) 8
      else zeros 8 := by
  unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes
  rw [List.append_assoc, window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.pairs_length]; omega),
    window_flatMap_const _ _ 104 (ClaudeWCT.W9.Machine.Expand.OldW.pairBytes_length ls) m (by simp; omega) r 8 (by omega)]
  have hidx : ((List.range 21).reverse)[m]'(by simp <;> omega) = 20 - m := by simp <;> omega
  rw [hidx]
  unfold ClaudeWCT.W9.Machine.Expand.OldW.pairBytes
  by_cases h1 : r < 16
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega), window_zeros _ _ _ (by omega),
      if_neg (by omega), if_neg (by omega)]
  by_cases h2 : r < 32
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 16).length = 16 by simp [zeros],
      if_pos (by omega)]
  by_cases h3 : r < 88
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      show (zeros 16 ++ bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls (2 * (20 - m) + 1))).length = 32 by
        simp [zeros, bytesLE_length],
      window_zeros _ _ _ (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [window_append_right _ _ _ _ (by simp [zeros, bytesLE_length]; omega),
      show (zeros 16 ++ bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls (2 * (20 - m) + 1)) ++ zeros 56).length = 88 by
        simp [zeros, bytesLE_length],
      if_neg (by omega), if_pos (by omega)]
/-- Pairing stage 1: an 8-byte word of chain 0's block at the end of a lower chain area. -/
theorem lc_tail {lay : Layer} (ls : LayerSignature lay) (q : Nat) (h1 : 2184 ≤ q) (h2 : q + 8 ≤ 2248) (h8 : q % 8 = 0) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes ls) q 8 =
      if 2232 ≤ q then window (bytesLE 16 (ClaudeWCT.W9.Machine.Expand.OldW.lsValue ls 0)) (q - 2232) 8 else zeros 8 := by
  unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes
  rw [List.append_assoc, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.pairs_length]; omega),
    ClaudeWCT.W9.Machine.Expand.OldW.pairs_length]
  by_cases h : 2232 ≤ q
  · rw [if_pos h, window_append_right _ _ _ _ (by simp [zeros]; omega), show (zeros 48).length = 48 by simp [zeros],
      show q - 2184 - 48 = q - 2232 by omega]
  · rw [if_neg h, window_append_left _ _ _ _ (by simp [zeros]; omega), window_zeros _ _ _ (by omega)]
/-- Pairing stage 1: the pair copy + zero fill rebuilds the witness's lower chain area. -/
theorem chOut_eq (L : Layer) (hL : L.val ≠ 0) (q : Nat) (hq : q + 8 ≤ 2248) (h8 : q % 8 = 0) :
    chOut (v6M N w) L.val q =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.lowerChainBytes (w.signature.layers L)) q 8)) := by
  obtain ⟨_, _, _, e4⟩ := lvDst_eq L hL
  have hS : ∀ s, chSrc L.val - SNAP2 + WIT + s = WIT + (8136 + layOffV6 L + 64 * height L + s) := by
    intro s; omega
  unfold chOut
  by_cases hlo : q < 2184
  · obtain ⟨m, r, hm, hr, rfl⟩ : ∃ m r, m < 21 ∧ r < 104 ∧ q = 104 * m + r :=
      ⟨q / 104, q % 104, by omega, Nat.mod_lt _ (by norm_num), by omega⟩
    have hr8 : r % 8 = 0 := by omega
    rw [lc_word _ m r hm hr hr8, show (104 * m + r) / 104 = m by omega, show (104 * m + r) % 104 = r by omega]
    unfold PairCopy.isVal PairCopy.srcOff
    by_cases hv : r = 16 ∨ r = 24 ∨ r = 88 ∨ r = 96
    · rw [if_pos ⟨hlo, hv⟩, hS]
      rcases hv with rfl | rfl | rfl | rfl
      · rw [if_pos rfl, if_pos (Or.inl rfl), show 128 * m + 112 = 64 * (2 * m + 1) + 48 + 0 by omega,
          v6_chainval N w L hL _ (by omega) 0 (Or.inl rfl), show 42 - (2 * m + 1) = 2 * (20 - m) + 1 by omega]
      · rw [if_neg (by omega), if_pos rfl, if_pos (Or.inr rfl), show 128 * m + 120 = 64 * (2 * m + 1) + 48 + 8 by omega,
          v6_chainval N w L hL _ (by omega) 8 (Or.inr rfl), show 42 - (2 * m + 1) = 2 * (20 - m) + 1 by omega]
      · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos (Or.inl rfl),
          show 128 * m + 48 = 64 * (2 * m) + 48 + 0 by omega,
          v6_chainval N w L hL _ (by omega) 0 (Or.inl rfl), show 42 - 2 * m = 2 * (20 - m) + 2 by omega]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (Or.inr rfl),
          show 128 * m + 56 = 64 * (2 * m) + 48 + 8 by omega,
          v6_chainval N w L hL _ (by omega) 8 (Or.inr rfl), show 42 - 2 * m = 2 * (20 - m) + 2 by omega]
    · rw [if_neg (fun h => hv h.2), if_neg (by omega), if_neg (by omega), if_neg (by omega), ofNat_readLE_zeros8]
  · rw [if_neg (fun h => hlo h.1), lc_tail _ q (by omega) hq h8]
    by_cases ht : 2232 ≤ q
    · rw [if_pos (by omega), if_pos ht, hS,
        show 2688 + (q - 2184) = 64 * 42 + 48 + (q - 2232) by omega,
        v6_chainval N w L hL 42 (by omega) _ (by omega)]
    · rw [if_neg (by omega), if_neg ht, ofNat_readLE_zeros8]
end chainarea
section ident3
variable (N : HashOutput) (w : WCT9.Witness)
/-- Pairing stage 1: a word of a lower layer region of the final witness after the second pass. -/
theorem zone_low (L : Layer) (hL : L.val ≠ 0) (o : Nat) (h1 : ClaudeWCT.W9.Machine.Expand.OldW.layerBase L ≤ o)
    (h2 : o + 8 ≤ ClaudeWCT.W9.Machine.Expand.OldW.layerBase L + (16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L + 2248))
    (h8 : o % 8 = 0) :
    BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8)) =
      if o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L < 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L then
        pathOut (v6M N w) L.val (lroute L.val (WCT9.digestIndex N)) (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L)
      else chOut (v6M N w) L.val (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L - 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L) := by
  have hW : WIT = 0x800 := rfl
  set leaf := (route (WCT9.digestIndex N) L).1 with hleafdef
  have hleaf : leaf < 2 ^ height L := ClaudeWCT.W9.Machine.Expand.OldW.route_leaf_lt _ _
  have hps : 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L ≤ 16 * 25 ∧ ClaudeWCT.W9.Machine.Expand.OldW.layerBase L % 8 = 0 ∧
      ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L ≥ 20 := by
    fin_cases L <;> simp_all [ClaudeWCT.W9.Machine.Expand.OldW.pathSlots, ClaudeWCT.W9.Machine.Expand.OldW.layerBase]
  have hlo : 8136 + layOffV6 L + 64 * (height L + chainCount L) ≤ 21832 ∧ layOffV6 L % 64 = 0 := by
    fin_cases L <;> decide
  have hcs := ClaudeWCT.W9.Machine.Expand.chainSlotsV6_lower L hL
  have hh1 := ClaudeWCT.W9.Machine.Expand.OldW.height_pos' L
  have harea := lower_area L hL
  rw [show o = ClaudeWCT.W9.Machine.Expand.OldW.layerBase L + (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L) by omega,
    ClaudeWCT.W9.Machine.Expand.OldW.win_layerRegion N w L _ 8 (by omega), Nat.add_sub_cancel_left]
  unfold layerRegion
  rw [if_neg hL]
  by_cases hp : o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L < 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L
  · rw [if_pos hp, window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.lowerPathBytes_length]; omega)]
    unfold pathOut
    have hro := rootOff_eq_hi L hL (WCT9.digestIndex N)
    rw [← hleafdef] at hro
    by_cases hrt : o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L = rootOff L.val (lroute L.val (WCT9.digestIndex N))
    · rw [if_pos hrt, hrt, hro, ClaudeWCT.W9.Machine.Expand.OldW.lowerPath_hi hL hleaf]
      decide
    rw [if_neg hrt]
    rw [lroute_eq L hL, ← hleafdef]
    cases h : (List.range (lvH L.val)).find? (fun j => decide (lvHit L.val leaf j (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L)))
      with
    | none =>
      simp only
      rw [v7_free hL hleaf _ _ _ (by omega) (by omega) (fun j => by
        have := List.find?_eq_none.mp h j.val (List.mem_range.mpr (by rw [lvH_eq L hL]; exact j.isLt))
        have h' : ¬ lvHit L.val leaf j.val (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L) := fun hh => this (decide_eq_true hh)
        unfold lvHit sibS padS at h'
        rw [plan_eq] at h'
        unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot
        rw [sibOff_eq _ (Nat.mod_lt _ (by norm_num))]
        omega) (fun hh => hrt (by rw [hh, ← hro, lroute_eq L hL]))]
      simp [zeros]; rfl
    | some j =>
      simp only
      obtain ⟨hj, hp'⟩ := lvs_find_some h
      rw [lvH_eq L hL] at hj
      have hh : lvHit L.val leaf j (o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L) := of_decide_eq_true hp'
      unfold lvHit sibS padS at hh
      rw [plan_eq] at hh
      set pj := (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan L leaf).getD j 0 with hpj
      have hb : leaf / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hsb := sibOff_eq (leaf / 2 ^ j % 2) hb
      have hpbnd := ClaudeWCT.W9.Machine.Expand.OldW.lower_pad_bound L hL leaf hleaf j hj
      have hsbnd := ClaudeWCT.W9.Machine.Expand.OldW.lower_sib_bound L hL leaf hleaf j hj
      unfold ClaudeWCT.W9.Machine.Expand.OldW.lowerSibSlot at hsbnd
      rw [sibOff_eq _ hb, ← hpj] at hsbnd
      rw [← hpj] at hpbnd
      set d := o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L - 16 * pj with hd
      have hdv : d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ (⟨j, hj⟩ : Fin (height L)).val % 2) ∨
          d = SigGolfCandidate.T3M.sibOff (leaf / 2 ^ (⟨j, hj⟩ : Fin (height L)).val % 2) + 8 ∨ d = 32 ∨ d = 40 := by
        simp only; rw [hsb]; omega
      have e7 := v7_block hL hleaf (w.signature.layers L) (w.counters (Fin.ofNat 4 (L.val - 1))) ⟨j, hj⟩ d
        (by omega) hdv
      have e6 := v6_block (leaf := leaf) (w.signature.layers L) (w.counters (Fin.ofNat 4 (L.val - 1))) ⟨j, hj⟩ d
        (by omega) (by omega) hdv
      simp only at e7 e6
      rw [plan_eq, ← hpj, show o - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L = 16 * pj + d by omega, e7,
        show 16 * pj + d - 16 * pj = d by omega,
        show lvSrc L.val j - SNAP2 + WIT + d = WIT + (8136 + layOffV6 L + (64 * (height L - 1 - j) + d)) by
          rw [lvSrc_eq L hL j hj]; omega,
        v6M_eq N w _ (by omega) (by omega)]
      rw [show 8136 + layOffV6 L + (64 * (height L - 1 - j) + d) = 8136 + layOffV6 L + (64 * (height L - 1 - j) + d)
        from rfl, v6_layer N w L _ (by omega)]
      unfold layerRegionV6
      rw [if_neg hL, e6]
  · rw [if_neg hp, window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.lowerPathBytes_length]; omega),
      ClaudeWCT.W9.Machine.Expand.OldW.lowerPathBytes_length, chOut_eq N w L hL _ (by omega) (by omega)]
end ident3
/-- Pairing stage 1: final witness words of the layer regions above the top path area (`[8864, 20104)`) are the
second pass's output (`out2old` at staging offset `8 i + 856`). -/
theorem compact2_words (N : HashOutput) (w : WCT9.Witness) (i : Nat) (h1 : 8864 ≤ 8 * i) (h2 : 8 * i < 20104) :
    BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (8 * i) 8)) =
      out2old (v6M N w) (WCT9.digestIndex N) (8 * i + 856) := by
  unfold out2old
  rw [if_neg (show ¬ 8 * i + 856 < 8952 by omega)]
  by_cases htop : 8 * i + 856 < 13176
  · rw [if_pos htop]
    have h66 : height (0 : Layer) + ClaudeWCT.W9.Machine.Expand.chainSlotsV6 0 = 66 := rfl
    have hw7 := ClaudeWCT.W9.Machine.Expand.OldW.win_layerRegion N w 0 (8 * i - 8096) 8
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.pathSlots, ClaudeWCT.W9.Machine.Expand.OldW.chainArea]; omega)
    have hw6 := v6_layer N w 0 (8 * i - 8096) (by rw [h66]; omega)
    rw [show ClaudeWCT.W9.Machine.Expand.OldW.layerBase 0 + (8 * i - 8096) = 8 * i by
      simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase]; omega] at hw7
    rw [hw7, layerRegion_top_tail N w _ (by omega),
      show WIT + (8 * i + 856 - 816) = WIT + (8136 + layOffV6 0 + (8 * i - 8096)) by simp [layOffV6]; omega,
      v6M_eq N w _ (by simp [layOffV6]; omega) (by simp [layOffV6]; omega), hw6]
  rw [if_neg htop, if_pos (show 8 * i + 856 < 20960 by omega)]
  have hW : WIT = 0x800 := rfl
  have key : ∀ L : Layer, L.val ≠ 0 → zoneLay (8 * i + 856) = L.val →
      ClaudeWCT.W9.Machine.Expand.OldW.layerBase L ≤ 8 * i →
      8 * i + 8 ≤ ClaudeWCT.W9.Machine.Expand.OldW.layerBase L +
        (16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L + 2248) →
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (8 * i) 8)) =
        (if 8 * i + 856 - (lvDst (zoneLay (8 * i + 856)) - WIT) < pathTop (zoneLay (8 * i + 856)) then
          pathOut (v6M N w) (zoneLay (8 * i + 856)) (lroute (zoneLay (8 * i + 856)) (WCT9.digestIndex N))
            (8 * i + 856 - (lvDst (zoneLay (8 * i + 856)) - WIT))
        else chOut (v6M N w) (zoneLay (8 * i + 856)) (8 * i + 856 - (chDst (zoneLay (8 * i + 856)) - WIT))) := by
    intro L hL hz h1 h2
    obtain ⟨e1, e2, e3, e4⟩ := lvDst_eq L hL
    rw [hz, e1, e2, e3, zone_low N w L hL (8 * i) h1 h2 (by omega),
      show 8 * i + 856 - (ClaudeWCT.W9.Machine.Expand.OldW.layerBase L + 856) =
        8 * i - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L by omega,
      show 8 * i + 856 - (ClaudeWCT.W9.Machine.Expand.OldW.layerBase L + 856 +
        16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L) =
        8 * i - ClaudeWCT.W9.Machine.Expand.OldW.layerBase L - 16 * ClaudeWCT.W9.Machine.Expand.OldW.pathSlots L by
        omega]
  by_cases hz1 : 8 * i + 856 < 15824
  · exact key 1 (by decide) (by unfold zoneLay; rw [if_pos hz1]; rfl)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase]; omega)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase, ClaudeWCT.W9.Machine.Expand.OldW.pathSlots]; omega)
  · by_cases hz2 : 8 * i + 856 < 18392
    · exact key 2 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_pos hz2]; rfl)
        (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase]; omega)
        (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase, ClaudeWCT.W9.Machine.Expand.OldW.pathSlots]; omega)
    · exact key 3 (by decide) (by unfold zoneLay; rw [if_neg hz1, if_neg hz2]; rfl)
        (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase]; omega)
        (by simp [ClaudeWCT.W9.Machine.Expand.OldW.layerBase, ClaudeWCT.W9.Machine.Expand.OldW.pathSlots]; omega)

/-- C4: the second pass leaves the top path area in the old 64-byte stride layout (`layerRegionV6 N w 0`); the
post-pass re-places it. -/
theorem compact2_top_old (N : HashOutput) (w : WCT9.Witness) (i : Nat) (h1 : 8096 ≤ 8 * i) (h2 : 8 * i < 8864) :
    out2old (v6M N w) (WCT9.digestIndex N) (8 * i + 856) =
      BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * i - 8096) 8)) := by
  have h66 : height (0 : Layer) + ClaudeWCT.W9.Machine.Expand.chainSlotsV6 0 = 66 := rfl
  have hw6 := v6_layer N w 0 (8 * i - 8096) (by rw [h66]; omega)
  unfold out2old
  rw [if_neg (by omega), if_pos (by omega),
    show WIT + (8 * i + 856 - 816) = WIT + (8136 + layOffV6 0 + (8 * i - 8096)) by simp [layOffV6, WIT]; omega,
    v6M_eq N w _ (by simp [layOffV6]; omega) (by simp [layOffV6]; omega), hw6]
/-- Pairing stage 1: the staged rho / digest counter (second-pass offsets 20960 .. 20984) are the witness tail. -/
theorem tail_words (N : HashOutput) (w : WCT9.Witness) (t : Nat) (ht : t < 4) :
    out2old (v6M N w) (WCT9.digestIndex N) (20960 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (23208 + 8 * t) 8)) := by
  rw [ClaudeWCT.W9.Machine.Expand.OldW.win_tail N w _ _ (by omega)]
  have hrho : ∀ d, d + 8 ≤ 16 → window (tailBytes w) d 8 = window (witListV6 N w) d 8 := fun d hd => by
    rw [v6_head N w _ (by omega)]
    unfold tailBytes headerBytesV5
    simp only [List.append_assoc]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]; omega),
      window_append_left _ _ _ _ (by simp [bytesLE_length]; omega)]
  unfold out2old
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [if_pos (by norm_num), show 8 * 0 = 0 from rfl, hrho 0 (by omega), ← v6M_eq N w 0 (by omega) (by omega),
      Nat.add_zero]
  · rw [if_neg (by norm_num), if_pos (by norm_num), show 8 * 1 = 8 from rfl, hrho 8 (by omega),
      ← v6M_eq N w 8 (by omega) (by omega)]
  · rw [if_neg (by norm_num), if_neg (by norm_num), if_pos (by norm_num), show 8 * 2 = 16 from rfl]
    unfold tailBytes
    simp only [List.append_assoc]
    rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
      show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
      window_append_left _ _ _ _ (by simp [zeros]), window_zeros _ _ _ (by omega), ofNat_readLE_zeros8]
  · rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), show 8 * 3 = 24 from rfl,
      ClaudeWCT.W9.Machine.Expand.OldW.tail_counter_window, v6M_eq N w 16 (by omega) (by omega), v6_head N w _ (by omega)]
    have hh : window (headerBytesV5 w) 16 8 = bytesLE 4 w.digestCounter ++ zeros 4 := by
      unfold headerBytesV5
      rw [show bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3) ++
        zeros 28 = bytesLE 16 w.signature.rho ++ (bytesLE 4 w.digestCounter ++ zeros 4 ++ (zeros 8 ++
          bytesLE 4 (w.counters 3) ++ zeros 28)) by simp [zeros, List.append_assoc, List.replicate_add]]
      rw [window_append_right _ _ _ _ (by simp [bytesLE_length]),
        show 16 - (bytesLE 16 w.signature.rho).length = 0 by simp [bytesLE_length],
        window_append_left _ _ _ _ (by simp [bytesLE_length, zeros]), window_full _ _ (by simp [bytesLE_length, zeros])]
    rw [hh, wu_small _ (by
      rw [SigGolfCandidate.T3M.readLE_append, bytesLE_length]
      rw [SigGolfCandidate.T3M.readLE_bytesLE]
      have := w.digestCounter.isLt
      have hz : readLE (zeros 4) = 0 := by decide
      rw [hz]; omega)]
/-! ### Pairing stage 1: the leaf buffers written by the layout block -/
def layOf (k : Nat) : Layer := Fin.ofNat 4 (3 - Layout.grpK k)
def iK (k : Nat) : Nat := k - 43 * Layout.grpK k
def kOf (lay : Layer) (i : Nat) : Nat := 43 * (3 - lay.val) + i
theorem buf_table : ∀ k < 180, iK k < chainCount (layOf k) ∧
    Layout.slotK k = 2904 + ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot (layOf k) (iK k) ∧
    Layout.sK k = 2904 + ClaudeWCT.W9.Machine.Expand.OldW.chainBlock (layOf k) (iK k) + ClaudeWCT.W9.Machine.Expand.OldW.valueOff (layOf k) (iK k) ∧
    11768 ≤ Layout.sK k ∧ Layout.sK k + 16 ≤ 23008 ∧ Layout.slotK k % 8 = 0 := by
  decide +kernel

theorem buf_table2 : ∀ lay : Layer, ∀ i < chainCount lay, kOf lay i < 180 ∧
    Layout.slotK (kOf lay i) = 2904 + ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i := by
  decide +kernel
theorem hitVal_hit (M : Nat → Word) (k : Nat) (hk : k < 180) (A : Nat)
    (h : Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16) :
    Layout.hitVal M 180 A = M (Layout.sK k + (A - Layout.slotK k)) := by
  have key : ∀ j, k < j → j ≤ 180 → Layout.hitVal M j A = M (Layout.sK k + (A - Layout.slotK k)) := by
    intro j
    induction j with
    | zero => intro h1; omega
    | succ j ih =>
      intro h1 h2
      rw [Layout.hitVal_succ M j A (by omega)]
      by_cases hjk : j = k
      · subst hjk; rw [if_pos h]
      · have := Layout.slot_mono k j (by omega) (by omega)
        rw [if_neg (by omega)]
        exact ih (by omega) (by omega)
  exact key 180 hk le_rfl
theorem hitVal_miss (M : Nat → Word) (A : Nat)
    (h : ∀ k < 180, ¬ (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) : Layout.hitVal M 180 A = 0 := by
  have hn : (List.range 180).find? (fun k => decide (Layout.slotK k ≤ A ∧ A < Layout.slotK k + 16)) = none := by
    rw [List.find?_eq_none]; intro k hk; simpa using h k (List.mem_range.mp hk)
  unfold Layout.hitVal; rw [hn]
theorem bufferMem_low (M : Nat → Word) (A : Nat) (hA : A < 23008) (h1 : A ≠ 1240) : Buffer.bufferMem M A = M A := by
  unfold Buffer.bufferMem Layout.lbMem Layout.itMem
  rw [if_neg h1, if_neg (by omega), if_neg (by omega)]
section buffers
variable (N : HashOutput) (w : WCT9.Witness)
theorem win_value (lay : Layer) (i : Nat) (hi : i < chainCount lay) (d : Nat) (hd : d + 8 ≤ 16) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (ClaudeWCT.W9.Machine.Expand.OldW.chainBlock lay i + ClaudeWCT.W9.Machine.Expand.OldW.valueOff lay i + d) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values ⟨i, hi⟩)) d 8 := by
  have hv : ClaudeWCT.W9.Machine.Expand.OldW.lsValue (w.signature.layers lay) i = (w.signature.layers lay).values ⟨i, hi⟩ := by
    simp [ClaudeWCT.W9.Machine.Expand.OldW.lsValue, hi]
  rw [← window_window' _ _ 16 d 8 hd,
    ClaudeWCT.W9.Machine.Expand.OldW.win_chain N w lay ⟨i, hi⟩ _ (by unfold ClaudeWCT.W9.Machine.Expand.OldW.valueOff; split <;> omega)]
  unfold ClaudeWCT.W9.Machine.Expand.OldW.chainCell ClaudeWCT.W9.Machine.Expand.OldW.valueOff
  by_cases hG : ClaudeWCT.W9.Machine.Expand.OldW.isG lay i = true
  · simp only [hG, if_true]
    rw [window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _), hv]
  · simp only [hG, if_false, Bool.false_eq_true]
    rw [window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
      window_full _ _ (bytesLE_length _ _), hv]
theorem win_slot (lay : Layer) (i : Nat) (hi : i < chainCount lay) (d : Nat) (hd : d + 8 ≤ 16) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i + d) 8 =
      window (bytesLE 16 ((w.signature.layers lay).values ⟨i, hi⟩)) d 8 := by
  have hb := ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot_bounds lay i hi
  rw [← window_window' _ _ 16 d 8 hd, ClaudeWCT.W9.Machine.Expand.OldW.witList_split, window_append_right _ _ _ _ (by
    simp only [List.length_append, ClaudeWCT.W9.Machine.Expand.OldW.headerBytes_length, ClaudeWCT.W9.Machine.Expand.OldW.wctBytes_length,
      ClaudeWCT.W9.Machine.Expand.OldW.layers_length]
    omega)]
  simp only [List.length_append, ClaudeWCT.W9.Machine.Expand.OldW.headerBytes_length, ClaudeWCT.W9.Machine.Expand.OldW.wctBytes_length,
    ClaudeWCT.W9.Machine.Expand.OldW.layers_length]
  rw [window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.Machine.Expand.OldW.leafBuffersBytes_length]; omega),
    show 80 + 8016 + 12008 = 20104 by decide,
    ClaudeWCT.W9.Machine.Expand.OldW.win_leafBuffersBytes w.signature lay ⟨i, hi⟩]
theorem lb_zero (sig : WCT9.Signature) (lay : Layer) (off : Nat) (h8 : off % 8 = 0)
    (hlen : off + 8 ≤ ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen lay)
    (hz : ∀ i < chainCount lay, ¬ (ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i - ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay ≤ off ∧
      off < ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i - ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay + 16)) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBytes sig lay) off 8 = zeros 8 := by
  unfold ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot at hz
  simp only [Nat.add_sub_cancel_left] at hz
  unfold ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBytes
  have hE := ClaudeWCT.W9.Machine.Expand.OldW.endpointBytes_length sig lay
  have hc : 2 ≤ chainCount lay ∧ 16 * chainCount lay + 16 + (if lay = 0 then 80 else if lay.val = 1 then 16 else 32) =
      ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen lay := by
    fin_cases lay <;> decide
  generalize (if lay = 0 then 80 else if lay.val = 1 then 16 else 32) = Z at hc ⊢
  have htl : ((ClaudeWCT.W9.Machine.Expand.OldW.endpointBytes sig lay).take 16).length = 16 := by
    rw [List.length_take, hE]; omega
  have hdl : ((ClaudeWCT.W9.Machine.Expand.OldW.endpointBytes sig lay).drop 16).length = 16 * chainCount lay - 16 := by
    rw [List.length_drop, hE]
  by_cases h0 : off < 16
  · exfalso; have h := hz 0 (by omega); simp only [if_pos rfl, ↓reduceIte] at h; omega
  by_cases h1 : off < 32
  · rw [window_append_left _ _ _ _ (by simp [zeros, htl, hdl]; omega),
      window_append_left _ _ _ _ (by simp [zeros, htl]; omega),
      window_append_right _ _ _ _ (by rw [htl]; omega), htl, window_zeros _ _ _ (by simp [zeros]; omega)]
  by_cases h2 : 16 * chainCount lay + 16 ≤ off
  · rw [window_append_right _ _ _ _ (by simp [zeros, htl, hdl]; omega), window_zeros _ _ _ (by
      simp only [List.length_append, htl, hdl, zeros, List.length_replicate]; omega)]
  exfalso; have h := hz ((off - 16) / 16) (by omega); rw [if_neg (by omega)] at h; omega

theorem buf_zero (o : Nat) (h1 : 20104 ≤ o) (h2 : o < 23208) (h8 : o % 8 = 0)
    (hz : ∀ lay : Layer, ∀ i < chainCount lay,
      ¬ (ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i ≤ o ∧ o < ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i + 16)) :
    window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8 = zeros 8 := by
  have go : ∀ lay : Layer, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay ≤ o →
      o + 8 ≤ ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay + ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen lay →
      window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8 = zeros 8 := by
    intro lay hb he
    have hs : ∀ i, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay ≤ ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot lay i := by
      intro i; unfold ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot; omega
    rw [show o = ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay + (o - ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase lay) by omega,
      ClaudeWCT.W9.Machine.Expand.OldW.win_leafBuffer N w lay _ 8 (by omega)]
    apply lb_zero _ lay _ (by fin_cases lay <;> simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase] at hb ⊢ <;> omega) (by omega)
    intro i hi h
    have := hs i
    exact hz lay i hi ⟨by omega, by omega⟩
  by_cases a3 : o < 20840
  · exact go 3 (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase]; omega) (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen]; omega)
  by_cases a2 : o < 21576
  · exact go 2 (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen]; omega)
  by_cases a1 : o < 22296
  · exact go 1 (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen]; omega)
  · exact go 0 (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase]; omega)
      (by simp [ClaudeWCT.W9.Machine.Expand.OldW.leafBufferBase, ClaudeWCT.W9.Machine.Expand.OldW.leafBufferLen]; omega)
/-- Pairing stage 1: the leaf buffers and the tail after the layout block. -/
theorem buffer_words (M : Nat → Word)
    (hM : ∀ o, 8864 ≤ o → o < 20104 → o % 8 = 0 →
      M (2904 + o) = BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8)))
    (hT : ∀ t < 4, M (23008 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (23208 + 8 * t) 8)))
    (i : Nat) (h1 : 20104 ≤ 8 * i) (h2 : 8 * i < 23240) :
    Buffer.bufferMem M (2904 + 8 * i) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (8 * i) 8)) := by
  unfold Buffer.bufferMem Layout.lbMem Layout.itMem
  rw [if_neg (by omega)]
  by_cases ht : 23208 ≤ 8 * i
  · rw [if_pos (by omega), show 2904 + 8 * i - 3104 = 23008 + 8 * ((8 * i - 23208) / 8) by omega,
      hT _ (by omega), show 23208 + 8 * ((8 * i - 23208) / 8) = 8 * i by omega]
  rw [if_neg (by omega), if_pos (by omega)]
  by_cases hs : ∃ k, k < 180 ∧ Layout.slotK k ≤ 2904 + 8 * i ∧ 2904 + 8 * i < Layout.slotK k + 16
  · obtain ⟨k, hk, ha, hb⟩ := hs
    obtain ⟨hi, hsl, hsk, hk1, hk2, hk8⟩ := buf_table k hk
    rw [hitVal_hit M k hk _ ⟨ha, hb⟩]
    set d := 2904 + 8 * i - Layout.slotK k with hd
    have hd8 : d = 0 ∨ d = 8 := by omega
    rw [show Layout.sK k + d = 2904 + (ClaudeWCT.W9.Machine.Expand.OldW.chainBlock (layOf k) (iK k) +
        ClaudeWCT.W9.Machine.Expand.OldW.valueOff (layOf k) (iK k) + d) by omega,
      hM _ (by omega) (by omega) (by
        have := (Layout.tab_facts.2.2.2.2.2.2.2.2 k hk).1
        omega),
      win_value N w _ _ hi d (by omega),
      show 8 * i = ClaudeWCT.W9.Machine.Expand.OldW.leafBufferSlot (layOf k) (iK k) + d by omega,
      win_slot N w _ _ hi d (by omega)]
  · have hn : ∀ k < 180, ¬ (Layout.slotK k ≤ 2904 + 8 * i ∧ 2904 + 8 * i < Layout.slotK k + 16) :=
      fun k hk h => hs ⟨k, hk, h⟩
    rw [hitVal_miss M _ hn, buf_zero N w (8 * i) h1 (by omega) (by omega) (fun lay j hj h => by
      obtain ⟨hk, he⟩ := buf_table2 lay j hj
      exact hn _ hk ⟨by omega, by omega⟩), ofNat_readLE_zeros8]
end buffers

section topPost
variable (N : HashOutput) (w : WCT9.Witness)
end topPost
/-! ### C4: the top path area after the post-pass -/
open SigGolfCandidate.T3 (route height LayerSignature)
open SigGolfCandidate.T3M (layerBytes layerBytes_merkle window_append_left window_append_right window_full)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Expand (layerRegionV6)
/-- The post-pass's table slot is the witness's sibling slot (`topSibSlot`). -/
theorem ppSlot_eq_sib (leaf : Nat) (hl : leaf < 4096) (j : Nat) (hj : j < 12) :
    16 * Buffer.Post.ppSlot leaf j = ClaudeWCT.W9.Machine.Expand.OldW.topSibSlot leaf j := by
  have hs : ∀ b, b < 2 → SigGolfCandidate.T3M.sibOff b = 48 * (1 - b) := fun b hb => by
    unfold SigGolfCandidate.T3M.sibOff; split <;> omega
  unfold Buffer.Post.ppSlot
  by_cases h6 : j < 6
  · rw [if_pos h6, ClaudeWCT.W9.Machine.Expand.OldW.topSibSlot_lo h6]
    unfold slotA ClaudeWCT.W9.Machine.Expand.OldW.topSibA ClaudeWCT.W9.Machine.Expand.OldW.topSlotA
    rw [hs _ (Nat.mod_lt _ (by norm_num))]; ring
  · rw [if_neg h6, ClaudeWCT.W9.Machine.Expand.OldW.topSibSlot_hi (by omega) hj, Nat.mod_eq_of_lt (show leaf / 64 < 64 by omega)]
    unfold slotB ClaudeWCT.W9.Machine.Expand.OldW.topSibB ClaudeWCT.W9.Machine.Expand.OldW.topSlotB
    rw [hs _ (Nat.mod_lt _ (by norm_num))]; ring
/-- The old (pre-C4) top layout holds sibling `j` at `64 (11 - j) + sibOff`. -/
theorem oldTop_sib (leaf : Nat) (ls : LayerSignature 0) (j : Nat) (hj : j < height (0 : Layer)) (d : Nat)
    (hd : d = 0 ∨ d = 8) :
    window (layerBytes 0 leaf ls) (Buffer.Post.ppOld leaf j - 11000 + d) 8 = window (bytesLE 16 (ls.path ⟨j, hj⟩)) d 8 := by
  have hb : leaf / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h12 : j < 12 := lt_of_lt_of_eq hj ClaudeWCT.W9.Machine.Expand.OldW.height_top
  have hm := layerBytes_merkle 0 leaf ls ⟨j, hj⟩ (48 * (1 - leaf / 2 ^ j % 2)) (by omega)
  simp only [Fin.val_mk] at hm
  have hin : window (if leaf / 2 ^ j % 2 = 1 then bytesLE 16 (ls.path ⟨j, hj⟩) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (ls.path ⟨j, hj⟩)) (48 * (1 - leaf / 2 ^ j % 2)) 16 = bytesLE 16 (ls.path ⟨j, hj⟩) := by
    rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ j) with h | h
    · rw [h, if_neg (by decide), show 48 * (1 - 0) = (zeros 48).length by simp [zeros],
        window_append_right _ _ _ _ le_rfl, Nat.sub_self, window_full _ _ (bytesLE_length _ _)]
    · rw [h, if_pos rfl, show 48 * (1 - 1) = 0 from rfl, window_append_left _ _ _ _ (by rw [bytesLE_length]),
        window_full _ _ (bytesLE_length _ _)]
  rw [show Buffer.Post.ppOld leaf j - 11000 + d = 64 * (height (0 : Layer) - 1 - j) + 48 * (1 - leaf / 2 ^ j % 2) + d by
      unfold Buffer.Post.ppOld Buffer.Post.ppBit; rw [ClaudeWCT.W9.Machine.Expand.OldW.height_top]; omega,
    ← window_window' _ _ 16 d 8 (by omega), hm, hin]
/-- The top path area after the post-pass is the witness's plan-placed area. -/
theorem postMem_top (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hold : ∀ q < 96, M (11000 + 8 * q) = BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * q) 8)))
    (q : Nat) (hq : q < 96) :
    Buffer.Post.ppPlace (Buffer.bufferMem M) (route (WCT9.digestIndex N) 0).1 12 (11000 + 8 * q) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (8096 + 8 * q) 8)) := by
  have hw := ClaudeWCT.W9.Machine.Expand.OldW.win_topPath N w (8 * q) 8 (by omega)
  rw [show ClaudeWCT.W9.Machine.Expand.OldW.layerBase 0 = 8096 from rfl] at hw
  rw [hw]
  have hl6 : ∀ q < 96, window (layerRegionV6 N w 0) (8 * q) 8 =
      window (layerBytes 0 (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) (8 * q) 8 := by
    intro q hq
    have h63 : 64 * (height (0 : Layer) + chainCount (0 : Layer)) = 4032 := rfl
    unfold layerRegionV6 ClaudeWCT.W9.Machine.Expand.layerBytesV6
    rw [if_pos (show (0 : Layer).val = 0 from rfl), if_pos (show (0 : Layer).val = 0 from rfl), List.append_assoc,
      window_append_left _ _ _ _ (by rw [List.length_take, layerBytes_length, h63]; omega),
      window_take _ _ _ _ (by omega)]
  replace hold : ∀ q < 96, M (11000 + 8 * q) = BitVec.ofNat 64 (readLE (window
      (layerBytes 0 (route (WCT9.digestIndex N) 0).1 (w.signature.layers 0)) (8 * q) 8)) :=
    fun q hq => (hold q hq).trans (by rw [hl6 q hq])
  have hl : (route (WCT9.digestIndex N) 0).1 < 4096 := by
    have h1 : (route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2 ^ 19 % 2 ^ 12 := rfl
    rw [h1]; exact Nat.mod_lt _ (by norm_num)
  generalize (route (WCT9.digestIndex N) 0).1 = leaf at hl hold ⊢
  generalize w.signature.layers 0 = ls at hold ⊢
  by_cases hs : ∃ j, j < 12 ∧ 16 * Buffer.Post.ppSlot leaf j ≤ 8 * q ∧ 8 * q < 16 * Buffer.Post.ppSlot leaf j + 16
  · obtain ⟨j, hj, h1, h2⟩ := hs
    have hj' : j < height (0 : Layer) := lt_of_lt_of_eq hj ClaudeWCT.W9.Machine.Expand.OldW.height_top.symm
    have he := ppSlot_eq_sib leaf hl j hj
    have hpo := Buffer.Post.ppOld_lt leaf j
    have hpb := Buffer.Post.ppBit_lt leaf j
    have hpo' : 11000 ≤ Buffer.Post.ppOld leaf j := by unfold Buffer.Post.ppOld; omega
    obtain ⟨D, hD8, hDq⟩ : ∃ D, (D = 0 ∨ D = 8) ∧ 8 * q = 16 * Buffer.Post.ppSlot leaf j + D :=
      ⟨8 * q - 16 * Buffer.Post.ppSlot leaf j, by omega, by omega⟩
    rw [hDq, show 11000 + (16 * Buffer.Post.ppSlot leaf j + D) = Buffer.Post.ppNew leaf j + D by
        unfold Buffer.Post.ppNew; omega,
      Buffer.Post.ppPlace_hit _ leaf hl j hj _ hD8,
      bufferMem_low _ _ (by omega) (by omega),
      show Buffer.Post.ppOld leaf j + D = 11000 + 8 * ((Buffer.Post.ppOld leaf j - 11000 + D) / 8) by omega,
      hold _ (by omega),
      show 8 * ((Buffer.Post.ppOld leaf j - 11000 + D) / 8) = Buffer.Post.ppOld leaf j - 11000 + D by omega,
      oldTop_sib leaf ls j hj' D hD8, he, ← window_window' _ _ 16 D 8 (by omega),
      ClaudeWCT.W9.Machine.Expand.OldW.topPath_sib leaf ls ⟨j, hj'⟩]
  · have hm : ∀ j < 12, ¬ (16 * Buffer.Post.ppSlot leaf j ≤ 8 * q ∧ 8 * q < 16 * Buffer.Post.ppSlot leaf j + 16) :=
      fun j hj h => hs ⟨j, hj, h⟩
    rw [Buffer.Post.ppPlace_miss _ leaf q hq hm,
      ClaudeWCT.W9.Machine.Expand.OldW.topPath_zero leaf ls (by omega) (fun j => by
        have hj : j.val < 12 := lt_of_lt_of_eq j.isLt ClaudeWCT.W9.Machine.Expand.OldW.height_top
        have := hm j.val hj
        rw [← ppSlot_eq_sib leaf hl j.val hj]
        omega)]
    decide

/-- Pairing stage 1: the final witness words `[8096, 23240)` after the buffer pass and the top post-pass. -/
theorem postMem_words (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hM : ∀ o, 8864 ≤ o → o < 20104 → o % 8 = 0 →
      M (2904 + o) = BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) o 8)))
    (hT : ∀ t < 4, M (23008 + 8 * t) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.Machine.Expand.OldW.witList N w) (23208 + 8 * t) 8)))
    (hold : ∀ q < 96, M (11000 + 8 * q) = BitVec.ofNat 64 (readLE (window (layerRegionV6 N w 0) (8 * q) 8)))
    (i : Nat) (h1 : 1012 ≤ i) (h2 : i < 2905) :
    Buffer.Post.ppPlace (Buffer.bufferMem M) (route (WCT9.digestIndex N) 0).1 12 (2904 + 8 * i) =
      (wordsOf (ClaudeWCT.W9.Machine.Expand.OldW.witList N w)).getD i 0 := by
  have hl : (route (WCT9.digestIndex N) 0).1 < 4096 := by
    have h1 : (route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2 ^ 19 % 2 ^ 12 := rfl
    rw [h1]; exact Nat.mod_lt _ (by norm_num)
  rw [wordsOf_getD' _ 2905 (ClaudeWCT.W9.Machine.Expand.OldW.witList_length_eq N w) i h2]
  by_cases htop : 8 * i < 8864
  · rw [show 2904 + 8 * i = 11000 + 8 * (i - 1012) by omega, postMem_top N w M hold (i - 1012) (by omega),
      show 8096 + 8 * (i - 1012) = 8 * i by omega]
  rw [Buffer.Post.ppPlace_out _ _ hl 12 le_rfl _ (by omega)]
  by_cases hb : 8 * i < 20104
  · rw [bufferMem_low _ _ (by omega) (by omega)]
    exact hM _ (by omega) hb (by omega)
  · exact buffer_words N w M hM hT i (by omega) (by omega)

end ClaudeWCT.W9.Machine.Expand.Compact2
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsRuns ====
section

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def runA (look : Nat → Option (BitVec 32)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux { noAlias := true } look (stops.map pcOf) 200 (pcOf n) dirs (σK []) []
def cE (n : Nat) : E := .c (BitVec.ofNat 64 n)
def ldc (a : Nat) : E := .ld (cE a)
def mwc (a : Nat) (e : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, e)
def regsOf (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def pres2 (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ecall : Bool) (k cyc : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ecall, k, cyc, brs, none⟩
def pres (regs : List (Reg × E)) (mem : SymMem) (obl : List Oblig) (pc : Nat) (ecall : Bool) (k : Nat)
    (brs : List Br) : PRes :=
  ⟨⟨regsOf regs, mem, obl⟩, pcOf pc, ecall, k, k, brs, none⟩
def qI (c i : Nat) : Nat := qIdx.getD (6 * c + i) 0
def chkI (c i s : Nat) : Nat := chkIdx.getD (30 * c + 5 * i + s) 0
def skipI (c i s : Nat) : Nat := skipIdx.getD (30 * c + 5 * i + s) 0
def leafI (c : Nat) : Nat := leafIdx.getD c 0
def lI (c : Nat) : Nat := lIdx.getD c 0
def tI (c : Nat) : Nat := tIdx.getD c 0
def nodeI (c : Nat) : Nat := nodeIdx.getD c 0
def ntI (c : Nat) : Nat := ntIdx.getD c 0
def rI (c : Nat) : Nat := rIdx.getD c 0
def lwuI (c : Nat) : Nat := lwuIdx.getD c 0
def pcI (c l : Nat) : Nat := rI c + 12 + 13 * l
def lcEnd (c i : Nat) : Nat := if i = 5 then lI c else qI c (i + 1)
def hdr8 (c : Nat) : Nat := 2049 + 65536 * c
def hdr6 (c : Nat) : Nat := 1537 + 65536 * c
/-- FTS chain word constant. C4 (FTS coordinate + 1, as b3cc11b's campaign S2): coordinate nibble `c + 1`. -/
def chainK (c i : Nat) : Nat := 0x80 + 4 * i + 65536 * (c + 1)
def nodeK (c : Nat) : Nat := 769 + 65536 * (4 + c)
def slotV (c i : Nat) : Nat := SIG + 16 + 208 * c + 16 * i
def slotP (c l : Nat) : Nat := SIG + 112 + 208 * c + 16 * l
def leafOff (i : Nat) : Nat := if i = 0 then 0 else 16 * (i + 2)
def forOff (c : Nat) : Nat := 32 + 32 * c
def w1E : E := .bin .or (.bin .sll (.reg .x18) (cE 32)) (.reg .x22)
def qE (c i : Nat) : E := .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (chainK c i))
def idx32E : E := .bin .sll (.reg .x22) (cE 32)
/-- FTS node word base. C4: coordinate nibble `c + 1`; coordinate 0 goes through the arena trampoline
`lui t2,16; or t1,t1,t2; ori t1,t1,1537`, which produces the same expression. -/
def nodeLoE (c : Nat) : E := .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (cE (65536 * (c + 1)))) (cE 1537)
/-- FTS leaf word. C4: coordinate nibble `c + 1`; for coordinate 0 the arena trampoline ORs `65536` and `1537`
separately. -/
def leafLoE (c : Nat) : E :=
  if c = 0 then
    .bin .or (.bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE 65536)) (cE 1537)
  else .bin .or (.bin .or (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (1537 + 65536 * (c + 1)))
def leafX7 (c : Nat) : E := if c = 0 then cE 65536 else cE (65536 * (c + 1) + 1537)
def x29A (off : Nat) : Addr := ⟨some (.reg .x29), BitVec.ofNat 64 off⟩
def nodeLo7 (c index : Nat) : Nat := 1537 + 65536 * (c + 1) + 2 ^ 27 * index
def leafLo7 (c index j : Nat) : Nat := 1537 + 65536 * (c + 1) + 2 ^ 20 * j + 2 ^ 27 * index
def dE (i : Nat) : E := .bin .sub (cE 4) (.bin .and (.bin .srl (.reg .x25) (cE (3 * i))) (cE 7))
def x18p1 : E := .bin .add (.reg .x18) (cE 1)
def x18m1 : E := .bin .add (.reg .x18) (cE (2 ^ 64 - 1))
def heapLeafE : E := .bin .sll (.bin .add (.reg .x18) (cE 128)) (cE 4)
def sh5 : E := .bin .sll (.reg .x18) (cE 5)
def sh4 : E := .bin .sll (.reg .x18) (cE 4)
def pathE (l : Nat) : E := .bin .sll (.bin .xor (.bin .srl (.bin .add (.reg .x24) (cE 128)) (cE l)) (cE 1)) (cE 4)
def fdw (c : Nat) : Nat := WCT9.childBase c / 64
def fsh (c : Nat) : Nat := [0,0,21,36,0,21,36,0,21].getD c 0
def fhas (c : Nat) : Bool := c % 3 != 1
def fsrcE (c : Nat) : E :=
  if fhas c then .bin .srl (ldc (NBUF + 8 * fdw c)) (cE (fsh c)) else ldc (NBUF + 8 * fdw c)
def fchildE (c : Nat) : E := if c = 3 ∨ c = 6 then .bin .srl (fsrcE c) (cE 21) else .bin .and (fsrcE c) (cE 127)
def fieldE (c : Nat) : E := .bin .and (.bin .srl (fsrcE c) (cE 7)) (cE 1023)
def expF (c : Nat) : PRes :=
  pres [(.x6, .bin .sll (fieldE c) (cE 2)), (.x24, fchildE c), (.x25, fieldE c),
    (.x28, .bin .add (.bin .sll (fieldE c) (cE 2)) (cE TBL))] [] [] (lwuI c) false
    (if fhas c then 13 else 12) []
def expChk (c i s v : Nat) : PRes :=
  if v = 0 then pres [] [] [] (skipI c i s) false 1 [⟨.ne, .reg .x18, .reg .x24, true⟩]
  else if v = 1 then
    pres [(.x6, cE s)] [] [] (skipI c i s) false 3 [⟨.ne, .reg .x26, cE s, true⟩, ⟨.ne, .reg .x18, .reg .x24, false⟩]
  else
    pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x28, cE CHAINW), (.x29, cE (slotV c i))]
      [mwc (slotV c i + 8) (ldc (CHAINW + 56)), mwc (slotV c i) (ldc (CHAINW + 48))] [] (skipI c i s) false 11
      [⟨.ne, .reg .x26, cE s, false⟩, ⟨.ne, .reg .x18, .reg .x24, false⟩]
def expStp (c i s : Nat) : PRes :=
  pres [(.x6, cE (s - 1)), (.x10, cE CHAINW), (.x11, cE 64), (.x12, cE (CHAINW + 48)), (.x29, cE CHAINW)]
    [mwc (CHAINW + 16) (.bin (.st .b 1) (ldc (CHAINW + 16)) (cE (s - 1)))] [] (chkI c i s - 1) true 9 []
def expLc (c i : Nat) : PRes :=
  pres [(.x6, ldc (CHAINW + 48)), (.x7, ldc (CHAINW + 56)), (.x28, cE CHAINW), (.x29, cE LEAFW)]
    [mwc (LEAFW + leafOff i + 8) (ldc (CHAINW + 56)), mwc (LEAFW + leafOff i) (ldc (CHAINW + 48))] []
    (lcEnd c i) false 8 []
/-- Nested FTS (r1-1): the leaf pad word `off` of coordinate `c`, i.e. `L_{c-1}` from the previous forest pair. -/
def padE (c off : Nat) : E := if c = 0 then cE 0 else ldc (FORW + forOff (c - 1) + off)
def expL (c : Nat) : PRes :=
  pres [(.x6, heapLeafE), (.x7, leafX7 c), (.x10, cE LEAFW), (.x11, cE 128), (.x12, .bin .add heapLeafE (cE HEAPW))]
    [(x29A 24, cE 0), (x29A 16, leafLoE c), (x29A 40, padE c 8), (x29A 32, padE c 0)]
    ([.valid (x29A 24) 8, .valid (x29A 16) 8, .valid (x29A 40) 8] ++
      (if c = 0 then [] else [.ne ⟨none, BitVec.ofNat 64 (FORW + forOff (c - 1) + 8)⟩ (x29A 32)]) ++
      [.valid (x29A 32) 8]) (tI c - 1) true
    (if c = 0 then 21 else 23) []
def expT (c : Nat) (back : Bool) : PRes :=
  if back then pres [(.x6, cE 128), (.x18, x18p1)] [] [] (leafI c) false 3 [⟨.ltu, x18p1, cE 128, true⟩]
  else pres [(.x6, cE 128), (.x18, cE 127)] [] [] (nodeI c) false 4 [⟨.ltu, x18p1, cE 128, false⟩]
def nodeLd (off : Nat) : E := .ld (.bin .add sh5 (cE (HEAPW + off)))
def nodeAddr (off : Nat) : Addr := ⟨some sh5, BitVec.ofNat 64 (HEAPW + off)⟩
def nodeX7 (c : Nat) : E := cE (65536 * (c + 1))
/-- Packed node tweak (heaps `8..127`): high word `[h < 8] * h`, low word `nodeLo7 + [h < 8] * h - h`. -/
def nodeHiE : E := .bin .mul (.bin .sltu (.reg .x18) (cE 8)) (.reg .x18)
def nodeDE : E := .bin .sub nodeHiE (.reg .x18)
def nodeLoNE (c : Nat) : E := .bin .add (nodeLoE c) nodeDE
def expN (c : Nat) : PRes :=
  pres2 [(.x6, nodeLoNE c), (.x7, nodeDE), (.x10, cE NODEW), (.x11, cE 64), (.x12, cE NOUTW),
    (.x28, .bin .add sh5 (cE HEAPW)), (.x29, nodeHiE)]
    [mwc (NODEW + 24) nodeHiE, mwc (NODEW + 16) (nodeLoNE c), mwc (NODEW + 56) (nodeLd 24),
      mwc (NODEW + 48) (nodeLd 16), mwc (NODEW + 8) (nodeLd 8), mwc NODEW (nodeLd 0)]
    [.ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 NODEW⟩, .ne (nodeAddr 24) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩,
      .valid (nodeAddr 24) 8, .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 NODEW⟩,
      .ne (nodeAddr 16) ⟨none, BitVec.ofNat 64 (NODEW + 8)⟩, .valid (nodeAddr 16) 8, .valid (nodeAddr 8) 8,
      .valid (nodeAddr 0) 8]
    (ntI c - 1) true (if c = 0 then 29 else 25) (if c = 0 then 32 else 28) []
def heapAddr (off : Nat) : Addr := ⟨some sh4, BitVec.ofNat 64 (HEAPW + off)⟩
/-- Nested FTS (r1-1): the fold output half, `16 * [heap < 4]` (heaps 2 and 3 keep the HIGH half). -/
def hiSelE : E := .bin .sll (.bin .sltu (.reg .x18) (cE 4)) (cE 4)
def outE : E := .bin .add hiSelE (cE NOUTW)
def outAddr (off : Nat) : Addr := ⟨some hiSelE, BitVec.ofNat 64 (NOUTW + off)⟩
def outLd (off : Nat) : E := .ld (.bin .add hiSelE (cE (NOUTW + off)))
/-- Fold post-hash kind for `c >= 1`: 0 = heap other than 4 and 2, 1 = heap 4 (pad := R_{c-1}), 2 = heap 2 (pad := 0). -/
def ntDirs (c kd : Nat) (back : Bool) : List Dir :=
  if c = 0 then [.br back] else if kd = 1 then [.br false, .br back] else if kd = 2 then [.br true, .br false, .br back]
  else [.br true, .br true, .br back]
def ntPadMem (c kd : Nat) : SymMem :=
  if c = 0 then [] else if kd = 1 then
    [mwc (NODEW + 40) (ldc (FORW + forOff (c - 1) + 24)), mwc (NODEW + 32) (ldc (FORW + forOff (c - 1) + 16))]
  else if kd = 2 then [mwc (NODEW + 40) (cE 0), mwc (NODEW + 32) (cE 0)] else []
def ntOutObl (c kd : Nat) : List Oblig :=
  if c = 0 ∨ kd = 0 then [.valid (outAddr 8) 8, .valid (outAddr 0) 8]
  else [.ne (outAddr 8) ⟨none, BitVec.ofNat 64 (NODEW + 32)⟩, .ne (outAddr 8) ⟨none, BitVec.ofNat 64 (NODEW + 40)⟩,
    .valid (outAddr 8) 8, .ne (outAddr 0) ⟨none, BitVec.ofNat 64 (NODEW + 32)⟩,
    .ne (outAddr 0) ⟨none, BitVec.ofNat 64 (NODEW + 40)⟩, .valid (outAddr 0) 8]
def ntBrs (c kd : Nat) : List Br :=
  if c = 0 then [] else if kd = 1 then [⟨.ne, .reg .x18, cE 4, false⟩]
  else if kd = 2 then [⟨.ne, .reg .x18, cE 2, false⟩, ⟨.ne, .reg .x18, cE 4, true⟩]
  else [⟨.ne, .reg .x18, cE 2, true⟩, ⟨.ne, .reg .x18, cE 4, true⟩]
def expNT (c kd : Nat) (back : Bool) : PRes :=
  pres [(.x6, cE 1), (.x7, outLd 8), (.x18, x18m1), (.x28, outE),
    (.x29, .bin .add sh4 (cE HEAPW))]
    ([(heapAddr 8, outLd 8), (heapAddr 0, outLd 0)] ++ ntPadMem c kd)
    ([.valid (heapAddr 8) 8, .valid (heapAddr 0) 8] ++ ntOutObl c kd)
    (if back then nodeI c else rI c) false (if c = 0 then 18 else if kd = 0 then 22 else 25)
    (⟨.ne, x18m1, cE 1, back⟩ :: ntBrs c kd)
def expR0 (c : Nat) : PRes :=
  pres [(.x6, ldc (HEAPW + 48)), (.x7, ldc (HEAPW + 56)), (.x28, cE (HEAPW + 32)), (.x29, cE (FORW + forOff c))]
    [mwc (FORW + forOff c + 24) (ldc (HEAPW + 56)), mwc (FORW + forOff c + 16) (ldc (HEAPW + 48)),
      mwc (FORW + forOff c + 8) (ldc (HEAPW + 40)), mwc (FORW + forOff c) (ldc (HEAPW + 32))] [] (pcI c 0) false 12 []
def pathAddr (l off : Nat) : Addr := ⟨some (pathE l), BitVec.ofNat 64 (HEAPW + off)⟩
def pathLd (l off : Nat) : E := .ld (.bin .add (pathE l) (cE (HEAPW + off)))
def expPC (c l : Nat) : PRes :=
  pres [(.x6, pathLd l 0), (.x7, pathLd l 8), (.x28, .bin .add (pathE l) (cE HEAPW)), (.x29, cE (slotP c l))]
    [mwc (slotP c l + 8) (pathLd l 8), mwc (slotP c l) (pathLd l 0)] [.valid (pathAddr l 8) 8, .valid (pathAddr l 0) 8]
    (pcI c (l + 1)) false 13 []
def expSK : PRes :=
  pres [(.x6, ldc 0x90), (.x7, ldc 0x98), (.x28, cE 0x80), (.x29, cE PRIVW)]
    [mwc (PRIVW + 40) (ldc 0x98), mwc (PRIVW + 32) (ldc 0x90), mwc (PRIVW + 8) (ldc 0x88), mwc PRIVW (ldc 0x80)] []
    (fieldIdx.getD 0 0) false 11 []
/-- Nested FTS (r1-1): the forest hash is replaced by copying `(L8, R8)` to `FOUT` and the encoding R slot. -/
def expFor : PRes :=
  pres [(.x6, ldc (FORW + forOff 8 + 16)), (.x7, ldc (FORW + forOff 8 + 24)), (.x28, cE PRIVW), (.x29, cE 0x20000)]
    [mwc (0x20290 + 8) (ldc (FORW + forOff 8 + 24)), mwc 0x20290 (ldc (FORW + forOff 8 + 16)),
      mwc (FOUT + 8) (ldc (FORW + forOff 8 + 8)), mwc FOUT (ldc (FORW + forOff 8))] [] 370 false 12 []
def expJ : PRes := pres [] [] [] 370 false 1 []
def runF (c : Nat) : Option PRes := run (coordLook c) [lwuI c] (cbase c) []
def chkDirs (v : Nat) : List Dir := if v = 0 then [.br true] else if v = 1 then [.br false, .br true] else [.br false, .br false]
def runChk (c i s v : Nat) : Option PRes := run (coordLook c) [skipI c i s] (chkI c i s) (chkDirs v)
def runStp (c i s : Nat) : Option PRes := run (coordLook c) [] (skipI c i (s - 1)) []
def runLc (c i : Nat) : Option PRes := run (coordLook c) [lcEnd c i] (skipI c i 4) []
def runL (c : Nat) : Option PRes := runA (coordLook c) [] (lI c) []
def runT (c : Nat) (back : Bool) : Option PRes := run (coordLook c) [leafI c, nodeI c] (tI c) [.br back]
def runN (c : Nat) : Option PRes := runA (coordLook c) [] (nodeI c) []
def runNT (c kd : Nat) (back : Bool) : Option PRes := runA (coordLook c) [nodeI c, rI c] (ntI c) (ntDirs c kd back)
def runR0 (c : Nat) : Option PRes := run (coordLook c) [pcI c 0] (rI c) []
def runPC (c l : Nat) : Option PRes := run (coordLook c) [pcI c (l + 1)] (pcI c l) []
def runSK : Option PRes := run headLook [fieldIdx.getD 0 0] 11175 []
def runFor : Option PRes := run forLook [370] 20715 []
def runJ : Option PRes := run tailLook [370] 20729 []
/-! ### Stage A (campaign X1): coefficient prologue, call sites and the shared GF(2^128) Horner routine HORN -/
def paIdx : List Nat := [11962,13021,14081,15141,16200,17260,18320,19379,20439]
def paI (c : Nat) : Nat := paIdx.getD c 0
def ecI (c : Nat) : Nat := paI c - 1
def hornI : Nat := 11368
def hkI : Nat := 11220
def hbI : Nat := 11226
def hfI : Nat := 11374
def orIdx : E := .bin .or (cE 0) (.reg .x22)
def x7p1 : E := .bin .add (.reg .x7) (cE 1)
def pairWE : E := .bin .or (.bin .sll x7p1 (cE 32)) (.reg .x22)
def expZ (c : Nat) : PRes :=
  pres [(.x6, orIdx), (.x7, cE 0), (.x10, cE PRIVW), (.x11, cE 64), (.x12, cE COEF), (.x29, cE PRIVW)]
    [mwc (PRIVW + 24) orIdx, mwc (PRIVW + 16) (cE (hdr8 c))] [] (ecI c) true 14 []
def expCL (c : Nat) (b : Bool) : PRes :=
  if b then
    pres [(.x6, pairWE), (.x7, x7p1), (.x10, cE PRIVW), (.x11, cE 64), (.x12, .bin .add (.reg .x12) (cE 32)),
      (.x29, cE PRIVW)] [mwc (PRIVW + 24) pairWE] [] (ecI c) true 10 [⟨.ne, x7p1, cE 27, true⟩]
  else
    pres [(.x6, cE 27), (.x7, x7p1), (.x12, .bin .add (.reg .x12) (cE 32)), (.x18, cE 0)] [] [] (leafI c) false 6
      [⟨.ne, x7p1, cE 27, false⟩]
def ptE (i : Nat) : E :=
  .bin .add (.bin .sll (.bin .add (.bin .sll (.reg .x18) (cE 1)) (.reg .x18)) (cE 1)) (cE (i + 1))
def retW (c i : Nat) : Nat := 0x1000 + 4 * (qI c i + 5)
def expQ (c i : Nat) : PRes := pres [(.x1, cE (retW c i)), (.x6, ptE i)] [] [] hornI false 5 []
def expS (c i : Nat) : PRes :=
  pres [(.x6, cE 4), (.x7, cE (chainK c i)), (.x26, dE i), (.x29, cE CHAINW)]
    [mwc (CHAINW + 24) (cE 0), mwc (CHAINW + 16) (qE c i)] [] (chkI c i 0) false (if c = 0 then 17 else 15) []
def expH0 : PRes := pres [(.x7, cE (COEF + 864)), (.x10, cE 0), (.x11, cE 0), (.x28, cE COEF)] [] [] hkI false 6 []
def expHK : PRes :=
  pres [(.x7, .bin .add (.reg .x7) (cE (2 ^ 64 - 16))), (.x12, cE 0), (.x13, cE 0), (.x14, cE 0), (.x15, cE 0),
    (.x16, .reg .x6)] [] [] hbI false 6 []
def sh1 (r : Reg) : E := .bin .sll (.reg r) (cE 1)
def hi63 (r : Reg) : E := .bin .srl (.reg r) (cE 63)
def xr (a b : Reg) : E := .bin .xor (.reg a) (.reg b)
def hbShift : List (Reg × E) :=
  [(.x10, sh1 .x10), (.x11, .bin .or (sh1 .x11) (hi63 .x10)), (.x12, .bin .or (sh1 .x12) (hi63 .x11)),
    (.x16, .bin .srl (.reg .x16) (cE 1)), (.x17, hi63 .x10)]
def expHB (b1 b2 : Bool) : PRes :=
  pres ((if b1 then [] else [(.x13, xr .x13 .x10), (.x14, xr .x14 .x11), (.x15, xr .x15 .x12)]) ++ hbShift) [] []
    (if b2 then hbI else hfI) false ((if b1 then 11 else 14) + (if b2 then 0 else 1))
    [⟨.ne, .bin .srl (.reg .x16) (cE 1), cE 0, b2⟩, ⟨.eq, .bin .and (.reg .x16) (cE 1), cE 0, b1⟩]
def shE (r : Reg) (k : Nat) : E := .bin .sll (.reg r) (cE k)
def foldE : E := .bin .xor (.bin .xor (.bin .xor (.bin .xor (.reg .x13) (shE .x15 1)) (shE .x15 2)) (shE .x15 7)) (.reg .x15)
def c0E : E := .ld (.reg .x7)
def c1E : E := .ld (.bin .add (.reg .x7) (cE 8))
def hfRegs : List (Reg × E) :=
  [(.x10, .bin .xor foldE c0E), (.x11, .bin .xor (.reg .x14) c1E), (.x13, foldE), (.x17, c1E)]
def hfObl : List Oblig := [.valid ⟨some (.reg .x7), BitVec.ofNat 64 8⟩ 8, .valid ⟨some (.reg .x7), 0⟩ 8]
def expHF (b : Bool) : PRes :=
  if b then pres hfRegs [] hfObl hkI false 12 [⟨.ne, .reg .x7, .reg .x28, true⟩]
  else ⟨⟨regsOf (hfRegs ++ [(.x29, cE CHAINW)]),
      [mwc (CHAINW + 56) (.bin .xor (.reg .x14) c1E), mwc (CHAINW + 48) (.bin .xor foldE c0E)], hfObl⟩,
    0, false, 17, 17, [⟨.ne, .reg .x7, .reg .x28, false⟩], some (.bin .and (.reg .x1) (cE (2 ^ 64 - 2)))⟩
def runZ (c : Nat) : Option PRes := run (coordLook c) [] (lwuI c + 1) []
def runCL (c : Nat) (b : Bool) : Option PRes := run (coordLook c) [leafI c] (paI c) [.br b]
def runQ (c i : Nat) : Option PRes := run (coordLook c) [hornI] (qI c i) []
def runS (c i : Nat) : Option PRes := run (coordLook c) [chkI c i 0] (qI c i + 5) []
def runH0 : Option PRes := run (coordLook 0) [hkI] hornI []
def runHK : Option PRes := run (coordLook 0) [hbI] hkI []
def runHB (b1 b2 : Bool) : Option PRes := run (coordLook 0) [hbI, hfI] hbI [.br b1, .br b2]
def runHF (b : Bool) : Option PRes := run (coordLook 0) [hkI] hfI (if b then [.br true] else [.br false, .jmp])
def okC (c : Nat) : Bool := optBeq (runCL c true) (expCL c true) && optBeq (runCL c false) (expCL c false)
def okQ (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runQ c i) (expQ c i)
def okS (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runS c i) (expS c i)
def okHorn : Bool :=
  optBeq runH0 expH0 && optBeq runHK expHK && optBeq (runHB true true) (expHB true true) &&
    optBeq (runHB true false) (expHB true false) && optBeq (runHB false true) (expHB false true) &&
    optBeq (runHB false false) (expHB false false) && optBeq (runHF true) (expHF true) &&
    optBeq (runHF false) (expHF false)
def okF (c : Nat) : Bool := optBeq (runF c) (expF c) && optBeq (runZ c) (expZ c)
def okChk (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range 5).all fun s => (List.range 3).all fun v =>
    optBeq (runChk c i s v) (expChk c i s v)
def okStp (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range' 1 4).all fun s => optBeq (runStp c i s) (expStp c i s)
def okLc (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runLc c i) (expLc c i)
def okTail (c : Nat) : Bool :=
  optBeq (runL c) (expL c) && optBeq (runT c true) (expT c true) && optBeq (runT c false) (expT c false) &&
    optBeq (runN c) (expN c) && optBeq (runNT c 0 true) (expNT c 0 true) &&
    optBeq (runNT c (if c = 0 then 0 else 2) false) (expNT c (if c = 0 then 0 else 2) false) &&
    optBeq (runNT c 1 true) (expNT c 1 true) &&
    optBeq (runR0 c) (expR0 c) && (List.range 7).all fun l => optBeq (runPC c l) (expPC c l)
def okCoord (c : Nat) : Bool := okF c && okC c && okQ c && okS c && okChk c && okStp c && okLc c && okTail c
def okGlobal : Bool := optBeq runSK expSK && optBeq runFor expFor && optBeq runJ expJ && okHorn
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-- The unchanged chain and coefficient region excludes the replaced field and leaf hooks. -/
def coordLookW (c n : Nat) : Option (BitVec 32) := (coordCodesW.getD c [])[n - cbase c]?
/-- Witness stack (charge 86): the installed coordinate windows (`coordCodesW`), the FTS G stubs at 21200..21229 and
the C4 arena. -/
def coordLook (c n : Nat) : Option (BitVec 32) :=
  if cbase c < n ∧ n < lI c then coordLookW c n
  else if 21200 ≤ n ∧ n < 21230 then ftsStub[n - 21200]? else arenaLook n
structure Fetch (im : Image) : Prop where
  head : LookOK im headLook
  coordinate : ∀ c, c < 9 → LookOK im (coordLook c)
theorem coordLook_ok {im : Image} (h : Fetch im) {c : Nat} (hc : c<9) : LookOK im (coordLook c) := h.coordinate c hc
theorem headLook_ok {im : Image} (h : Fetch im) : LookOK im headLook := h.head
def runChk (c i s v : Nat) : Option PRes := run (coordLook c) [skipI c i s] (chkI c i s) (chkDirs v)
def runStp (c i s : Nat) : Option PRes := run (coordLook c) [] (skipI c i (s - 1)) []
def runLc (c i : Nat) : Option PRes := run (coordLook c) [lcEnd c i] (skipI c i 4) []
def runZ (c : Nat) : Option PRes := run (coordLook c) [] (lwuI c + 1) []
def runCL (c : Nat) (b : Bool) : Option PRes := run (coordLook c) [leafI c] (paI c) [.br b]
def runQ (c i : Nat) : Option PRes := run (coordLook c) [hornI] (qI c i) []
def runS (c i : Nat) : Option PRes := run (coordLook c) [chkI c i 0] (qI c i + 5) []
def runH0 : Option PRes := run (coordLook 0) [hkI] hornI []
def runHK : Option PRes := run (coordLook 0) [hbI] hkI []
def runHB (b1 b2 : Bool) : Option PRes := run (coordLook 0) [hbI, hfI] hbI [.br b1, .br b2]
def runHF (b : Bool) : Option PRes := run (coordLook 0) [hkI] hfI (if b then [.br true] else [.br false, .jmp])
def okC (c : Nat) : Bool := optBeq (runCL c true) (expCL c true) && optBeq (runCL c false) (expCL c false)
def okQ (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runQ c i) (expQ c i)
def okS (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runS c i) (expS c i)
def okHorn : Bool :=
  optBeq runH0 expH0 && optBeq runHK expHK && optBeq (runHB true true) (expHB true true) &&
    optBeq (runHB true false) (expHB true false) && optBeq (runHB false true) (expHB false true) &&
    optBeq (runHB false false) (expHB false false) && optBeq (runHF true) (expHF true) &&
    optBeq (runHF false) (expHF false)
def okChk (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range 5).all fun s => (List.range 3).all fun v =>
    optBeq (runChk c i s v) (expChk c i s v)
/-! Witness stack: FTS G chains 1, 3. The HASH site `lui a0` becomes `jal t3,stub`; the stub copies the header to
`CHAINW+64`, zeroes `CHAINW+80..111`, hashes `CHAINW+48..111` into `CHAINW+32` (interior: the high half lands on the
value slot `CHAINW+48`) or `CHAINW+48` (terminal step, low half), zeroes `CHAINW+32/40` and returns to the site + 6. -/
def stubAt (s : Nat) : Nat := if s = 4 then 21215 else 21200
def stubOut (s : Nat) : Nat := if s = 4 then CHAINW + 48 else CHAINW + 32
def hdrE (s : Nat) : E := .bin (.st .b 1) (ldc (CHAINW + 16)) (cE (s - 1))
def expStpG (c i s : Nat) : PRes :=
  pres [(.x6, ldc (CHAINW + 24)), (.x10, cE (CHAINW + 48)), (.x11, cE 64), (.x12, cE (stubOut s)),
      (.x28, .c (pcOf (chkI c i s - 5))), (.x29, cE CHAINW)]
    [mwc (CHAINW + 104) (cE 0), mwc (CHAINW + 96) (cE 0), mwc (CHAINW + 88) (cE 0), mwc (CHAINW + 80) (cE 0),
      mwc (CHAINW + 72) (ldc (CHAINW + 24)), mwc (CHAINW + 64) (hdrE s), mwc (CHAINW + 16) (hdrE s)] []
    (stubAt s + 11) true 16 []
def knownG (c i s : Nat) : List (Reg × Word) := [(.x28, pcOf (chkI c i s - 5)), (.x29, BitVec.ofNat 64 CHAINW)]
def runPostG (c i s : Nat) : Option PRes :=
  pathAux scfg (coordLook c) [pcOf (chkI c i s)] 200 (pcOf (stubAt s + 12)) [] (σK (knownG c i s)) []
def expPostG (c i s : Nat) : PRes :=
  ⟨⟨RegFile.withKnown (knownG c i s), [mwc (CHAINW + 40) (cE 0), mwc (CHAINW + 32) (cE 0)], []⟩,
    pcOf (chkI c i s), false, 3, 3, [], none⟩
def okStp (c : Nat) : Bool :=
  (List.range 6).all fun i => (List.range' 1 4).all fun s =>
    if WCT9.ftsIsG i then optBeq (runStp c i s) (expStpG c i s) && optBeq (runPostG c i s) (expPostG c i s)
    else optBeq (runStp c i s) (expStp c i s)
def okLc (c : Nat) : Bool := (List.range 6).all fun i => optBeq (runLc c i) (expLc c i)
def okCoord (c : Nat) : Bool := optBeq (runZ c) (expZ c) && okC c && okQ c && okS c && okChk c && okStp c && okLc c
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x20eb023,0x20eb423,0x1bb1313,0x1491393,0x730333,0xeeceb06f,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words1 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0xe0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x203b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words2 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x640e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x303b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words3 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0x40e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x403b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words4 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x680e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x503b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words5 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0x80e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x603b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words6 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x6c0e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x703b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words7 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x197313,0x531313,0x67e37,0xc0e0e13,0x6e0e33,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x803b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def words8 : List (BitVec 32) := bv_list% 32 [0x50eb7,0x200e8e93,0x50e37,0x700e0e13,0xe3303,0x8e3383,0x26eb023,0x27eb423,0x1bb1313,0x1491393,0x730333,0x903b7,0x60138393,0x730333,0x6eb823,0xebc23,0x90313,0x137393,0x639393,0x135313,0x730333,0x8030313,0x431313,0x51637,0x60613,0x660633,0x50537,0x20050513,0x8000593,0x73]
def entry (c : Nat) : Nat := [22780,22970,23192,23394,23616,23818,24040,24242,24464].getD c 0
def hashPc (c : Nat) : Nat := [22800,23002,23217,23426,23641,23850,24065,24274,24493].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def c4StubPc : Nat := 1726
def c4Stub : List (BitVec 32) := bv_list% 32 [0x103b7,0x60138393,0x1111406f]
def look (c n : Nat) : Option (BitVec 32) := if entry c ≤ n then (words c)[n-entry c]? else if c = 0 ∧ c4StubPc ≤ n then c4Stub[n-c4StubPc]? else none
def runLeaf (c : Nat) : Option PRes := run (look c) [] (entry c) []
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def branchE : E := .bin .and (.reg .x18) (cE 1)
def branchShift (k : Nat) : E := .bin .sll branchE (cE k)
def physicalE (c : Nat) : E := if first c then .reg .x18 else .bin .add (.bin .srl (.reg .x18) (cE 1)) (branchShift 6)
def outOffset (c : Nat) : E := .bin .sll (.bin .add (physicalE c) (cE 128)) (cE 4)
def padAddr (c off : Nat) : E :=
  if c%2=1 then .bin .add (branchShift 5) (cE (0x67000+64*(c/2)+off)) else cE (FORW+32*c+off)
def padLoad (c off : Nat) : E := if c=0 then cE 0 else .ld (padAddr c off)
def headerE (c : Nat) : E := .bin .add
  (.bin .add (.bin .sll (.reg .x22) (cE 27)) (.bin .sll (.reg .x18) (cE 20))) (cE (1537+65536*(c+1)))
def leafRegs (c : Nat) : List (Reg × E) :=
  [(.x6,outOffset c),(.x7,if first c then cE (1537+65536*(c+1)) else branchShift 6),
   (.x10,cE LEAFW),(.x11,cE 128),(.x12,.bin .add (outOffset c) (cE HEAPW)),
   (.x28,if c=0 then .reg .x28 else padAddr c 0),(.x29,cE LEAFW)]
def leafMem (c : Nat) : SymMem :=
  [mwc (LEAFW+24) (cE 0),mwc (LEAFW+16) (headerE c),mwc (LEAFW+40) (padLoad c 8),mwc (LEAFW+32) (padLoad c 0)]
def leafObl (c : Nat) : List Oblig := if c%2=1 then
  [.valid ⟨some (branchShift 5),BitVec.ofNat 64 (0x67000+64*(c/2)+8)⟩ 8,
   .valid ⟨some (branchShift 5),BitVec.ofNat 64 (0x67000+64*(c/2))⟩ 8] else []
def cycles (c : Nat) : Nat := if c=0 then 23 else if c%2=1 then 32 else if c=8 then 29 else 25
def expected (c : Nat) : PRes := pres (leafRegs c) (leafMem c) (leafObl c) (hashPc c) true (cycles c) []
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0xe6ceb06f,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x180006f,0x653823,0x1253c23,0x400393,0x796463,0x40006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words1 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x203b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x10e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words2 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x303b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x650e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words3 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x403b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x50e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words4 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x503b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x690e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words5 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x603b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0x90e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words6 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x703b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x6d0e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words7 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x803b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x400006f,0x653823,0x1253c23,0x400393,0x2796863,0x195313,0xffe30313,0x531313,0x67e37,0xd0e0e13,0x6e0e33,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def words8 : List (BitVec 32) := bv_list% 32 [0x51e37,0xe0e13,0x591313,0x6e0e33,0x50537,0x30050513,0xe3303,0x8e3383,0x653023,0x753423,0x10e3303,0x18e3383,0x2653823,0x2753c23,0x1bb1313,0x903b7,0x60138393,0x730333,0x800393,0x796a63,0x41230333,0x653823,0x53c23,0x300006f,0x653823,0x1253c23,0x400393,0x2796063,0x50e37,0x710e0e13,0xe3303,0x8e3383,0x2653023,0x2753423,0xc0006f,0x2053023,0x2053423,0x4000593,0x50637,0x50060613,0x73]
def entry (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
def hashPc (c : Nat) : Nat := [22840, 23058, 23264, 23482, 23688, 23906, 24112, 24330, 24545].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def c4StubPc : Nat := 1729
def c4Stub : List (BitVec 32) := bv_list% 32 [0x103b7,0x60138393,0x1911406f]
def look (c n : Nat) : Option (BitVec 32) := if entry c ≤ n then (words c)[n-entry c]? else if c = 0 ∧ c4StubPc ≤ n then c4Stub[n-c4StubPc]? else none
def dirs (mode : Nat) : List Dir := if mode=0 then [.br false] else [.br true,.br (mode=2)]
def runNode (c mode : Nat) : Option PRes := runA (look c) [] (entry c) (dirs mode)
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify

def loE (c : Nat) : E := .bin .add (.bin .sll (.reg .x22) (cE 27)) (cE (1537+65536*(c+1)))
def hdrLo (c mode : Nat) : E := if mode=0 then .bin .sub (loE c) (.reg .x18) else loE c
def hdrHi (mode : Nat) : E := if mode=0 then cE 0 else .reg .x18
def padShift : E := .bin .sll (.bin .add (.bin .srl (.reg .x18) (cE 1)) (cE (2^64-2))) (cE 5)
def padAddr (c off : Nat) : E :=
  if c%2=1 then .bin .add padShift (cE (0x67000+64*(c/2)+16+off)) else cE (FORW+32*c+16+off)
def padWord (c mode off : Nat) : E := if mode=1 ∧ c≠0 then .ld (padAddr c off) else cE 0

def regs (c mode : Nat) : List (Reg × E) :=
  [(.x6,if mode=1 ∧ c≠0 then padWord c mode 0 else hdrLo c mode),
   (.x7,if mode=1 ∧ c≠0 then padWord c mode 8 else cE (if mode=0 then 8 else 4)),
   (.x10,cE NODEW),(.x11,cE 64),(.x12,cE NOUTW),
   (.x28,if mode=1 ∧ c≠0 then padAddr c 0 else .bin .add sh5 (cE HEAPW))]
def mem (c mode : Nat) : SymMem :=
  [mwc (NODEW+40) (padWord c mode 8),mwc (NODEW+32) (padWord c mode 0),
   mwc (NODEW+24) (hdrHi mode),mwc (NODEW+16) (hdrLo c mode),
   mwc (NODEW+56) (nodeLd 24),mwc (NODEW+48) (nodeLd 16),mwc (NODEW+8) (nodeLd 8),mwc NODEW (nodeLd 0)]
def readObl : List Oblig :=
  [.ne (nodeAddr 24) ⟨none,BitVec.ofNat 64 NODEW⟩,.ne (nodeAddr 24) ⟨none,BitVec.ofNat 64 (NODEW+8)⟩,
   .valid (nodeAddr 24) 8,.ne (nodeAddr 16) ⟨none,BitVec.ofNat 64 NODEW⟩,
   .ne (nodeAddr 16) ⟨none,BitVec.ofNat 64 (NODEW+8)⟩,.valid (nodeAddr 16) 8,
   .valid (nodeAddr 8) 8,.valid (nodeAddr 0) 8]
def padReadAddr (c off : Nat) : Addr := ⟨some padShift,BitVec.ofNat 64 (0x67000+64*(c/2)+16+off)⟩
def padReadObl (c off : Nat) : List Oblig :=
  ([0,8,48,56,16,24].map fun n=>Oblig.ne (padReadAddr c off) ⟨none,BitVec.ofNat 64 (NODEW+n)⟩) ++
    [.valid (padReadAddr c off) 8]
def obligations (c mode : Nat) : List Oblig :=
  (if mode=1 ∧ c%2=1 then padReadObl c 8 ++ padReadObl c 0 else []) ++ readObl

def branches (mode : Nat) : List Br :=
  if mode=0 then [⟨.ltu,.reg .x18,cE 8,false⟩] else
    [⟨.ltu,.reg .x18,cE 4,mode=2⟩,⟨.ltu,.reg .x18,cE 8,true⟩]
def cycles (c mode : Nat) : Nat :=
  if mode=1 then if c=0 then 32 else if c%2=1 then 38 else 34 else if c=0 then 31 else 29
def expected (c mode : Nat) : PRes :=
  pres (regs c mode) (mem c mode) (obligations c mode) (hashPc c) true (cycles c mode) (branches mode)
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def hookWords : List (BitVec 32) := bv_list% 32 [0x7480a06f,0x1b90906f,0x4a10806f,0x7390706f,0x2240706f,0x4bc0606f,0x7a40506f,0x2410406f,0x5290306f]
def hookLook (c n : Nat) : Option (BitVec 32) := if n=lI c then some (hookWords.getD c 0) else none
def runHook (c : Nat) : Option PRes := run (hookLook c) [entry c] (lI c) []
def expectedHook (c : Nat) : PRes := pres [] [] [] (entry c) false 1 []
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-! C1 (stage 1): the first word after each leaf `ecall` is a hook `jal zero,stub`. The stub copies the HIGH half
of the leaf answer (`a2+16..31`) onto its LOW half (`a2+0..15`) when the physical child is even (heap `128+p`
even), re-executes the displaced instruction and jumps back to the word after the hook. -/
def words0 : List (BitVec 32) := bv_list% 32 [0xa94ff06f,0x8000313,0x696663,0x7f00913,0x80006f,0xaadf406f]
def words1 : List (BitVec 32) := bv_list% 32 [0xfadfe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xfdcf506f]
def words2 : List (BitVec 32) := bv_list% 32 [0xc95fe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xd24f606f]
def words3 : List (BitVec 32) := bv_list% 32 [0x991fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xa5cf706f]
def words4 : List (BitVec 32) := bv_list% 32 [0xf1cfe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xfa1f706f]
def words5 : List (BitVec 32) := bv_list% 32 [0xc18fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xcd9f806f]
def words6 : List (BitVec 32) := bv_list% 32 [0x900fe06f,0x8000313,0x696663,0x7f00913,0x80006f,0xa21f906f]
def words7 : List (BitVec 32) := bv_list% 32 [0xce0fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xf54fa06f]
def words8 : List (BitVec 32) := bv_list% 32 [0x9b8fe06f,0x690e63,0x7e00313,0x690663,0x290913,0x140006f,0x100913,0xc0006f,0x7f00913,0x80006f,0xc78fb06f]
def stub0 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x5550006f]
def stub1 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x380106f]
def stub2 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x3540106f]
def stub3 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x6540106f]
def stub4 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0xcd0106f]
def stub5 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x3cd0106f]
def stub6 : List (BitVec 32) := bv_list% 32 [0x197313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x190913,0x6e90106f]
def stub7 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x3050106f]
def stub8 : List (BitVec 32) := bv_list% 32 [0x195313,0x137313,0x31a63,0x1063303,0x663023,0x1863303,0x663423,0x7f00313,0x62d0106f]
def entry (c : Nat) : Nat := [22801, 23003, 23218, 23427, 23642, 23851, 24066, 24275, 24494].getD c 0
def nodePc (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
/-- C1 leaf stub entry of coordinate `c` (in the former nop gaps of `signCode_85`). -/
def stubPc (c : Nat) : Nat := [21942, 21958, 21975, 21991, 22049, 22065, 22082, 22539, 22556].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def stubWords (c : Nat) : List (BitVec 32) := [stub0,stub1,stub2,stub3,stub4,stub5,stub6,stub7,stub8].getD c []
def look (c n : Nat) : Option (BitVec 32) :=
  if entry c ≤ n then (words c)[n-entry c]? else if stubPc c ≤ n then (stubWords c)[n-stubPc c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def dirs (c mode : Nat) : List Dir := if first c then [.br (mode≠2)] else
  if mode=2 then [.br true] else [.br false,.br (mode=1)]
/-- `odd`: the physical child is odd (the stub's `bne` is taken and the LOW half is kept). -/
def runNext (c mode : Nat) (odd : Bool) : Option PRes :=
  run (look c) [leafI c,nodePc c] (entry c) (.br odd :: dirs c mode)
def nextE (c mode : Nat) : E := if mode=2 then cE 127 else if first c then x18p1 else
  if mode=1 then cE 1 else .bin .add (.reg .x18) (cE 2)
def cycles (c mode : Nat) : Nat := if first c then if mode=2 then 5 else 4 else if mode=2 then 4 else 7
def branches (c mode : Nat) : List Br := if first c then [⟨.ltu,x18p1,cE 128,mode≠2⟩] else
  if mode=2 then [⟨.eq,.reg .x18,cE 127,true⟩] else
  [⟨.eq,.reg .x18,cE 126,mode=1⟩,⟨.eq,.reg .x18,cE 127,false⟩]
/-- The stub's parity test: physical parity is raw bit 0 on A coordinates and raw bit 1 on B/C coordinates. -/
def parityE (c : Nat) : E := if first c then .bin .and (.reg .x18) (cE 1) else
  .bin .and (.bin .srl (.reg .x18) (cE 1)) (cE 1)
def a2A (off : Nat) : Addr := ⟨some (.reg .x12),BitVec.ofNat 64 off⟩
def a2Ld (off : Nat) : E := .ld (.bin .add (.reg .x12) (cE off))
def stubMem (odd : Bool) : SymMem := if odd then [] else [(a2A 8,a2Ld 24),(a2A 0,a2Ld 16)]
def stubObl (odd : Bool) : List Oblig := if odd then [] else
  [.valid (a2A 8) 8,.valid (a2A 24) 8,.valid (a2A 0) 8,.valid (a2A 16) 8]
def stubCycles (c : Nat) (odd : Bool) : Nat := (if first c then 4 else 5)+(if odd then 0 else 4)
def expected (c mode : Nat) (odd : Bool) : PRes := pres
  [(.x6,cE (if first c then 128 else if mode=2 then 127 else 126)),(.x18,nextE c mode)]
  (stubMem odd) (stubObl odd) (if mode=2 then nodePc c else leafI c) false (cycles c mode+stubCycles c odd)
  (branches c mode++[⟨.ne,parityE c,cE 0,odd⟩])
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
/-! C1 (stage 1): the fold half selector is a hook `jal zero,stub` (A/B: the former `addi t2,zero,8|4`; C: the
displaced `lui t4,0x51`). The stub selects the HIGH half (`t3 += 16`) iff `heap < halfLimit` (A/B tops, as in
#884) or `heap ≥ 16` and even (C1), and jumps back past Ghost's (now dead) `bgeu`/`addi t3` pair.
Stage 2 (merged singleton "Cm"): the C stub (22565..22573, 9 words) has the A/B shape with the first test
`heap = 2` (`addi t1,s2,-2; beq t1,zero,HI`) in place of `heap < halfLimit`, so the singleton's left top node
(heap 2) keeps the HIGH half; heap 3 keeps the LOW half. -/
def words0 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xa0cff06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf2691ee3]
def words1 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xee9fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words2 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xbf1fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words3 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x8cdfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words4 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xe78fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words5 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xb54fe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words6 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x85cfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x300313,0xf26910e3]
def words7 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0xc1cfe06f,0x797463,0x10e0e13,0x51eb7,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf06918e3]
def words8 : List (BitVec 32) := bv_list% 32 [0x50e37,0x500e0e13,0x904fe06f,0xe8e93,0x491313,0x6e8eb3,0xe3303,0x8e3383,0x6eb023,0x7eb423,0xfff90913,0x100313,0xf26916e3]
def stub0 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x5e50006f]
def stub1 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x1080106f]
def stub2 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x4000106f]
def stub3 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x7240106f]
def stub4 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x1790106f]
def stub5 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x49d0106f]
def stub6 : List (BitVec 32) := bv_list% 32 [0x893313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x7950106f]
def stub7 : List (BitVec 32) := bv_list% 32 [0x493313,0x31a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x3d50106f]
def stub8 : List (BitVec 32) := bv_list% 32 [0xffe90313,0x30a63,0x1093313,0x31863,0x197313,0x31463,0x10e0e13,0x51eb7,0x6e10106f]
def entry (c : Nat) : Nat := [22841, 23059, 23265, 23483, 23689, 23907, 24113, 24331, 24546].getD c 0
def finishPc (c : Nat) : Nat := [22857, 23075, 23281, 23499, 23705, 23923, 24129, 24347, 24559].getD c 0
def nodePc (c : Nat) : Nat := [22807, 23014, 23224, 23438, 23648, 23862, 24072, 24286, 24505].getD c 0
/-- C1 fold stub entry of coordinate `c`. -/
def stubPc (c : Nat) : Nat := [21950, 21967, 21983, 22000, 22057, 22074, 22090, 22548, 22565].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def stubWords (c : Nat) : List (BitVec 32) := [stub0,stub1,stub2,stub3,stub4,stub5,stub6,stub7,stub8].getD c []
def look (c n : Nat) : Option (BitVec 32) :=
  if entry c ≤ n then (words c)[n-entry c]? else if stubPc c ≤ n then (stubWords c)[n-stubPc c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def limit (c : Nat) : Nat := if first c then 3 else 1
def halfLimit (c : Nat) : Nat := if first c then 8 else 4
/-- The stub's path class of heap `h`: `0` a top heap below `halfLimit` (A/B) or the singleton's heap 2 (C, stage 2)
(HIGH), `1` another heap below 16 (LOW), `2` an odd heap `≥ 16` (LOW), `3` an even heap `≥ 16` (HIGH, C1). -/
def cls (c h : Nat) : Nat :=
  if (c≠8 ∧ h<halfLimit c) ∨ (c=8 ∧ h=2) then 0 else if h<16 then 1 else if h%2=1 then 2 else 3
def clsHigh (_c k : Nat) : Bool := decide (k=0 ∨ k=3)
/-- Branch directions of the stub (the same for every coordinate since stage 2). -/
def stubDirs (_c k : Nat) : List Dir :=
  if k=0 then [.br true] else if k=1 then [.br false,.br true] else if k=2 then [.br false,.br false,.br true]
  else [.br false,.br false,.br false]
def dirs (c k : Nat) (back : Bool) : List Dir := stubDirs c k++[.br back]
def runTail (c k : Nat) (back : Bool) : Option PRes :=
  run (look c) [nodePc c,finishPc c] (entry c) (dirs c k back)
def halfOff (high : Bool) : Nat := if high then 16 else 0
def outWord (high : Bool) (off : Nat) : E := ldc (NOUTW+halfOff high+off)
/-- Tail cycles by class (stage 2: the singleton's 18/19/21/22 equal A/B's). -/
def cycles (_c k : Nat) : Nat := if k=0 then 18 else if k=1 then 19 else if k=2 then 21 else 22
def ltB (n : Nat) (d : Bool) : Br := ⟨.ne,.bin .sltu (.reg .x18) (cE n),cE 0,d⟩
def oddB (d : Bool) : Br := ⟨.ne,.bin .and (.reg .x18) (cE 1),cE 0,d⟩
/-- Stage 2 (C stub): `addi t1,s2,-2; beq t1,zero,HI`, i.e. `heap = 2`. -/
def eq2B (d : Bool) : Br := ⟨.eq,.bin .add (.reg .x18) (cE (2^64-2)),cE 0,d⟩
/-- The stub's first test: `heap < halfLimit` on A/B, `heap = 2` on the singleton C. -/
def topB (c : Nat) (d : Bool) : Br := if c=8 then eq2B d else ltB (halfLimit c) d
def stubBranches (c k : Nat) : List Br :=
  if k=0 then [topB c true] else if k=1 then [ltB 16 true,topB c false]
  else if k=2 then [oddB true,ltB 16 false,topB c false]
  else [oddB false,ltB 16 false,topB c false]
def branches (c k : Nat) (back : Bool) : List Br := ⟨.ne,x18m1,cE (limit c),back⟩::stubBranches c k
def expected (c k : Nat) (back : Bool) : PRes :=
  pres [(.x6,cE (limit c)),(.x7,outWord (clsHigh c k) 8),(.x18,x18m1),
    (.x28,cE (NOUTW+halfOff (clsHigh c k))),(.x29,.bin .add sh4 (cE HEAPW))]
    [(heapAddr 8,outWord (clsHigh c k) 8),(heapAddr 0,outWord (clsHigh c k) 0)]
    [.valid (heapAddr 8) 8,.valid (heapAddr 0) 8]
    (if back then nodePc c else finishPc c) false (cycles c k) (branches c k back)
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0xe8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words1 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x640e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words2 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0x40e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words3 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x680e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words4 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0x80e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words5 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x6c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words6 : List (BitVec 32) := bv_list% 32 [0x51e37,0x40e0e13,0x67eb7,0xc0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x20e3303,0x28e3383,0x26eb023,0x27eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x80c0c13]
def words7 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x700e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def words8 : List (BitVec 32) := bv_list% 32 [0x51e37,0x20e0e13,0x50eb7,0x720e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e3303,0x18e3383,0x6eb823,0x7ebc23,0x1c7313,0x631313,0x1c5c13,0x6c0c33,0x80c0c13]
def entry (c : Nat) : Nat := [22857, 23075, 23281, 23499, 23705, 23923, 24129, 24347, 24559].getD c 0
def pathPc (c : Nat) : Nat := [22878, 23092, 23302, 23516, 23726, 23940, 24150, 24364, 24576].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def look (c n : Nat) : Option (BitVec 32) := if entry c≤n then (words c)[n-entry c]? else none
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def source (c : Nat) : Nat := HEAPW+(if first c then 64 else 32)
def target (c : Nat) : Nat := if first c then 0x67000+64*(c/2) else FORW+32*(c+1)
def nwords (c : Nat) : Nat := if first c then 8 else 4
def loBit : E := .bin .sll (.bin .and (.reg .x24) (cE 1)) (cE 6)
def physicalE (c : Nat) : E := if first c then .reg .x24 else .bin .add (.bin .srl (.reg .x24) (cE 1)) loBit
def mem (c : Nat) : SymMem := ((List.range (nwords c)).reverse.map fun k=>mwc (target c+8*k) (ldc (source c+8*k)))
def expected (c : Nat) : PRes := pres
  [(.x6,if first c then ldc (source c+48) else loBit),(.x7,ldc (source c+8*(nwords c-1))),
   (.x24,.bin .add (physicalE c) (cE 128)),(.x28,cE (source c)),(.x29,cE (target c))]
  (mem c) [] (pathPc c) false ((words c).length) []
def runFinish (c : Nat) := runA (look c) [pathPc c] (entry c) []
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x70e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x80e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x90e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xa0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xb0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0xc0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words1 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x140e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x150e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x160e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x170e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x180e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x190e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x1a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words2 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x210e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x220e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x230e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x240e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x250e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x260e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words3 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x2e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x2f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x300e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x310e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x320e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x330e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x340e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words4 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3b0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3d0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x3f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x400e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words5 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x480e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x490e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4b0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4c0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4d0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x4e0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words6 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x550e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x560e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x570e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x580e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x590e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x5a0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words7 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x620e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x630e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x640e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x650e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x660e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x670e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x680e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def words8 : List (BitVec 32) := bv_list% 32 [0xc5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x6f0e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x1c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x700e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x2c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x710e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x3c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x720e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x4c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x730e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x5c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x740e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x6c5313,0x134313,0x431313,0x51e37,0xe0e13,0x6e0e33,0x7eb7,0x750e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423]
def basePc (c : Nat) : Nat := [22878, 23092, 23302, 23516, 23726, 23940, 24150, 24364, 24576].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def entry (c level : Nat) : Nat := basePc c+12*level
def look (c n : Nat) : Option (BitVec 32) := if basePc c≤n then (words c)[n-basePc c]? else none
def levels (c : Nat) : Nat := if c<8 ∧ c%2=0 then 6 else 7
def offsetE (level : Nat) : E := .bin .sll (.bin .xor (.bin .srl (.reg .x24) (cE level)) (cE 1)) (cE 4)
def address (level off : Nat) : Addr := ⟨some (offsetE level),BitVec.ofNat 64 (HEAPW+off)⟩
def word (level off : Nat) : E := .ld (.bin .add (offsetE level) (cE (HEAPW+off)))
def target (c level : Nat) : Nat := slotV c 6+16*level
def expected (c level : Nat) : PRes := pres
  [(.x6,word level 0),(.x7,word level 8),(.x28,.bin .add (offsetE level) (cE HEAPW)),(.x29,cE (target c level))]
  [mwc (target c level+8) (word level 8),mwc (target c level) (word level 0)]
  [.valid (address level 8) 8,.valid (address level 0) 8] (entry c (level+1)) false 12 []
def runPath (c level : Nat) := runA (look c) [entry c (level+1)] (entry c level) []
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x7eb7,0xd0e8e93,0xeb023,0xeb423,0x891f506f]
def words1 : List (BitVec 32) := bv_list% 32 [0xda4f606f]
def words2 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x270e8e93,0xeb023,0xeb423,0xb0cf706f]
def words3 : List (BitVec 32) := bv_list% 32 [0x824f806f]
def words4 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x410e8e93,0xeb023,0xeb423,0xd89f806f]
def words5 : List (BitVec 32) := bv_list% 32 [0xaa1f906f]
def words6 : List (BitVec 32) := bv_list% 32 [0x7eb7,0x5b0e8e93,0xeb023,0xeb423,0x809fa06f]
def words7 : List (BitVec 32) := bv_list% 32 [0xd1cfb06f]
def words8 : List (BitVec 32) := bv_list% 32 [0xa5cfc06f]
def entry (c : Nat) : Nat := [22950, 23176, 23374, 23600, 23798, 24024, 24222, 24448, 24660].getD c 0
def nextPc (c : Nat) : Nat := [12238, 13297, 14357, 15417, 16476, 17536, 18596, 19655, 20715].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def first (c : Nat) : Bool := decide (c<8 ∧ c%2=0)
def look (c n : Nat) : Option (BitVec 32) := if entry c≤n then (words c)[n-entry c]? else none
def target (c : Nat) : Nat := slotP c 6
def expected (c : Nat) : PRes := pres (if first c then [(.x29,cE (target c))] else [])
  (if first c then [mwc (target c+8) (cE 0),mwc (target c) (cE 0)] else []) [] (nextPc c) false (if first c then 5 else 1) []
def runEnd (c : Nat) := run (look c) [nextPc c] (entry c) []
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def words0 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0xe3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0xe3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xb11f406f]
def words1 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0xe3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0x885f506f]
def words2 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x8e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd9cf606f]
def words3 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x8e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x8e3c83,0x25cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xb04f706f]
def words4 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x10e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0x818f806f]
def words5 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x10e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd81f806f]
def words6 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0xc5c13,0x7fc7c13,0x20e37,0x160e0e13,0x10e3c83,0x25cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xa99f906f]
def words7 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0x6c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x18e3c83,0xdcdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xffcfa06f]
def words8 : List (BitVec 32) := bv_list% 32 [0x20e37,0x160e0e13,0x18e3c03,0x25c5c13,0x7fc7c13,0x20e37,0x160e0e13,0x18e3c83,0x19cdc93,0x3ffcfc93,0xfefe37,0xe0e13,0x2c9313,0x6e0e33,0xd14fb06f]
def entry (c : Nat) : Nat := [22765, 22955, 23177, 23379, 23601, 23803, 24025, 24227, 24449].getD c 0
def hookWord (c : Nat) : BitVec 32 := [0x4ec0b06f,0x7740a06f,0x2610906f,0x4f90806f,0x7e10706f,0x27c0706f,0x5640606f,0x7fc0506f,0x2e90406f].getD c 0
def words (c : Nat) : List (BitVec 32) := [words0,words1,words2,words3,words4,words5,words6,words7,words8].getD c []
def rawBit (c : Nat) : Nat := [0, 6, 64, 70, 128, 134, 192, 198, 229].getD c 0
def rankBit (c : Nat) : Nat := [13, 77, 89, 101, 141, 153, 165, 205, 217].getD c 0
def look (c n : Nat) : Option (BitVec 32) := if n=cbase c then some (hookWord c) else if entry c ≤ n then (words c)[n-entry c]? else none
def fieldE (bit width : Nat) : E := .bin .and (.bin .srl (ldc (NBUF+8*(bit/64))) (cE (bit%64))) (cE (2^width-1))
def expected (c : Nat) : PRes := pres [(.x6,.bin .sll (fieldE (rankBit c) 10) (cE 2)),
  (.x24,fieldE (rawBit c) 7),(.x25,fieldE (rankBit c) 10),
  (.x28,.bin .add (.bin .sll (fieldE (rankBit c) 10) (cE 2)) (cE TBL))] [] [] (lwuI c) false ((words c).length+1) []
def runField (c : Nat) : Option PRes := run (look c) [lwuI c] (cbase c) []
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def base (expand : Bool) : Nat := if expand then 45056 else 22600
def signWords : List (BitVec 32) := bv_list% 32 [0x993,0x293,0x200337,0x30313,0x2869f063,0x20e37,0x120e0e13,0xe3823,0x13e3c23,0x20537,0x12050513,0x4000593,0x20637,0x16060613,0x73,0x20e37,0x160e0e13,0x18e3303,0x3235313,0x31700393,0x22737c63,0xa13,0x208b7,0x16088893,0xfebab7,0xa8a93,0x8bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x206cf863,0x19a8e33,0xe4303,0x6a0a33,0x8bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x88bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x1c6cfc63,0x19a8e33,0xe4303,0x6a0a33,0x8bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x88bc83,0x19cdc93,0x3ffcfc93,0x23300313,0x1a6cf063,0x19a8e33,0xe4303,0x6a0a33,0x88bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x88bc83,0x25cdc93,0x3ffcfc93,0x23300313,0x166cf463,0x19a8e33,0xe4303,0x6a0a33,0x88bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x108bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x126cf863,0x19a8e33,0xe4303,0x6a0a33,0x108bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x108bc83,0x19cdc93,0x3ffcfc93,0x23300313,0xe6cfc63,0x19a8e33,0xe4303,0x6a0a33,0x108bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x108bc83,0x25cdc93,0x3ffcfc93,0x23300313,0xc6cf063,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0xc5c13,0x1fc7c13,0x18a8e33,0x400e4303,0x6a0a33,0x188bc83,0xdcdc93,0x3ffcfc93,0x23300313,0x86cf463,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0x7c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x188bc83,0x19cdc93,0x3ffcfc93,0x23300313,0x46cf863,0x19a8e33,0xe4303,0x6a0a33,0x188bc03,0x26c5c13,0x1fc7c13,0x18a8e33,0x420e4303,0x6a0a33,0x30a00313,0x26a7263,0x20e37,0x160e0e13,0xe3b03,0x21b5b13,0x20e37,0x550e0e13,0x16e3023,0xaf9f406f,0x198993,0xd7dff06f]
def expandWords : List (BitVec 32) := bv_list% 32 [0x993,0x293,0x200337,0x30313,0x2a69f263,0x20e37,0x120e0e13,0xe3823,0x13e3c23,0x20537,0x12050513,0x4000593,0x20637,0x16060613,0x73,0x208b7,0x16088893,0x188b303,0x3235313,0x31700393,0x24737e63,0xff9a37,0xb90a0a13,0xa93,0x8bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x226c7e63,0x18a0333,0x34303,0x6a8ab3,0x8bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x1e6c7e63,0x18a0333,0x34303,0x6a8ab3,0x8bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0x19c5c13,0x3ffc7c13,0x23300313,0x1a6c7e63,0x18a0333,0x34303,0x6a8ab3,0x88bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x88bc03,0x25c5c13,0x3ffc7c13,0x23300313,0x166c7e63,0x18a0333,0x34303,0x6a8ab3,0x88bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x126c7e63,0x18a0333,0x34303,0x6a8ab3,0x108bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0x19c5c13,0x3ffc7c13,0x23300313,0xe6c7e63,0x18a0333,0x34303,0x6a8ab3,0x108bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x108bc03,0x25c5c13,0x3ffc7c13,0x23300313,0xa6c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0xc5c13,0x1fc7c13,0xff9337,0x19030313,0x1830333,0x34303,0x6a8ab3,0x188bc03,0xdc5c13,0x3ffc7c13,0x23300313,0x66c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0x7c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x188bc03,0x19c5c13,0x3ffc7c13,0x23300313,0x26c7e63,0x18a0333,0x34303,0x6a8ab3,0x188bc03,0x26c5c13,0x1fc7c13,0xff9337,0x1b030313,0x1830333,0x34303,0x6a8ab3,0x30a00313,0x6af463,0x180006f,0x198993,0xd59ff06f]
def words (expand : Bool) : List (BitVec 32) := if expand then expandWords else signWords
 def look (expand : Bool) (n : Nat) : Option (BitVec 32) := if base expand ≤ n then (words expand)[n-base expand]? else none
 def trial (expand : Bool) : Nat := base expand+2
 def next (expand : Bool) : Nat := if expand then 45227 else 22762
 def fail (expand : Bool) : Nat := next expand+2
 def firstField (expand : Bool) : Nat := if expand then 45080 else 22626
 def field (expand : Bool) (k : Nat) : Nat := firstField expand+(if expand then 16 else 14)*k
 def rankLoad (expand : Bool) (k : Nat) : Nat := field expand k+6
 def corrLoad (expand : Bool) (k : Nat) : Nat := field expand k+(if expand then 14 else 12)
 def cap (expand : Bool) : Nat := field expand 9
 def accepted (expand : Bool) : Nat := cap expand+2
 def sumReg (expand : Bool) : Reg := if expand then .x21 else .x20
 def tableReg (expand : Bool) : Reg := if expand then .x20 else .x21
 def rankReg (expand : Bool) : Reg := if expand then .x24 else .x25
 def addrReg (expand : Bool) : Reg := if expand then .x6 else .x28
 def tableBase (expand : Bool) : Nat := if expand then 0xff8b90 else 0xfeb000
 def correctionOffset (expand : Bool) (k : Nat) : Nat := (if expand then 1536 else 1024)+(if SharedLeaf.first k then 0 else 32)
 def fieldAddr (bit : Nat) : Addr := ⟨some (.reg .x17),BitVec.ofNat 64 (8*(bit/64))⟩
 def fieldE (bit width : Nat) : E := .bin .and (.bin .srl (.ld (fieldAddr bit).toE) (cE (bit%64))) (cE (2^width-1))
 def rankE (k : Nat) : E := fieldE (SharedField.rankBit k) 10
 def costBit (k : Nat) : Nat := SharedField.rawBit k+(if SharedLeaf.first k then 0 else 1)
 def costE (k : Nat) : E := fieldE (costBit k) 5
 def gateE : E := .bin .srl (ldc (NBUF+24)) (cE 50)
 def expectedHead (expand reject : Bool) : PRes := pres [(.x6,cE (2^21))] [] []
   (if reject then fail expand else trial expand+3) false 3 [⟨.geu,.reg .x19,cE (2^21),reject⟩]
 def expectedTrial (expand : Bool) : PRes := pres [(.x28,cE DIG),(.x10,cE DIG),(.x11,cE 64),(.x12,cE NBUF)]
   [mwc (DIG+24) (.reg .x19),mwc (DIG+16) (cE 0)] [] (base expand+14) true 9 []
 def expectedGate (expand reject : Bool) : PRes := pres [((if expand then .x17 else .x28),cE NBUF),(.x6,gateE),(.x7,cE 791)] [] []
   (if reject then next expand else base expand+21) false 6 [⟨.geu,gateE,cE 791,reject⟩]
 def expectedInit (expand : Bool) : PRes := pres (if expand then [(.x20,cE (tableBase expand)),(.x21,cE 0)]
   else [(.x20,cE 0),(.x17,cE NBUF),(.x21,cE (tableBase expand))]) [] [] (firstField expand) false (if expand then 3 else 5) []
 def expectedRank (expand : Bool) (k : Nat) (reject : Bool) : PRes := pres [(rankReg expand,rankE k),(.x6,cE 563)] [] [.valid (fieldAddr (SharedField.rankBit k)) 8]
   (if reject then next expand else field expand k+5) false 5 [⟨.geu,rankE k,cE 563,reject⟩]
 def expectedRankAddr (expand : Bool) (k : Nat) : PRes := pres [(addrReg expand,.bin .add (.reg (tableReg expand)) (.reg (rankReg expand)))] [] [] (rankLoad expand k) false 1 []
 def expectedCorrPrep (expand : Bool) (k : Nat) : PRes := pres
   [(sumReg expand,.bin .add (.reg (sumReg expand)) (.reg .x6)),(.x24,costE k),
     (addrReg expand,if expand then .bin .add (costE k) (cE (tableBase expand+correctionOffset expand k))
       else .bin .add (.reg (tableReg expand)) (costE k))] [] [.valid (fieldAddr (costBit k)) 8] (corrLoad expand k) false (if expand then 7 else 5) []
 def expectedSum (expand : Bool) (k : Nat) : PRes := pres [(sumReg expand,.bin .add (.reg (sumReg expand)) (.reg .x6))] [] [] (field expand (k+1)) false 1 []
 def expectedCap (expand reject : Bool) : PRes := pres [(.x6,cE 778)] [] [] (if reject then next expand else accepted expand) false 2
   [⟨.geu,.reg (sumReg expand),cE 778,reject⟩]
 def expectedNext (expand : Bool) : PRes := pres [(.x19,.bin .add (.reg .x19) (cE 1))] [] [] (trial expand) false 2 []
 def rankLbuWord (expand : Bool) : BitVec 32 := if expand then 0x00034303 else 0x000e4303
 def corrLbuWord (expand : Bool) (k : Nat) : BitVec 32 := if expand then 0x00034303 else if SharedLeaf.first k then 0x400e4303 else 0x420e4303
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem codeAt_get_word {im : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : b<2^30) (hc : CodeAt im (pcOf b) code) {i : Nat} {w : BitVec 32}
    (hi : code[i]?=some w) : im.code[b+i]?=some w := by
  have hpc : (pcOf b).toNat=4096+4*b := by
    simp only [pcOf,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rest,hrest⟩ := hc.2.2.2
  rw [hpc,show (4096+4*b-4096)/4=b by omega] at hrest
  have hlen:= (List.getElem?_eq_some_iff.mp hi).1
  have hh : (code++rest)[i]?=some w := by rwa [List.getElem?_append_left hlen]
  rw [hrest,List.getElem?_drop] at hh
  simpa [Nat.add_comm] using hh

theorem look_of_code {im : Image} (m : Bool)
    (hc : CodeAt im (pcOf (base m)) (words m)) : LookOK im (look m) := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hn
    have hb : base m<2^30 := by cases m <;> decide
    have hh:=codeAt_get_word hb hc hw
    simpa only [Nat.add_sub_cancel' hn] using hh
  · cases hw
end ClaudeWCT.W9.Machine.Sign.SharedDigest
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckAPart0 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_0 : okF 0 = true := by decide +kernel
private theorem component_okC_0 : okC 0 = true := by decide +kernel
private theorem component_okQ_0 : okQ 0 = true := by decide +kernel
private theorem component_okS_0 : okS 0 = true := by decide +kernel
private theorem component_okChk_0 : okChk 0 = true := by decide +kernel
private theorem component_okStp_0 : okStp 0 = true := by decide +kernel
private theorem component_okLc_0 : okLc 0 = true := by decide +kernel
private theorem component_okTail_0 : okTail 0 = true := by decide +kernel
theorem okCoord_0 : okCoord 0 = true := by
  simp only [okCoord, component_okF_0, component_okC_0, component_okQ_0, component_okS_0, component_okChk_0, component_okStp_0, component_okLc_0, component_okTail_0, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_0 : SigGolfCandidate.T3M.Verify.optBeq (runZ 0) (expZ 0) = true := by decide +kernel
private theorem component_okC_0 : okC 0 = true := by decide +kernel
private theorem component_okQ_0 : okQ 0 = true := by decide +kernel
private theorem component_okS_0 : okS 0 = true := by decide +kernel
private theorem component_okChk_0 : okChk 0 = true := by decide +kernel
private theorem component_okStp_0 : okStp 0 = true := by decide +kernel
private theorem component_okLc_0 : okLc 0 = true := by decide +kernel
theorem okCoord_0 : okCoord 0 = true := by
  simp only [okCoord, component_z_0, component_okC_0, component_okQ_0, component_okS_0, component_okChk_0, component_okStp_0, component_okLc_0, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckAPart1 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_1 : okF 1 = true := by decide +kernel
private theorem component_okC_1 : okC 1 = true := by decide +kernel
private theorem component_okQ_1 : okQ 1 = true := by decide +kernel
private theorem component_okS_1 : okS 1 = true := by decide +kernel
private theorem component_okChk_1 : okChk 1 = true := by decide +kernel
private theorem component_okStp_1 : okStp 1 = true := by decide +kernel
private theorem component_okLc_1 : okLc 1 = true := by decide +kernel
private theorem component_okTail_1 : okTail 1 = true := by decide +kernel
theorem okCoord_1 : okCoord 1 = true := by
  simp only [okCoord, component_okF_1, component_okC_1, component_okQ_1, component_okS_1, component_okChk_1, component_okStp_1, component_okLc_1, component_okTail_1, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_1 : SigGolfCandidate.T3M.Verify.optBeq (runZ 1) (expZ 1) = true := by decide +kernel
private theorem component_okC_1 : okC 1 = true := by decide +kernel
private theorem component_okQ_1 : okQ 1 = true := by decide +kernel
private theorem component_okS_1 : okS 1 = true := by decide +kernel
private theorem component_okChk_1 : okChk 1 = true := by decide +kernel
private theorem component_okStp_1 : okStp 1 = true := by decide +kernel
private theorem component_okLc_1 : okLc 1 = true := by decide +kernel
theorem okCoord_1 : okCoord 1 = true := by
  simp only [okCoord, component_z_1, component_okC_1, component_okQ_1, component_okS_1, component_okChk_1, component_okStp_1, component_okLc_1, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckAPart2 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_2 : okF 2 = true := by decide +kernel
private theorem component_okC_2 : okC 2 = true := by decide +kernel
private theorem component_okQ_2 : okQ 2 = true := by decide +kernel
private theorem component_okS_2 : okS 2 = true := by decide +kernel
private theorem component_okChk_2 : okChk 2 = true := by decide +kernel
private theorem component_okStp_2 : okStp 2 = true := by decide +kernel
private theorem component_okLc_2 : okLc 2 = true := by decide +kernel
private theorem component_okTail_2 : okTail 2 = true := by decide +kernel
theorem okCoord_2 : okCoord 2 = true := by
  simp only [okCoord, component_okF_2, component_okC_2, component_okQ_2, component_okS_2, component_okChk_2, component_okStp_2, component_okLc_2, component_okTail_2, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_2 : SigGolfCandidate.T3M.Verify.optBeq (runZ 2) (expZ 2) = true := by decide +kernel
private theorem component_okC_2 : okC 2 = true := by decide +kernel
private theorem component_okQ_2 : okQ 2 = true := by decide +kernel
private theorem component_okS_2 : okS 2 = true := by decide +kernel
private theorem component_okChk_2 : okChk 2 = true := by decide +kernel
private theorem component_okStp_2 : okStp 2 = true := by decide +kernel
private theorem component_okLc_2 : okLc 2 = true := by decide +kernel
theorem okCoord_2 : okCoord 2 = true := by
  simp only [okCoord, component_z_2, component_okC_2, component_okQ_2, component_okS_2, component_okChk_2, component_okStp_2, component_okLc_2, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckAPart3 ====
section

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
theorem okGlobal_ok : okGlobal = true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem okHorn_ok : okHorn = true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckA ====
section

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckBPart0 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_3 : okF 3 = true := by decide +kernel
private theorem component_okC_3 : okC 3 = true := by decide +kernel
private theorem component_okQ_3 : okQ 3 = true := by decide +kernel
private theorem component_okS_3 : okS 3 = true := by decide +kernel
private theorem component_okChk_3 : okChk 3 = true := by decide +kernel
private theorem component_okStp_3 : okStp 3 = true := by decide +kernel
private theorem component_okLc_3 : okLc 3 = true := by decide +kernel
private theorem component_okTail_3 : okTail 3 = true := by decide +kernel
theorem okCoord_3 : okCoord 3 = true := by
  simp only [okCoord, component_okF_3, component_okC_3, component_okQ_3, component_okS_3, component_okChk_3, component_okStp_3, component_okLc_3, component_okTail_3, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_3 : SigGolfCandidate.T3M.Verify.optBeq (runZ 3) (expZ 3) = true := by decide +kernel
private theorem component_okC_3 : okC 3 = true := by decide +kernel
private theorem component_okQ_3 : okQ 3 = true := by decide +kernel
private theorem component_okS_3 : okS 3 = true := by decide +kernel
private theorem component_okChk_3 : okChk 3 = true := by decide +kernel
private theorem component_okStp_3 : okStp 3 = true := by decide +kernel
private theorem component_okLc_3 : okLc 3 = true := by decide +kernel
theorem okCoord_3 : okCoord 3 = true := by
  simp only [okCoord, component_z_3, component_okC_3, component_okQ_3, component_okS_3, component_okChk_3, component_okStp_3, component_okLc_3, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckBPart1 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_4 : okF 4 = true := by decide +kernel
private theorem component_okC_4 : okC 4 = true := by decide +kernel
private theorem component_okQ_4 : okQ 4 = true := by decide +kernel
private theorem component_okS_4 : okS 4 = true := by decide +kernel
private theorem component_okChk_4 : okChk 4 = true := by decide +kernel
private theorem component_okStp_4 : okStp 4 = true := by decide +kernel
private theorem component_okLc_4 : okLc 4 = true := by decide +kernel
private theorem component_okTail_4 : okTail 4 = true := by decide +kernel
theorem okCoord_4 : okCoord 4 = true := by
  simp only [okCoord, component_okF_4, component_okC_4, component_okQ_4, component_okS_4, component_okChk_4, component_okStp_4, component_okLc_4, component_okTail_4, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_4 : SigGolfCandidate.T3M.Verify.optBeq (runZ 4) (expZ 4) = true := by decide +kernel
private theorem component_okC_4 : okC 4 = true := by decide +kernel
private theorem component_okQ_4 : okQ 4 = true := by decide +kernel
private theorem component_okS_4 : okS 4 = true := by decide +kernel
private theorem component_okChk_4 : okChk 4 = true := by decide +kernel
private theorem component_okStp_4 : okStp 4 = true := by decide +kernel
private theorem component_okLc_4 : okLc 4 = true := by decide +kernel
theorem okCoord_4 : okCoord 4 = true := by
  simp only [okCoord, component_z_4, component_okC_4, component_okQ_4, component_okS_4, component_okChk_4, component_okStp_4, component_okLc_4, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckBPart2 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_5 : okF 5 = true := by decide +kernel
private theorem component_okC_5 : okC 5 = true := by decide +kernel
private theorem component_okQ_5 : okQ 5 = true := by decide +kernel
private theorem component_okS_5 : okS 5 = true := by decide +kernel
private theorem component_okChk_5 : okChk 5 = true := by decide +kernel
private theorem component_okStp_5 : okStp 5 = true := by decide +kernel
private theorem component_okLc_5 : okLc 5 = true := by decide +kernel
private theorem component_okTail_5 : okTail 5 = true := by decide +kernel
theorem okCoord_5 : okCoord 5 = true := by
  simp only [okCoord, component_okF_5, component_okC_5, component_okQ_5, component_okS_5, component_okChk_5, component_okStp_5, component_okLc_5, component_okTail_5, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_5 : SigGolfCandidate.T3M.Verify.optBeq (runZ 5) (expZ 5) = true := by decide +kernel
private theorem component_okC_5 : okC 5 = true := by decide +kernel
private theorem component_okQ_5 : okQ 5 = true := by decide +kernel
private theorem component_okS_5 : okS 5 = true := by decide +kernel
private theorem component_okChk_5 : okChk 5 = true := by decide +kernel
private theorem component_okStp_5 : okStp 5 = true := by decide +kernel
private theorem component_okLc_5 : okLc 5 = true := by decide +kernel
theorem okCoord_5 : okCoord 5 = true := by
  simp only [okCoord, component_z_5, component_okC_5, component_okQ_5, component_okS_5, component_okChk_5, component_okStp_5, component_okLc_5, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckB ====
section

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckCPart0 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_6 : okF 6 = true := by decide +kernel
private theorem component_okC_6 : okC 6 = true := by decide +kernel
private theorem component_okQ_6 : okQ 6 = true := by decide +kernel
private theorem component_okS_6 : okS 6 = true := by decide +kernel
private theorem component_okChk_6 : okChk 6 = true := by decide +kernel
private theorem component_okStp_6 : okStp 6 = true := by decide +kernel
private theorem component_okLc_6 : okLc 6 = true := by decide +kernel
private theorem component_okTail_6 : okTail 6 = true := by decide +kernel
theorem okCoord_6 : okCoord 6 = true := by
  simp only [okCoord, component_okF_6, component_okC_6, component_okQ_6, component_okS_6, component_okChk_6, component_okStp_6, component_okLc_6, component_okTail_6, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_6 : SigGolfCandidate.T3M.Verify.optBeq (runZ 6) (expZ 6) = true := by decide +kernel
private theorem component_okC_6 : okC 6 = true := by decide +kernel
private theorem component_okQ_6 : okQ 6 = true := by decide +kernel
private theorem component_okS_6 : okS 6 = true := by decide +kernel
private theorem component_okChk_6 : okChk 6 = true := by decide +kernel
private theorem component_okStp_6 : okStp 6 = true := by decide +kernel
private theorem component_okLc_6 : okLc 6 = true := by decide +kernel
theorem okCoord_6 : okCoord 6 = true := by
  simp only [okCoord, component_z_6, component_okC_6, component_okQ_6, component_okS_6, component_okChk_6, component_okStp_6, component_okLc_6, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckCPart1 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_7 : okF 7 = true := by decide +kernel
private theorem component_okC_7 : okC 7 = true := by decide +kernel
private theorem component_okQ_7 : okQ 7 = true := by decide +kernel
private theorem component_okS_7 : okS 7 = true := by decide +kernel
private theorem component_okChk_7 : okChk 7 = true := by decide +kernel
private theorem component_okStp_7 : okStp 7 = true := by decide +kernel
private theorem component_okLc_7 : okLc 7 = true := by decide +kernel
private theorem component_okTail_7 : okTail 7 = true := by decide +kernel
theorem okCoord_7 : okCoord 7 = true := by
  simp only [okCoord, component_okF_7, component_okC_7, component_okQ_7, component_okS_7, component_okChk_7, component_okStp_7, component_okLc_7, component_okTail_7, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_7 : SigGolfCandidate.T3M.Verify.optBeq (runZ 7) (expZ 7) = true := by decide +kernel
private theorem component_okC_7 : okC 7 = true := by decide +kernel
private theorem component_okQ_7 : okQ 7 = true := by decide +kernel
private theorem component_okS_7 : okS 7 = true := by decide +kernel
private theorem component_okChk_7 : okChk 7 = true := by decide +kernel
private theorem component_okStp_7 : okStp 7 = true := by decide +kernel
private theorem component_okLc_7 : okLc 7 = true := by decide +kernel
theorem okCoord_7 : okCoord 7 = true := by
  simp only [okCoord, component_z_7, component_okC_7, component_okQ_7, component_okS_7, component_okChk_7, component_okStp_7, component_okLc_7, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckCPart2 ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace ClaudeWCT.W9.Machine.Sign
private theorem component_okF_8 : okF 8 = true := by decide +kernel
private theorem component_okC_8 : okC 8 = true := by decide +kernel
private theorem component_okQ_8 : okQ 8 = true := by decide +kernel
private theorem component_okS_8 : okS 8 = true := by decide +kernel
private theorem component_okChk_8 : okChk 8 = true := by decide +kernel
private theorem component_okStp_8 : okStp 8 = true := by decide +kernel
private theorem component_okLc_8 : okLc 8 = true := by decide +kernel
private theorem component_okTail_8 : okTail 8 = true := by decide +kernel
theorem okCoord_8 : okCoord 8 = true := by
  simp only [okCoord, component_okF_8, component_okC_8, component_okQ_8, component_okS_8, component_okChk_8, component_okStp_8, component_okLc_8, component_okTail_8, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
private theorem component_z_8 : SigGolfCandidate.T3M.Verify.optBeq (runZ 8) (expZ 8) = true := by decide +kernel
private theorem component_okC_8 : okC 8 = true := by decide +kernel
private theorem component_okQ_8 : okQ 8 = true := by decide +kernel
private theorem component_okS_8 : okS 8 = true := by decide +kernel
private theorem component_okChk_8 : okChk 8 = true := by decide +kernel
private theorem component_okStp_8 : okStp 8 = true := by decide +kernel
private theorem component_okLc_8 : okLc 8 = true := by decide +kernel
theorem okCoord_8 : okCoord 8 = true := by
  simp only [okCoord, component_z_8, component_okC_8, component_okQ_8, component_okS_8, component_okChk_8, component_okStp_8, component_okLc_8, Bool.true_and]
end ClaudeWCT.W9.Machine.Sign.SharedReuse
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_FtsCheckC ====
section

namespace ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Sign
end
