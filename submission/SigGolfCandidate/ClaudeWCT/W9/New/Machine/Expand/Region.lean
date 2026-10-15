import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ChainCode
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes chainBytes_window)
set_option linter.unusedSimpArgs false
theorem wordsOf_getD (L : List UInt8) (m : Nat) (hL : L.length = 8 * m) (i : Nat) (hi : i < m) :
    (wordsOf L).getD i 0 = BitVec.ofNat 64 (readLE (window L (8 * i) 8)) := by
  rw [wordsOf_eq_range m L hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hw : readLE (window L (8 * i) 8) < 2 ^ 64 := by
    have := readLE_lt (window L (8 * i) 8)
    have hl : (window L (8 * i) 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L (8 * i) 8) < 256 ^ (window L (8 * i) 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hw, show 2 ^ (64 * i) = 256 ^ (8 * i) by rw [pow_mul, pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop, show 2 ^ 64 = 256 ^ 8 by norm_num, SigGolfCandidate.T3M.readLE_take]
  rfl
theorem window_split16 (L : List UInt8) (o : Nat) (h : o + 16 ≤ L.length) :
    readLE (window L o 16) = readLE (window L o 8) + 2 ^ 64 * readLE (window L (o + 8) 8) := by
  unfold window
  rw [show (L.drop o).take 16 = (L.drop o).take 8 ++ (L.drop (o + 8)).take 8 by
      rw [show 16 = 8 + 8 from rfl, List.take_add, List.drop_drop, Nat.add_comm]]
  rw [SigGolfCandidate.T3M.readLE_append, List.length_take, Nat.min_eq_left (by simp; omega)]
  norm_num
theorem words_of_window16 (L : List UInt8) (hL : L.length = 1024) (o : Nat) (ho : o % 8 = 0) (ho' : o + 16 ≤ 1024)
    (d : Digest) (hd : window L o 16 = bytesLE 16 d) :
    (wordsOf L).getD (o / 8) 0 = d.extractLsb' 0 64 ∧ (wordsOf L).getD (o / 8 + 1) 0 = d.extractLsb' 64 64 := by
  have h1 := wordsOf_getD L 128 (by omega) (o / 8) (by omega)
  have h2 := wordsOf_getD L 128 (by omega) (o / 8 + 1) (by omega)
  rw [show 8 * (o / 8) = o by omega] at h1
  rw [show 8 * (o / 8 + 1) = o + 8 by omega] at h2
  have hs := window_split16 L o (by omega)
  rw [hd, SigGolfCandidate.T3M.readLE_bytesLE] at hs
  have hlo : readLE (window L o 8) < 2 ^ 64 := by
    have := readLE_lt (window L o 8)
    have hl : (window L o 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L o 8) < 256 ^ (window L o 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    have := d.isLt
    omega
section windows
variable (c : Nat) (op : WCT9.Opening)
theorem win_chainVal (t : Fin 6) : window (regionBytesV5 c op) (offC t.val + 48) 16 = bytesLE 16 (op.values t) := by
  rcases t with ⟨_ | i, ht⟩
  · rw [show offC 0 + 48 = 816 by rfl, region_leafV5 _ _ _ _ le_rfl (by omega), Nat.sub_self, leafZ_window_zero]
    rfl
  · have hi : i < 5 := by omega
    rw [show offC (i + 1) + 48 = 448 + (64 * (4 - i) + 48) by unfold offC; omega,
      region_chainV5 _ _ _ _ (by omega) (by omega),
      show 448 + (64 * (4 - i) + 48) - 448 = 64 * (4 - (⟨i, hi⟩ : Fin 5).val) + 48 by simp,
      chainBytes_window _ _ _ (by omega), window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
    rfl
theorem win_leafSlot (t : Fin 6) : window (regionBytesV5 c op) (slotC t.val) 16 = bytesLE 16 (op.values t) := by
  rcases t with ⟨_ | i, ht⟩
  · exact win_chainVal c op ⟨0, ht⟩
  · have hi : i < 5 := by omega
    rw [show slotC (i + 1) = 816 + (48 + 16 * i) by unfold slotC; simp; omega,
      region_leafV5 _ _ _ _ (by omega) (by omega),
      show 816 + (48 + 16 * i) - 816 = 48 + 16 * (⟨i, hi⟩ : Fin 5).val by simp, leafZ_window_succ]
    rfl
/-- The leaf pad slot (848) of a placed region is zero. -/
theorem win_leafPad : window (regionBytesV5 c op) 848 16 = zeros 16 := by
  rw [region_leafV5 _ _ _ _ (by omega) (by omega), show 848 - 816 = 32 by rfl, leafZ_window_pad]
theorem win_chainPad (t : Nat) (ht : t < 6) (o : Nat) (ho : o = 0 ∨ o = 16 ∨ o = 32) :
    window (regionBytesV5 c op) (offC t + o) 16 = zeros 16 := by
  rcases t with _ | i
  · rw [show offC 0 + o = 768 + o by rfl, region_prefixV5 _ _ _ _ (by omega) (by omega)]
  · have hi : i < 5 := by omega
    rw [show offC (i + 1) + o = 448 + (64 * (4 - i) + o) by unfold offC; omega,
      region_chainV5 _ _ _ _ (by omega) (by omega),
      show 448 + (64 * (4 - i) + o) - 448 = 64 * (4 - (⟨i, hi⟩ : Fin 5).val) + o by simp,
      chainBytes_window _ _ _ (by omega), window_append_left _ _ _ _ (by simp [zeros]; omega),
      window_zeros _ _ _ (by omega)]
theorem win_sib (l : Fin 7) :
    window (regionBytesV5 c op) (64 * (6 - l.val) + 48 * (1 - c / 2 ^ l.val % 2)) 16 = bytesLE 16 (op.path l) := by
  have hl := l.isLt
  have hb : c / 2 ^ l.val % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [region_merkleV5 _ _ _ _ (by omega), merkleBytesV5_window _ _ _ _ (by omega)]
  split
  · rename_i h; rw [h, show 48 * (1 - 1) = 0 by rfl, window_append_left _ _ _ _ (by simp [bytesLE_length]),
      window_full _ _ (bytesLE_length _ _)]
  · rename_i h
    rw [show 48 * (1 - c / 2 ^ l.val % 2) = 48 by omega, window_append_right _ _ _ _ (by simp [zeros]),
      show 48 - (zeros 48).length = 0 by simp [zeros], window_full _ _ (bytesLE_length _ _)]
theorem win_mpad (l : Fin 7) : window (regionBytesV5 c op) (64 * (6 - l.val) + 32) 16 = zeros 16 := by
  have hl := l.isLt
  rw [region_merkleV5 _ _ _ _ (by omega), merkleBytesV5_window _ _ _ _ (by omega)]
  split
  · rw [window_append_right _ _ _ _ (by simp [bytesLE_length]), window_zeros _ _ _ (by simp [bytesLE_length])]
  · rw [window_append_left _ _ _ _ (by simp [zeros, bytesLE_length]), window_zeros _ _ _ (by omega)]
end windows
theorem zeros16 : zeros 16 = bytesLE 16 (0 : Digest) := (VLib.bytesLE16_zero).symm
theorem placed_digAt {N : HashOutput} {sig : WCT9.Signature} {s : MachineState} (hp : Placed N sig s) (k : Nat)
    (hk : k < 9) (o : Nat) (ho : o % 8 = 0) (ho' : o + 16 ≤ 1024) (d : Digest)
    (hd : window (regionBytesV5 (WCT9.child N ⟨k, hk⟩).val (sig.openings ⟨k, hk⟩)) o 16 = bytesLE 16 d) :
    DigAt s (regBase k + o) d := by
  have hw := words_of_window16 _ (regionBytesV5_length _ _) o ho ho' d hd
  have hk' : (⟨k % 9, Nat.mod_lt _ (by decide)⟩ : WCT9.Coord) = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
  constructor
  · rw [show regBase k + o = regBase k + 8 * (o / 8) by omega, hp k (o / 8) hk (by omega), regionWord, hk']
    exact hw.1
  · rw [show regBase k + o + 8 = regBase k + 8 * (o / 8 + 1) by omega, hp k (o / 8 + 1) hk (by omega), regionWord, hk']
    exact hw.2
end ClaudeWCT.W9.Machine.Expand
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros window_flatMap_const)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ### C1 (FTS half-swap): the first-pass region layout

The first pass places the siblings of levels 0..4 into the packed plan windows (`Merkle.sibO l j`, from the plan
table at `PLAN`); levels 5 and 6 and everything from byte 448 on are as in `regionBytesV5`. -/
/-- The level whose sibling the first pass places on the 16-byte cell `m` of child `j`'s region, if any. -/
def cellLev (j m : Nat) : Option Nat := (List.range 7).find? (fun l => Merkle.sibO l j == 16 * m)
def pathD (op : WCT9.Opening) (l : Nat) : Digest := if h : l < 7 then op.path ⟨l, h⟩ else 0
def cellC1 (j : Nat) (op : WCT9.Opening) (m : Nat) : Digest :=
  match cellLev j m with
  | some l => pathD op l
  | none => 0
def merkleBytesC1 (j : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.range 28).flatMap fun m => bytesLE 16 (cellC1 j op m)
/-- C1: the first-pass scratch region of child `j`. -/
def regionBytesC1 (j : Nat) (op : WCT9.Opening) : List UInt8 := merkleBytesC1 j op ++ (regionBytesV5 j op).drop 448
theorem merkleBytesC1_length (j : Nat) (op : WCT9.Opening) : (merkleBytesC1 j op).length = 448 := by
  unfold merkleBytesC1
  rw [List.length_flatMap]
  simp only [bytesLE_length, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
theorem regionBytesC1_length (j : Nat) (op : WCT9.Opening) : (regionBytesC1 j op).length = 1024 := by
  simp only [regionBytesC1, List.length_append, merkleBytesC1_length, List.length_drop, regionBytesV5_length]
theorem win1_cell (j : Nat) (op : WCT9.Opening) (m : Nat) (hm : m < 28) :
    window (regionBytesC1 j op) (16 * m) 16 = bytesLE 16 (cellC1 j op m) := by
  unfold regionBytesC1
  rw [window_append_left _ _ _ _ (by rw [merkleBytesC1_length]; omega), merkleBytesC1,
    show 16 * m = 16 * m + 0 from rfl,
    window_flatMap_const _ _ 16 (fun b => bytesLE_length _ _) m (by simp; omega) 0 16 (by omega),
    window_full _ _ (bytesLE_length _ _)]
  simp [List.getElem_range]
theorem win1_rest (j : Nat) (op : WCT9.Opening) (o n : Nat) (ho : 448 ≤ o) :
    window (regionBytesC1 j op) o n = window (regionBytesV5 j op) o n := by
  unfold regionBytesC1
  rw [window_append_right _ _ _ _ (by rw [merkleBytesC1_length]; omega), merkleBytesC1_length]
  unfold window
  rw [List.drop_drop]
  first
    | rw [show o - 448 + 448 = o by omega]
    | rw [show 448 + (o - 448) = o by omega]
set_option maxRecDepth 100000 in
theorem cellLev_sib_all : ∀ j < 128, ∀ l < 7,
    cellLev j (Merkle.sibO l j / 16) = some l ∧ Merkle.sibO l j % 16 = 0 ∧ Merkle.sibO l j < 448 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem cellLev_pad_all : ∀ j < 128, ∀ l < 5,
    cellLev j (Merkle.padO l j / 16) = none ∧ Merkle.padO l j % 16 = 0 ∧ Merkle.padO l j < 448 := by
  decide +kernel
theorem win1_sib (j : Nat) (hj : j < 128) (op : WCT9.Opening) (l : Fin 7) :
    window (regionBytesC1 j op) (Merkle.sibO l.val j) 16 = bytesLE 16 (op.path l) := by
  obtain ⟨h1, h2, h3⟩ := cellLev_sib_all j hj l.val l.isLt
  rw [show Merkle.sibO l.val j = 16 * (Merkle.sibO l.val j / 16) by omega, win1_cell _ _ _ (by omega)]
  unfold cellC1
  rw [h1]
  simp [pathD, l.isLt]
theorem win1_mpad (j : Nat) (hj : j < 128) (op : WCT9.Opening) (l : Nat) (hl : l < 5) :
    window (regionBytesC1 j op) (Merkle.padO l j) 16 = zeros 16 := by
  obtain ⟨h1, h2, h3⟩ := cellLev_pad_all j hj l hl
  rw [show Merkle.padO l j = 16 * (Merkle.padO l j / 16) by omega, win1_cell _ _ _ (by omega)]
  unfold cellC1
  rw [h1, zeros16]
def regionWord1 (N : HashOutput) (sig : WCT9.Signature) (k i : Nat) : Word :=
  (wordsOf (regionBytesC1 (WCT9.child N ⟨k % 9, Nat.mod_lt _ (by decide)⟩).val
    (sig.openings ⟨k % 9, Nat.mod_lt _ (by decide)⟩))).getD i 0
/-- C1: the first-pass placement (siblings of levels 0..4 in the plan windows). -/
def Placed1 (N : HashOutput) (sig : WCT9.Signature) (s : MachineState) : Prop :=
  ∀ k i, k < 9 → i < 128 → s.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = regionWord1 N sig k i
theorem placed1_digAt {N : HashOutput} {sig : WCT9.Signature} {s : MachineState} (hp : Placed1 N sig s) (k : Nat)
    (hk : k < 9) (o : Nat) (ho : o % 8 = 0) (ho' : o + 16 ≤ 1024) (d : Digest)
    (hd : window (regionBytesC1 (WCT9.child N ⟨k, hk⟩).val (sig.openings ⟨k, hk⟩)) o 16 = bytesLE 16 d) :
    DigAt s (regBase k + o) d := by
  have hw := words_of_window16 _ (regionBytesC1_length _ _) o ho ho' d hd
  have hk' : (⟨k % 9, Nat.mod_lt _ (by decide)⟩ : WCT9.Coord) = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
  constructor
  · rw [show regBase k + o = regBase k + 8 * (o / 8) by omega, hp k (o / 8) hk (by omega), regionWord1, hk']
    exact hw.1
  · rw [show regBase k + o + 8 = regBase k + 8 * (o / 8 + 1) by omega, hp k (o / 8 + 1) hk (by omega), regionWord1,
      hk']
    exact hw.2
end ClaudeWCT.W9.Machine.Expand
end
