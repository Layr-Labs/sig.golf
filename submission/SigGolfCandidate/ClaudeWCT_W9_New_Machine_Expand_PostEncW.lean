import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PostEnc

/-! # The post-pass produces the nonce-free paired witness encoding

Main result `ppMem_witEnc`: if, at the post-pass entry (pc 49400), the memory `M` holds
* (FTS) at `2904 + 8 j` (`j < 958`) the words `j` of `Paired.witEnc output w` (new layout bytes `[0, 7664)`),
* (old) at `2904 + 8 j` (`1012 ≤ j < 2905`, `j ≠ 2789`) the words `j` of the pre-witness-stack encoding
  `OldW.witList output (ClaudeWCT.W9.T3M.Paired.mainWitness w)` (window style, as compaction states them),
* (choice) at `2904 + 8 · 2789 = 25216` that old word with its low byte replaced by `choiceByte w.topHigh`
  (the `end` routine's `sb`),
* (leaf) `leafOf (M 0x20160) ≡ route leaf of digestIndex output (mod 4096)`,
then `ppMem (leafOf (M 0x20160)) M` holds the 2752 words of `Paired.witEnc output w` at `4128 + 8 k` — exactly the
`hbuf` hypothesis of `PadWit.padMem_witEncN` / `pad_hook_witEncN`. -/

set_option autoImplicit false

namespace ClaudeWCT.W9.Machine.Expand.PostEnc
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer route readLE)
open SigGolfCandidate.T3M (window)
open ClaudeWCT.W9.Machine.Expand.PostPass
open ClaudeWCT.W9.T3M (choiceByte)
open SigGolfCandidate.T3M (pcOf RegsExcept)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- Word `j` of the old (pre-witness-stack) encoding, as the compaction leaves it at `2904 + 8 j`. -/
def oldWord (N : HashOutput) (w : WCT9.Witness) (o : Nat) : Word :=
  BitVec.ofNat 64 (readLE (window (OldW.witList N w) o 8))

/-- The post-pass map only depends on the leaf modulo `4096`. -/
theorem ppMem_leaf_congr (l1 l2 : Nat) (h : l1 % 4096 = l2 % 4096) (M : Nat → Word) : ppMem l1 M = ppMem l2 M := by
  rw [ppMem_eq, ppMem_eq, show l1 % 64 = l2 % 64 by omega, show l1 / 64 % 64 = l2 / 64 % 64 by omega]

/-- A word of the new non-paired encoding, window style. -/
theorem witEnc_word (N : HashOutput) (w : WCT9.Witness) (o : Nat) :
    (ClaudeWCT.W9.T3M.witEnc N w).extractLsb' (8 * o) 64 =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) o 8)) := by
  unfold ClaudeWCT.W9.T3M.witEnc
  exact ClaudeWCT.W9.T3M.extract_readLE_lt _ 22012 (ClaudeWCT.W9.T3M.witList_readLE_lt N w) o 8

/-- Paired words at offsets `≥ 7664`: the non-paired encoding of the main witness (choice word aside). -/
theorem paired_word_tail (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (o : Nat)
    (h1 : 7664 ≤ o) (hc : o + 8 ≤ 21104 ∨ 21104 < o) :
    (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (8 * o) 64 =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList output (ClaudeWCT.W9.T3M.Paired.mainWitness w)) o 8)) := by
  rw [ClaudeWCT.W9.T3M.Paired.word_witEnc_tail output w o h1 hc, witEnc_word]

theorem paired_word_choice (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (8 * 21104) 64 =
      replaceByte (BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList output (ClaudeWCT.W9.T3M.Paired.mainWitness w)) 21104 8)))
        0 (choiceByte w.topHigh).toBitVec := by
  have e := ClaudeWCT.W9.T3M.PairedReadout.choiceWord_witEnc output w
  rw [show 8 * (8 * 2638) = 8 * 21104 by norm_num] at e
  rw [e, witEnc_word]

theorem lowDelta_old (o : Nat) (h1 : 11144 ≤ o) (h2 : o < 22016) (h8 : o % 8 = 0) :
    8096 ≤ o + lowDelta o ∧ o + lowDelta o < 23240 ∧ (o + lowDelta o) % 8 = 0 ∧
      (o + lowDelta o = 22312 ↔ o = 21104) := by
  unfold lowDelta; split_ifs <;> omega

/-- **The encoding theorem.** -/
theorem ppMem_witEnc (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (M : Nat → Word)
    (hF : ∀ j, j < 958 → M (2904 + 8 * j) = (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (64 * j) 64)
    (hO : ∀ j, 1012 ≤ j → j < 2905 → j ≠ 2789 →
      M (2904 + 8 * j) = oldWord output (ClaudeWCT.W9.T3M.Paired.mainWitness w) (8 * j))
    (hC : M (2904 + 8 * 2789) =
      replaceByte (oldWord output (ClaudeWCT.W9.T3M.Paired.mainWitness w) (8 * 2789)) 0 (choiceByte w.topHigh).toBitVec)
    (hleaf : leafOf (M 0x20160) % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096) :
    ∀ k, k < 2752 → ppMem (leafOf (M 0x20160)) M (4128 + 8 * k) = (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (64 * k) 64 := by
  intro k hk
  rw [ppMem_leaf_congr _ _ hleaf]
  by_cases hfts : k < 958
  · rw [ppMem_out _ _ _ (by omega), stage7_fts _ _ (by omega) (by omega), hF k hfts]
  have hO' : ∀ o, 8096 ≤ o → o < 12320 → o % 8 = 0 →
      M (2904 + o) = BitVec.ofNat 64 (readLE (window (OldW.witList output (ClaudeWCT.W9.T3M.Paired.mainWitness w)) o 8)) := by
    intro o h1 h2 h3
    have := hO (o / 8) (by omega) (by omega) (by omega)
    rwa [show 8 * (o / 8) = o by omega] at this
  rw [show 64 * k = 8 * (8 * k) by ring]
  by_cases htop : k < 1393
  · -- top layer (new bytes [7664, 11144))
    have e := top_word output (ClaudeWCT.W9.T3M.Paired.mainWitness w) M hO' (8 * k - 7664) (by omega) (by omega)
    rw [show 11792 + (8 * k - 7664) = 4128 + 8 * k by omega, show 7664 + (8 * k - 7664) = 8 * k by omega] at e
    rw [e, paired_word_tail output w (8 * k) (by omega) (by omega)]
  · -- lower layers, leaf buffers, tail (new bytes [11144, 22016))
    obtain ⟨b1, b2, b3, b4⟩ := lowDelta_old (8 * k) (by omega) (by omega) (by omega)
    rw [ppMem_out _ _ _ (by omega), stage7_low _ _ (by omega) (by omega) (by omega)]
    by_cases hch : k = 2638
    · subst hch
      have hd : 8 * 2638 + lowDelta (8 * 2638) = 2904 + 8 * 2789 - 2904 := by
        unfold lowDelta; norm_num
      rw [hd, show 2904 + (2904 + 8 * 2789 - 2904) = 2904 + 8 * 2789 by norm_num, hC, oldWord,
        show 8 * 2789 = 8 * 2638 + lowDelta (8 * 2638) from hd.symm,
        ← lower_window output (ClaudeWCT.W9.T3M.Paired.mainWitness w) (8 * 2638) (by norm_num) (by norm_num) (by norm_num),
        show 8 * 2638 = 21104 by norm_num, paired_word_choice]
    · have hne : 8 * k + lowDelta (8 * k) ≠ 22312 := fun h => hch (by have := b4.mp h; omega)
      have := hO ((8 * k + lowDelta (8 * k)) / 8) (by omega) (by omega) (by omega)
      rw [show 8 * ((8 * k + lowDelta (8 * k)) / 8) = 8 * k + lowDelta (8 * k) by omega] at this
      rw [this, oldWord, ← lower_window output (ClaudeWCT.W9.T3M.Paired.mainWitness w) (8 * k) (by omega) (by omega) (by omega),
        paired_word_tail output w (8 * k) (by omega) (by omega)]

/-- FTS hypothesis in window style (bytes `[0, 7664)` of `Paired.witList`). -/
theorem fts_word_window (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (j : Nat)
    (hj : j < 958) :
    BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.Paired.witList output w) (8 * j) 8)) =
      (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (64 * j) 64 := by
  unfold ClaudeWCT.W9.T3M.Paired.witEnc
  rw [show 64 * j = 8 * (8 * j) by ring, show (64 : Nat) = 8 * 8 from rfl,
    ClaudeWCT.W9.T3M.PairedReadout.extract_readLE _ 22012 (8 * j) 8 (by omega)]
  rfl

/-- **Machine form.** Run the post-pass from pc 49400 to the pad-writer hook (pc 54174): the 2752 witness dwords at
`0x1020` hold `Paired.witEnc output w`. -/
theorem pp_witEnc (s : MachineState) (hpc : s.pc = pcOf 49400) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hF : ∀ j, j < 958 → s.getMem (BitVec.ofNat 64 (2904 + 8 * j)) = (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (64 * j) 64)
    (hO : ∀ j, 1012 ≤ j → j < 2905 → j ≠ 2789 →
      s.getMem (BitVec.ofNat 64 (2904 + 8 * j)) = oldWord output (ClaudeWCT.W9.T3M.Paired.mainWitness w) (8 * j))
    (hC : s.getMem (BitVec.ofNat 64 (2904 + 8 * 2789)) =
      replaceByte (oldWord output (ClaudeWCT.W9.T3M.Paired.mainWitness w) (8 * 2789)) 0 (choiceByte w.topHigh).toBitVec)
    (hleaf : leafOf (s.getMem (BitVec.ofNat 64 0x20160)) % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096) :
    ∃ t, Steps SigGolfCandidate.T3M.Images.expandImage s 16205 ppCycles t ∧ t.pc = pcOf 54174 ∧
      RegsExcept s t [.x6, .x7, .x10, .x28, .x29, .x30] ∧
      (∀ k, k < 2752 → t.getMem (BitVec.ofNat 64 (4128 + 8 * k)) = (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (64 * k) 64) ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        ppMem (leafOf (s.getMem (BitVec.ofNat 64 0x20160))) (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  obtain ⟨t, st, tp, tr, tm⟩ := pp_spec s hpc
  refine ⟨t, st, tp, tr, fun k hk => ?_, tm⟩
  rw [tm (4128 + 8 * k) (by omega)]
  exact ppMem_witEnc output w (fun B => s.getMem (BitVec.ofNat 64 B)) hF hO hC hleaf k hk

/-- The post-pass leaves the nonce / saved-leaf scratch `[0x66700, 0x66760)` untouched. -/
theorem ppMem_scratch (leaf : Nat) (M : Nat → Word) (A : Nat) (h1 : 0x66700 ≤ A) (h2 : A < 0x66760) :
    ppMem leaf M A = M A := by
  rw [ppMem_out _ _ _ (by omega)]
  unfold stage7
  rw [zfill_miss _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega),
    bmv_miss _ _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega),
    fcp_miss _ _ _ _ _ (by omega)]

/-- Machine form of `ppMem_scratch` (pp_spec frame): the eleven nonces `0x66700 + 8 j` and the leaf word `0x66758`
read by the pad writer are those at the post-pass entry. -/
theorem pp_scratch (s t : MachineState)
    (tm : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
      ppMem (leafOf (s.getMem (BitVec.ofNat 64 0x20160))) (fun B => s.getMem (BitVec.ofNat 64 B)) A)
    (A : Nat) (h1 : 0x66700 ≤ A) (h2 : A < 0x66760) :
    t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  rw [tm A (by omega), ppMem_scratch _ _ _ h1 h2]

end ClaudeWCT.W9.Machine.Expand.PostEnc
