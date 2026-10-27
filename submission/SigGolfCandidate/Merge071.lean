import SigGolfCandidate.Merge069
import SigGolfCandidate.Merge070

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PostEnc ====
section

/-! # The witness-stack post-pass at the encoding level

`PostPass.pp_spec` describes the post-pass (words 49400..54175) as the memory map `ppMem`. Here: if, at its entry,
the FTS block `[2904, 10568)` holds the bytes `[0, 7664)` of `Paired.witEnc` and `[11000, 26144)` holds the bytes
`[8096, 23240)` of the pre-witness-stack encoding `OldW.witList` (with the choice byte at 25216), then afterwards
`[4128, 26144)` holds `Paired.witEnc` word by word. -/

set_option autoImplicit false

namespace ClaudeWCT.W9.Machine.Expand.PostPass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ### Table lookups -/
def rowSrc (pairs : List (Nat × Nat)) (q : Nat) : Option Nat :=
  (pairs.reverse.find? (fun e => decide (e.2 = q))).map Prod.fst
def vSrc (A : Nat) : Option Nat := (vTable.reverse.find? (fun e => decide (e.1 = A))).map Prod.snd

theorem rowFun_eq (pairs : List (Nat × Nat)) (M : Nat → Word) (q : Nat) :
    rowFun pairs M (11792 + q) = match rowSrc pairs q with
      | some s => M (0x301000 + s)
      | none => M (11792 + q) := by
  unfold rowFun rowSrc
  have h : (fun e : Nat × Nat => decide (11792 + e.2 = 11792 + q)) = (fun e => decide (e.2 = q)) := by
    funext e; simp
  rw [h]
  cases pairs.reverse.find? (fun e => decide (e.2 = q)) <;> rfl

theorem rowFun_miss (pairs : List (Nat × Nat)) (M : Nat → Word) (A : Nat) (h : ∀ e ∈ pairs, 11792 + e.2 ≠ A) :
    rowFun pairs M A = M A := by
  unfold rowFun
  rw [List.find?_eq_none.mpr (fun e he => by simpa using h e (List.mem_reverse.mp he))]

theorem vFun_eq (M : Nat → Word) (A : Nat) :
    vFun M A = match vSrc A with
      | some s => M (0x300000 + s)
      | none => M A := by
  unfold vFun vSrc
  cases vTable.reverse.find? (fun e => decide (e.1 = A)) <;> rfl

theorem vTable_dst : ∀ e ∈ vTable, 12464 ≤ e.1 ∧ e.1 < 15272 := by decide

theorem vSrc_miss (A : Nat) (h : A < 12464 ∨ 15272 ≤ A) : vSrc A = none := by
  unfold vSrc
  rw [List.find?_eq_none.mpr (fun e he => by
    have := vTable_dst e (List.mem_reverse.mp he)
    simp only [decide_eq_true_eq]; omega)]
  rfl

theorem vFun_miss (M : Nat → Word) (A : Nat) (h : A < 12464 ∨ 15272 ≤ A) : vFun M A = M A := by
  rw [vFun_eq, vSrc_miss A h]

/-- Expected value-table source of the word at `12464 + 104 m + 8 t` (top pair `26 - m` of the new layout). -/
def vExp (m t : Nat) : Option Nat :=
  if 2 ≤ t ∧ t < 4 then some (64 * (53 - 2 * (26 - m)) + 48 + 8 * (t - 2))
  else if 11 ≤ t then some (64 * (53 - (2 * (26 - m) + 1)) + 48 + 8 * (t - 11)) else none

theorem vSrc_table : ∀ m < 27, ∀ t < 13, vSrc (12464 + 104 * m + 8 * t) = vExp m t := by decide +kernel

theorem rowsA_dst : ∀ r < 64, ∀ e ∈ rowsA.getD r [], e.2 < 672 := by decide +kernel
theorem rowsB_dst : ∀ r < 64, ∀ e ∈ rowsB.getD r [], e.2 < 672 := by decide +kernel

theorem rowsA_src : ∀ r < 64, ∀ j < 6, ∀ h < 2,
    rowSrc (rowsA.getD r []) (ClaudeWCT.W9.T3M.topSibA r j + 8 * h) = some (OldW.topSibA r j + 8 * h) := by
  decide +kernel
theorem rowsB_src : ∀ r < 64, ∀ j < 6, ∀ h < 2,
    rowSrc (rowsB.getD r []) (ClaudeWCT.W9.T3M.topSibB r j + 8 * h) = some (OldW.topSibB r j + 8 * h) := by
  decide +kernel
theorem rowsA_none : ∀ r < 64, ∀ q < 84,
    (∀ j < 6, 8 * q + 8 ≤ ClaudeWCT.W9.T3M.topSibA r j ∨ ClaudeWCT.W9.T3M.topSibA r j + 16 ≤ 8 * q) →
      rowSrc (rowsA.getD r []) (8 * q) = none := by
  decide +kernel
theorem rowsB_none : ∀ r < 64, ∀ q < 84,
    (∀ j < 6, 8 * q + 8 ≤ ClaudeWCT.W9.T3M.topSibB r j ∨ ClaudeWCT.W9.T3M.topSibB r j + 16 ≤ 8 * q) →
      rowSrc (rowsB.getD r []) (8 * q) = none := by
  decide +kernel
theorem newA_bound : ∀ r < 64, ∀ j < 6,
    336 ≤ ClaudeWCT.W9.T3M.topSibA r j ∧ ClaudeWCT.W9.T3M.topSibA r j + 16 ≤ 672 ∧
      ClaudeWCT.W9.T3M.topSibA r j % 8 = 0 := by decide
theorem newB_bound : ∀ r < 64, ∀ j < 6,
    ClaudeWCT.W9.T3M.topSibB r j + 16 ≤ 320 ∧ ClaudeWCT.W9.T3M.topSibB r j % 8 = 0 := by decide
theorem oldA_bound : ∀ r < 64, ∀ j < 6, OldW.topSibA r j + 16 ≤ 768 ∧ OldW.topSibA r j % 8 = 0 := by decide
theorem oldB_bound : ∀ r < 64, ∀ j < 6, OldW.topSibB r j + 16 ≤ 768 ∧ OldW.topSibB r j % 8 = 0 := by decide

/-! ### The copy/move/zero stages -/
theorem fcp_hit (M : Nat → Word) (a b i A : Nat) (h1 : b ≤ A) (h2 : A < b + 8 * i) (h3 : (A - b) % 8 = 0) :
    fcp M a b i A = M (a + (A - b)) := if_pos ⟨h1, h2, h3⟩
theorem fcp_miss (M : Nat → Word) (a b i A : Nat) (h : A < b ∨ b + 8 * i ≤ A) : fcp M a b i A = M A :=
  if_neg (by omega)
theorem bmv_hit (M : Nat → Word) (T d i A : Nat) (h1 : T + d + 8 ≤ A + 8 * i) (h2 : A ≤ T + d)
    (h3 : (T + d - A) % 8 = 0) : bmv M T d i A = M (A - d) := if_pos ⟨h1, h2, h3⟩
theorem bmv_miss (M : Nat → Word) (T d i A : Nat) (h : A + 8 * i < T + d + 8 ∨ T + d < A) : bmv M T d i A = M A :=
  if_neg (by omega)
theorem zfill_hit (M : Nat → Word) (a i A : Nat) (h1 : a ≤ A) (h2 : A < a + 8 * i) (h3 : (A - a) % 8 = 0) :
    zfill M a i A = 0 := if_pos ⟨h1, h2, h3⟩
theorem zfill_miss (M : Nat → Word) (a i A : Nat) (h : A < a ∨ a + 8 * i ≤ A) : zfill M a i A = M A :=
  if_neg (by omega)

/-- Memory after the save, move and zero stages (before the value copies and the row blocks). -/
def stage7 (M : Nat → Word) : Nat → Word :=
  zfill (bmv (bmv (bmv (bmv (fcp (fcp M 11768 0x300000 432) 11000 0x301000 96) 26088 16 202) 24456 32 90)
    23720 48 1063) 10560 1224 958) 11792 435

theorem ppMem_eq (leaf : Nat) (M : Nat → Word) :
    ppMem leaf M = rowFun (rowsB.getD (leaf / 64 % 64) []) (rowFun (rowsA.getD (leaf % 64) []) (vFun (stage7 M))) :=
  rfl

theorem stage7_path (M : Nat → Word) (s : Nat) (hs : s < 768) (h8 : s % 8 = 0) :
    stage7 M (0x301000 + s) = M (11000 + s) := by
  unfold stage7
  rw [zfill_miss _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega),
    bmv_miss _ _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega), fcp_hit _ _ _ _ _ (by omega) (by omega) (by omega),
    show 0x301000 + s - 0x301000 = s by omega, fcp_miss _ _ _ _ _ (by omega)]

theorem stage7_chain (M : Nat → Word) (s : Nat) (hs : s < 3456) (h8 : s % 8 = 0) :
    stage7 M (0x300000 + s) = M (11768 + s) := by
  unfold stage7
  rw [zfill_miss _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega),
    bmv_miss _ _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega),
    fcp_hit _ _ _ _ _ (by omega) (by omega) (by omega), show 0x300000 + s - 0x300000 = s by omega]

theorem stage7_top (M : Nat → Word) (q : Nat) (hq : q < 3480) (h8 : q % 8 = 0) : stage7 M (11792 + q) = 0 := by
  unfold stage7
  exact zfill_hit _ _ _ _ (by omega) (by omega) (by omega)

theorem stage7_fts (M : Nat → Word) (o : Nat) (ho : o < 7664) (h8 : o % 8 = 0) :
    stage7 M (4128 + o) = M (2904 + o) := by
  unfold stage7
  rw [zfill_miss _ _ _ _ (by omega), bmv_hit _ _ _ _ _ (by omega) (by omega) (by omega),
    show 4128 + o - 1224 = 2904 + o by omega, bmv_miss _ _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega),
    bmv_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega)]

/-- Shift of the lower part: new byte `o` (`11144 ≤ o`) comes from old byte `o + lowDelta o`. -/
def lowDelta (o : Nat) : Nat := if o < 19648 then 1176 else if o < 20368 then 1192 else if o < 21984 then 1208 else 1224

theorem stage7_low (M : Nat → Word) (o : Nat) (h1 : 11144 ≤ o) (h2 : o < 22016) (h8 : o % 8 = 0) :
    stage7 M (4128 + o) = M (2904 + (o + lowDelta o)) := by
  unfold stage7 lowDelta
  rw [zfill_miss _ _ _ _ (by omega), bmv_miss _ _ _ _ _ (by omega)]
  by_cases ha : o < 19648
  · rw [if_pos ha, bmv_hit _ _ _ _ _ (by omega) (by omega) (by omega), bmv_miss _ _ _ _ _ (by omega),
      bmv_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega)]
    congr 1; omega
  rw [if_neg ha, bmv_miss _ _ _ _ _ (by omega)]
  by_cases hb : o < 20368
  · rw [if_pos hb, bmv_hit _ _ _ _ _ (by omega) (by omega) (by omega), bmv_miss _ _ _ _ _ (by omega),
      fcp_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega)]
    congr 1; omega
  rw [if_neg hb, bmv_miss _ _ _ _ _ (by omega)]
  by_cases hc : o < 21984
  · rw [if_pos hc, bmv_hit _ _ _ _ _ (by omega) (by omega) (by omega),
      fcp_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega)]
    congr 1; omega
  rw [if_neg hc, bmv_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega), fcp_miss _ _ _ _ _ (by omega)]
  congr 1; omega

/-- Away from the top region the value copies and row blocks do not write. -/
theorem ppMem_out (leaf : Nat) (M : Nat → Word) (A : Nat) (h : A < 11792 ∨ 15272 ≤ A) :
    ppMem leaf M A = stage7 M A := by
  rw [ppMem_eq, rowFun_miss _ _ _ (fun e he => by
      have := rowsB_dst _ (Nat.mod_lt _ (by decide)) e he; omega),
    rowFun_miss _ _ _ (fun e he => by have := rowsA_dst _ (Nat.mod_lt _ (by decide)) e he; omega),
    vFun_miss _ _ (by omega)]
end ClaudeWCT.W9.Machine.Expand.PostPass

namespace ClaudeWCT.W9.Machine.Expand.PostEnc
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput Layer LayerSignature height chainCount route readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap_const window_full
  window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Expand.PostPass
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem window_window (L : List UInt8) (o m a n : Nat) (h : a + n ≤ m) :
    window (window L o m) a n = window L (o + a) n := by
  unfold window
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

theorem zeros_length (n : Nat) : (zeros n).length = n := List.length_replicate ..

theorem readLE_zeros8 : readLE (zeros 8) = 0 := by decide

/-! ### Lower part: lower layers, leaf buffers and tail -/
theorem lowerPlan_eq : OldW.lowerPlan = ClaudeWCT.W9.T3M.lowerPlan := rfl
theorem lsValue_eq {lay : Layer} (ls : LayerSignature lay) (i : Nat) :
    OldW.lsValue ls i = ClaudeWCT.W9.T3M.lsValue ls i := rfl

theorem layerRegion_eq (N : HashOutput) (w : WCT9.Witness) (lay : Layer) (hl : lay.val ≠ 0) :
    OldW.layerRegion N w lay = ClaudeWCT.W9.T3M.layerRegion N w lay := by
  have hp : OldW.pathSlots lay = ClaudeWCT.W9.T3M.pathSlots lay := by
    fin_cases lay
    · exact absurd rfl hl
    all_goals rfl
  unfold OldW.layerRegion ClaudeWCT.W9.T3M.layerRegion
  rw [if_neg hl, if_neg hl]
  congr 1
  unfold OldW.lowerPathBytes ClaudeWCT.W9.T3M.lowerPathBytes OldW.lowerPathByte ClaudeWCT.W9.T3M.lowerPathByte
    OldW.lowerSibSlot ClaudeWCT.W9.T3M.lowerSibSlot OldW.lowerCtrSlot ClaudeWCT.W9.T3M.lowerCtrSlot
    OldW.lowerHiSlot ClaudeWCT.W9.T3M.lowerHiSlot
  rw [hp, lowerPlan_eq]
  all_goals rfl

theorem leafBuffer_ext (sig : WCT9.Signature) (lay : Layer) :
    ∃ Z, OldW.leafBufferBytes sig lay = ClaudeWCT.W9.T3M.leafBufferBytes sig lay ++ Z := by
  have he : ∀ l, OldW.endpointBytes sig l = ClaudeWCT.W9.T3M.endpointBytes sig l := fun _ => rfl
  have key : ∀ (A : List UInt8) (a b : Nat), b ≤ a → A ++ zeros a = (A ++ zeros b) ++ zeros (a - b) := by
    intro A a b h
    rw [List.append_assoc]
    congr 1
    unfold zeros
    rw [← List.replicate_add]
    congr 1
    omega
  fin_cases lay
  · exact ⟨_, key _ 80 64 (by omega)⟩
  · exact ⟨_, key _ 16 16 (by omega)⟩
  · exact ⟨_, key _ 32 16 (by omega)⟩
  · exact ⟨_, key _ 32 16 (by omega)⟩

theorem leafBuffer_win (sig : WCT9.Signature) (lay : Layer) (j : Nat)
    (h : j + 8 ≤ ClaudeWCT.W9.T3M.leafBufferLen lay) :
    window (OldW.leafBufferBytes sig lay) j 8 = window (ClaudeWCT.W9.T3M.leafBufferBytes sig lay) j 8 := by
  obtain ⟨Z, hZ⟩ := leafBuffer_ext sig lay
  rw [hZ, window_append_left _ _ _ _ (by rw [ClaudeWCT.W9.T3M.leafBufferBytes_length]; exact h)]

theorem lower_window (N : HashOutput) (w : WCT9.Witness) (o : Nat) (h1 : 11144 ≤ o) (h2 : o < 22016)
    (h8 : o % 8 = 0) :
    window (ClaudeWCT.W9.T3M.witList N w) o 8 = window (OldW.witList N w) (o + lowDelta o) 8 := by
  unfold lowDelta
  have hlay : ∀ lay : Layer, lay.val ≠ 0 → ClaudeWCT.W9.T3M.layerBase lay ≤ o →
      o + 8 ≤ ClaudeWCT.W9.T3M.layerBase lay + (16 * ClaudeWCT.W9.T3M.pathSlots lay + ClaudeWCT.W9.T3M.chainArea lay) →
      OldW.layerBase lay = ClaudeWCT.W9.T3M.layerBase lay + 1176 →
      OldW.pathSlots lay = ClaudeWCT.W9.T3M.pathSlots lay → OldW.chainArea lay = ClaudeWCT.W9.T3M.chainArea lay →
      window (ClaudeWCT.W9.T3M.witList N w) o 8 = window (OldW.witList N w) (o + 1176) 8 := by
    intro lay hl hb he hob hps hca
    obtain ⟨j, rfl⟩ : ∃ j, o = ClaudeWCT.W9.T3M.layerBase lay + j := ⟨o - ClaudeWCT.W9.T3M.layerBase lay, by omega⟩
    rw [show ClaudeWCT.W9.T3M.layerBase lay + j + 1176 = OldW.layerBase lay + j by omega,
      OldW.win_layerRegion _ _ _ _ _ (by rw [hps, hca]; omega), layerRegion_eq N w lay hl,
      ClaudeWCT.W9.T3M.win_layerRegion _ _ _ _ _ (by omega)]
  have hbuf : ∀ (lay : Layer) (d : Nat), ClaudeWCT.W9.T3M.leafBufferBase lay ≤ o →
      o + 8 ≤ ClaudeWCT.W9.T3M.leafBufferBase lay + ClaudeWCT.W9.T3M.leafBufferLen lay →
      OldW.leafBufferBase lay = ClaudeWCT.W9.T3M.leafBufferBase lay + d →
      ClaudeWCT.W9.T3M.leafBufferLen lay ≤ OldW.leafBufferLen lay →
      window (ClaudeWCT.W9.T3M.witList N w) o 8 = window (OldW.witList N w) (o + d) 8 := by
    intro lay d hb he hob hlen
    obtain ⟨j, rfl⟩ : ∃ j, o = ClaudeWCT.W9.T3M.leafBufferBase lay + j :=
      ⟨o - ClaudeWCT.W9.T3M.leafBufferBase lay, by omega⟩
    rw [show ClaudeWCT.W9.T3M.leafBufferBase lay + j + d = OldW.leafBufferBase lay + j by omega,
      OldW.win_leafBuffer _ _ _ _ _ (by omega), leafBuffer_win _ _ _ (by omega),
      ClaudeWCT.W9.T3M.win_leafBuffer _ _ _ _ _ (by omega)]
  by_cases ha : o < 13792
  · rw [if_pos (by omega)]
    exact hlay 1 (by decide) (show 11144 ≤ o by omega) (show o + 8 ≤ 13792 by omega) rfl rfl rfl
  by_cases hb : o < 16360
  · rw [if_pos (by omega)]
    exact hlay 2 (by decide) (show 13792 ≤ o by omega) (show o + 8 ≤ 16360 by omega) rfl rfl rfl
  by_cases hc : o < 18928
  · rw [if_pos (by omega)]
    exact hlay 3 (by decide) (show 16360 ≤ o by omega) (show o + 8 ≤ 18928 by omega) rfl rfl rfl
  by_cases hd : o < 19648
  · rw [if_pos hd]
    exact hbuf 3 1176 (show 18928 ≤ o by omega) (show o + 8 ≤ 19648 by omega) rfl (by decide)
  by_cases he : o < 20368
  · rw [if_neg hd, if_pos he]
    exact hbuf 2 1192 (show 19648 ≤ o by omega) (show o + 8 ≤ 20368 by omega) rfl (by decide)
  by_cases hf : o < 21088
  · rw [if_neg hd, if_neg he, if_pos (by omega)]
    exact hbuf 1 1208 (show 20368 ≤ o by omega) (show o + 8 ≤ 21088 by omega) rfl (by decide)
  by_cases hg : o < 21984
  · rw [if_neg hd, if_neg he, if_pos hg]
    exact hbuf 0 1208 (show 21088 ≤ o by omega) (show o + 8 ≤ 21984 by omega) rfl (by decide)
  rw [if_neg hd, if_neg he, if_neg hg]
  obtain ⟨j, rfl⟩ : ∃ j, o = 21984 + j := ⟨o - 21984, by omega⟩
  rw [show 21984 + j + 1224 = 23208 + j by omega, OldW.win_tail _ _ _ _ (by omega),
    ClaudeWCT.W9.T3M.win_tail _ _ _ _ (by omega)]
  rfl

/-! ### Top region -/
theorem rowFun_some {pairs : List (Nat × Nat)} {q s : Nat} (M : Nat → Word) (h : rowSrc pairs q = some s) :
    rowFun pairs M (11792 + q) = M (0x301000 + s) := by rw [rowFun_eq, h]
theorem rowFun_none {pairs : List (Nat × Nat)} {q : Nat} (M : Nat → Word) (h : rowSrc pairs q = none) :
    rowFun pairs M (11792 + q) = M (11792 + q) := by rw [rowFun_eq, h]

theorem win_sub (L : List UInt8) (a h : Nat) (hh : h < 2) : window L (a + 8 * h) 8 = window (window L a 16) (8 * h) 8 :=
  (window_window L a 16 (8 * h) 8 (by omega)).symm

theorem topPair_win {lay : Layer} (ls : LayerSignature lay) (p t : Nat) (ht : t < 13) :
    window (ClaudeWCT.W9.T3M.topPairBytes ls p) (8 * t) 8 =
      if t < 2 then zeros 8 else if t < 4 then window (bytesLE 16 (ClaudeWCT.W9.T3M.lsValue ls (2 * p))) (8 * t - 16) 8
      else if t < 11 then zeros 8 else window (bytesLE 16 (ClaudeWCT.W9.T3M.lsValue ls (2 * p + 1))) (8 * t - 88) 8 := by
  unfold ClaudeWCT.W9.T3M.topPairBytes
  simp only [List.append_assoc]
  split_ifs with h1 h2 h3
  · rw [window_append_left _ _ _ _ (by rw [zeros_length]; omega), window_zeros _ _ _ (by omega)]
  · rw [window_append_right _ _ _ _ (by rw [zeros_length]; omega), zeros_length,
      window_append_left _ _ _ _ (by rw [bytesLE_length]; omega)]
  · rw [window_append_right _ _ _ _ (by rw [zeros_length]; omega), zeros_length,
      window_append_right _ _ _ _ (by rw [bytesLE_length]; omega), bytesLE_length,
      window_append_left _ _ _ _ (by rw [zeros_length]; omega), window_zeros _ _ _ (by omega)]
  · rw [window_append_right _ _ _ _ (by rw [zeros_length]; omega), zeros_length,
      window_append_right _ _ _ _ (by rw [bytesLE_length]; omega), bytesLE_length,
      window_append_right _ _ _ _ (by rw [zeros_length]; omega), zeros_length]
    congr 1 <;> omega

theorem topChain_win (ls : LayerSignature 0) (m t : Nat) (hm : m < 27) (ht : t < 13) :
    window (ClaudeWCT.W9.T3M.topChainBytes ls) (104 * m + 8 * t) 8 =
      window (ClaudeWCT.W9.T3M.topPairBytes ls (26 - m)) (8 * t) 8 := by
  unfold ClaudeWCT.W9.T3M.topChainBytes
  rw [window_flatMap_const _ _ 104 (ClaudeWCT.W9.T3M.topPairBytes_length ls) m (by simp; omega) _ _ (by omega)]
  have hidx : ((List.range 27).reverse)[m]'(by simp <;> omega) = 26 - m := by simp <;> omega
  rw [hidx]

theorem win_topChain (N : HashOutput) (w : WCT9.Witness) (c : Nat) (hc : c + 8 ≤ 2808) :
    window (ClaudeWCT.W9.T3M.witList N w) (7664 + (672 + c)) 8 =
      window (ClaudeWCT.W9.T3M.topChainBytes (w.signature.layers 0)) c 8 := by
  rw [show 7664 + (672 + c) = ClaudeWCT.W9.T3M.layerBase 0 + (672 + c) from rfl,
    ClaudeWCT.W9.T3M.win_layerRegion _ _ _ _ _ (show 672 + c + 8 ≤ 3480 by omega)]
  unfold ClaudeWCT.W9.T3M.layerRegion
  rw [if_pos (show (0 : Layer).val = 0 from rfl),
    window_append_right _ _ _ _ (by rw [ClaudeWCT.W9.T3M.topPathBytes_length]; show 672 ≤ 672 + c; omega),
    ClaudeWCT.W9.T3M.topPathBytes_length, show 672 + c - 16 * ClaudeWCT.W9.T3M.pathSlots 0 = c by
      show 672 + c - 672 = c; omega]

theorem old_chainBlock (i : Nat) (hi : i < 54) : OldW.chainBlock 0 i = 8864 + 64 * (53 - i) := by
  unfold OldW.chainBlock OldW.chainSlot
  rw [if_pos (show (0 : Layer).val = 0 from rfl)]
  have h1 : OldW.layerBase 0 = 8096 := rfl
  have h2 : OldW.pathSlots 0 = 48 := rfl
  rw [h1, h2]

/-- Old top chain `i` (`64`-byte F block, value at `+48`). -/
theorem old_value_win (N : HashOutput) (w : WCT9.Witness) (i h : Nat) (hi : i < 54) (hh : h < 2) :
    window (OldW.witList N w) (8864 + 64 * (53 - i) + 48 + 8 * h) 8 =
      window (bytesLE 16 (ClaudeWCT.W9.T3M.lsValue (w.signature.layers 0) i)) (8 * h) 8 := by
  by_cases h51 : i < 51
  · have e := OldW.win_chain N w 0 ⟨i, by simpa [chainCount] using h51⟩ 48 (by omega)
    simp only at e
    rw [old_chainBlock i hi] at e
    rw [win_sub _ _ _ hh, e]
    unfold OldW.chainCell
    rw [if_neg (by rw [OldW.isG_eq_false (Or.inl rfl)]; decide),
      window_append_right _ _ _ _ (by rw [zeros_length]),
      zeros_length, Nat.sub_self, window_full _ _ (bytesLE_length _ _), lsValue_eq]
  · -- T51: the blocks of #938's chains 51..53 are zero (and so is `lsValue` there)
    have hv : ClaudeWCT.W9.T3M.lsValue (w.signature.layers 0) i = 0 := by
      unfold ClaudeWCT.W9.T3M.lsValue
      rw [dif_neg (by simpa [chainCount] using h51)]
    rw [hv, ClaudeWCT.WCT9.bytesLE_zero16, show SigGolfCandidate.T3.zero16 = zeros 16 from rfl,
      window_zeros _ _ _ (by omega),
      show 8864 + 64 * (53 - i) + 48 + 8 * h = OldW.layerBase 0 + (768 + (64 * (53 - i) + 48 + 8 * h)) by
        show _ = 8096 + _; omega,
      OldW.win_layerRegion N w 0 _ 8 (by show _ ≤ 16 * 48 + 3456; omega)]
    unfold OldW.layerRegion
    rw [if_pos (show (0 : Layer).val = 0 from rfl),
      window_append_right _ _ _ _ (by rw [OldW.topPathBytes_length, OldW.pathSlots_top]; omega),
      OldW.topPathBytes_length, OldW.pathSlots_top, Nat.add_sub_cancel_left,
      window_append_left _ _ _ _ (by rw [zeros_length]; omega), window_zeros _ _ _ (by omega)]

theorem top_word (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hO : ∀ o, 8096 ≤ o → o < 12320 → o % 8 = 0 →
      M (2904 + o) = BitVec.ofNat 64 (readLE (window (OldW.witList N w) o 8)))
    (q : Nat) (hq : q < 3480) (h8 : q % 8 = 0) :
    ppMem (route (WCT9.digestIndex N) 0).1 M (11792 + q) =
      BitVec.ofNat 64 (readLE (window (ClaudeWCT.W9.T3M.witList N w) (7664 + q) 8)) := by
  set leaf := (route (WCT9.digestIndex N) 0).1 with hleaf
  set ls := w.signature.layers 0 with hls
  have hr : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr' : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  have h12 : 12 ≤ height (0 : Layer) := by decide
  by_cases hpath : q < 672
  · have hnew : window (ClaudeWCT.W9.T3M.witList N w) (7664 + q) 8 =
        window (ClaudeWCT.W9.T3M.topPathBytes leaf ls) q 8 := ClaudeWCT.W9.T3M.win_topPath N w q 8 (by omega)
    rw [hnew]
    have hAnone : (¬ ∃ j < 6, ClaudeWCT.W9.T3M.topSibA (leaf % 64) j ≤ q ∧ q < ClaudeWCT.W9.T3M.topSibA (leaf % 64) j + 16) →
        rowSrc (rowsA.getD (leaf % 64) []) q = none := by
      intro hA
      have := rowsA_none _ hr (q / 8) (by omega) (fun j hj => by
        have := newA_bound _ hr j hj
        by_contra hc
        exact hA ⟨j, hj, by omega⟩)
      rwa [show 8 * (q / 8) = q by omega] at this
    have hBnone : (¬ ∃ j < 6, ClaudeWCT.W9.T3M.topSibB (leaf / 64 % 64) j ≤ q ∧
        q < ClaudeWCT.W9.T3M.topSibB (leaf / 64 % 64) j + 16) → rowSrc (rowsB.getD (leaf / 64 % 64) []) q = none := by
      intro hB
      have := rowsB_none _ hr' (q / 8) (by omega) (fun j hj => by
        have := newB_bound _ hr' j hj
        by_contra hc
        exact hB ⟨j, hj, by omega⟩)
      rwa [show 8 * (q / 8) = q by omega] at this
    by_cases hA : ∃ j < 6, ClaudeWCT.W9.T3M.topSibA (leaf % 64) j ≤ q ∧ q < ClaudeWCT.W9.T3M.topSibA (leaf % 64) j + 16
    · obtain ⟨j, hj, h1, h2⟩ := hA
      obtain ⟨b1, b2, b3⟩ := newA_bound _ hr j hj
      obtain ⟨c1, c2⟩ := oldA_bound _ hr j hj
      have hB : ¬ ∃ j < 6, ClaudeWCT.W9.T3M.topSibB (leaf / 64 % 64) j ≤ q ∧
          q < ClaudeWCT.W9.T3M.topSibB (leaf / 64 % 64) j + 16 := by
        rintro ⟨j', hj', h1', h2'⟩
        have := newB_bound _ hr' j' hj'
        omega
      have hBn := hBnone hB
      obtain ⟨h, hh, rfl⟩ : ∃ h < 2, q = ClaudeWCT.W9.T3M.topSibA (leaf % 64) j + 8 * h :=
        ⟨(q - ClaudeWCT.W9.T3M.topSibA (leaf % 64) j) / 8, by omega, by omega⟩
      rw [ppMem_eq, rowFun_none _ hBn, rowFun_some _ (rowsA_src _ hr j hj h hh), vFun_miss _ _ (by omega),
        stage7_path _ _ (by omega) (by omega),
        show 11000 + (OldW.topSibA (leaf % 64) j + 8 * h) = 2904 + (8096 + (OldW.topSibA (leaf % 64) j + 8 * h)) by
          omega, hO _ (by omega) (by omega) (by omega)]
      have eo := OldW.topPath_sib leaf ls ⟨j, by omega⟩
      have en := ClaudeWCT.W9.T3M.topPath_sib leaf ls ⟨j, by omega⟩
      simp only at eo en
      rw [OldW.topSibSlot_lo hj] at eo
      rw [ClaudeWCT.W9.T3M.topSibSlot_lo hj] at en
      rw [show (8096 : Nat) + (OldW.topSibA (leaf % 64) j + 8 * h) =
          OldW.layerBase 0 + (OldW.topSibA (leaf % 64) j + 8 * h) from rfl, OldW.win_topPath N w _ 8 (by omega),
        win_sub _ _ _ hh, eo, win_sub _ _ _ hh, en]
    by_cases hB : ∃ j < 6, ClaudeWCT.W9.T3M.topSibB (leaf / 64 % 64) j ≤ q ∧
        q < ClaudeWCT.W9.T3M.topSibB (leaf / 64 % 64) j + 16
    · obtain ⟨j, hj, h1, h2⟩ := hB
      obtain ⟨b1, b2⟩ := newB_bound _ hr' j hj
      obtain ⟨c1, c2⟩ := oldB_bound _ hr' j hj
      obtain ⟨h, hh, rfl⟩ : ∃ h < 2, q = ClaudeWCT.W9.T3M.topSibB (leaf / 64 % 64) j + 8 * h :=
        ⟨(q - ClaudeWCT.W9.T3M.topSibB (leaf / 64 % 64) j) / 8, by omega, by omega⟩
      rw [ppMem_eq, rowFun_some _ (rowsB_src _ hr' j hj h hh),
        rowFun_miss _ _ _ (fun e he => by have := rowsA_dst _ hr e he; omega), vFun_miss _ _ (by omega),
        stage7_path _ _ (by omega) (by omega),
        show 11000 + (OldW.topSibB (leaf / 64 % 64) j + 8 * h) =
          2904 + (8096 + (OldW.topSibB (leaf / 64 % 64) j + 8 * h)) by omega, hO _ (by omega) (by omega) (by omega)]
      have eo := OldW.topPath_sib leaf ls ⟨j + 6, by omega⟩
      have en := ClaudeWCT.W9.T3M.topPath_sib leaf ls ⟨j + 6, by omega⟩
      simp only at eo en
      rw [OldW.topSibSlot_hi (by omega) (by omega), Nat.add_sub_cancel] at eo
      rw [ClaudeWCT.W9.T3M.topSibSlot_hi (by omega) (by omega), Nat.add_sub_cancel] at en
      rw [show (8096 : Nat) + (OldW.topSibB (leaf / 64 % 64) j + 8 * h) =
          OldW.layerBase 0 + (OldW.topSibB (leaf / 64 % 64) j + 8 * h) from rfl, OldW.win_topPath N w _ 8 (by omega),
        win_sub _ _ _ hh, eo, win_sub _ _ _ hh, en]
    · rw [ppMem_eq, rowFun_none _ (hBnone hB), rowFun_none _ (hAnone hA), vFun_miss _ _ (by omega),
        stage7_top _ _ (by omega) h8, ClaudeWCT.W9.T3M.topPath_zero leaf ls (by omega) (fun jj => by
          have hjj := jj.isLt
          by_cases h6 : jj.val < 6
          · rw [ClaudeWCT.W9.T3M.topSibSlot_lo h6]
            have := newA_bound _ hr jj.val h6
            by_contra hc
            exact hA ⟨jj.val, h6, by omega⟩
          · have h12' : jj.val < 12 := by
              have : height (0 : Layer) = 12 := rfl
              omega
            rw [ClaudeWCT.W9.T3M.topSibSlot_hi (by omega) h12']
            have := newB_bound _ hr' (jj.val - 6) (by omega)
            by_contra hc
            exact hB ⟨jj.val - 6, by omega, by omega⟩), readLE_zeros8]
      rfl
  · -- chain area
    obtain ⟨c, rfl⟩ : ∃ c, q = 672 + c := ⟨q - 672, by omega⟩
    have hm : c / 104 < 27 := by omega
    have ht : c % 104 / 8 < 13 := by omega
    have hc : c = 104 * (c / 104) + 8 * (c % 104 / 8) := by omega
    rw [ppMem_eq, rowFun_miss _ _ _ (fun e he => by have := rowsB_dst _ hr' e he; omega),
      rowFun_miss _ _ _ (fun e he => by have := rowsA_dst _ hr e he; omega), vFun_eq,
      show 11792 + (672 + c) = 12464 + 104 * (c / 104) + 8 * (c % 104 / 8) by omega,
      vSrc_table _ hm _ ht, win_topChain N w c (by omega), hc, topChain_win ls _ _ hm ht, topPair_win ls _ _ ht]
    rw [← hc]
    generalize hmm : c / 104 = m at hm hc
    generalize htt : c % 104 / 8 = t at ht hc
    unfold vExp
    by_cases t1 : t < 2
    · rw [if_neg (by omega), if_neg (by omega), if_pos t1]
      dsimp only
      rw [show 12464 + 104 * m + 8 * t = 11792 + (672 + 104 * m + 8 * t) by omega,
        stage7_top _ _ (by omega) (by omega), readLE_zeros8] <;> rfl
    by_cases t2 : t < 4
    · rw [if_pos (by omega), if_neg t1, if_pos t2]
      dsimp only
      rw [stage7_chain _ _ (by omega) (by omega),
        show 11768 + (64 * (53 - 2 * (26 - m)) + 48 + 8 * (t - 2)) =
          2904 + (8864 + 64 * (53 - 2 * (26 - m)) + 48 + 8 * (t - 2)) by omega,
        hO _ (by omega) (by omega) (by omega), old_value_win N w _ _ (by omega) (by omega),
        show 8 * (t - 2) = 8 * t - 16 by omega]
    by_cases t3 : t < 11
    · rw [if_neg (by omega), if_neg (by omega), if_neg t1, if_neg t2, if_pos t3]
      dsimp only
      rw [show 12464 + 104 * m + 8 * t = 11792 + (672 + 104 * m + 8 * t) by omega,
        stage7_top _ _ (by omega) (by omega), readLE_zeros8] <;> rfl
    · rw [if_neg (by omega), if_pos (by omega), if_neg t1, if_neg t2, if_neg t3]
      dsimp only
      rw [stage7_chain _ _ (by omega) (by omega),
        show 11768 + (64 * (53 - (2 * (26 - m) + 1)) + 48 + 8 * (t - 11)) =
          2904 + (8864 + 64 * (53 - (2 * (26 - m) + 1)) + 48 + 8 * (t - 11)) by omega,
        hO _ (by omega) (by omega) (by omega), old_value_win N w _ _ (by omega) (by omega),
        show 8 * (t - 11) = 8 * t - 88 by omega]
end ClaudeWCT.W9.Machine.Expand.PostEnc
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PostEncW ====
section

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
end
