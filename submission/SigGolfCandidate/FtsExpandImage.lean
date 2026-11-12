import SigGolfCandidate.Merge060
import SigGolfCandidate.FtsExpandRun
import SigGolfCandidate.FtsExpand16
set_option debug.skipKernelTC true
set_option linter.all false

/-! # E8: the expand image holds the FTS grind code

The expander's NOP pad carries `SEARCH` (61000), the 384 trampolines (61100) and the three copy families
(63488 first, 67584 k8, 75776 odd) as their own `Merge055` blocks. Each block is checked once against the image
(`codeAt_expand_last`); every copy prefix and trampoline is a kernel-checked sub-window of its block. -/

namespace W9Drv.SharedBank
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind (SEARCH TRAMP searchWords trampWords)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- E10-style cut: the six FTS blocks are contiguous in the image (61000..83968, with NOP gaps), so the image is
checked once over the whole window and each block is a structural sub-window (no kernel evaluation of the prefix). -/
def ftsWin : List (BitVec 32) := Images.expandFtsSearch ++ (List.replicate 3 0x13 ++ (Images.expandFtsPost ++
  (List.replicate 11 0x13 ++ (Images.expandFtsTramp ++ (List.replicate 468 0x13 ++ (Images.expandFtsCopyFirst ++
  (Images.expandFtsCopyK8 ++ Images.expandFtsCopyOdd)))))))

theorem codeAt_ftsWin : CodeAt Images.expandImage (pcOf 61000) ftsWin := by
  -- The image's appends are right-associated once (`expandCode_172_eq_R`, Merge060): the kernel's `drop` through
  -- the left-nested chains of small blocks (words 4068..12012) is what costs time and memory.
  apply codeAt_expand_lastR <;> decide +kernel

theorem codeAt_app {im : Image} {b : Nat} {l1 l2 : List (BitVec 32)} (h : CodeAt im (pcOf b) (l1 ++ l2)) :
    CodeAt im (pcOf b) l1 ∧ CodeAt im (pcOf (b + l1.length)) l2 := by
  refine ⟨?_, codeAt_sub l1.length h (by simp) (by simp)⟩
  have := codeAt_sub 0 h (seg := l1) (by simp) (by simp)
  simpa using this

theorem len_search : Images.expandFtsSearch.length = 47 := by decide +kernel
theorem len_post : Images.expandFtsPost.length = 39 := by decide +kernel
theorem len_tramp : Images.expandFtsTramp.length = 1920 := by decide +kernel
theorem len_first : Images.expandFtsCopyFirst.length = 4096 := by decide +kernel
theorem len_k8 : Images.expandFtsCopyK8.length = 8192 := by decide +kernel

theorem ftsWin_parts :
    CodeAt Images.expandImage (pcOf 61000) Images.expandFtsSearch ∧
    CodeAt Images.expandImage (pcOf 61050) Images.expandFtsPost ∧
    CodeAt Images.expandImage (pcOf 61100) Images.expandFtsTramp ∧
    CodeAt Images.expandImage (pcOf 63488) Images.expandFtsCopyFirst ∧
    CodeAt Images.expandImage (pcOf 67584) Images.expandFtsCopyK8 ∧
    CodeAt Images.expandImage (pcOf 75776) Images.expandFtsCopyOdd := by
  obtain ⟨hs, h1⟩ := codeAt_app codeAt_ftsWin
  obtain ⟨_, h2⟩ := codeAt_app h1
  obtain ⟨hp, h3⟩ := codeAt_app h2
  obtain ⟨_, h4⟩ := codeAt_app h3
  obtain ⟨ht, h5⟩ := codeAt_app h4
  obtain ⟨_, h6⟩ := codeAt_app h5
  obtain ⟨hf, h7⟩ := codeAt_app h6
  obtain ⟨hk, ho⟩ := codeAt_app h7
  simp only [len_search, len_post, len_tramp, len_first, len_k8, List.length_replicate] at hp ht hf hk ho
  exact ⟨hs, hp, ht, hf, hk, ho⟩

theorem codeAt_search : CodeAt Images.expandImage (pcOf SEARCH) searchWords := by
  rw [show searchWords = Images.expandFtsSearch by decide +kernel]
  exact ftsWin_parts.1

theorem codeAt_post : CodeAt Images.expandImage (pcOf SigGolfCandidate.FtsGrind.POST)
    SigGolfCandidate.FtsGrind.postWords := by
  rw [show SigGolfCandidate.FtsGrind.postWords = Images.expandFtsPost by decide +kernel]
  exact ftsWin_parts.2.1

theorem codeAt_tramps : CodeAt Images.expandImage (pcOf TRAMP) Images.expandFtsTramp := ftsWin_parts.2.2.1
theorem codeAt_copyFirst : CodeAt Images.expandImage (pcOf 63488) Images.expandFtsCopyFirst := ftsWin_parts.2.2.2.1
theorem codeAt_copyK8 : CodeAt Images.expandImage (pcOf 67584) Images.expandFtsCopyK8 := ftsWin_parts.2.2.2.2.1
theorem codeAt_copyOdd : CodeAt Images.expandImage (pcOf 75776) Images.expandFtsCopyOdd := ftsWin_parts.2.2.2.2.2

theorem copyCodeAt_of {im : Image} {base : Nat} {words : List (BitVec 32)} (hb : base < 2 ^ 40)
    (h : CodeAt im (pcOf base) words) : ∀ i w, words[i]? = some w → im.code[base + i]? = some w := by
  have hc := h.2.2.2
  have hp : (pcOf base).toNat = 4096 + 4 * base := by
    simp only [pcOf, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp, show (4096 + 4 * base - 4096) / 4 = base by omega] at hc
  intro i word hi
  obtain ⟨hbound, hval⟩ := List.getElem?_eq_some_iff.mp hi
  have h := List.prefix_iff_getElem?.mp hc i hbound
  simpa only [List.getElem?_drop, hval] using h

/-! ### Copy prefixes

S5185 (FTS16, TIER2 E13): `copyPre j` now carries the level-2 site `jal zero, tramp2Of j` at `ecIdx j 3`; on A70 the
old `copyPre` made all twelve `copyOk*` batches FALSE (`#eval`), the restated ones evaluate to true (3 x 128). -/

def copyOkA (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFtsCopyFirst.drop (32 * j)).take (SharedAProof.copyPre j).length == SharedAProof.copyPre j
def copyOkB (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFtsCopyOdd.drop (64 * SharedBProof.cSlot j)).take (SharedBProof.copyPre j).length ==
    SharedBProof.copyPre j
def copyOkC (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFtsCopyK8.drop (64 * SharedCProof.cSlot j)).take (SharedCProof.copyPre j).length ==
    SharedCProof.copyPre j

theorem copyOkA_0 : copyOkA 0 32 = true := by decide +kernel
theorem copyOkA_1 : copyOkA 32 32 = true := by decide +kernel
theorem copyOkA_2 : copyOkA 64 32 = true := by decide +kernel
theorem copyOkA_3 : copyOkA 96 32 = true := by decide +kernel
theorem copyOkB_0 : copyOkB 0 32 = true := by decide +kernel
theorem copyOkB_1 : copyOkB 32 32 = true := by decide +kernel
theorem copyOkB_2 : copyOkB 64 32 = true := by decide +kernel
theorem copyOkB_3 : copyOkB 96 32 = true := by decide +kernel
theorem copyOkC_0 : copyOkC 0 32 = true := by decide +kernel
theorem copyOkC_1 : copyOkC 32 32 = true := by decide +kernel
theorem copyOkC_2 : copyOkC 64 32 = true := by decide +kernel
theorem copyOkC_3 : copyOkC 96 32 = true := by decide +kernel

theorem of_batches {f : Nat → Nat → Bool} {P : Nat → Prop}
    (hf : ∀ lo n, f lo n = true → ∀ j, lo ≤ j → j < lo + n → P j)
    (h0 : f 0 32 = true) (h1 : f 32 32 = true) (h2 : f 64 32 = true) (h3 : f 96 32 = true) :
    ∀ j < 128, P j := by
  intro j hj
  by_cases a : j < 32; · exact hf 0 32 h0 j (by omega) (by omega)
  by_cases b : j < 64; · exact hf 32 32 h1 j (by omega) (by omega)
  by_cases c : j < 96; · exact hf 64 32 h2 j (by omega) (by omega)
  exact hf 96 32 h3 j (by omega) (by omega)

theorem cSlotB_lt (j : Nat) (hj : j < 128) : SharedBProof.cSlot j < 128 := by
  unfold SharedBProof.cSlot; omega
theorem cSlotC_lt (j : Nat) (hj : j < 128) : SharedCProof.cSlot j < 128 := by
  unfold SharedCProof.cSlot; omega

theorem copyCode_A (j : Nat) (hj : j < 128) : SharedAProof.CopyCodeAt Images.expandImage j := by
  have hw := of_batches (f := copyOkA) (P := fun j =>
      (Images.expandFtsCopyFirst.drop (32 * j)).take (SharedAProof.copyPre j).length = SharedAProof.copyPre j)
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    copyOkA_0 copyOkA_1 copyOkA_2 copyOkA_3 j hj
  have hl : 32 * j + (SharedAProof.copyPre j).length ≤ Images.expandFtsCopyFirst.length := by
    have := congrArg List.length hw
    rw [List.length_take, List.length_drop] at this
    have hL : Images.expandFtsCopyFirst.length = 4096 := by decide
    omega
  have hc := codeAt_sub (32 * j) codeAt_copyFirst hl hw
  have hb : SharedAProof.copyBase j = 63488 + 32 * j := by
    unfold SharedAProof.copyBase SharedAProof.cSlot SigGolfCandidate.FtsGrind.COPY_FIRST; rfl
  rw [← hb] at hc
  exact copyCodeAt_of (by unfold SharedAProof.copyBase SharedAProof.cSlot SigGolfCandidate.FtsGrind.COPY_FIRST; omega) hc

theorem copyCode_B (j : Nat) (hj : j < 128) : SharedBProof.CopyCodeAt Images.expandImage j := by
  have hw := of_batches (f := copyOkB) (P := fun j =>
      (Images.expandFtsCopyOdd.drop (64 * SharedBProof.cSlot j)).take (SharedBProof.copyPre j).length =
        SharedBProof.copyPre j)
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    copyOkB_0 copyOkB_1 copyOkB_2 copyOkB_3 j hj
  have hl : 64 * SharedBProof.cSlot j + (SharedBProof.copyPre j).length ≤ Images.expandFtsCopyOdd.length := by
    have := congrArg List.length hw
    rw [List.length_take, List.length_drop] at this
    have hL : Images.expandFtsCopyOdd.length = 8192 := by decide
    have := cSlotB_lt j hj
    omega
  have hc := codeAt_sub (64 * SharedBProof.cSlot j) codeAt_copyOdd hl hw
  have hs := cSlotB_lt j hj
  have hb : SharedBProof.copyBase j = 75776 + 64 * SharedBProof.cSlot j := by
    unfold SharedBProof.copyBase SigGolfCandidate.FtsGrind.COPY_ODD; rfl
  rw [← hb] at hc
  exact copyCodeAt_of (by rw [hb]; omega) hc

theorem copyCode_C (j : Nat) (hj : j < 128) : SharedCProof.CopyCodeAt Images.expandImage j := by
  have hw := of_batches (f := copyOkC) (P := fun j =>
      (Images.expandFtsCopyK8.drop (64 * SharedCProof.cSlot j)).take (SharedCProof.copyPre j).length =
        SharedCProof.copyPre j)
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    copyOkC_0 copyOkC_1 copyOkC_2 copyOkC_3 j hj
  have hl : 64 * SharedCProof.cSlot j + (SharedCProof.copyPre j).length ≤ Images.expandFtsCopyK8.length := by
    have := congrArg List.length hw
    rw [List.length_take, List.length_drop] at this
    have hL : Images.expandFtsCopyK8.length = 8192 := by decide
    have := cSlotC_lt j hj
    omega
  have hc := codeAt_sub (64 * SharedCProof.cSlot j) codeAt_copyK8 hl hw
  have hs := cSlotC_lt j hj
  have hb : SharedCProof.copyBase j = 67584 + 64 * SharedCProof.cSlot j := by
    unfold SharedCProof.copyBase SigGolfCandidate.FtsGrind.COPY_K8; rfl
  rw [← hb] at hc
  exact copyCodeAt_of (by rw [hb]; omega) hc

/-! ### Trampolines -/

def trampOkA (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFtsTramp.drop (SharedAProof.trampOf j - TRAMP)).take 5 ==
    trampWords (SharedAProof.trampOf j) SEARCH (SharedAProof.siteB j + 1)
def trampOkB (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFtsTramp.drop (SharedBProof.trampOf j - TRAMP)).take 5 ==
    trampWords (SharedBProof.trampOf j) SEARCH (SharedBProof.siteB j + 1)
def trampOkC (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFtsTramp.drop (SharedCProof.trampOf j - TRAMP)).take 5 ==
    trampWords (SharedCProof.trampOf j) SEARCH (SharedCProof.siteB j + 1)

theorem trampOkA_0 : trampOkA 0 32 = true := by decide +kernel
theorem trampOkA_1 : trampOkA 32 32 = true := by decide +kernel
theorem trampOkA_2 : trampOkA 64 32 = true := by decide +kernel
theorem trampOkA_3 : trampOkA 96 32 = true := by decide +kernel
theorem trampOkB_0 : trampOkB 0 32 = true := by decide +kernel
theorem trampOkB_1 : trampOkB 32 32 = true := by decide +kernel
theorem trampOkB_2 : trampOkB 64 32 = true := by decide +kernel
theorem trampOkB_3 : trampOkB 96 32 = true := by decide +kernel
theorem trampOkC_0 : trampOkC 0 32 = true := by decide +kernel
theorem trampOkC_1 : trampOkC 32 32 = true := by decide +kernel
theorem trampOkC_2 : trampOkC 64 32 = true := by decide +kernel
theorem trampOkC_3 : trampOkC 96 32 = true := by decide +kernel

theorem tramp_code {t : Nat} {ws : List (BitVec 32)} (hlo : TRAMP ≤ t) (hhi : t + 5 ≤ TRAMP + 1920)
    (hlen : ws.length = 5) (h : (Images.expandFtsTramp.drop (t - TRAMP)).take 5 = ws) :
    CodeAt Images.expandImage (pcOf t) ws := by
  have hl : Images.expandFtsTramp.length = 1920 := by decide
  have hc := codeAt_sub (t - TRAMP) codeAt_tramps (by rw [hlen, hl]; omega) (by rw [hlen]; exact h)
  rwa [show TRAMP + (t - TRAMP) = t by omega] at hc

theorem trampWords_length (b target ret : Nat) : (trampWords b target ret).length = 5 := rfl

theorem tramp_A (j : Nat) (hj : j < 128) : CodeAt Images.expandImage (pcOf (SharedAProof.trampOf j))
    (trampWords (SharedAProof.trampOf j) SEARCH (SharedAProof.siteB j + 1)) := by
  have hw := of_batches (f := trampOkA) (P := fun j =>
      (Images.expandFtsTramp.drop (SharedAProof.trampOf j - TRAMP)).take 5 =
        trampWords (SharedAProof.trampOf j) SEARCH (SharedAProof.siteB j + 1))
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    trampOkA_0 trampOkA_1 trampOkA_2 trampOkA_3 j hj
  exact tramp_code (by unfold SharedAProof.trampOf; omega)
    (by unfold SharedAProof.trampOf SharedAProof.cSlot TRAMP; omega) (trampWords_length ..) hw

theorem tramp_B (j : Nat) (hj : j < 128) : CodeAt Images.expandImage (pcOf (SharedBProof.trampOf j))
    (trampWords (SharedBProof.trampOf j) SEARCH (SharedBProof.siteB j + 1)) := by
  have hw := of_batches (f := trampOkB) (P := fun j =>
      (Images.expandFtsTramp.drop (SharedBProof.trampOf j - TRAMP)).take 5 =
        trampWords (SharedBProof.trampOf j) SEARCH (SharedBProof.siteB j + 1))
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    trampOkB_0 trampOkB_1 trampOkB_2 trampOkB_3 j hj
  exact tramp_code (by unfold SharedBProof.trampOf; omega)
    (by unfold SharedBProof.trampOf SharedBProof.cSlot TRAMP; omega) (trampWords_length ..) hw

theorem tramp_C (j : Nat) (hj : j < 128) : CodeAt Images.expandImage (pcOf (SharedCProof.trampOf j))
    (trampWords (SharedCProof.trampOf j) SEARCH (SharedCProof.siteB j + 1)) := by
  have hw := of_batches (f := trampOkC) (P := fun j =>
      (Images.expandFtsTramp.drop (SharedCProof.trampOf j - TRAMP)).take 5 =
        trampWords (SharedCProof.trampOf j) SEARCH (SharedCProof.siteB j + 1))
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    trampOkC_0 trampOkC_1 trampOkC_2 trampOkC_3 j hj
  exact tramp_code (by unfold SharedCProof.trampOf; omega)
    (by unfold SharedCProof.trampOf SharedCProof.cSlot TRAMP; omega) (trampWords_length ..) hw

/-! ### S5185 (FTS16, TIER2 E12): the 384 level-2 trampolines

`tramp2Of j` (57216 + 5 (128 f + cSlot j)) is `trampWords (tramp2Of j) (s2Base (hiSel j 3)) (site2C j + 1)`: the
high-half search 57117 when `hiSel j 3` (bit 3 of `j` clear, even heap 16..30), else 57066 (`#eval`: 3 x 128 true). -/

def tramp2OkA (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFts16Code.drop (SharedAProof.tramp2Of j - SigGolfCandidate.FtsGrind.FTS16)).take 5 ==
    trampWords (SharedAProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedAProof.hiSel j 3))
      (SharedAProof.site2C j + 1)
def tramp2OkB (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFts16Code.drop (SharedBProof.tramp2Of j - SigGolfCandidate.FtsGrind.FTS16)).take 5 ==
    trampWords (SharedBProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedBProof.hiSel j 3))
      (SharedBProof.site2C j + 1)
def tramp2OkC (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (Images.expandFts16Code.drop (SharedCProof.tramp2Of j - SigGolfCandidate.FtsGrind.FTS16)).take 5 ==
    trampWords (SharedCProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedCProof.hiSel j 3))
      (SharedCProof.site2C j + 1)

theorem tramp2OkA_0 : tramp2OkA 0 32 = true := by decide +kernel
theorem tramp2OkA_1 : tramp2OkA 32 32 = true := by decide +kernel
theorem tramp2OkA_2 : tramp2OkA 64 32 = true := by decide +kernel
theorem tramp2OkA_3 : tramp2OkA 96 32 = true := by decide +kernel
theorem tramp2OkB_0 : tramp2OkB 0 32 = true := by decide +kernel
theorem tramp2OkB_1 : tramp2OkB 32 32 = true := by decide +kernel
theorem tramp2OkB_2 : tramp2OkB 64 32 = true := by decide +kernel
theorem tramp2OkB_3 : tramp2OkB 96 32 = true := by decide +kernel
theorem tramp2OkC_0 : tramp2OkC 0 32 = true := by decide +kernel
theorem tramp2OkC_1 : tramp2OkC 32 32 = true := by decide +kernel
theorem tramp2OkC_2 : tramp2OkC 64 32 = true := by decide +kernel
theorem tramp2OkC_3 : tramp2OkC 96 32 = true := by decide +kernel

theorem tramp2_code {t : Nat} {ws : List (BitVec 32)} (hlo : SigGolfCandidate.FtsGrind.TRAMP2 ≤ t)
    (hhi : t + 5 ≤ SigGolfCandidate.FtsGrind.TRAMP2 + 1920) (hlen : ws.length = 5)
    (h : (Images.expandFts16Code.drop (t - SigGolfCandidate.FtsGrind.FTS16)).take 5 = ws) :
    CodeAt Images.expandImage (pcOf t) ws := by
  have hl := SigGolfCandidate.FtsGrind.fts16_length
  have hc := codeAt_sub (t - SigGolfCandidate.FtsGrind.FTS16) SigGolfCandidate.FtsGrind.codeAt_fts16
    (by rw [hlen, hl]; unfold SigGolfCandidate.FtsGrind.TRAMP2 at hhi; unfold SigGolfCandidate.FtsGrind.FTS16; omega)
    (by rw [hlen]; exact h)
  rwa [show SigGolfCandidate.FtsGrind.FTS16 + (t - SigGolfCandidate.FtsGrind.FTS16) = t by
    unfold SigGolfCandidate.FtsGrind.TRAMP2 at hlo; unfold SigGolfCandidate.FtsGrind.FTS16; omega] at hc

theorem tramp2_A (j : Nat) (hj : j < 128) : CodeAt Images.expandImage (pcOf (SharedAProof.tramp2Of j))
    (trampWords (SharedAProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedAProof.hiSel j 3))
      (SharedAProof.site2C j + 1)) := by
  have hw := of_batches (f := tramp2OkA) (P := fun j =>
      (Images.expandFts16Code.drop (SharedAProof.tramp2Of j - SigGolfCandidate.FtsGrind.FTS16)).take 5 =
        trampWords (SharedAProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedAProof.hiSel j 3))
          (SharedAProof.site2C j + 1))
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    tramp2OkA_0 tramp2OkA_1 tramp2OkA_2 tramp2OkA_3 j hj
  exact tramp2_code (by unfold SharedAProof.tramp2Of; omega)
    (by unfold SharedAProof.tramp2Of SharedAProof.cSlot SigGolfCandidate.FtsGrind.TRAMP2; omega)
    (trampWords_length ..) hw

theorem tramp2_B (j : Nat) (hj : j < 128) : CodeAt Images.expandImage (pcOf (SharedBProof.tramp2Of j))
    (trampWords (SharedBProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedBProof.hiSel j 3))
      (SharedBProof.site2C j + 1)) := by
  have hw := of_batches (f := tramp2OkB) (P := fun j =>
      (Images.expandFts16Code.drop (SharedBProof.tramp2Of j - SigGolfCandidate.FtsGrind.FTS16)).take 5 =
        trampWords (SharedBProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedBProof.hiSel j 3))
          (SharedBProof.site2C j + 1))
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    tramp2OkB_0 tramp2OkB_1 tramp2OkB_2 tramp2OkB_3 j hj
  exact tramp2_code (by unfold SharedBProof.tramp2Of; omega)
    (by unfold SharedBProof.tramp2Of SharedBProof.cSlot SigGolfCandidate.FtsGrind.TRAMP2; omega)
    (trampWords_length ..) hw

theorem tramp2_C (j : Nat) (hj : j < 128) : CodeAt Images.expandImage (pcOf (SharedCProof.tramp2Of j))
    (trampWords (SharedCProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedCProof.hiSel j 3))
      (SharedCProof.site2C j + 1)) := by
  have hw := of_batches (f := tramp2OkC) (P := fun j =>
      (Images.expandFts16Code.drop (SharedCProof.tramp2Of j - SigGolfCandidate.FtsGrind.FTS16)).take 5 =
        trampWords (SharedCProof.tramp2Of j) (SigGolfCandidate.FtsGrind.s2Base (SharedCProof.hiSel j 3))
          (SharedCProof.site2C j + 1))
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    tramp2OkC_0 tramp2OkC_1 tramp2OkC_2 tramp2OkC_3 j hj
  exact tramp2_code (by unfold SharedCProof.tramp2Of; omega)
    (by unfold SharedCProof.tramp2Of SharedCProof.cSlot SigGolfCandidate.FtsGrind.TRAMP2; omega)
    (trampWords_length ..) hw

/- E8: the expand image's copy routines, trampolines and `SEARCH`. -/
/-- VR8: the expand image's node-8 region (235776..243967, bank chunks 921..952), equal to the pre-VR8
`expandSharedCode_921..952` (Merge060 `expand_node8_window`). -/
def expandNode8 : List (BitVec 32) :=
  ([Images.expandSharedCode_921, Images.expandSharedCode_922, Images.expandSharedCode_923,
    Images.expandSharedCode_924, Images.expandSharedCode_925, Images.expandSharedCode_926,
    Images.expandSharedCode_927, Images.expandSharedCode_928, Images.expandSharedCode_929,
    Images.expandSharedCode_930, Images.expandSharedCode_931, Images.expandSharedCode_932,
    Images.expandSharedCode_933, Images.expandSharedCode_934, Images.expandSharedCode_935,
    Images.expandSharedCode_936, Images.expandSharedCode_937, Images.expandSharedCode_938,
    Images.expandSharedCode_939, Images.expandSharedCode_940, Images.expandSharedCode_941,
    Images.expandSharedCode_942, Images.expandSharedCode_943, Images.expandSharedCode_944,
    Images.expandSharedCode_945, Images.expandSharedCode_946, Images.expandSharedCode_947,
    Images.expandSharedCode_948, Images.expandSharedCode_949, Images.expandSharedCode_950,
    Images.expandSharedCode_951, Images.expandSharedCode_952] : List (List (BitVec 32))).flatten
theorem expandNode8_length : expandNode8.length = 8192 := by decide +kernel
theorem codeAt_node8 : CodeAt Images.expandImage (pcOf 235776) expandNode8 := by
  have hp : (pcOf 235776).toNat = 4096 + 4 * 235776 := by
    simp [pcOf]
  have hlen := expandNode8_length
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hp, show (4096 + 4 * 235776 - 4096) / 4 = 235776 by omega]
  unfold expandNode8
  rw [← Images.expand_node8_window]
  exact List.take_prefix 8192 _

/-- VR8: the expand image keeps the pre-VR8 node-8 routines (`expandSharedCode_921 .. _952`); each
`SharedCProof.childWords j` sits at `childBase j` (pattern of `copyCode_C`: batches of
`(expandNode8.drop (64 * cSlot j)).take (childWords j).length = childWords j` plus one window check). -/
def bankOkC (lo n : Nat) : Bool := (List.range' lo n).all fun j =>
  (expandNode8.drop (64 * SharedCProof.cSlot j)).take (SharedCProof.childWords j).length ==
    SharedCProof.childWords j

theorem bankOkC_0 : bankOkC 0 32 = true := by decide +kernel
theorem bankOkC_1 : bankOkC 32 32 = true := by decide +kernel
theorem bankOkC_2 : bankOkC 64 32 = true := by decide +kernel
theorem bankOkC_3 : bankOkC 96 32 = true := by decide +kernel

theorem bankCode_C (j : Nat) (hj : j < 128) : SharedCProof.ChildCodeAt Images.expandImage j := by
  have hw := of_batches (f := bankOkC) (P := fun j =>
      (expandNode8.drop (64 * SharedCProof.cSlot j)).take (SharedCProof.childWords j).length =
        SharedCProof.childWords j)
    (fun lo n h j h1 h2 => by
      have := List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
      simpa only [beq_iff_eq] using this)
    bankOkC_0 bankOkC_1 bankOkC_2 bankOkC_3 j hj
  have hl : 64 * SharedCProof.cSlot j + (SharedCProof.childWords j).length ≤ expandNode8.length := by
    have := congrArg List.length hw
    rw [List.length_take, List.length_drop] at this
    have hs := cSlotC_lt j hj
    rw [expandNode8_length] at this ⊢
    omega
  have hc := codeAt_sub (64 * SharedCProof.cSlot j) codeAt_node8 hl hw
  have hs := cSlotC_lt j hj
  have hb : SharedCProof.childBase j = 235776 + 64 * SharedCProof.cSlot j := rfl
  rw [← hb] at hc
  exact copyCodeAt_of (by rw [hb]; omega) hc
theorem installed_copies : CopyCodes Images.expandImage :=
  ⟨codeAt_search, copyCode_A, copyCode_B, copyCode_C, bankCode_C, tramp_A, tramp_B, tramp_C,
    SigGolfCandidate.FtsGrind.codeAt_search2, tramp2_A, tramp2_B, tramp2_C⟩

end W9Drv.SharedBank
