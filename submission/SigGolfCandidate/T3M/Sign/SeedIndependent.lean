import SigGolfCandidate.T3M.Sign.Basic

namespace SigGolfCandidate.T3M.Sign.SeedIndependent
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open Keygen
def sub27S : List (BitVec 32) := [33171,0x79c0006f]
def sub29S : List (BitVec 32) := List.replicate 11 0x13
def sub40S : List (BitVec 32) := [2451]
def sub80S : List (BitVec 32) := [4824595,623715]
def sub120S : List (BitVec 32) := [6037011,3018291,134967,537857811,930563,9319299,7286819,8336419,134967,588189459,17707779,26096515,7286819,8336419,33857043,688915,0xfe6f3023,55221779,787347,0x580e42e3]
def sub157S : List (BitVec 32) := [1726995,0x5f00006f]
/-- Campaign T8D: the sign words at `1013 + 42 .. 1013 + 75` that the keygen image no longer shares (the keygen's
top hooks at 157/159..161/192 changed); the sign keeps its own copies so that `Keygen` edits cannot reach it.
Offsets 42..71 are dead in the T8D sign image (top seeds via TOPSEED/HORN, lower seeds via stage B's SEED). -/
def sub42S : List (BitVec 32) := [0x3ac1306f,67310179]
def sub44S : List (BitVec 32) := [1695251,17044243,34479891,31679283,1270547,295827,34152211,31712179,134711,7223331,8272931,132407,67110291,132663,67503635]
def sub59S : List (BitVec 32) := [115]
def sub60S : List (BitVec 32) := [1703443,5119507,134839,68062867,31329843,134967,487526163,930563,9319299,7286819,8336419,20647475]
def sub75S : List (BitVec 32) := [0x6750006f]
/-- Campaign T8D: the leaf prologue `1528..1541` ends with `j 1554` (PRE: `bne s0` / `jal ra,COEFGEN` / `j 1053`). -/
def hpS : List (BitVec 32) := [0xf49333,19071795,16978707,538141459,50601747,31679283,0xc100f13,59711251,31679283,134711,0x600e0e13,7223331,932899,0x340006f]
def hpmS : List (BitVec 32) := [17078931,538634899,0xfff40313,50533139,7006899,0xc100313,58921747,7006899,0xa75ff06f]
def norootS : List (BitVec 32) := [1049363,0xa06a08e3,0x961ff06f]
/-- The sign's leaf code at `b = 1013` (explicit: the shared `Keygen.sub_*` names only where the sign and keygen
words agree and the shared run lemmas are used). -/
def signSubL : Rv.Layout := [(0, sub_0), (1, sub_1), (2, sub_2), (8, sub_8), (9, sub_9), (23, sub_23), (24, sub_24),
  (26, sub_26), (27, sub27S), (29, sub29S), (40, sub40S), (41, sub_41), (42, sub42S), (44, sub44S), (59, sub59S),
  (60, sub60S), (72, sub_72), (73, sub_73), (75, sub75S), (76, sub_76), (77, sub_77), (78, sub_78), (79, sub_79),
  (80, sub80S), (82, sub_82), (83, sub_83), (92, sub_92), (95, sub_95), (96, sub_96), (105, sub_105), (106, sub_106),
  (112, sub_112), (113, sub_113), (116, sub_116), (117, sub_117), (118, sub_118), (120, sub120S), (140, sub_140),
  (146, sub_146), (147, sub_147), (157, sub157S), (159, sub_159)]
def SeedIndependentAt (image : Image) (b : Nat) : Prop :=
  (∀ off code, (off, code) ∈ signSubL → CodeAt image (pcOf (b + off)) code) ∧
  (b = 117 ∨ b = 1013) ∧
  (CodeAt image (pcOf (b + 1000)) Sign.maxDigitCodeS ∧
   CodeAt image (pcOf (b + 1004)) revCode ∧
   (image = Images.signImage ∧ b = 1013))
private theorem signSubL_ok : layoutOk 0 signSubL = true := by decide +kernel
private theorem signSubAt : CodeAt Images.signImage (pcOf 1013) (layoutCode signSubL) :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem seedIndependentAt_sign : SeedIndependentAt Images.signImage 1013 := by
  refine ⟨?_, Or.inr rfl, Sign.codeAt_maxDigit, Sign.codeAt_2017, rfl, rfl⟩
  intro off code hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact codeAt_sublayout signSubAt signSubL_ok hi
theorem codeAt_sub_0 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 0)) sub_0 :=
  h.1 0 sub_0 (by decide +kernel)
theorem codeAt_sub_1 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1)) sub_1 :=
  h.1 1 sub_1 (by decide +kernel)
theorem codeAt_sub_2 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 2)) sub_2 :=
  h.1 2 sub_2 (by decide +kernel)
theorem codeAt_sub_8 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 8)) sub_8 :=
  h.1 8 sub_8 (by decide +kernel)
theorem codeAt_sub_9 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 9)) sub_9 :=
  h.1 9 sub_9 (by decide +kernel)
theorem codeAt_sub_23 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 23)) sub_23 :=
  h.1 23 sub_23 (by decide +kernel)
theorem codeAt_sub_24 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 24)) sub_24 :=
  h.1 24 sub_24 (by decide +kernel)
theorem codeAt_sub_26 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 26)) sub_26 :=
  h.1 26 sub_26 (by decide +kernel)
theorem codeAt_sub27S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 27)) sub27S :=
  h.1 27 sub27S (by decide +kernel)
theorem codeAt_sub40S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 40)) sub40S :=
  h.1 40 sub40S (by decide +kernel)
theorem codeAt_sub_41 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 41)) sub_41 :=
  h.1 41 sub_41 (by decide +kernel)
theorem codeAt_sub_72 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 72)) sub_72 :=
  h.1 72 sub_72 (by decide +kernel)
theorem codeAt_sub_73 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 73)) sub_73 :=
  h.1 73 sub_73 (by decide +kernel)
theorem codeAt_sub_75 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 75)) sub75S :=
  h.1 75 sub75S (by decide +kernel)
theorem codeAt_sub_76 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 76)) sub_76 :=
  h.1 76 sub_76 (by decide +kernel)
theorem codeAt_sub_77 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 77)) sub_77 :=
  h.1 77 sub_77 (by decide +kernel)
theorem codeAt_sub_78 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 78)) sub_78 :=
  h.1 78 sub_78 (by decide +kernel)
theorem codeAt_sub_79 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 79)) sub_79 :=
  h.1 79 sub_79 (by decide +kernel)
theorem codeAt_sub80S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 80)) sub80S :=
  h.1 80 sub80S (by decide +kernel)
theorem codeAt_sub_82 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 82)) sub_82 :=
  h.1 82 sub_82 (by decide +kernel)
theorem codeAt_sub_83 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 83)) sub_83 :=
  h.1 83 sub_83 (by decide +kernel)
theorem codeAt_sub_92 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 92)) sub_92 :=
  h.1 92 sub_92 (by decide +kernel)
theorem codeAt_sub_95 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 95)) sub_95 :=
  h.1 95 sub_95 (by decide +kernel)
theorem codeAt_sub_96 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 96)) sub_96 :=
  h.1 96 sub_96 (by decide +kernel)
theorem codeAt_sub_105 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 105)) sub_105 :=
  h.1 105 sub_105 (by decide +kernel)
theorem codeAt_sub_106 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 106)) sub_106 :=
  h.1 106 sub_106 (by decide +kernel)
theorem codeAt_sub_112 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 112)) sub_112 :=
  h.1 112 sub_112 (by decide +kernel)
theorem codeAt_sub_113 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 113)) sub_113 :=
  h.1 113 sub_113 (by decide +kernel)
theorem codeAt_sub_116 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 116)) sub_116 :=
  h.1 116 sub_116 (by decide +kernel)
theorem codeAt_sub_117 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 117)) sub_117 :=
  h.1 117 sub_117 (by decide +kernel)
theorem codeAt_sub_118 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 118)) sub_118 :=
  h.1 118 sub_118 (by decide +kernel)
theorem codeAt_sub120S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 120)) sub120S :=
  h.1 120 sub120S (by decide +kernel)
theorem codeAt_sub_140 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 140)) sub_140 :=
  h.1 140 sub_140 (by decide +kernel)
theorem codeAt_sub_146 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 146)) sub_146 :=
  h.1 146 sub_146 (by decide +kernel)
theorem codeAt_sub_147 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 147)) sub_147 :=
  h.1 147 sub_147 (by decide +kernel)
theorem codeAt_sub157S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 157)) sub157S :=
  h.1 157 sub157S (by decide +kernel)
theorem codeAt_sub_159 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 159)) sub_159 :=
  h.1 159 sub_159 (by decide +kernel)
theorem codeAt_rev {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1004)) revCode := h.2.2.2.1
theorem codeAt_maxLow {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1000)) Sign.maxLowS := by
  have q := codeAt_sublayout (L := Sign.maxLayoutS) (b := b + 1000) h.2.2.1 Sign.maxLayoutS_ok
    (i := 0) (o := 0) (seg := Sign.maxLowS) (by kernel_rfl)
  simpa only [Nat.add_zero] using q
theorem codeAt_maxHigh {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 1002)) maxHigh := by
  have q := codeAt_sublayout (L := Sign.maxLayoutS) (b := b + 1000) h.2.2.1 Sign.maxLayoutS_ok
    (i := 1) (o := 2) (seg := maxHigh) (by kernel_rfl)
  simpa [Nat.add_assoc] using q
theorem codeAt_sub_61 {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 61)) (sub_60.drop 1) := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hpS {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1528) hpS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_hpmS {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1542) hpmS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_norootS {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf 1551) norootS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
def norootJ : List (BitVec 32) := [0x961ff06f]
theorem codeAt_norootJ {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf 1553) norootJ := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem b_eq {image : Image} {b : Nat} (h : SeedIndependentAt image b) : b = 1013 := h.2.2.2.2.2
/-- Campaign T8D: PRE at 1554 (`bne s0,zero,1053`). -/
def preS : List (BitVec 32) := [0x820416e3]
theorem codeAt_preS {image : Image} {b : Nat} (h : SeedIndependentAt image b) : CodeAt image (pcOf 1554) preS := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
/-- Campaign T8D: the top chains enter the old seed copy at `b + 71` (`add t3,s6,s3`) after TOPSEED. -/
def sub71S : List (BitVec 32) := [20647475]
theorem codeAt_sub71S {image : Image} {b : Nat} (h : SeedIndependentAt image b) :
    CodeAt image (pcOf (b + 71)) sub71S := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  exact codeAt_sign_slice (by decide +kernel) (by decide +kernel)
sym_block blkS_27 := symRun { noAlias := true } sub27S (pcOf (1013 + 27)) 100
sym_block blkS_40 := symRun { noAlias := true } sub40S (pcOf (1013 + 40)) 100
sym_block blkS_80 := symRun { noAlias := true } sub80S (pcOf (1013 + 80)) 100
sym_block blkS_120 := symRun { noAlias := true } sub120S (pcOf (1013 + 120)) 100
sym_block blkS_157 := symRun { noAlias := true } sub157S (pcOf (1013 + 157)) 100
sym_block blkS_hp := symRun { noAlias := true } hpS (pcOf 1528) 100
sym_block blkS_hpm := symRun { noAlias := true } hpmS (pcOf 1542) 100
sym_block blkS_noroot := symRun { noAlias := true } norootS (pcOf 1551) 100
sym_block blkS_nrj := symRun { noAlias := true } norootJ (pcOf 1553) 100
sym_block blkS_pre := symRun { noAlias := true } preS (pcOf 1554) 100
sym_block blkS_71 := symRun { noAlias := true } sub71S (pcOf (1013 + 71)) 100
sym_block blkS_75 := symRun { noAlias := true } sub75S (pcOf (1013 + 75)) 100
sym_block blkS_maxLow := symRun { noAlias := true } Sign.maxLowS (pcOf (1013 + 1000)) 100
end SigGolfCandidate.T3M.Sign.SeedIndependent
