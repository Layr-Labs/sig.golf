import SigGolfCandidate.Merge047
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge055

-- ==== merged from T3M_Search_Blocks ====
section

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def dsE_0 : List (BitVec 32) := [1049399,0x50698663]
def dsS_0 : List (BitVec 32) := [1049399,0x60698a63]
def ds_0 (d : Nat) : List (BitVec 32) := if d = 30 then dsE_0 else dsS_0
def ds_2 (_d : Nat) : List (BitVec 32) := [4919,787,627603,134711,302910995,7223331,8272931,132407,302318867,67110291,132663,369493523]
def ds_14 (_d : Nat) : List (BitVec 32) := [115]
def dsE_15 : List (BitVec 32) := [348131567]
def dsS_15 : List (BitVec 32) := [0x74010ef]
def ds_15 (d : Nat) : List (BitVec 32) := if d = 30 then dsE_15 else dsS_15
def ds_16 (_d : Nat) : List (BitVec 32) := [431715]
def ds_17 (_d : Nat) : List (BitVec 32) := [1673619,0xfb9ff06f]
def dsL (d : Nat) : Rv.Layout := [(0, ds_0 d), (2, ds_2 d), (14, ds_14 d), (15, ds_15 d), (16, ds_16 d), (17, ds_17 d)]
theorem dsL_ok (d : Nat) : layoutOk 0 (dsL d) = true := by
  unfold dsL; by_cases h : d = 30 <;> simp [h, ds_0, ds_2, ds_14, ds_15, ds_16, ds_17, dsE_0, dsS_0, dsE_15, dsS_15, layoutOk]
def DsAt (image : Image) (d b : Nat) : Prop :=
  (CodeAt image (pcOf d) (layoutCode (dsL d)) ∧ GateAt image b) ∧ (d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543)
theorem codeAt_ds_0 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 0)) (ds_0 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 0) rfl
theorem codeAt_ds_2 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 2)) (ds_2 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 1) rfl
theorem codeAt_ds_14 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 14)) (ds_14 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 2) rfl
theorem codeAt_ds_15 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 15)) (ds_15 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 3) rfl
theorem codeAt_ds_16 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 16)) (ds_16 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 4) rfl
theorem codeAt_ds_17 {image : Image} {d b : Nat} (h : DsAt image d b) :
    CodeAt image (pcOf (d + 17)) (ds_17 d) :=
  codeAt_sublayout h.1.1 (dsL_ok d) (i := 5) rfl
theorem dsAt_of {image : Image} {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543)
    (h : (image.code.drop d).take 19 = layoutCode (dsL d)) (hg : GateAt image b) : DsAt image d b := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, hg⟩, hdb⟩
  · rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · rw [← h]
    have e : (pcOf d).toNat = 0x1000 + 4 * d := by rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [e, show (0x1000 + 4 * d - 0x1000) / 4 = d by omega]
    exact List.take_prefix _ _
sym_block blkds30_0 := symRun { noAlias := true } (ds_0 30) (pcOf (30 + 0)) 100
sym_block blkds153_0 := symRun { noAlias := true } (ds_0 153) (pcOf (153 + 0)) 100
sym_block blkds30_2 := symRun { noAlias := true } (ds_2 30) (pcOf (30 + 2)) 100
sym_block blkds153_2 := symRun { noAlias := true } (ds_2 153) (pcOf (153 + 2)) 100
sym_block blkds30_15 := symRun { noAlias := true } (ds_15 30) (pcOf (30 + 15)) 100
sym_block blkds153_15 := symRun { noAlias := true } (ds_15 153) (pcOf (153 + 15)) 100
sym_block blkds30_16 := symRun { noAlias := true } (ds_16 30) (pcOf (30 + 16)) 100
sym_block blkds153_16 := symRun { noAlias := true } (ds_16 153) (pcOf (153 + 16)) 100
sym_block blkds30_17 := symRun { noAlias := true } (ds_17 30) (pcOf (30 + 17)) 100
sym_block blkds153_17 := symRun { noAlias := true } (ds_17 153) (pcOf (153 + 17)) 100
def stds_0 : SymState := blkds30_0.res.st
def pcEds_0 (d b : Nat) : E := rebase blkds30_0.res.pc (pcOf b) (pcOf (d + 2))
theorem run_ds0 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_0 d) (pcOf (d + 0)) 100 =
      some ⟨stds_0, pcEds_0 d b, blkds30_0.res.stop, blkds30_0.res.steps, blkds30_0.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_0.trans (congrArg some (by kernel_rfl))
  · exact blkds153_0.trans (congrArg some (by kernel_rfl))
def stds_2 : SymState := blkds30_2.res.st
def pcEds_2 (d b : Nat) : E := .c (pcOf (d + 14))
theorem run_ds2 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_2 d) (pcOf (d + 2)) 100 =
      some ⟨stds_2, pcEds_2 d b, blkds30_2.res.stop, blkds30_2.res.steps, blkds30_2.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_2.trans (congrArg some (by kernel_rfl))
  · exact blkds153_2.trans (congrArg some (by kernel_rfl))
def stds_15 (d : Nat) : SymState := { blkds30_15.res.st with regs := blkds30_15.res.st.regs.set Reg.x1 (.c (pcOf (d + 16))) }
def pcEds_15 (d b : Nat) : E := .c (pcOf (gatePc b))
theorem run_ds15 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_15 d) (pcOf (d + 15)) 100 =
      some ⟨stds_15 d, pcEds_15 d b, blkds30_15.res.stop, blkds30_15.res.steps, blkds30_15.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_15.trans (congrArg some (by kernel_rfl))
  · exact blkds153_15.trans (congrArg some (by kernel_rfl))
def stds_16 : SymState := blkds30_16.res.st
def pcEds_16 (d b : Nat) : E := rebase blkds30_16.res.pc (pcOf (d + 19)) (pcOf (d + 17))
theorem run_ds16 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_16 d) (pcOf (d + 16)) 100 =
      some ⟨stds_16, pcEds_16 d b, blkds30_16.res.stop, blkds30_16.res.steps, blkds30_16.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_16.trans (congrArg some (by kernel_rfl))
  · exact blkds153_16.trans (congrArg some (by kernel_rfl))
def stds_17 : SymState := blkds30_17.res.st
def pcEds_17 (d b : Nat) : E := .c (pcOf (d + 0))
theorem run_ds17 {d b : Nat} (hdb : d = 30 ∧ b = 354 ∨ d = 153 ∧ b = 543) :
    symRun { noAlias := true } (ds_17 d) (pcOf (d + 17)) 100 =
      some ⟨stds_17, pcEds_17 d b, blkds30_17.res.stop, blkds30_17.res.steps, blkds30_17.res.cycles⟩ := by
  rcases hdb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkds30_17.trans (congrArg some (by kernel_rfl))
  · exact blkds153_17.trans (congrArg some (by kernel_rfl))
end SigGolfCandidate.T3M.Search
end
-- ==== merged from T3M_Expand_Blocks ====
section

section
namespace SigGolfCandidate.T3M
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def expandCurrentCodeChunks : List (List (BitVec 32)) := [Images.expandCode_0, Images.expandCode_1, Images.expandCode_2, Images.expandCode_3, Images.expandCode_4, Images.expandCode_5, Images.expandCode_6, Images.expandCode_7, Images.expandCode_8, Images.expandCode_9, Images.expandCode_10, Images.expandCode_11, Images.expandCode_12, Images.expandCode_13, Images.expandCode_14, Images.expandCode_15, Images.expandCode_16, Images.expandCode_17, Images.expandCode_18, Images.expandCode_19, Images.expandCode_20, Images.expandCode_21, Images.expandCode_22, Images.expandCode_23, Images.expandCode_24, Images.expandCode_25, Images.expandCode_26, Images.expandCode_27, Images.expandCode_28, Images.expandCode_29, Images.expandCode_30, Images.expandCode_31, Images.expandCode_32, Images.expandCode_33, Images.expandCode_34, Images.expandCode_35, Images.expandCode_36, Images.expandCode_37, Images.expandCode_38, Images.expandCode_39, Images.expandCode_40, Images.expandCode_41, Images.expandCode_42, Images.expandCode_43, Images.expandCode_44, Images.expandCode_45, Images.expandCode_46, Images.expandCode_47, Images.expandCode_48, Images.expandCode_49, Images.expandCode_50, Images.expandCode_51, Images.expandCode_52, Images.expandCode_53, Images.expandCode_54, Images.expandCode_55, Images.expandCode_56, Images.expandCode_57, Images.expandCode_58, Images.expandCode_59, Images.expandCode_60, Images.expandCode_61, Images.expandCode_62, Images.expandCode_63, Images.expandCode_64, Images.expandCode_65, Images.expandCode_66, Images.expandCode_67, Images.expandCode_68, Images.expandCode_69, Images.expandCode_70, Images.expandCode_71, Images.expandCode_72, Images.expandCode_73, Images.expandCode_74, Images.expandCode_75, Images.expandCode_76, Images.expandCode_77, Images.expandCode_78, Images.expandCode_79, Images.expandCode_80, Images.expandCode_81, Images.expandCode_82, Images.expandCode_83, Images.expandCode_84, Images.expandCode_85, Images.expandCode_86, Images.expandCode_87, Images.expandCode_88, Images.expandCode_89, Images.expandCode_90, Images.expandCode_91, Images.expandCode_92, Images.expandCode_93, Images.expandCode_94, Images.expandCode_95, Images.expandCode_96, Images.expandCode_97, Images.expandCode_98, Images.expandCode_99, Images.expandCode_100, Images.expandCode_101, Images.expandCode_102, Images.expandCode_103, Images.expandCode_104, Images.expandCode_105, Images.expandCode_106, Images.expandCode_107, Images.expandCode_108, Images.expandCode_109, Images.expandCode_110, Images.expandCode_111, Images.expandCode_112, Images.expandCode_113, Images.expandCode_114, Images.expandCode_115, Images.expandCode_116, Images.expandCode_117, Images.expandCode_118, Images.expandCode_119, Images.expandCode_120, Images.expandCode_121, Images.expandCode_122, Images.expandCode_123, Images.expandCode_124, Images.expandCode_125, Images.expandCode_126, Images.expandCode_127, Images.expandCode_128, Images.expandCode_129, Images.expandCode_130, Images.expandCode_131, Images.expandCode_132, Images.expandCode_133, Images.expandCode_134, Images.expandCode_135, Images.expandCode_136, Images.expandCode_137, Images.expandCode_138, Images.expandCode_139, Images.expandCode_140, Images.expandCode_141, Images.expandCode_142, Images.expandCode_143, Images.expandCode_144, Images.expandCode_145, Images.expandCode_146, Images.expandCode_147, Images.expandCode_148, Images.expandCode_149, Images.expandCode_150, Images.expandCode_151, Images.expandCode_152, Images.expandCode_153, Images.expandCode_154, Images.expandCode_155, Images.expandCode_156, Images.expandCode_157, Images.expandCode_158, Images.expandCode_159, Images.expandCode_160, Images.expandCode_161, Images.expandCode_162, Images.expandCode_163, Images.expandCode_164, Images.expandCode_165, Images.expandCode_166, Images.expandCode_167, Images.expandCode_168, Images.expandCode_169, Images.expandCode_170, Images.expandCode_171, Images.expandCode_172]
private theorem foldl_chunks (cs : List (List (BitVec 32))) (acc : List (BitVec 32)) :
    cs.foldl (· ++ ·) acc = acc ++ cs.flatten := by
  induction cs generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
  | cons c cs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]
theorem expandCurrentCode_flatten : Images.expandCode = expandCurrentCodeChunks.flatten := by
  change expandCurrentCodeChunks.foldl (· ++ ·) [] = expandCurrentCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_expand_current_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (expandCurrentCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.expandImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.expandCode.drop b).take code.length = code
  rw [expandCurrentCode_flatten]
  exact h
/-- Skip whole image chunks before reducing a small code slice. -/
def expandCurrentCodeTail (b : Nat) : List (BitVec 32) :=
  (expandCurrentCodeChunks.drop (b / 256)).flatten.drop (b % 256)
set_option maxRecDepth 100000 in
private theorem expandCurrentCodeChunks_ok :
    (expandCurrentCodeChunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel
private theorem expandCurrentCodeChunks_length : expandCurrentCodeChunks.length = 173 := by
  decide +kernel
private theorem expand_current_drop_chunks : ∀ (cs : List (List (BitVec 32))) (k : Nat),
    (cs.dropLast.all fun c => c.length == 256) = true → k < cs.length →
    cs.flatten.drop (256 * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show 256 * (k + 1) = c.length + 256 * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this
theorem expandCurrentCodeTail_eq (b : Nat) (hb : b / 256 < 173) :
    expandCurrentCodeTail b = expandCurrentCodeChunks.flatten.drop b := by
  unfold expandCurrentCodeTail
  rw [← expand_current_drop_chunks expandCurrentCodeChunks (b / 256) expandCurrentCodeChunks_ok
    (by rw [expandCurrentCodeChunks_length]; exact hb), List.drop_drop]
  congr 1
  omega
theorem codeAt_expand_current_chunk {b : Nat} {code : List (BitVec 32)}
    (hi : b / 256 < 173)
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (expandCurrentCodeTail b).take code.length = code) :
    CodeAt Images.expandImage (pcOf b) code := by
  apply codeAt_expand_current_slice hb
  rw [← expandCurrentCodeTail_eq b hi]
  exact h
private theorem expand_drop_chunks : ∀ (cs : List (List (BitVec 32))) (k : Nat),
    (cs.dropLast.all fun c => c.length == 256) = true → k < cs.length →
    cs.flatten.drop (256 * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show 256 * (k + 1) = c.length + 256 * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this
/-- The final chunk may hold appended producer code beyond the original chunk grid. -/
theorem expandCodeTailLast_eq (b : Nat) (hlo : 44032 ≤ b) :
    Images.expandCode_172.drop (b - 44032) = expandCurrentCodeChunks.flatten.drop b := by
  have hd := expand_current_drop_chunks expandCurrentCodeChunks 172 expandCurrentCodeChunks_ok
    (by rw [expandCurrentCodeChunks_length]; decide)
  have hx : expandCurrentCodeChunks.drop 172 = [Images.expandCode_172] := by rfl
  rw [hx, List.flatten_cons, List.flatten_nil, List.append_nil] at hd
  have he : expandCurrentCodeChunks.flatten.drop 44032 = Images.expandCode_172 := hd
  rw [show b = 44032 + (b - 44032) by omega, ← List.drop_drop, he]
  simp only [Nat.add_sub_cancel_left]

theorem codeAt_expand_last {b : Nat} {code : List (BitVec 32)}
    (hlo : 44032 ≤ b) (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (hc : (Images.expandCode_172.drop (b - 44032)).take code.length = code) :
    CodeAt Images.expandImage (pcOf b) code := by
  apply codeAt_expand_current_slice hb
  rw [← expandCodeTailLast_eq b hlo]
  exact hc

/-- A sub-window of a checked code window (no new kernel check of the image). -/
theorem codeAt_sub {image : Image} {b : Nat} {code seg : List (BitVec 32)} (o : Nat)
    (hc : CodeAt image (pcOf b) code) (hlen : o + seg.length ≤ code.length)
    (h : (code.drop o).take seg.length = seg) :
    CodeAt image (pcOf (b + o)) seg := by
  have hsplit : code = code.take o ++ seg ++ (code.drop o).drop seg.length := by
    conv_lhs => rw [← List.take_append_drop o code, ← List.take_append_drop seg.length (code.drop o), h]
    simp only [List.append_assoc]
  rw [hsplit] at hc
  have := CodeAt.drop_prefix hc
  have hl : (code.take o).length = o := by rw [List.length_take]; omega
  rw [hl, ofNat_add_ofNat] at this
  rwa [pcOf, show 0x1000 + 4 * (b + o) = 0x1000 + 4 * b + 4 * o by ring]

/-- Campaign T51: the new expand code 54176..54738 (shared top kernel 54176, unpacker 54356, KCOPY 54522, KMAX
54532, GT 54543, ZB 54553, DEC 54569), checked once against the image; every T51 block is a `codeAt_sub` of it. -/
def t51Code : List (BitVec 32) := [
  0xa0537,0xa050513,0xa13,0xc00a93,0x231e13,0x3fce7e13,0xae0e33,0xf60e6c83,
  0xccde93,0x4efe93,0x1dc8cb3,0x635e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,
  0xe35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x1635e13,0x3fce7e13,0xae0e33,
  0xe6e83,0x1dc8cb3,0x1e35e13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x2635e13,
  0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0x2e35e13,0x3fce7e13,0xae0e33,0xe6e83,
  0x1dc8cb3,0x3635e13,0x1fce7e13,0x13ce3e93,0x120e9863,0xae0e33,0x4c4e6e83,0x1dc8cb3,
  0x3f35f13,0x139e13,0x1cf6f33,0x2f1e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,
  0x5f5e13,0x1fce7e13,0xae0e33,0x400e6583,0xcf5e13,0x1fce7e13,0xae0e33,0x400e6e83,
  0x1d585b3,0x13f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1d585b3,0x1af5e13,0x1fce7e13,
  0xae0e33,0x400e6e83,0x1dc8cb3,0x21f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,
  0x28f5e13,0x1fce7e13,0xae0e33,0x400e6e83,0x1dc8cb3,0x2e3de13,0x3fce7e13,0xae0e33,
  0xe6e83,0x1dc8cb3,0x363de13,0x3fce7e13,0xae0e33,0xe6e83,0x1dc8cb3,0xbc8cb3,
  0x125d593,0xf5f593,0x16cde13,0x41c88e33,0x6e3e93,0x40e8663,0x8cde93,0x3fefe93,
  0x1e3f13,0x1ee8eb3,0x8ebe93,0x20e8a63,0xffcfe93,0x40be8eb3,0xffce0f13,0x1f3f13,
  0x1ee8eb3,0x15ece63,0xa1463,0x2e8e93,0x66f37,0x5df3023,0x7f4f3c23,0xf40006f,
  0x20a1063,0x3e3de93,0xe8c63,0x8000a13,0xe00a93,0x1063303,0x1863383,0xe15ff06f,
  0xc59cb06f,0x13,0x13,0x13,0x13,0x13,0x13,0x13,
  0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,
  0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,
  0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,
  0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,
  0x13,0x13,0x13,0x13,0x13,0x13,0x13,0x13,
  0x13,0x13,0x13,0x13,0x20537,0x42050513,0x3c50923,0x600f13,
  0x500593,0x3f35c93,0x139e93,0x1dcecb3,0xff37e13,0xfd8e0e13,0x3ee7eb3,0x1d50023,
  0x3ee5e33,0x3ee7eb3,0x1d500a3,0x3ee5eb3,0x1d50123,0x835e13,0xffe7e13,0x3ee7eb3,
  0x1d501a3,0x3ee5e33,0x3ee7eb3,0x1d50223,0x3ee5eb3,0x1d502a3,0x1035e13,0xffe7e13,
  0x3ee7eb3,0x1d50323,0x3ee5e33,0x3ee7eb3,0x1d503a3,0x3ee5eb3,0x1d50423,0x1835e13,
  0xffe7e13,0x3ee7eb3,0x1d504a3,0x3ee5e33,0x3ee7eb3,0x1d50523,0x3ee5eb3,0x1d505a3,
  0x2035e13,0xffe7e13,0x3ee7eb3,0x1d50623,0x3ee5e33,0x3ee7eb3,0x1d506a3,0x3ee5eb3,
  0x1d50723,0x2835e13,0xffe7e13,0x3ee7eb3,0x1d507a3,0x3ee5e33,0x3ee7eb3,0x1d50823,
  0x3ee5eb3,0x1d508a3,0x3035e13,0xffe7e13,0x3ee7eb3,0x1d50923,0x3ee5e33,0x3ee7eb3,
  0x1d509a3,0x3ee5eb3,0x1d50a23,0x303de13,0xffe7e13,0x3ee7eb3,0x1d50aa3,0x3ee5e33,
  0x3ee7eb3,0x1d50b23,0x3ee5eb3,0x1d50ba3,0x383de13,0x3ee7eb3,0x1d50c23,0x3ee5e33,
  0x3ee7eb3,0x1d50ca3,0x3ee5eb3,0x1d50d23,0x7fcfe13,0x7fe4e13,0x2be7eb3,0x1d50da3,
  0x2be5e33,0x2be7eb3,0x1d50e23,0x2be5eb3,0x1d50ea3,0x7cde13,0x7fe7e13,0x7fe4e13,
  0x2be7eb3,0x1d50f23,0x2be5e33,0x2be7eb3,0x1d50fa3,0x2be5eb3,0x3d50023,0xecde13,
  0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d500a3,0x2be5e33,0x2be7eb3,0x3d50123,0x2be5eb3,
  0x3d501a3,0x15cde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d50223,0x2be5e33,0x2be7eb3,
  0x3d502a3,0x2be5eb3,0x3d50323,0x1ccde13,0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d503a3,
  0x2be5e33,0x2be7eb3,0x3d50423,0x2be5eb3,0x3d504a3,0x23cde13,0x7fe7e13,0x7fe4e13,
  0x2be7eb3,0x3d50523,0x2be5e33,0x2be7eb3,0x3d505a3,0x2be5eb3,0x3d50623,0x2acde13,
  0x7fe7e13,0x7fe4e13,0x2be7eb3,0x3d506a3,0x2be5e33,0x2be7eb3,0x3d50723,0x2be5eb3,
  0x3d507a3,0x3835e13,0x7fe7e13,0x7fe4e13,0x700f13,0x3ee7eb3,0x3d50823,0x3ee5eb3,
  0x3d508a3,0x8067,0xa0eb7,0xffae37,0xe00e0e13,0x768e0f13,0xe3303,0x6eb023,
  0x8e0e13,0x8e8e93,0xffee68e3,0xb18cb06f,0x500a93,0x1b00e13,0x3c9c063,0x400a93,
  0x3000e13,0x1c9ca63,0x600a93,0x3200e13,0x1c9c463,0x500a93,0xbe5cb06f,0x400313,
  0xfe598393,0x153b393,0x40730333,0xfd098393,0x13b393,0x730333,0x99463,0x700313,
  0xe2dfa06f,0x713,0xf93,0x300e13,0x3c6c863,0xffd68713,0x71463,0x100713,
  0x4000e13,0x40ee0e33,0xfff00f93,0x1cf9fb3,0xb00e13,0x1c69663,0xff00f93,0x28f9f93,
  0xe9df406f,0x913,0x8e37,0xa88e0e13,0xe3303,0x3f35393,0x796933,0x131313,
  0x135313,0x6e3023,0x8e37,0xa98e0e13,0xe3303,0x3f35393,0x139393,0x796933,
  0x131313,0x135313,0x6e3023,0x8e37,0xaa8e0e13,0xe3303,0x3e35393,0x239393,
  0x796933,0x231313,0x235313,0x6e3023,0x8e37,0xab8e0e13,0xe3303,0x3d35393,
  0x439393,0x796933,0x331313,0x335313,0x6e3023,0x8e37,0xac8e0e13,0xe3303,
  0x3c35393,0x739393,0x796933,0x431313,0x435313,0x6e3023,0x8e37,0xad8e0e13,
  0xe3303,0x3b35393,0xb39393,0x796933,0x531313,0x535313,0x6e3023,0x8e37,
  0xae8e0e13,0xe3303,0x3a35393,0x1039393,0x796933,0x631313,0x635313,0x6e3023,
  0x8e37,0xaf8e0e13,0xe3303,0x3935393,0x1639393,0x796933,0x731313,0x735313,
  0x6e3023,0x1095313,0x66e37,0x6e3023,0x23b7,0xe4038393,0x736463,0xfadca06f,
  0x8e37,0x440e0e13,0xe3983,0x8e4383,0x9e4e83,0xae4f03,0x8e9e93,0x1d3e3b3,
  0x10f1f13,0x1e3ea33,0x3091e93,0x30ede93,0x18e9e93,0x1da6a33,0x8e37,0x430e0e13,
  0x8f37,0xb00f0f13,0xe3303,0x8e3383,0x86e3023,0x87e3423,0xff0e0e13,0xffee56e3,
  0x8e37,0xaf0e0e13,0x7f37,0x580f0f13,0xe3303,0x8e3383,0x46e3023,0x47e3423,
  0xff0e0e13,0xffee56e3,0x7e37,0x570e0e13,0x7f37,0x3f0f0f13,0xe3303,0x8e3383,
  0x26e3823,0x27e3c23,0xff0e0e13,0xffee56e3,0x7e37,0x3e0e0e13,0x7f37,0x260f0f13,
  0xe3303,0x8e3383,0x26e3023,0x27e3423,0xff0e0e13,0xffee56e3,0x7e37,0x250e0e13,
  0x7f37,0xd0f0f13,0xe3303,0x8e3383,0x6e3823,0x7e3c23,0xff0e0e13,0xffee56e3,
  0x7e37,0x7f0e0e93,0xc0e3823,0xc0e3c23,0x260e3823,0x260e3c23,0x400e3823,0x400e3c23,
  0x5a0e3823,0x5a0e3c23,0x360eb023,0x360eb423,0x360eb823,0x360ebc23,0x380eb023,0x380eb423,
  0x353eb823,0x354ebc23,0x313,0x393,0xe13,0xe93,0xf13,0x913,
  0x993,0xa13,0x8bdca06f]

set_option maxRecDepth 100000 in
theorem codeAt_t51 : CodeAt Images.expandImage (pcOf 54176) t51Code := by
  apply codeAt_expand_last <;> decide +kernel

theorem codeAt_t51_sub {seg : List (BitVec 32)} (o : Nat) (hlen : o + seg.length ≤ t51Code.length)
    (h : (t51Code.drop o).take seg.length = seg) :
    CodeAt Images.expandImage (pcOf (54176 + o)) seg :=
  codeAt_sub o codeAt_t51 hlen h
theorem codeAt_t51_at {seg : List (BitVec 32)} (b : Nat) (hb : 54176 ≤ b)
    (hlen : b - 54176 + seg.length ≤ t51Code.length)
    (h : (t51Code.drop (b - 54176)).take seg.length = seg) : CodeAt Images.expandImage (pcOf b) seg := by
  have := codeAt_t51_sub (b - 54176) hlen h
  rwa [show 54176 + (b - 54176) = b by omega] at this

/-- The installed shared-forest driver is bound independently of the reference image. -/
theorem codeAt_expand_shared_driver :
    CodeAt Images.expandImage (pcOf 45056) Images.expandSharedDriver := by
  apply codeAt_expand_last <;> decide +kernel

end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedVariables false
def seg_0 : List (BitVec 32) := [1179816047,32439,7991,2148470547,963331,9352067,7286819,8336419,32439,134967,302976787,963331,9352067,7286819,8336419,28343,134967,336531219,1645130499,1653519235,7286819,8336419,28343,134967,353308435,1661907715,1670296451,7286819,8336419,814911599]
def seg_68 : List (BitVec 32) := [3146515,74045539]
def seg_104 : List (BitVec 32) := [4789907,32311,370019859,29787827,1640723,4462355,3415571,29820723,134711,1242435091,29820723,472835,7821075,20405811,1998355,101581411]
def seg_203 : List (BitVec 32) := [17698323]
def seg_204 : List (BitVec 32) := [134839,839814803,31329843,134839,604933779,963331,9352067,7221283,8270883,1311763,3672109167]
def seg_249 : List (BitVec 32) := [3146771,6293395,45092115,3475,211814547,134711,1426984467,930563,218003,66063891,29620531,6509715,822083823]
def seg_262 : List (BitVec 32) := [7735,2181959187,20848675,34871,772278291,27575,411798419,23607,1821117459,898629871]
def seg_272 : List (BitVec 32) := [2098195,6293395,45092115,3475,211814547,134711,1426984467,930563,6509459,66063891,29620531,12801171,725614831]
def seg_285 : List (BitVec 32) := [24119,1519259155,20848675,34871,4245162003,23479,1418431379,23607,2827750419,802160879]
def seg_295 : List (BitVec 32) := [1049619,7341971,45092115,3475,210765971,134711,1426984467,930563,12800915,133172755,29620531,20141203,629145839]
def seg_308 : List (BitVec 32) := [24119,2525892115,20848675,34871,3406301203,23479,2425064339,19511,3834383379,705691887]
/-- T51: 320 `li s10, 51` (51 top chains), 322 `li a7, 152` (target), 331 `jal ra, 54522` (KCOPY). -/
def seg_318 : List (BitVec 32) := [1043,12584851,0x3300d13,53480851,0x9800893,134711,1426984467,930563,20140947,7735,4294839827,29620531,32724115,0x6bd340ef]
def seg_332 : List (BitVec 32) := [20023,3465416211,20848675,34871,2299004947,19383,3364588435,15415,4035709971,605028591]
def seg_997 : List (BitVec 32) := [1142063215,19,19,19,19,19,19,19,19,19,19,19,2451]
def seg_1010 : List (BitVec 32) := [229235299]
def seg_1011 : List (BitVec 32) := [4824595,17698355,134967,487526163,930563,9319299,7286819,8336419,930563,9319299,40613923,41663523,4228615059,134711,1108217363,20844083]
def seg_1027 : List (BitVec 32) := [936451]
def seg_1028 : List (BitVec 32) := [7342739,267363]
def seg_1030 : List (BitVec 32) := [536871023]
def seg_1031 : List (BitVec 32) := [89805923]
def seg_1041 : List (BitVec 32) := [0x20c2f06f]
/-! Witness stack: the chain step block at 49300..49337 (G/F select with the top rule, direct HASH at 49328/49336). -/
def seg_49300 : List (BitVec 32) := [0x00040c63]
def seg_49301 : List (BitVec 32) := [0x0019f313,0x06030a63]
def seg_49303 : List (BitVec 32) := [0x00600313,0x00000393,0x02c0006f]
def seg_49306 : List (BitVec 32) := [0x0019f313,0x00000393,0x04731e63]
def seg_49309 : List (BitVec 32) := [0x03400393,0x0533ca63]
/-- T51: 49311 `j 54543` (GT: the G terminal step `maxDigit - 1`, chain 0 keeps HIGH). -/
def seg_49311 : List (BitVec 32) := [0x1c00506f]
def seg_49314 : List (BitVec 32) := [0x00600313]
def seg_49315 : List (BitVec 32) := [0x018e3383]
def seg_49316 : List (BitVec 32) := [0x010e3f03,0x05ee3023,0x047e3423,0x040e3823,0x040e3c23,0x060e3023,0x060e3423,
  0x030e0513,0x04000593,0x020e0613,0x006a1463]
def seg_49327 : List (BitVec 32) := [0x030e0613]
def seg_49328 : List (BitVec 32) := [0x73]
def seg_49329 : List (BitVec 32) := [0x001a0a13,0xd55d006f]
def seg_49331 : List (BitVec 32) := [0x020e3023,0x020e3423,0x000e0513,0x04000593,0x030e0613]
def seg_49336 : List (BitVec 32) := [0x73]
def seg_49337 : List (BitVec 32) := [0xc08fa06f]
def seg_1046 : List (BitVec 32) := [115]
def seg_1047 : List (BitVec 32) := [1761775727,19]
def seg_1049 : List (BitVec 32) := [995262575,19]
def seg_1052 : List (BitVec 32) := [134839,1611566739,31329843,134839,487493267,963331,9352067,7221283,8270883,1673619,4078956655]
def seg_1063 : List (BitVec 32) := [1901331,4395795,66257683,4228084499,132407,1610941715,198035,132663,604374547]
def seg_1072 : List (BitVec 32) := [115]
def seg_1073 : List (BitVec 32) := [2579,5053971,29887283]
def seg_1076 : List (BitVec 32) := [284841571]
def seg_1077 : List (BitVec 32) := [21585459,1998355,68028515]
def seg_1080 : List (BitVec 32) := [733955,9122691,7090211,8139811,134967,537857811,733955,9122691,7286819,8336419,134839,604933779,134967,588189459,963331,9352067,7286819,8336419,79691887]
def seg_1099 : List (BitVec 32) := [733955,9122691,40646691,41696291,1573032047,19,134967,537857811,963331,9352067,7286819,8336419,134967,588189459,733955,9122691,7286819,8336419]
def seg_1138 : List (BitVec 32) := [115]
def seg_1139 : List (BitVec 32) := [17500947,4228647955,1706515,4020236399]
def seg_1143 : List (BitVec 32) := [134839,604933779,134967,638521107,963331,9352067,7286819,8336419,32871]
/-- T51: 1158 `j 54532` (KMAX: the T51 top chain caps). -/
def seg_1158 : List (BitVec 32) := [0x1f83406f]
def seg_1160 : List (BitVec 32) := [4197011,3751800943]
sym_block eblk_262 := symRun { noAlias := true } seg_262 (pcOf 262) 200
sym_block eblk_285 := symRun { noAlias := true } seg_285 (pcOf 285) 200
sym_block eblk_295 := symRun { noAlias := true } seg_295 (pcOf 295) 200
sym_block eblk_308 := symRun { noAlias := true } seg_308 (pcOf 308) 200
sym_block eblk_318 := symRun { noAlias := true } seg_318 (pcOf 318) 200
sym_block eblk_332 := symRun { noAlias := true } seg_332 (pcOf 332) 200
sym_block eblk_997 := symRun { noAlias := true } seg_997 (pcOf 997) 200
sym_block eblk_1010 := symRun { noAlias := true } seg_1010 (pcOf 1010) 200
sym_block eblk_1011 := symRun { noAlias := true } seg_1011 (pcOf 1011) 200
sym_block eblk_1028 := symRun { noAlias := true } seg_1028 (pcOf 1028) 200
sym_block eblk_1030 := symRun { noAlias := true } seg_1030 (pcOf 1030) 200
sym_block eblk_1031 := symRun { noAlias := true } seg_1031 (pcOf 1031) 200
sym_block eblk_1041 := symRun { noAlias := true } seg_1041 (pcOf 1041) 200
sym_block eblk_49300 := symRun { noAlias := true } seg_49300 (pcOf 49300) 200
sym_block eblk_49301 := symRun { noAlias := true } seg_49301 (pcOf 49301) 200
sym_block eblk_49303 := symRun { noAlias := true } seg_49303 (pcOf 49303) 200
sym_block eblk_49306 := symRun { noAlias := true } seg_49306 (pcOf 49306) 200
sym_block eblk_49309 := symRun { noAlias := true } seg_49309 (pcOf 49309) 200
sym_block eblk_49311 := symRun { noAlias := true } seg_49311 (pcOf 49311) 200
sym_block eblk_49314 := symRun { noAlias := true } seg_49314 (pcOf 49314) 200
sym_block eblk_49315 := symRun { noAlias := true } seg_49315 (pcOf 49315) 200
sym_block eblk_49316 := symRun { noAlias := true } seg_49316 (pcOf 49316) 200
sym_block eblk_49327 := symRun { noAlias := true } seg_49327 (pcOf 49327) 200
sym_block eblk_49329 := symRun { noAlias := true } seg_49329 (pcOf 49329) 200
sym_block eblk_49331 := symRun { noAlias := true } seg_49331 (pcOf 49331) 200
sym_block eblk_49337 := symRun { noAlias := true } seg_49337 (pcOf 49337) 200
sym_block eblk_1047 := symRun { noAlias := true } seg_1047 (pcOf 1047) 200
sym_block eblk_1049 := symRun { noAlias := true } seg_1049 (pcOf 1049) 200
sym_block eblk_1052 := symRun { noAlias := true } seg_1052 (pcOf 1052) 200
sym_block eblk_1063 := symRun { noAlias := true } seg_1063 (pcOf 1063) 200
sym_block eblk_1073 := symRun { noAlias := true } seg_1073 (pcOf 1073) 200
sym_block eblk_1076 := symRun { noAlias := true } seg_1076 (pcOf 1076) 200
sym_block eblk_1077 := symRun { noAlias := true } seg_1077 (pcOf 1077) 200
sym_block eblk_1080 := symRun { noAlias := true } seg_1080 (pcOf 1080) 200
sym_block eblk_1099 := symRun { noAlias := true } seg_1099 (pcOf 1099) 200
sym_block eblk_1139 := symRun { noAlias := true } seg_1139 (pcOf 1139) 200
sym_block eblk_1143 := symRun { noAlias := true } seg_1143 (pcOf 1143) 200
sym_block eblk_1158 := symRun { noAlias := true } seg_1158 (pcOf 1158) 200
sym_block eblk_1160 := symRun { noAlias := true } seg_1160 (pcOf 1160) 200
end SigGolfCandidate.T3M.Expand
end


-- Check the large outer chunk lists sequentially with their required recursion depth.
set_option Elab.async false
set_option maxRecDepth 100000

namespace SigGolfCandidate.T3M.Images
private theorem shared_foldl_chunks (cs : List (List (BitVec 32))) (acc : List (BitVec 32)) :
    cs.foldl (· ++ ·) acc = acc ++ cs.flatten := by
  induction cs generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
  | cons c cs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]

private theorem shared_flatten_length (cs : List (List (BitVec 32)))
    (h : ∀ c ∈ cs, c.length = 256) : cs.flatten.length = cs.length * 256 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := h c (by simp)
    have hs := ih (fun d hd => h d (by simp only [List.mem_cons]; exact Or.inr hd))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hc, hs]
    omega

set_option maxHeartbeats 4000000 in
/-- The producer executes the exact proved verifier chain and child banks. -/
theorem expand_banks_eq_verify :
    (expandCode.drop 195584).take 59072 = (verifyCode.drop 195584).take 59072 := by
  let leading : List (List (BitVec 32)) := [verifyCode_0, verifyCode_1, verifyCode_2, verifyCode_3, verifyCode_4, verifyCode_5, verifyCode_6, verifyCode_7, verifyCode_8, verifyCode_9, verifyCode_10, verifyCode_11, verifyCode_12, verifyCode_13, verifyCode_14, verifyCode_15, verifyCode_16, verifyCode_17, verifyCode_18, verifyCode_19, verifyCode_20, verifyCode_21, verifyCode_22, verifyCode_23, verifyCode_24, verifyCode_25, verifyCode_26, verifyCode_27, verifyCode_28, verifyCode_29, verifyCode_30, verifyCode_31, verifyCode_32, verifyCode_33, verifyCode_34, verifyCode_35, verifyCode_36, verifyCode_37, verifyCode_38, verifyCode_39, verifyCode_40, verifyCode_41, verifyCode_42, verifyCode_43, verifyCode_44, verifyCode_45, verifyCode_46, verifyCode_47, verifyCode_48, verifyCode_49, verifyCode_50, verifyCode_51, verifyCode_52, verifyCode_53, verifyCode_54, verifyCode_55, verifyCode_56, verifyCode_57, verifyCode_58, verifyCode_59, verifyCode_60, verifyCode_61, verifyCode_62, verifyCode_63, verifyCode_64, verifyCode_65, verifyCode_66, verifyCode_67, verifyCode_68, verifyCode_69, verifyCode_70, verifyCode_71, verifyCode_72, verifyCode_73, verifyCode_74, verifyCode_75, verifyCode_76, verifyCode_77, verifyCode_78, verifyCode_79, verifyCode_80, verifyCode_81, verifyCode_82, verifyCode_83, verifyCode_84, verifyCode_85, verifyCode_86, verifyCode_87, verifyCode_88, verifyCode_89, verifyCode_90, verifyCode_91, verifyCode_92, verifyCode_93, verifyCode_94, verifyCode_95, verifyCode_96, verifyCode_97, verifyCode_98, verifyCode_99, verifyCode_100, verifyCode_101, verifyCode_102, verifyCode_103, verifyCode_104, verifyCode_105, verifyCode_106, verifyCode_107, verifyCode_108, verifyCode_109, verifyCode_110, verifyCode_111, verifyCode_112, verifyCode_113, verifyCode_114, verifyCode_115, verifyCode_116, verifyCode_117, verifyCode_118, verifyCode_119, verifyCode_120, verifyCode_121, verifyCode_122, verifyCode_123, verifyCode_124, verifyCode_125, verifyCode_126, verifyCode_127, verifyCode_128, verifyCode_129, verifyCode_130, verifyCode_131, verifyCode_132, verifyCode_133, verifyCode_134, verifyCode_135, verifyCode_136, verifyCode_137, verifyCode_138, verifyCode_139, verifyCode_140, verifyCode_141, verifyCode_142, verifyCode_143, verifyCode_144, verifyCode_145, verifyCode_146, verifyCode_147, verifyCode_148, verifyCode_149, verifyCode_150, verifyCode_151, verifyCode_152, verifyCode_153, verifyCode_154, verifyCode_155, verifyCode_156, verifyCode_157, verifyCode_158, verifyCode_159, verifyCode_160, verifyCode_161, verifyCode_162, verifyCode_163, verifyCode_164, verifyCode_165, verifyCode_166, verifyCode_167, verifyCode_168, verifyCode_169, verifyCode_170, verifyCode_171, verifyCode_172, verifyCode_173, verifyCode_174, verifyCode_175, verifyCode_176, verifyCode_177, verifyCode_178, verifyCode_179, verifyCode_180, verifyCode_181, verifyCode_182, verifyCode_183, verifyCode_184, verifyCode_185, verifyCode_186, verifyCode_187, verifyCode_188, verifyCode_189, verifyCode_190, verifyCode_191, verifyCode_192, verifyCode_193, verifyCode_194, verifyCode_195, verifyCode_196, verifyCode_197, verifyCode_198, verifyCode_199, verifyCode_200, verifyCode_201, verifyCode_202, verifyCode_203, verifyCode_204, verifyCode_205, verifyCode_206, verifyCode_207, verifyCode_208, verifyCode_209, verifyCode_210, verifyCode_211, verifyCode_212, verifyCode_213, verifyCode_214, verifyCode_215, verifyCode_216, verifyCode_217, verifyCode_218, verifyCode_219, verifyCode_220, verifyCode_221, verifyCode_222, verifyCode_223, verifyCode_224, verifyCode_225, verifyCode_226, verifyCode_227, verifyCode_228, verifyCode_229, verifyCode_230, verifyCode_231, verifyCode_232, verifyCode_233, verifyCode_234, verifyCode_235, verifyCode_236, verifyCode_237, verifyCode_238, verifyCode_239, verifyCode_240, verifyCode_241, verifyCode_242, verifyCode_243, verifyCode_244, verifyCode_245, verifyCode_246, verifyCode_247, verifyCode_248, verifyCode_249, verifyCode_250, verifyCode_251, verifyCode_252, verifyCode_253, verifyCode_254, verifyCode_255, verifyCode_256, verifyCode_257, verifyCode_258, verifyCode_259, verifyCode_260, verifyCode_261, verifyCode_262, verifyCode_263, verifyCode_264, verifyCode_265, verifyCode_266, verifyCode_267, verifyCode_268, verifyCode_269, verifyCode_270, verifyCode_271, verifyCode_272, verifyCode_273, verifyCode_274, verifyCode_275, verifyCode_276, verifyCode_277, verifyCode_278, verifyCode_279, verifyCode_280, verifyCode_281, verifyCode_282, verifyCode_283, verifyCode_284, verifyCode_285, verifyCode_286, verifyCode_287, verifyCode_288, verifyCode_289, verifyCode_290, verifyCode_291, verifyCode_292, verifyCode_293, verifyCode_294, verifyCode_295, verifyCode_296, verifyCode_297, verifyCode_298, verifyCode_299, verifyCode_300, verifyCode_301, verifyCode_302, verifyCode_303, verifyCode_304, verifyCode_305, verifyCode_306, verifyCode_307, verifyCode_308, verifyCode_309, verifyCode_310, verifyCode_311, verifyCode_312, verifyCode_313, verifyCode_314, verifyCode_315, verifyCode_316, verifyCode_317, verifyCode_318, verifyCode_319, verifyCode_320, verifyCode_321, verifyCode_322, verifyCode_323, verifyCode_324, verifyCode_325, verifyCode_326, verifyCode_327, verifyCode_328, verifyCode_329, verifyCode_330, verifyCode_331, verifyCode_332, verifyCode_333, verifyCode_334, verifyCode_335, verifyCode_336, verifyCode_337, verifyCode_338, verifyCode_339, verifyCode_340, verifyCode_341, verifyCode_342, verifyCode_343, verifyCode_344, verifyCode_345, verifyCode_346, verifyCode_347, verifyCode_348, verifyCode_349, verifyCode_350, verifyCode_351, verifyCode_352, verifyCode_353, verifyCode_354, verifyCode_355, verifyCode_356, verifyCode_357, verifyCode_358, verifyCode_359, verifyCode_360, verifyCode_361, verifyCode_362, verifyCode_363, verifyCode_364, verifyCode_365, verifyCode_366, verifyCode_367, verifyCode_368, verifyCode_369, verifyCode_370, verifyCode_371, verifyCode_372, verifyCode_373, verifyCode_374, verifyCode_375, verifyCode_376, verifyCode_377, verifyCode_378, verifyCode_379, verifyCode_380, verifyCode_381, verifyCode_382, verifyCode_383, verifyCode_384, verifyCode_385, verifyCode_386, verifyCode_387, verifyCode_388, verifyCode_389, verifyCode_390, verifyCode_391, verifyCode_392, verifyCode_393, verifyCode_394, verifyCode_395, verifyCode_396, verifyCode_397, verifyCode_398, verifyCode_399, verifyCode_400, verifyCode_401, verifyCode_402, verifyCode_403, verifyCode_404, verifyCode_405, verifyCode_406, verifyCode_407, verifyCode_408, verifyCode_409, verifyCode_410, verifyCode_411, verifyCode_412, verifyCode_413, verifyCode_414, verifyCode_415, verifyCode_416, verifyCode_417, verifyCode_418, verifyCode_419, verifyCode_420, verifyCode_421, verifyCode_422, verifyCode_423, verifyCode_424, verifyCode_425, verifyCode_426, verifyCode_427, verifyCode_428, verifyCode_429, verifyCode_430, verifyCode_431, verifyCode_432, verifyCode_433, verifyCode_434, verifyCode_435, verifyCode_436, verifyCode_437, verifyCode_438, verifyCode_439, verifyCode_440, verifyCode_441, verifyCode_442, verifyCode_443, verifyCode_444, verifyCode_445, verifyCode_446, verifyCode_447, verifyCode_448, verifyCode_449, verifyCode_450, verifyCode_451, verifyCode_452, verifyCode_453, verifyCode_454, verifyCode_455, verifyCode_456, verifyCode_457, verifyCode_458, verifyCode_459, verifyCode_460, verifyCode_461, verifyCode_462, verifyCode_463, verifyCode_464, verifyCode_465, verifyCode_466, verifyCode_467, verifyCode_468, verifyCode_469, verifyCode_470, verifyCode_471, verifyCode_472, verifyCode_473, verifyCode_474, verifyCode_475, verifyCode_476, verifyCode_477, verifyCode_478, verifyCode_479, verifyCode_480, verifyCode_481, verifyCode_482, verifyCode_483, verifyCode_484, verifyCode_485, verifyCode_486, verifyCode_487, verifyCode_488, verifyCode_489, verifyCode_490, verifyCode_491, verifyCode_492, verifyCode_493, verifyCode_494, verifyCode_495, verifyCode_496, verifyCode_497, verifyCode_498, verifyCode_499, verifyCode_500, verifyCode_501, verifyCode_502, verifyCode_503, verifyCode_504, verifyCode_505, verifyCode_506, verifyCode_507, verifyCode_508, verifyCode_509, verifyCode_510, verifyCode_511, verifyCode_512, verifyCode_513, verifyCode_514, verifyCode_515, verifyCode_516, verifyCode_517, verifyCode_518, verifyCode_519, verifyCode_520, verifyCode_521, verifyCode_522, verifyCode_523, verifyCode_524, verifyCode_525, verifyCode_526, verifyCode_527, verifyCode_528, verifyCode_529, verifyCode_530, verifyCode_531, verifyCode_532, verifyCode_533, verifyCode_534, verifyCode_535, verifyCode_536, verifyCode_537, verifyCode_538, verifyCode_539, verifyCode_540, verifyCode_541, verifyCode_542, verifyCode_543, verifyCode_544, verifyCode_545, verifyCode_546, verifyCode_547, verifyCode_548, verifyCode_549, verifyCode_550, verifyCode_551, verifyCode_552, verifyCode_553, verifyCode_554, verifyCode_555, verifyCode_556, verifyCode_557, verifyCode_558, verifyCode_559, verifyCode_560, verifyCode_561, verifyCode_562, verifyCode_563, verifyCode_564, verifyCode_565, verifyCode_566, verifyCode_567, verifyCode_568, verifyCode_569, verifyCode_570, verifyCode_571, verifyCode_572, verifyCode_573, verifyCode_574, verifyCode_575, verifyCode_576, verifyCode_577, verifyCode_578, verifyCode_579, verifyCode_580, verifyCode_581, verifyCode_582, verifyCode_583, verifyCode_584, verifyCode_585, verifyCode_586, verifyCode_587, verifyCode_588, verifyCode_589, verifyCode_590, verifyCode_591, verifyCode_592, verifyCode_593, verifyCode_594, verifyCode_595, verifyCode_596, verifyCode_597, verifyCode_598, verifyCode_599, verifyCode_600, verifyCode_601, verifyCode_602, verifyCode_603, verifyCode_604, verifyCode_605, verifyCode_606, verifyCode_607, verifyCode_608, verifyCode_609, verifyCode_610, verifyCode_611, verifyCode_612, verifyCode_613, verifyCode_614, verifyCode_615, verifyCode_616, verifyCode_617, verifyCode_618, verifyCode_619, verifyCode_620, verifyCode_621, verifyCode_622, verifyCode_623, verifyCode_624, verifyCode_625, verifyCode_626, verifyCode_627, verifyCode_628, verifyCode_629, verifyCode_630, verifyCode_631, verifyCode_632, verifyCode_633, verifyCode_634, verifyCode_635, verifyCode_636, verifyCode_637, verifyCode_638, verifyCode_639, verifyCode_640, verifyCode_641, verifyCode_642, verifyCode_643, verifyCode_644, verifyCode_645, verifyCode_646, verifyCode_647, verifyCode_648, verifyCode_649, verifyCode_650, verifyCode_651, verifyCode_652, verifyCode_653, verifyCode_654, verifyCode_655, verifyCode_656, verifyCode_657, verifyCode_658, verifyCode_659, verifyCode_660, verifyCode_661, verifyCode_662, verifyCode_663, verifyCode_664, verifyCode_665, verifyCode_666, verifyCode_667, verifyCode_668, verifyCode_669, verifyCode_670, verifyCode_671, verifyCode_672, verifyCode_673, verifyCode_674, verifyCode_675, verifyCode_676, verifyCode_677, verifyCode_678, verifyCode_679, verifyCode_680, verifyCode_681, verifyCode_682, verifyCode_683, verifyCode_684, verifyCode_685, verifyCode_686, verifyCode_687, verifyCode_688, verifyCode_689, verifyCode_690, verifyCode_691, verifyCode_692, verifyCode_693, verifyCode_694, verifyCode_695, verifyCode_696, verifyCode_697, verifyCode_698, verifyCode_699, verifyCode_700, verifyCode_701, verifyCode_702, verifyCode_703, verifyCode_704, verifyCode_705, verifyCode_706, verifyCode_707, verifyCode_708, verifyCode_709, verifyCode_710, verifyCode_711, verifyCode_712, verifyCode_713, verifyCode_714, verifyCode_715, verifyCode_716, verifyCode_717, verifyCode_718, verifyCode_719, verifyCode_720, verifyCode_721, verifyCode_722, verifyCode_723, verifyCode_724, verifyCode_725, verifyCode_726, verifyCode_727, verifyCode_728, verifyCode_729, verifyCode_730, verifyCode_731, verifyCode_732, verifyCode_733, verifyCode_734, verifyCode_735, verifyCode_736, verifyCode_737, verifyCode_738, verifyCode_739, verifyCode_740, verifyCode_741, verifyCode_742, verifyCode_743, verifyCode_744, verifyCode_745, verifyCode_746, verifyCode_747, verifyCode_748, verifyCode_749, verifyCode_750, verifyCode_751, verifyCode_752, verifyCode_753, verifyCode_754, verifyCode_755, verifyCode_756, verifyCode_757, verifyCode_758, verifyCode_759, verifyCode_760, verifyCode_761, verifyCode_762, verifyCode_763]
  let middle : List (List (BitVec 32)) := [verifyCode_764, verifyCode_765, verifyCode_766, verifyCode_767, verifyCode_768, verifyCode_769, verifyCode_770, verifyCode_771, verifyCode_772, verifyCode_773, verifyCode_774, verifyCode_775, verifyCode_776, verifyCode_777, verifyCode_778, verifyCode_779, verifyCode_780, verifyCode_781, verifyCode_782, verifyCode_783, verifyCode_784, verifyCode_785, verifyCode_786, verifyCode_787, verifyCode_788, verifyCode_789, verifyCode_790, verifyCode_791, verifyCode_792, verifyCode_793, verifyCode_794, verifyCode_795, verifyCode_796, verifyCode_797, verifyCode_798, verifyCode_799, verifyCode_800, verifyCode_801, verifyCode_802, verifyCode_803, verifyCode_804, verifyCode_805, verifyCode_806, verifyCode_807, verifyCode_808, verifyCode_809, verifyCode_810, verifyCode_811, verifyCode_812, verifyCode_813, verifyCode_814, verifyCode_815, verifyCode_816, verifyCode_817, verifyCode_818, verifyCode_819, verifyCode_820, verifyCode_821, verifyCode_822, verifyCode_823, verifyCode_824, verifyCode_825, verifyCode_826, verifyCode_827, verifyCode_828, verifyCode_829, verifyCode_830, verifyCode_831, verifyCode_832, verifyCode_833, verifyCode_834, verifyCode_835, verifyCode_836, verifyCode_837, verifyCode_838, verifyCode_839, verifyCode_840, verifyCode_841, verifyCode_842, verifyCode_843, verifyCode_844, verifyCode_845, verifyCode_846, verifyCode_847, verifyCode_848, verifyCode_849, verifyCode_850, verifyCode_851, verifyCode_852, verifyCode_853, verifyCode_854, verifyCode_855, verifyCode_856, verifyCode_857, verifyCode_858, verifyCode_859, verifyCode_860, verifyCode_861, verifyCode_862, verifyCode_863, verifyCode_864, verifyCode_865, verifyCode_866, verifyCode_867, verifyCode_868, verifyCode_869, verifyCode_870, verifyCode_871, verifyCode_872, verifyCode_873, verifyCode_874, verifyCode_875, verifyCode_876, verifyCode_877, verifyCode_878, verifyCode_879, verifyCode_880, verifyCode_881, verifyCode_882, verifyCode_883, verifyCode_884, verifyCode_885, verifyCode_886, verifyCode_887, verifyCode_888, verifyCode_889, verifyCode_890, verifyCode_891, verifyCode_892, verifyCode_893, verifyCode_894, verifyCode_895, verifyCode_896, verifyCode_897, verifyCode_898, verifyCode_899, verifyCode_900, verifyCode_901, verifyCode_902, verifyCode_903, verifyCode_904, verifyCode_905, verifyCode_906, verifyCode_907, verifyCode_908, verifyCode_909, verifyCode_910, verifyCode_911, verifyCode_912, verifyCode_913, verifyCode_914, verifyCode_915, verifyCode_916, verifyCode_917, verifyCode_918, verifyCode_919, verifyCode_920, verifyCode_921, verifyCode_922, verifyCode_923, verifyCode_924, verifyCode_925, verifyCode_926, verifyCode_927, verifyCode_928, verifyCode_929, verifyCode_930, verifyCode_931, verifyCode_932, verifyCode_933, verifyCode_934, verifyCode_935, verifyCode_936, verifyCode_937, verifyCode_938, verifyCode_939, verifyCode_940, verifyCode_941, verifyCode_942, verifyCode_943, verifyCode_944, verifyCode_945, verifyCode_946, verifyCode_947, verifyCode_948, verifyCode_949, verifyCode_950, verifyCode_951, verifyCode_952, verifyCode_953, verifyCode_954, verifyCode_955, verifyCode_956, verifyCode_957, verifyCode_958, verifyCode_959, verifyCode_960, verifyCode_961, verifyCode_962, verifyCode_963, verifyCode_964, verifyCode_965, verifyCode_966, verifyCode_967, verifyCode_968, verifyCode_969, verifyCode_970, verifyCode_971, verifyCode_972, verifyCode_973, verifyCode_974, verifyCode_975, verifyCode_976, verifyCode_977, verifyCode_978, verifyCode_979, verifyCode_980, verifyCode_981, verifyCode_982, verifyCode_983, verifyCode_984, verifyCode_985, verifyCode_986, verifyCode_987, verifyCode_988, verifyCode_989, verifyCode_990, verifyCode_991, verifyCode_992, verifyCode_993]
  let suffix : List (List (BitVec 32)) := [verifyCode_995, verifyCode_996, verifyCode_997, verifyCode_998, verifyCode_999, verifyCode_1000, verifyCode_1001, verifyCode_1002, verifyCode_1003, verifyCode_1004]
  have huniform : ∀ c ∈ leading ++ middle ++ [verifyCode_994], c.length = 256 := by
    intro c hc
    have hm : c ∈ SigGolfCandidate.T3M.Verify.vChunks.dropLast := by
      change c ∈ (leading ++ middle ++ [verifyCode_994]) ++ suffix.dropLast
      exact List.mem_append_left _ hc
    exact (beq_iff_eq.mp ((List.all_eq_true.mp SigGolfCandidate.T3M.Verify.vChunks_ok) c hm))
  have hpre : leading.flatten.length = 195584 := by
    have hl := shared_flatten_length leading (fun c hc => huniform c (by
      exact List.mem_append_left _ (List.mem_append_left _ hc)))
    simpa only [show leading.length = 764 by rfl] using hl
  have hmid : middle.flatten.length = 58880 := by
    have hl := shared_flatten_length middle (fun c hc => huniform c (by
      exact List.mem_append_left _ (List.mem_append_right _ hc)))
    simpa only [show middle.length = 230 by rfl] using hl
  have h994 : verifyCode_994.length = 256 := huniform _ (by
    exact List.mem_append_right _ (by simp))
  have hbank : expandSharedBanks.length = 59072 := by
    change (middle ++ [verifyCode_994.take 192]).flatten.length = _
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_append, List.length_take, h994, hmid]
    rfl
  have hshape : expandSharedBanks = middle.flatten ++ verifyCode_994.take 192 := by
    change (middle ++ [verifyCode_994.take 192]).flatten = _
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
  have hv0 : verifyCode = leading.flatten ++ (middle.flatten ++ (verifyCode_994 ++ suffix.flatten)) := by
    rw [verifyCode, shared_foldl_chunks, List.nil_append]
    change (leading ++ (middle ++ (verifyCode_994 :: suffix))).flatten = _
    simp only [List.flatten_append, List.flatten_cons]
  have hv : verifyCode = leading.flatten ++ (expandSharedBanks ++ (verifyCode_994.drop 192 ++ suffix.flatten)) := by
    rw [hv0, hshape]
    simp only [List.append_assoc]
    rw [← List.append_assoc (verifyCode_994.take 192) (verifyCode_994.drop 192), List.take_append_drop]
  have he : expandCode.drop 195584 = expandSharedBanks := by
    rw [expandCode, shared_foldl_chunks, List.nil_append]
    let front : List (List (BitVec 32)) := [expandCode_0, expandCode_1, expandCode_2, expandCode_3, expandCode_4, expandCode_5, expandCode_6, expandCode_7, expandCode_8, expandCode_9, expandCode_10, expandCode_11, expandCode_12, expandCode_13, expandCode_14, expandCode_15, expandCode_16, expandCode_17, expandCode_18, expandCode_19, expandCode_20, expandCode_21, expandCode_22, expandCode_23, expandCode_24, expandCode_25, expandCode_26, expandCode_27, expandCode_28, expandCode_29, expandCode_30, expandCode_31, expandCode_32, expandCode_33, expandCode_34, expandCode_35, expandCode_36, expandCode_37, expandCode_38, expandCode_39, expandCode_40, expandCode_41, expandCode_42, expandCode_43, expandCode_44, expandCode_45, expandCode_46, expandCode_47, expandCode_48, expandCode_49, expandCode_50, expandCode_51, expandCode_52, expandCode_53, expandCode_54, expandCode_55, expandCode_56, expandCode_57, expandCode_58, expandCode_59, expandCode_60, expandCode_61, expandCode_62, expandCode_63, expandCode_64, expandCode_65, expandCode_66, expandCode_67, expandCode_68, expandCode_69, expandCode_70, expandCode_71, expandCode_72, expandCode_73, expandCode_74, expandCode_75, expandCode_76, expandCode_77, expandCode_78, expandCode_79, expandCode_80, expandCode_81, expandCode_82, expandCode_83, expandCode_84, expandCode_85, expandCode_86, expandCode_87, expandCode_88, expandCode_89, expandCode_90, expandCode_91, expandCode_92, expandCode_93, expandCode_94, expandCode_95, expandCode_96, expandCode_97, expandCode_98, expandCode_99, expandCode_100, expandCode_101, expandCode_102, expandCode_103, expandCode_104, expandCode_105, expandCode_106, expandCode_107, expandCode_108, expandCode_109, expandCode_110, expandCode_111, expandCode_112, expandCode_113, expandCode_114, expandCode_115, expandCode_116, expandCode_117, expandCode_118, expandCode_119, expandCode_120, expandCode_121, expandCode_122, expandCode_123, expandCode_124, expandCode_125, expandCode_126, expandCode_127, expandCode_128, expandCode_129, expandCode_130, expandCode_131, expandCode_132, expandCode_133, expandCode_134, expandCode_135, expandCode_136, expandCode_137, expandCode_138, expandCode_139, expandCode_140, expandCode_141, expandCode_142, expandCode_143, expandCode_144, expandCode_145, expandCode_146, expandCode_147, expandCode_148, expandCode_149, expandCode_150, expandCode_151, expandCode_152, expandCode_153, expandCode_154, expandCode_155, expandCode_156, expandCode_157, expandCode_158, expandCode_159, expandCode_160, expandCode_161, expandCode_162, expandCode_163, expandCode_164, expandCode_165, expandCode_166, expandCode_167, expandCode_168, expandCode_169, expandCode_170, expandCode_171]
    have hf : front.flatten.length = 44032 := by
      rw [List.length_flatten]
      decide +kernel
    change (front ++ [expandCode_172]).flatten.drop 195584 = _
    rw [List.flatten_append, show [expandCode_172].flatten = expandCode_172 by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]]
    have hh : 195584 = front.flatten.length + 151552 := by omega
    rw [hh, ← List.drop_drop, List.drop_left]
    -- Pairing stage 1: the driver prefix now also holds the constructor/layout blocks (48000..49738).
    obtain ⟨driverPrefix, hdp, hp⟩ : ∃ P, expandCode_172 = P ++ expandSharedBanks ∧ P.length = 151552 :=
      ⟨_, rfl, by decide +kernel⟩
    rw [hdp, ← hp, List.drop_left]
  rw [he, hv, ← hpre, List.drop_left]
  rw [← hbank, List.take_left, List.take_length]
end SigGolfCandidate.T3M.Images

namespace SigGolfCandidate.T3M.Expand
open SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Canon ====
section

/-! # Expand canonical counter search (configuration e7b, r3-lean-sign expand porter; img-v6 port canon-v6)

Split out of `Expand/Routine.lean` so that it builds independently of the forest/FTS modules.
Expand kernel base `b = 354`; choice block at 43040 (`choiceBase 354`), `pa` at 43057, `topcr` at 43064..43070,
floor hooks at 46905 (policy hints, img-v6 radix 484/22/1), lower credit hook at 46918 (credit words `0x66040 + 8 lay`).
Campaign T51: the top layer runs the shared T51 kernel at its expand instance (`1272: j 54176`, `K_ENTRY` 54176, unpacker
54356..54521, RAM table 0xA0000 from KCOPY): `T51.trial` / `T51.unpack` in `CanonicalExpand.cs_loop`. -/

namespace ClaudeWCT.W9.Machine.Expand.SharedCounterHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
/-- `46905`: `t3 := mem[0x66000]` (policy hints), `t4 := 22` (radix), branch on the layer (v6: `s0-3`). -/
def firstCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xe3e03,0x1600e93,0xffd40f13,0xf0c63]
sym_block first := symRun {noAlias:=true} firstCode (pcOf 46905) 20
def middleCode : List (BitVec 32) := bv_list% 32 [0x3de5e33,0xffe40f13,0xf0663]
sym_block middle := symRun {noAlias:=true} middleCode (pcOf 46911) 20
def lastCode : List (BitVec 32) := bv_list% 32 [0x3de5e33,0xb40fc06f]
sym_block last := symRun {noAlias:=true} lastCode (pcOf 46914) 20
def remainderCode : List (BitVec 32) := bv_list% 32 [0x3de7e33,0xb38fc06f]
sym_block remainder := symRun {noAlias:=true} remainderCode (pcOf 46916) 20
def lowerCreditCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x341e93,0x1de0e33,0x54e3023,0xf21d206f]
sym_block lowerCredit := symRun {noAlias:=true} lowerCreditCode (pcOf 46918) 20
def topCreditCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xff4a0e93,0x5de3023,0xee1d206f]
sym_block topCredit := symRun {noAlias:=true} topCreditCode (pcOf 46924) 20
structure Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46905) firstCode
  middle : CodeAt im (pcOf 46911) middleCode
  last : CodeAt im (pcOf 46914) lastCode
  remainder : CodeAt im (pcOf 46916) remainderCode
  lowerCredit : CodeAt im (pcOf 46918) lowerCreditCode
  topCredit : CodeAt im (pcOf 46924) topCreditCode
theorem rem22 (n : Nat) (hn : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 22#64=BitVec.ofNat 64 (n%22) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_remu,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n%22<2^64 by omega)]
  omega
theorem div22 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 22#64=BitVec.ofNat 64 (n/22) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/22<2^64 by omega)]
  omega
theorem floor1_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=1)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 11 17 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/484%22) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=middle.res.toState s1
  have st2 : Steps im s1 3 6 s2 := symRun_sound middle hc.middle s1 (by simp [s1, first.res, s2, middle.res, rv_simp, h8]) (by simp [middle.res,rv_simp])
  let s3:=last.res.toState s2
  have st3 : Steps im s2 2 5 s3 := symRun_sound last hc.last s2 (by simp [s1, first.res, s2, middle.res, s3, last.res, rv_simp, h8]) (by simp [last.res,rv_simp])
  refine ⟨s3,st1.trans (st2.trans (st3)),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, middle.res, s3, last.res,rv_simp,h8]
  · simp [s1, first.res, s2, middle.res, s3, last.res,rv_simp,hm]
    simp only [div22 hints (by omega),div22 (hints/22) (by omega),rem22 hints (by omega),rem22 (hints/22) (by omega)]
    try (congr 1; omega)
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
theorem floor2_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=2)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 11 17 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/22%22) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=middle.res.toState s1
  have st2 : Steps im s1 3 6 s2 := symRun_sound middle hc.middle s1 (by simp [s1, first.res, s2, middle.res, rv_simp, h8]) (by simp [middle.res,rv_simp])
  let s3:=remainder.res.toState s2
  have st3 : Steps im s2 2 5 s3 := symRun_sound remainder hc.remainder s2 (by simp [s1, first.res, s2, middle.res, s3, remainder.res, rv_simp, h8]) (by simp [remainder.res,rv_simp])
  refine ⟨s3,st1.trans (st2.trans (st3)),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, middle.res, s3, remainder.res,rv_simp,h8]
  · simp [s1, first.res, s2, middle.res, s3, remainder.res,rv_simp,hm]
    simp only [div22 hints (by omega),div22 (hints/22) (by omega),rem22 hints (by omega),rem22 (hints/22) (by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
theorem floor3_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=3)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 8 11 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints%22) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=remainder.res.toState s1
  have st2 : Steps im s1 2 5 s2 := symRun_sound remainder hc.remainder s1 (by simp [s1, first.res, s2, remainder.res, rv_simp, h8]) (by simp [remainder.res,rv_simp])
  refine ⟨s2,st1.trans (st2),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, remainder.res,rv_simp,h8]
  · simp [s1, first.res, s2, remainder.res,rv_simp,hm]
    simp only [div22 hints (by omega),div22 (hints/22) (by omega),rem22 hints (by omega),rem22 (hints/22) (by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
def lowerPrepCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x341e93,0x1de0e33]
def lowerStoreCode : List (BitVec 32) := bv_list% 32 [0x54e3023,0xf21d206f]
sym_block lowerPrep := symRun {noAlias:=true} lowerPrepCode (pcOf 46918) 6
sym_block lowerStore := symRun {noAlias:=true} lowerStoreCode (pcOf 46922) 4

theorem lowerPrep_steps {im : Image} (hc : CodeAt im (pcOf 46918) lowerPrepCode)
    (s : MachineState) (hp : s.pc=pcOf 46918) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 46922 ∧ t.getReg .x28=BitVec.ofNat 64 (0x66000+8*lay) ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerPrep hc s hp (by simp [lowerPrep.res,rv_simp]),rfl,?_,?_,?_⟩
  · rcases hl with ⟨hl,hu⟩;interval_cases lay <;> simp [lowerPrep.res,rv_simp,h8]
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl

theorem lowerStore_steps {im : Image} (hc : CodeAt im (pcOf 46922) lowerStoreCode)
    (s : MachineState) (hp : s.pc=pcOf 46922) (addr : Nat) (ha : addr+72<2^24) (hal : addr%8=0)
    (h28 : s.getReg .x28=BitVec.ofNat 64 addr) (credit : BitVec 64) (h20 : s.getReg .x20=credit) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 787 ∧ t.getMem (BitVec.ofNat 64 (addr+64))=credit ∧
      RegsExcept s t [] ∧ Frame s t (fun A=>A=addr+64) := by
  refine ⟨_,symRun_sound lowerStore hc s hp (by simp [lowerStore.res,rv_simp,h28,accessValid_iff,MEMORY_BYTES];omega),rfl,?_,?_,?_⟩
  · simp only [Result.toState_getMem,lowerStore.res];t3n [h28,h20]
    try rw [Nat.mod_eq_of_lt (show addr+64<18446744073709551616 by omega),if_pos rfl]
  · intro r hr;cases r <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,lowerStore.res];t3n [h28]
    rw [Nat.mod_eq_of_lt (show addr+64<18446744073709551616 by omega),if_neg (by omega)]

theorem lowerCredit_steps {im : Image} (hc : CodeAt im (pcOf 46918) lowerCreditCode)
    (s : MachineState) (hp : s.pc=pcOf 46918) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (credit : BitVec 64) (hc' : s.getReg .x20=credit) :
    ∃ t,Steps im s 6 6 t ∧ t.pc=pcOf 787 ∧ t.getMem (BitVec.ofNat 64 (0x66040+8*lay))=credit ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun A=>A=0x66040+8*lay) := by
  have prep : CodeAt im (pcOf 46918) lowerPrepCode := by
    simpa using (CodeAt.drop_prefix (pre:=[]) (seg:=lowerPrepCode) (post:=lowerStoreCode) hc)
  have store : CodeAt im (pcOf 46922) lowerStoreCode := by
    simpa [lowerPrepCode,pcOf] using (CodeAt.drop_prefix (pre:=lowerPrepCode) (seg:=lowerStoreCode) (post:=[]) hc)
  obtain ⟨u,su,up,ug,ur,uf⟩:=lowerPrep_steps prep s hp lay hl h8
  have u20 : u.getReg .x20=credit := (ur.get (by decide)).trans hc'
  obtain ⟨t,ut,tp,tg,tr,tf⟩:=lowerStore_steps store u up (0x66000+8*lay) (by omega) (by omega) ug credit u20
  refine ⟨t,su.trans ut,tp,?_,(ur.trans tr).mono (by decide),?_⟩
  · simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tg
  · exact (uf.trans tf).mono (by intro A _ h;rcases h with h|h;exact False.elim h;simp_all [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm])

theorem topCredit_steps {im : Image} (hc : CodeAt im (pcOf 46924) topCreditCode)
    (s : MachineState) (hp : s.pc=pcOf 46924) (acc : Nat) (ha : 12≤acc) (hb : acc<2^64)
    (hx : s.getReg .x20=BitVec.ofNat 64 acc) :
    ∃ t,Steps im s 5 5 t ∧ t.pc=pcOf 776 ∧ t.getMem (0x66040#64)=BitVec.ofNat 64 (acc-12) ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun A=>A=0x66040) := by
  refine ⟨_,symRun_sound topCredit hc s hp (by simp [topCredit.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp only [Result.toState_getMem,topCredit.res];t3n [hx];omega
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn
    simp only [Result.toState_getMem,topCredit.res];t3n []
    rw [if_neg (by omega)]
end ClaudeWCT.W9.Machine.Expand.SharedCounterHooks

namespace ClaudeWCT.W9.Machine.Expand.SharedCounterHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem code_slice {im : Image} {base off : Nat} {words part : List (BitVec 32)}
    (hc : CodeAt im (pcOf base) words) (ho : off+part.length≤words.length)
    (he : (words.drop off).take part.length=part) :
    CodeAt im (pcOf (base+off)) part := by
  have hsplit : words=words.take off ++ part ++ words.drop (off+part.length) := by
    calc
      words = words.take off ++ words.drop off := (List.take_append_drop off words).symm
      _ = words.take off ++ (words.drop off).take part.length ++ (words.drop off).drop part.length := by
        simp only [List.append_assoc,List.take_append_drop]
      _ = words.take off ++ part ++ words.drop (off+part.length) := by rw [he,List.drop_drop]
  rw [hsplit] at hc
  have hh:=CodeAt.drop_prefix hc
  have hl : (words.take off).length=off := by rw [List.length_take,Nat.min_eq_left (by omega)]
  rw [hl] at hh
  convert hh using 1
  simp only [pcOf,←BitVec.ofNat_add]
  congr 1
  omega

theorem code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : Code im := by
  constructor
  · exact code_slice (off:=1849) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1855) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1858) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1860) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1862) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1868) hc (by decide +kernel) (by decide +kernel)
theorem installed_code : Code Images.expandImage := code_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand.SharedCounterHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT WCT9.CanonicalPolicy
def creditAddr (lay : Layer) : Nat := 0x66040+8*lay.val
def CreditW (lay : Layer) (A : Nat) : Prop := A=creditAddr lay ∧ 0x66040≤A ∧ A<0x66060
/-- Floors read from the policy hints (img-v6 mixed radix `484·f1 + 22·f2 + f3`); the top floor is 14. Agrees with
`Research.V7Composed198Gate.hintFloor` (`CanonicalPolicy.topFloor = 14`). -/
def hintFloor (hints : BitVec 16) (lay : Layer) : Nat :=
  if lay=0 then 14 else hints.toNat/22^(3-lay.val)%22
theorem creditAddr_lt (lay : Layer) : creditAddr lay<2^64 := by
  have := lay.isLt;unfold creditAddr;omega
theorem creditAddr_mem (lay : Layer) : CreditW lay (creditAddr lay) := by
  have := lay.isLt
  unfold CreditW creditAddr
  omega
theorem creditW_zero {X : Nat} (h : CreditW 0 X) : X=0x66040 := by
  rcases h with ⟨h,_⟩; rw [h]; rfl
theorem hintFloor_lt (hints : BitVec 16) (lay : Layer) : hintFloor hints lay<22 := by
  unfold hintFloor
  split_ifs
  · omega
  · exact Nat.mod_lt _ (by decide)
theorem hintFloor_top (hints : BitVec 16) : hintFloor hints 0=14 := rfl
theorem flag_not_credit (lay : Layer) : ¬ CreditW lay FLAG := by
  unfold CreditW FLAG; omega
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

def lowerAddCode : List (BitVec 32) := bv_list% 32 [0x41988e33,0xffae0e13,0x1e3e13,0x1ca0a33]
/-- `43024: jal zero, pa` (path-aware lower credit, choice block at 43057). -/
def floorJumpCode : List (BitVec 32) := bv_list% 32 [0x0840006f]
def lowerCreditJumpCode : List (BitVec 32) := bv_list% 32 [0x4c90306f]
def lowerBranchCode : List (BitVec 32) := bv_list% 32 [0x1ca6463]
def lowerBadCode : List (BitVec 32) := bv_list% 32 [0xc85d606f]
sym_block lowerAddRun := symRun {noAlias:=true} lowerAddCode (pcOf 43020) 6
sym_block lowerFloorJumpRun := symRun {noAlias:=true} floorJumpCode (pcOf 43024) 2
sym_block lowerCreditJumpRun := symRun {noAlias:=true} lowerCreditJumpCode (pcOf 43028) 2
sym_block lowerBranchRun := symRun {noAlias:=true} lowerBranchCode (pcOf 43027) 2
sym_block lowerBadRun := symRun {noAlias:=true} lowerBadCode (pcOf 43029) 2

structure Code (image : Image) : Prop where
  scoring : CanonicalReward.PrefixAt image 354
  floorJump : CodeAt image (pcOf 43024) floorJumpCode
  lowerBranch : CodeAt image (pcOf 43027) lowerBranchCode
  lowerJump : CodeAt image (pcOf 43028) lowerCreditJumpCode
  lowerBad : CodeAt image (pcOf 43029) lowerBadCode
  hooks : ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.Code image
  /-- Campaign T51: the top-trial kernel `K` at 54176 (`1272: j 54176`) and the contiguous unpacker
  (54356..54467 | 54468..54521). -/
  t51K : CodeAt image (pcOf 54176) (T51.kCode T51.expandInst)
  t51UA : CodeAt image (pcOf 54356) T51.uCodeA
  t51UB : CodeAt image (pcOf 54468) T51.uCodeB
theorem Code.kAt {image : Image} (h : Code image) : T51.T51KAt image T51.expandInst := T51.expandKAt h.t51K
theorem Code.uAt {image : Image} (h : Code image) : T51.T51UAt image T51.expandInst := T51.expandUAt h.t51UA h.t51UB

theorem lowerAdd_steps {image : Image} (hc : CodeAt image (pcOf 43020) lowerAddCode)
    (s : MachineState) (hp : s.pc=pcOf 43020) (a T S : Nat) (hs : S≤T)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hc8 : T-S<8) :
    ∃ t, Steps image s 4 4 t ∧ t.pc=pcOf 43024 ∧
      t.getReg .x20=BitVec.ofNat 64 (a+if T-S=6 then 1 else 0) ∧
      RegsExcept s t [.x20,.x28] ∧ Frame s t (fun _=>False) := by
  have hsub : s.getReg .x17-s.getReg .x25=BitVec.ofNat 64 (T-S) := by
    rw [h17,h25]
    conv_lhs => lhs; rw [← Nat.sub_add_cancel hs,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hflag := Reward.eq_small (T-S) 6 hc8 (by decide) (by decide)
  change (if (BitVec.ofNat 64 (T-S)+18446744073709551610#64).ult 1#64 then 1#64 else 0#64)=
    BitVec.ofNat 64 (if T-S=6 then 1 else 0) at hflag
  refine ⟨_,symRun_sound lowerAddRun hc s hp (by simp [lowerAddRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · change s.getReg .x20+(if ((s.getReg .x17-s.getReg .x25)+18446744073709551610#64).ult 1#64 then 1#64 else 0#64)=_
    rw [hsub,hflag,h20,BitVec.ofNat_add]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A _ _; rfl

theorem lowerFloorJump_steps {image : Image} (hc : CodeAt image (pcOf 43024) floorJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 43024) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (choiceBase 354+17) ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerFloorJumpRun hc s hp (by simp [lowerFloorJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerCreditJump_steps {image : Image} (hc : CodeAt image (pcOf 43028) lowerCreditJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 43028) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 46918 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerCreditJumpRun hc s hp (by simp [lowerCreditJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerBranch_steps {image : Image} (hc : CodeAt image (pcOf 43027) lowerBranchCode)
    (s : MachineState) (hp : s.pc=pcOf 43027) (a floor : Nat) (ha : a<2^64) (hf : floor<2^64)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) (h28 : s.getReg .x28=BitVec.ofNat 64 floor) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=(if floor≤a then pcOf 43028 else pcOf 43029) ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerBranchRun hc s hp (by simp [lowerBranchRun.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult (s.getReg .x28) then _ else _)=_
    rw [h20,h28,ofNat_ult a floor ha hf]
    split_ifs <;> simp_all [E.eval] <;> omega
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerBad_steps {image : Image} (hc : CodeAt image (pcOf 43029) lowerBadCode)
    (s : MachineState) (hp : s.pc=pcOf 43029) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 822 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerBadRun hc s hp (by simp [lowerBadRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT LowerLUT
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1800000
set_option maxRecDepth 32768

theorem floor_steps {image : Image} (hC : SharedCounterHooks.Code image) (s : MachineState)
    (hp : s.pc=pcOf 46905) (lay : Layer) (hl : lay≠0) (hints : BitVec 16)
    (hh : hints.toNat<8000) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) :
    ∃ t n c, c≤17 ∧ Steps image s n c t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hintFloor hints lay) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  fin_cases lay
  · exact (hl rfl).elim
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor1_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,11,17,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor2_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,11,17,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor3_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,8,11,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩

/-- Lower reward with the path-aware bonus (`pa`, +4 when the LOW half `L` at `EOUT` is spare), floor from the
policy hints. -/
theorem lower_spec {image : Image} (hK : KernAt image 354 (Code image)) (s : MachineState) (lay : Layer) (hl : lay≠0)
    (v : Digest) (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (L : BitVec 128) (hm0 : s.getMem (BitVec.ofNat 64 EOUT)=L.extractLsb' 0 64)
    (hm8 : s.getMem (BitVec.ofNat 64 (EOUT+8))=L.extractLsb' 64 64)
    (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
    (hints : BitVec 16) (hh : hints.toNat<8000) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) (hf : floor=hintFloor hints lay) :
    let a := partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)
    ∃ t n c, c≤(if floor≤a then 110 else 104) ∧ Steps image s n c t ∧
      t.pc=(if floor≤a then pcOf 787 else pcOf 822) ∧
      (floor≤a → t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 a) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t (CreditW lay) := by
  dsimp only
  have hC := hK.reward
  have ha0 : partialScore v 14+(if T-S=6 then 1 else 0)<2^60 := by have h := partial_bound v 14; split_ifs <;> omega
  have ha : partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)<2^64 := by
    split_ifs <;> omega
  have hfloor : floor<2^64 := by have := hintFloor_lt hints lay;omega
  have hlow : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt; have hn : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  obtain ⟨u,su,pu,ux11,ux20,ru,fu⟩ := CanonicalReward.Lower.init_spec (Or.inl rfl) hC.scoring s hp
  obtain ⟨v1,sv,pv,vx,rv,fv⟩ := CanonicalReward.Lower.loop_spec (Or.inl rfl) hC.scoring u v
    (ht.frame fu (by simp)) pu ((ru.get (by decide)).trans h6) ((ru.get (by decide)).trans h7) ux11 ux20 14 (by omega)
  have had : CodeAt image (pcOf 43020) lowerAddCode := by
    have h := CanonicalReward.lower_slice hC.scoring 73 4 (by decide)
    convert h using 1 <;> rfl
  obtain ⟨v2,s2,p2,x2,r2,f2⟩ := lowerAdd_steps had v1 (by simpa [Reward.base] using pv) (partialScore v 14) T S hST vx
    (((ru.trans rv).get (by decide)).trans h17) (((ru.trans rv).get (by decide)).trans h25) hc
  obtain ⟨v3,s3,p3,r3,f3⟩ := lowerFloorJump_steps hC.floorJump v2 p2
  have f03 := ((fu.trans fv).trans f2).trans f3
  obtain ⟨kp,vp,sp,kple,pp,xp,rp,fp⟩ := pa_spec hK v3 p3 L (partialScore v 14+(if T-S=6 then 1 else 0)) (by omega)
    (by rw [f03.get (by decide) (by simp)]; exact hm0) (by rw [f03.get (by decide) (by simp)]; exact hm8)
    (by rw [r3.get (by decide),x2])
  obtain ⟨v4,n4,c4,hc4,s4,p4,x4,r4,f4⟩ := floor_steps hC.hooks vp (by simpa [paTarget] using pp) lay hl hints hh
    (by rw [rp.get (by decide),r3.get (by decide),r2.get (by decide),rv.get (by decide),ru.get (by decide),h8])
    (by rw [fp.get (by decide) (by simp),f03.get (by decide) (by simp),hm])
  have x20 : v4.getReg .x20=BitVec.ofNat 64 (partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)) := by
    rw [r4.get (by decide),xp]
  obtain ⟨v5,s5,p5,r5,f5⟩ := lowerBranch_steps hC.lowerBranch v4 p4 _ floor ha hfloor x20 (by simpa [hf] using x4)
  have rr := ((((ru.trans rv).trans r2).trans r3).trans rp).trans r4
  have ff := (f03.trans fp).trans f4
  by_cases hg : floor≤partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)
  · rw [if_pos hg] at p5
    obtain ⟨v6,s6,p6,r6,f6⟩ := lowerCreditJump_steps hC.lowerJump v5 p5
    obtain ⟨t,st,pt,mt,rt,ft⟩ := SharedCounterHooks.lowerCredit_steps hC.hooks.lowerCredit v6 p6 lay.val hlow
      (by rw [r6.get (by decide),r5.get (by decide),r4.get (by decide),rp.get (by decide),r3.get (by decide),
        r2.get (by decide),rv.get (by decide),ru.get (by decide),h8])
      _ (by rw [r6.get (by decide),r5.get (by decide),x20])
    refine ⟨t,_,_,?_,(((((((su.trans sv).trans s2).trans s3).trans sp).trans s4).trans s5).trans s6).trans st,
      by rw [if_pos hg]; exact pt,fun _=>mt,?_,?_⟩
    · rw [if_pos hg]; omega
    · exact ((rr.trans r5).trans r6).trans rt |>.mono (by decide)
    · exact ((ff.trans f5).trans f6).trans ft |>.mono (by
        intro A hA h; simp only [false_or] at h; subst A; exact creditAddr_mem lay)
  · rw [if_neg hg] at p5
    obtain ⟨t,st,pt,rt,ft⟩ := lowerBad_steps hC.lowerBad v5 p5
    refine ⟨t,_,_,?_,((((((su.trans sv).trans s2).trans s3).trans sp).trans s4).trans s5).trans st,
      by rw [if_neg hg]; exact pt,fun h=>False.elim (hg h),?_,?_⟩
    · rw [if_neg hg]; omega
    · exact (rr.trans r5).trans rt |>.mono (by decide)
    · exact (ff.trans f5).trans ft |>.mono (by simp [CreditW])

end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT WCT9.CanonicalPolicy
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

theorem lower_reward (lay : Layer) (hl : lay≠0) (v : Digest) (T S : Nat) (low : Bool) :
    LowerLUT.partialScore v 14+(if T-S=6 then 1 else 0)+(if low then 4 else 0)=
      credit lay low (lowDigits v++[T-S]) := by
  have h := LowerLUT.packed_reward lay hl v (T-S)
  rw [credit_lower hl]
  simp only [LowerLUT.partialScore,reward] at h ⊢
  omega

theorem lower_spec_credit {image : Image} (hK : KernAt image 354 (Code image)) (s : MachineState) (lay : Layer)
    (hl : lay≠0) (v : Digest) (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (L : BitVec 128) (hm0 : s.getMem (BitVec.ofNat 64 EOUT)=L.extractLsb' 0 64)
    (hm8 : s.getMem (BitVec.ofNat 64 (EOUT+8))=L.extractLsb' 64 64)
    (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
    (hints : BitVec 16) (hh : hints.toNat<8000) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) (hf : floor=hintFloor hints lay) :
    let low := decide (T3.lowerSpare L)
    let good := floor+WCT9.dispatchPenalty lay (lowDigits v++[T-S])≤pathReward lay low (lowDigits v++[T-S])
    ∃ t n c, c≤(if good then 110 else 104) ∧ Steps image s n c t ∧
      t.pc=(if good then pcOf 787 else pcOf 822) ∧
      (good → t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 (credit lay low (lowDigits v++[T-S]))) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t (CreditW lay) := by
  dsimp only
  have h := lower_spec hK s lay hl v ht hp h6 h7 L hm0 hm8 T S floor h17 h25 hST hc hints hh h8 hm hf
  have e := lower_reward lay hl v T S (decide (T3.lowerSpare L))
  have e' : (if T3.lowerSpare L then 4 else 0)=(if decide (T3.lowerSpare L) then 4 else 0) := by
    by_cases hs : T3.lowerSpare L <;> simp [hs]
  have hg : (floor+WCT9.dispatchPenalty lay (lowDigits v++[T-S])≤
      pathReward lay (decide (T3.lowerSpare L)) (lowDigits v++[T-S]))↔
      floor≤credit lay (decide (T3.lowerSpare L)) (lowDigits v++[T-S]) := by
    simp [credit,WCT9.dispatchPenalty,hl]
  dsimp only at h
  rw [e',e] at h
  simpa only [hg] using h
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace ClaudeWCT.W9.Machine.Expand.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_kernel (P : Prop) (hP : P) : KernAt Images.expandImage 354 P := by
  refine ⟨⟨?_,?_⟩,Or.inl rfl,?_,⟨?_,?_,?_⟩,?_,?_,?_,hP⟩
  all_goals apply codeAt_expand_current_chunk <;> decide +kernel

theorem reward_code_of_hooks (hH : SharedCounterHooks.Code Images.expandImage) :
    CanonicalExpandHooks.Code Images.expandImage := by
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,hH,?_,?_,?_⟩
  rotate_right 3
  all_goals first
    | (apply codeAt_t51_at <;> decide +kernel)
    | (apply codeAt_expand_current_chunk <;> decide +kernel)
theorem installed_reward_code : CanonicalExpandHooks.Code Images.expandImage :=
  reward_code_of_hooks SharedCounterHooks.installed_code
theorem installed_searchKernel : KernAt Images.expandImage 354 (CanonicalExpandHooks.Code Images.expandImage) :=
  installed_kernel _ installed_reward_code
end ClaudeWCT.W9.Machine.Expand.SharedSearchCode

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : WCT9.LayerMsg
  ret : Nat
  floor : Nat
  hints : BitVec 16
def csT (lay : Layer) : Nat := if lay = 0 then 755 else 404
def csOk (lay : Layer) : Nat := if lay = 0 then 4096 else 4096
theorem capLimit_le (n : Nat) : capLimit n ≤ 2 ^ 22 := by unfold capLimit; omega
theorem capLimit_eq (lay : Layer) : capLimit lay.val = WCT9.searchLimit lay := by
  fin_cases lay <;> rfl
theorem length_filter_range (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]
/-- Path-aware producer reward test (`low` = the LOW half was selected). -/
def rewardOK (lay : Layer) (floor : Nat) (low : Bool) (ds : List Nat) : Prop :=
  floor + WCT9.dispatchPenalty lay ds ≤ WCT9.CanonicalPolicy.pathReward lay low ds
instance (lay : Layer) (floor : Nat) (low : Bool) (ds : List Nat) : Decidable (rewardOK lay floor low ds) := by
  unfold rewardOK; infer_instance
theorem reward_credit_le {lay : Layer} {floor : Nat} {low : Bool} {ds : List Nat}
    (h : rewardOK lay floor low ds) : floor ≤ WCT9.CanonicalPolicy.credit lay low ds := by
  unfold rewardOK WCT9.CanonicalPolicy.credit at *
  omega
theorem producerDecode_top (v : Digest) (floor : Nat) (low : Bool) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 floor low v =
      if rewardOK 0 floor low ds ∧ WCT9.canonicalZeroBound 0 ds then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.producerRankBound,rewardOK]
  try exact if_congr Iff.rfl rfl rfl
theorem producerDecode_lower {lay : Layer} (hlz : lay≠0) (v : Digest) (floor c : Nat) (low : Bool) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode lay v=some ds) (hds : ds=lowDigits v++[c]) :
    WCT9.CanonicalPolicy.producerDecodeAt lay floor low v=
      if rewardOK lay floor low ds ∧ (lowDigits v++[c]).count 0≤5 ∧ Rank.rankOK v then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.canonicalZeroBound,WCT9.producerZeroCap,WCT9.producerRankBound,
    rewardOK,Rank.rankOK,Rank.rankFloor,WCT9.producerRankFloor,hlz,hds,filter_zero_count]
/-! Producer output on a full 256-bit answer, split by the machine's trial order. -/
theorem producerDecodeOut_top_low (a : BitVec 256) {ds : List Nat}
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 14 true (a.extractLsb' 0 128) = some ds) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 14 a = some (ds, true) := by
  have hg : WCT9.topGood (a.extractLsb' 0 128) := by
    unfold WCT9.topGood; rw [show WCT9.CanonicalPolicy.topFloor = 14 from rfl, h]; rfl
  have hl : WCT9.lowSelected 0 a = true := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hg]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 0 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl, h]; rfl
theorem producerDecodeOut_top_blocked (a : BitVec 256)
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 14 true (a.extractLsb' 0 128) = none)
    (hb : T3.TopChoice.blocked (a.extractLsb' 0 128)) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 14 a = none := by
  have hl : WCT9.lowSelected 0 a = true := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hb]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 0 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl, h]; rfl
theorem producerDecodeOut_top_high (a : BitVec 256)
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 14 true (a.extractLsb' 0 128) = none)
    (hb : ¬ T3.TopChoice.blocked (a.extractLsb' 0 128)) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 14 a =
      (WCT9.CanonicalPolicy.producerDecodeAt 0 14 false (a.extractLsb' 128 128)).map (·, false) := by
  have hg : ¬ WCT9.topGood (a.extractLsb' 0 128) := by
    unfold WCT9.topGood; rw [show WCT9.CanonicalPolicy.topFloor = 14 from rfl, h]; simp
  have hl : WCT9.lowSelected 0 a = false := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hg, hb]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 128 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl]
def cfFlag (_b : Nat) : Nat := 0
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (lay : Layer) (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨
    (DigW A ∨ (CanonicalExpandHooks.CreditW lay A ∨ A = FLAG))
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 32
  x15 : A.tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height A.lay)
  m0 : s.getMem (BitVec.ofNat 64 ENC) = (left A.msg).extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = (left A.msg).extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right A.msg).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right A.msg).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
  reward : Reward.RewardTablesOK s
  zt : ZeroCap.ZtOK b s
  floorLt : A.floor<22
  floorTop : A.lay=0 → A.floor=14
  hintsLt : A.hints.toNat<8000
  floorEq : A.floor=CanonicalExpandHooks.hintFloor A.hints A.lay
  floorMem : s.getMem (0x66000#64)=BitVec.ofNat 64 A.hints.toNat
  /-- Campaign T51: the packed top tables in RAM at 0xA0000 (`T51.expandInst.blk`, copied by KCOPY 54522 from the
  data block 0xFF9E00) for the top search. -/
  t51table : A.lay=0 → T51.T51TableW 0xA0000 s
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (capBase b)
  hi : i ≤ capLimit A.lay.val
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t (CsW A.lay)
def DummyOut (A : CsArgs) (s0 t : MachineState) : Prop :=
  t.pc = pcOf A.ret ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s0 t csRegs ∧ Frame s0 t (CsW A.lay) ∧
    (t.getReg .x25).toNat ≤ 129
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) :
    Option (BitVec 32 × List Nat × Bool) → MachineState → Prop
  | none, t => t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds, low), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, WCT9.CanonicalPolicy.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t (CsW A.lay) ∧
      (A.lay ≠ 0 → (t.getReg .x25).toNat ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) ∧
      t.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds) ∧
      A.floor ≤ WCT9.CanonicalPolicy.credit A.lay low ds ∧
      (A.lay=0 → t.getMem (BitVec.ofNat 64 FLAG)=BitVec.ofNat 64 (if low then 0 else 128))
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u (CsW A.lay)
theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem TrialSt.stepCredit {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat}
    (h : TrialSt b A s0 i u) {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r=>decide (r∈csRegs ∧ r≠.x19))=true)
    (hf : Frame u u' (CanonicalExpandHooks.CreditW A.lay)) : TrialSt b A s0 i u' := by
  have hL' : ∀ r∈L, r∈csRegs ∧ r≠.x19 := fun r hr=>by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr.get (fun h'=>(hL' _ h').2 rfl),h.x19]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.h16]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.h24]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.c32]
  · exact (h.regs.trans hr).mono (fun r hr'=>by rcases List.mem_append.1 hr' with h1|h1;exact h1;exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h'=>by
      rcases h' with h'|h';exact h';exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))
theorem TrialSt.stepFlag {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat}
    (h : TrialSt b A s0 i u) {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r=>decide (r∈csRegs ∧ r≠.x19))=true)
    (hf : Frame u u' (fun A => A = FLAG)) : TrialSt b A s0 i u' := by
  have hL' : ∀ r∈L, r∈csRegs ∧ r≠.x19 := fun r hr=>by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr.get (fun h'=>(hL' _ h').2 rfl),h.x19]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.h16]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.h24]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.c32]
  · exact (h.regs.trans hr).mono (fun r hr'=>by rcases List.mem_append.1 hr' with h1|h1;exact h1;exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h'=>by
      rcases h' with h'|h';exact h';exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))))
theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr
/-- A step that writes only inside `CsW`, away from the counter cells. -/
theorem TrialSt.stepW {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L) (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true)
    {W : Nat → Prop} (hf : Frame u u' W) (hW : ∀ X, W X → CsW A.lay X)
    (hC : ∀ X, W X → X ≠ ENC + 16 ∧ X ≠ ENC + 24 ∧ X ≠ ENC + 32) : TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by unfold ENC; omega) (fun hw => (hC _ hw).1 rfl), h.h16]
  · rw [hf.get (by unfold ENC; omega) (fun hw => (hC _ hw).2.1 rfl), h.h24]
  · rw [hf.get (by unfold ENC; omega) (fun hw => (hC _ hw).2.2 rfl), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun X _ h' => by rcases h' with h' | h'; exact h'; exact hW X h')
section trial
variable {image : Image} {b : Nat} {sk : BitVec 256}
theorem cs_next {A : CsArgs} {s0 u : MachineState} {i F W : Nat} {Q : Option (BitVec 32 × List Nat × Bool) → MachineState → Prop}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 468)) (hi : i < capLimit A.lay.val)
    (ih : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t W (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i + 1) F) Q) :
    TBSim image sk u (2 + W) (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i + 1) F) Q := by
  obtain ⟨t1, s1, p1, h19, r1, f1⟩ := cs468_spec hK u hpc i hu.x19
  have hcap := capLimit_le A.lay.val
  refine TBSim.steps s1 (ih t1 ⟨p1, by omega, h19, ?_, ?_, ⟨i, by omega, ?_⟩, ?_, ?_⟩)
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h16]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h24]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.c32]
  · exact (hu.regs.trans r1).mono (by decide)
  · exact (hu.frame.trans f1).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 51 else 43 := by
  fin_cases lay <;> rfl

theorem target_lt (lay : Layer) : T3.target lay < 2 ^ 63 := by
  fin_cases lay <;> decide
theorem getD_map_range {f : Nat → Nat} {n j : Nat} (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]
structure RewardReady (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (ds : List Nat) (low : Bool)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf A.ret
  trial : TrialSt b A s0 i t
  len : ds.length=T3.chainCount A.lay
  digs : ∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)
  sum : A.lay ≠ 0 → (t.getReg .x25).toNat ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)
  credit : t.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds)
theorem cs_success {A : CsArgs} {s0 u : MachineState} {i : Nat} {ds : List Nat} {low : Bool}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0) (hu : RewardReady b A s0 i ds low u)
    (hi : i < capLimit A.lay.val) (answer : Digest) (hdec : WCT9.CanonicalPolicy.decode A.lay answer = some ds)
    (hfloor : A.floor ≤ WCT9.CanonicalPolicy.credit A.lay low ds)
    (hflag : A.lay=0 → u.getMem (BitVec.ofNat 64 FLAG)=BitVec.ofNat 64 (if low then 0 else 128)) :
    TBSim image sk u 0 (pure (some (BitVec.ofNat 32 i,ds,low))) (CsPost image b A s0) := by
  have hcap := capLimit_le A.lay.val
  have hc : (BitVec.ofNat 32 i).toNat=i := by rw [BitVec.toNat_ofNat]; omega
  refine TBSim.pure ⟨hu.pc,?_,?_,?_,⟨answer,hdec⟩,hu.len,hu.digs,hu.trial.regs,hu.trial.frame,hu.sum,hu.credit,hfloor,hflag⟩
  · rw [hc]; omega
  · rw [hc]; exact hu.trial.x19
  · rw [hc]; exact hu.trial.c32

theorem cs_prepare {A : CsArgs} {s0 u : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 433)) (hi : i < 2 ^ 22) (hlz : A.lay ≠ 0)
    (v : Digest) (hv : T3.lowerSpare v) (S : Nat) (ds : List Nat) (hdec : WCT9.CanonicalPolicy.decode A.lay v = some ds)
    (hds : ds = lowDigits v ++ [T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) - S]) (hS : S ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h25 : u.getReg .x25 = BitVec.ofNat 64 S) (low : Bool)
    (hcredit : u.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds)) :
    ∃ k t, Steps image u k k t ∧ k ≤ 815 ∧ RewardReady b A s0 i ds low t := by
  have hl0 : A.lay.val ≠ 0 := fun h => hlz (Fin.ext h)
  obtain ⟨u1, su1, pu1, a6, a7, ru1, fu1⟩ := Credit.align_spec hK u hpc v hv h6 h7
  have hu1 := hu.step ru1 (by decide) fu1
  obtain ⟨k, t, st, kle, tpc, tdig, tchk, tr, tf⟩ := cs_tail hK u1 pu1 (BitVec.ofNat 128 (T3.lowerWord v)) A.lay.val
    (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) S A.ret A.lay.isLt (target_lt _) (fun _ => hS)
    (by rw [hu1.reg (by decide), hpre.x1]) (by rw [hu1.reg (by decide), hpre.x8])
    (by rw [hu1.reg (by decide), hpre.x17]) (by rw [ru1.get (by decide), h25])
    (by rw [hu1.reg (by decide), hpre.x26, chainCount_eq]; simp [hlz, hl0])
    (by rw [hu1.reg (by decide), hpre.x27, csN4]; simp [hlz, hl0]) a6 a7
  rw [if_neg hl0] at kle tdig
  have hfr := (hu1.frame.trans tf).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have hregs : RegsExcept s0 t csRegs := (hu1.regs.trans tr).mono (by decide)
  refine ⟨5+k,t,su1.trans st,by omega,?_,?_,?_,?_,?_,?_⟩
  · simpa [hlz] using tpc
  · refine ⟨?_,?_,?_,?_,hregs,hfr⟩
    · rw [tr.get (by decide),hu1.x19]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.h16]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.h24]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.c32]
  · rw [hds,chainCount_eq,if_neg hlz]; simp [lowDigits_length]
  · intro j hj
    rw [chainCount_eq,if_neg hlz] at hj
    rw [hds]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length];exact hj),lowDigits_eq,getD_map_range hj]
      simpa only [if_neg hl0] using tdig j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [lowDigits_length]),lowDigits_length]
      simpa using tchk hl0
  · intro _
    rw [tr.get (by decide),ru1.get (by decide),h25,BitVec.toNat_ofNat]
    have := target_lt (WCT9.CanonicalPolicy.normalLayer A.lay)
    omega
  · rw [tf.get (CanonicalExpandHooks.creditAddr_lt _) (by unfold CanonicalExpandHooks.creditAddr DigW DIGITS;omega),fu1.get (CanonicalExpandHooks.creditAddr_lt _) (by simp),hcredit]
theorem TrialSt.table {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : TableOK s0) : TableOK u :=
  ht.frame hu.frame (by intro j hj; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.cf {A : CsArgs} {s0 u : MachineState} {i : Nat} {flag : Nat}
    (hu : TrialSt b A s0 i u) (ht : CfTableOK flag s0) : CfTableOK flag u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.reward {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : Reward.RewardTablesOK s0) : Reward.RewardTablesOK u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.zt {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : ZeroCap.ZtOK 354 s0) : ZeroCap.ZtOK 354 u :=
  ht.frame hu.frame (by
    intro j hj
    simp only [ZeroCap.ZT, CsW, CanonicalExpandHooks.CreditW, DigW, ENC, EOUT, DIGITS, FLAG] <;> norm_num <;> omega)
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < capLimit A.lay.val) :
    ∃ k t2, Steps image t k k t2 ∧ k ≤ 14 ∧ t2.pc = pcOf (b + 123) ∧
      fetch image t2 = some (.base .ECALL) ∧
      t2.getReg .x5 = 0 ∧ hashArgumentsValid t2 = true ∧
      hashInput t2 = toQ (T3.pad64 (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i))) ∧
      t2.getReg .x12 = BitVec.ofNat 64 EOUT ∧ TrialSt b A s0 i t2 := by
  have hcap := capLimit_le A.lay.val
  obtain ⟨k1, t1, s1, k1le, p1, r1, f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide), hpre.x8]) hI.x19
  rw [if_neg (by omega)] at p1
  obtain ⟨x, hx, hx32⟩ := hI.c32
  obtain ⟨t2, s2, p2, c32, h10, h11, h12, r2, f2⟩ := cs115_spec hK t1 p1 i x (by omega) hx
    (by rw [r1.get (by decide), hI.x19]) (by rw [f1.get (by simp only [ENC]; omega) (by simp), hx32])
  have fr : Frame s0 t2 (CsW A.lay) := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
    simp only [or_false] at h; rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h)))
  have mem : ∀ addr, addr < 2 ^ 64 → ¬ CsW A.lay addr → t2.getMem (BitVec.ofNat 64 addr) = s0.getMem (BitVec.ofNat 64 addr) :=
    fun addr hA hn => fr.get hA hn
  have hT : TrialSt b A s0 i t2 := by
    refine ⟨?_, ?_, ?_, c32, ((hI.regs.trans r1).trans r2).mono (by decide), fr⟩
    · rw [r2.get (by decide), r1.get (by decide), hI.x19]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h16]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h24]
  have hk : k1 + 8 ≤ 14 := by omega
  refine ⟨_, t2, s1.trans s2, hk, p2, (codeAt_k_123 hK).fetch _ p2, by rw [hT.reg (by decide), hpre.x5],
    hashArgs_const t2 ENC 64 EOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, h12, hT⟩
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine hashInput_toQ t2 _ 0 ENC (BC.encodingInput_length _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [readWords_eight, BC.wordsOf_encodingInput, hc]
  have nw : ∀ addr, addr = ENC ∨ addr = ENC + 8 ∨ addr = ENC + 40 ∨ addr = ENC + 48 ∨ addr = ENC + 56 → ¬ CsW A.lay addr := by
    intro A hA; simp only [CsW, CanonicalExpandHooks.CreditW, DigW, ENC, EOUT, DIGITS, FLAG] at hA ⊢; omega
  rw [mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hT.h16, hT.h24, c32, mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hpre.m0, hpre.m8, hpre.z40, hpre.r48, hpre.r56]
theorem TrialSt.hash {A : CsArgs} {s0 t2 : MachineState} {i : Nat} (hT : TrialSt b A s0 i t2)
    (h12 : t2.getReg .x12 = BitVec.ofNat 64 EOUT) (a : BitVec 256) : TrialSt b A s0 i (writeHash t2 a) := by
  have fw := Frame.writeHash t2 a EOUT h12 (by decide)
  refine ⟨by rw [getReg_writeHash, hT.x19], ?_, ?_, ?_, ?_, ?_⟩
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h16]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h24]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.c32]
  · intro r hr; rw [getReg_writeHash]; exact hT.regs r hr
  · exact (hT.frame.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem cfFlag_lt (b : Nat) : cfFlag b < 256 := by change 0<256;decide
theorem cs_exhaust {A : CsArgs} {s0 t : MachineState} {i : Nat}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i=capLimit A.lay.val) :
    TBSim image sk t (0*csT A.lay+csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i 0)
      (CsPost image b A s0) := by
  obtain ⟨k1,t1,s1,k1le,p1,r1,f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide),hpre.x8]) hI.x19
  rw [if_pos hi] at p1
  have hk1 : k1≤6 := k1le
  have h8 : t1.getReg .x8=BitVec.ofNat 64 A.lay.val := by
    rw [r1.get (by decide),hI.regs.get (by decide),hpre.x8]
  have fr1 : Frame s0 t1 (CsW A.lay) := (hI.frame.trans f1).mono (fun A _ h=>by simpa using h)
  have hcf : CfTableOK 0 t1 := hpre.cf.frame fr1
    (by intro j hj hj';unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG;omega)
  obtain ⟨n,t2,hn,s2,p2,r2,f2⟩ := Credit.exhaust_fail hK t1 p1 A.lay.val A.lay.isLt h8 0
    (by decide) hcf (Or.inr rfl)
  obtain ⟨t3,s3,p3,h5,h10,hf⟩ := cs0_spec hK t2 p2
  change TBSim image sk t _ (pure none) _
  refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure ?_)).mono ?_ (fun _ _ h=>h)
  · exact ⟨p3,h5,h10,hf⟩
  · unfold csOk;split_ifs <;> omega

end trial
end SigGolfCandidate.T3M.Search.CanonicalExpand

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
variable {image : Image} {sk : BitVec 256}
theorem cs_loop {A : CsArgs} {s0 : MachineState} (hK : KernAt image 354 (CanonicalExpandHooks.Code image)) (hpre : CsPre 354 A s0) :
    ∀ F i t, i + F = capLimit A.lay.val → CsInv 354 A s0 i t →
      TBSim image sk t (F * csT A.lay + csOk A.lay) (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i F)
        (CsPost image 354 A s0) := by
  have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := ⟨fun h => Fin.ext h,fun h => by rw [h];rfl⟩
  have hcap := capLimit_le A.lay.val
  intro F
  induction F with
  | zero =>
    intro i t h hI
    exact cs_exhaust hK hpre hI (by omega)
  | succ F ih =>
    intro i t h hI
    have hi : i < capLimit A.lay.val := by omega
    have hi22 : i < 2 ^ 22 := by omega
    obtain ⟨k2,t2,s2,k2le,p2,hf,h5,hv,hq,h12,hT⟩ := cs_answer hK hpre hI hi
    have prog : WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i (F+1) =
        (T3.publicHash (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i)) >>= fun answer =>
          match WCT9.CanonicalPolicy.producerDecodeOut A.lay A.floor answer with
          | none => WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i+1) F
          | some found => pure (some (BitVec.ofNat 32 i,found))) := rfl
    have ih' : ∀ t, CsInv 354 A s0 (i+1) t → TBSim image sk t (F*csT A.lay+csOk A.lay)
        (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i+1) F) (CsPost image 354 A s0) :=
      fun t ht => ih (i+1) t (by omega) ht
    rw [prog]
    refine (TBSim.steps s2 (TBSim.publicHash_bindC hf h5 hv hq
      (W:=F*csT A.lay+csOk A.lay+(csT A.lay-22)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [BC.blocks_encodingInput,Nat.succ_mul];unfold csT at *;split_ifs at k2le ⊢ <;> omega
    have hT3 := hT.hash h12 a
    have p3 : (writeHash t2 a).pc=pcOf (354+124) := by rw [pc_writeHash,p2,pcOf_add4]
    have hd := DigAt.writeHash_lo t2 a EOUT h12 (by decide)
    have hhi := DigAt.writeHash_hi t2 a EOUT h12 (by decide)
    obtain ⟨t4,s4,p4,h6,h7,h25,r4,f4⟩ := cs124_spec hK (writeHash t2 a) p3 A.lay.val A.lay.isLt
      (by rw [hT3.reg (by decide),hpre.x8])
    rw [hd.1] at h6
    rw [hd.2] at h7
    have hT4 := hT3.step r4 (by decide) f4
    -- the answer halves stay in `EOUT .. EOUT + 32` (frames below never write there)
    have mL0 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 EOUT) = t4.getMem (BitVec.ofNat 64 EOUT) →
        w.getMem (BitVec.ofNat 64 EOUT) = (a.extractLsb' 0 128).extractLsb' 0 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hd.1
    have mL8 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+8)) = t4.getMem (BitVec.ofNat 64 (EOUT+8)) →
        w.getMem (BitVec.ofNat 64 (EOUT+8)) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hd.2
    have mH0 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+16)) = t4.getMem (BitVec.ofNat 64 (EOUT+16)) →
        w.getMem (BitVec.ofNat 64 (EOUT+16)) = (a.extractLsb' 128 128).extractLsb' 0 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hhi.1
    have mH8 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+24)) = t4.getMem (BitVec.ofNat 64 (EOUT+24)) →
        w.getMem (BitVec.ofNat 64 (EOUT+24)) = (a.extractLsb' 128 128).extractLsb' 64 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hhi.2
    by_cases hlz : A.lay=0
    · rw [if_pos (hl0.2 hlz)] at p4
      have hfl : A.floor = 14 := hpre.floorTop hlz
      have e : WCT9.CanonicalPolicy.producerDecodeOut A.lay A.floor a = WCT9.CanonicalPolicy.producerDecodeOut 0 14 a := by
        rw [hlz,hfl]
      rw [e]
      -- T51: `tcEntry 354` (1272) jumps to the T51 kernel `K_ENTRY` (54176)
      obtain ⟨tg,sg,pg,rg,fg⟩ := top_entry_spec hK t4 p4
      have hTg := hT4.step rg (by decide) fg
      have hKT : T51.T51KAt image T51.expandInst := CanonicalExpandHooks.Code.kAt hK.reward
      have hUT : T51.T51UAt image T51.expandInst := CanonicalExpandHooks.Code.uAt hK.reward
      have fgE : ∀ X, X < 2^64 → tg.getMem (BitVec.ofNat 64 X) = t4.getMem (BitVec.ofNat 64 X) :=
        fun X hX => fg.get hX (by simp)
      have h6g : tg.getReg .x6 = (a.extractLsb' 0 128).extractLsb' 0 64 := by rw [rg.get (by decide),h6]
      have h7g : tg.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64 := by rw [rg.get (by decide),h7]
      have h12g : tg.getReg .x12 = BitVec.ofNat 64 EOUT := by
        rw [rg.get (by decide),r4.get (by decide),getReg_writeHash,h12]
      have h17g : tg.getReg .x17 = BitVec.ofNat 64 (T3.target 0) := by
        rw [hTg.reg (by decide),hpre.x17,hlz]; rfl
      have htg : T51.T51TableW T51.expandInst.blk tg := (hpre.t51table hlz).frame hTg.frame (by decide) (by decide)
        (by intro k hk; unfold CsW CanonicalExpandHooks.CreditW CanonicalExpandHooks.creditAddr DigW ENC EOUT DIGITS FLAG; omega)
      obtain ⟨hAcc,hRej⟩ := T51.trial hKT tg (by rw [pg]; rfl) a h6g h7g h12g
        (mH0 tg (fgE _ (by unfold EOUT;omega))) (mH8 tg (fgE _ (by unfold EOUT;omega))) h17g htg
      cases hD : WCT9.CanonicalPolicy.producerDecodeOut 0 14 a with
      | some found =>
        obtain ⟨ds,low⟩ := found
        obtain ⟨k,t,st,kle,pt,t6,t7,hdec,t28,tcr,tfl,rt,ft⟩ := hAcc ds low hD
        have hTt := hTg.stepW rt (by decide) ft (fun X hX => by
          rcases hX with hX | hX
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            rw [hlz, hX]; exact CanonicalExpandHooks.creditAddr_mem 0
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hX))))))
          (fun X hX => by rcases hX with rfl | rfl <;> decide)
        obtain ⟨t',st',pt',tdig,rt',ft'⟩ := T51.unpack hUT t pt _ ds hdec t6 t7 t28
        have hTt' := hTt.stepW rt' (by decide) ft' (fun X hX => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX)))))
          (fun X hX => by unfold ENC DIGITS at *; omega)
        have hret : t.getReg .x1 = pcOf A.ret := by rw [hTt.reg (by decide),hpre.x1]
        have hlen : ds.length = T3.chainCount A.lay := by
          rw [hlz]; exact T51.decode_length hdec
        have hR' : RewardReady 354 A s0 i ds low t' := by
          refine ⟨?_,hTt',hlen,?_,fun h => absurd hlz h,?_⟩
          · rw [pt',hret]; exact pcOf_and_not1 _
          · intro j hj; rw [hlz] at hj; exact tdig j hj
          · rw [ft'.get (CanonicalExpandHooks.creditAddr_lt _)
              (by unfold CanonicalExpandHooks.creditAddr DIGITS; omega),hlz]
            exact tcr
        have done := cs_success (sk:=sk) hK hpre hR' hi _ (by rw [hlz]; exact hdec)
          (by rw [hfl,hlz]; exact T51.producerDecodeOut_floor hD)
          (fun _ => by rw [ft'.get (by decide) (by unfold DIGITS FLAG; omega)]; exact tfl)
        refine (TBSim.steps ((s4.trans sg).trans (st.trans st')) done).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_pos hlz,T51.expandInst];omega
      | none =>
        obtain ⟨k,t,st,kle,pt,rt,ft⟩ := hRej hD
        have hTt := hTg.step rt (by decide) ft
        refine (TBSim.steps ((s4.trans sg).trans st) (cs_next hK hTt pt hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_pos hlz];omega
    · rw [if_neg (fun h => hlz (hl0.1 h))] at p4
      set v := WCT9.encodingAnswer A.lay a with hvdef
      set low := decide (T3.lowerSpare (a.extractLsb' 0 128)) with hlowdef
      have hlow : WCT9.lowSelected A.lay a = low := by simp [WCT9.lowSelected,hlz,hlowdef]
      unfold WCT9.CanonicalPolicy.producerDecodeOut
      rw [hlow]
      obtain ⟨td,sd,pd,rd,fd⟩ := cs130_spec hK t4 p4
      have hTd := hT4.step rd (by decide) fd
      obtain ⟨ks,t5,ss,hs7,p5,h6s,h7s,r5,f5⟩ := selector_spec hK td pd a A.lay hlz
        ((rd.get (by decide)).trans h6) ((rd.get (by decide)).trans h7)
        (by rw [rd.get (by decide),r4.get (by decide),getReg_writeHash,h12])
        (by rw [fd.get (by unfold EOUT;omega) (by simp),f4.get (by unfold EOUT;omega) (by simp)];exact hhi.1)
        (by rw [fd.get (by unfold EOUT;omega) (by simp),f4.get (by unfold EOUT;omega) (by simp)];exact hhi.2)
      have s5 := sd.trans ss
      have hT5 := hTd.step r5 (by decide) f5
      change t5.pc=(if T3.lowerSpare v then _ else _) at p5
      change t5.getReg .x6=v.extractLsb' 0 64 at h6s
      change t5.getReg .x7=v.extractLsb' 64 64 at h7s
      have hnormal : WCT9.CanonicalPolicy.normalLayer A.lay≠0 := by
        simp [WCT9.CanonicalPolicy.normalLayer,hlz]
      have hdec := decode_low (WCT9.CanonicalPolicy.normalLayer A.lay) hnormal v
      change WCT9.CanonicalPolicy.decode A.lay v=_ at hdec
      by_cases hr : T3.lowerSpare v
      · rw [if_pos hr] at p5
        obtain ⟨t6,s6,p6,h25',h28',r6,f6⟩ := cs132_spec hK t5 p5 v (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) (target_lt _) h6s h7s
          (by rw [r5.get (by decide),rd.get (by decide),h25]) (by rw [hT5.reg (by decide),hpre.x17])
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : (lowDigits v).sum≤T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) ∧ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum<8
        · rw [if_pos hs] at p6
          obtain ⟨t7,s7,p7,r7,f7⟩ := cs259_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          have hd' : WCT9.CanonicalPolicy.decode A.lay v=some (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) := by rw [hdec,if_pos ⟨hr,hs⟩]
          rw [producerDecode_lower hlz v A.floor _ low hd' rfl]
          obtain ⟨k8,n8,t8,s8,n8le,p8,r8,f8⟩ := zero_rank_spec hK t7 p7 v (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
            (by
              have h : ∀ lay : T3.Layer,T3.target lay<256 := by decide
              exact h (WCT9.CanonicalPolicy.normalLayer A.lay)) hs.1
            (by rw [r7.get (by decide),r6.get (by decide),h6s])
            (by rw [r7.get (by decide),r6.get (by decide),h7s])
            (by rw [hT7.reg (by decide),hpre.x17]) (by rw [r7.get (by decide),h25'])
            (lowZeros_bound v (by
              have hmin : ∀ lay : T3.Layer,lay≠0 → 199≤T3.target lay := by decide
              have ht := hmin (WCT9.CanonicalPolicy.normalLayer A.lay) hnormal;omega))
          have hT8 := hT7.step r8 (by decide) f8
          have fL8 : Frame t4 t8 (fun _ => False) := ((((((fd.trans f5).trans f6).trans f7).trans f8)).mono
            (fun A _ h => by simp at h))
          by_cases hok : (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]).count 0≤5 ∧ Rank.rankOK v
          · rw [if_pos hok] at p8
            have hTables : Reward.RewardTablesOK t8 := hpre.reward.frame hT8.frame
              (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
            obtain ⟨tR,nR,cR,hcR,sR,pR,mR,rR,fR⟩ := CanonicalExpandHooks.lower_spec_credit hK t8 A.lay hlz v hTables p8
              (by rw [r8.get (by decide),r7.get (by decide),r6.get (by decide),h6s])
              (by rw [r8.get (by decide),r7.get (by decide),r6.get (by decide),h7s])
              (a.extractLsb' 0 128) (mL0 t8 (fL8.get (by decide) (by simp))) (mL8 t8 (fL8.get (by decide) (by simp)))
              (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) (lowDigits v).sum A.floor
              (by rw [hT8.reg (by decide),hpre.x17])
              (by rw [r8.get (by decide),r7.get (by decide),h25']) hs.1 hs.2 A.hints hpre.hintsLt
              (by rw [hT8.reg (by decide),hpre.x8])
              (by rw [hT8.frame.get (by decide) (by unfold CsW CanonicalExpandHooks.CreditW ENC EOUT DigW DIGITS FLAG;omega),hpre.floorMem])
              hpre.floorEq
            have hTR := hT8.stepCredit rR (by decide) fR
            change tR.pc=(if rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum])
              then pcOf (354+433) else pcOf (354+468)) at pR
            change cR≤(if rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) then 110 else 104) at hcR
            change (rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) → _) at mR
            by_cases hreward : rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum])
            · rw [if_pos hreward] at pR hcR
              simp only [hreward,hok,and_self,if_true]
              obtain ⟨k9,t9,s9,k9le,hR⟩ := cs_prepare hK hpre hTR pR hi22 hlz v hr _ _ hd' rfl hs.1
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),r6.get (by decide),h6s])
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),r6.get (by decide),h7s])
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),h25']) low (mR hreward)
              have done := cs_success (sk:=sk) hK hpre hR hi v hd' (reward_credit_le hreward) (fun h => absurd h hlz)
              refine (TBSim.steps ((((((s4.trans s5).trans s6).trans s7).trans s8).trans sR).trans s9) done).mono ?_ (fun _ _ h => h)
              simp only [csT,csOk,if_neg hlz];omega
            · rw [if_neg hreward] at pR hcR
              simp only [hreward,false_and,if_false]
              refine (TBSim.steps (((((s4.trans s5).trans s6).trans s7).trans s8).trans sR)
                (cs_next hK hTR pR hi ih')).mono ?_ (fun _ _ h => h)
              simp only [csT,csOk,if_neg hlz];omega
          · rw [if_neg hok] at p8
            have hno : ¬ (rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) ∧
                (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]).count 0≤5 ∧ Rank.rankOK v) := fun hh => hok hh.2
            simp only [if_neg hno]
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_next hK hT8 p8 hi ih')).mono ?_ (fun _ _ h => h)
            simp only [csT,csOk,if_neg hlz];omega
        · rw [if_neg hs] at p6
          have hd' : WCT9.CanonicalPolicy.decode A.lay v=none := by rw [hdec,if_neg (fun h => hs h.2)]
          have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor low v=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
          rw [hpd]
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          simp only [csT,csOk,if_neg hlz];omega
      · rw [if_neg hr] at p5
        have hd' : WCT9.CanonicalPolicy.decode A.lay v=none := by rw [hdec,if_neg (fun h => hr h.1)]
        have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor low v=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
        rw [hpd]
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_neg hlz];omega
end SigGolfCandidate.T3M.Search.CanonicalExpand

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
variable {image : Image} {sk : BitVec 256}
theorem counterSearch_tbsim {A : CsArgs} {s0 : MachineState} (hK : KernAt image 354 (CanonicalExpandHooks.Code image)) (hpre : CsPre 354 A s0) :
    TBSim image sk s0 (18 + capLimit A.lay.val * csT A.lay + csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay)) (CsPost image 354 A s0) := by
  obtain ⟨t, st, pt, h16, h24, h19, rt, ft⟩ := cs103_spec hK s0 hpre.pc A.lay A.tree A.leaf hpre.hroute
    hpre.x8 hpre.x9 hpre.x18 hpre.x15
  obtain ⟨t', st', pt', rt', ft'⟩ := cs113_spec hK t pt
  have hI : CsInv 354 A s0 0 t' := by
    refine ⟨pt', Nat.zero_le _, by rw [rt'.get (by decide), h19], by rw [ft'.get (by simp only [ENC]; omega) (by simp), h16],
      by rw [ft'.get (by simp only [ENC]; omega) (by simp), h24], ?_,
      (rt.trans rt').mono (by decide), (ft.trans ft').mono (fun A _ h => by
        rcases h with h | h
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact absurd h id)⟩
    obtain ⟨x, hx, hx32⟩ := hpre.c32
    exact ⟨x, hx, by rw [ft'.get (by simp only [ENC]; omega) (by simp), ft.get (by simp only [ENC]; omega)
      (by simp only [ENC]; omega), hx32]⟩
  rw [← capLimit_eq]
  have := TBSim.steps st (TBSim.steps st' (cs_loop (sk := sk) hK hpre (capLimit A.lay.val) 0 t' (by omega) hI))
  exact this.mono (le_of_eq (by ring)) (fun _ _ h => h)

def csCost (lay : Layer) : Nat := (WCT9.searchLimit lay * csT lay)+8192

theorem counterSearch_good {A : CsArgs} {s0 : MachineState}
    (hK : KernAt image 354 (CanonicalExpandHooks.Code image)) (hp : CsPre 354 A s0) :
    TBSim image sk s0 (csCost A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
      (CsPost image 354 A s0) := by
  refine (counterSearch_tbsim hK hp).mono ?_ (fun _ _ h=>h)
  rw [capLimit_eq]
  unfold csCost csOk
  split_ifs <;> omega
end SigGolfCandidate.T3M.Search.CanonicalExpand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_EndRoutine ====
section

/-! # Expand `end` routine (configuration e7b)

Word 47011 (formerly `addi a0,zero,0`) is `jal zero, 43071`. The routine at 43071..43076 loads the choice flag word
`mem[0x667F8]` (0, or 128 after the producer took HIGH), stores its low byte at abs 25216 = `WIT + choiceOff`
(`sb t1, 640(0x6000)`), sets `a0 := 0` and jumps to the witness-stack post-pass at 49400 (img-merged; was the halting `ecall` at
47012). -/

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def endCode : List (BitVec 32) := bv_list% 32 [0x00066e37,0x7f8e3303,0x00006e37,0x286e0023,0x00000513,0x2d00606f]
sym_block endRun := symRun { noAlias := true } endCode (pcOf 43071) 20

/-- The flag byte written by `end`. -/
def flagByte (s : MachineState) : BitVec 8 := (s.getMem (BitVec.ofNat 64 0x667F8)).truncate 8

theorem end_mem (s : MachineState) (A : Nat) (hA : A < 2^64) :
    (endRun.res.toState s).getMem (BitVec.ofNat 64 A) =
      if A = 25216 then replaceByte (s.getMem (BitVec.ofNat 64 25216)) 0 (flagByte s)
      else s.getMem (BitVec.ofNat 64 A) := by
  simp only [Result.toState_getMem,endRun.res,flagByte]
  t3n []
  all_goals (try rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)])
  all_goals (split_ifs <;> first | rfl | omega)

theorem end_steps {im : Image} (hc : CodeAt im (pcOf 43071) endCode)
    (s : MachineState) (hpc : s.pc=pcOf 43071) :
    ∃t, Steps im s 6 6 t ∧ t.pc=pcOf 49400 ∧ t.getReg .x10=0#64 ∧
      t.getMem (BitVec.ofNat 64 25216)=replaceByte (s.getMem (BitVec.ofNat 64 25216)) 0 (flagByte s) ∧
      RegsExcept s t [.x6,.x10,.x28] ∧ Frame s t (fun A=>A=25216) := by
  refine ⟨_,symRun_sound endRun hc s hpc (by simp [endRun.res,rv_simp,accessValid_iff,MEMORY_BYTES]),?_,?_,?_,?_,?_⟩
  · simp [endRun.res, Result.toState_pc, E.eval]
  · simp [endRun.res, rv_simp]
  · rw [end_mem s 25216 (by norm_num), if_pos rfl]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    rw [end_mem s A hA, if_neg hn]

theorem installed_end : CodeAt Images.expandImage (pcOf 43071) endCode := by
  apply codeAt_expand_current_chunk <;> decide +kernel
end ClaudeWCT.W9.Machine.Expand.SharedScatter
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PostPass ====
section

/-! # The witness-stack post-pass of the img-merged expander (words 49400 .. 54175)

Entered from the `end` routine (`jal 49400`). In order:
1. save the old top chain area `[11768, 15224)` to `0x300000` and the old top path area `[11000, 11768)` to
   `0x301000` (forward word loops);
2. move `[24480, 26096)` up by 16, `[23744, 24464)` by 32, `[15224, 23728)` by 48 and the FTS block
   `[2904, 10568)` by 1224 (backward word loops, highest word first);
3. zero the new top layer area `[11792, 15272)`;
4. copy the 54 top chain values (words 49469 .. 50054, straight line) from the saved chain blocks into the 27 pairs;
5. place the twelve top siblings through two per-row blocks (row `leaf % 64` at `50078 + 32 r`, row
   `leaf / 64 % 64` at `52126 + 32 r`; `leaf = mem[0x20160] >> 52`), each copying six 16-byte siblings from the saved
   path area to the new plan slots;
6. `a0 := 0` and halt (`ecall` at 54175).

This file: the code, its symbolic runs and the machine-level loop/block specifications. -/

namespace ClaudeWCT.W9.Machine.Expand.PostPass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def cfgP : Config := { noAlias := true }

theorem valid8P (X : Nat) (h : X + 8 ≤ 16777216) (h8 : X % 8 = 0) : accessValid (BitVec.ofNat 64 X) 8 = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [show MEMORY_BYTES = 16777216 from rfl]; omega, h8⟩

theorem ult_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  simp [BitVec.ult, toNat_ofNat_lt hx, toNat_ofNat_lt hy]

theorem ofNat_sub8 (c : Nat) (hc : 8 ≤ c) :
    BitVec.ofNat 64 c + 18446744073709551608#64 = BitVec.ofNat 64 (c - 8) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 8 := ⟨c - 8, by omega⟩
  rw [show k + 8 - 8 = k by omega, ← ofNat_add_ofNat, BitVec.add_assoc,
    show (BitVec.ofNat 64 8 + 18446744073709551608#64 : BitVec 64) = 0#64 by decide]
  exact BitVec.add_zero _

/-! ### Code -/
def cPro1 : List (BitVec 32) := [0x3e37,0xdf8e0e13,0x300eb7,0xe8e93,0x4f37,0xb78f0f13]
def cPro2 : List (BitVec 32) := [0x3e37,0xaf8e0e13,0x301eb7,0xe8e93,0x3f37,0xdf8f0f13]
/-- Forward copy body (both save loops). -/
def fBody : List (BitVec 32) := [0xe3303,0x6eb023,0x8e0e13,0x8e8e93,0xffee68e3]
def cMv1 : List (BitVec 32) := [0x6e37,0x5e8e0e13,0x6f37,0xf98f0f13,0x1000393]
def cMv2 : List (BitVec 32) := [0x6e37,0xf88e0e13,0x6f37,0xcb8f0f13,0x2000393]
def cMv3 : List (BitVec 32) := [0x6e37,0xca8e0e13,0x4f37,0xb70f0f13,0x3000393]
def cMv4 : List (BitVec 32) := [0x3e37,0x940e0e13,0x1f37,0xb50f0f13,0x4c800393]
/-- Backward move body (all four moves). -/
def mBody : List (BitVec 32) := [0xe3303,0x7e0eb3,0x6eb023,0xff8e0e13,0xffcf48e3]
def cZPro : List (BitVec 32) := [0x3e37,0xe10e0e13,0x4f37,0xba8f0f13]
def zBody : List (BitVec 32) := [0xe3023,0x8e0e13,0xffee6ce3]

theorem code_last {b : Nat} {code : List (BitVec 32)} (hlo : 44032 ≤ b)
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (hc : (Images.expandCode_172.drop (b - 44032)).take code.length = code) :
    CodeAt Images.expandImage (pcOf b) code := codeAt_expand_last hlo hb hc

theorem code_pro1 : CodeAt Images.expandImage (pcOf 49400) cPro1 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_pro2 : CodeAt Images.expandImage (pcOf 49411) cPro2 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_f1 : CodeAt Images.expandImage (pcOf 49406) fBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_f2 : CodeAt Images.expandImage (pcOf 49417) fBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv1 : CodeAt Images.expandImage (pcOf 49422) cMv1 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv2 : CodeAt Images.expandImage (pcOf 49432) cMv2 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv3 : CodeAt Images.expandImage (pcOf 49442) cMv3 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv4 : CodeAt Images.expandImage (pcOf 49452) cMv4 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m1 : CodeAt Images.expandImage (pcOf 49427) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m2 : CodeAt Images.expandImage (pcOf 49437) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m3 : CodeAt Images.expandImage (pcOf 49447) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m4 : CodeAt Images.expandImage (pcOf 49457) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_zpro : CodeAt Images.expandImage (pcOf 49462) cZPro := code_last (by decide) (by decide) (by decide +kernel)
theorem code_z : CodeAt Images.expandImage (pcOf 49466) zBody := code_last (by decide) (by decide) (by decide +kernel)

/-! ### Symbolic results -/
/-- A prologue loading three constants into `t3`, `t4`/`t2` and `t5`. -/
def proRes (r : Reg) (a b c next n : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x28 (.c (BitVec.ofNat 64 a))).set r (.c (BitVec.ofNat 64 b))).set .x30
      (.c (BitVec.ofNat 64 c)), [], []⟩, .c (pcOf next), .endOfCode, n, n⟩
theorem run_pro1 : symRun cfgP cPro1 (pcOf 49400) 40 = some (proRes .x29 11768 0x300000 15224 49406 6) := by
  kernel_rfl
theorem run_pro2 : symRun cfgP cPro2 (pcOf 49411) 40 = some (proRes .x29 11000 0x301000 11768 49417 6) := by
  kernel_rfl
theorem run_mv1 : symRun cfgP cMv1 (pcOf 49422) 40 = some (proRes .x7 26088 16 24472 49427 5) := by kernel_rfl
theorem run_mv2 : symRun cfgP cMv2 (pcOf 49432) 40 = some (proRes .x7 24456 32 23736 49437 5) := by kernel_rfl
theorem run_mv3 : symRun cfgP cMv3 (pcOf 49442) 40 = some (proRes .x7 23720 48 15216 49447 5) := by kernel_rfl
theorem run_mv4 : symRun cfgP cMv4 (pcOf 49452) 40 = some (proRes .x7 10560 1224 2896 49457 5) := by kernel_rfl
def zProRes : Result :=
  ⟨⟨(RegFile.init.set .x28 (.c (BitVec.ofNat 64 11792))).set .x30 (.c (BitVec.ofNat 64 15272)), [], []⟩,
    .c (pcOf 49466), .endOfCode, 4, 4⟩
theorem run_zpro : symRun cfgP cZPro (pcOf 49462) 40 = some zProRes := by kernel_rfl

def fRes (p : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x6 (.ld (.reg .x28))).set .x28 (.bin .add (.reg .x28) (.c 8#64))).set .x29
      (.bin .add (.reg .x29) (.c 8#64)),
    [(⟨some (.reg .x29), 0#64⟩, .ld (.reg .x28))],
    [.valid ⟨some (.reg .x29), 0#64⟩ 8, .valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .ltu (.bin .add (.reg .x28) (.c 8#64)) (.reg .x30) (.c (pcOf p)) (.c (pcOf (p + 5))), .branch, 5, 5⟩
theorem run_f (p : Nat) (hp : p = 49406 ∨ p = 49417) : symRun cfgP fBody (pcOf p) 40 = some (fRes p) := by
  rcases hp with rfl | rfl <;> kernel_rfl

def mRes (p : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x6 (.ld (.reg .x28))).set .x28 (.bin .add (.reg .x28) (.c 18446744073709551608#64))).set
      .x29 (.bin .add (.reg .x28) (.reg .x7)),
    [(⟨some (.bin .add (.reg .x28) (.reg .x7)), 0#64⟩, .ld (.reg .x28))],
    [.valid ⟨some (.bin .add (.reg .x28) (.reg .x7)), 0#64⟩ 8, .valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .lt (.reg .x30) (.bin .add (.reg .x28) (.c 18446744073709551608#64)) (.c (pcOf p)) (.c (pcOf (p + 5))),
   .branch, 5, 5⟩
theorem run_m (p : Nat) (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457) :
    symRun cfgP mBody (pcOf p) 40 = some (mRes p) := by
  rcases hp with rfl | rfl | rfl | rfl <;> kernel_rfl

def zRes : Result :=
  ⟨⟨RegFile.init.set .x28 (.bin .add (.reg .x28) (.c 8#64)),
    [(⟨some (.reg .x28), 0#64⟩, .c 0#64)],
    [.valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .ltu (.bin .add (.reg .x28) (.c 8#64)) (.reg .x30) (.c (pcOf 49466)) (.c (pcOf 49469)), .branch, 3, 3⟩
theorem run_z : symRun cfgP zBody (pcOf 49466) 40 = some zRes := by kernel_rfl

/-! ### Prologues -/
theorem pro_spec {im : Image} {code : List (BitVec 32)} {p : Nat} {r : Reg} {a b c next n : Nat}
    (hrun : symRun cfgP code (pcOf p) 40 = some (proRes r a b c next n)) (hc : CodeAt im (pcOf p) code)
    (hr : r = .x29 ∨ r = .x7)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s n n t ∧ t.pc = pcOf next ∧ t.getReg .x28 = BitVec.ofNat 64 a ∧
      t.getReg r = BitVec.ofNat 64 b ∧ t.getReg .x30 = BitVec.ofNat 64 c ∧
      RegsExcept s t [.x28, r, .x30] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound hrun hc s hpc (by simp [proRes, Result.obligs, Oblig.all]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [proRes, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, proRes]
    rcases hr with rfl | rfl <;> cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A; rfl

/-! ### Forward copy loop -/
/-- Memory after `i` words of `[a, a + 8 n)` were copied to `b`. -/
def fcp (M : Nat → Word) (a b i : Nat) (A : Nat) : Word :=
  if b ≤ A ∧ A < b + 8 * i ∧ (A - b) % 8 = 0 then M (a + (A - b)) else M A

theorem f_iter {im : Image} {p : Nat} (hp : p = 49406 ∨ p = 49417) (hc : CodeAt im (pcOf p) fBody)
    (t : MachineState) (hpc : t.pc = pcOf p) (a b e : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 a) (h29 : t.getReg .x29 = BitVec.ofNat 64 b)
    (h30 : t.getReg .x30 = BitVec.ofNat 64 e)
    (ha : a % 8 = 0) (ha' : a + 8 ≤ 16777216) (hb : b % 8 = 0) (hb' : b + 8 ≤ 16777216) (he : e < 2 ^ 64) :
    ∃ u, Steps im t 5 5 u ∧ u.pc = (if a + 8 < e then pcOf p else pcOf (p + 5)) ∧
      u.getReg .x28 = BitVec.ofNat 64 (a + 8) ∧ u.getReg .x29 = BitVec.ofNat 64 (b + 8) ∧
      RegsExcept t u [.x6, .x28, .x29] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) =
        if A = b then t.getMem (BitVec.ofNat 64 a) else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound (run_f p hp) hc t hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [fRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, h29, BitVec.add_zero]
    exact ⟨valid8P _ hb' hb, valid8P _ ha' ha⟩
  · simp only [Result.toState_pc, fRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_add8']
    rw [ult_ofNat _ _ (by omega) he]
    by_cases h : a + 8 < e <;> simp [h]
  · simp [fRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_add8']
  · simp [fRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h29, ofNat_add8']
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, fRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, fRes, memEval_cons, memEval_nil, Addr.eval, E.eval, h28, h29,
      BitVec.add_zero]
    by_cases hAb : A = b
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

structure FInv (M : Nat → Word) (p a b e i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if a + 8 * i < e then pcOf p else pcOf (p + 5))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (a + 8 * i)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (b + 8 * i)
  x30 : t.getReg .x30 = BitVec.ofNat 64 e
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = fcp M a b i A

theorem f_loop {im : Image} {p : Nat} (hp : p = 49406 ∨ p = 49417) (hc : CodeAt im (pcOf p) fBody)
    (s : MachineState) (M : Nat → Word) (a b n : Nat) (hn : 0 < n)
    (hpc : s.pc = pcOf p) (h28 : s.getReg .x28 = BitVec.ofNat 64 a) (h29 : s.getReg .x29 = BitVec.ofNat 64 b)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (a + 8 * n))
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (ha : a % 8 = 0) (hb : b % 8 = 0) (ha' : a + 8 * n ≤ 16777216) (hb' : b + 8 * n ≤ 16777216)
    (hov : a + 8 * n ≤ b) :
    ∀ i, i ≤ n → ∃ t, Steps im s (5 * i) (5 * i) t ∧ RegsExcept s t [.x6, .x28, .x29] ∧
      FInv M p a b (a + 8 * n) i t := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, ⟨by rw [hpc, if_pos (by omega)], by simpa using h28,
      by simpa using h29, h30, fun A hA => ?_⟩⟩
    rw [hM A hA]; unfold fcp; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf p := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, u29, ru, mu⟩ := f_iter hp hc t hpc' (a + 8 * i) (b + 8 * i) (a + 8 * n)
      hI.x28 hI.x29 hI.x30 (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : a + 8 * i + 8 < a + 8 * n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show a + 8 * i + 8 = a + 8 * (i + 1) by ring]
    · rw [u29, show b + 8 * i + 8 = b + 8 * (i + 1) by ring]
    · rw [ru.get (by decide), hI.x30]
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (a + 8 * i)) = M (a + 8 * i) := by
        rw [hI.mem _ (by omega)]; unfold fcp; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold fcp
      by_cases hA' : A = b + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show b + 8 * i - b = 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : b ≤ A ∧ A < b + 8 * i ∧ (A - b) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

/-! ### Backward move loop -/
/-- Memory after the `i` highest words `T, T - 8, ..` were moved up by `d`. -/
def bmv (M : Nat → Word) (T d i : Nat) (A : Nat) : Word :=
  if T + d + 8 ≤ A + 8 * i ∧ A ≤ T + d ∧ (T + d - A) % 8 = 0 then M (A - d) else M A

theorem m_iter {im : Image} {p : Nat} (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457)
    (hc : CodeAt im (pcOf p) mBody)
    (t : MachineState) (hpc : t.pc = pcOf p) (c d lo : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 c) (h7 : t.getReg .x7 = BitVec.ofNat 64 d)
    (h30 : t.getReg .x30 = BitVec.ofNat 64 lo)
    (hc8 : c % 8 = 0) (hd8 : d % 8 = 0) (hc' : 8 ≤ c) (hcd : c + d + 8 ≤ 16777216) (hlo : lo < 2 ^ 63) :
    ∃ u, Steps im t 5 5 u ∧ u.pc = (if lo < c - 8 then pcOf p else pcOf (p + 5)) ∧
      u.getReg .x28 = BitVec.ofNat 64 (c - 8) ∧ u.getReg .x7 = BitVec.ofNat 64 d ∧
      RegsExcept t u [.x6, .x28, .x29] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) =
        if A = c + d then t.getMem (BitVec.ofNat 64 c) else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound (run_m p hp) hc t hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [mRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h28, h7, BitVec.add_zero,
      ofNat_add_ofNat]
    exact ⟨valid8P _ hcd (by omega), valid8P _ (by omega) hc8⟩
  · simp only [Result.toState_pc, mRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_sub8 c hc']
    rw [ofNat_slt _ _ hlo (by omega)]
    by_cases h : lo < c - 8 <;> simp [h]
  · simp [mRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_sub8 c hc']
  · simp [mRes, RegFile.get, RegFile.set, RegFile.init, E.eval, h7]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, mRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, mRes, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, h28, h7,
      BitVec.add_zero, ofNat_add_ofNat]
    by_cases hAb : A = c + d
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

structure MInv (M : Nat → Word) (p T d lo i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if lo + 8 * i < T then pcOf p else pcOf (p + 5))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (T - 8 * i)
  x7 : t.getReg .x7 = BitVec.ofNat 64 d
  x30 : t.getReg .x30 = BitVec.ofNat 64 lo
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = bmv M T d i A

/-- The move loop over the `n` words `T, T - 8, .., T - 8 (n - 1) = lo + 8` (`lo` is the exclusive bound in `t5`). -/
theorem m_loop {im : Image} {p : Nat} (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457)
    (hc : CodeAt im (pcOf p) mBody)
    (s : MachineState) (M : Nat → Word) (T d lo n : Nat) (hn : 0 < n) (hT : T = lo + 8 * n)
    (hpc : s.pc = pcOf p) (h28 : s.getReg .x28 = BitVec.ofNat 64 T) (h7 : s.getReg .x7 = BitVec.ofNat 64 d)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 lo)
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (hT8 : T % 8 = 0) (hd8 : d % 8 = 0) (hd : 0 < d) (hlo : 8 ≤ lo) (hTd : T + d + 8 ≤ 16777216) :
    ∀ i, i ≤ n → ∃ t, Steps im s (5 * i) (5 * i) t ∧ RegsExcept s t [.x6, .x28, .x29] ∧
      MInv M p T d lo i t := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, ⟨by rw [hpc, if_pos (by omega)], by simpa using h28,
      h7, h30, fun A hA => ?_⟩⟩
    rw [hM A hA]; unfold bmv; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf p := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, u7, ru, mu⟩ := m_iter hp hc t hpc' (T - 8 * i) d lo hI.x28 hI.x7 hI.x30
      (by omega) hd8 (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ⟨?_, ?_, u7, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : lo < T - 8 * i - 8
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show T - 8 * i - 8 = T - 8 * (i + 1) by omega]
    · rw [ru.get (by decide), hI.x30]
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (T - 8 * i)) = M (T - 8 * i) := by
        rw [hI.mem _ (by omega)]; unfold bmv; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold bmv
      by_cases hA' : A = T - 8 * i + d
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show T - 8 * i + d - d = T - 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : T + d + 8 ≤ A + 8 * i ∧ A ≤ T + d ∧ (T + d - A) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

/-! ### Zero loop -/
def zfill (M : Nat → Word) (a i : Nat) (A : Nat) : Word :=
  if a ≤ A ∧ A < a + 8 * i ∧ (A - a) % 8 = 0 then 0 else M A

theorem z_iter {im : Image} (hc : CodeAt im (pcOf 49466) zBody)
    (t : MachineState) (hpc : t.pc = pcOf 49466) (a e : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 a) (h30 : t.getReg .x30 = BitVec.ofNat 64 e)
    (ha : a % 8 = 0) (ha' : a + 8 ≤ 16777216) (he : e < 2 ^ 64) :
    ∃ u, Steps im t 3 3 u ∧ u.pc = (if a + 8 < e then pcOf 49466 else pcOf 49469) ∧
      u.getReg .x28 = BitVec.ofNat 64 (a + 8) ∧ RegsExcept t u [.x28] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = if A = a then 0 else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound run_z hc t hpc ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [zRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, BitVec.add_zero]
    exact valid8P _ ha' ha
  · simp only [Result.toState_pc, zRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_add8']
    rw [ult_ofNat _ _ (by omega) he]
    by_cases h : a + 8 < e <;> simp [h]
  · simp [zRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_add8']
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, zRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, zRes, memEval_cons, memEval_nil, Addr.eval, E.eval, h28, BitVec.add_zero]
    by_cases hAb : A = a
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

theorem z_loop {im : Image} (hc : CodeAt im (pcOf 49466) zBody)
    (s : MachineState) (M : Nat → Word) (a n : Nat) (hn : 0 < n)
    (hpc : s.pc = pcOf 49466) (h28 : s.getReg .x28 = BitVec.ofNat 64 a)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (a + 8 * n))
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (ha : a % 8 = 0) (ha' : a + 8 * n ≤ 16777216) :
    ∀ i, i ≤ n → ∃ t, Steps im s (3 * i) (3 * i) t ∧ RegsExcept s t [.x28] ∧
      t.pc = (if a + 8 * i < a + 8 * n then pcOf 49466 else pcOf 49469) ∧
      t.getReg .x28 = BitVec.ofNat 64 (a + 8 * i) ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zfill M a i A := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, by rw [hpc, if_pos (by omega)], by simpa using h28,
      fun A hA => ?_⟩
    rw [hM A hA]; unfold zfill; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, pt, t28, mt⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 49466 := by rw [pt, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, ru, mu⟩ := z_iter hc t hpc' (a + 8 * i) (a + 8 * n) t28
      (by rw [rt.get (by decide), h30]) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ?_, ?_, ?_⟩
    · rw [pu]; by_cases h : a + 8 * i + 8 < a + 8 * n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show a + 8 * i + 8 = a + 8 * (i + 1) by ring]
    · intro A hA
      rw [mu A hA, mt A hA]
      unfold zfill
      by_cases hA' : A = a + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hA']
        by_cases hin : a ≤ A ∧ A < a + 8 * i ∧ (A - a) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

end ClaudeWCT.W9.Machine.Expand.PostPass
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PostPassB ====
section

/-! # Post-pass, part B: the value copies, the sibling rows, the dispatch and the halt (generated by
`scratch/expand/pp/genB.py` from img-merged/expand.code). -/

namespace ClaudeWCT.W9.Machine.Expand.PostPass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ### The value copies (words 49469 .. 50054) -/
/-- `(destination, offset in the saved chain area at 0x300000)` of the 108 value-word copies, in program order. -/
def vTable : List (Nat × Nat) := [(12552,48),(12560,56),(12480,112),(12488,120),(12656,176),(12664,184),(12584,240),(12592,248),(12760,304),(12768,312),(12688,368),(12696,376),(12864,432),(12872,440),(12792,496),(12800,504),(12968,560),(12976,568),(12896,624),(12904,632),(13072,688),(13080,696),(13000,752),(13008,760),(13176,816),(13184,824),(13104,880),(13112,888),(13280,944),(13288,952),(13208,1008),(13216,1016),(13384,1072),(13392,1080),(13312,1136),(13320,1144),(13488,1200),(13496,1208),(13416,1264),(13424,1272),(13592,1328),(13600,1336),(13520,1392),(13528,1400),(13696,1456),(13704,1464),(13624,1520),(13632,1528),(13800,1584),(13808,1592),(13728,1648),(13736,1656),(13904,1712),(13912,1720),(13832,1776),(13840,1784),(14008,1840),(14016,1848),(13936,1904),(13944,1912),(14112,1968),(14120,1976),(14040,2032),(14048,2040),(14216,2096),(14224,2104),(14144,2160),(14152,2168),(14320,2224),(14328,2232),(14248,2288),(14256,2296),(14424,2352),(14432,2360),(14352,2416),(14360,2424),(14528,2480),(14536,2488),(14456,2544),(14464,2552),(14632,2608),(14640,2616),(14560,2672),(14568,2680),(14736,2736),(14744,2744),(14664,2800),(14672,2808),(14840,2864),(14848,2872),(14768,2928),(14776,2936),(14944,2992),(14952,3000),(14872,3056),(14880,3064),(15048,3120),(15056,3128),(14976,3184),(14984,3192),(15152,3248),(15160,3256),(15080,3312),(15088,3320),(15256,3376),(15264,3384),(15184,3440),(15192,3448)]
def cVals : List (BitVec 32) := [0x300eb7,0xe8e93,0x3e37,0x108e0e13,0x3000393,0x1d383b3,0x3b303,0x6e3023,0x3800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0xc0e0e13,0x7000393,0x1d383b3,0x3b303,0x6e3023,0x7800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x170e0e13,0xb000393,0x1d383b3,0x3b303,0x6e3023,0xb800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x128e0e13,0xf000393,0x1d383b3,0x3b303,0x6e3023,0xf800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x1d8e0e13,0x13000393,0x1d383b3,0x3b303,0x6e3023,0x13800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x190e0e13,0x17000393,0x1d383b3,0x3b303,0x6e3023,0x17800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x240e0e13,0x1b000393,0x1d383b3,0x3b303,0x6e3023,0x1b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x1f8e0e13,0x1f000393,0x1d383b3,0x3b303,0x6e3023,0x1f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x2a8e0e13,0x23000393,0x1d383b3,0x3b303,0x6e3023,0x23800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x260e0e13,0x27000393,0x1d383b3,0x3b303,0x6e3023,0x27800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x310e0e13,0x2b000393,0x1d383b3,0x3b303,0x6e3023,0x2b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x2c8e0e13,0x2f000393,0x1d383b3,0x3b303,0x6e3023,0x2f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x378e0e13,0x33000393,0x1d383b3,0x3b303,0x6e3023,0x33800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x330e0e13,0x37000393,0x1d383b3,0x3b303,0x6e3023,0x37800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x3e0e0e13,0x3b000393,0x1d383b3,0x3b303,0x6e3023,0x3b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x398e0e13,0x3f000393,0x1d383b3,0x3b303,0x6e3023,0x3f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x448e0e13,0x43000393,0x1d383b3,0x3b303,0x6e3023,0x43800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x400e0e13,0x47000393,0x1d383b3,0x3b303,0x6e3023,0x47800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x4b0e0e13,0x4b000393,0x1d383b3,0x3b303,0x6e3023,0x4b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x468e0e13,0x4f000393,0x1d383b3,0x3b303,0x6e3023,0x4f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x518e0e13,0x53000393,0x1d383b3,0x3b303,0x6e3023,0x53800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x4d0e0e13,0x57000393,0x1d383b3,0x3b303,0x6e3023,0x57800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x580e0e13,0x5b000393,0x1d383b3,0x3b303,0x6e3023,0x5b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x538e0e13,0x5f000393,0x1d383b3,0x3b303,0x6e3023,0x5f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x5e8e0e13,0x63000393,0x1d383b3,0x3b303,0x6e3023,0x63800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x5a0e0e13,0x67000393,0x1d383b3,0x3b303,0x6e3023,0x67800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x650e0e13,0x6b000393,0x1d383b3,0x3b303,0x6e3023,0x6b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x608e0e13,0x6f000393,0x1d383b3,0x3b303,0x6e3023,0x6f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x6b8e0e13,0x73000393,0x1d383b3,0x3b303,0x6e3023,0x73800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x670e0e13,0x77000393,0x1d383b3,0x3b303,0x6e3023,0x77800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x720e0e13,0x7b000393,0x1d383b3,0x3b303,0x6e3023,0x7b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x6d8e0e13,0x7f000393,0x1d383b3,0x3b303,0x6e3023,0x7f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x788e0e13,0x13b7,0x83038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x83838393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x740e0e13,0x13b7,0x87038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x87838393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x7f0e0e13,0x13b7,0x8b038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x8b838393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x7a8e0e13,0x13b7,0x8f038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x8f838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x858e0e13,0x13b7,0x93038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x93838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x810e0e13,0x13b7,0x97038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x97838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x8c0e0e13,0x13b7,0x9b038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x9b838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x878e0e13,0x13b7,0x9f038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x9f838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x928e0e13,0x13b7,0xa3038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xa3838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x8e0e0e13,0x13b7,0xa7038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xa7838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x990e0e13,0x13b7,0xab038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xab838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x948e0e13,0x13b7,0xaf038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xaf838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x9f8e0e13,0x13b7,0xb3038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xb3838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x9b0e0e13,0x13b7,0xb7038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xb7838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xa60e0e13,0x13b7,0xbb038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xbb838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xa18e0e13,0x13b7,0xbf038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xbf838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xac8e0e13,0x13b7,0xc3038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xc3838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xa80e0e13,0x13b7,0xc7038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xc7838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xb30e0e13,0x13b7,0xcb038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xcb838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xae8e0e13,0x13b7,0xcf038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xcf838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xb98e0e13,0x13b7,0xd3038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xd3838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xb50e0e13,0x13b7,0xd7038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xd7838393,0x1d383b3,0x3b303,0x6e3423]
def vWrite (e : Nat × Nat) : Addr × E := (⟨none, BitVec.ofNat 64 e.1⟩, .ld (.c (BitVec.ofNat 64 (0x300000 + e.2))))
def vWrites : SymMem := vTable.reverse.map vWrite
def vRegs : RegFile := (((RegFile.init.set .x6 (.ld (.c (BitVec.ofNat 64 3149176)))).set .x7 (.c (BitVec.ofNat 64 3149176))).set .x28
  (.c (BitVec.ofNat 64 15184))).set .x29 (.c (BitVec.ofNat 64 0x300000))
def vRes : Result := ⟨⟨vRegs, vWrites, []⟩, .c (pcOf 50055), .endOfCode, 586, 586⟩
theorem code_vals : CodeAt Images.expandImage (pcOf 49469) cVals := code_last (by decide) (by decide) (by decide +kernel)
theorem run_vals : symRun cfgP cVals (pcOf 49469) 700 = some vRes := by kernel_rfl

/-! ### The sibling rows -/
/-- Line A: `(load offset from 0x301000, store offset from 11792)` of the 12 word copies of each row. -/
def rowsA : List (List (Nat × Nat)) := [[(528,464),(536,472),(576,512),(584,520),(624,560),(632,568),(672,608),(680,616),(720,656),(728,664),(448,384),(456,392)],[(464,400),(472,408),(576,512),(584,520),(624,560),(632,568),(672,608),(680,616),(720,656),(728,664),(448,384),(456,392)],[(528,512),(536,520),(544,400),(552,408),(656,560),(664,568),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(464,448),(472,456),(544,400),(552,408),(656,560),(664,568),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(528,512),(536,520),(576,560),(584,568),(592,400),(600,408),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(464,448),(472,456),(576,560),(584,568),(592,400),(600,408),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(528,560),(536,568),(592,448),(600,456),(544,400),(552,408),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(464,496),(472,504),(592,448),(600,456),(544,400),(552,408),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(528,512),(536,520),(576,560),(584,568),(624,608),(632,616),(640,400),(648,408),(752,656),(760,664),(448,384),(456,392)],[(464,448),(472,456),(576,560),(584,568),(624,608),(632,616),(640,400),(648,408),(752,656),(760,664),(448,384),(456,392)],[(528,560),(536,568),(592,448),(600,456),(704,608),(712,616),(544,400),(552,408),(752,656),(760,664),(448,384),(456,392)],[(464,496),(472,504),(592,448),(600,456),(704,608),(712,616),(544,400),(552,408),(752,656),(760,664),(448,384),(456,392)],[(528,560),(536,568),(576,608),(584,616),(640,448),(648,456),(592,400),(600,408),(752,656),(760,664),(448,384),(456,392)],[(464,496),(472,504),(576,608),(584,616),(640,448),(648,456),(592,400),(600,408),(752,656),(760,664),(448,384),(456,392)],[(528,608),(536,616),(640,496),(648,504),(592,448),(600,456),(544,400),(552,408),(752,656),(760,664),(448,384),(456,392)],[(464,544),(472,552),(640,496),(648,504),(592,448),(600,456),(544,400),(552,408),(752,656),(760,664),(448,384),(456,392)],[(528,512),(536,520),(576,560),(584,568),(624,608),(632,616),(672,656),(680,664),(688,400),(696,408),(448,384),(456,392)],[(464,448),(472,456),(576,560),(584,568),(624,608),(632,616),(672,656),(680,664),(688,400),(696,408),(448,384),(456,392)],[(528,560),(536,568),(592,448),(600,456),(704,608),(712,616),(752,656),(760,664),(544,400),(552,408),(448,384),(456,392)],[(464,496),(472,504),(592,448),(600,456),(704,608),(712,616),(752,656),(760,664),(544,400),(552,408),(448,384),(456,392)],[(528,560),(536,568),(576,608),(584,616),(640,448),(648,456),(752,656),(760,664),(592,400),(600,408),(448,384),(456,392)],[(464,496),(472,504),(576,608),(584,616),(640,448),(648,456),(752,656),(760,664),(592,400),(600,408),(448,384),(456,392)],[(528,608),(536,616),(640,496),(648,504),(592,448),(600,456),(752,656),(760,664),(544,400),(552,408),(448,384),(456,392)],[(464,544),(472,552),(640,496),(648,504),(592,448),(600,456),(752,656),(760,664),(544,400),(552,408),(448,384),(456,392)],[(528,560),(536,568),(576,608),(584,616),(624,656),(632,664),(688,448),(696,456),(640,400),(648,408),(448,384),(456,392)],[(464,496),(472,504),(576,608),(584,616),(624,656),(632,664),(688,448),(696,456),(640,400),(648,408),(448,384),(456,392)],[(528,608),(536,616),(640,496),(648,504),(752,656),(760,664),(592,448),(600,456),(544,400),(552,408),(448,384),(456,392)],[(464,544),(472,552),(640,496),(648,504),(752,656),(760,664),(592,448),(600,456),(544,400),(552,408),(448,384),(456,392)],[(528,608),(536,616),(576,656),(584,664),(688,496),(696,504),(640,448),(648,456),(592,400),(600,408),(448,384),(456,392)],[(464,544),(472,552),(576,656),(584,664),(688,496),(696,504),(640,448),(648,456),(592,400),(600,408),(448,384),(456,392)],[(528,656),(536,664),(688,544),(696,552),(640,496),(648,504),(592,448),(600,456),(544,400),(552,408),(448,384),(456,392)],[(464,592),(472,600),(688,544),(696,552),(640,496),(648,504),(592,448),(600,456),(544,400),(552,408),(448,384),(456,392)],[(512,448),(520,456),(560,496),(568,504),(608,544),(616,552),(656,592),(664,600),(704,640),(712,648),(400,336),(408,344)],[(448,384),(456,392),(560,496),(568,504),(608,544),(616,552),(656,592),(664,600),(704,640),(712,648),(400,336),(408,344)],[(512,496),(520,504),(528,384),(536,392),(640,544),(648,552),(688,592),(696,600),(736,640),(744,648),(400,336),(408,344)],[(448,432),(456,440),(528,384),(536,392),(640,544),(648,552),(688,592),(696,600),(736,640),(744,648),(400,336),(408,344)],[(512,496),(520,504),(560,544),(568,552),(576,384),(584,392),(688,592),(696,600),(736,640),(744,648),(400,336),(408,344)],[(448,432),(456,440),(560,544),(568,552),(576,384),(584,392),(688,592),(696,600),(736,640),(744,648),(400,336),(408,344)],[(512,544),(520,552),(528,432),(536,440),(704,384),(712,392),(640,592),(648,600),(688,640),(696,648),(400,336),(408,344)],[(448,480),(456,488),(528,432),(536,440),(704,384),(712,392),(640,592),(648,600),(688,640),(696,648),(400,336),(408,344)],[(512,496),(520,504),(560,544),(568,552),(608,592),(616,600),(624,384),(632,392),(736,640),(744,648),(400,336),(408,344)],[(448,432),(456,440),(560,544),(568,552),(608,592),(616,600),(624,384),(632,392),(736,640),(744,648),(400,336),(408,344)],[(512,544),(520,552),(528,432),(536,440),(640,592),(648,600),(704,384),(712,392),(688,640),(696,648),(400,336),(408,344)],[(448,480),(456,488),(528,432),(536,440),(640,592),(648,600),(704,384),(712,392),(688,640),(696,648),(400,336),(408,344)],[(512,544),(520,552),(560,592),(568,600),(576,432),(584,440),(704,384),(712,392),(688,640),(696,648),(400,336),(408,344)],[(448,480),(456,488),(560,592),(568,600),(576,432),(584,440),(704,384),(712,392),(688,640),(696,648),(400,336),(408,344)],[(512,592),(520,600),(528,480),(536,488),(704,432),(712,440),(656,384),(664,392),(640,640),(648,648),(400,336),(408,344)],[(448,528),(456,536),(528,480),(536,488),(704,432),(712,440),(656,384),(664,392),(640,640),(648,648),(400,336),(408,344)],[(512,496),(520,504),(560,544),(568,552),(608,592),(616,600),(656,640),(664,648),(672,384),(680,392),(400,336),(408,344)],[(448,432),(456,440),(560,544),(568,552),(608,592),(616,600),(656,640),(664,648),(672,384),(680,392),(400,336),(408,344)],[(512,544),(520,552),(528,432),(536,440),(640,592),(648,600),(688,640),(696,648),(704,384),(712,392),(400,336),(408,344)],[(448,480),(456,488),(528,432),(536,440),(640,592),(648,600),(688,640),(696,648),(704,384),(712,392),(400,336),(408,344)],[(512,544),(520,552),(560,592),(568,600),(576,432),(584,440),(688,640),(696,648),(704,384),(712,392),(400,336),(408,344)],[(448,480),(456,488),(560,592),(568,600),(576,432),(584,440),(688,640),(696,648),(704,384),(712,392),(400,336),(408,344)],[(512,592),(520,600),(528,480),(536,488),(704,432),(712,440),(640,640),(648,648),(656,384),(664,392),(400,336),(408,344)],[(448,528),(456,536),(528,480),(536,488),(704,432),(712,440),(640,640),(648,648),(656,384),(664,392),(400,336),(408,344)],[(512,544),(520,552),(560,592),(568,600),(608,640),(616,648),(624,432),(632,440),(704,384),(712,392),(400,336),(408,344)],[(448,480),(456,488),(560,592),(568,600),(608,640),(616,648),(624,432),(632,440),(704,384),(712,392),(400,336),(408,344)],[(512,592),(520,600),(528,480),(536,488),(640,640),(648,648),(704,432),(712,440),(656,384),(664,392),(400,336),(408,344)],[(448,528),(456,536),(528,480),(536,488),(640,640),(648,648),(704,432),(712,440),(656,384),(664,392),(400,336),(408,344)],[(512,592),(520,600),(560,640),(568,648),(576,480),(584,488),(704,432),(712,440),(656,384),(664,392),(400,336),(408,344)],[(448,528),(456,536),(560,640),(568,648),(576,480),(584,488),(704,432),(712,440),(656,384),(664,392),(400,336),(408,344)],[(512,640),(520,648),(528,528),(536,536),(704,480),(712,488),(656,432),(664,440),(608,384),(616,392),(400,336),(408,344)],[(448,576),(456,584),(528,528),(536,536),(704,480),(712,488),(656,432),(664,440),(608,384),(616,392),(400,336),(408,344)]]
def rowCodeA : List (List (BitVec 32)) := [[0x210eb303,0x1c6f3823,0x218eb303,0x1c6f3c23,0x240eb303,0x206f3023,0x248eb303,0x206f3423,0x270eb303,0x226f3823,0x278eb303,0x226f3c23,0x2a0eb303,0x266f3023,0x2a8eb303,0x266f3423,0x2d0eb303,0x286f3823,0x2d8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xf81ff06f],[0x1d0eb303,0x186f3823,0x1d8eb303,0x186f3c23,0x240eb303,0x206f3023,0x248eb303,0x206f3423,0x270eb303,0x226f3823,0x278eb303,0x226f3c23,0x2a0eb303,0x266f3023,0x2a8eb303,0x266f3423,0x2d0eb303,0x286f3823,0x2d8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xf01ff06f],[0x210eb303,0x206f3023,0x218eb303,0x206f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x290eb303,0x226f3823,0x298eb303,0x226f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xe81ff06f],[0x1d0eb303,0x1c6f3023,0x1d8eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x290eb303,0x226f3823,0x298eb303,0x226f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xe01ff06f],[0x210eb303,0x206f3023,0x218eb303,0x206f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xd81ff06f],[0x1d0eb303,0x1c6f3023,0x1d8eb303,0x1c6f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xd01ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xc81ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xc01ff06f],[0x210eb303,0x206f3023,0x218eb303,0x206f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x270eb303,0x266f3023,0x278eb303,0x266f3423,0x280eb303,0x186f3823,0x288eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xb81ff06f],[0x1d0eb303,0x1c6f3023,0x1d8eb303,0x1c6f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x270eb303,0x266f3023,0x278eb303,0x266f3423,0x280eb303,0x186f3823,0x288eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xb01ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xa81ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xa01ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x981ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x901ff06f],[0x210eb303,0x266f3023,0x218eb303,0x266f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x881ff06f],[0x1d0eb303,0x226f3023,0x1d8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x801ff06f],[0x210eb303,0x206f3023,0x218eb303,0x206f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x270eb303,0x266f3023,0x278eb303,0x266f3423,0x2a0eb303,0x286f3823,0x2a8eb303,0x286f3c23,0x2b0eb303,0x186f3823,0x2b8eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xf80ff06f],[0x1d0eb303,0x1c6f3023,0x1d8eb303,0x1c6f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x270eb303,0x266f3023,0x278eb303,0x266f3423,0x2a0eb303,0x286f3823,0x2a8eb303,0x286f3c23,0x2b0eb303,0x186f3823,0x2b8eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xf00ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xe80ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xe00ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xd80ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xd00ff06f],[0x210eb303,0x266f3023,0x218eb303,0x266f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xc80ff06f],[0x1d0eb303,0x226f3023,0x1d8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xc00ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x270eb303,0x286f3823,0x278eb303,0x286f3c23,0x2b0eb303,0x1c6f3023,0x2b8eb303,0x1c6f3423,0x280eb303,0x186f3823,0x288eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xb80ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x270eb303,0x286f3823,0x278eb303,0x286f3c23,0x2b0eb303,0x1c6f3023,0x2b8eb303,0x1c6f3423,0x280eb303,0x186f3823,0x288eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xb00ff06f],[0x210eb303,0x266f3023,0x218eb303,0x266f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xa80ff06f],[0x1d0eb303,0x226f3023,0x1d8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xa00ff06f],[0x210eb303,0x266f3023,0x218eb303,0x266f3423,0x240eb303,0x286f3823,0x248eb303,0x286f3c23,0x2b0eb303,0x1e6f3823,0x2b8eb303,0x1e6f3c23,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x980ff06f],[0x1d0eb303,0x226f3023,0x1d8eb303,0x226f3423,0x240eb303,0x286f3823,0x248eb303,0x286f3c23,0x2b0eb303,0x1e6f3823,0x2b8eb303,0x1e6f3c23,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x900ff06f],[0x210eb303,0x286f3823,0x218eb303,0x286f3c23,0x2b0eb303,0x226f3023,0x2b8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x880ff06f],[0x1d0eb303,0x246f3823,0x1d8eb303,0x246f3c23,0x2b0eb303,0x226f3023,0x2b8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x800ff06f],[0x200eb303,0x1c6f3023,0x208eb303,0x1c6f3423,0x230eb303,0x1e6f3823,0x238eb303,0x1e6f3c23,0x260eb303,0x226f3023,0x268eb303,0x226f3423,0x290eb303,0x246f3823,0x298eb303,0x246f3c23,0x2c0eb303,0x286f3023,0x2c8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xf81fe06f],[0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x230eb303,0x1e6f3823,0x238eb303,0x1e6f3c23,0x260eb303,0x226f3023,0x268eb303,0x226f3423,0x290eb303,0x246f3823,0x298eb303,0x246f3c23,0x2c0eb303,0x286f3023,0x2c8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xf01fe06f],[0x200eb303,0x1e6f3823,0x208eb303,0x1e6f3c23,0x210eb303,0x186f3023,0x218eb303,0x186f3423,0x280eb303,0x226f3023,0x288eb303,0x226f3423,0x2b0eb303,0x246f3823,0x2b8eb303,0x246f3c23,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xe81fe06f],[0x1c0eb303,0x1a6f3823,0x1c8eb303,0x1a6f3c23,0x210eb303,0x186f3023,0x218eb303,0x186f3423,0x280eb303,0x226f3023,0x288eb303,0x226f3423,0x2b0eb303,0x246f3823,0x2b8eb303,0x246f3c23,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xe01fe06f],[0x200eb303,0x1e6f3823,0x208eb303,0x1e6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x240eb303,0x186f3023,0x248eb303,0x186f3423,0x2b0eb303,0x246f3823,0x2b8eb303,0x246f3c23,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xd81fe06f],[0x1c0eb303,0x1a6f3823,0x1c8eb303,0x1a6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x240eb303,0x186f3023,0x248eb303,0x186f3423,0x2b0eb303,0x246f3823,0x2b8eb303,0x246f3c23,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xd01fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xc81fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xc01fe06f],[0x200eb303,0x1e6f3823,0x208eb303,0x1e6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x260eb303,0x246f3823,0x268eb303,0x246f3c23,0x270eb303,0x186f3023,0x278eb303,0x186f3423,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xb81fe06f],[0x1c0eb303,0x1a6f3823,0x1c8eb303,0x1a6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x260eb303,0x246f3823,0x268eb303,0x246f3c23,0x270eb303,0x186f3023,0x278eb303,0x186f3423,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xb01fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xa81fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xa01fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x240eb303,0x1a6f3823,0x248eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x981fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x240eb303,0x1a6f3823,0x248eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x901fe06f],[0x200eb303,0x246f3823,0x208eb303,0x246f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x881fe06f],[0x1c0eb303,0x206f3823,0x1c8eb303,0x206f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x801fe06f],[0x200eb303,0x1e6f3823,0x208eb303,0x1e6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x260eb303,0x246f3823,0x268eb303,0x246f3c23,0x290eb303,0x286f3023,0x298eb303,0x286f3423,0x2a0eb303,0x186f3023,0x2a8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xf80fe06f],[0x1c0eb303,0x1a6f3823,0x1c8eb303,0x1a6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x260eb303,0x246f3823,0x268eb303,0x246f3c23,0x290eb303,0x286f3023,0x298eb303,0x286f3423,0x2a0eb303,0x186f3023,0x2a8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xf00fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xe80fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xe00fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x240eb303,0x1a6f3823,0x248eb303,0x1a6f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xd80fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x240eb303,0x1a6f3823,0x248eb303,0x1a6f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xd00fe06f],[0x200eb303,0x246f3823,0x208eb303,0x246f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xc80fe06f],[0x1c0eb303,0x206f3823,0x1c8eb303,0x206f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xc00fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x260eb303,0x286f3023,0x268eb303,0x286f3423,0x270eb303,0x1a6f3823,0x278eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xb80fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x260eb303,0x286f3023,0x268eb303,0x286f3423,0x270eb303,0x1a6f3823,0x278eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xb00fe06f],[0x200eb303,0x246f3823,0x208eb303,0x246f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xa80fe06f],[0x1c0eb303,0x206f3823,0x1c8eb303,0x206f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xa00fe06f],[0x200eb303,0x246f3823,0x208eb303,0x246f3c23,0x230eb303,0x286f3023,0x238eb303,0x286f3423,0x240eb303,0x1e6f3023,0x248eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x980fe06f],[0x1c0eb303,0x206f3823,0x1c8eb303,0x206f3c23,0x230eb303,0x286f3023,0x238eb303,0x286f3423,0x240eb303,0x1e6f3023,0x248eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x900fe06f],[0x200eb303,0x286f3023,0x208eb303,0x286f3423,0x210eb303,0x206f3823,0x218eb303,0x206f3c23,0x2c0eb303,0x1e6f3023,0x2c8eb303,0x1e6f3423,0x290eb303,0x1a6f3823,0x298eb303,0x1a6f3c23,0x260eb303,0x186f3023,0x268eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x880fe06f],[0x1c0eb303,0x246f3023,0x1c8eb303,0x246f3423,0x210eb303,0x206f3823,0x218eb303,0x206f3c23,0x2c0eb303,0x1e6f3023,0x2c8eb303,0x1e6f3423,0x290eb303,0x1a6f3823,0x298eb303,0x1a6f3c23,0x260eb303,0x186f3023,0x268eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x800fe06f]]
/-- Line B: `(load offset from 0x301000, store offset from 11792)` of the 12 word copies of each row. -/
def rowsB : List (List (Nat × Nat)) := [[(48,48),(56,56),(96,96),(104,104),(144,144),(152,152),(192,192),(200,200),(240,240),(248,248),(288,288),(296,296)],[(0,0),(8,8),(112,112),(120,120),(160,160),(168,168),(208,208),(216,216),(256,256),(264,264),(304,304),(312,312)],[(48,112),(56,120),(64,0),(72,8),(176,160),(184,168),(224,208),(232,216),(272,256),(280,264),(320,304),(328,312)],[(0,48),(8,56),(80,0),(88,8),(192,160),(200,168),(240,208),(248,216),(288,256),(296,264),(336,304),(344,312)],[(48,112),(56,120),(96,160),(104,168),(112,0),(120,8),(224,208),(232,216),(272,256),(280,264),(320,304),(328,312)],[(0,48),(8,56),(112,160),(120,168),(128,0),(136,8),(240,208),(248,216),(288,256),(296,264),(336,304),(344,312)],[(48,160),(56,168),(64,48),(72,56),(144,0),(152,8),(256,208),(264,216),(304,256),(312,264),(352,304),(360,312)],[(0,96),(8,104),(80,48),(88,56),(160,0),(168,8),(272,208),(280,216),(320,256),(328,264),(368,304),(376,312)],[(48,112),(56,120),(96,160),(104,168),(144,208),(152,216),(160,0),(168,8),(272,256),(280,264),(320,304),(328,312)],[(0,48),(8,56),(112,160),(120,168),(160,208),(168,216),(176,0),(184,8),(288,256),(296,264),(336,304),(344,312)],[(48,160),(56,168),(64,48),(72,56),(176,208),(184,216),(192,0),(200,8),(304,256),(312,264),(352,304),(360,312)],[(0,96),(8,104),(80,48),(88,56),(192,208),(200,216),(208,0),(216,8),(320,256),(328,264),(368,304),(376,312)],[(48,160),(56,168),(96,208),(104,216),(112,48),(120,56),(192,0),(200,8),(304,256),(312,264),(352,304),(360,312)],[(0,96),(8,104),(112,208),(120,216),(128,48),(136,56),(208,0),(216,8),(320,256),(328,264),(368,304),(376,312)],[(48,208),(56,216),(64,96),(72,104),(144,48),(152,56),(320,0),(328,8),(256,256),(264,264),(304,304),(312,312)],[(0,144),(8,152),(80,96),(88,104),(208,48),(216,56),(160,0),(168,8),(320,256),(328,264),(368,304),(376,312)],[(48,112),(56,120),(96,160),(104,168),(144,208),(152,216),(192,256),(200,264),(208,0),(216,8),(320,304),(328,312)],[(0,48),(8,56),(112,160),(120,168),(160,208),(168,216),(208,256),(216,264),(224,0),(232,8),(336,304),(344,312)],[(48,160),(56,168),(64,48),(72,56),(176,208),(184,216),(224,256),(232,264),(240,0),(248,8),(352,304),(360,312)],[(0,96),(8,104),(80,48),(88,56),(192,208),(200,216),(240,256),(248,264),(256,0),(264,8),(368,304),(376,312)],[(48,160),(56,168),(96,208),(104,216),(112,48),(120,56),(224,256),(232,264),(240,0),(248,8),(352,304),(360,312)],[(0,96),(8,104),(112,208),(120,216),(128,48),(136,56),(240,256),(248,264),(256,0),(264,8),(368,304),(376,312)],[(48,208),(56,216),(64,96),(72,104),(144,48),(152,56),(256,256),(264,264),(320,0),(328,8),(304,304),(312,312)],[(0,144),(8,152),(80,96),(88,104),(208,48),(216,56),(320,256),(328,264),(160,0),(168,8),(368,304),(376,312)],[(48,160),(56,168),(96,208),(104,216),(144,256),(152,264),(160,48),(168,56),(240,0),(248,8),(352,304),(360,312)],[(0,96),(8,104),(112,208),(120,216),(160,256),(168,264),(176,48),(184,56),(256,0),(264,8),(368,304),(376,312)],[(48,208),(56,216),(64,96),(72,104),(176,256),(184,264),(192,48),(200,56),(320,0),(328,8),(304,304),(312,312)],[(0,144),(8,152),(80,96),(88,104),(192,256),(200,264),(256,48),(264,56),(208,0),(216,8),(368,304),(376,312)],[(48,208),(56,216),(96,256),(104,264),(112,96),(120,104),(192,48),(200,56),(320,0),(328,8),(304,304),(312,312)],[(0,144),(8,152),(112,256),(120,264),(128,96),(136,104),(256,48),(264,56),(208,0),(216,8),(368,304),(376,312)],[(48,256),(56,264),(64,144),(72,152),(144,96),(152,104),(320,48),(328,56),(272,0),(280,8),(256,304),(264,312)],[(0,192),(8,200),(80,144),(88,152),(256,96),(264,104),(208,48),(216,56),(160,0),(168,8),(368,304),(376,312)],[(48,112),(56,120),(96,160),(104,168),(144,208),(152,216),(192,256),(200,264),(240,304),(248,312),(256,0),(264,8)],[(0,48),(8,56),(112,160),(120,168),(160,208),(168,216),(208,256),(216,264),(256,304),(264,312),(272,0),(280,8)],[(48,160),(56,168),(64,48),(72,56),(176,208),(184,216),(224,256),(232,264),(272,304),(280,312),(288,0),(296,8)],[(0,96),(8,104),(80,48),(88,56),(192,208),(200,216),(240,256),(248,264),(288,304),(296,312),(304,0),(312,8)],[(48,160),(56,168),(96,208),(104,216),(112,48),(120,56),(224,256),(232,264),(272,304),(280,312),(288,0),(296,8)],[(0,96),(8,104),(112,208),(120,216),(128,48),(136,56),(240,256),(248,264),(288,304),(296,312),(304,0),(312,8)],[(48,208),(56,216),(64,96),(72,104),(144,48),(152,56),(256,256),(264,264),(304,304),(312,312),(320,0),(328,8)],[(0,144),(8,152),(80,96),(88,104),(208,48),(216,56),(320,256),(328,264),(368,304),(376,312),(160,0),(168,8)],[(48,160),(56,168),(96,208),(104,216),(144,256),(152,264),(160,48),(168,56),(272,304),(280,312),(288,0),(296,8)],[(0,96),(8,104),(112,208),(120,216),(160,256),(168,264),(176,48),(184,56),(288,304),(296,312),(304,0),(312,8)],[(48,208),(56,216),(64,96),(72,104),(176,256),(184,264),(192,48),(200,56),(304,304),(312,312),(320,0),(328,8)],[(0,144),(8,152),(80,96),(88,104),(192,256),(200,264),(256,48),(264,56),(368,304),(376,312),(208,0),(216,8)],[(48,208),(56,216),(96,256),(104,264),(112,96),(120,104),(192,48),(200,56),(304,304),(312,312),(320,0),(328,8)],[(0,144),(8,152),(112,256),(120,264),(128,96),(136,104),(256,48),(264,56),(368,304),(376,312),(208,0),(216,8)],[(48,256),(56,264),(64,144),(72,152),(144,96),(152,104),(320,48),(328,56),(256,304),(264,312),(272,0),(280,8)],[(0,192),(8,200),(80,144),(88,152),(256,96),(264,104),(208,48),(216,56),(368,304),(376,312),(160,0),(168,8)],[(48,160),(56,168),(96,208),(104,216),(144,256),(152,264),(192,304),(200,312),(208,48),(216,56),(288,0),(296,8)],[(0,96),(8,104),(112,208),(120,216),(160,256),(168,264),(208,304),(216,312),(224,48),(232,56),(304,0),(312,8)],[(48,208),(56,216),(64,96),(72,104),(176,256),(184,264),(224,304),(232,312),(240,48),(248,56),(320,0),(328,8)],[(0,144),(8,152),(80,96),(88,104),(192,256),(200,264),(240,304),(248,312),(304,48),(312,56),(256,0),(264,8)],[(48,208),(56,216),(96,256),(104,264),(112,96),(120,104),(224,304),(232,312),(240,48),(248,56),(320,0),(328,8)],[(0,144),(8,152),(112,256),(120,264),(128,96),(136,104),(240,304),(248,312),(304,48),(312,56),(256,0),(264,8)],[(48,256),(56,264),(64,144),(72,152),(144,96),(152,104),(256,304),(264,312),(320,48),(328,56),(272,0),(280,8)],[(0,192),(8,200),(80,144),(88,152),(256,96),(264,104),(368,304),(376,312),(208,48),(216,56),(160,0),(168,8)],[(48,208),(56,216),(96,256),(104,264),(144,304),(152,312),(160,96),(168,104),(240,48),(248,56),(320,0),(328,8)],[(0,144),(8,152),(112,256),(120,264),(160,304),(168,312),(176,96),(184,104),(304,48),(312,56),(256,0),(264,8)],[(48,256),(56,264),(64,144),(72,152),(176,304),(184,312),(192,96),(200,104),(320,48),(328,56),(272,0),(280,8)],[(0,192),(8,200),(80,144),(88,152),(192,304),(200,312),(304,96),(312,104),(256,48),(264,56),(208,0),(216,8)],[(48,256),(56,264),(96,304),(104,312),(112,144),(120,152),(192,96),(200,104),(320,48),(328,56),(272,0),(280,8)],[(0,192),(8,200),(112,304),(120,312),(128,144),(136,152),(304,96),(312,104),(256,48),(264,56),(208,0),(216,8)],[(48,304),(56,312),(64,192),(72,200),(144,144),(152,152),(320,96),(328,104),(272,48),(280,56),(224,0),(232,8)],[(0,240),(8,248),(80,192),(88,200),(304,144),(312,152),(256,96),(264,104),(208,48),(216,56),(160,0),(168,8)]]
def rowCodeB : List (List (BitVec 32)) := [[0x30eb303,0x26f3823,0x38eb303,0x26f3c23,0x60eb303,0x66f3023,0x68eb303,0x66f3423,0x90eb303,0x86f3823,0x98eb303,0x86f3c23,0xc0eb303,0xc6f3023,0xc8eb303,0xc6f3423,0xf0eb303,0xe6f3823,0xf8eb303,0xe6f3c23,0x120eb303,0x126f3023,0x128eb303,0x126f3423,0xf9dfd06f],[0xeb303,0x6f3023,0x8eb303,0x6f3423,0x70eb303,0x66f3823,0x78eb303,0x66f3c23,0xa0eb303,0xa6f3023,0xa8eb303,0xa6f3423,0xd0eb303,0xc6f3823,0xd8eb303,0xc6f3c23,0x100eb303,0x106f3023,0x108eb303,0x106f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0xf1dfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x40eb303,0x6f3023,0x48eb303,0x6f3423,0xb0eb303,0xa6f3023,0xb8eb303,0xa6f3423,0xe0eb303,0xc6f3823,0xe8eb303,0xc6f3c23,0x110eb303,0x106f3023,0x118eb303,0x106f3423,0x140eb303,0x126f3823,0x148eb303,0x126f3c23,0xe9dfd06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x50eb303,0x6f3023,0x58eb303,0x6f3423,0xc0eb303,0xa6f3023,0xc8eb303,0xa6f3423,0xf0eb303,0xc6f3823,0xf8eb303,0xc6f3c23,0x120eb303,0x106f3023,0x128eb303,0x106f3423,0x150eb303,0x126f3823,0x158eb303,0x126f3c23,0xe1dfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x60eb303,0xa6f3023,0x68eb303,0xa6f3423,0x70eb303,0x6f3023,0x78eb303,0x6f3423,0xe0eb303,0xc6f3823,0xe8eb303,0xc6f3c23,0x110eb303,0x106f3023,0x118eb303,0x106f3423,0x140eb303,0x126f3823,0x148eb303,0x126f3c23,0xd9dfd06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x70eb303,0xa6f3023,0x78eb303,0xa6f3423,0x80eb303,0x6f3023,0x88eb303,0x6f3423,0xf0eb303,0xc6f3823,0xf8eb303,0xc6f3c23,0x120eb303,0x106f3023,0x128eb303,0x106f3423,0x150eb303,0x126f3823,0x158eb303,0x126f3c23,0xd1dfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x40eb303,0x26f3823,0x48eb303,0x26f3c23,0x90eb303,0x6f3023,0x98eb303,0x6f3423,0x100eb303,0xc6f3823,0x108eb303,0xc6f3c23,0x130eb303,0x106f3023,0x138eb303,0x106f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xc9dfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x50eb303,0x26f3823,0x58eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x110eb303,0xc6f3823,0x118eb303,0xc6f3c23,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xc1dfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x60eb303,0xa6f3023,0x68eb303,0xa6f3423,0x90eb303,0xc6f3823,0x98eb303,0xc6f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x110eb303,0x106f3023,0x118eb303,0x106f3423,0x140eb303,0x126f3823,0x148eb303,0x126f3c23,0xb9dfd06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x70eb303,0xa6f3023,0x78eb303,0xa6f3423,0xa0eb303,0xc6f3823,0xa8eb303,0xc6f3c23,0xb0eb303,0x6f3023,0xb8eb303,0x6f3423,0x120eb303,0x106f3023,0x128eb303,0x106f3423,0x150eb303,0x126f3823,0x158eb303,0x126f3c23,0xb1dfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x40eb303,0x26f3823,0x48eb303,0x26f3c23,0xb0eb303,0xc6f3823,0xb8eb303,0xc6f3c23,0xc0eb303,0x6f3023,0xc8eb303,0x6f3423,0x130eb303,0x106f3023,0x138eb303,0x106f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xa9dfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x50eb303,0x26f3823,0x58eb303,0x26f3c23,0xc0eb303,0xc6f3823,0xc8eb303,0xc6f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xa1dfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x70eb303,0x26f3823,0x78eb303,0x26f3c23,0xc0eb303,0x6f3023,0xc8eb303,0x6f3423,0x130eb303,0x106f3023,0x138eb303,0x106f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0x99dfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0x80eb303,0x26f3823,0x88eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0x91dfd06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0x90eb303,0x26f3823,0x98eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x100eb303,0x106f3023,0x108eb303,0x106f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x89dfd06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0x81dfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x60eb303,0xa6f3023,0x68eb303,0xa6f3423,0x90eb303,0xc6f3823,0x98eb303,0xc6f3c23,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x140eb303,0x126f3823,0x148eb303,0x126f3c23,0xf9cfd06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x70eb303,0xa6f3023,0x78eb303,0xa6f3423,0xa0eb303,0xc6f3823,0xa8eb303,0xc6f3c23,0xd0eb303,0x106f3023,0xd8eb303,0x106f3423,0xe0eb303,0x6f3023,0xe8eb303,0x6f3423,0x150eb303,0x126f3823,0x158eb303,0x126f3c23,0xf1cfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x40eb303,0x26f3823,0x48eb303,0x26f3c23,0xb0eb303,0xc6f3823,0xb8eb303,0xc6f3c23,0xe0eb303,0x106f3023,0xe8eb303,0x106f3423,0xf0eb303,0x6f3023,0xf8eb303,0x6f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xe9cfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x50eb303,0x26f3823,0x58eb303,0x26f3c23,0xc0eb303,0xc6f3823,0xc8eb303,0xc6f3c23,0xf0eb303,0x106f3023,0xf8eb303,0x106f3423,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xe1cfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x70eb303,0x26f3823,0x78eb303,0x26f3c23,0xe0eb303,0x106f3023,0xe8eb303,0x106f3423,0xf0eb303,0x6f3023,0xf8eb303,0x6f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xd9cfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0x80eb303,0x26f3823,0x88eb303,0x26f3c23,0xf0eb303,0x106f3023,0xf8eb303,0x106f3423,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xd1cfd06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0x90eb303,0x26f3823,0x98eb303,0x26f3c23,0x100eb303,0x106f3023,0x108eb303,0x106f3423,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0xc9cfd06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xc1cfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x90eb303,0x106f3023,0x98eb303,0x106f3423,0xa0eb303,0x26f3823,0xa8eb303,0x26f3c23,0xf0eb303,0x6f3023,0xf8eb303,0x6f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xb9cfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0xa0eb303,0x106f3023,0xa8eb303,0x106f3423,0xb0eb303,0x26f3823,0xb8eb303,0x26f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xb1cfd06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0xb0eb303,0x106f3023,0xb8eb303,0x106f3423,0xc0eb303,0x26f3823,0xc8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0xa9cfd06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xa1cfd06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x60eb303,0x106f3023,0x68eb303,0x106f3423,0x70eb303,0x66f3023,0x78eb303,0x66f3423,0xc0eb303,0x26f3823,0xc8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x99cfd06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x70eb303,0x106f3023,0x78eb303,0x106f3423,0x80eb303,0x66f3023,0x88eb303,0x66f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0x91cfd06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x40eb303,0x86f3823,0x48eb303,0x86f3c23,0x90eb303,0x66f3023,0x98eb303,0x66f3423,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0x100eb303,0x126f3823,0x108eb303,0x126f3c23,0x89cfd06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x50eb303,0x86f3823,0x58eb303,0x86f3c23,0x100eb303,0x66f3023,0x108eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0x81cfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x60eb303,0xa6f3023,0x68eb303,0xa6f3423,0x90eb303,0xc6f3823,0x98eb303,0xc6f3c23,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0xf0eb303,0x126f3823,0xf8eb303,0x126f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0xf9dfc06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x70eb303,0xa6f3023,0x78eb303,0xa6f3423,0xa0eb303,0xc6f3823,0xa8eb303,0xc6f3c23,0xd0eb303,0x106f3023,0xd8eb303,0x106f3423,0x100eb303,0x126f3823,0x108eb303,0x126f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0xf1dfc06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x40eb303,0x26f3823,0x48eb303,0x26f3c23,0xb0eb303,0xc6f3823,0xb8eb303,0xc6f3c23,0xe0eb303,0x106f3023,0xe8eb303,0x106f3423,0x110eb303,0x126f3823,0x118eb303,0x126f3c23,0x120eb303,0x6f3023,0x128eb303,0x6f3423,0xe9dfc06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x50eb303,0x26f3823,0x58eb303,0x26f3c23,0xc0eb303,0xc6f3823,0xc8eb303,0xc6f3c23,0xf0eb303,0x106f3023,0xf8eb303,0x106f3423,0x120eb303,0x126f3823,0x128eb303,0x126f3c23,0x130eb303,0x6f3023,0x138eb303,0x6f3423,0xe1dfc06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x70eb303,0x26f3823,0x78eb303,0x26f3c23,0xe0eb303,0x106f3023,0xe8eb303,0x106f3423,0x110eb303,0x126f3823,0x118eb303,0x126f3c23,0x120eb303,0x6f3023,0x128eb303,0x6f3423,0xd9dfc06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0x80eb303,0x26f3823,0x88eb303,0x26f3c23,0xf0eb303,0x106f3023,0xf8eb303,0x106f3423,0x120eb303,0x126f3823,0x128eb303,0x126f3c23,0x130eb303,0x6f3023,0x138eb303,0x6f3423,0xd1dfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0x90eb303,0x26f3823,0x98eb303,0x26f3c23,0x100eb303,0x106f3023,0x108eb303,0x106f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xc9dfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0xc1dfc06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x90eb303,0x106f3023,0x98eb303,0x106f3423,0xa0eb303,0x26f3823,0xa8eb303,0x26f3c23,0x110eb303,0x126f3823,0x118eb303,0x126f3c23,0x120eb303,0x6f3023,0x128eb303,0x6f3423,0xb9dfc06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0xa0eb303,0x106f3023,0xa8eb303,0x106f3423,0xb0eb303,0x26f3823,0xb8eb303,0x26f3c23,0x120eb303,0x126f3823,0x128eb303,0x126f3c23,0x130eb303,0x6f3023,0x138eb303,0x6f3423,0xb1dfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0xb0eb303,0x106f3023,0xb8eb303,0x106f3423,0xc0eb303,0x26f3823,0xc8eb303,0x26f3c23,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xa9dfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0xa1dfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x60eb303,0x106f3023,0x68eb303,0x106f3423,0x70eb303,0x66f3023,0x78eb303,0x66f3423,0xc0eb303,0x26f3823,0xc8eb303,0x26f3c23,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x99dfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x70eb303,0x106f3023,0x78eb303,0x106f3423,0x80eb303,0x66f3023,0x88eb303,0x66f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x91dfc06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x40eb303,0x86f3823,0x48eb303,0x86f3c23,0x90eb303,0x66f3023,0x98eb303,0x66f3423,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x100eb303,0x126f3823,0x108eb303,0x126f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0x89dfc06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x50eb303,0x86f3823,0x58eb303,0x86f3c23,0x100eb303,0x66f3023,0x108eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x81dfc06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x90eb303,0x106f3023,0x98eb303,0x106f3423,0xc0eb303,0x126f3823,0xc8eb303,0x126f3c23,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0x120eb303,0x6f3023,0x128eb303,0x6f3423,0xf9cfc06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0xa0eb303,0x106f3023,0xa8eb303,0x106f3423,0xd0eb303,0x126f3823,0xd8eb303,0x126f3c23,0xe0eb303,0x26f3823,0xe8eb303,0x26f3c23,0x130eb303,0x6f3023,0x138eb303,0x6f3423,0xf1cfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0xb0eb303,0x106f3023,0xb8eb303,0x106f3423,0xe0eb303,0x126f3823,0xe8eb303,0x126f3c23,0xf0eb303,0x26f3823,0xf8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xe9cfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0xf0eb303,0x126f3823,0xf8eb303,0x126f3c23,0x130eb303,0x26f3823,0x138eb303,0x26f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0xe1cfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x60eb303,0x106f3023,0x68eb303,0x106f3423,0x70eb303,0x66f3023,0x78eb303,0x66f3423,0xe0eb303,0x126f3823,0xe8eb303,0x126f3c23,0xf0eb303,0x26f3823,0xf8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xd9cfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x70eb303,0x106f3023,0x78eb303,0x106f3423,0x80eb303,0x66f3023,0x88eb303,0x66f3423,0xf0eb303,0x126f3823,0xf8eb303,0x126f3c23,0x130eb303,0x26f3823,0x138eb303,0x26f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0xd1cfc06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x40eb303,0x86f3823,0x48eb303,0x86f3c23,0x90eb303,0x66f3023,0x98eb303,0x66f3423,0x100eb303,0x126f3823,0x108eb303,0x126f3c23,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0xc9cfc06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x50eb303,0x86f3823,0x58eb303,0x86f3c23,0x100eb303,0x66f3023,0x108eb303,0x66f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0xc1cfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x60eb303,0x106f3023,0x68eb303,0x106f3423,0x90eb303,0x126f3823,0x98eb303,0x126f3c23,0xa0eb303,0x66f3023,0xa8eb303,0x66f3423,0xf0eb303,0x26f3823,0xf8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xb9cfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x70eb303,0x106f3023,0x78eb303,0x106f3423,0xa0eb303,0x126f3823,0xa8eb303,0x126f3c23,0xb0eb303,0x66f3023,0xb8eb303,0x66f3423,0x130eb303,0x26f3823,0x138eb303,0x26f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0xb1cfc06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x40eb303,0x86f3823,0x48eb303,0x86f3c23,0xb0eb303,0x126f3823,0xb8eb303,0x126f3c23,0xc0eb303,0x66f3023,0xc8eb303,0x66f3423,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0xa9cfc06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x50eb303,0x86f3823,0x58eb303,0x86f3c23,0xc0eb303,0x126f3823,0xc8eb303,0x126f3c23,0x130eb303,0x66f3023,0x138eb303,0x66f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0xa1cfc06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x60eb303,0x126f3823,0x68eb303,0x126f3c23,0x70eb303,0x86f3823,0x78eb303,0x86f3c23,0xc0eb303,0x66f3023,0xc8eb303,0x66f3423,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0x99cfc06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x70eb303,0x126f3823,0x78eb303,0x126f3c23,0x80eb303,0x86f3823,0x88eb303,0x86f3c23,0x130eb303,0x66f3023,0x138eb303,0x66f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x91cfc06f],[0x30eb303,0x126f3823,0x38eb303,0x126f3c23,0x40eb303,0xc6f3023,0x48eb303,0xc6f3423,0x90eb303,0x86f3823,0x98eb303,0x86f3c23,0x140eb303,0x66f3023,0x148eb303,0x66f3423,0x110eb303,0x26f3823,0x118eb303,0x26f3c23,0xe0eb303,0x6f3023,0xe8eb303,0x6f3423,0x89cfc06f],[0xeb303,0xe6f3823,0x8eb303,0xe6f3c23,0x50eb303,0xc6f3023,0x58eb303,0xc6f3423,0x130eb303,0x86f3823,0x138eb303,0x86f3c23,0x100eb303,0x66f3023,0x108eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x81cfc06f]]
sym_block RA0 := symRun cfgP (rowCodeA.getD 0 []) (pcOf 50078) 40
sym_block RA1 := symRun cfgP (rowCodeA.getD 1 []) (pcOf 50110) 40
sym_block RA2 := symRun cfgP (rowCodeA.getD 2 []) (pcOf 50142) 40
sym_block RA3 := symRun cfgP (rowCodeA.getD 3 []) (pcOf 50174) 40
sym_block RA4 := symRun cfgP (rowCodeA.getD 4 []) (pcOf 50206) 40
sym_block RA5 := symRun cfgP (rowCodeA.getD 5 []) (pcOf 50238) 40
sym_block RA6 := symRun cfgP (rowCodeA.getD 6 []) (pcOf 50270) 40
sym_block RA7 := symRun cfgP (rowCodeA.getD 7 []) (pcOf 50302) 40
sym_block RA8 := symRun cfgP (rowCodeA.getD 8 []) (pcOf 50334) 40
sym_block RA9 := symRun cfgP (rowCodeA.getD 9 []) (pcOf 50366) 40
sym_block RA10 := symRun cfgP (rowCodeA.getD 10 []) (pcOf 50398) 40
sym_block RA11 := symRun cfgP (rowCodeA.getD 11 []) (pcOf 50430) 40
sym_block RA12 := symRun cfgP (rowCodeA.getD 12 []) (pcOf 50462) 40
sym_block RA13 := symRun cfgP (rowCodeA.getD 13 []) (pcOf 50494) 40
sym_block RA14 := symRun cfgP (rowCodeA.getD 14 []) (pcOf 50526) 40
sym_block RA15 := symRun cfgP (rowCodeA.getD 15 []) (pcOf 50558) 40
sym_block RA16 := symRun cfgP (rowCodeA.getD 16 []) (pcOf 50590) 40
sym_block RA17 := symRun cfgP (rowCodeA.getD 17 []) (pcOf 50622) 40
sym_block RA18 := symRun cfgP (rowCodeA.getD 18 []) (pcOf 50654) 40
sym_block RA19 := symRun cfgP (rowCodeA.getD 19 []) (pcOf 50686) 40
sym_block RA20 := symRun cfgP (rowCodeA.getD 20 []) (pcOf 50718) 40
sym_block RA21 := symRun cfgP (rowCodeA.getD 21 []) (pcOf 50750) 40
sym_block RA22 := symRun cfgP (rowCodeA.getD 22 []) (pcOf 50782) 40
sym_block RA23 := symRun cfgP (rowCodeA.getD 23 []) (pcOf 50814) 40
sym_block RA24 := symRun cfgP (rowCodeA.getD 24 []) (pcOf 50846) 40
sym_block RA25 := symRun cfgP (rowCodeA.getD 25 []) (pcOf 50878) 40
sym_block RA26 := symRun cfgP (rowCodeA.getD 26 []) (pcOf 50910) 40
sym_block RA27 := symRun cfgP (rowCodeA.getD 27 []) (pcOf 50942) 40
sym_block RA28 := symRun cfgP (rowCodeA.getD 28 []) (pcOf 50974) 40
sym_block RA29 := symRun cfgP (rowCodeA.getD 29 []) (pcOf 51006) 40
sym_block RA30 := symRun cfgP (rowCodeA.getD 30 []) (pcOf 51038) 40
sym_block RA31 := symRun cfgP (rowCodeA.getD 31 []) (pcOf 51070) 40
sym_block RA32 := symRun cfgP (rowCodeA.getD 32 []) (pcOf 51102) 40
sym_block RA33 := symRun cfgP (rowCodeA.getD 33 []) (pcOf 51134) 40
sym_block RA34 := symRun cfgP (rowCodeA.getD 34 []) (pcOf 51166) 40
sym_block RA35 := symRun cfgP (rowCodeA.getD 35 []) (pcOf 51198) 40
sym_block RA36 := symRun cfgP (rowCodeA.getD 36 []) (pcOf 51230) 40
sym_block RA37 := symRun cfgP (rowCodeA.getD 37 []) (pcOf 51262) 40
sym_block RA38 := symRun cfgP (rowCodeA.getD 38 []) (pcOf 51294) 40
sym_block RA39 := symRun cfgP (rowCodeA.getD 39 []) (pcOf 51326) 40
sym_block RA40 := symRun cfgP (rowCodeA.getD 40 []) (pcOf 51358) 40
sym_block RA41 := symRun cfgP (rowCodeA.getD 41 []) (pcOf 51390) 40
sym_block RA42 := symRun cfgP (rowCodeA.getD 42 []) (pcOf 51422) 40
sym_block RA43 := symRun cfgP (rowCodeA.getD 43 []) (pcOf 51454) 40
sym_block RA44 := symRun cfgP (rowCodeA.getD 44 []) (pcOf 51486) 40
sym_block RA45 := symRun cfgP (rowCodeA.getD 45 []) (pcOf 51518) 40
sym_block RA46 := symRun cfgP (rowCodeA.getD 46 []) (pcOf 51550) 40
sym_block RA47 := symRun cfgP (rowCodeA.getD 47 []) (pcOf 51582) 40
sym_block RA48 := symRun cfgP (rowCodeA.getD 48 []) (pcOf 51614) 40
sym_block RA49 := symRun cfgP (rowCodeA.getD 49 []) (pcOf 51646) 40
sym_block RA50 := symRun cfgP (rowCodeA.getD 50 []) (pcOf 51678) 40
sym_block RA51 := symRun cfgP (rowCodeA.getD 51 []) (pcOf 51710) 40
sym_block RA52 := symRun cfgP (rowCodeA.getD 52 []) (pcOf 51742) 40
sym_block RA53 := symRun cfgP (rowCodeA.getD 53 []) (pcOf 51774) 40
sym_block RA54 := symRun cfgP (rowCodeA.getD 54 []) (pcOf 51806) 40
sym_block RA55 := symRun cfgP (rowCodeA.getD 55 []) (pcOf 51838) 40
sym_block RA56 := symRun cfgP (rowCodeA.getD 56 []) (pcOf 51870) 40
sym_block RA57 := symRun cfgP (rowCodeA.getD 57 []) (pcOf 51902) 40
sym_block RA58 := symRun cfgP (rowCodeA.getD 58 []) (pcOf 51934) 40
sym_block RA59 := symRun cfgP (rowCodeA.getD 59 []) (pcOf 51966) 40
sym_block RA60 := symRun cfgP (rowCodeA.getD 60 []) (pcOf 51998) 40
sym_block RA61 := symRun cfgP (rowCodeA.getD 61 []) (pcOf 52030) 40
sym_block RA62 := symRun cfgP (rowCodeA.getD 62 []) (pcOf 52062) 40
sym_block RA63 := symRun cfgP (rowCodeA.getD 63 []) (pcOf 52094) 40
sym_block RB0 := symRun cfgP (rowCodeB.getD 0 []) (pcOf 52126) 40
sym_block RB1 := symRun cfgP (rowCodeB.getD 1 []) (pcOf 52158) 40
sym_block RB2 := symRun cfgP (rowCodeB.getD 2 []) (pcOf 52190) 40
sym_block RB3 := symRun cfgP (rowCodeB.getD 3 []) (pcOf 52222) 40
sym_block RB4 := symRun cfgP (rowCodeB.getD 4 []) (pcOf 52254) 40
sym_block RB5 := symRun cfgP (rowCodeB.getD 5 []) (pcOf 52286) 40
sym_block RB6 := symRun cfgP (rowCodeB.getD 6 []) (pcOf 52318) 40
sym_block RB7 := symRun cfgP (rowCodeB.getD 7 []) (pcOf 52350) 40
sym_block RB8 := symRun cfgP (rowCodeB.getD 8 []) (pcOf 52382) 40
sym_block RB9 := symRun cfgP (rowCodeB.getD 9 []) (pcOf 52414) 40
sym_block RB10 := symRun cfgP (rowCodeB.getD 10 []) (pcOf 52446) 40
sym_block RB11 := symRun cfgP (rowCodeB.getD 11 []) (pcOf 52478) 40
sym_block RB12 := symRun cfgP (rowCodeB.getD 12 []) (pcOf 52510) 40
sym_block RB13 := symRun cfgP (rowCodeB.getD 13 []) (pcOf 52542) 40
sym_block RB14 := symRun cfgP (rowCodeB.getD 14 []) (pcOf 52574) 40
sym_block RB15 := symRun cfgP (rowCodeB.getD 15 []) (pcOf 52606) 40
sym_block RB16 := symRun cfgP (rowCodeB.getD 16 []) (pcOf 52638) 40
sym_block RB17 := symRun cfgP (rowCodeB.getD 17 []) (pcOf 52670) 40
sym_block RB18 := symRun cfgP (rowCodeB.getD 18 []) (pcOf 52702) 40
sym_block RB19 := symRun cfgP (rowCodeB.getD 19 []) (pcOf 52734) 40
sym_block RB20 := symRun cfgP (rowCodeB.getD 20 []) (pcOf 52766) 40
sym_block RB21 := symRun cfgP (rowCodeB.getD 21 []) (pcOf 52798) 40
sym_block RB22 := symRun cfgP (rowCodeB.getD 22 []) (pcOf 52830) 40
sym_block RB23 := symRun cfgP (rowCodeB.getD 23 []) (pcOf 52862) 40
sym_block RB24 := symRun cfgP (rowCodeB.getD 24 []) (pcOf 52894) 40
sym_block RB25 := symRun cfgP (rowCodeB.getD 25 []) (pcOf 52926) 40
sym_block RB26 := symRun cfgP (rowCodeB.getD 26 []) (pcOf 52958) 40
sym_block RB27 := symRun cfgP (rowCodeB.getD 27 []) (pcOf 52990) 40
sym_block RB28 := symRun cfgP (rowCodeB.getD 28 []) (pcOf 53022) 40
sym_block RB29 := symRun cfgP (rowCodeB.getD 29 []) (pcOf 53054) 40
sym_block RB30 := symRun cfgP (rowCodeB.getD 30 []) (pcOf 53086) 40
sym_block RB31 := symRun cfgP (rowCodeB.getD 31 []) (pcOf 53118) 40
sym_block RB32 := symRun cfgP (rowCodeB.getD 32 []) (pcOf 53150) 40
sym_block RB33 := symRun cfgP (rowCodeB.getD 33 []) (pcOf 53182) 40
sym_block RB34 := symRun cfgP (rowCodeB.getD 34 []) (pcOf 53214) 40
sym_block RB35 := symRun cfgP (rowCodeB.getD 35 []) (pcOf 53246) 40
sym_block RB36 := symRun cfgP (rowCodeB.getD 36 []) (pcOf 53278) 40
sym_block RB37 := symRun cfgP (rowCodeB.getD 37 []) (pcOf 53310) 40
sym_block RB38 := symRun cfgP (rowCodeB.getD 38 []) (pcOf 53342) 40
sym_block RB39 := symRun cfgP (rowCodeB.getD 39 []) (pcOf 53374) 40
sym_block RB40 := symRun cfgP (rowCodeB.getD 40 []) (pcOf 53406) 40
sym_block RB41 := symRun cfgP (rowCodeB.getD 41 []) (pcOf 53438) 40
sym_block RB42 := symRun cfgP (rowCodeB.getD 42 []) (pcOf 53470) 40
sym_block RB43 := symRun cfgP (rowCodeB.getD 43 []) (pcOf 53502) 40
sym_block RB44 := symRun cfgP (rowCodeB.getD 44 []) (pcOf 53534) 40
sym_block RB45 := symRun cfgP (rowCodeB.getD 45 []) (pcOf 53566) 40
sym_block RB46 := symRun cfgP (rowCodeB.getD 46 []) (pcOf 53598) 40
sym_block RB47 := symRun cfgP (rowCodeB.getD 47 []) (pcOf 53630) 40
sym_block RB48 := symRun cfgP (rowCodeB.getD 48 []) (pcOf 53662) 40
sym_block RB49 := symRun cfgP (rowCodeB.getD 49 []) (pcOf 53694) 40
sym_block RB50 := symRun cfgP (rowCodeB.getD 50 []) (pcOf 53726) 40
sym_block RB51 := symRun cfgP (rowCodeB.getD 51 []) (pcOf 53758) 40
sym_block RB52 := symRun cfgP (rowCodeB.getD 52 []) (pcOf 53790) 40
sym_block RB53 := symRun cfgP (rowCodeB.getD 53 []) (pcOf 53822) 40
sym_block RB54 := symRun cfgP (rowCodeB.getD 54 []) (pcOf 53854) 40
sym_block RB55 := symRun cfgP (rowCodeB.getD 55 []) (pcOf 53886) 40
sym_block RB56 := symRun cfgP (rowCodeB.getD 56 []) (pcOf 53918) 40
sym_block RB57 := symRun cfgP (rowCodeB.getD 57 []) (pcOf 53950) 40
sym_block RB58 := symRun cfgP (rowCodeB.getD 58 []) (pcOf 53982) 40
sym_block RB59 := symRun cfgP (rowCodeB.getD 59 []) (pcOf 54014) 40
sym_block RB60 := symRun cfgP (rowCodeB.getD 60 []) (pcOf 54046) 40
sym_block RB61 := symRun cfgP (rowCodeB.getD 61 []) (pcOf 54078) 40
sym_block RB62 := symRun cfgP (rowCodeB.getD 62 []) (pcOf 54110) 40
sym_block RB63 := symRun cfgP (rowCodeB.getD 63 []) (pcOf 54142) 40

/-! ### Generic memory lemmas -/
def vFun (M : Nat → Word) (A : Nat) : Word :=
  match vTable.reverse.find? (fun e => decide (e.1 = A)) with
  | some e => M (0x300000 + e.2)
  | none => M A

theorem memEval_vmap (s : MachineState) (L : List (Nat × Nat)) (hL : ∀ e ∈ L, e.1 < 2 ^ 64 ∧ 0x300000 + e.2 < 2 ^ 64)
    (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (L.map vWrite) (BitVec.ofNat 64 A) =
      match L.find? (fun e => decide (e.1 = A)) with
      | some e => s.getMem (BitVec.ofNat 64 (0x300000 + e.2))
      | none => s.getMem (BitVec.ofNat 64 A) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have he := hL e (List.mem_cons_self ..)
    rw [List.map_cons, memEval_cons, List.find?_cons]
    simp only [vWrite, Addr.eval, E.eval]
    by_cases h : e.1 = A
    · subst h; simp
    · rw [if_neg (fun h' => h ((ofNat_inj hA he.1).mp h').symm), ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))]
      simp [h]

theorem vTable_bounds : ∀ e ∈ vTable.reverse, e.1 < 2 ^ 64 ∧ 0x300000 + e.2 < 2 ^ 64 := by decide +kernel

theorem vals_spec {im : Image} (hc : CodeAt im (pcOf 49469) cVals) (s : MachineState) (hpc : s.pc = pcOf 49469) :
    ∃ t, Steps im s 586 586 t ∧ t.pc = pcOf 50055 ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      t.getReg .x29 = BitVec.ofNat 64 0x300000 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = vFun (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  refine ⟨_, symRun_sound run_vals hc s hpc (by simp [vRes, Result.obligs, Oblig.all]), ?_, ?_, ?_, ?_⟩
  · simp [vRes, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, vRes, vRegs]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · simp [vRes, vRegs, RegFile.get, RegFile.set, E.eval]
  · intro A hA
    simp only [Result.toState_getMem, vRes, vWrites]
    rw [memEval_vmap s _ vTable_bounds A hA]
    rfl

/-- The row obligations: valid stores into the new path area, valid loads from the saved area, and the
load/store separation. -/
def oblOK : Oblig → Bool
  | .valid ⟨some (.reg .x30), off⟩ 8 => decide (off.toNat + 8 ≤ 672) && decide (off.toNat % 8 = 0)
  | .valid ⟨some (.reg .x29), off⟩ 8 => decide (off.toNat + 8 ≤ 768) && decide (off.toNat % 8 = 0)
  | .ne ⟨some (.reg .x29), a⟩ ⟨some (.reg .x30), b⟩ => decide (a.toNat < 4096) && decide (b.toNat < 4096)
  | _ => false

theorem ofNat_add_word (c : Nat) (w : Word) : BitVec.ofNat 64 c + w = BitVec.ofNat 64 (c + w.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem oblOK_holds (s : MachineState) (h29 : s.getReg .x29 = BitVec.ofNat 64 0x301000)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 11792) (o : Oblig) (h : oblOK o = true) : o.holds s := by
  unfold oblOK at h
  split at h
  · rename_i off
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Oblig.holds, Addr.eval, E.eval, h30, ofNat_add_word]
    exact valid8P _ (by omega) (by omega)
  · rename_i off
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Oblig.holds, Addr.eval, E.eval, h29, ofNat_add_word]
    exact valid8P _ (by omega) (by omega)
  · rename_i a b
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Oblig.holds, Addr.eval, E.eval, h29, h30, ofNat_add_word]
    intro he
    have := (ofNat_inj (by omega) (by omega)).mp he
    omega
  · exact absurd h (by simp)

def rowWrite (e : Nat × Nat) : Addr × E :=
  (⟨some (.reg .x30), BitVec.ofNat 64 e.2⟩, .ld (addC (.reg .x29) (BitVec.ofNat 64 e.1)))
def rowLast (pairs : List (Nat × Nat)) : Nat := (pairs.getLast?.map Prod.fst).getD 0
structure RowOK (R : Result) (pairs : List (Nat × Nat)) (ret : Nat) : Prop where
  mem : R.st.mem = pairs.reverse.map rowWrite
  obl : R.st.obl.all oblOK = true
  pc : R.pc = .c (pcOf ret)
  steps : R.steps = 25
  cycles : R.cycles = 25
  regs : R.st.regs = RegFile.init.set .x6 (.ld (addC (.reg .x29) (BitVec.ofNat 64 (rowLast pairs))))

def rowFun (pairs : List (Nat × Nat)) (M : Nat → Word) (A : Nat) : Word :=
  match pairs.reverse.find? (fun e => decide (11792 + e.2 = A)) with
  | some e => M (0x301000 + e.1)
  | none => M A

theorem memEval_rmap (s : MachineState) (h29 : s.getReg .x29 = BitVec.ofNat 64 0x301000)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 11792) (L : List (Nat × Nat)) (hL : ∀ e ∈ L, e.1 < 4096 ∧ e.2 < 4096)
    (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (L.map rowWrite) (BitVec.ofNat 64 A) =
      match L.find? (fun e => decide (11792 + e.2 = A)) with
      | some e => s.getMem (BitVec.ofNat 64 (0x301000 + e.1))
      | none => s.getMem (BitVec.ofNat 64 A) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have he := hL e (List.mem_cons_self ..)
    rw [List.map_cons, memEval_cons, List.find?_cons]
    simp only [rowWrite, Addr.eval, E.eval, addC_eval, h29, h30, ofNat_add_ofNat]
    by_cases h : 11792 + e.2 = A
    · subst h; simp
    · rw [if_neg (fun h' => h ((ofNat_inj hA (by omega)).mp h').symm), ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))]
      simp [h]

theorem row_spec {im : Image} {code : List (BitVec 32)} {p ret : Nat} {pairs : List (Nat × Nat)} {R : Result}
    (hrun : symRun cfgP code (pcOf p) 40 = some R) (hc : CodeAt im (pcOf p) code) (hok : RowOK R pairs ret)
    (hpairs : ∀ e ∈ pairs, e.1 < 4096 ∧ e.2 < 4096)
    (s : MachineState) (hpc : s.pc = pcOf p) (h29 : s.getReg .x29 = BitVec.ofNat 64 0x301000)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 11792) :
    ∃ t, Steps im s 25 25 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = rowFun pairs (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  have hobl : R.obligs s := by
    show Oblig.all s _
    rw [Oblig.all_iff]
    intro o ho
    exact oblOK_holds s h29 h30 o (List.all_eq_true.mp hok.obl o ho)
  have st := symRun_sound hrun hc s hpc hobl
  rw [hok.steps, hok.cycles] at st
  refine ⟨_, st, ?_, ?_, ?_⟩
  · simp [hok.pc, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Result.toState_getReg, hok.regs]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, hok.mem]
    rw [memEval_rmap s h29 h30 _ (fun e he => hpairs e (List.mem_reverse.mp he)) A hA]
    rfl

theorem rowA_ok (r : Nat) (hr : r < 64) : ∃ R, symRun cfgP (rowCodeA.getD r []) (pcOf (50078 + 32 * r)) 40 = some R ∧
    RowOK R (rowsA.getD r []) 50070 := by
  interval_cases r
  · exact ⟨_, RA0, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA1, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA2, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA3, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA4, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA5, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA6, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA7, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA8, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA9, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA10, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA11, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA12, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA13, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA14, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA15, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA16, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA17, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA18, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA19, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA20, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA21, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA22, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA23, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA24, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA25, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA26, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA27, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA28, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA29, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA30, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA31, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA32, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA33, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA34, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA35, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA36, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA37, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA38, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA39, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA40, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA41, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA42, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA43, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA44, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA45, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA46, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA47, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA48, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA49, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA50, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA51, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA52, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA53, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA54, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA55, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA56, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA57, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA58, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA59, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA60, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA61, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA62, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA63, by constructor <;> kernel_rfl⟩

theorem rowB_ok (r : Nat) (hr : r < 64) : ∃ R, symRun cfgP (rowCodeB.getD r []) (pcOf (52126 + 32 * r)) 40 = some R ∧
    RowOK R (rowsB.getD r []) 50077 := by
  interval_cases r
  · exact ⟨_, RB0, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB1, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB2, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB3, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB4, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB5, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB6, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB7, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB8, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB9, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB10, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB11, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB12, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB13, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB14, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB15, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB16, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB17, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB18, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB19, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB20, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB21, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB22, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB23, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB24, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB25, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB26, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB27, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB28, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB29, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB30, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB31, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB32, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB33, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB34, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB35, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB36, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB37, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB38, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB39, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB40, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB41, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB42, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB43, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB44, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB45, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB46, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB47, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB48, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB49, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB50, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB51, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB52, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB53, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB54, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB55, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB56, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB57, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB58, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB59, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB60, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB61, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB62, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB63, by constructor <;> kernel_rfl⟩
theorem rowsA_bounds : ∀ r < 64, ∀ e ∈ rowsA.getD r [], e.1 < 4096 ∧ e.2 < 4096 := by decide +kernel
theorem rowsB_bounds : ∀ r < 64, ∀ e ∈ rowsB.getD r [], e.1 < 4096 ∧ e.2 < 4096 := by decide +kernel

end ClaudeWCT.W9.Machine.Expand.PostPass
end
-- ==== merged from T3M_Verify_ChainCheckParts ====
section

namespace SigGolfCandidate.T3M
/-- Join bounded checks while keeping the closed code predicates opaque to unification. -/
theorem chain_all_range'_add {p : Nat → Bool} {lo left right : Nat}
    (hleft : (List.range' lo left).all p = true)
    (hright : (List.range' (lo + left) right).all p = true) :
    (List.range' lo (left + right)).all p = true := by
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl

theorem triCheck_add {t lo left right : Nat} (hdiv : left % 8 = 0)
    (hleft : triCheck t lo left = true)
    (hright : triCheck t (lo + left) right = true) :
    triCheck t lo (left + right) = true := by
  simp only [triCheck, Bool.and_eq_true] at hleft hright ⊢
  refine ⟨@chain_all_range'_add (entCheck t) lo left right hleft.1 hright.1, ?_⟩
  have hstart : (lo + left) / 8 = lo / 8 + left / 8 := by omega
  have hcount : (left + right) / 8 = left / 8 + right / 8 := by omega
  rw [hstart] at hright
  rw [hcount]
  exact @chain_all_range'_add (fun q => blkCheck t (q / 8) (q % 8))
    (lo / 8) (left / 8) (right / 8) hleft.2 hright.2
end SigGolfCandidate.T3M
end
