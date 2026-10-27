import SigGolfCandidate.Merge050
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059

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
