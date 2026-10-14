import SigGolfCandidate.T3M.ImageSlice
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Expand

namespace SigGolfCandidate.T3M.Images.Slices
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-- Skip full fixed-width chunks before reducing the requested suffix. -/
def chunkTail {α : Type} (cs : List (List α)) (width b : Nat) : List α :=
  (cs.drop (b / width)).flatten.drop (b % width)

private theorem foldl_chunks {α : Type} (cs : List (List α)) (acc : List α) :
    cs.foldl (· ++ ·) acc = acc ++ cs.flatten := by
  induction cs generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
  | cons c cs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]

private theorem drop_chunks {α : Type} (width : Nat) :
    ∀ (cs : List (List α)) (k : Nat),
    (cs.dropLast.all fun c => c.length == width) = true → k < cs.length →
    cs.flatten.drop (width * k) = (cs.drop k).flatten := by
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
        have hlen : c.length = width := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == width) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show width * (k + 1) = c.length + width * k by rw [hlen]; ring,
          ← List.drop_drop, List.drop_left]
        exact this

theorem chunkTail_eq {α : Type} (cs : List (List α)) (width b : Nat)
    (hall : (cs.dropLast.all fun c => c.length == width) = true)
    (hb : b / width < cs.length) : chunkTail cs width b = cs.flatten.drop b := by
  unfold chunkTail
  rw [← drop_chunks width cs (b / width) hall hb, List.drop_drop]
  congr 1
  have := Nat.mod_add_div b width
  omega

def expandChunks : List (List (BitVec 32)) :=
  [expandCode_0, expandCode_1, expandCode_2, expandCode_3, expandCode_4, expandCode_5, expandCode_6, expandCode_7, expandCode_8, expandCode_9, expandCode_10, expandCode_11, expandCode_12, expandCode_13, expandCode_14, expandCode_15, expandCode_16, expandCode_17, expandCode_18, expandCode_19, expandCode_20, expandCode_21, expandCode_22, expandCode_23, expandCode_24, expandCode_25, expandCode_26, expandCode_27, expandCode_28, expandCode_29, expandCode_30, expandCode_31, expandCode_32, expandCode_33, expandCode_34, expandCode_35, expandCode_36, expandCode_37, expandCode_38, expandCode_39, expandCode_40, expandCode_41, expandCode_42, expandCode_43, expandCode_44, expandCode_45, expandCode_46, expandCode_47, expandCode_48, expandCode_49, expandCode_50, expandCode_51, expandCode_52, expandCode_53, expandCode_54, expandCode_55, expandCode_56, expandCode_57, expandCode_58, expandCode_59, expandCode_60, expandCode_61, expandCode_62, expandCode_63, expandCode_64, expandCode_65, expandCode_66, expandCode_67, expandCode_68, expandCode_69, expandCode_70, expandCode_71, expandCode_72, expandCode_73, expandCode_74, expandCode_75, expandCode_76, expandCode_77, expandCode_78, expandCode_79, expandCode_80, expandCode_81, expandCode_82, expandCode_83, expandCode_84, expandCode_85, expandCode_86, expandCode_87, expandCode_88, expandCode_89, expandCode_90, expandCode_91, expandCode_92, expandCode_93, expandCode_94, expandCode_95, expandCode_96, expandCode_97, expandCode_98, expandCode_99, expandCode_100, expandCode_101, expandCode_102, expandCode_103, expandCode_104, expandCode_105, expandCode_106, expandCode_107, expandCode_108, expandCode_109, expandCode_110, expandCode_111, expandCode_112, expandCode_113, expandCode_114, expandCode_115, expandCode_116, expandCode_117, expandCode_118, expandCode_119, expandCode_120, expandCode_121, expandCode_122, expandCode_123, expandCode_124, expandCode_125, expandCode_126, expandCode_127, expandCode_128, expandCode_129, expandCode_130, expandCode_131, expandCode_132, expandCode_133, expandCode_134, expandCode_135, expandCode_136, expandCode_137, expandCode_138, expandCode_139, expandCode_140, expandCode_141, expandCode_142, expandCode_143, expandCode_144, expandCode_145, expandCode_146, expandCode_147, expandCode_148, expandCode_149, expandCode_150, expandCode_151, expandCode_152, expandCode_153, expandCode_154, expandCode_155, expandCode_156, expandCode_157, expandCode_158, expandCode_159, expandCode_160, expandCode_161, expandCode_162, expandCode_163, expandCode_164, expandCode_165, expandCode_166, expandCode_167, expandCode_168, expandCode_169, expandCode_170, expandCode_171, expandCode_172, expandCode_173]

private theorem expandCode_flatten : expandCode = expandChunks.flatten := by
  change expandChunks.foldl (· ++ ·) [] = expandChunks.flatten
  rw [foldl_chunks, List.nil_append]

private theorem expandChunks_ok :
    (expandChunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel

private theorem expandChunks_length : expandChunks.length = 174 := by
  decide +kernel

theorem expandCode_drop_eq (b : Nat) (hb : b / 256 < 174) :
    expandCode.drop b = chunkTail expandChunks 256 b := by
  rw [expandCode_flatten]
  exact (chunkTail_eq expandChunks 256 b expandChunks_ok
    (by rw [expandChunks_length]; exact hb)).symm

def signChunks : List (List (BitVec 32)) :=
  [signCode_0, signCode_1, signCode_2, signCode_3, signCode_4, signCode_5, signCode_6, signCode_7, signCode_8, signCode_9, signCode_10, signCode_11, signCode_12, signCode_13, signCode_14, signCode_15, signCode_16, signCode_17, signCode_18, signCode_19, signCode_20, signCode_21, signCode_22, signCode_23, signCode_24, signCode_25, signCode_26, signCode_27, signCode_28, signCode_29, signCode_30, signCode_31, signCode_32, signCode_33, signCode_34, signCode_35, signCode_36, signCode_37, signCode_38, signCode_39, signCode_40, signCode_41, signCode_42, signCode_43, signCode_44, signCode_45, signCode_46, signCode_47, signCode_48, signCode_49, signCode_50, signCode_51, signCode_52, signCode_53, signCode_54, signCode_55, signCode_56, signCode_57, signCode_58, signCode_59, signCode_60, signCode_61, signCode_62, signCode_63, signCode_64, signCode_65, signCode_66, signCode_67, signCode_68, signCode_69, signCode_70, signCode_71, signCode_72, signCode_73, signCode_74, signCode_75, signCode_76, signCode_77, signCode_78, signCode_79, signCode_80, signCode_81, signCode_82, signCode_83, signCode_84, signCode_85]

private theorem signCode_flatten : signCode = signChunks.flatten := by
  change signChunks.foldl (· ++ ·) [] = signChunks.flatten
  rw [foldl_chunks, List.nil_append]

private theorem signChunks_ok :
    (signChunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel

private theorem signChunks_length : signChunks.length = 86 := by
  decide +kernel

theorem signCode_drop_eq (b : Nat) (hb : b / 256 < 86) :
    signCode.drop b = chunkTail signChunks 256 b := by
  rw [signCode_flatten]
  exact (chunkTail_eq signChunks 256 b signChunks_ok
    (by rw [signChunks_length]; exact hb)).symm

end SigGolfCandidate.T3M.Images.Slices
