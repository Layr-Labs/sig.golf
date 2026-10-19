import SigGolfCandidate.T3M_ImageSlice
import SigGolfCandidate.T3M_Images_Sign
import SigGolfCandidate.T3M_Images_Expand
set_option Elab.async false

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
  [expandCode_0, expandCode_1, expandCode_2, expandCode_3, expandCode_4, expandCode_5, expandCode_6, expandCode_7, expandCode_8, expandCode_9, expandCode_10, expandCode_11, expandCode_12, expandCode_13, expandCode_14, expandCode_15, expandCode_16, expandCode_17, expandCode_18, expandCode_19, expandCode_20, expandCode_21, expandCode_22, expandCode_23, expandCode_24, expandCode_25, expandCode_26, expandCode_27, expandCode_28, expandCode_29, expandCode_30, expandCode_31, expandCode_32, expandCode_33, expandCode_34, expandCode_35, expandCode_36, expandCode_37, expandCode_38, expandCode_39, expandCode_40, expandCode_41, expandCode_42, expandCode_43, expandCode_44, expandCode_45, expandCode_46, expandCode_47, expandCode_48, expandCode_49, expandCode_50, expandCode_51, expandCode_52, expandCode_53, expandCode_54, expandCode_55, expandCode_56, expandCode_57, expandCode_58, expandCode_59, expandCode_60, expandCode_61, expandCode_62, expandCode_63, expandCode_64, expandCode_65, expandCode_66, expandCode_67, expandCode_68, expandCode_69, expandCode_70, expandCode_71, expandCode_72, expandCode_73, expandCode_74, expandCode_75, expandCode_76, expandCode_77, expandCode_78, expandCode_79, expandCode_80, expandCode_81, expandCode_82, expandCode_83, expandCode_84, expandCode_85, expandCode_86, expandCode_87, expandCode_88, expandCode_89, expandCode_90, expandCode_91, expandCode_92, expandCode_93, expandCode_94, expandCode_95, expandCode_96, expandCode_97, expandCode_98, expandCode_99, expandCode_100, expandCode_101, expandCode_102, expandCode_103, expandCode_104, expandCode_105, expandCode_106, expandCode_107, expandCode_108, expandCode_109, expandCode_110, expandCode_111, expandCode_112, expandCode_113, expandCode_114, expandCode_115, expandCode_116, expandCode_117, expandCode_118, expandCode_119, expandCode_120, expandCode_121, expandCode_122, expandCode_123, expandCode_124, expandCode_125, expandCode_126, expandCode_127, expandCode_128, expandCode_129, expandCode_130, expandCode_131, expandCode_132, expandCode_133, expandCode_134, expandCode_135, expandCode_136, expandCode_137, expandCode_138, expandCode_139, expandCode_140, expandCode_141, expandCode_142, expandCode_143, expandCode_144, expandCode_145, expandCode_146, expandCode_147, expandCode_148, expandCode_149, expandCode_150, expandCode_151, expandCode_152, expandCode_153, expandCode_154, expandCode_155, expandCode_156, expandCode_157, expandCode_158, expandCode_159, expandCode_160, expandCode_161, expandCode_162, expandCode_163, expandCode_164, expandCode_165, expandCode_166, expandCode_167, expandCode_168, expandCode_169, expandCode_170, expandCode_171, expandCode_172]

private theorem expandCode_flatten : expandCode = expandChunks.flatten := by
  change expandChunks.foldl (· ++ ·) [] = expandChunks.flatten
  rw [foldl_chunks, List.nil_append]

private theorem expandChunks_ok :
    (expandChunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel

private theorem expandChunks_length : expandChunks.length = 173 := by
  decide +kernel

theorem expandCode_drop_eq (b : Nat) (hb : b / 256 < 173) :
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

def signReferenceChunks : List (List (BitVec 32)) :=
  [signReferenceCode_0, signReferenceCode_1, signReferenceCode_2, signReferenceCode_3, signReferenceCode_4, signReferenceCode_5, signReferenceCode_6, signReferenceCode_7, signReferenceCode_8, signReferenceCode_9, signReferenceCode_10, signReferenceCode_11, signReferenceCode_12, signReferenceCode_13, signReferenceCode_14, signReferenceCode_15, signReferenceCode_16, signReferenceCode_17, signReferenceCode_18, signReferenceCode_19, signReferenceCode_20, signReferenceCode_21, signReferenceCode_22, signReferenceCode_23, signReferenceCode_24, signReferenceCode_25, signReferenceCode_26, signReferenceCode_27, signReferenceCode_28, signReferenceCode_29, signReferenceCode_30, signReferenceCode_31, signReferenceCode_32, signReferenceCode_33, signReferenceCode_34, signReferenceCode_35, signReferenceCode_36, signReferenceCode_37, signReferenceCode_38, signReferenceCode_39, signReferenceCode_40, signReferenceCode_41, signReferenceCode_42, signReferenceCode_43, signReferenceCode_44, signReferenceCode_45, signReferenceCode_46, signReferenceCode_47, signReferenceCode_48, signReferenceCode_49, signReferenceCode_50, signReferenceCode_51, signReferenceCode_52, signReferenceCode_53, signReferenceCode_54, signReferenceCode_55, signReferenceCode_56, signReferenceCode_57, signReferenceCode_58, signReferenceCode_59, signReferenceCode_60, signReferenceCode_61, signReferenceCode_62, signReferenceCode_63, signReferenceCode_64, signReferenceCode_65, signReferenceCode_66, signReferenceCode_67, signReferenceCode_68, signReferenceCode_69, signReferenceCode_70, signReferenceCode_71, signReferenceCode_72, signReferenceCode_73, signReferenceCode_74, signReferenceCode_75, signReferenceCode_76, signReferenceCode_77, signReferenceCode_78, signReferenceCode_79, signReferenceCode_80, signReferenceCode_81, signReferenceCode_82, signReferenceCode_83, signReferenceCode_84, signReferenceCode_85]

private theorem signReferenceCode_flatten : signReferenceCode = signReferenceChunks.flatten := by
  change signReferenceChunks.foldl (· ++ ·) [] = signReferenceChunks.flatten
  rw [foldl_chunks, List.nil_append]

private theorem signReferenceChunks_ok :
    (signReferenceChunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel

private theorem signReferenceChunks_length : signReferenceChunks.length = 86 := by
  decide +kernel

theorem signReferenceCode_drop_eq (b : Nat) (hb : b / 256 < 86) :
    signReferenceCode.drop b = chunkTail signReferenceChunks 256 b := by
  rw [signReferenceCode_flatten]
  exact (chunkTail_eq signReferenceChunks 256 b signReferenceChunks_ok
    (by rw [signReferenceChunks_length]; exact hb)).symm

def expandReferenceChunks : List (List (BitVec 32)) :=
  [expandReferenceCode_0, expandReferenceCode_1, expandReferenceCode_2, expandReferenceCode_3, expandReferenceCode_4, expandReferenceCode_5, expandReferenceCode_6, expandReferenceCode_7, expandReferenceCode_8, expandReferenceCode_9, expandReferenceCode_10, expandReferenceCode_11, expandReferenceCode_12, expandReferenceCode_13, expandReferenceCode_14, expandReferenceCode_15, expandReferenceCode_16, expandReferenceCode_17, expandReferenceCode_18, expandReferenceCode_19, expandReferenceCode_20, expandReferenceCode_21, expandReferenceCode_22, expandReferenceCode_23, expandReferenceCode_24, expandReferenceCode_25, expandReferenceCode_26, expandReferenceCode_27, expandReferenceCode_28, expandReferenceCode_29, expandReferenceCode_30, expandReferenceCode_31, expandReferenceCode_32, expandReferenceCode_33, expandReferenceCode_34, expandReferenceCode_35, expandReferenceCode_36, expandReferenceCode_37, expandReferenceCode_38, expandReferenceCode_39, expandReferenceCode_40, expandReferenceCode_41, expandReferenceCode_42, expandReferenceCode_43, expandReferenceCode_44, expandReferenceCode_45, expandReferenceCode_46, expandReferenceCode_47, expandReferenceCode_48, expandReferenceCode_49, expandReferenceCode_50, expandReferenceCode_51, expandReferenceCode_52, expandReferenceCode_53, expandReferenceCode_54, expandReferenceCode_55, expandReferenceCode_56, expandReferenceCode_57, expandReferenceCode_58, expandReferenceCode_59, expandReferenceCode_60, expandReferenceCode_61, expandReferenceCode_62, expandReferenceCode_63, expandReferenceCode_64, expandReferenceCode_65, expandReferenceCode_66, expandReferenceCode_67, expandReferenceCode_68, expandReferenceCode_69, expandReferenceCode_70, expandReferenceCode_71, expandReferenceCode_72, expandReferenceCode_73, expandReferenceCode_74, expandReferenceCode_75, expandReferenceCode_76, expandReferenceCode_77, expandReferenceCode_78, expandReferenceCode_79, expandReferenceCode_80, expandReferenceCode_81, expandReferenceCode_82, expandReferenceCode_83, expandReferenceCode_84, expandReferenceCode_85, expandReferenceCode_86, expandReferenceCode_87, expandReferenceCode_88, expandReferenceCode_89, expandReferenceCode_90, expandReferenceCode_91, expandReferenceCode_92, expandReferenceCode_93, expandReferenceCode_94, expandReferenceCode_95, expandReferenceCode_96, expandReferenceCode_97, expandReferenceCode_98, expandReferenceCode_99, expandReferenceCode_100, expandReferenceCode_101, expandReferenceCode_102, expandReferenceCode_103, expandReferenceCode_104, expandReferenceCode_105, expandReferenceCode_106, expandReferenceCode_107, expandReferenceCode_108, expandReferenceCode_109, expandReferenceCode_110, expandReferenceCode_111, expandReferenceCode_112, expandReferenceCode_113, expandReferenceCode_114, expandReferenceCode_115, expandReferenceCode_116, expandReferenceCode_117, expandReferenceCode_118, expandReferenceCode_119, expandReferenceCode_120, expandReferenceCode_121, expandReferenceCode_122, expandReferenceCode_123, expandReferenceCode_124, expandReferenceCode_125, expandReferenceCode_126, expandReferenceCode_127, expandReferenceCode_128, expandReferenceCode_129, expandReferenceCode_130, expandReferenceCode_131, expandReferenceCode_132, expandReferenceCode_133, expandReferenceCode_134, expandReferenceCode_135, expandReferenceCode_136, expandReferenceCode_137, expandReferenceCode_138, expandReferenceCode_139, expandReferenceCode_140, expandReferenceCode_141, expandReferenceCode_142, expandReferenceCode_143, expandReferenceCode_144, expandReferenceCode_145, expandReferenceCode_146, expandReferenceCode_147, expandReferenceCode_148, expandReferenceCode_149, expandReferenceCode_150, expandReferenceCode_151, expandReferenceCode_152, expandReferenceCode_153, expandReferenceCode_154, expandReferenceCode_155, expandReferenceCode_156, expandReferenceCode_157, expandReferenceCode_158, expandReferenceCode_159, expandReferenceCode_160, expandReferenceCode_161, expandReferenceCode_162, expandReferenceCode_163, expandReferenceCode_164, expandReferenceCode_165, expandReferenceCode_166, expandReferenceCode_167, expandReferenceCode_168, expandReferenceCode_169, expandReferenceCode_170, expandReferenceCode_171, expandReferenceCode_172]

private theorem expandReferenceCode_flatten : expandReferenceCode = expandReferenceChunks.flatten := by
  change expandReferenceChunks.foldl (· ++ ·) [] = expandReferenceChunks.flatten
  rw [foldl_chunks, List.nil_append]

private theorem expandReferenceChunks_ok :
    (expandReferenceChunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel

private theorem expandReferenceChunks_length : expandReferenceChunks.length = 173 := by
  decide +kernel

theorem expandReferenceCode_drop_eq (b : Nat) (hb : b / 256 < 173) :
    expandReferenceCode.drop b = chunkTail expandReferenceChunks 256 b := by
  rw [expandReferenceCode_flatten]
  exact (chunkTail_eq expandReferenceChunks 256 b expandReferenceChunks_ok
    (by rw [expandReferenceChunks_length]; exact hb)).symm

end SigGolfCandidate.T3M.Images.Slices
