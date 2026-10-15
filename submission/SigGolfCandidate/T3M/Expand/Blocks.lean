import SigGolfCandidate.T3M.ImageSlice
import SigGolfCandidate.T3M.Verify.Code
import SigGolfCandidate.T3M.Search.Blocks

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
def expandCodeChunks : List (List (BitVec 32)) := [Images.expandReferenceCode_0, Images.expandReferenceCode_1, Images.expandReferenceCode_2, Images.expandReferenceCode_3, Images.expandReferenceCode_4, Images.expandReferenceCode_5, Images.expandReferenceCode_6, Images.expandReferenceCode_7, Images.expandReferenceCode_8, Images.expandReferenceCode_9, Images.expandReferenceCode_10, Images.expandReferenceCode_11, Images.expandReferenceCode_12, Images.expandReferenceCode_13, Images.expandReferenceCode_14, Images.expandReferenceCode_15, Images.expandReferenceCode_16, Images.expandReferenceCode_17, Images.expandReferenceCode_18, Images.expandReferenceCode_19, Images.expandReferenceCode_20, Images.expandReferenceCode_21, Images.expandReferenceCode_22, Images.expandReferenceCode_23, Images.expandReferenceCode_24, Images.expandReferenceCode_25, Images.expandReferenceCode_26, Images.expandReferenceCode_27, Images.expandReferenceCode_28, Images.expandReferenceCode_29, Images.expandReferenceCode_30, Images.expandReferenceCode_31, Images.expandReferenceCode_32, Images.expandReferenceCode_33, Images.expandReferenceCode_34, Images.expandReferenceCode_35, Images.expandReferenceCode_36, Images.expandReferenceCode_37, Images.expandReferenceCode_38, Images.expandReferenceCode_39, Images.expandReferenceCode_40, Images.expandReferenceCode_41, Images.expandReferenceCode_42, Images.expandReferenceCode_43, Images.expandReferenceCode_44, Images.expandReferenceCode_45, Images.expandReferenceCode_46, Images.expandReferenceCode_47, Images.expandReferenceCode_48, Images.expandReferenceCode_49, Images.expandReferenceCode_50, Images.expandReferenceCode_51, Images.expandReferenceCode_52, Images.expandReferenceCode_53, Images.expandReferenceCode_54, Images.expandReferenceCode_55, Images.expandReferenceCode_56, Images.expandReferenceCode_57, Images.expandReferenceCode_58, Images.expandReferenceCode_59, Images.expandReferenceCode_60, Images.expandReferenceCode_61, Images.expandReferenceCode_62, Images.expandReferenceCode_63, Images.expandReferenceCode_64, Images.expandReferenceCode_65, Images.expandReferenceCode_66, Images.expandReferenceCode_67, Images.expandReferenceCode_68, Images.expandReferenceCode_69, Images.expandReferenceCode_70, Images.expandReferenceCode_71, Images.expandReferenceCode_72, Images.expandReferenceCode_73, Images.expandReferenceCode_74, Images.expandReferenceCode_75, Images.expandReferenceCode_76, Images.expandReferenceCode_77, Images.expandReferenceCode_78, Images.expandReferenceCode_79, Images.expandReferenceCode_80, Images.expandReferenceCode_81, Images.expandReferenceCode_82, Images.expandReferenceCode_83, Images.expandReferenceCode_84, Images.expandReferenceCode_85, Images.expandReferenceCode_86, Images.expandReferenceCode_87, Images.expandReferenceCode_88, Images.expandReferenceCode_89, Images.expandReferenceCode_90, Images.expandReferenceCode_91, Images.expandReferenceCode_92, Images.expandReferenceCode_93, Images.expandReferenceCode_94, Images.expandReferenceCode_95, Images.expandReferenceCode_96, Images.expandReferenceCode_97, Images.expandReferenceCode_98, Images.expandReferenceCode_99, Images.expandReferenceCode_100, Images.expandReferenceCode_101, Images.expandReferenceCode_102, Images.expandReferenceCode_103, Images.expandReferenceCode_104, Images.expandReferenceCode_105, Images.expandReferenceCode_106, Images.expandReferenceCode_107, Images.expandReferenceCode_108, Images.expandReferenceCode_109, Images.expandReferenceCode_110, Images.expandReferenceCode_111, Images.expandReferenceCode_112, Images.expandReferenceCode_113, Images.expandReferenceCode_114, Images.expandReferenceCode_115, Images.expandReferenceCode_116, Images.expandReferenceCode_117, Images.expandReferenceCode_118, Images.expandReferenceCode_119, Images.expandReferenceCode_120, Images.expandReferenceCode_121, Images.expandReferenceCode_122, Images.expandReferenceCode_123, Images.expandReferenceCode_124, Images.expandReferenceCode_125, Images.expandReferenceCode_126, Images.expandReferenceCode_127, Images.expandReferenceCode_128, Images.expandReferenceCode_129, Images.expandReferenceCode_130, Images.expandReferenceCode_131, Images.expandReferenceCode_132, Images.expandReferenceCode_133, Images.expandReferenceCode_134, Images.expandReferenceCode_135, Images.expandReferenceCode_136, Images.expandReferenceCode_137, Images.expandReferenceCode_138, Images.expandReferenceCode_139, Images.expandReferenceCode_140, Images.expandReferenceCode_141, Images.expandReferenceCode_142, Images.expandReferenceCode_143, Images.expandReferenceCode_144, Images.expandReferenceCode_145, Images.expandReferenceCode_146, Images.expandReferenceCode_147, Images.expandReferenceCode_148, Images.expandReferenceCode_149, Images.expandReferenceCode_150, Images.expandReferenceCode_151, Images.expandReferenceCode_152, Images.expandReferenceCode_153, Images.expandReferenceCode_154, Images.expandReferenceCode_155, Images.expandReferenceCode_156, Images.expandReferenceCode_157, Images.expandReferenceCode_158, Images.expandReferenceCode_159, Images.expandReferenceCode_160, Images.expandReferenceCode_161, Images.expandReferenceCode_162, Images.expandReferenceCode_163, Images.expandReferenceCode_164, Images.expandReferenceCode_165, Images.expandReferenceCode_166, Images.expandReferenceCode_167, Images.expandReferenceCode_168, Images.expandReferenceCode_169, Images.expandReferenceCode_170, Images.expandReferenceCode_171, Images.expandReferenceCode_172]
theorem expandCode_flatten : Images.expandReferenceCode = expandCodeChunks.flatten := by
  change expandCodeChunks.foldl (· ++ ·) [] = expandCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_expand_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (expandCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.expandReferenceImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.expandReferenceCode.drop b).take code.length = code
  rw [expandCode_flatten]
  exact h
/-- Skip whole image chunks before reducing a small code slice. -/
def expandCodeTail (b : Nat) : List (BitVec 32) :=
  (expandCodeChunks.drop (b / 256)).flatten.drop (b % 256)
set_option maxRecDepth 100000 in
private theorem expandCodeChunks_ok :
    (expandCodeChunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel
private theorem expandCodeChunks_length : expandCodeChunks.length = 173 := by
  decide +kernel
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
theorem expandCodeTail_eq (b : Nat) (hb : b / 256 < 173) :
    expandCodeTail b = expandCodeChunks.flatten.drop b := by
  unfold expandCodeTail
  rw [← expand_drop_chunks expandCodeChunks (b / 256) expandCodeChunks_ok
    (by rw [expandCodeChunks_length]; exact hb), List.drop_drop]
  congr 1
  omega
theorem codeAt_expand_chunk {b : Nat} {code : List (BitVec 32)}
    (hi : b / 256 < 173)
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (expandCodeTail b).take code.length = code) :
    CodeAt Images.expandReferenceImage (pcOf b) code := by
  apply codeAt_expand_slice hb
  rw [← expandCodeTail_eq b hi]
  exact h

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
def seg_0 : List (BitVec 32) := [1179816047,32439,7991,2148470547,963331,9352067,7286819,8336419,32439,134967,302976787,963331,9352067,7286819,8336419,28343,134967,336531219,1578021635,1586410371,7286819,8336419,28343,134967,353308435,1594798851,1603187587,7286819,8336419,814911599]
def seg_49 : List (BitVec 32) := [134711,370019859,930947,34903187,34919571,134711,1426984467,10367011,7735,2165181971,20848675,139575,2323,6967,3289058067,1043]
def seg_65 : List (BitVec 32) := [7340819,610556515]
def seg_67 : List (BitVec 32) := [2451]
def seg_68 : List (BitVec 32) := [3146515,74045539]
def seg_70 : List (BitVec 32) := [1316627,8849203,20383539,4660755,32439,17731219,31329843,5707411,4658963,15107763,7863,2249100947,30836403,930563,9319299,6729763,7779363,1673619,4213174383]
def seg_89 : List (BitVec 32) := [4462355,3415571,29820723,134711,1242435091,29820723,472451,7722387,7341331,898629871]
def seg_99 : List (BitVec 32) := [2451]
def seg_100 : List (BitVec 32) := [4195091,376035427]
def seg_102 : List (BitVec 32) := [120587027,1047090787]
def seg_104 : List (BitVec 32) := [4789907,32311,370019859,29787827,1640723,4462355,3415571,29820723,134711,1242435091,29820723,472835,7821075,20405811,1998355,101581411]
def seg_120 : List (BitVec 32) := [134967,537857811,439043,8827779,7286819,8336419,134839,604933779,134967,588189459,963331,9352067,7286819,8336419,7052819,4955923,32378419,23989811,439043,8827779,7222307,8271907,1805203,100663407]
def seg_144 : List (BitVec 32) := [134839,604933779,134967,537857811,963331,9352067,7286819,8336419,134967,588189459,439043,8827779,7286819,8336419,7052819,4955923,32378419,23989811,439043,8827779,40778787,75378723,1805203]
def seg_167 : List (BitVec 32) := [3149331,1094585907,1050259,29791923,1674771,29842995,29787827,4919,2685600531,17047315,31679283,1980760175]
def seg_179 : List (BitVec 32) := [33857299,31679283,134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
def seg_190 : List (BitVec 32) := [115]
def seg_191 : List (BitVec 32) := [1673619,3911184495]
def seg_193 : List (BitVec 32) := [6037011,25062963,30081059,7052819,4955923,32378419,30083891,9112339,4464147,263267]
def seg_203 : List (BitVec 32) := [17698323]
def seg_204 : List (BitVec 32) := [134839,839814803,31329843,134839,604933779,963331,9352067,7221283,8270883,1311763,3672109167]
def seg_215 : List (BitVec 32) := [591507]
def seg_216 : List (BitVec 32) := [120587027,40293987]
def seg_218 : List (BitVec 32) := [4627987,32439,370052755,31329843,930563,537073251]
def seg_224 : List (BitVec 32) := [9319171,537072227]
def seg_226 : List (BitVec 32) := [1476243,4250923119]
def seg_228 : List (BitVec 32) := [4919,2954035987,295827,134711,839781907,7223331,8272931,132407,839189779,134219155,132663,973473299]
def seg_240 : List (BitVec 32) := [115]
def seg_241 : List (BitVec 32) := [134839,974032531,134967,638521107,963331,9352067,7286819,8336419]
def seg_249 : List (BitVec 32) := [3146771,6293395,45092115,3475,211814547,134711,1426984467,930563,218003,66063891,29620531,6509715,822083823]
def seg_262 : List (BitVec 32) := [7735,2181959187,20848675,34871,772278291,27575,411798419,23607,1821117459,898629871]
def seg_272 : List (BitVec 32) := [2098195,6293395,45092115,3475,211814547,134711,1426984467,930563,6509459,66063891,29620531,12801171,725614831]
def seg_285 : List (BitVec 32) := [24119,1519259155,20848675,34871,4245162003,23479,1418431379,23607,2827750419,802160879]
def seg_295 : List (BitVec 32) := [1049619,7341971,45092115,3475,210765971,134711,1426984467,930563,12800915,133172755,29620531,20141203,629145839]
def seg_308 : List (BitVec 32) := [24119,2525892115,20848675,34871,3406301203,23479,2425064339,19511,3834383379,705691887]
def seg_318 : List (BitVec 32) := [1043,12584851,56626451,53480851,152045715,134711,1426984467,930563,20140947,7735,4294839827,29620531,32724115,528482543]
def seg_332 : List (BitVec 32) := [20023,3465416211,20848675,34871,2299004947,19383,3364588435,15415,4035709971,605028591]
def seg_342 : List (BitVec 32) := [1967296623,638455315,167775891,930563,963459,7544419]
def seg_348 : List (BitVec 32) := [9319171,9352067,7542883]
def seg_351 : List (BitVec 32) := [1297248367,1299]
def seg_353 : List (BitVec 32) := [115]
def seg_824 : List (BitVec 32) := [4244701459,1126435,10564643,11614243,4462355,3415571,29820723,134711,1242435091,29820723,2579]
def seg_835 : List (BitVec 32) := [3808787,15601203,933507,11460403,79627875]
def seg_840 : List (BitVec 32) := [1706515,3149331,4291433187]
def seg_843 : List (BitVec 32) := [120589843,2244566243]
def seg_845 : List (BitVec 32) := [4791827,32439,370052755,31329843,134967,604966675,930563,9319299,7286819,8336419,1640723,1299,574619759]
def seg_858 : List (BitVec 32) := [168106083]
def seg_859 : List (BitVec 32) := [34210403]
def seg_860 : List (BitVec 32) := [6037011,25062963,30081059,7052819,4955923,32378419,30083891,9112339]
def seg_868 : List (BitVec 32) := [2963,2030611,1316627,8849203,21432115,4658963,32311,17698323,29820723,134967,772738835,471811,8860547,7286819,8336419,4919,2417165075,17047315,31679283,1388314735]
def seg_888 : List (BitVec 32) := [33857299,31679283,134711,739118611,7223331,8272931,132407,738526483,67110291,132663,604374547]
def seg_899 : List (BitVec 32) := [115]
def seg_900 : List (BitVec 32) := [1049875,390070383]
def seg_902 : List (BitVec 32) := [4294247699,1414547,3961516271]
def seg_905 : List (BitVec 32) := [10566691,134839,604933779,963331,9352067,39923747,40973347,8467715,16856451,4294247699,1414547,1410451,3906990319]
def seg_918 : List (BitVec 32) := [134967,537857811,33633027,42021763,7286819,8336419,134839,604933779,134967,588189459,963331,9352067,7286819,8336419,8470019,11536019,1103529651,1052179,14554803,16858627,29787827,4919,2685600531,17047315,31679283,1035993199]
def seg_944 : List (BitVec 32) := [33857299,31679283,134711,537792019,7223331,8272931,25247235,34477667]
def seg_952 : List (BitVec 32) := [7052819,4955923,32378419,23989811,33633027,42021763,7222307,8271907,1805203,109052015]
def seg_962 : List (BitVec 32) := [33888867]
def seg_963 : List (BitVec 32) := [7052819,4955923,32378419,23989811,134839,604933779,963331,9352067,40778787,75378723,1805203,54526063]
def seg_975 : List (BitVec 32) := [6037011,25062963,17722899,30081059,7052819,4955923,32378419,30083891,9112339,2963,16858627,1997843]
def seg_987 : List (BitVec 32) := [132407,537199891,67110291,132663,604374547]
def seg_992 : List (BitVec 32) := [115]
def seg_993 : List (BitVec 32) := [1049875]
def seg_994 : List (BitVec 32) := [77955,50397459,32871]
def seg_997 : List (BitVec 32) := [1142063215,19,19,19,19,19,19,19,19,19,19,19,2451]
def seg_1010 : List (BitVec 32) := [229235299]
def seg_1011 : List (BitVec 32) := [4824595,17698355,134967,487526163,930563,9319299,7286819,8336419,930563,9319299,40613923,41663523,4228615059,134711,1108217363,20844083]
def seg_1027 : List (BitVec 32) := [936451]
def seg_1028 : List (BitVec 32) := [7342739,267363]
def seg_1030 : List (BitVec 32) := [536871023]
def seg_1031 : List (BitVec 32) := [89805923]
def seg_1032 : List (BitVec 32) := [901775471,21201843,33788691,17047315,31679283,269706003,134711,437128723,7223331,132407,436536595,67110291,132663,486934035]
def seg_1046 : List (BitVec 32) := [115]
def seg_1047 : List (BitVec 32) := [1706515,4225757295]
def seg_1049 : List (BitVec 32) := [995262575,19]
def seg_1051 : List (BitVec 32) := [19]
def seg_1052 : List (BitVec 32) := [134839,1611566739,31329843,134839,487493267,963331,9352067,7221283,8270883,1673619,4078956655]
def seg_1063 : List (BitVec 32) := [1901331,4395795,66257683,4228084499,132407,1610941715,198035,132663,604374547]
def seg_1072 : List (BitVec 32) := [115]
def seg_1073 : List (BitVec 32) := [2579,5053971,29887283]
def seg_1076 : List (BitVec 32) := [284841571]
def seg_1077 : List (BitVec 32) := [21585459,1998355,68028515]
def seg_1080 : List (BitVec 32) := [733955,9122691,7090211,8139811,134967,537857811,733955,9122691,7286819,8336419,134839,604933779,134967,588189459,963331,9352067,7286819,8336419,79691887]
def seg_1099 : List (BitVec 32) := [733955,9122691,40646691,41696291,134839,604933779,134967,537857811,963331,9352067,7286819,8336419,134967,588189459,733955,9122691,7286819,8336419]
def seg_1117 : List (BitVec 32) := [1402101871,4294839827,1050259,29791923,1707539,29974067,29787827,710049903,19,19,19,19,134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
def seg_1138 : List (BitVec 32) := [115]
def seg_1139 : List (BitVec 32) := [17500947,4228647955,1706515,4020236399]
def seg_1143 : List (BitVec 32) := [134839,604933779,134967,638521107,963331,9352067,7286819,8336419,32871]
def seg_1152 : List (BitVec 32) := [131895,394474243,14897939,7566099,3489863267,3088052335]
def seg_1158 : List (BitVec 32) := [7342739,3787051235]
def seg_1160 : List (BitVec 32) := [4197011,3751800943]
def seg_1162 : List (BitVec 32) := [426899,267648787,9379603,8639379,31712179,7735,4043181587,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,1432227347,29622067,2039571,1299347,29619123,31712179,50566035,2207248495]
def seg_1190 : List (BitVec 32) := [426899,267648787,9379603,8639379,31712179,7735,4043181587,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,1432227347,29622067,2039571,1299347,29619123,31712179,50566035,3152015471]
def seg_1218 : List (BitVec 32) := [1074693011,1073972115,267648787,9379603,8639379,31712179,7735,4043181587,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,1432227347,29622067,2039571,1299347,29619123,31712179,50566035,2795499631]
def expL : Rv.Layout := [(0, seg_0), (30, layoutCode (Search.dsL 30)), (49, seg_49), (65, seg_65), (67, seg_67), (68, seg_68), (70, seg_70), (89, seg_89), (99, seg_99), (100, seg_100), (102, seg_102), (104, seg_104), (120, seg_120), (144, seg_144), (167, seg_167), (179, seg_179), (190, seg_190), (191, seg_191), (193, seg_193), (203, seg_203), (204, seg_204), (215, seg_215), (216, seg_216), (218, seg_218), (224, seg_224), (226, seg_226), (228, seg_228), (240, seg_240), (241, seg_241), (249, seg_249), (262, seg_262), (272, seg_272), (285, seg_285), (295, seg_295), (308, seg_308), (318, seg_318), (332, seg_332), (342, seg_342), (348, seg_348), (351, seg_351), (353, seg_353), (354, Search.kernCode 354), (824, seg_824), (835, seg_835), (840, seg_840), (843, seg_843), (845, seg_845), (858, seg_858), (859, seg_859), (860, seg_860), (868, seg_868), (888, seg_888), (899, seg_899), (900, seg_900), (902, seg_902), (905, seg_905), (918, seg_918), (944, seg_944), (952, seg_952), (962, seg_962), (963, seg_963), (975, seg_975), (987, seg_987), (992, seg_992), (993, seg_993), (994, seg_994), (997, seg_997), (1010, seg_1010), (1011, seg_1011), (1027, seg_1027), (1028, seg_1028), (1030, seg_1030), (1031, seg_1031), (1032, seg_1032), (1046, seg_1046), (1047, seg_1047), (1049, seg_1049), (1051, seg_1051), (1052, seg_1052), (1063, seg_1063), (1072, seg_1072), (1073, seg_1073), (1076, seg_1076), (1077, seg_1077), (1080, seg_1080), (1099, seg_1099), (1117, seg_1117), (1138, seg_1138), (1139, seg_1139), (1143, seg_1143), (1152, seg_1152), (1158, seg_1158), (1160, seg_1160), (1162, seg_1162), (1190, seg_1190), (1218, seg_1218), (1247, [0x00c00393, 0x00040a63, 0x00100393, 0x00740463, 0x00000393, 0x00638393, 0x00749333, 0x01230333, 0x00020e37, 0x1a0e0e13, 0x02035393, 0x007e3c23, 0x02031313, 0x01035313, 0x03041393, 0x00736333, 0x0c100f13, 0x038f1f13, 0x01e36333, 0x0ffa7393, 0x00839393, 0x00736333, 0x0809e393, 0x00736333, 0xc5dff06f])]
theorem expL_ok : layoutOk 0 expL = true := by decide +kernel
abbrev image : Image := Images.expandReferenceImage
/-- The entry instruction is supplied by the compact-layout prologue. -/
theorem codeAt_49 : CodeAt image (pcOf 49) seg_49 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_65 : CodeAt image (pcOf 65) seg_65 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_67 : CodeAt image (pcOf 67) seg_67 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_68 : CodeAt image (pcOf 68) seg_68 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_70 : CodeAt image (pcOf 70) seg_70 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_89 : CodeAt image (pcOf 89) seg_89 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_99 : CodeAt image (pcOf 99) seg_99 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_100 : CodeAt image (pcOf 100) seg_100 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_102 : CodeAt image (pcOf 102) seg_102 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_104 : CodeAt image (pcOf 104) seg_104 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_120 : CodeAt image (pcOf 120) seg_120 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_144 : CodeAt image (pcOf 144) seg_144 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_167 : CodeAt image (pcOf 167) seg_167 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_179 : CodeAt image (pcOf 179) seg_179 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_190 : CodeAt image (pcOf 190) seg_190 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_191 : CodeAt image (pcOf 191) seg_191 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_193 : CodeAt image (pcOf 193) seg_193 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_203 : CodeAt image (pcOf 203) seg_203 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_204 : CodeAt image (pcOf 204) seg_204 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_215 : CodeAt image (pcOf 215) seg_215 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_216 : CodeAt image (pcOf 216) seg_216 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_218 : CodeAt image (pcOf 218) seg_218 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_224 : CodeAt image (pcOf 224) seg_224 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_226 : CodeAt image (pcOf 226) seg_226 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_228 : CodeAt image (pcOf 228) seg_228 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_240 : CodeAt image (pcOf 240) seg_240 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_241 : CodeAt image (pcOf 241) seg_241 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_249 : CodeAt image (pcOf 249) seg_249 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_262 : CodeAt image (pcOf 262) seg_262 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_272 : CodeAt image (pcOf 272) seg_272 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_285 : CodeAt image (pcOf 285) seg_285 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_295 : CodeAt image (pcOf 295) seg_295 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_308 : CodeAt image (pcOf 308) seg_308 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_318 : CodeAt image (pcOf 318) seg_318 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_332 : CodeAt image (pcOf 332) seg_332 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_342 : CodeAt image (pcOf 342) seg_342 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_348 : CodeAt image (pcOf 348) seg_348 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_351 : CodeAt image (pcOf 351) seg_351 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_353 : CodeAt image (pcOf 353) seg_353 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_824 : CodeAt image (pcOf 824) seg_824 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_835 : CodeAt image (pcOf 835) seg_835 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_840 : CodeAt image (pcOf 840) seg_840 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_843 : CodeAt image (pcOf 843) seg_843 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_845 : CodeAt image (pcOf 845) seg_845 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_858 : CodeAt image (pcOf 858) seg_858 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_859 : CodeAt image (pcOf 859) seg_859 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_860 : CodeAt image (pcOf 860) seg_860 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_868 : CodeAt image (pcOf 868) seg_868 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_888 : CodeAt image (pcOf 888) seg_888 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_899 : CodeAt image (pcOf 899) seg_899 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_900 : CodeAt image (pcOf 900) seg_900 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_902 : CodeAt image (pcOf 902) seg_902 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_905 : CodeAt image (pcOf 905) seg_905 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_918 : CodeAt image (pcOf 918) seg_918 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_944 : CodeAt image (pcOf 944) seg_944 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_952 : CodeAt image (pcOf 952) seg_952 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_962 : CodeAt image (pcOf 962) seg_962 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_963 : CodeAt image (pcOf 963) seg_963 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_975 : CodeAt image (pcOf 975) seg_975 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_987 : CodeAt image (pcOf 987) seg_987 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_992 : CodeAt image (pcOf 992) seg_992 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_993 : CodeAt image (pcOf 993) seg_993 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_994 : CodeAt image (pcOf 994) seg_994 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_997 : CodeAt image (pcOf 997) seg_997 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1010 : CodeAt image (pcOf 1010) seg_1010 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1011 : CodeAt image (pcOf 1011) seg_1011 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1027 : CodeAt image (pcOf 1027) seg_1027 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1028 : CodeAt image (pcOf 1028) seg_1028 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1030 : CodeAt image (pcOf 1030) seg_1030 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1031 : CodeAt image (pcOf 1031) seg_1031 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1032 : CodeAt image (pcOf 1032) seg_1032 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1046 : CodeAt image (pcOf 1046) seg_1046 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1047 : CodeAt image (pcOf 1047) seg_1047 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1049 : CodeAt image (pcOf 1049) seg_1049 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1051 : CodeAt image (pcOf 1051) seg_1051 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1052 : CodeAt image (pcOf 1052) seg_1052 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1063 : CodeAt image (pcOf 1063) seg_1063 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1072 : CodeAt image (pcOf 1072) seg_1072 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1073 : CodeAt image (pcOf 1073) seg_1073 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1076 : CodeAt image (pcOf 1076) seg_1076 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1077 : CodeAt image (pcOf 1077) seg_1077 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1080 : CodeAt image (pcOf 1080) seg_1080 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1099 : CodeAt image (pcOf 1099) seg_1099 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1138 : CodeAt image (pcOf 1138) seg_1138 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1139 : CodeAt image (pcOf 1139) seg_1139 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1143 : CodeAt image (pcOf 1143) seg_1143 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1158 : CodeAt image (pcOf 1158) seg_1158 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1160 : CodeAt image (pcOf 1160) seg_1160 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1162 : CodeAt image (pcOf 1162) seg_1162 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1190 : CodeAt image (pcOf 1190) seg_1190 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem codeAt_1218 : CodeAt image (pcOf 1218) seg_1218 :=
  codeAt_expand_chunk (by decide +kernel) (by decide +kernel) (by decide +kernel)
sym_block eblk_49 := symRun { noAlias := true } seg_49 (pcOf 49) 200
sym_block eblk_65 := symRun { noAlias := true } seg_65 (pcOf 65) 200
sym_block eblk_67 := symRun { noAlias := true } seg_67 (pcOf 67) 200
sym_block eblk_68 := symRun { noAlias := true } seg_68 (pcOf 68) 200
sym_block eblk_70 := symRun { noAlias := true } seg_70 (pcOf 70) 200
sym_block eblk_89 := symRun { noAlias := true } seg_89 (pcOf 89) 200
sym_block eblk_99 := symRun { noAlias := true } seg_99 (pcOf 99) 200
sym_block eblk_100 := symRun { noAlias := true } seg_100 (pcOf 100) 200
sym_block eblk_102 := symRun { noAlias := true } seg_102 (pcOf 102) 200
sym_block eblk_104 := symRun { noAlias := true } seg_104 (pcOf 104) 200
sym_block eblk_120 := symRun { noAlias := true } seg_120 (pcOf 120) 200
sym_block eblk_144 := symRun { noAlias := true } seg_144 (pcOf 144) 200
sym_block eblk_167 := symRun { noAlias := true } seg_167 (pcOf 167) 200
sym_block eblk_179 := symRun { noAlias := true } seg_179 (pcOf 179) 200
sym_block eblk_191 := symRun { noAlias := true } seg_191 (pcOf 191) 200
sym_block eblk_193 := symRun { noAlias := true } seg_193 (pcOf 193) 200
sym_block eblk_203 := symRun { noAlias := true } seg_203 (pcOf 203) 200
sym_block eblk_204 := symRun { noAlias := true } seg_204 (pcOf 204) 200
sym_block eblk_215 := symRun { noAlias := true } seg_215 (pcOf 215) 200
sym_block eblk_216 := symRun { noAlias := true } seg_216 (pcOf 216) 200
sym_block eblk_218 := symRun { noAlias := true } seg_218 (pcOf 218) 200
sym_block eblk_224 := symRun { noAlias := true } seg_224 (pcOf 224) 200
sym_block eblk_226 := symRun { noAlias := true } seg_226 (pcOf 226) 200
sym_block eblk_228 := symRun { noAlias := true } seg_228 (pcOf 228) 200
sym_block eblk_241 := symRun { noAlias := true } seg_241 (pcOf 241) 200
sym_block eblk_249 := symRun { noAlias := true } seg_249 (pcOf 249) 200
sym_block eblk_262 := symRun { noAlias := true } seg_262 (pcOf 262) 200
sym_block eblk_272 := symRun { noAlias := true } seg_272 (pcOf 272) 200
sym_block eblk_285 := symRun { noAlias := true } seg_285 (pcOf 285) 200
sym_block eblk_295 := symRun { noAlias := true } seg_295 (pcOf 295) 200
sym_block eblk_308 := symRun { noAlias := true } seg_308 (pcOf 308) 200
sym_block eblk_318 := symRun { noAlias := true } seg_318 (pcOf 318) 200
sym_block eblk_332 := symRun { noAlias := true } seg_332 (pcOf 332) 200
sym_block eblk_348 := symRun { noAlias := true } seg_348 (pcOf 348) 200
sym_block eblk_351 := symRun { noAlias := true } seg_351 (pcOf 351) 200
sym_block eblk_824 := symRun { noAlias := true } seg_824 (pcOf 824) 200
sym_block eblk_835 := symRun { noAlias := true } seg_835 (pcOf 835) 200
sym_block eblk_840 := symRun { noAlias := true } seg_840 (pcOf 840) 200
sym_block eblk_843 := symRun { noAlias := true } seg_843 (pcOf 843) 200
sym_block eblk_845 := symRun { noAlias := true } seg_845 (pcOf 845) 200
sym_block eblk_858 := symRun { noAlias := true } seg_858 (pcOf 858) 200
sym_block eblk_859 := symRun { noAlias := true } seg_859 (pcOf 859) 200
sym_block eblk_860 := symRun { noAlias := true } seg_860 (pcOf 860) 200
sym_block eblk_868 := symRun { noAlias := true } seg_868 (pcOf 868) 200
sym_block eblk_888 := symRun { noAlias := true } seg_888 (pcOf 888) 200
sym_block eblk_900 := symRun { noAlias := true } seg_900 (pcOf 900) 200
sym_block eblk_902 := symRun { noAlias := true } seg_902 (pcOf 902) 200
sym_block eblk_905 := symRun { noAlias := true } seg_905 (pcOf 905) 200
sym_block eblk_918 := symRun { noAlias := true } seg_918 (pcOf 918) 200
sym_block eblk_944 := symRun { noAlias := true } seg_944 (pcOf 944) 200
sym_block eblk_952 := symRun { noAlias := true } seg_952 (pcOf 952) 200
sym_block eblk_962 := symRun { noAlias := true } seg_962 (pcOf 962) 200
sym_block eblk_963 := symRun { noAlias := true } seg_963 (pcOf 963) 200
sym_block eblk_975 := symRun { noAlias := true } seg_975 (pcOf 975) 200
sym_block eblk_987 := symRun { noAlias := true } seg_987 (pcOf 987) 200
sym_block eblk_993 := symRun { noAlias := true } seg_993 (pcOf 993) 200
sym_block eblk_994 := symRun { noAlias := true } seg_994 (pcOf 994) 200
sym_block eblk_997 := symRun { noAlias := true } seg_997 (pcOf 997) 200
sym_block eblk_1010 := symRun { noAlias := true } seg_1010 (pcOf 1010) 200
sym_block eblk_1011 := symRun { noAlias := true } seg_1011 (pcOf 1011) 200
sym_block eblk_1027 := symRun { noAlias := true } seg_1027 (pcOf 1027) 200
sym_block eblk_1028 := symRun { noAlias := true } seg_1028 (pcOf 1028) 200
sym_block eblk_1030 := symRun { noAlias := true } seg_1030 (pcOf 1030) 200
sym_block eblk_1031 := symRun { noAlias := true } seg_1031 (pcOf 1031) 200
sym_block eblk_1032 := symRun { noAlias := true } seg_1032 (pcOf 1032) 200
sym_block eblk_1047 := symRun { noAlias := true } seg_1047 (pcOf 1047) 200
sym_block eblk_1049 := symRun { noAlias := true } seg_1049 (pcOf 1049) 200
sym_block eblk_1051 := symRun { noAlias := true } seg_1051 (pcOf 1051) 200
sym_block eblk_1052 := symRun { noAlias := true } seg_1052 (pcOf 1052) 200
sym_block eblk_1063 := symRun { noAlias := true } seg_1063 (pcOf 1063) 200
sym_block eblk_1073 := symRun { noAlias := true } seg_1073 (pcOf 1073) 200
sym_block eblk_1076 := symRun { noAlias := true } seg_1076 (pcOf 1076) 200
sym_block eblk_1077 := symRun { noAlias := true } seg_1077 (pcOf 1077) 200
sym_block eblk_1080 := symRun { noAlias := true } seg_1080 (pcOf 1080) 200
sym_block eblk_1099 := symRun { noAlias := true } seg_1099 (pcOf 1099) 200
sym_block eblk_1117 := symRun { noAlias := true } seg_1117 (pcOf 1117) 200
sym_block eblk_1139 := symRun { noAlias := true } seg_1139 (pcOf 1139) 200
sym_block eblk_1143 := symRun { noAlias := true } seg_1143 (pcOf 1143) 200
sym_block eblk_1158 := symRun { noAlias := true } seg_1158 (pcOf 1158) 200
sym_block eblk_1160 := symRun { noAlias := true } seg_1160 (pcOf 1160) 200
sym_block eblk_1162 := symRun { noAlias := true } seg_1162 (pcOf 1162) 200
sym_block eblk_1190 := symRun { noAlias := true } seg_1190 (pcOf 1190) 200
sym_block eblk_1218 := symRun { noAlias := true } seg_1218 (pcOf 1218) 200
end SigGolfCandidate.T3M.Expand
end


-- Check the large outer chunk lists sequentially with their required recursion depth.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

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
    let driverPrefix := expandSharedLowTail ++ List.replicate 863 (0x13 : BitVec 32) ++
      expandSharedDriver ++ List.replicate 148571 (0x13 : BitVec 32)
    have hp : driverPrefix.length = 151552 := by
      change (expandSharedLowTail ++ List.replicate 863 (0x13 : BitVec 32) ++ expandSharedDriver ++ List.replicate 148571 (0x13 : BitVec 32)).length = _
      simp only [List.length_append, List.length_replicate]
      decide +kernel
    change (driverPrefix ++ expandSharedBanks).drop 151552 = _
    rw [← hp, List.drop_left]
  rw [he, hv, ← hpre, List.drop_left]
  rw [← hbank, List.take_left, List.take_length]
end SigGolfCandidate.T3M.Images

namespace SigGolfCandidate.T3M.Expand
open SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
/-- All verifier instruction certificates inside the shared FTS bank transport
unchanged into the installed expansion image. -/
theorem codeAt_shared_bank {base : Nat} {words : List (BitVec 32)}
    (hlo : 195584 ≤ base) (hhi : base + words.length ≤ 254656)
    (hc : CodeAt Images.verifyImage (pcOf base) words) :
    CodeAt Images.expandImage (pcOf base) words := by
  exact codeAt_of_window_eq (source := Images.verifyImage) (target := Images.expandImage)
    (start := 195584) (count := 59072) hlo hhi (by decide : 4096+4*(195584+59072)<2^64)
    Images.expand_banks_eq_verify.symm hc
end SigGolfCandidate.T3M.Expand
