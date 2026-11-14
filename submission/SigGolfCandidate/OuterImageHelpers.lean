import SigGolfCandidate.OuterImageWindows
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImageHelpers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterImages

theorem sign_helper : CodeAt signImage (pcOf 26156) OuterSignImageLayout.code := by
  apply CodeAt.of_append (pre:=(Images.signCode.take 26156).mapIdx signPatch) (post:=OuterCodecMachine.packCode++[0x73]++Images.signCode.drop 26241)
    (by simp [signImage,signCode,List.append_assoc])
  · simp only [List.length_mapIdx,List.length_take,Images.signCode_length,pcOf]
    decide +kernel
  · simp only [List.length_mapIdx,List.length_take,Images.signCode_length]
    decide +kernel

theorem sign_pack : CodeAt signImage (pcOf 26207) OuterCodecMachine.packCode := by
  apply CodeAt.of_append (pre:=(Images.signCode.take 26156).mapIdx signPatch++OuterSignImageLayout.code) (post:=[0x73]++Images.signCode.drop 26241)
    (by simp [signImage,signCode,List.append_assoc])
  · simp only [List.length_append,List.length_mapIdx,List.length_take,Images.signCode_length,pcOf]
    decide +kernel
  · simp only [List.length_append,List.length_mapIdx,List.length_take,Images.signCode_length]
    decide +kernel

theorem expand_chunk (a : Nat) (code : List (BitVec 32)) (hb : a+code.length≤235776)
    (hc : ∀ (i : Nat) (hi : i<code.length) (w : BitVec 32),expandPatch (a+i) w=code[i]) :
    CodeAt expandImage (pcOf a) code := by
  apply codeAt_slice (by omega)
  change (expandCode.drop a).take code.length=code
  rw [OuterImageWindows.prefix_window a code.length hb]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,prefix_length]
    omega
  · intro i h1 h2
    simp only [expandPrefix,List.getElem_take,List.getElem_drop,List.getElem_mapIdx]
    exact hc i h2 _

theorem expand_post : CodeAt expandImage (pcOf 88260) OuterNoncePostMachine.postCode := by
  apply expand_chunk _ _ (by decide +kernel)
  intro i hi w
  have hn : OuterNoncePostMachine.postCode.length=20 := by decide +kernel
  have hii : i<20 := by omega
  simp only [expandPatch,if_neg (by omega : 88260+i≠0),if_neg (by omega : 88260+i≠54334),
    if_neg (by omega : 88260+i≠84218),if_pos (by omega : 88260≤88260+i ∧ 88260+i<88280),Nat.add_sub_cancel_left]
  exact List.getD_eq_getElem _ _ hi

theorem expand_unpack : CodeAt expandImage (pcOf 88300) OuterCodecMachine.unpackCode := by
  apply expand_chunk _ _ (by decide +kernel)
  intro i hi w
  have hn : OuterCodecMachine.unpackCode.length=38 := by decide +kernel
  have hii : i<38 := by omega
  simp only [expandPatch,if_neg (by omega : 88300+i≠0),if_neg (by omega : 88300+i≠54334),
    if_neg (by omega : 88300+i≠84218),if_neg (by omega : ¬(88260≤88300+i ∧ 88300+i<88280)),
    if_neg (by omega : 88300+i≠88280),if_pos (by omega : 88300≤88300+i ∧ 88300+i<88338),Nat.add_sub_cancel_left]
  exact List.getD_eq_getElem _ _ hi

#print axioms sign_helper
#print axioms sign_pack
#print axioms expand_post
#print axioms expand_unpack
end OuterImageHelpers
