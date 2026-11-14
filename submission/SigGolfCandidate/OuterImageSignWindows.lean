import SigGolfCandidate.OuterImageHelpers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImageSignWindows
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterImages

theorem prefix_window (a n : Nat) (hb : a+n≤26156) :
    (signCode.drop a).take n=((Images.signCode.mapIdx signPatch).drop a).take n := by
  rw [List.take_drop,signCode,List.append_assoc,List.append_assoc,List.append_assoc,
    List.take_append_of_le_length (by simp only [List.length_mapIdx,List.length_take,Images.signCode_length];omega)]
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_take,List.length_mapIdx,Images.signCode_length]
    omega
  · intro i h1 h2
    simp only [List.getElem_drop,List.getElem_take,List.getElem_mapIdx]

theorem unchanged_window (a n : Nat) (hb : a+n≤26156)
    (hc : ∀ i,a ≤ i → i<a+n → ∀ w,signPatch i w=w) :
    (signCode.drop a).take n=(Images.signCode.drop a).take n := by
  rw [prefix_window a n hb]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_mapIdx]
  · intro i h1 h2
    have hn : i<n := by have H:=h1;simp only [List.length_take] at H;omega
    simp only [List.getElem_take,List.getElem_drop,List.getElem_mapIdx]
    exact hc (a+i) (by omega) (by omega) _

theorem chunk (a : Nat) (code : List (BitVec 32)) (hb : a+code.length≤26156)
    (hc : ∀ (i : Nat) (hi : i<code.length) (w : BitVec 32),signPatch (a+i) w=code[i]) :
    CodeAt signImage (pcOf a) code := by
  apply codeAt_slice (by omega)
  change (signCode.drop a).take code.length=code
  rw [prefix_window a code.length hb]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_mapIdx,Images.signCode_length]
    omega
  · intro i h1 h2
    simp only [List.getElem_take,List.getElem_drop,List.getElem_mapIdx]
    exact hc i h2 _

theorem sign_jump : CodeAt signImage (pcOf 25338) [jump 25338 26156] := by
  apply chunk _ _ (by decide)
  intro i hi w
  have he : i=0 := by simp only [List.length_singleton] at hi;omega
  subst i
  simp only [Nat.add_zero,signPatch,show ¬25338=1977 from by decide,show 25338=25338 from rfl,if_false,if_true,List.getElem_cons_zero]

theorem pack_jump : CodeAt signImage (pcOf 25963) [jump 25963 26207] := by
  apply chunk _ _ (by decide)
  intro i hi w
  have he : i=0 := by simp only [List.length_singleton] at hi;omega
  subst i
  simp only [Nat.add_zero,signPatch,show ¬25963=1977 from by decide,show ¬25963=25338 from by decide,show 25963=25963 from rfl,if_false,if_true,List.getElem_cons_zero]

#print axioms sign_jump
#print axioms pack_jump
end OuterImageSignWindows
