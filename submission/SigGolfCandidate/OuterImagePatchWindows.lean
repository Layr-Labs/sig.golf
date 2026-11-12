import SigGolfCandidate.OuterImageSignWindows
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImagePatchWindows
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterImages

theorem slice {im : Image} {a : Nat} {code : List (BitVec 32)} (ha : a<2^40)
    (hc : CodeAt im (pcOf a) code) : (im.code.drop a).take code.length=code := by
  have hs:=hc.2.2.2
  have hp : (pcOf a).toNat=4096+4*a := by
    simp only [pcOf,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp,show (4096+4*a-4096)/4=a from by omega] at hs
  exact (List.prefix_iff_eq_take.mp hs).symm

theorem sign_window (a n : Nat) (hb : a+n≤26156) :
    (signCode.drop a).take n=((Images.signCode.drop a).take n).mapIdx (fun i w=>signPatch (a+i) w) := by
  rw [OuterImageSignWindows.prefix_window a n hb]
  apply List.ext_getElem
  · simp only [List.length_mapIdx,List.length_take,List.length_drop]
  · intro i h1 h2
    simp only [List.getElem_take,List.getElem_drop,List.getElem_mapIdx]

theorem expand_window (a n : Nat) (hb : a+n≤235776) :
    (expandCode.drop a).take n=((Images.expandCode.drop a).take n).mapIdx (fun i w=>expandPatch (a+i) w) := by
  rw [OuterImageWindows.prefix_window a n hb]
  apply List.ext_getElem
  · simp only [expandPrefix,List.length_mapIdx,List.length_take,List.length_drop,Images.expandCode_length]
    omega
  · intro i h1 h2
    simp only [expandPrefix,List.getElem_take,List.getElem_drop,List.getElem_mapIdx]

#print axioms sign_window
#print axioms expand_window
end OuterImagePatchWindows
