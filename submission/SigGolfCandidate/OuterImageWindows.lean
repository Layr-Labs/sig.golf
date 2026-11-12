import SigGolfCandidate.OuterImageBanks
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImageWindows
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterImages

theorem prefix_window (a n : Nat) (hb : a+n ≤ 235776) :
    (expandCode.drop a).take n=(expandPrefix.drop a).take n := by
  rw [List.take_drop,expandCode,List.append_assoc,List.append_assoc,
    List.take_append_of_le_length (by rw [prefix_length];omega),←List.take_drop]

theorem unchanged_window (a n : Nat) (hb : a+n ≤ 235776)
    (hc : ∀ i,a ≤ i → i < a+n → ∀ w,expandPatch i w=w) :
    (expandCode.drop a).take n=(Images.expandCode.drop a).take n := by
  rw [prefix_window a n hb]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,prefix_length,Images.expandCode_length]
    omega
  · intro i h1 h2
    have hn : i < n := by
      have H:=h1
      simp only [List.length_take] at H
      omega
    simp only [expandPrefix,List.getElem_take,List.getElem_drop,List.getElem_mapIdx]
    exact hc (a+i) (by omega) (by omega) _

theorem high_patch (i : Nat) (hi : 88339 ≤ i) (w : BitVec 32) : expandPatch i w=w := by
  unfold expandPatch
  split_ifs <;> try omega
  rfl

theorem high_window (a n : Nat) (ha : 88339 ≤ a) (hb : a+n ≤ 235776) :
    (expandCode.drop a).take n=(Images.expandCode.drop a).take n :=
  unchanged_window a n hb (fun i hi _ w=>high_patch i (by omega) w)

theorem high_word (p : Nat) (ha : 88339 ≤ p) (hb : p < 235776) :
    expandImage.code[p]?=Images.expandImage.code[p]? := by
  have h:=high_window p 1 ha (by omega)
  have h0:=congrArg (fun xs : List (BitVec 32)=>xs[0]?) h
  simpa only [expandImage,Images.expandImage,List.getElem?_take,show 0<1 from by decide,↓reduceIte,List.getElem?_drop,Nat.add_zero] using h0

#print axioms high_window
end OuterImageWindows
