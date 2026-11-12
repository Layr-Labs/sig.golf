import SigGolfCandidate.OuterImageBankA
set_option debug.skipKernelTC false
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImageCopies
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind W9Machine W9Drv OuterImages

theorem mid_window : (expandCode.drop 54335).take 29883=(Images.expandCode.drop 54335).take 29883 := by
  apply OuterImageWindows.unchanged_window 54335 29883 (by decide)
  intro i ha hb w
  unfold expandPatch
  split_ifs <;> try omega
  rfl

theorem late_window : (expandCode.drop 84219).take 4041=(Images.expandCode.drop 84219).take 4041 := by
  apply OuterImageWindows.unchanged_window 84219 4041 (by decide)
  intro i ha hb w
  unfold expandPatch
  split_ifs <;> try omega
  rfl

theorem mid_word (p : Nat) (ha : 54335≤p) (hb : p<84218) :
    expandImage.code[p]?=Images.expandImage.code[p]? := by
  have h:=image_slice_of_window (source:=expandImage) (target:=Images.expandImage) (start:=54335) (count:=29883) (base:=p) (len:=1) ha (by omega) mid_window
  have h0:=congrArg (fun xs : List (BitVec 32)=>xs[0]?) h
  simpa only [expandImage,Images.expandImage,List.getElem?_take,show 0<1 from by decide,↓reduceIte,List.getElem?_drop,Nat.add_zero] using h0

theorem mid_code {b : Nat} {code : List (BitVec 32)} (ha : 54335≤b) (hb : b+code.length≤84218)
    (hc : CodeAt Images.expandImage (pcOf b) code) : CodeAt expandImage (pcOf b) code :=
  codeAt_of_window_eq (source:=Images.expandImage) (target:=expandImage) (start:=54335) (count:=29883) ha hb (by decide) mid_window.symm hc

theorem late_code {b : Nat} {code : List (BitVec 32)} (ha : 84219≤b) (hb : b+code.length≤88260)
    (hc : CodeAt Images.expandImage (pcOf b) code) : CodeAt expandImage (pcOf b) code :=
  codeAt_of_window_eq (source:=Images.expandImage) (target:=expandImage) (start:=84219) (count:=4041) ha hb (by decide) late_window.symm hc

theorem boundsA : ∀ j : Fin 128,
    54335≤SharedAProof.copyBase j.val ∧ SharedAProof.copyBase j.val+(SharedAProof.copyPre j.val).length≤84218 ∧
    54335≤SharedAProof.trampOf j.val ∧ SharedAProof.trampOf j.val+5≤84218 ∧
    84219≤SharedAProof.tramp16Of j.val ∧ SharedAProof.tramp16Of j.val+5≤88260 := by decide +kernel

theorem copyA (j : Nat) (hj : j<128) : SharedAProof.CopyCodeAt expandImage j := by
  have hb:=boundsA ⟨j,hj⟩
  dsimp only at hb
  intro i w hi
  obtain ⟨hil,hival⟩:=List.getElem?_eq_some_iff.mp hi
  rw [mid_word (SharedAProof.copyBase j+i) (by omega) (by omega)]
  exact SharedBank.installed_copies.copyA j hj i w hi

theorem trampA (j : Nat) (hj : j<128) : CodeAt expandImage (pcOf (SharedAProof.trampOf j))
    (trampWords (SharedAProof.trampOf j) SEARCH (SharedAProof.siteB j+1)) := by
  have hb:=boundsA ⟨j,hj⟩
  dsimp only at hb
  apply mid_code (by omega) ?_ (SharedBank.installed_copies.trampA j hj)
  rw [SharedBank.trampWords_length]
  omega

theorem tramp16A (j : Nat) (hj : j<128) : CodeAt expandImage (pcOf (SharedAProof.tramp16Of j))
    (trampWords (SharedAProof.tramp16Of j) SEARCH16 (SharedAProof.site16C j+1)) := by
  have hb:=boundsA ⟨j,hj⟩
  dsimp only at hb
  apply late_code (by omega) ?_ (SharedBank.installed_copies.tramp16A j hj)
  rw [SharedBank.trampWords_length]
  omega

theorem boundsB : ∀ j : Fin 128,
    54335≤SharedBProof.copyBase j.val ∧ SharedBProof.copyBase j.val+(SharedBProof.copyPre j.val).length≤84218 ∧
    54335≤SharedBProof.trampOf j.val ∧ SharedBProof.trampOf j.val+5≤84218 ∧
    84219≤SharedBProof.tramp16Of j.val ∧ SharedBProof.tramp16Of j.val+5≤88260 := by decide +kernel

theorem copyB (j : Nat) (hj : j<128) : SharedBProof.CopyCodeAt expandImage j := by
  have hb:=boundsB ⟨j,hj⟩
  dsimp only at hb
  intro i w hi
  obtain ⟨hil,hival⟩:=List.getElem?_eq_some_iff.mp hi
  rw [mid_word (SharedBProof.copyBase j+i) (by omega) (by omega)]
  exact SharedBank.installed_copies.copyB j hj i w hi

theorem trampB (j : Nat) (hj : j<128) : CodeAt expandImage (pcOf (SharedBProof.trampOf j))
    (trampWords (SharedBProof.trampOf j) SEARCH (SharedBProof.siteB j+1)) := by
  have hb:=boundsB ⟨j,hj⟩
  dsimp only at hb
  apply mid_code (by omega) ?_ (SharedBank.installed_copies.trampB j hj)
  rw [SharedBank.trampWords_length]
  omega

theorem tramp16B (j : Nat) (hj : j<128) : CodeAt expandImage (pcOf (SharedBProof.tramp16Of j))
    (trampWords (SharedBProof.tramp16Of j) SEARCH16 (SharedBProof.site16C j+1)) := by
  have hb:=boundsB ⟨j,hj⟩
  dsimp only at hb
  apply late_code (by omega) ?_ (SharedBank.installed_copies.tramp16B j hj)
  rw [SharedBank.trampWords_length]
  omega

theorem boundsC : ∀ j : Fin 128,
    54335≤SharedCProof.copyBase j.val ∧ SharedCProof.copyBase j.val+(SharedCProof.copyPre j.val).length≤84218 ∧
    54335≤SharedCProof.trampOf j.val ∧ SharedCProof.trampOf j.val+5≤84218 ∧
    84219≤SharedCProof.tramp16Of j.val ∧ SharedCProof.tramp16Of j.val+5≤88260 := by decide +kernel

theorem copyC (j : Nat) (hj : j<128) : SharedCProof.CopyCodeAt expandImage j := by
  have hb:=boundsC ⟨j,hj⟩
  dsimp only at hb
  intro i w hi
  obtain ⟨hil,hival⟩:=List.getElem?_eq_some_iff.mp hi
  rw [mid_word (SharedCProof.copyBase j+i) (by omega) (by omega)]
  exact SharedBank.installed_copies.copyC j hj i w hi

theorem trampC (j : Nat) (hj : j<128) : CodeAt expandImage (pcOf (SharedCProof.trampOf j))
    (trampWords (SharedCProof.trampOf j) SEARCH (SharedCProof.siteB j+1)) := by
  have hb:=boundsC ⟨j,hj⟩
  dsimp only at hb
  apply mid_code (by omega) ?_ (SharedBank.installed_copies.trampC j hj)
  rw [SharedBank.trampWords_length]
  omega

theorem tramp16C (j : Nat) (hj : j<128) : CodeAt expandImage (pcOf (SharedCProof.tramp16Of j))
    (trampWords (SharedCProof.tramp16Of j) SEARCH16 (SharedCProof.site16C j+1)) := by
  have hb:=boundsC ⟨j,hj⟩
  dsimp only at hb
  apply late_code (by omega) ?_ (SharedBank.installed_copies.tramp16C j hj)
  rw [SharedBank.trampWords_length]
  omega

theorem copies : SharedBank.CopyCodes expandImage := by
  refine ⟨?_,copyA,copyB,copyC,trampA,trampB,trampC,?_,tramp16A,tramp16B,tramp16C⟩
  · exact mid_code (by decide) (by rw [searchWords_length];decide) SharedBank.installed_copies.search
  · exact mid_code (by decide) (by rw [search16Words_length];decide) SharedBank.installed_copies.search16

theorem codes : OuterSharedBank.Codes expandImage :=
  ⟨copies,OuterImageBankA.code,(fun j hj=>OuterImageBanks.b_child ⟨j,hj⟩),(fun j hj=>OuterImageBanks.c_child ⟨j,hj⟩)⟩

#print axioms copies
#print axioms codes
end OuterImageCopies
