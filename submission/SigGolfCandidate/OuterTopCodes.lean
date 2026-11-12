import SigGolfCandidate.OuterImageTransfers
import SigGolfCandidate.Merge094
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterTopCodes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand

theorem driver : CodeAt OuterImages.expandImage (pcOf 45056) Images.expandSharedDriver :=
  OuterImageTransfers.code (b:=45056) (by decide +kernel) codeAt_expand_shared_driver

theorem coordinates : ∀ k : Fin 9,SharedScatter.CoordinateCode OuterImages.expandImage k.val :=
  SharedScatter.coordinateCodes (SharedScatter.entryCode_of_driver driver) (SharedScatter.valuesCode_of_driver driver)
    (SharedScatter.planCode_of_driver driver) (SharedScatter.pathsCode_of_driver driver)
    (SharedScatter.sixthCode_of_driver driver) (SharedScatter.topCode_of_driver driver)

theorem zero : SharedZero.ClearCode OuterImages.expandImage := SharedZero.code_of_driver driver

theorem low_word (p : Nat) (ha : 1≤p) (hb : p<54334) :
    OuterImages.expandImage.code[p]?=Images.expandImage.code[p]? := by
  have h:=image_slice_of_window (source:=OuterImages.expandImage) (target:=Images.expandImage)
    (start:=1) (count:=54333) (base:=p) (len:=1) ha (by omega) OuterInstalledDispatch.window
  have h0:=congrArg (fun xs : List (BitVec 32)=>xs[0]?) h
  simpa only [List.getElem?_take,show 0<1 from by decide,↓reduceIte,List.getElem?_drop,Nat.add_zero] using h0

namespace CLayout
open ClaudeWCT.W9.Machine.Expand.Layout

theorem code : ClaudeWCT.W9.Machine.Expand.Layout.Code OuterImages.expandImage := by
  have old:=installed_layout
  constructor
  · exact OuterImageTransfers.code (b:=48100) (by decide +kernel) old.top
  · exact OuterImageTransfers.code (b:=48112) (by decide +kernel) old.clr0
  · exact OuterImageTransfers.code (b:=48116) (by decide +kernel) old.clrL
  · intro g hg
    have hb : ∀ i : Fin 4,OuterImageTransfers.Clean (lbHeadPc.getD i.val 0) (lbHeadCodes.getD i.val []).length := by decide +kernel
    have h:=hb ⟨g,hg⟩
    dsimp only at h
    exact OuterImageTransfers.code (b:=lbHeadPc.getD g 0) h (old.head g hg)
  · intro k hk
    have hb : ∀ i : Fin 180,OuterImageTransfers.Clean (pcK i.val) (lbCodes.getD i.val []).length := by decide +kernel
    have h:=hb ⟨k,hk⟩
    dsimp only at h
    exact OuterImageTransfers.code (b:=pcK k) h (old.chunk k hk)
  · exact OuterImageTransfers.code (b:=49207) (by decide +kernel) old.ret
end CLayout

theorem compact : CompactCodeAt OuterImages.expandImage := by
  refine ⟨?_,?_,CLayout.code⟩
  · intro n w hw
    have orig:=hw
    unfold compactLook at hw
    split at hw
    · rename_i hs
      simp only [compactScope,decide_eq_true_eq] at hs
      rw [low_word n (by omega) (by omega)]
      exact installed_compact.look n w orig
    · cases hw
  · have old:=installed_pairCopy
    constructor
    · exact OuterImageTransfers.code (b:=48000) (by decide +kernel) old.c0
    · exact OuterImageTransfers.code (b:=48001) (by decide +kernel) old.cL
    · exact OuterImageTransfers.code (b:=48013) (by decide +kernel) old.cT

theorem search : SrchCoreAt OuterImages.expandImage :=
  OuterImageTransfers.code (b:=42795) (by decide +kernel) SharedControl.installed_srchCore

theorem afterCode : CodeAt OuterImages.expandImage (pcOf 46509) SharedScatter.afterCode := SharedScatter.after_of_driver driver
theorem finishCode : CodeAt OuterImages.expandImage (pcOf 47005) SharedScatter.finishCode := SharedScatter.finish_of_driver driver
theorem endCode : CodeAt OuterImages.expandImage (pcOf 43071) SharedScatter.endCode :=
  OuterImageTransfers.code (b:=43071) (by decide +kernel) SharedScatter.installed_end
theorem scatterJump : CodeAt OuterImages.expandImage (pcOf 43761) [0x24c0306f] :=
  OuterImageTransfers.code (b:=43761) (by decide +kernel) SharedControl.scatter_code
theorem compactJump : CodeAt OuterImages.expandImage (pcOf 351) [0x4d52706f] :=
  OuterImageTransfers.code (b:=351) (by decide +kernel) SharedControl.compact_code

#print axioms compact
#print axioms coordinates
#print axioms search
end OuterTopCodes
