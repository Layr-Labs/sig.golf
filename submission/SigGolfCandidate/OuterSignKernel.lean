import SigGolfCandidate.OuterSignTransfers
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignKernel
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search

theorem hooks : CanonicalHooks.Code OuterImages.signImage := by
  have old:=SigGolfCandidate.T3M.Sign.SharedSearchCode.installed_hooks
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact OuterSignTransfers.code (b:=Reward.base 543 false) (by decide +kernel) old.scoring.1
  · exact OuterSignTransfers.code (b:=Reward.base 543 true) (by decide +kernel) old.scoring.2
  · exact OuterSignTransfers.code (b:=21015) (by decide +kernel) old.floorJump
  · exact OuterSignTransfers.code (b:=21018) (by decide +kernel) old.lowerBranch
  · exact OuterSignTransfers.code (b:=21019) (by decide +kernel) old.lowerJump
  · exact OuterSignTransfers.code (b:=21020) (by decide +kernel) old.lowerBad
  · exact OuterSignTransfers.code (b:=21438) (by decide +kernel) old.topBranch
  · exact OuterSignTransfers.code (b:=21179) (by decide +kernel) old.cr0
  · exact OuterSignTransfers.code (b:=21182) (by decide +kernel) old.cr3
  · exact OuterSignTransfers.code (b:=21183) (by decide +kernel) old.cr4
  · exact OuterSignTransfers.code (b:=21185) (by decide +kernel) old.cr6
  · exact OuterSignTransfers.code (b:=21667) (by decide +kernel) old.zc
  · exact OuterSignTransfers.code (b:=22491) (by decide +kernel) old.floorHook
  · exact OuterSignTransfers.code (b:=22495) (by decide +kernel) old.lowerHook
  · exact OuterSignTransfers.code (b:=22499) (by decide +kernel) old.topHook
  · exact OuterSignTransfers.code (b:=1798) (by decide +kernel) old.t51K
  · exact OuterSignTransfers.code_tail (b:=26241) (by decide +kernel) (by decide +kernel) old.t51UA
  · exact OuterSignTransfers.code (b:=21342) (by decide +kernel) old.t51UJ
  · exact OuterSignTransfers.code_tail (b:=26361) (by decide +kernel) (by decide +kernel) old.t51UB
  · exact OuterSignTransfers.code (b:=1952) (by decide +kernel) old.guardPrep
  · exact OuterSignTransfers.code (b:=26008) (by decide +kernel) old.guardHelper
  · exact OuterSignTransfers.code (b:=1959) (by decide +kernel) old.guardTest
  · exact OuterSignTransfers.code (b:=1960) (by decide +kernel) old.guardReject
  · exact OuterSignTransfers.code (b:=1961) (by decide +kernel) old.guardAccept

theorem kernel (P : Prop) (hP : P) : KernAt OuterImages.signImage 543 P := by
  have old:=SigGolfCandidate.T3M.Sign.SharedSearchCode.installed_kernel P hP
  rcases old with ⟨⟨h0,h1⟩,hb,⟨h2,h3⟩,⟨h4,h5,h6⟩,h7,h8,h9,_⟩
  refine ⟨⟨?_,?_⟩,hb,⟨?_,?_⟩,⟨?_,?_,?_⟩,?_,?_,?_,hP⟩
  · exact OuterSignTransfers.code (b:=543) (by decide +kernel) h0
  · exact OuterSignTransfers.code (b:=capBase 543) (by decide +kernel) h1
  · exact OuterSignTransfers.code (b:=prxBase 543) (by decide +kernel) h2
  · exact OuterSignTransfers.code (b:=rtBase 543) (by decide +kernel) h3
  · exact OuterSignTransfers.code (b:=tcBase 543) (by decide +kernel) h4
  · exact OuterSignTransfers.code (b:=tcEntry 543) (by decide +kernel) h5
  · exact OuterSignTransfers.code (b:=stubBase 543) (by decide +kernel) h6
  · exact OuterSignTransfers.code (b:=zBase 543) (by decide +kernel) h7
  · exact OuterSignTransfers.code (b:=selectorBase 543) (by decide +kernel) h8
  · exact OuterSignTransfers.code (b:=choiceBase 543) (by decide +kernel) h9

theorem code : KernAt OuterImages.signImage 543 (CanonicalHooks.Code OuterImages.signImage) := kernel _ hooks
#print axioms code
end OuterSignKernel
