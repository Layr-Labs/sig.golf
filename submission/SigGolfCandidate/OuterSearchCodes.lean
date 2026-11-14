import SigGolfCandidate.OuterImageTransfers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSearchCodes
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search
open ClaudeWCT.W9.Machine.Expand

theorem hooks : SharedCounterHooks.Code OuterImages.expandImage := by
  have old:=SharedCounterHooks.installed_code
  constructor
  · exact OuterImageTransfers.code (b:=46905) (by decide +kernel) old.first
  · exact OuterImageTransfers.code (b:=46911) (by decide +kernel) old.middle
  · exact OuterImageTransfers.code (b:=46914) (by decide +kernel) old.last
  · exact OuterImageTransfers.code (b:=46916) (by decide +kernel) old.remainder
  · exact OuterImageTransfers.code (b:=46918) (by decide +kernel) old.lowerCredit
  · exact OuterImageTransfers.code (b:=46924) (by decide +kernel) old.topCredit

theorem reward : CanonicalExpandHooks.Code OuterImages.expandImage := by
  have old:=SharedSearchCode.installed_reward_code
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,hooks,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact OuterImageTransfers.code (b:=Reward.base 354 false) (by decide +kernel) old.scoring.1
  · exact OuterImageTransfers.code (b:=Reward.base 354 true) (by decide +kernel) old.scoring.2
  · exact OuterImageTransfers.code (b:=43024) (by decide +kernel) old.floorJump
  · exact OuterImageTransfers.code (b:=43027) (by decide +kernel) old.lowerBranch
  · exact OuterImageTransfers.code (b:=43028) (by decide +kernel) old.lowerJump
  · exact OuterImageTransfers.code (b:=43029) (by decide +kernel) old.lowerBad
  · exact OuterImageTransfers.code (b:=54176) (by decide +kernel) old.t51K
  · exact OuterImageTransfers.code (b:=90000) (by decide +kernel) old.t51UA
  · exact OuterImageTransfers.code (b:=90120) (by decide +kernel) old.t51UB
  · exact OuterImageTransfers.code (b:=54310) (by decide +kernel) old.guardPrep
  · exact OuterImageTransfers.code (b:=88095) (by decide +kernel) old.guardHelper
  · exact OuterImageTransfers.code (b:=54317) (by decide +kernel) old.guardTest
  · exact OuterImageTransfers.code (b:=54318) (by decide +kernel) old.guardReject
  · exact OuterImageTransfers.code (b:=54319) (by decide +kernel) old.guardAccept

theorem kernel (P : Prop) (hP : P) : KernAt OuterImages.expandImage 354 P := by
  have old:=SharedSearchCode.installed_kernel P hP
  rcases old with ⟨⟨h0,h1⟩,hb,⟨h2,h3⟩,⟨h4,h5,h6⟩,h7,h8,h9,_⟩
  refine ⟨⟨?_,?_⟩,hb,⟨?_,?_⟩,⟨?_,?_,?_⟩,?_,?_,?_,hP⟩
  · exact OuterImageTransfers.code (b:=354) (by decide +kernel) h0
  · exact OuterImageTransfers.code (b:=capBase 354) (by decide +kernel) h1
  · exact OuterImageTransfers.code (b:=prxBase 354) (by decide +kernel) h2
  · exact OuterImageTransfers.code (b:=rtBase 354) (by decide +kernel) h3
  · exact OuterImageTransfers.code (b:=tcBase 354) (by decide +kernel) h4
  · exact OuterImageTransfers.code (b:=tcEntry 354) (by decide +kernel) h5
  · exact OuterImageTransfers.code (b:=stubBase 354) (by decide +kernel) h6
  · exact OuterImageTransfers.code (b:=zBase 354) (by decide +kernel) h7
  · exact OuterImageTransfers.code (b:=selectorBase 354) (by decide +kernel) h8
  · exact OuterImageTransfers.code (b:=choiceBase 354) (by decide +kernel) h9

theorem code : KernAt OuterImages.expandImage 354 (CanonicalExpandHooks.Code OuterImages.expandImage) := kernel _ reward

#print axioms code
end OuterSearchCodes
