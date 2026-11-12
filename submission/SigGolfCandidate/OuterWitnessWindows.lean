import SigGolfCandidate.OuterWitnessOverlay
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterWitnessWindows
open SigGolfCandidate.T3M W9Machine OuterWitnessOverlay
open OuterExpand
open ClaudeWCT.W9.T3M
instance (o n : Nat) : Decidable (WinFree o n) := by unfold WinFree;infer_instance

theorem chain : ∀ i : Fin 6,
    WinFree (wctChainOff i.val+wctPad0Off i.val) 16 ∧
    WinFree (wctChainOff i.val+24) 8 ∧
    WinFree (wctChainOff i.val+wctPad1Off i.val) 16 ∧
    WinFree (V3.leafSlot i.val) 16 ∧
    WinFree (wctChainOff i.val+wctValueOff i.val) 16 := by decide +kernel

theorem path : ∀ j : Fin 128,∀ l : Fin 6,
    WinFree (SharedV3.sibOff j.val l.val) 16 ∧
    (l.val<5 → WinFree (SharedV3.blkOff j.val l.val+32) 16) ∧
    (l.val<4 → WinFree (SharedV3.blkOff j.val l.val+16) 16) := by decide +kernel

theorem hand : WinFree 160 16 ∧ WinFree 672 16 := by decide +kernel

theorem topOther : ∀ coord : Fin 9,∀ j : Fin 128,
    SharedV3.topOtherOff coord.val j.val+16≤21756 ∧
    ∀ c : Fin 5,SharedV3.topOtherOff coord.val j.val+16≤outerNoncePos c.val ∨
      outerNoncePos c.val+8≤SharedV3.topOtherOff coord.val j.val := by decide +kernel

#print axioms chain
#print axioms path
#print axioms hand
#print axioms topOther
end OuterWitnessWindows
