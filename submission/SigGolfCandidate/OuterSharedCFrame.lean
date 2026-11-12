import SigGolfCandidate.OuterSharedPost
import SigGolfCandidate.OuterChildModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSharedCFrame
open RiscvZkvm.Rv64 SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open W9Machine W9Drv.SharedCProof SigGolfCandidate.FtsGrind
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

def OldWrites (B j X : Nat) : Prop := prefixWrites B X ∨ (B-handO j≤X ∧ X<B-handO j+32) ∨
  (slotA B≤X ∧ X<slotA B+16) ∨ (1104≤X ∧ X<1144) ∨ (SCR≤X ∧ X<SCR+32) ∨ far16 B X

theorem allowed (coord : Fin 9) (j : Fin 128) (X : Nat) (h : OuterCopyChildFlatC.Writes coord.val j.val X) :
    OldWrites (coordRegion coord.val) j.val X ∨ OuterSharedPost.Extra coord.val X := by
  have h2:=blk_bounds j.val j.isLt 2 (by decide)
  have h3:=blk_bounds j.val j.isLt 3 (by decide)
  have h5:=blk_bounds j.val j.isLt 5 (by decide)
  rcases h with h|h|h
  · unfold OuterCopyLayer2C.Changes at h
    unfold OldWrites OuterSharedPost.Extra prefixWrites
    unfold padO at h
    omega
  · unfold OuterCopyGroundC.Changes at h
    unfold OldWrites OuterSharedPost.Extra prefixWrites
    unfold padO at h
    omega
  · rcases h with ⟨off,hoff,he⟩|hw|he
    · have ho:=stagesW_bound j.isLt (by decide) hoff
      unfold OldWrites OuterSharedPost.Extra prefixWrites
      omega
    · unfold OuterNodeSearchInvariant.Work at hw
      unfold OldWrites OuterSharedPost.Extra prefixWrites
      omega
    · unfold OldWrites OuterSharedPost.Extra OuterSharedPost.record
      omega

#print axioms allowed
end OuterSharedCFrame
