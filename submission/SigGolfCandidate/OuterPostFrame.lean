import SigGolfCandidate.OuterLayersRecovery
import SigGolfCandidate.OuterPostEnc
import SigGolfCandidate.OuterPadWitness
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterPostFrame
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

theorem record_bounds (m : Fin 9) : 0x7f0000≤OuterSharedPost.record m.val ∧ OuterSharedPost.record m.val<0x7f8000 := by
  unfold OuterSharedPost.record
  have:=m.isLt
  omega

theorem of_memory {s t : MachineState} {ns : List Nat} (h : OuterForestCompactRecords.Inv 9 ns s)
    (hm : ∀ m : Fin 9,t.getMem (BitVec.ofNat 64 (OuterSharedPost.record m.val))=s.getMem (BitVec.ofNat 64 (OuterSharedPost.record m.val))) :
    OuterForestCompactRecords.Inv 9 ns t :=
  ⟨h.len,fun m hn hf=>(hm m).trans (h.record m hn hf)⟩

theorem pp_mem (leaf : Nat) (M : Nat → Word) (A : Nat) (h1 : 0x7f0000 ≤ A) (h2 : A < 0x7f8000) :
    PostPass.ppMem leaf M A = M A := by
  rw [PostPass.ppMem_out _ _ _ (by omega), PostPass.stage7_unfold, PostPass.zfill_miss _ _ _ _ (by omega),
    PostPass.bmv_miss _ _ _ _ _ (by omega), PostPass.dmv_miss _ _ _ _ (by omega), PostPass.fcp_miss _ _ _ _ _ (by omega),
    PostPass.fcp_miss _ _ _ _ _ (by omega), PostPass.fcp_miss _ _ _ _ _ (by omega), PostPass.bmv_miss _ _ _ _ _ (by omega),
    PostPass.bmv_miss _ _ _ _ _ (by omega), PostPass.bmv_miss _ _ _ _ _ (by omega), PostPass.fcp_miss _ _ _ _ _ (by omega),
    PostPass.fcp_miss _ _ _ _ _ (by omega), PostPass.fcp_miss _ _ _ _ _ (by omega)]


theorem post16_miss (M : Word → Word) (A : Word)
    (h : ∀ k,k<4 → A≠M (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot16 (SigGolfCandidate.FtsGrind.sB k)))) :
    SigGolfCandidate.FtsGrind.postMem16 M A=M A := by
  unfold SigGolfCandidate.FtsGrind.postMem16
  rw [foldl_upd_apply]
  exact foldl_if_none _ _ _ _ _ (fun k hk=>h k (List.mem_range.mp hk))

#print axioms pp_mem
#print axioms post16_miss
end OuterPostFrame
