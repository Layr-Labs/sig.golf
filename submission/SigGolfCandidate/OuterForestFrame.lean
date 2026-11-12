import SigGolfCandidate.OuterSharedCore
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestFrame
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT.W9.Machine.Expand

def writes (X : Nat) : Prop := SharedForestRun.writes X ∨ 8323072≤X ∧ X<8355840

def childW (L : W9Machine.Layout) (k : Fin 9) (raw : Fin 128) (X : Nat) : Prop :=
  SharedForestRun.childW L k raw X ∨ OuterSharedPost.Extra k.val X

theorem extra_bounds (k : Fin 9) (X : Nat) (h : OuterSharedPost.Extra k.val X) : writes X := by
  rcases h with h|h|h
  · subst X; left; left; omega
  · subst X; left; left; omega
  · right
    unfold OuterSharedPost.record at h
    have := k.isLt
    omega

theorem child_bounds {image : Image} (k : Fin 9) (raw : Fin 128) (X : Nat)
    (h : childW (SharedDispatch.layout image k) k raw X) : writes X := by
  rcases h with h|h
  · exact Or.inl (SharedForestRun.child_writes_bounds k raw X h)
  · exact extra_bounds k X h

theorem child_low {L : W9Machine.Layout} {k : Fin 9} {raw : Fin 128} {X : Nat}
    (h : childW L k raw X) (ha : 2048≤X) (hb : X<11000) : SharedForestRun.childW L k raw X := by
  rcases h with h|h
  · exact h
  · rcases h with h|h|h
    · omega
    · omega
    · unfold OuterSharedPost.record at h
      omega

theorem core_frame {L : W9Machine.Layout} {w : W9Machine.WBytes} {index : Nat} {k : Fin 9}
    {raw : Fin 128} {u entry t : MachineState} {ends : List Digest} {computed : Digest×Nat×Nat×Nat}
    (hp : Chain.Post L w index k raw u ends entry) (ht : OuterSharedPost.Post L k raw entry computed t) :
    Frame u t (childW L k raw) := by
  intro addr ha hn
  have he : ¬OuterSharedPost.Writes L k raw addr := by
    intro H
    rcases H with H|H
    · exact hn (Or.inl H)
    · exact hn (Or.inr H)
  rw [ht.frame addr ha he]
  apply hp.frame addr ha
  intro h
  apply hn
  left;left;left
  unfold Chain.writes at h
  simp only [Chain.base] at h ⊢
  split <;> omega

theorem core_frame_dispatch {L : W9Machine.Layout} {w : W9Machine.WBytes} {index : Nat} {k : Fin 9}
    {raw : Fin 128} {u entry t : MachineState} {ends : List Digest} {computed : Digest×Nat×Nat×Nat}
    (hp : Chain.Post L w index k raw ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : OuterSharedPost.Post L k raw entry computed t) : Frame u t (childW L k raw) := by
  intro addr ha hn
  exact (core_frame hp ht addr ha hn).trans (SharedDispatch.result_mem k u _)

theorem fields_frame {index : Nat} {raw : Fin 9 → Fin 128} {ranks : Fin 9 → Fin 563}
    {u t : MachineState} (hf : Frame u t writes) (hu : SharedForestRun.Fields index raw ranks u) :
    SharedForestRun.Fields index raw ranks t := by
  have hm (addr : Nat) (ha : 11000≤addr) (hb : addr<0x7e0000) :
      t.getMem (BitVec.ofNat 64 addr)=u.getMem (BitVec.ofNat 64 addr) :=
    hf addr (by omega) (by unfold writes SharedForestRun.writes SharedChild.scratchW SigGolfCandidate.FtsGrind.SCR SigGolfCandidate.FtsGrind.SCR16; omega)
  refine ⟨(hm 0x66010 (by decide) (by decide)).trans hu.index,?_,?_⟩
  · intro k
    rw [SharedDispatch.rawRead,hm _ (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    exact hu.raw k
  · intro k
    rw [SharedDispatch.rankRead,hm _ (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    exact hu.rank k

#print axioms core_frame
#print axioms fields_frame
end OuterForestFrame
