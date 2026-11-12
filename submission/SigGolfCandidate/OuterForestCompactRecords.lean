import SigGolfCandidate.OuterForestFrame
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestCompactRecords
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT.W9.Machine.Expand
open OuterForestFrame

def count (n : Nat) : Nat := min n 8/2+(if 9≤n then 1 else 0)

theorem geometry : ∀ k : Fin 9,
    count (k.val+1)=count k.val+(if SharedV3.first k.val then 0 else 1) ∧
    (SharedV3.first k.val=false → k.val/2=count k.val) ∧
    (∀ m : Fin 9,m.val<k.val → SharedV3.first m.val=false → m.val/2<count k.val) := by decide +kernel

structure Inv (n : Nat) (ns : List Nat) (u : MachineState) : Prop where
  len : ns.length=count n
  record : ∀ m : Fin 9,m.val<n → SharedV3.first m.val=false →
    u.getMem (BitVec.ofNat 64 (OuterSharedPost.record m.val))=BitVec.ofNat 64 (ns.getD (m.val/2) 0)

theorem keep {image : Image} {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {u entry t : MachineState} {k : Fin 9} {ends : List Digest} {res : Digest×Nat×Nat×Nat}
    (hp : Chain.Post (SharedDispatch.layout image k) (SharedV3.viewWB 2904 w k.val u) index k (raw k)
      ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : OuterSharedPost.Post (SharedDispatch.layout image k) k (raw k) entry res t)
    (m : Fin 9) (hm : m.val<k.val) (hfirst : SharedV3.first m.val=false) :
      t.getMem (BitVec.ofNat 64 (OuterSharedPost.record m.val))=
        u.getMem (BitVec.ofNat 64 (OuterSharedPost.record m.val)) := by
    have hk:=k.isLt
    have hf:=core_frame_dispatch hp ht
    have hmpos : 0 < m.val := by
      by_contra h
      have hz : m.val = 0 := by omega
      simp only [hz,SharedV3.first] at hfirst
      contradiction
    apply hf _ (by unfold OuterSharedPost.record;omega)
    intro hw
    rcases hw with hw|hw
    · have H:=SharedForestRun.child_writes_bounds k (raw k) _ hw
      unfold SharedForestRun.writes SharedChild.scratchW SigGolfCandidate.FtsGrind.SCR SigGolfCandidate.FtsGrind.SCR16 OuterSharedPost.record at H
      omega
    · rcases hw with hw|hw|hw <;> unfold OuterSharedPost.record at hw <;> omega

theorem next {image : Image} {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {u entry t : MachineState} {k : Fin 9} {ns : List Nat} {ends : List Digest} {res : Digest×Nat×Nat×Nat}
    (hr : Inv k.val ns u)
    (hp : Chain.Post (SharedDispatch.layout image k) (SharedV3.viewWB 2904 w k.val u) index k (raw k)
      ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : OuterSharedPost.Post (SharedDispatch.layout image k) k (raw k) entry res t) :
    Inv (k.val+1) (if SharedV3.first k.val then ns else ns++[res.2.2.2]) t := by
  have hg:=geometry k
  have hlen:=hr.len
  cases hf : SharedV3.first k.val with
  | true=>
    simp only [hf,if_true] at hg ⊢
    refine ⟨by omega,?_⟩
    intro m hm hfirst
    have hmk : m.val<k.val := by
      by_contra h
      have he : m=k := Fin.ext (by omega)
      subst m
      rw [hf] at hfirst
      contradiction
    rw [keep hp ht m hmk hfirst]
    exact hr.record m hmk hfirst
  | false=>
    simp only [hf,Bool.false_eq_true,if_false] at hg ⊢
    have gd_old (m : Fin 9) (hm : m.val<k.val) (hfirst : SharedV3.first m.val=false) :
        (ns++[res.2.2.2]).getD (m.val/2) 0=ns.getD (m.val/2) 0 := by
      have H:=hg.2.2 m hm hfirst
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (show m.val/2<ns.length by omega)]
    have gd_new : (ns++[res.2.2.2]).getD (k.val/2) 0=res.2.2.2 := by
      have he : k.val/2=ns.length := by rw [hlen];exact hg.2.1 trivial
      simp only [he,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
    refine ⟨by simp only [List.length_append,List.length_singleton];omega,?_⟩
    intro m hm hfirst
    rcases Nat.lt_or_ge m.val k.val with h|h
    · rw [keep hp ht m h hfirst,gd_old m h hfirst]
      exact hr.record m h hfirst
    · obtain rfl : m=k := Fin.ext (by omega)
      rw [gd_new]
      exact ht.outer hfirst

#print axioms geometry
#print axioms next
end OuterForestCompactRecords
