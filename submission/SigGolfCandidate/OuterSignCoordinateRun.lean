import SigGolfCandidate.OuterSignCoordinate
import SigGolfCandidate.OuterSignCoordinateCode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignCoordinateRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open ClaudeWCT ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open OuterSignCoordinate
variable {sk : BitVec 256}

theorem writes_outside {c A : Nat} (hc:c<9)
    (hA:(NBUF≤A ∧ A<NBUF+32) ∨ (TBL≤A ∧ A<TBL+65536) ∨
      A=PRIVW ∨ A=PRIVW+8 ∨ A=PRIVW+32 ∨ A=PRIVW+40 ∨ ZeroCell A) : ¬OuterSignCoordinate.coordinateW c A := by
  intro hw
  have ho : SharedCoordinate.coordinateW c A ∨ A=1152 ∨ A=1160 := by
    unfold OuterSignCoordinate.coordinateW OuterSignCoordinate.allWrites OuterSignCoordinate.writes
      SharedCoordinate.coordinateW SharedCoordinate.allWrites at *
    tauto
  rcases ho with ho|ho|ho
  · exact SharedCoordinate.writes_outside hc hA ho
  all_goals
    subst A
    simp only [ZeroCell,ScrZero,NBUF,TBL,PRIVW,CHAINW,NODEW] at hA
    omega

def cost (c : Nat) : Nat := 19+(14+21*SharedReuse.coefStepC+(128*SharedLeaves.cost+SharedTree.count c*(SharedNode.unitC+77865)+110))
theorem ready_frame {sk N : BitVec 256} {s t : MachineState} {c : Nat} {rs : List Reg}
    (hc:c < 9) (h:Ready sk N s) (hr:RegsExcept s t rs) (h5:.x5 ∉ rs) (h22:.x22 ∉ rs)
    (hf:Frame s t (OuterSignCoordinate.coordinateW c)) : Ready sk N t := by
  refine ⟨by rw[hr.get h5];exact h.x5,by rw[hr.get h22];exact h.x22,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k hk;rw[hf.get (by ao) (writes_outside hc (by left;constructor <;> ao))];exact h.nbuf k hk
  · intro k hk;rw[hf.get (by ao) (writes_outside hc (by right;left;constructor <;> ao))];exact h.table k hk
  · rw[hf.get (by ao) (writes_outside hc (by simp))];exact h.p0
  · rw[hf.get (by ao) (writes_outside hc (by simp))];exact h.p8
  · rw[hf.get (by ao) (writes_outside hc (by simp))];exact h.p32
  · rw[hf.get (by ao) (writes_outside hc (by simp))];exact h.p40
  · intro A hA
    rw[hf.get (by unfold ZeroCell ScrZero at hA;aoh) (writes_outside hc (by simp[hA]))]
    exact h.zero A hA

theorem coordinate (hf:SharedReuse.Fetch OuterImages.signImage) {c : Nat} (hc:c < 9) (hcode:OuterSignCoordinateCode.Code c)
    (a : BitVec 256) (hrank:rank c a < 563) (s : MachineState) (hpc:s.pc=pcOf (cbase c))
    (hs:Ready sk a s) {leftPads rightPads : Nat → Digest}
    (hpadL:∀j, j < 128 → SharedLeaf.PadAt c (SharedNext.raw c j) (leftPads j) s)
    (hpadR:∀h, h < 128 → SharedNode.PadAt c h (rightPads h) s) :
    TBSim OuterImages.signImage sk s (cost c)
      (OuterSignCoordinate.program (WCT9.digestIndex a) c (chosen c a) ⟨rank c a,hrank⟩ leftPads rightPads)
      (fun rv t=>OuterSignCoordinate.FullOut c (WCT9.digestIndex a) s rv (chosen c a) t ∧ Ready sk a t) := by
  obtain ⟨u,n,su,hn,upc,u24,u28,ur,uf⟩:=SharedField.step_field hcode.field hc s hpc hs.nbuf
  have hu:Ready sk a u:=hs.frame hc ur (by simp) (by simp) (uf.mono (fun _ _ h=>h.elim))
  obtain ⟨v,sv,vpc,v25,vr,vf⟩:=SharedReuse.step_lwu hf hc u upc (f:=rank c a) (by omega) u28 hu.table
  have hv:Ready sk a v:=hu.frame hc vr (by simp) (by simp) (vf.mono (fun _ _ h=>h.elim))
  have huv:Frame s v (fun _=>False):=(uf.trans vf).mono (fun _ _ h=>h.elim id id)
  have v24:v.getReg .x24=BitVec.ofNat 64 (SharedNext.raw c (chosen c a)):=by rw[vr.get (by simp),u24,raw_chosen]
  have hb:=hv.body _ _ v24 v25
  refine (TBSim.steps (su.trans sv)
    ((OuterSignCoordinate.coefs_rows_finish hf hcode.leaf hcode.hook hcode.next hcode.node hcode.tail hcode.finish hcode.path hcode.ending
      hc (chosen_lt c a) (WCT9.digestIndex_lt a) (lt_trans (pkAt_lt _) (by decide)) (pkAt_digit _ hrank)
      (fun j hj => ?_) (fun h hh => ?_) vpc hb
      ⟨hv.zero _ (by simp[ZeroCell,ScrZero]),hv.zero _ (by simp[ZeroCell,ScrZero]),
        hv.zero _ (by simp[ZeroCell,ScrZero]),hv.zero _ (by simp[ZeroCell,ScrZero])⟩).mono le_rfl (fun rv t ht=>?_))).mono ?_ (fun _ _ h=>h)
  · exact padL_coefFrame (hpadL j hj) hc (SharedNext.raw_lt c hj) (huv.mono (fun _ _ h=>h.elim))
  · exact padR_coefFrame (hpadR h hh) hc (huv.mono (fun _ _ h=>h.elim))
  · have hfull:OuterSignCoordinate.FullOut c (WCT9.digestIndex a) s rv (chosen c a) t:=
      ⟨ht.out,((ur.trans vr).trans ht.regs).mono (by simp[bodyRegs]),
        (huv.trans ht.frame).mono (fun _ _ h=>h.elim False.elim id)⟩
    exact ⟨hfull,ready_frame hc hs hfull.regs (by simp[bodyRegs]) (by simp[bodyRegs]) hfull.frame⟩
  · unfold cost;omega
#print axioms ready_frame
#print axioms coordinate
end OuterSignCoordinateRun
