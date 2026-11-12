import SigGolfCandidate.OuterSignCoordinateRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignForest
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open SigGolfCandidate.Research
open ClaudeWCT ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedCoordinate
variable {sk : BitVec 256}
def forestW (A : Nat) : Prop := ∃c,c < 9 ∧ OuterSignCoordinate.coordinateW c A

def step (a : BitVec 256) (ranks : Nat → WCT9.Rank) (acc : List Row) (c : Nat) : M (List Row) := do
  let pads:=priorPads c (acc.getD (c-1) emptyRow).1
  let row←OuterSignCoordinate.program (WCT9.digestIndex a) c (chosen c a) (ranks c) (fun j=>(pads (j/64)).1) (rightPads pads)
  pure (acc++[row])
def forestProgram (a : BitVec 256) (ranks : Nat → WCT9.Rank) : M (List Row) :=
  (List.range 9).foldlM (step a ranks) []

structure ForestInv (sk a : BitVec 256) (s0 : MachineState) (n : Nat) (rows : List Row) (t : MachineState) : Prop where
  pc : t.pc=pcOf (if n < 9 then cbase n else 20715)
  ready : Ready sk a t
  length : rows.length=n
  prior : n ≠ 0 → RootAt (n-1) (rows.getD (n-1) emptyRow).1 t
  signatures : ∀j,j < n → SigAt j (chosen j a) (rows.getD j emptyRow) t
  regs : RegsExcept s0 t (.x25::.x24::.x18::bodyRegs)
  frame : Frame s0 t forestW


theorem writes_other_signature {c d A : Nat} (hc:c<9) (hd:d<9) (hne:c≠d)
    (ha:slotV d 0≤A ∧ A<slotV d 0+208) : ¬OuterSignCoordinate.coordinateW c A := by
  intro hw
  have ho : SharedCoordinate.coordinateW c A ∨ A=1152 ∨ A=1160 := by
    unfold OuterSignCoordinate.coordinateW OuterSignCoordinate.allWrites OuterSignCoordinate.writes
      SharedCoordinate.coordinateW SharedCoordinate.allWrites at *
    tauto
  rcases ho with ho|ho|ho
  · exact SharedCoordinate.writes_other_signature hc hd hne ha ho
  all_goals unfold slotV SIG at ha;omega

theorem sigAt_frame {c d sel : Nat} {rv : Row} {s t : MachineState} (hc:c < 9) (hd:d < 9) (hne:c ≠ d)
    (hs:SigAt d sel rv s) (hf:Frame s t (OuterSignCoordinate.coordinateW c)) : SigAt d sel rv t := by
  have hl:=SharedPath.levels_bound d
  refine ⟨⟨hs.values.1,?_⟩,?_,?_⟩
  · intro i hi
    exact (hs.values.2 i hi).frame hf (by unfold slotV;ao)
      (writes_other_signature hc hd hne (by unfold slotV;constructor <;> omega))
      (writes_other_signature hc hd hne (by unfold slotV;constructor <;> omega))
  · intro l hll
    exact (hs.paths l hll).frame hf (by unfold SharedPath.target slotV;ao)
      (writes_other_signature hc hd hne (by unfold SharedPath.target slotV;constructor <;> omega))
      (writes_other_signature hc hd hne (by unfold SharedPath.target slotV;constructor <;> omega))
  · intro hfirst
    exact (hs.dummy hfirst).frame hf (by unfold SharedEnd.target slotP;ao)
      (writes_other_signature hc hd hne (by unfold SharedEnd.target slotP slotV;constructor <;> omega))
      (writes_other_signature hc hd hne (by unfold SharedEnd.target slotP slotV;constructor <;> omega))

def forestStepBound : Nat := 19+(14+21*SharedReuse.coefStepC+(128*SharedLeaves.cost+126*(SharedNode.unitC+77865)+110))
theorem cost_le (c : Nat) : OuterSignCoordinateRun.cost c ≤ forestStepBound := by
  have:=SharedTree.limit_bounds c
  have hm : (127-SharedTail.limit c)*(SharedNode.unitC+77865) ≤ 126*(SharedNode.unitC+77865) := Nat.mul_le_mul_right _ (by omega)
  unfold OuterSignCoordinateRun.cost forestStepBound SharedTree.count
  exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_left hm (128*SharedLeaves.cost)) 110) (14+21*SharedReuse.coefStepC)) 19

theorem forest_step (hf:SharedReuse.Fetch OuterImages.signImage) (hcode:∀c,c < 9 → OuterSignCoordinateCode.Code c)
    (a : BitVec 256) (ranks : Nat → WCT9.Rank) (hranks:∀c,c < 9 → (ranks c).val=rank c a)
    {s0 : MachineState} (c : Nat) (hc:c < 9) (acc : List Row) (s : MachineState)
    (hs:ForestInv sk a s0 c acc s) :
    TBSim OuterImages.signImage sk s forestStepBound (step a ranks acc c) (ForestInv sk a s0 (c+1)) := by
  have hrank:rank c a < 563:=(hranks c hc) ▸ (ranks c).isLt
  have he: (⟨rank c a,hrank⟩:WCT9.Rank)=ranks c:=Fin.ext (hranks c hc).symm
  unfold step
  have hrun:=OuterSignCoordinateRun.coordinate hf hc (hcode c hc) a hrank s (by simpa only[if_pos hc]using hs.pc) hs.ready
    (leaf_pads hc hs.prior) (node_pads hc hs.prior)
  rw[he]at hrun
  refine (TBSim.bind (W₂:=0) hrun (fun rv t ht=>TBSim.pure ?_)).mono (by have:=cost_le c;omega) (fun _ _ h=>h)
  refine ⟨ht.1.out.pc.trans (congrArg pcOf (nextPc_eq c hc)),ht.2,by simp[hs.length],?_,?_,?_,?_⟩
  · intro _
    simpa only[Nat.add_sub_cancel_right,←hs.length,getD_append_new]using ht.1.out.roots
  · intro j hj
    by_cases hjc:j=c
    · subst j
      simpa only[←hs.length,getD_append_new]using (⟨ht.1.out.values,ht.1.out.paths,ht.1.out.dummy⟩:SigAt c (chosen c a) rv t)
    · rw[getD_append_old _ _ _ _ (by rw[hs.length];omega)]
      exact sigAt_frame hc (by omega) (by omega) (hs.signatures j (by omega)) ht.1.frame
  · exact (hs.regs.trans ht.1.regs).mono (by simp[bodyRegs])
  · exact (hs.frame.trans ht.1.frame).mono (fun A _ h=>h.elim id (fun h=>⟨c,hc,h⟩))

theorem forest_loop (hf:SharedReuse.Fetch OuterImages.signImage) (hcode:∀c,c < 9 → OuterSignCoordinateCode.Code c)
    (a : BitVec 256) (ranks : Nat → WCT9.Rank) (hranks:∀c,c < 9 → (ranks c).val=rank c a)
    (s : MachineState) (hpc:s.pc=pcOf (cbase 0)) (hs:Ready sk a s) :
    TBSim OuterImages.signImage sk s (9*forestStepBound) (forestProgram a ranks) (ForestInv sk a s 9) := by
  unfold forestProgram
  rw[List.range_eq_range']
  exact TBSim.foldlM_range' 0 9 _ _ (ForestInv sk a s) forestStepBound
    (fun c hc acc t ht=>by simpa only[Nat.zero_add]using forest_step hf hcode a ranks hranks c hc acc t ht)
    ⟨by simpa using hpc,hs,rfl,by simp,by simp,RegsExcept.refl _ _,Frame.refl _ _⟩
#print axioms forest_step
#print axioms forest_loop
end OuterSignForest
