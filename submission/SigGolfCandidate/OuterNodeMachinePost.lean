import SigGolfCandidate.OuterNodeMachineCounter
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeMachinePost
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks

def recordAddr (s : MachineState) : Word :=
  (((s.getMem (s.getReg .x10+16#64) >>> 16) &&& 15#64) ||| 2032#64) <<< 12

theorem b_post_obligs (s : MachineState) (input record : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0)
    (hr : recordAddr s=BitVec.ofNat 64 record) (hrlo : 2^22 ≤ record) (hrhi : record < 2^23)
    (hrm : record % 8 = 0) : b_post.res.obligs s := by
  have hrec : (BitVec.ofNat 64 record).toNat=record := toNat_ofNat_lt (by omega)
  have hne0 : BitVec.ofNat 64 record≠1152#64 := by
    intro he
    have hh:=congrArg BitVec.toNat he
    simp only [hrec,BitVec.toNat_ofNat] at hh
    omega
  have hne1 : BitVec.ofNat 64 record≠1160#64 := by
    intro he
    have hh:=congrArg BitVec.toNat he
    simp only [hrec,BitVec.toNat_ofNat] at hh
    omega
  dsimp only [recordAddr] at hr
  simp only [ha,ofNat_add_ofNat] at hr
  simp [b_post.res,Result.obligs,Oblig.all,Oblig.holds,Addr.eval,E.eval,BinOp.eval,UnOp.eval,LoadKind.fromWord,
    hr,ha,ofNat_add_ofNat,memAccessValid_iff,BitVec.toNat_ofNat,MEMORY_BYTES,hrec,hne0,hne1,Ne.symm hne0,Ne.symm hne1]
  omega


theorem b_post_values (s : MachineState) :
    (b_post.res.toState s).getMem (recordAddr s)=s.getReg .x6 ∧
    (b_post.res.toState s).getReg .x6=s.getMem 1152 ∧
    (b_post.res.toState s).getReg .x7=s.getMem 1160 ∧
    (b_post.res.toState s).pc=pcOf 246498 := by
  simp [Result.toState_getMem,Result.toState_getReg,Result.toState_pc,b_post.res,RegFile.get,
    memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,recordAddr]

theorem b_post_frame (s : MachineState) (a : Word) (ha : a≠recordAddr s) :
    (b_post.res.toState s).getMem a=s.getMem a := by
  rw [Result.toState_getMem]
  apply memEval_frame
  intro p hp
  simp only [b_post.res,List.mem_cons,List.not_mem_nil,or_false] at hp
  subst p
  simpa [recordAddr,Addr.eval,E.eval,BinOp.eval] using ha


theorem b_post_run {im : Image} (hc : CodeAt im (pcOf 246512) b_postCode) (s : MachineState)
    (hp : s.pc=pcOf 246512) (input record : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0)
    (hr : recordAddr s=BitVec.ofNat 64 record) (hrlo : 2^22 ≤ record) (hrhi : record < 2^23)
    (hrm : record % 8 = 0) :
    ∃ t,Steps im s 9 9 t ∧ t.pc=pcOf 246498 ∧ RegsExcept s t [.x6,.x7] ∧
      t.getMem (recordAddr s)=s.getReg .x6 ∧ t.getReg .x6=s.getMem 1152 ∧ t.getReg .x7=s.getMem 1160 ∧
      (∀ a,a≠recordAddr s→t.getMem a=s.getMem a) := by
  refine ⟨b_post.res.toState s,symRun_sound b_post hc s hp
    (b_post_obligs s input record ha hi hl hm hr hrlo hrhi hrm),(b_post_values s).2.2.2,?_,
    (b_post_values s).1,(b_post_values s).2.1,(b_post_values s).2.2.1,b_post_frame s⟩
  intro r hx;cases r <;> simp at hx <;> rfl

theorem c_post_obligs (s : MachineState) (input record : Nat) (ha : s.getReg .x10=BitVec.ofNat 64 input)
    (hi : input < 2^20) (hl : 2048 ≤ input) (hm : input % 8 = 0)
    (hr : recordAddr s=BitVec.ofNat 64 record) (hrlo : 2^22 ≤ record) (hrhi : record < 2^23)
    (hrm : record % 8 = 0) : c_post.res.obligs s :=
  b_post_obligs s input record ha hi hl hm hr hrlo hrhi hrm

#print axioms b_post_run
#print axioms c_post_obligs
#print axioms b_post_values
#print axioms b_post_frame
#print axioms b_post_obligs
end OuterNodeMachinePost
