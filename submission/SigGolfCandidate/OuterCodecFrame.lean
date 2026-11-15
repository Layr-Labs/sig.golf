import SigGolfCandidate.OuterCodecMachine
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterCodecFrame
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine

def carrierWords : List Word := [29080,29480,29880,30280,30488,33848]

theorem pack_frame (s : MachineState) (a : Word) (ha : a∉carrierWords) :
    (packBlock.res.toState s).getMem a=s.getMem a := by
  rw [Result.toState_getMem]
  apply memEval_frame
  intro p hp
  simp only [packBlock.res,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    intro he
    apply ha
    simp only [Addr.eval,E.eval] at he
    subst a
    decide

theorem unpack_frame (s : MachineState) (a : Word) (ha : a∉(carrierWords++[33856,160])) :
    (unpackBlock.res.toState s).getMem a=s.getMem a := by
  rw [Result.toState_getMem]
  apply memEval_frame
  intro p hp
  simp only [unpackBlock.res,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    intro he
    apply ha
    simp only [Addr.eval,E.eval] at he
    subst a
    decide

/-- E3: the unpack tail decodes the published pk word: mem[160] := 1 - mem[160]. -/
theorem unpack_pk (s : MachineState) :
    (unpackBlock.res.toState s).getMem 160=1-s.getMem 160 := by
  first
  | rfl
  | (simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
      LoadKind.fromWord,StoreKind.merge]
     try norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
     try bv_omega)

#print axioms pack_frame
#print axioms unpack_pk
#print axioms unpack_frame
end OuterCodecFrame
