import SigGolfCandidate.OuterCodecFrame
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterCodecValues
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine

theorem pack_first_word (s : MachineState) :
    (packBlock.res.toState s).getMem 29080=
      s.getMem 29080 ||| ((s.getMem 33856 &&& 7) <<< 61) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem pack_second_word (s : MachineState) :
    (packBlock.res.toState s).getMem 29480=
      s.getMem 29480 ||| (((s.getMem 33856 >>> 3) &&& 7) <<< 61) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem pack_third_word (s : MachineState) :
    (packBlock.res.toState s).getMem 29880=
      s.getMem 29880 ||| (((s.getMem 33856 >>> 6) &&& 7) <<< 61) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem pack_fourth_word (s : MachineState) :
    (packBlock.res.toState s).getMem 30280=
      s.getMem 30280 ||| (((s.getMem 33856 >>> 9) &&& 7) <<< 61) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem pack_fifth_word (s : MachineState) :
    (packBlock.res.toState s).getMem 30488=
      s.getMem 30488 ||| (((s.getMem 33856 >>> 12) &&& 15) <<< 60) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_first_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 29080=s.getMem 29080 &&& 2305843009213693951 := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_second_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 29480=s.getMem 29480 &&& 2305843009213693951 := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_third_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 29880=s.getMem 29880 &&& 2305843009213693951 := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_fourth_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 30280=s.getMem 30280 &&& 2305843009213693951 := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_fifth_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 30488=s.getMem 30488 &&& 1152921504606846975 := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [replaceByte,extractByte,extractHalfword,BitVec.truncate]

def unpackedTail (s : MachineState) : Word :=
  (s.getMem 29080 >>> 61) ||| ((s.getMem 29480 >>> 61) <<< 3) |||
  ((s.getMem 29880 >>> 61) <<< 6) ||| ((s.getMem 30280 >>> 61) <<< 9) ||| ((s.getMem 30488 >>> 60) <<< 12)
theorem unpack_tail_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 33856=(s.getMem 33856 &&& ~~~65535) ||| unpackedTail s := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [unpackedTail,replaceHalfword,replaceByte,extractByte,extractHalfword,BitVec.truncate]

#print axioms pack_first_word
#print axioms pack_fifth_word
#print axioms unpack_tail_word
end OuterCodecValues
