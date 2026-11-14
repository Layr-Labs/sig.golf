import SigGolfCandidate.OuterCodecFrame
set_option debug.skipKernelTC true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterCodecValues
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine

def packedWord (s : MachineState) : Word :=
  (s.getMem 29080 >>> 56) ||| ((s.getMem 29480 >>> 56) <<< 3) |||
  ((s.getMem 29880 >>> 56) <<< 6) ||| ((s.getMem 30280 >>> 56) <<< 9) |||
  ((s.getMem 30488 >>> 56) <<< 12) ||| ((s.getMem 33856 &&& 65535) <<< 16)
def joinedWord (s : MachineState) : Word :=
  (s.getMem 29080 >>> 56) ||| ((s.getMem 29480 >>> 56) <<< 8) |||
  ((s.getMem 29880 >>> 56) <<< 16) ||| ((s.getMem 30280 >>> 56) <<< 24)
def unpackedTail (s : MachineState) : Word := joinedWord s >>> 16

theorem pack_first_word (s : MachineState) :
    (packBlock.res.toState s).getMem 29080=replaceByte (s.getMem 29080) 7 (extractByte (packedWord s) 0) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem pack_second_word (s : MachineState) :
    (packBlock.res.toState s).getMem 29480=replaceByte (s.getMem 29480) 7 (extractByte (packedWord s) 1) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem pack_third_word (s : MachineState) :
    (packBlock.res.toState s).getMem 29880=replaceByte (s.getMem 29880) 7 (extractByte (packedWord s) 2) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem pack_fourth_word (s : MachineState) :
    (packBlock.res.toState s).getMem 30280=replaceByte (s.getMem 30280) 7 (extractByte (packedWord s) 3) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem pack_fifth_word (s : MachineState) :
    (packBlock.res.toState s).getMem 30488=replaceByte (s.getMem 30488) 7 (extractByte (s.getMem 33848) 7) := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem pack_last_word (s : MachineState) :
    (packBlock.res.toState s).getMem 33848=replaceByte (s.getMem 33848) 7 0 := by
  simp only [Result.toState_getMem,packBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_first_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 29080=replaceByte (s.getMem 29080) 7 (((joinedWord s >>> 0) &&& 7).setWidth 8) := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_second_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 29480=replaceByte (s.getMem 29480) 7 (((joinedWord s >>> 3) &&& 7).setWidth 8) := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_third_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 29880=replaceByte (s.getMem 29880) 7 (((joinedWord s >>> 6) &&& 7).setWidth 8) := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_fourth_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 30280=replaceByte (s.getMem 30280) 7 (((joinedWord s >>> 9) &&& 7).setWidth 8) := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_fifth_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 30488=replaceByte (s.getMem 30488) 7 (((joinedWord s >>> 12) &&& 15).setWidth 8) := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_last_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 33848=replaceByte (s.getMem 33848) 7 (extractByte (s.getMem 30488) 7) := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

theorem unpack_tail_word (s : MachineState) :
    (unpackBlock.res.toState s).getMem 33856=replaceHalfword (s.getMem 33856) 0 ((unpackedTail s).setWidth 16) := by
  simp only [Result.toState_getMem,unpackBlock.res,memEval_cons,memEval_nil,Addr.eval,E.eval,BinOp.eval,UnOp.eval,
    LoadKind.fromWord,StoreKind.merge]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod,BitVec.reduceEq,↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [packedWord,joinedWord,unpackedTail,replaceByte,replaceHalfword,extractByte,extractHalfword,BitVec.truncate]

#print axioms pack_first_word
#print axioms unpack_tail_word
end OuterCodecValues
