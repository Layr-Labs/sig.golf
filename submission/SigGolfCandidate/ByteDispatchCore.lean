import SigGolfCandidate.Merge054
import Mathlib.Tactic
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.ByteDispatch
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv
def off (h : Nat) : Nat := if h=8 then 15 else h
def src (h : Nat) : E := .un (.ld .bu (if h=8 then 7 else h))
  (.ld (if h=8 then addC (.reg .x16) 8 else .reg .x16))
def col (h : Nat) : Nat := [0,62,68,74,80,86,92,98,354].getD h 0
def im (h : Nat) : Word := BitVec.ofNat 64 (2^64+4*col h-2048)
def val (h : Nat) : E := .bin .sll (src h) (.c 11#64)
def code (h : Nat) : List (BitVec 32) :=
  [BitVec.ofNat 32 (off h*2^20+0x84703),0xb71713,
   BitVec.ofNat 32 (((4*col h+2048)%4096)*2^20+0x70067)]
def result (h : Nat) : Result :=
  ⟨⟨RegFile.init.set .x14 (val h),[],[.align8 (.reg .x16),.valid ⟨some (.reg .x16),BitVec.ofNat 64 (off h)⟩ 1]⟩,
    .bin .and (.bin .add (val h) (.c (im h))) (.c (~~~1#64)),.jump,3,3⟩
theorem run_checks : ∀ h : Fin 8, rOK (symRun {noAlias := true} (code (h.val+1)) (pcOf 0) 5) (result (h.val+1))=true := by
  decide +kernel
theorem byte_extract (v : BitVec 128) (k : Fin 16) :
    (extractByte (v.extractLsb' (64*(k.val/8)) 64) (k.val%8)).zeroExtend 64 =
      BitVec.ofNat 64 (v.toNat / 2^(8*k.val) % 256) := by
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;> norm_num [extractByte,BitVec.toNat_setWidth,BitVec.extractLsb'_toNat,
    BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul]
  all_goals omega
def Source (v : BitVec 128) (s : MachineState) : Prop :=
  ∃ d : Nat, 16136 ≤ d ∧ d%8=0 ∧ d+16≤MEMORY_BYTES ∧
    s.getReg .x16=BitVec.ofNat 64 d ∧ DigAt s d v

theorem source_read (v : BitVec 128) (s : MachineState) (hs : Source v s) (h : Fin 8) :
    (src (h.val+1)).eval s = BitVec.ofNat 64 (v.toNat / 2^(8*off (h.val+1)) % 256) := by
  obtain ⟨d,hd,ha,hb,hr,hv⟩:=hs
  have hm0 : s.getMem (s.getReg .x16)=v.extractLsb' 0 64 := by rw [hr]; exact hv.1
  have hm8 : s.getMem (s.getReg .x16+8#64)=v.extractLsb' 64 64 := by
    rw [hr,show (8#64 : Word)=BitVec.ofNat 64 8 from rfl,ofNat_add_ofNat];exact hv.2
  fin_cases h
  all_goals simp only [Fin.val_zero,Fin.val_mk] at *
  all_goals first
    | simpa [src,off,addC,E.eval,UnOp.eval,LoadKind.fromWord,BinOp.eval,hm0,hm8] using byte_extract v ⟨1,by decide⟩
    | simpa [src,off,addC,E.eval,UnOp.eval,LoadKind.fromWord,BinOp.eval,hm0,hm8] using byte_extract v ⟨2,by decide⟩
    | simpa [src,off,addC,E.eval,UnOp.eval,LoadKind.fromWord,BinOp.eval,hm0,hm8] using byte_extract v ⟨3,by decide⟩
    | simpa [src,off,addC,E.eval,UnOp.eval,LoadKind.fromWord,BinOp.eval,hm0,hm8] using byte_extract v ⟨4,by decide⟩
    | simpa [src,off,addC,E.eval,UnOp.eval,LoadKind.fromWord,BinOp.eval,hm0,hm8] using byte_extract v ⟨5,by decide⟩
    | simpa [src,off,addC,E.eval,UnOp.eval,LoadKind.fromWord,BinOp.eval,hm0,hm8] using byte_extract v ⟨6,by decide⟩
    | simpa [src,off,addC,E.eval,UnOp.eval,LoadKind.fromWord,BinOp.eval,hm0,hm8] using byte_extract v ⟨7,by decide⟩
    | simpa [src,off,addC,E.eval,UnOp.eval,LoadKind.fromWord,BinOp.eval,hm0,hm8] using byte_extract v ⟨15,by decide⟩

theorem low_byte_shift (w : BitVec 64) :
    ((extractByte w 0).zeroExtend 64 <<< 11) = ((w <<< 56) >>> 45) := by
  apply BitVec.eq_of_toNat_eq
  norm_num [extractByte,BitVec.toNat_setWidth,BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

#print axioms source_read
#print axioms low_byte_shift
theorem result_obligs (v : BitVec 128) (s : MachineState) (hs : Source v s) (h : Fin 8) :
    (result (h.val+1)).obligs s := by
  obtain ⟨d,hd,ha,hb,hr,hv⟩:=hs
  have hb0 : d+16≤16777216 := by simpa [MEMORY_BYTES] using hb
  have h64 : d<2^64 := by unfold MEMORY_BYTES at hb;omega
  have hvalid : ∀ n : Nat, n≤15 → accessValid (BitVec.ofNat 64 d+BitVec.ofNat 64 n) 1=true := by
    intro n hn
    have hdn : d+n<2^64 := by unfold MEMORY_BYTES at hb;omega
    rw [ofNat_add_ofNat]
    simp [accessValid_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hdn,Nat.mod_eq_of_lt h64,MEMORY_BYTES]
    omega
  simp only [result,Result.obligs,Oblig.all,Oblig.holds,E.eval,Addr.eval]
  constructor
  · rw [hr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h64];exact ha
  · rw [hr]
    apply hvalid
    fin_cases h <;> decide

#print axioms result_obligs
def prefixCode (hi : Bool) : List (BitVec 32) :=
  if hi then [0x1863883,0x1060813,0x84703,0xb71713,0xd1870067,0x13]
  else [0x863883,0x60813,0x84703,0xb71713,0xd1870067,0x13]
def prefixBase (hi : Bool) : E := if hi then addC (.reg .x12) 16 else .reg .x12
def prefixVal (hi : Bool) : E := .bin .sll (.un (.ld .bu 0) (.ld (prefixBase hi))) (.c 11#64)
def prefixResult (hi : Bool) : Result :=
  ⟨⟨((RegFile.init.set .x17 (.ld (addC (.reg .x12) (if hi then 24 else 8)))).set .x16 (prefixBase hi)).set .x14 (prefixVal hi),
    [],[.align8 (.reg .x12),.valid ⟨some (.reg .x12),if hi then 16#64 else 0#64⟩ 1,
        .valid ⟨some (.reg .x12),if hi then 24#64 else 8#64⟩ 8]⟩,
    .bin .and (.bin .add (prefixVal hi) (.c (BitVec.ofNat 64 (2^64-744)))) (.c (~~~1#64)),.jump,5,5⟩
theorem prefixLow_runs : (fun p : Word => symRun {noAlias := true} (prefixCode false) p 5)=(fun _=>some (prefixResult false)) := by kernel_rfl
theorem prefixHigh_runs : (fun p : Word => symRun {noAlias := true} (prefixCode true) p 5)=(fun _=>some (prefixResult true)) := by kernel_rfl
theorem prefixLow_run (p : Word) : symRun {noAlias := true} (prefixCode false) p 5=some (prefixResult false) := congrFun prefixLow_runs p
theorem prefixHigh_run (p : Word) : symRun {noAlias := true} (prefixCode true) p 5=some (prefixResult true) := congrFun prefixHigh_runs p
def initialTarget (v : BitVec 128) : Word :=
  ((((v.extractLsb' 0 64) <<< 56) >>> 45)+BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64

theorem prefix_end {im : Image} (s : MachineState) (hi : Bool) (v : BitVec 128) (d q : Nat)
    (hpc : s.pc=pcOf q) (hc : CodeAt im (pcOf q) (prefixCode hi))
    (h12 : s.getReg .x12=BitVec.ofNat 64 d)
    (hd : d%8=0 ∧ 16136≤d ∧ d+32≤0x7000)
    (hv : DigAt s (d+(if hi then 16 else 0)) v) :
    ∃t,Steps im s 5 5 t ∧ t.pc=initialTarget v ∧ Source v t ∧
      t.getReg .x17=v.extractLsb' 64 64 ∧ RegsExcept s t [.x16,.x17,.x14] ∧ Frame s t (fun _=>False) := by
  cases hi with
  | false =>
    simp only [Bool.false_eq_true,if_false,Nat.add_zero] at hc hv
    have m0 : s.getMem (s.getReg .x12)=v.extractLsb' 0 64 := by rw [h12];exact hv.1
    have m8 : s.getMem (s.getReg .x12+8#64)=v.extractLsb' 64 64 := by
      rw [h12,show (8#64 : Word)=BitVec.ofNat 64 8 from rfl,ofNat_add_ofNat];exact hv.2
    have he:=symRun_sound (prefixLow_run (pcOf q)) hc s hpc (by
      simp [prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp,h12,accessValid_iff,MEMORY_BYTES] <;> omega)
    let t:=(prefixResult false).toState s
    have ft : Frame s t (fun _=>False) := by intro A _ _;simp [t,prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp]
    have ht : t.getReg .x16=BitVec.ofNat 64 d := by simp [t,prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp,h12]
    have hs : Source v t :=
      ⟨d,hd.2.1,hd.1,by unfold MEMORY_BYTES;omega,ht,hv.frame ft (by omega) (by simp) (by simp)⟩
    refine ⟨t,he,?_,hs,?_,?_,ft⟩
    · change (((extractByte (s.getMem (s.getReg .x12)) 0).zeroExtend 64 <<< 11)+BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64=initialTarget v
      rw [m0,low_byte_shift];rfl
    · simpa [t,prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp] using m8
    · intro r hr;cases r <;> simp at hr <;> simp [t,prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp] <;> rfl
  | true =>
    simp only [if_true] at hc hv
    have m0 : s.getMem (s.getReg .x12+16#64)=v.extractLsb' 0 64 := by
      rw [h12,show (16#64 : Word)=BitVec.ofNat 64 16 from rfl,ofNat_add_ofNat];exact hv.1
    have m8 : s.getMem (s.getReg .x12+24#64)=v.extractLsb' 64 64 := by
      rw [h12,show (24#64 : Word)=BitVec.ofNat 64 24 from rfl,ofNat_add_ofNat]
      simpa only [Nat.add_assoc] using hv.2
    have he:=symRun_sound (prefixHigh_run (pcOf q)) hc s hpc (by
      simp [prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp,h12,accessValid_iff,MEMORY_BYTES] <;> omega)
    let t:=(prefixResult true).toState s
    have ft : Frame s t (fun _=>False) := by intro A _ _;simp [t,prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp]
    have ht : t.getReg .x16=BitVec.ofNat 64 (d+16) := by simp [t,prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp,h12,ofNat_add_ofNat]
    have hs : Source v t :=
      ⟨d+16,by omega,by omega,by unfold MEMORY_BYTES;omega,ht,hv.frame ft (by omega) (by simp) (by simp)⟩
    refine ⟨t,he,?_,hs,?_,?_,ft⟩
    · change (((extractByte (s.getMem (s.getReg .x12+16#64)) 0).zeroExtend 64 <<< 11)+BitVec.ofNat 64 (2^64-744)) &&& ~~~1#64=initialTarget v
      rw [m0,low_byte_shift];rfl
    · simpa [t,prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp] using m8
    · intro r hr;cases r <;> simp at hr <;> simp [t,prefixResult,prefixBase,prefixVal,RegFile.set,addC,E.eval,BinOp.eval,rv_simp] <;> rfl
#print axioms prefix_end

end SigGolfCandidate.T3M.ByteDispatch
