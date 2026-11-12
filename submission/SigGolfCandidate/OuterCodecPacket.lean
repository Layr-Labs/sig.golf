import SigGolfCandidate.OuterCodecValues
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterCodecPacket
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterCodecValues OuterTailPacket

def readCarriers (s : MachineState) : Five := ⟨extractByte (s.getMem 29080) 7,extractByte (s.getMem 29480) 7,
  extractByte (s.getMem 29880) 7,extractByte (s.getMem 30280) 7,extractByte (s.getMem 30488) 7⟩
def readTail (s : MachineState) : BitVec 16 := extractHalfword (s.getMem 33856) 0

theorem pack_packet (s : MachineState) (hclear : clear (readCarriers s)=readCarriers s) :
    readCarriers (packBlock.res.toState s)=pack (readCarriers s) (readTail s) := by
  have ha:=congrArg Five.a hclear
  have hb:=congrArg Five.b hclear
  have hc:=congrArg Five.c hclear
  have hd:=congrArg Five.d hclear
  have he:=congrArg Five.e hclear
  dsimp only [clear,readCarriers] at ha hb hc hd he
  have ha5 : (s.getMem 29080#64).getLsbD 61=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 5) ha
    simpa [extractByte] using hh.symm
  have ha6 : (s.getMem 29080#64).getLsbD 62=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 6) ha
    simpa [extractByte] using hh.symm
  have ha7 : (s.getMem 29080#64).getLsbD 63=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 7) ha
    simpa [extractByte] using hh.symm
  have hb5 : (s.getMem 29480#64).getLsbD 61=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 5) hb
    simpa [extractByte] using hh.symm
  have hb6 : (s.getMem 29480#64).getLsbD 62=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 6) hb
    simpa [extractByte] using hh.symm
  have hb7 : (s.getMem 29480#64).getLsbD 63=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 7) hb
    simpa [extractByte] using hh.symm
  have hc5 : (s.getMem 29880#64).getLsbD 61=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 5) hc
    simpa [extractByte] using hh.symm
  have hc6 : (s.getMem 29880#64).getLsbD 62=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 6) hc
    simpa [extractByte] using hh.symm
  have hc7 : (s.getMem 29880#64).getLsbD 63=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 7) hc
    simpa [extractByte] using hh.symm
  have hd5 : (s.getMem 30280#64).getLsbD 61=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 5) hd
    simpa [extractByte] using hh.symm
  have hd6 : (s.getMem 30280#64).getLsbD 62=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 6) hd
    simpa [extractByte] using hh.symm
  have hd7 : (s.getMem 30280#64).getLsbD 63=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 7) hd
    simpa [extractByte] using hh.symm
  have he4 : (s.getMem 30488#64).getLsbD 60=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 4) he
    simpa [extractByte] using hh.symm
  have he5 : (s.getMem 30488#64).getLsbD 61=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 5) he
    simpa [extractByte] using hh.symm
  have he6 : (s.getMem 30488#64).getLsbD 62=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 6) he
    simpa [extractByte] using hh.symm
  have he7 : (s.getMem 30488#64).getLsbD 63=false := by
    have hh:=congrArg (fun v : BitVec 8=>v.getLsbD 7) he
    simpa [extractByte] using hh.symm
  apply Five.ext
  all_goals
    simp only [readCarriers,pack,ha,hb,hc,hd,he,pack_first_word,pack_second_word,pack_third_word,pack_fourth_word,pack_fifth_word]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [←BitVec.getLsbD_eq_getElem,readTail,extractByte,extractHalfword,BitVec.truncate,ha5,ha6,ha7,hb5,hb6,hb7,hc5,hc6,hc7,hd5,hd6,hd7,he4,he5,he6,he7]

theorem unpack_packet (s : MachineState) :
    readCarriers (unpackBlock.res.toState s)=clear (readCarriers s) := by
  apply Five.ext
  all_goals
    simp only [readCarriers,clear,unpack_first_word,unpack_second_word,unpack_third_word,unpack_fourth_word,unpack_fifth_word]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [extractByte]

theorem unpack_tail (s : MachineState) :
    readTail (unpackBlock.res.toState s)=(unpack (readCarriers s)).2 := by
  simp only [readTail,unpack_tail_word]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [unpackedTail,readCarriers,unpack,extractByte,extractHalfword,BitVec.truncate]


theorem unpack_run {im : Image} (hc : CodeAt im (pcOf 88300) unpackCode) (s : MachineState)
    (hp : s.pc=pcOf 88300) :
    ∃ t,Steps im s 38 38 t ∧ t.pc=pcOf 88338 ∧ RegsExcept s t [.x6,.x7,.x28,.x29] ∧
      t.getReg .x6=0 ∧ t.getReg .x7=0 ∧ t.getReg .x28=0 ∧ t.getReg .x29=0 ∧
      readCarriers t=clear (readCarriers s) ∧ readTail t=(unpack (readCarriers s)).2 ∧
      ∀ a,a∉(OuterCodecFrame.carrierWords++[33856])→t.getMem a=s.getMem a := by
  refine ⟨unpackBlock.res.toState s,symRun_sound unpackBlock hc s hp (unpack_obligs s),rfl,?_,
    rfl,rfl,rfl,rfl,unpack_packet s,unpack_tail s,OuterCodecFrame.unpack_frame s⟩
  intro r hr
  cases r <;> simp at hr <;> rfl

theorem pack_run_packet {im : Image} (hc : CodeAt im (pcOf 26207) packCode) (s : MachineState)
    (hp : s.pc=pcOf 26207) (hclear : clear (readCarriers s)=readCarriers s) :
    ∃ t,Steps im s 33 33 t ∧ t.pc=pcOf 26240 ∧ RegsExcept s t [.x6,.x7,.x28,.x29] ∧
      readCarriers t=pack (readCarriers s) (readTail s) ∧
      ∀ a,a∉OuterCodecFrame.carrierWords→t.getMem a=s.getMem a := by
  refine ⟨packBlock.res.toState s,symRun_sound packBlock hc s hp (pack_obligs s),rfl,?_,
    pack_packet s hclear,OuterCodecFrame.pack_frame s⟩
  intro r hr
  cases r <;> simp at hr <;> rfl

#print axioms pack_run_packet
#print axioms unpack_run
#print axioms pack_packet
#print axioms unpack_packet
#print axioms unpack_tail
end OuterCodecPacket
