import SigGolfCandidate.OuterSignEntry
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterSignPlain
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterSignBlocks OuterSignEntry

structure Input (A D : Nat) (input : List UInt8) (s : MachineState) : Prop where
  x5 : s.getReg .x5=0
  x10 : s.getReg .x10=BitVec.ofNat 64 A
  x11 : s.getReg .x11=64#64
  x12 : s.getReg .x12=BitVec.ofNat 64 D
  len : input.length=64
  words : s.readWords (BitVec.ofNat 64 A) 8=wordsOf input
  alo : 2048≤A
  ahi : A<2^20
  aa : A%8=0
  dlo : 2048≤D
  dhi : D<2^20
  da : D%8=0

structure Out (s : MachineState) (D : Nat) (a : HashOutput) (t : MachineState) : Prop where
  at_pc : t.pc=pcOf 25339
  regs : RegsExcept s t []
  output : ∀ k<4,t.getMem (BitVec.ofNat 64 (D+8*k))=a.extractLsb' (64*k) 64
  frame : Frame s t (fun X=>X=1152 ∨ X=1160 ∨ D≤X ∧ X<D+32)

theorem run {im : Image} {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s u : MachineState}
    (F : Input A D input s) (hc : CodeAt im (pcOf 26203) [0x73])
    (hd : CodeAt im (pcOf 26204) doneCode) (hu : Ready s A D (pcOf 26203) u) :
    TBSim im sk u 11 (publicHash input) (Out s D) := by
  have ha:=F.ahi;have hdhi:=F.dhi;have hlo:=F.alo;have hdlo:=F.dlo
  have gr : ∀ r,r∉[Reg.x6,Reg.x7]→u.getReg r=s.getReg r := hu.regs
  have h10 : u.getReg .x10=BitVec.ofNat 64 A := by rw [gr _ (by decide)];exact F.x10
  have h12 : u.getReg .x12=BitVec.ofNat 64 D := by rw [gr _ (by decide)];exact F.x12
  have h5 : u.getReg .x5=0 := by rw [gr _ (by decide)];exact F.x5
  have h11 : u.getReg .x11=64#64 := by rw [gr _ (by decide)];exact F.x11
  have hv : hashArgumentsValid u=true := hashArgs_const u A 64 D h10 h11 h12 F.aa (by norm_num) (by omega) F.da (by omega)
  have hq : hashInput u=toQ (pad64 input) := by
    rw [pad64_of_aligned _ (by rw [F.len])]
    refine hashInput_toQ u _ 0 A F.len h10 F.aa (by omega) h11 (by norm_num) ?_
    rw [frame_readWordsG hu.savedFrame A 8 (by omega) (fun i hi=>by omega)]
    exact F.words
  have hf : fetch im u=some (.base .ECALL) := (hc.fetch u hu.at_pc).trans rfl
  have hb : (toQ (pad64 input)).blocks=1 := by
    rw [pad64_of_aligned _ (by rw [F.len]),blocks_toQ ⟨by rw [F.len];omega,by rw [F.len]⟩,F.len]
  have he:=tb_pub (sk:=sk) (W:=3) (f:=fun a=>pure a) (Q:=Out s D) hf h5 hv hq (fun a=>?_)
  · simpa only [hb,bind_pure] using he
  let v:=writeHash u a
  have vp : v.pc=pcOf 26204 := by rw [pc_writeHash,hu.at_pc];decide
  have vo : done.res.obligs v := by simp [done.res,Result.obligs,Oblig.all]
  let t:=done.res.toState v
  have hs:=symRun_sound done hd v vp vo
  have fw:=Frame.writeHash u a D h12 (by omega)
  have keep : ∀ X,X<2048→v.getMem (BitVec.ofNat 64 X)=u.getMem (BitVec.ofNat 64 X) := by
    intro X hX;exact fw.get (by omega) (by omega)
  have tm : ∀ x,t.getMem x=v.getMem x := fun _=>rfl
  refine tb_pure_steps hs ⟨rfl,?_,?_,?_⟩
  · intro reg _
    by_cases hr : reg∈[Reg.x6,Reg.x7]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · change v.getMem 1152=s.getReg .x6
        change v.getMem 1152#64=_
        rw [keep _ (by decide)];exact hu.saved6
      · change v.getMem 1160=s.getReg .x7
        change v.getMem 1160#64=_
        rw [keep _ (by decide)];exact hu.saved7
    · have rd : RegsExcept v t [.x6,.x7] := by intro r hr;cases r <;> simp at hr <;> rfl
      rw [rd.get hr,getReg_writeHash,hu.regs.get hr]
  · intro k hk;rw [tm,getMem_writeHash u a D _ h12 (by omega) (by omega)]
    interval_cases k <;> simp
  · intro X hX hn
    rw [tm,fw.get hX (by omega)]
    exact hu.savedFrame X hX (by omega)

#print axioms run
end OuterSignPlain
