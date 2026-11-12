import SigGolfCandidate.OuterNodePreHash
import SigGolfCandidate.FtsExpandSearch
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeSearchInvariant
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind
open SphincsSecurity (bytesLE bytesLE_length)

structure Input (A D : Nat) (pre right : List UInt8) (s : MachineState) : Prop where
  x5 : s.getReg .x5=0
  x10 : s.getReg .x10=BitVec.ofNat 64 A
  x11 : s.getReg .x11=64
  x12 : s.getReg .x12=BitVec.ofNat 64 D
  pre_len : pre.length=32
  right_len : right.length=16
  pre_words : s.readWords (BitVec.ofNat 64 A) 4=wordsOf pre
  right_words : s.readWords (BitVec.ofNat 64 (A+48)) 2=wordsOf right
  alo : 2048≤A
  ahi : A<2^20
  aa : A%8=0
  dlo : 2048≤D
  dhi : D<2^20
  da : D%8=0
  disjoint : D+32≤A ∨ A+64≤D

def Work (A D X : Nat) : Prop := X=A+32 ∨ X=A+40 ∨ (D≤X ∧ X<D+32) ∨ X=1152 ∨ X=1160

structure Stage (s : MachineState) (A D : Nat) (pc : Word) (n : Nat) (t : MachineState) : Prop where
  at_pc : t.pc=pc
  regs : RegsExcept s t [.x6,.x7]
  nonce : t.getReg .x6=BitVec.ofNat 64 n
  saved6 : t.getMem 1152=s.getReg .x6
  saved7 : t.getMem 1160=s.getReg .x7
  pad40 : t.getMem (BitVec.ofNat 64 (A+40))=0
  frame : Frame s t (Work A D)

structure Answer (A D n : Nat) (a : HashOutput) (t : MachineState) : Prop where
  output : ∀ k<4,t.getMem (BitVec.ofNat 64 (D+8*k))=a.extractLsb' (64*k) 64
  pad32 : t.getMem (BitVec.ofNat 64 (A+32))=BitVec.ofNat 64 n
  pad40 : t.getMem (BitVec.ofNat 64 (A+40))=0

theorem pre_preserved {A D : Nat} {pre right : List UInt8} {s t : MachineState}
    (F : Input A D pre right s) (h : Frame s t (Work A D)) :
    t.readWords (BitVec.ofNat 64 A) 4=wordsOf pre := by
  rw [frame_readWordsG h A 4 (by have:=F.ahi;omega) (fun i hi=>by
    unfold Work;have:=F.disjoint;have:=F.alo;omega),F.pre_words]

theorem right_preserved {A D : Nat} {pre right : List UInt8} {s t : MachineState}
    (F : Input A D pre right s) (h : Frame s t (Work A D)) :
    t.readWords (BitVec.ofNat 64 (A+48)) 2=wordsOf right := by
  rw [frame_readWordsG h (A+48) 2 (by have:=F.ahi;omega) (fun i hi=>by
    unfold Work;have:=F.disjoint;have:=F.alo;omega),F.right_words]

theorem trial {im : Image} {sk : BitVec 256} {A D n : Nat} {pre right : List UInt8}
    {s u : MachineState} {pc : Word} (F : Input A D pre right s)
    (hc : CodeAt im pc OuterNodeMachineBlocks.b_preHashCode)
    (hu : Stage s A D pc n u) (hn : n<2^64)
    {β : Type} {W : Nat} {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (h : ∀ a t,Stage s A D (pc+8#64) n t → Answer A D n a t → TBSim im sk t W (f a) Q) :
    TBSim im sk u (9+W) (publicHash (trialInput pre n right) >>= f) Q := by
  have ha:=F.ahi;have hd:=F.dhi;have hlo:=F.alo;have hdl:=F.dlo;have hsep:=F.disjoint
  have g10 : u.getReg .x10=BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)];exact F.x10
  obtain ⟨v,hsteps,hpc,hr,hfetch,h32,hmem⟩:=OuterNodePreHash.runB pc hc u hu.at_pc A g10 ha hlo F.aa
  rw [hu.nonce] at h32
  have fv : Frame u v (fun X=>X=A+32) := by
    intro X hX hne
    apply hmem
    exact fun he=>hne ((ofNat_inj hX (by omega)).mp he)
  have fs : Frame s v (Work A D) := (hu.frame.trans fv).mono (by
    intro X _ hX;rcases hX with hX|hX;exact hX;exact Or.inl hX)
  have gr : ∀ r,r∉[Reg.x6,Reg.x7] → v.getReg r=s.getReg r := by
    intro r hr';rw [hr.get (by simp),hu.regs.get hr']
  have g12 : v.getReg .x12=BitVec.ofNat 64 D := by rw [gr _ (by decide)];exact F.x12
  have hl:=trialInput_length pre right n F.pre_len F.right_len
  have hq : hashInput v=toQ (pad64 (trialInput pre n right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ v _ 0 A hl (by rw [gr _ (by decide)];exact F.x10) F.aa (by omega)
      (by rw [gr _ (by decide)];exact F.x11) (by norm_num) ?_
    have p40 : v.getMem (BitVec.ofNat 64 (A+40))=0 := by
      rw [fv.get (by omega) (by omega)];exact hu.pad40
    rw [show 8*(0+1)=4+2+2 from rfl,readWords_add,readWords_add,
      pre_preserved F fs,show A+8*4=A+32 by ring,readWords_two,h32,p40,
      show A+32+8*2=A+48 by ring,right_preserved F fs,trialInput,
      wordsOf_append _ _ (by rw [List.length_append,F.pre_len];simp [nonceBytes,bytesLE_length]),
      wordsOf_append _ _ (by rw [F.pre_len]),nonce_words n hn]
  have hv : hashArgumentsValid v=true := hashArgs_const v A 64 D
    (by rw [gr _ (by decide)];exact F.x10) (by rw [gr _ (by decide)];exact F.x11)
    g12 F.aa (by norm_num) (by omega) F.da (by omega)
  have h5 : v.getReg .x5=0 := by rw [gr _ (by decide)];exact F.x5
  have e:=tb_pub (sk:=sk) (W:=W) (f:=f) (Q:=Q) hfetch h5 hv hq (fun a=>?_)
  · have e':=TBSim.steps hsteps e
    rw [trial_blocks pre right n F.pre_len F.right_len] at e'
    convert e' using 1 <;> omega
  have fw:=Frame.writeHash v a D g12 (by omega)
  have fsw : Frame s (writeHash v a) (Work A D) := (fs.trans fw).mono (by
    intro X _ hX;rcases hX with hX|hX;exact hX;exact Or.inr (Or.inr (Or.inl hX)))
  have keep : ∀ X,X<2^64 → X≠A+32 → ¬(D≤X ∧ X<D+32) →
      (writeHash v a).getMem (BitVec.ofNat 64 X)=u.getMem (BitVec.ofNat 64 X) := by
    intro X hX hne hD
    rw [fw.get hX hD,fv.get hX hne]
  refine h a (writeHash v a) ⟨?_,?_,?_,?_,?_,?_,fsw⟩ ⟨?_,?_,?_⟩
  · rw [pc_writeHash,hpc];simp only [BitVec.add_assoc];rfl
  · intro r hr';rw [getReg_writeHash,gr r hr']
  · rw [getReg_writeHash,hr.get (by simp)];exact hu.nonce
  · change (writeHash v a).getMem 1152#64=_
    rw [keep 1152 (by decide) (by omega) (by omega)];exact hu.saved6
  · change (writeHash v a).getMem 1160#64=_
    rw [keep 1160 (by decide) (by omega) (by omega)];exact hu.saved7
  · rw [fw.get (by omega) (by omega),fv.get (by omega) (by omega)];exact hu.pad40
  · intro k hk
    rw [getMem_writeHash v a D _ g12 (by omega) (by omega)]
    interval_cases k <;> simp <;> omega
  · rw [fw.get (by omega) (by omega)];exact h32
  · rw [fw.get (by omega) (by omega),fv.get (by omega) (by omega)];exact hu.pad40

theorem Stage.readOnly {s u t : MachineState} {A D n m : Nat} {pc pc' : Word}
    (hu : Stage s A D pc n u) (hp : t.pc=pc') (hr : RegsExcept u t [.x6,.x7])
    (hn : t.getReg .x6=BitVec.ofNat 64 m) (hm : ∀ a,t.getMem a=u.getMem a) :
    Stage s A D pc' m t := by
  refine ⟨hp,(fun reg hreg=>by rw [hr.get hreg,hu.regs.get hreg]),hn,?_,?_,?_,?_⟩
  · rw [hm];exact hu.saved6
  · rw [hm];exact hu.saved7
  · rw [hm];exact hu.pad40
  · intro X hX hne;rw [hm];exact hu.frame X hX hne

theorem Answer.readOnly {u t : MachineState} {A D n : Nat} {a : HashOutput}
    (h : Answer A D n a u) (hm : ∀ x,t.getMem x=u.getMem x) : Answer A D n a t := by
  refine ⟨fun k hk=>?_,?_,?_⟩
  · rw [hm];exact h.output k hk
  · rw [hm];exact h.pad32
  · rw [hm];exact h.pad40

theorem heap_preserved {A D : Nat} {pre right : List UInt8} {s t : MachineState}
    (F : Input A D pre right s) (h : Frame s t (Work A D)) :
    t.getMem (BitVec.ofNat 64 (A+24))=s.getMem (BitVec.ofNat 64 (A+24)) := by
  have:=F.ahi;have:=F.alo;have:=F.disjoint
  exact h.get (by omega) (by unfold Work;omega)

theorem save {im : Image} {A D : Nat} {pre right : List UInt8} {s : MachineState} {pc : Word}
    (F : Input A D pre right s) (hc : CodeAt im pc OuterNodeMachineBlocks.b_saveCode)
    (hp : s.pc=pc) :
    ∃ t,Steps im s 4 4 t ∧ Stage s A D (pc+16#64) 0 t := by
  let r : Result:={OuterNodeMachineBlocks.b_save.res with pc:=.c (pc+16#64)}
  have hv:=OuterNodeMachineSave.b_save_values s A F.x10 F.ahi F.alo
  refine ⟨r.toState s,symRun_sound (OuterNodeRelocate.b_save_at pc) hc s hp
    (OuterNodeMachineSave.b_save_obligs s A F.x10 F.ahi F.alo F.aa),rfl,?_,hv.2.2.2,hv.1,hv.2.1,hv.2.2.1,?_⟩
  · intro reg hr;cases reg <;> simp at hr <;> rfl
  · intro X hX hne
    apply OuterNodeMachineSave.b_save_frame
    have ha:=F.ahi
    refine ⟨?_,?_,?_⟩
    · intro he;exact hne (Or.inr (Or.inr (Or.inr (Or.inl ((ofNat_inj hX (by decide)).mp he)))))
    · intro he;exact hne (Or.inr (Or.inr (Or.inr (Or.inr ((ofNat_inj hX (by decide)).mp he)))))
    · rw [F.x10,ofNat_add_ofNat]
      intro he;exact hne (Or.inr (Or.inl ((ofNat_inj hX (by omega)).mp he)))

#print axioms save

#print axioms trial

#print axioms pre_preserved
#print axioms right_preserved
end OuterNodeSearchInvariant
