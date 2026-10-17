import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.H2FrontA


namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def afterCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x20e3303,0x7a031a63]
sym_block afterRun := symRun { noAlias := true } afterCode (pcOf 46509) 20

theorem after_steps {im : Image} (hc : CodeAt im (pcOf 46509) afterCode)
    (s : MachineState) (hpc : s.pc=pcOf 46509) :
    ∃t, Steps im s 4 4 t ∧
      t.pc=(if s.getMem 417824=0 then pcOf 46513 else pcOf 47005) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound afterRun hc s hpc (by simp [afterRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,afterRun.res]
    t3n []
    split_ifs <;> simp_all [pcOf]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    rfl

/-- Final pass (words 47005..47011; 47012 is the halting `ecall`): restore the L3 counter word at `WIT + 32` from
`0x66018` and, stage 2 (C3), the L3 encoding row tweak's high word at `WIT + 24` (a witness pad, honest LE64 1),
which the final clear of `[WIT, WIT + 8256)` erased; the halt flag `t0 = 1` is stored there (`sd t0,24(t4)` took the
place of the old no-op `addi t3,t3,0`). -/
def finishCode : List (BitVec 32) := bv_list% 32 [0x66e37,0x18e3303,0xfb040e93,0x26eb023,0x100293,0x5ebc23,0x513]
sym_block finishRun := symRun { noAlias := true } finishCode (pcOf 47005) 20

theorem finish_mem (s : MachineState) (h8 : s.getReg .x8=BitVec.ofNat 64 2984) (A : Nat) (hA : A < 2^64) :
    (finishRun.res.toState s).getMem (BitVec.ofNat 64 A) =
      if A = 2928 then 1#64 else if A = 2936 then s.getMem (BitVec.ofNat 64 417816) else s.getMem (BitVec.ofNat 64 A) := by
  simp only [Result.toState_getMem,finishRun.res]
  t3n [h8]
  rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
  all_goals (split_ifs <;> first | rfl | omega)
/-- Pairing stage 1: the final pass addresses the witness through `s0 = coordinateBase 8 = 2984` (`t4 = s0 - 80`).
Stated with `BitVec.ofNat` addresses (numeric `Word` literals here make the kernel recurse deeply). -/
theorem finish_steps {im : Image} (hc : CodeAt im (pcOf 47005) finishCode)
    (s : MachineState) (hpc : s.pc=pcOf 47005) (h8 : s.getReg .x8=BitVec.ofNat 64 2984) :
    ∃t, Steps im s 7 7 t ∧ t.pc=pcOf 47012 ∧
      t.getMem (BitVec.ofNat 64 2936)=s.getMem (BitVec.ofNat 64 417816) ∧ t.getMem (BitVec.ofNat 64 2928)=1#64 ∧
      t.getReg .x5=1#64 ∧ t.getReg .x10=0#64 ∧
      RegsExcept s t [.x5,.x6,.x10,.x28,.x29] ∧ Frame s t (fun A=>A=2936 ∨ A=2928) := by
  refine ⟨_,symRun_sound finishRun hc s hpc (by simp [finishRun.res,rv_simp,h8,accessValid_iff,MEMORY_BYTES]),?_,?_,?_,?_,?_,?_,?_⟩
  · simp [finishRun.res, Result.toState_pc, E.eval]
  · rw [finish_mem s h8 2936 (by norm_num), if_neg (by norm_num), if_pos rfl]
  · rw [finish_mem s h8 2928 (by norm_num), if_pos rfl]
  · simp [finishRun.res, rv_simp]
  · simp [finishRun.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    rw [finish_mem s h8 A hA, if_neg (by omega), if_neg (by omega)]
#print axioms after_steps
#print axioms finish_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Research.SharedPathPacking W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem coordRegion_source (k : Fin 9) : coordRegion k.val=2904+V3.regionOffset k.val := by
  fin_cases k <;> rfl

theorem coordPhysical_source (k raw : Nat) : coordPhysical k raw=SharedV3.physical k raw := by
  simp [coordPhysical,SharedV3.physical,SharedV3.first,SigGolfCandidate.Research.SharedForest.physicalChild]

theorem pathDestination_source (k : Fin 9) (child : Fin 128) (level : Fin 5) :
    pathDestination (coordRegion k.val) child.val (packedSlots child.val) level.val=
      2904+V3.regionOffset k.val+SharedV3.sibOff child.val level.val := by
  change destination (coordRegion k.val) (block child.val level.val/16) (child.val/2^level.val)=_
  rw [Packing.path_slot,coordRegion_source]
  simp only [sibling,bitAt,SharedV3.sibOff,SharedV3.blkOff,if_pos level.isLt]

theorem sixthDestination_source (k : Fin 9) (child : Fin 128) :
    destination (coordRegion k.val) 52 (child.val/32)=
      2904+V3.regionOffset k.val+SharedV3.sibOff child.val 5 := by
  rw [coordRegion_source]
  simp [destination,SharedV3.sibOff,SharedV3.blkOff,Nat.add_assoc]

theorem topDest_source (k : Fin 9) (child : Fin 128) :
    topDest k.val child.val=2904+SharedV3.topOtherOff k.val child.val := by
  have h : ∀k : Fin 9,∀child : Fin 128,
      topDest k.val child.val=2904+SharedV3.topOtherOff k.val child.val := by
    intro k;fin_cases k <;> decide +kernel
  exact h k child

theorem chainDestination_source (k : Fin 9) (i : Fin 6) :
    coordRegion k.val+(688-64*i.val)=2904+(V3.chainOffset k.val i.val+48) := by
  rw [coordRegion_source]
  simp only [V3.chainOffset]
  have := i.isLt
  omega

theorem leafDestination_source (k : Fin 9) (i : Fin 6) (hi : 0 < i.val) :
    coordRegion k.val+720+16*i.val=2904+(V3.regionOffset k.val+V3.leafSlot i.val) := by
  rw [coordRegion_source]
  simp [V3.leafSlot,Nat.ne_of_gt hi,Nat.add_assoc]

theorem topInput_source (k : Fin 9) : topInput k.val=96+16*(SharedV3.lastLevel k.val+1) := by
  fin_cases k <;> rfl
#print axioms pathDestination_source
#print axioms topDest_source
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

structure SourceReadout (w : W9Machine.WBytes) (s : MachineState) (k child : Nat) : Prop where
  values : ∀i<6,DigAt s (coordSource k+16*i) (wdig w (V3.chainOffset k i+48))
  ends : ∀i<6,0 < i → DigAt s (coordSource k+16*i) (wdig w (V3.regionOffset k+V3.leafSlot i))
  paths : ∀i<5,DigAt s (coordSource k+96+16*i) (wdig w (V3.regionOffset k+SharedV3.sibOff child i))
  sixth : ¬firstCoord k → DigAt s (coordSource k+176) (wdig w (V3.regionOffset k+SharedV3.sibOff child 5))
  top : DigAt s (coordSource k+topInput k) (wdig w (SharedV3.topOtherOff k child))

theorem orig_word {w : W9Machine.WBytes} {t : MachineState} (off half : Nat) (hh : half<2)
    (hm : t.getMem (BitVec.ofNat 64 (2904+off+8*half))=(wdig w off).extractLsb' (64*half) 64) :
    W9Machine.OrigW w t (2904+off+8*half) := by
  unfold W9Machine.OrigW
  rw [hm]
  interval_cases half
  · simpa using (W9Machine.wdig_lo w off)
  · simpa [Nat.add_assoc] using (W9Machine.wdig_hi w off)

theorem digAt_half {t : MachineState} {A : Nat} {d : BitVec 128} (h : DigAt t A d)
    (half : Nat) (hh : half<2) :
    t.getMem (BitVec.ofNat 64 (A+8*half))=d.extractLsb' (64*half) 64 := by
  interval_cases half
  · simpa using h.1
  · simpa using h.2

theorem CoordinateReadout.original {s t : MachineState} {w : W9Machine.WBytes}
    (k : Fin 9) (child : Fin 128) (h : CoordinateReadout s k.val child.val t)
    (hs : SourceReadout w s k.val child.val) (A : Nat) (hA : PreciseCoordinateW k.val child.val A) :
    W9Machine.OrigW w t A := by
  have hv : ∀i<6,∀half<2,W9Machine.OrigW w t (coordRegion k.val+(688-64*i)+8*half) := by
    intro i hi half hh
    rw [chainDestination_source k ⟨i,hi⟩]
    apply orig_word _ half hh
    rw [←chainDestination_source k ⟨i,hi⟩,h.values i hi half hh]
    exact digAt_half (hs.values i hi) half hh
  have he : ∀i<6,0 < i → ∀half<2,W9Machine.OrigW w t (coordRegion k.val+720+16*i+8*half) := by
    intro i hi hip half hh
    rw [leafDestination_source k ⟨i,hi⟩ hip]
    apply orig_word _ half hh
    rw [←leafDestination_source k ⟨i,hi⟩ hip,h.ends i hi hip half hh]
    exact digAt_half (hs.ends i hi hip) half hh
  have hp : ∀i<5,∀half<2,W9Machine.OrigW w t (pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+8*half) := by
    intro i hi half hh
    rw [pathDestination_source k child ⟨i,hi⟩]
    rw [Nat.add_assoc 2904]
    apply orig_word _ half hh
    rw [←Nat.add_assoc 2904,←pathDestination_source k child ⟨i,hi⟩,h.paths i hi half hh]
    exact digAt_half (hs.paths i hi) half hh
  have h6 : ¬firstCoord k.val → ∀half<2,W9Machine.OrigW w t (destination (coordRegion k.val) 52 (child.val/32)+8*half) := by
    intro hn half hh
    rw [sixthDestination_source k child,Nat.add_assoc 2904]
    apply orig_word _ half hh
    rw [←Nat.add_assoc 2904,←sixthDestination_source k child,h.sixth hn half hh]
    exact digAt_half (hs.sixth hn) half hh
  have ht : ∀half<2,W9Machine.OrigW w t (topDest k.val child.val+8*half) := by
    intro half hh
    rw [topDest_source k child]
    apply orig_word _ half hh
    rw [←topDest_source k child,h.top half hh]
    exact digAt_half hs.top half hh
  rcases hA with ((ha|ha)|ha)|ha|ha
  · obtain ⟨i,hi,ha⟩:=ha
    rcases ha with ha|ha|⟨hip,ha|ha⟩
    · subst A;simpa using hv i hi 0 (by decide)
    · rw [ha,show coordRegion k.val+(696-64*i)=coordRegion k.val+(688-64*i)+8 by omega]
      simpa using hv i hi 1 (by decide)
    · subst A;simpa using he i hi hip 0 (by decide)
    · rw [ha,show coordRegion k.val+728+16*i=coordRegion k.val+720+16*i+8 by omega]
      simpa using he i hi hip 1 (by decide)
  · obtain ⟨i,hi,ha|ha⟩:=ha
    · subst A;simpa using hp i hi 0 (by decide)
    · subst A;simpa using hp i hi 1 (by decide)
  · obtain ⟨hn,ha|ha⟩:=ha
    · subst A;simpa using h6 hn 0 (by decide)
    · subst A;simpa using h6 hn 1 (by decide)
  · subst A;simpa using ht 0 (by decide)
  · subst A;simpa using ht 1 (by decide)
#print axioms CoordinateReadout.original
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedZero
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def words : List (BitVec 32) := [0xe3023,0x8e0e13,0xffde6ce3]
sym_block zeroRun := symRun {noAlias:=true} words (pcOf 45254) 10

def result (p : Word) : Result :=
  ⟨zeroRun.res.st,
    .ite .ltu (.bin .add (.reg .x28) (.c 8)) (.reg .x29)
      (.c (((p+4)+4)+18446744073709551608)) (.c (((p+4)+4)+4)),.branch,3,3⟩
theorem checked (p : Word) : symRun {noAlias:=true} words p 10=some (result p) := by krfl

theorem step {im : Image} (p : Word) (hc : CodeAt im p words)
    (s : MachineState) (hpc : s.pc=p) (A B : Nat)
    (ha : A%8=0) (hb : A+8≤B) (hB : B≤11064)
    (h28 : s.getReg .x28=BitVec.ofNat 64 A) (h29 : s.getReg .x29=BitVec.ofNat 64 B) :
    ∃t, Steps im s 3 3 t ∧ t.pc=(if A+8<B then p else p+12) ∧
      t.getReg .x28=BitVec.ofNat 64 (A+8) ∧ t.getMem (BitVec.ofNat 64 A)=0 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun x=>x=A) := by
  refine ⟨_,symRun_sound (checked p) hc s hpc ?_,?_,?_,?_,?_,?_⟩
  · simp [result,zeroRun.res,rv_simp,h28,accessValid_iff,MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc,result,E.eval,BinOp.eval,CmpOp.eval,h28,h29]
    rw [show (BitVec.ofNat 64 A+8 : Word)=BitVec.ofNat 64 (A+8) by simp [BitVec.ofNat_add]]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show A+8<2^64 by omega),Nat.mod_eq_of_lt (show B<2^64 by omega)]
    have hback : ((p+4)+4)+18446744073709551608=p := by
      simp only [BitVec.add_assoc]; change p+0=p;exact BitVec.add_zero p
    have hnext : ((p+4)+4)+4=p+12 := by simp only [BitVec.add_assoc];rfl
    rw [hback,hnext]
    split_ifs <;> simp_all
  · simp only [Result.toState_getReg,result,zeroRun.res]
    t3n [h28]
  · simp only [Result.toState_getMem,result,zeroRun.res]
    t3n [h28]
    simp
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro x hx hn
    simp only [Result.toState_getMem,result,zeroRun.res]
    t3n [h28]
    simp only [Nat.add_zero,Nat.mod_eq_of_lt (show x<18446744073709551616 by simpa using hx),Nat.mod_eq_of_lt (show A<18446744073709551616 by omega),if_neg hn]

theorem loop {im : Image} (p : Word) (hc : CodeAt im p words) (A : Nat) (ha : A%8=0) :
    ∀n (s : MachineState), A+8*(n+1)≤11064 → s.pc=p →
      s.getReg .x28=BitVec.ofNat 64 A → s.getReg .x29=BitVec.ofNat 64 (A+8*(n+1)) →
      ∃t,Steps im s (3*(n+1)) (3*(n+1)) t ∧ t.pc=p+12 ∧
        t.getReg .x28=BitVec.ofNat 64 (A+8*(n+1)) ∧
        (∀i<n+1,t.getMem (BitVec.ofNat 64 (A+8*i))=0) ∧
        RegsExcept s t [.x28] ∧ Frame s t (fun x=>A≤x ∧ x<A+8*(n+1)) := by
  intro n
  induction n generalizing A with
  | zero =>
    intro s hbound hp h28 h29
    obtain ⟨t,st,pt,rt,mt,rr,ff⟩:=step p hc s hp A (A+8) ha (by omega) (by omega) h28 (by simpa using h29)
    refine ⟨t,by simpa using st,?_,?_,?_,rr,ff.mono ?_⟩
    · simpa using pt
    · simpa using rt
    · intro i hi
      have : i=0 := by omega
      simpa [this] using mt
    · intro x hx he;omega
  | succ n ih =>
    intro s hbound hp h28 h29
    obtain ⟨u,su,pu,r28,mu,ru,fu⟩:=step p hc s hp A (A+8*(n+2)) ha (by omega) hbound h28 h29
    have hp' : u.pc=p := by simpa [show A+8<A+8*(n+2) by omega] using pu
    have h29' : u.getReg .x29=BitVec.ofNat 64 ((A+8)+8*(n+1)) := by
      rw [ru.get (by decide),h29]
      congr 1;omega
    obtain ⟨t,ut,pt,rt,mt,rr,ft⟩:=ih (A+8) (by omega) u (by omega) hp' r28 h29'
    refine ⟨t,?_,pt,?_,?_,(ru.trans rr).mono (by decide),?_⟩
    · convert su.trans ut using 1 <;> omega
    · convert rt using 2 <;> omega
    · intro i hi
      cases i with
      | zero => simpa using (ft.get (by omega) (by omega)).trans mu
      | succ i => simpa [Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using mt i (by omega)
    · exact (fu.trans ft).mono (by intro x hx h;rcases h with h|h <;> omega)
#print axioms checked
#print axioms step
#print axioms loop
end ClaudeWCT.W9.Machine.Expand.SharedZero

namespace ClaudeWCT.W9.Machine.Expand.SharedZero
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def acceptedCode : List (BitVec 32) := [0x66e37,0xe0e13,0x20e3023,0x13e3423,0x8bb03,0x21b5b13,0x16e3823,0x20eb7,0x550e8e93,0x16eb023,0x6000e93,0x8b303,0x6eb023,0x88b303,0x6eb423,0x108b303,0x6eb823,0x188b303,0x6ebc23,0x48000e13,0x3eb7,0xb38e8e93]
sym_block acceptedRun := symRun {noAlias:=true} acceptedCode (pcOf 45232) 100
def finalScatterCode : List (BitVec 32) := [0x48000e13,0x20e3303,0x66eb7,0xe8e93,0x6ebc23,0x100313,0x26eb023,0x6000e13,0x20eb7,0x160e8e93,0xe3303,0x6eb023,0x8e3303,0x6eb423,0x10e3303,0x6eb823,0x18e3303,0x6ebc23,0x48000e13,0x3eb7,0xaf8e8e93]
sym_block finalScatterRun := symRun {noAlias:=true} finalScatterCode (pcOf 46980) 100

theorem accepted_steps {im : Image} (hc : CodeAt im (pcOf 45232) acceptedCode)
    (s : MachineState) (hpc : s.pc=pcOf 45232) (h17 : s.getReg .x17=0x20160) :
    ∃t,Steps im s 22 22 t ∧ t.pc=pcOf 45254 ∧
      t.getReg .x28=1152 ∧ t.getReg .x29=11064 ∧
      t.getMem 0x66020=0 ∧ t.getMem 0x66008=s.getReg .x19 ∧
      t.getMem 0x66010=s.getMem 0x20160 >>> 33 ∧
      t.getMem 0x20550=s.getMem 0x20160 >>> 33 ∧
      (∀i<4,t.getMem (BitVec.ofNat 64 (96+8*i))=s.getMem (BitVec.ofNat 64 (0x20160+8*i))) ∧
      RegsExcept s t [.x6,.x22,.x28,.x29] ∧
      Frame s t (fun A=>A=0x66020 ∨ A=0x66008 ∨ A=0x66010 ∨ A=0x20550 ∨ (96≤A ∧ A<128)) := by
  refine ⟨_,symRun_sound acceptedRun hc s hpc ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [acceptedRun.res,rv_simp,h17,accessValid_iff,MEMORY_BYTES]
  · rfl
  · rfl
  · rfl
  · simp [acceptedRun.res,rv_simp,h17]
  · simp [acceptedRun.res,rv_simp,h17]
  · simp [acceptedRun.res,rv_simp,h17]
  · simp [acceptedRun.res,rv_simp,h17]
  · intro i hi
    interval_cases i <;> simp [acceptedRun.res,rv_simp,h17]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,acceptedRun.res]
    t3n [h17]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    split_ifs <;> first | rfl | omega

theorem finalScatter_steps {im : Image} (hc : CodeAt im (pcOf 46980) finalScatterCode)
    (s : MachineState) (hpc : s.pc=pcOf 46980) :
    ∃t,Steps im s 21 21 t ∧ t.pc=pcOf 47001 ∧
      t.getReg .x28=1152 ∧ t.getReg .x29=11000 ∧
      t.getMem 0x66018=s.getMem 1184 ∧ t.getMem 0x66020=1 ∧
      (∀i<4,t.getMem (BitVec.ofNat 64 (0x20160+8*i))=s.getMem (BitVec.ofNat 64 (96+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧
      Frame s t (fun A=>A=0x66018 ∨ A=0x66020 ∨ (0x20160≤A ∧ A<0x20180)) := by
  refine ⟨_,symRun_sound finalScatterRun hc s hpc ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [finalScatterRun.res,rv_simp,accessValid_iff,MEMORY_BYTES]
  · rfl
  · rfl
  · rfl
  · simp [finalScatterRun.res,rv_simp]
  · simp [finalScatterRun.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [finalScatterRun.res,rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,finalScatterRun.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    split_ifs <;> first | rfl | omega
#print axioms accepted_steps
#print axioms finalScatter_steps
end ClaudeWCT.W9.Machine.Expand.SharedZero

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def first0Code : List (BitVec 32) := [0x66e37,0xe0e13,0x40e3303,0x1536663]
sym_block first0Run := symRun {noAlias:=true} first0Code (pcOf 46933) 20
def zero0Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero0Run := symRun {noAlias:=true} zero0Code (pcOf 46937) 20
def sub0Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub0Run := symRun {noAlias:=true} sub0Code (pcOf 46939) 20
theorem first0_steps {im : Image} (hc : CodeAt im (pcOf 46933) first0Code)
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46939 else pcOf 46937) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417856#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first0Run hc s hp (by simp [first0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first0Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first0Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero0_steps {im : Image} (hc : CodeAt im (pcOf 46937) zero0Code)
    (s : MachineState) (hp : s.pc=pcOf 46937) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero0Run hc s hp (by simp [zero0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub0_steps {im : Image} (hc : CodeAt im (pcOf 46939) sub0Code)
    (s : MachineState) (hp : s.pc=pcOf 46939) (R C : Nat) (hR : R≤63) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub0Run hc s hp (by simp [sub0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub0Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual0Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46933) first0Code
  zero : CodeAt im (pcOf 46937) zero0Code
  sub : CodeAt im (pcOf 46939) sub0Code

theorem residual0_steps {im : Image} [hc : Residual0Code im]
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first0_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub0_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero0_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
#print axioms residual0_steps
def first1Code : List (BitVec 32) := [0x66e37,0xe0e13,0x48e3303,0x1536663]
sym_block first1Run := symRun {noAlias:=true} first1Code (pcOf 46949) 20
def zero1Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero1Run := symRun {noAlias:=true} zero1Code (pcOf 46953) 20
def sub1Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub1Run := symRun {noAlias:=true} sub1Code (pcOf 46955) 20
theorem first1_steps {im : Image} (hc : CodeAt im (pcOf 46949) first1Code)
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46955 else pcOf 46953) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417864#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first1Run hc s hp (by simp [first1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first1Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first1Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero1_steps {im : Image} (hc : CodeAt im (pcOf 46953) zero1Code)
    (s : MachineState) (hp : s.pc=pcOf 46953) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero1Run hc s hp (by simp [zero1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub1_steps {im : Image} (hc : CodeAt im (pcOf 46955) sub1Code)
    (s : MachineState) (hp : s.pc=pcOf 46955) (R C : Nat) (hR : R≤63) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub1Run hc s hp (by simp [sub1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub1Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual1Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46949) first1Code
  zero : CodeAt im (pcOf 46953) zero1Code
  sub : CodeAt im (pcOf 46955) sub1Code

theorem residual1_steps {im : Image} [hc : Residual1Code im]
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first1_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub1_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero1_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
#print axioms residual1_steps
def first2Code : List (BitVec 32) := [0x66e37,0xe0e13,0x50e3303,0x1536663]
sym_block first2Run := symRun {noAlias:=true} first2Code (pcOf 46966) 20
def zero2Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero2Run := symRun {noAlias:=true} zero2Code (pcOf 46970) 20
def sub2Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub2Run := symRun {noAlias:=true} sub2Code (pcOf 46972) 20
theorem first2_steps {im : Image} (hc : CodeAt im (pcOf 46966) first2Code)
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46972 else pcOf 46970) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417872#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first2Run hc s hp (by simp [first2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first2Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first2Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero2_steps {im : Image} (hc : CodeAt im (pcOf 46970) zero2Code)
    (s : MachineState) (hp : s.pc=pcOf 46970) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero2Run hc s hp (by simp [zero2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub2_steps {im : Image} (hc : CodeAt im (pcOf 46972) sub2Code)
    (s : MachineState) (hp : s.pc=pcOf 46972) (R C : Nat) (hR : R≤63) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub2Run hc s hp (by simp [sub2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub2Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual2Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46966) first2Code
  zero : CodeAt im (pcOf 46970) zero2Code
  sub : CodeAt im (pcOf 46972) sub2Code

theorem residual2_steps {im : Image} [hc : Residual2Code im]
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first2_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub2_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero2_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
#print axioms residual2_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def initCode : List (BitVec 32) := [0x66e37,0xe0e13,0xe3a03,0x3f00a93]
sym_block initRun := symRun {noAlias:=true} initCode (pcOf 46929) 100
def range1Code : List (BitVec 32) := [0x3000393,0x87afc63]
sym_block range1Run := symRun {noAlias:=true} range1Code (pcOf 46940) 100
def range2Code : List (BitVec 32) := [0x2300393,0x47afc63]
sym_block range2Run := symRun {noAlias:=true} range2Code (pcOf 46956) 100
def range3Code : List (BitVec 32) := [0x1200393,0x7afa63]
sym_block range3Run := symRun {noAlias:=true} range3Code (pcOf 46973) 100
def lastCode : List (BitVec 32) := [0x14400393,0x27a5eb3,0x1da9463]
sym_block lastRun := symRun {noAlias:=true} lastCode (pcOf 46975) 100
def goodCode : List (BitVec 32) := [0xea5fb06f]
sym_block goodRun := symRun {noAlias:=true} goodCode (pcOf 46978) 100
def badCode : List (BitVec 32) := [0xf7cd206f]
sym_block badRun := symRun {noAlias:=true} badCode (pcOf 46979) 100
theorem range1_steps {im : Image} (hc : CodeAt im (pcOf 46940) range1Code)
    (s : MachineState) (hp : s.pc=pcOf 46940) (R : Nat) (hR : R≤63)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<48 then pcOf 46942 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range1Run hc s hp (by simp [range1Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range1Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<48 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms range1_steps
theorem range2_steps {im : Image} (hc : CodeAt im (pcOf 46956) range2Code)
    (s : MachineState) (hp : s.pc=pcOf 46956) (R : Nat) (hR : R≤63)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<35 then pcOf 46958 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range2Run hc s hp (by simp [range2Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range2Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<35 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms range2_steps
theorem range3_steps {im : Image} (hc : CodeAt im (pcOf 46973) range3Code)
    (s : MachineState) (hp : s.pc=pcOf 46973) (R : Nat) (hR : R≤63)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<18 then pcOf 46975 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range3Run hc s hp (by simp [range3Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range3Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<18 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms range3_steps
theorem init_steps {im : Image} (hc : CodeAt im (pcOf 46929) initCode)
    (s : MachineState) (hp : s.pc=pcOf 46929) (hints : Nat)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃t,Steps im s 4 4 t ∧ t.pc=pcOf 46933 ∧ t.getReg .x20=BitVec.ofNat 64 hints ∧
      t.getReg .x21=63 ∧ RegsExcept s t [.x20,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound initRun hc s hp (by simp [initRun.res,rv_simp]),rfl,?_,rfl,?_,?_⟩
  · simp [initRun.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms init_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open RiscvZkvm.Rv64
theorem rem18 (n : Nat) (hn : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 18#64=BitVec.ofNat 64 (n%18) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_remu,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n%18<2^64 by omega)]
  omega
theorem div18 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 18#64=BitVec.ofNat 64 (n/18) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/18<2^64 by omega)]
  omega
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def lookup1PreCode : List (BitVec 32) := [0xff9e37,0x390e0e13,0x15e0e33]
sym_block lookup1PreRun := symRun {noAlias:=true} lookup1PreCode (pcOf 46942) 100
def lookup1LoadCode : List (BitVec 32) := [0xe4303]
def lookup1PostCode : List (BitVec 32) := [0x1200393,0x27a7eb3,0x7d31e63]
sym_block lookup1PostRun := symRun {noAlias:=true} lookup1PostCode (pcOf 46946) 100
theorem lookup1_pre {im : Image} (hc : CodeAt im (pcOf 46942) lookup1PreCode)
    (s : MachineState) (hp : s.pc=pcOf 46942) (R : Nat) (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 46945 ∧ t.getReg .x28=BitVec.ofNat 64 (16749456+R) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup1PreRun hc s hp (by simp [lookup1PreRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [lookup1PreRun.res,rv_simp,h21,BitVec.ofNat_add,add_comm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem lookup1_load {im : Image} (hc : CodeAt im (pcOf 46945) lookup1LoadCode)
    (s : MachineState) (hp : s.pc=pcOf 46945) (a F : Nat) (ha : a+1≤2^24) (hF : F<256)
    (h28 : s.getReg .x28=BitVec.ofNat 64 a) (hm : s.getByte (BitVec.ofNat 64 a)=BitVec.ofNat 8 F) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46946 ∧ t.getReg .x6=BitVec.ofNat 64 F ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hoff : s.getReg .x28+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 a := by
    rw [h28];apply BitVec.eq_of_toNat_eq;simp [signExtend12]
  have st:=steps_lbu (rd:=.x6) (rs:=.x28) (off:=0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by omega)];simp [MEMORY_BYTES];omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 46946;rw [hp];rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn;simp

theorem lookup1_post {im : Image} (hc : CodeAt im (pcOf 46946) lookup1PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46946) (H F : Nat) (hH : H<5832) (hF : F<18)
    (h6 : s.getReg .x6=BitVec.ofNat 64 F) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 3 6 t ∧ t.pc=(if F=H%18 then pcOf 46949 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup1PostRun hc s hp (by simp [lookup1PostRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lookup1PostRun.res]
    t3n [h6,h20]
    simp only [div18 H (by omega),rem18 H (by omega),rem18 (H/18) (by omega)]
    have he : (BitVec.ofNat 64 F=BitVec.ofNat 64 (H%18)) ↔ F=H%18 := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : F=H%18 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms lookup1_pre
#print axioms lookup1_load
#print axioms lookup1_post
def lookup2PreCode : List (BitVec 32) := [0xff9e37,0x3d0e0e13,0x15e0e33]
sym_block lookup2PreRun := symRun {noAlias:=true} lookup2PreCode (pcOf 46958) 100
def lookup2LoadCode : List (BitVec 32) := [0xe4303]
def lookup2PostCode : List (BitVec 32) := [0x1200393,0x27a5eb3,0x27efeb3,0x3d31c63]
sym_block lookup2PostRun := symRun {noAlias:=true} lookup2PostCode (pcOf 46962) 100
theorem lookup2_pre {im : Image} (hc : CodeAt im (pcOf 46958) lookup2PreCode)
    (s : MachineState) (hp : s.pc=pcOf 46958) (R : Nat) (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 46961 ∧ t.getReg .x28=BitVec.ofNat 64 (16749520+R) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup2PreRun hc s hp (by simp [lookup2PreRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [lookup2PreRun.res,rv_simp,h21,BitVec.ofNat_add,add_comm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem lookup2_load {im : Image} (hc : CodeAt im (pcOf 46961) lookup2LoadCode)
    (s : MachineState) (hp : s.pc=pcOf 46961) (a F : Nat) (ha : a+1≤2^24) (hF : F<256)
    (h28 : s.getReg .x28=BitVec.ofNat 64 a) (hm : s.getByte (BitVec.ofNat 64 a)=BitVec.ofNat 8 F) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46962 ∧ t.getReg .x6=BitVec.ofNat 64 F ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hoff : s.getReg .x28+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 a := by
    rw [h28];apply BitVec.eq_of_toNat_eq;simp [signExtend12]
  have st:=steps_lbu (rd:=.x6) (rs:=.x28) (off:=0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by omega)];simp [MEMORY_BYTES];omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 46962;rw [hp];rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn;simp

theorem lookup2_post {im : Image} (hc : CodeAt im (pcOf 46962) lookup2PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46962) (H F : Nat) (hH : H<5832) (hF : F<18)
    (h6 : s.getReg .x6=BitVec.ofNat 64 F) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 4 10 t ∧ t.pc=(if F=H/18%18 then pcOf 46966 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup2PostRun hc s hp (by simp [lookup2PostRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lookup2PostRun.res]
    t3n [h6,h20]
    simp only [div18 H (by omega),rem18 (H/18) (by omega)]
    have he : (BitVec.ofNat 64 F=BitVec.ofNat 64 (H/18%18)) ↔ F=H/18%18 := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : F=H/18%18 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms lookup2_pre
#print axioms lookup2_load
#print axioms lookup2_post
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
theorem lookup1_steps {im : Image}
    (hpre : CodeAt im (pcOf 46942) lookup1PreCode)
    (hload : CodeAt im (pcOf 46945) lookup1LoadCode)
    (hpost : CodeAt im (pcOf 46946) lookup1PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46942) (R H F : Nat) (hR : R<48) (hH : H<5832) (hF : F<18)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getByte (BitVec.ofNat 64 (16749456+R))=BitVec.ofNat 8 F) :
    ∃t,Steps im s 7 10 t ∧ t.pc=(if F=H%18 then pcOf 46949 else pcOf 46979) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u28,ru,fu⟩:=lookup1_pre hpre s hp R h21
  obtain ⟨v,sv,pv,v6,rv,fv⟩:=lookup1_load hload u pu (16749456+R) F (by omega) (by omega) u28
    (by rw [fu.getByte (by omega) (by simp)];exact hm)
  obtain ⟨t,st,pt,rt,ft⟩:=lookup1_post hpost v pv H F hH hF v6
    (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
  exact ⟨t,(su.trans sv).trans st,pt,((ru.trans rv).trans rt).mono (by decide),
    ((fu.trans fv).trans ft).mono (by simp)⟩
#print axioms lookup1_steps
theorem lookup2_steps {im : Image}
    (hpre : CodeAt im (pcOf 46958) lookup2PreCode)
    (hload : CodeAt im (pcOf 46961) lookup2LoadCode)
    (hpost : CodeAt im (pcOf 46962) lookup2PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46958) (R H F : Nat) (hR : R<35) (hH : H<5832) (hF : F<18)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getByte (BitVec.ofNat 64 (16749520+R))=BitVec.ofNat 8 F) :
    ∃t,Steps im s 8 14 t ∧ t.pc=(if F=H/18%18 then pcOf 46966 else pcOf 46979) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u28,ru,fu⟩:=lookup2_pre hpre s hp R h21
  obtain ⟨v,sv,pv,v6,rv,fv⟩:=lookup2_load hload u pu (16749520+R) F (by omega) (by omega) u28
    (by rw [fu.getByte (by omega) (by simp)];exact hm)
  obtain ⟨t,st,pt,rt,ft⟩:=lookup2_post hpost v pv H F hH hF v6
    (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
  exact ⟨t,(su.trans sv).trans st,pt,((ru.trans rv).trans rt).mono (by decide),
    ((fu.trans fv).trans ft).mono (by simp)⟩
#print axioms lookup2_steps
theorem div324 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 324#64=BitVec.ofNat 64 (n/324) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/324<2^64 by omega)]
  omega

theorem last_steps {im : Image} (hc : CodeAt im (pcOf 46975) lastCode)
    (s : MachineState) (hp : s.pc=pcOf 46975) (R H : Nat) (hR : R≤63) (hH : H<5832)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 3 6 t ∧ t.pc=(if H/324=R then pcOf 46978 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lastRun hc s hp (by simp [lastRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lastRun.res]
    t3n [h21,h20]
    rw [div324 H (by omega)]
    have he : (BitVec.ofNat 64 R=BitVec.ofNat 64 (H/324)) ↔ H/324=R := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : H/324=R <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem good_steps {im : Image} (hc : CodeAt im (pcOf 46978) goodCode) (s : MachineState) (hp : s.pc=pcOf 46978) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 42795 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  exact ⟨_,symRun_sound goodRun hc s hp (by simp [goodRun.res,rv_simp]),rfl,fun r _=>by cases r <;> rfl,fun A _ _=>rfl⟩
theorem bad_steps {im : Image} (hc : CodeAt im (pcOf 46979) badCode) (s : MachineState) (hp : s.pc=pcOf 46979) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 354 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  exact ⟨_,symRun_sound badRun hc s hp (by simp [badRun.res,rv_simp]),rfl,fun r _=>by cases r <;> rfl,fun A _ _=>rfl⟩
#print axioms last_steps
#print axioms good_steps
#print axioms bad_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
structure Code (im : Image) : Prop where
  init : CodeAt im (pcOf 46929) initCode
  r0 : Residual0Code im
  r1 : Residual1Code im
  r2 : Residual2Code im
  range1 : CodeAt im (pcOf 46940) range1Code
  range2 : CodeAt im (pcOf 46956) range2Code
  range3 : CodeAt im (pcOf 46973) range3Code
  lookup1Pre : CodeAt im (pcOf 46942) lookup1PreCode
  lookup1Load : CodeAt im (pcOf 46945) lookup1LoadCode
  lookup1Post : CodeAt im (pcOf 46946) lookup1PostCode
  lookup2Pre : CodeAt im (pcOf 46958) lookup2PreCode
  lookup2Load : CodeAt im (pcOf 46961) lookup2LoadCode
  lookup2Post : CodeAt im (pcOf 46962) lookup2PostCode
  last : CodeAt im (pcOf 46975) lastCode
  good : CodeAt im (pcOf 46978) goodCode
  bad : CodeAt im (pcOf 46979) badCode

def regs : List Reg := [.x6,.x7,.x21,.x28,.x29]
theorem phase1_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C H : Nat) (hR : R≤63) (hC : C<2^64) (hH : H<5832)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417856#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<48 → T r<18)
    (hbytes : ∀ r,r<48 → s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤15 ∧ c≤18 ∧ Steps im s n c t ∧
      t.pc=(if R-C<48 ∧ H%18=T (R-C) then pcOf 46949 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r0
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual0_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range1_steps hc.range1 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<48
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup1_steps hc.lookup1Pre hc.lookup1Load hc.lookup1Post v pv
      (R-C) H (T (R-C)) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+7,n+2+10,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
#print axioms phase1_steps
theorem phase2_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C H : Nat) (hR : R≤63) (hC : C<2^64) (hH : H<5832)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417864#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<35 → T r<18)
    (hbytes : ∀ r,r<35 → s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤16 ∧ c≤22 ∧ Steps im s n c t ∧
      t.pc=(if R-C<35 ∧ H/18%18=T (R-C) then pcOf 46966 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r1
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual1_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range2_steps hc.range2 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<35
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup2_steps hc.lookup2Pre hc.lookup2Load hc.lookup2Post v pv
      (R-C) H (T (R-C)) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+8,n+2+14,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
#print axioms phase2_steps
theorem phase3_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C H : Nat) (hR : R≤63) (hC : C<2^64) (hH : H<5832)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417872#64)=BitVec.ofNat 64 C) :
    ∃t n c,n≤11 ∧ c≤14 ∧ Steps im s n c t ∧
      t.pc=(if R-C<18 ∧ H/324=R-C then pcOf 46978 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r2
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual2_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range3_steps hc.range3 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<18
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=last_steps hc.last v pv (R-C) H (by omega) hH
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
    refine ⟨t,n+2+3,n+2+6,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
#print axioms phase3_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

abbrev Condition (H C0 C1 C2 : Nat) (T1 T2 : Nat→Nat) : Prop :=
  let R1:=63-C0
  let R2:=R1-C1
  let R3:=R2-C2
  R1<48 ∧ R2<35 ∧ R3<18 ∧ H%18=T1 R1 ∧ H/18%18=T2 R2 ∧ H/324=R3

theorem validate_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (H C0 C1 C2 : Nat)
    (hH : H<5832) (hC0 : C0<2^64) (hC1 : C1<2^64) (hC2 : C2<2^64)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 H)
    (hm0 : s.getMem (417856#64)=BitVec.ofNat 64 C0)
    (hm1 : s.getMem (417864#64)=BitVec.ofNat 64 C1)
    (hm2 : s.getMem (417872#64)=BitVec.ofNat 64 C2)
    (T1 T2 : Nat→Nat) (ht1 : ∀r,r<48→T1 r<18) (ht2 : ∀r,r<35→T2 r<18)
    (hb1 : ∀r,r<48→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T1 r))
    (hb2 : ∀r,r<35→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T2 r)) :
    ∃t n c,n≤47 ∧ c≤59 ∧ Steps im s n c t ∧
      t.pc=(if Condition H C0 C1 C2 T1 T2 then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u20,u21,ru,fu⟩:=init_steps hc.init s hp H hm
  obtain ⟨v,n1,c1,hn1,hc1,sv,pv,v21,rv,fv⟩:=phase1_steps hc u pu 63 C0 H (by omega) hC0 hH u21 u20
    (by rw [fu.get (by decide) (by simp)];exact hm0) T1 ht1
    (fun r hr=>by rw [fu.getByte (by omega) (by simp)];exact hb1 r hr)
  by_cases h1 : 63-C0<48 ∧ H%18=T1 (63-C0)
  · rw [if_pos h1] at pv
    obtain ⟨w,n2,c2,hn2,hc2,sw,pw,w21,rw_,fw⟩:=phase2_steps hc v pv (63-C0) C1 H (by omega) hC1 hH v21
      (by rw [rv.get (by decide)];exact u20)
      (by rw [fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm1) T2 ht2
      (fun r hr=>by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hb2 r hr)
    by_cases h2 : 63-C0-C1<35 ∧ H/18%18=T2 (63-C0-C1)
    · rw [if_pos h2] at pw
      obtain ⟨x,n3,c3,hn3,hc3,sx,px,x21,rx,fx⟩:=phase3_steps hc w pw (63-C0-C1) C2 H (by omega) hC2 hH w21
        (by rw [rw_.get (by decide),rv.get (by decide)];exact u20)
        (by rw [fw.get (by decide) (by simp),fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm2)
      by_cases h3 : 63-C0-C1-C2<18 ∧ H/324=63-C0-C1-C2
      · rw [if_pos h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=good_steps hc.good x px
        refine ⟨t,4+n1+n2+n3+1,4+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : Condition H C0 C1 C2 T1 T2 := by exact ⟨h1.1,h2.1,h3.1,h1.2,h2.2,h3.2⟩
          simpa only [if_pos hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
      · rw [if_neg h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad x px
        refine ⟨t,4+n1+n2+n3+1,4+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h3 ⟨h.2.2.1,h.2.2.2.2.2⟩
          simpa [hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
    · rw [if_neg h2] at pw
      obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad w pw
      refine ⟨t,4+n1+n2+1,4+c1+c2+1,by omega,by omega,((su.trans sv).trans sw).trans st,?_,?_,?_⟩
      · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h2 ⟨h.2.1,h.2.2.2.2.1⟩
        simpa [hcond] using pt
      · exact (((ru.trans rv).trans rw_).trans rt).mono (by decide)
      · exact (((fu.trans fv).trans fw).trans ft).mono (by simp)
  · rw [if_neg h1] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad v pv
    refine ⟨t,4+n1+1,4+c1+1,by omega,by omega,(su.trans sv).trans st,?_,?_,?_⟩
    · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h1 ⟨h.1,h.2.2.2.1⟩
      simpa [hcond] using pt
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
#print axioms validate_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : Code im := by
  constructor
  · exact SharedCounterHooks.code_slice (off:=1873) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1877) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1881) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1883) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1893) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1897) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1899) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1910) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1914) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1916) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1884) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1900) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1917) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1886) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1889) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1890) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1902) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1905) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1906) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1919) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1922) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1923) hc (by decide +kernel) (by decide +kernel)
theorem installed_code : Code Images.expandImage := code_of_driver codeAt_expand_shared_driver
#print axioms installed_code
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.WCT9 SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem credit_lt (lay : SigGolfCandidate.T3.Layer) (digits : List Nat) : CanonicalPolicy.credit lay digits<2^64 := by
  have hw : wordCredit lay digits≤SigGolfCandidate.T3.chainCount lay := by
    unfold wordCredit
    exact (List.length_filter_le _ _).trans_eq (List.length_range)
  have hs : savedCopies lay digits≤SigGolfCandidate.T3.chainCount lay := by
    unfold savedCopies
    exact (List.length_filter_le _ _).trans_eq (List.length_range)
  have hc : SigGolfCandidate.T3.chainCount lay≤54 := by fin_cases lay <;> decide +kernel
  unfold CanonicalPolicy.credit CanonicalPolicy.reward
  omega

theorem validate_source_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (hints : BitVec 16) (digits : List (List Nat))
    (hH : hints.toNat<5832) (hlen : digits.length=4)
    (hfloor : ∀lay:SigGolfCandidate.T3.Layer, SharedForest.hintFloor hints lay≤CanonicalPolicy.credit lay (digits.getD lay.val []))
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat)
    (hcredits : ∀lay:SigGolfCandidate.T3.Layer,s.getMem (BitVec.ofNat 64 (417856+8*lay.val))=
      BitVec.ofNat 64 (CanonicalPolicy.credit lay (digits.getD lay.val [])))
    (ht1 : ∀r,r<48→CanonicalPolicy.threshold 1 r<18)
    (ht2 : ∀r,r<35→CanonicalPolicy.threshold 2 r<18)
    (hb1 : ∀r,r<48→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 1 r))
    (hb2 : ∀r,r<35→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (CanonicalPolicy.threshold 2 r)) :
    ∃t n c,n≤47 ∧ c≤59 ∧ Steps im s n c t ∧
      t.pc=(if SharedForest.policyHintsValid hints digits then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t,n,c,hn,hc',st,pt,rt,ft⟩:=validate_steps hc s hp hints.toNat
    (CanonicalPolicy.credit 0 (digits.getD 0 []))
    (CanonicalPolicy.credit 1 (digits.getD 1 []))
    (CanonicalPolicy.credit 2 (digits.getD 2 [])) hH (credit_lt _ _) (credit_lt _ _) (credit_lt _ _) hm
    (hcredits 0) (hcredits 1) (hcredits 2)
    (CanonicalPolicy.threshold 1) (CanonicalPolicy.threshold 2) ht1 ht2 hb1 hb2
  refine ⟨t,n,c,hn,hc',st,?_,rt,ft⟩
  have hh:=policyCondition_iff hints digits hH hlen (by simpa [SharedForest.hintFloor] using hfloor 0)
    (hfloor 1) (hfloor 2)
  change (Condition hints.toNat (CanonicalPolicy.credit 0 (digits.getD 0 []))
    (CanonicalPolicy.credit 1 (digits.getD 1 [])) (CanonicalPolicy.credit 2 (digits.getD 2 []))
    (CanonicalPolicy.threshold 1) (CanonicalPolicy.threshold 2) ↔ SharedForest.policyHintsValid hints digits=true) at hh
  simpa only [hh] using pt
#print axioms credit_lt
#print axioms validate_source_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def moveCode : List (BitVec 32) := [0xe3303,0x6eb023,0xff8e0e13,0xff8e8e93,0xfff90913,0xfe0916e3]
sym_block moveRun := symRun {noAlias:=true} moveCode (pcOf 46895) 20

theorem move_step {im : Image} (hc : CodeAt im (pcOf 46895) moveCode)
    (s : MachineState) (hp : s.pc=pcOf 46895) (X Y n : Nat)
    (hx8 : X%8=0) (hy8 : Y%8=0) (hx : 8≤X) (hy : 8≤Y)
    (hX : X≤35000) (hY : Y≤35000) (hn : 0<n) (hn' : n<2^64)
    (h28 : s.getReg .x28=BitVec.ofNat 64 X)
    (h29 : s.getReg .x29=BitVec.ofNat 64 Y)
    (h18 : s.getReg .x18=BitVec.ofNat 64 n) :
    ∃t,Steps im s 6 6 t ∧ t.pc=(if n=1 then pcOf 46901 else pcOf 46895) ∧
      t.getReg .x28=BitVec.ofNat 64 (X-8) ∧ t.getReg .x29=BitVec.ofNat 64 (Y-8) ∧
      t.getReg .x18=BitVec.ofNat 64 (n-1) ∧
      t.getMem (BitVec.ofNat 64 Y)=s.getMem (BitVec.ofNat 64 X) ∧
      RegsExcept s t [.x6,.x18,.x28,.x29] ∧ Frame s t (fun A=>A=Y) := by
  have hxsub : (BitVec.ofNat 64 X+18446744073709551608 : Word)=BitVec.ofNat 64 (X-8) := by
    exact ofNat_sub8 X hx (by omega)
  have hysub : (BitVec.ofNat 64 Y+18446744073709551608 : Word)=BitVec.ofNat 64 (Y-8) := by
    exact ofNat_sub8 Y hy (by omega)
  have hnsub : (BitVec.ofNat 64 n+18446744073709551615 : Word)=BitVec.ofNat 64 (n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega,BitVec.ofNat_add,BitVec.add_assoc]
    change BitVec.ofNat 64 (n-1)+0=BitVec.ofNat 64 (n-1)
    exact BitVec.add_zero _
  refine ⟨_,symRun_sound moveRun hc s hp ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [moveRun.res,rv_simp,h28,h29,accessValid_iff,MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc,moveRun.res,E.eval,BinOp.eval,CmpOp.eval,h18,hnsub]
    have hz : (BitVec.ofNat 64 (n-1)=0) ↔ n=1 := by
      constructor
      · intro he;have he' := congrArg BitVec.toNat he
        change (n-1)%2^64=0 at he'
        rw [Nat.mod_eq_of_lt (show n-1<2^64 by omega)] at he'
        omega
      · rintro rfl;rfl
    change (if ((BitVec.ofNat 64 n+18446744073709551615 : Word) != 0) then pcOf 46895 else pcOf 46901) = _
    rw [hnsub]
    simp only [bne_iff_ne,ne_eq,hz]
    split_ifs <;> rfl
  · change s.getReg .x28+18446744073709551608=_
    rw [h28];exact hxsub
  · change s.getReg .x29+18446744073709551608=_
    rw [h29];exact hysub
  · change s.getReg .x18+18446744073709551615=_
    rw [h18];exact hnsub
  · simp only [Result.toState_getMem,moveRun.res]
    t3n [h28,h29]
    simp
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hnA
    simp only [Result.toState_getMem,moveRun.res]
    t3n [h28,h29]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    simp only [Nat.add_zero,Nat.mod_eq_of_lt (show Y<18446744073709551616 by omega),if_neg hnA]

theorem move_loop {im : Image} (hc : CodeAt im (pcOf 46895) moveCode)
    (S D : Nat) (hs8 : S%8=0) (hd8 : D%8=0) (hs : 8≤S) (hsd : S<D) :
    ∀n (s : MachineState), D+8*n≤35000 → s.pc=pcOf 46895 →
      s.getReg .x28=BitVec.ofNat 64 (S+8*n) →
      s.getReg .x29=BitVec.ofNat 64 (D+8*n) →
      s.getReg .x18=BitVec.ofNat 64 (n+1) →
      ∃t,Steps im s (6*(n+1)) (6*(n+1)) t ∧ t.pc=pcOf 46901 ∧
        t.getReg .x28=BitVec.ofNat 64 (S-8) ∧ t.getReg .x29=BitVec.ofNat 64 (D-8) ∧
        t.getReg .x18=0 ∧
        (∀i≤n,t.getMem (BitVec.ofNat 64 (D+8*i))=s.getMem (BitVec.ofNat 64 (S+8*i))) ∧
        RegsExcept s t [.x6,.x18,.x28,.x29] ∧
        Frame s t (fun A=>D≤A ∧ A<D+8*(n+1)) := by
  intro n
  induction n with
  | zero =>
    intro s hb hp h28 h29 h18
    simp only [Nat.mul_zero,Nat.add_zero] at hb h28 h29
    obtain ⟨t,st,pt,r28,r29,r18,mt,rt,ft⟩:=move_step hc s hp S D 1 hs8 hd8 hs (by omega) (by omega) hb (by decide) (by decide) h28 h29 h18
    refine ⟨t,by simpa using st,by simpa using pt,r28,r29,by simpa using r18,?_,rt,ft.mono (by intro A hA h;omega)⟩
    intro i hi
    have : i=0 := by omega
    simpa [this] using mt
  | succ n ih =>
    intro s hb hp h28 h29 h18
    obtain ⟨u,su,pu,r28,r29,r18,mu,ru,fu⟩:=move_step hc s hp (S+8*(n+1)) (D+8*(n+1)) (n+2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hb (by omega) (by omega) h28 h29 h18
    have p : u.pc=pcOf 46895 := by simpa using pu
    have a : u.getReg .x28=BitVec.ofNat 64 (S+8*n) := by rw [r28,show S+8*(n+1)-8=S+8*n by omega]
    have b : u.getReg .x29=BitVec.ofNat 64 (D+8*n) := by rw [r29,show D+8*(n+1)-8=D+8*n by omega]
    have c : u.getReg .x18=BitVec.ofNat 64 (n+1) := by simpa using r18
    obtain ⟨t,ut,pt,t28,t29,t18,mt,rt,ft⟩:=ih u (by omega) p a b c
    refine ⟨t,?_,pt,t28,t29,t18,?_,(ru.trans rt).mono (by decide),?_⟩
    · convert su.trans ut using 1 <;> omega
    · intro i hi
      by_cases hin : i≤n
      · rw [mt i hin,fu.get (by omega) (by omega)]
      · have he : i=n+1 := by omega
        subst i
        rw [ft.get (by omega) (by omega)];exact mu
    · exact (fu.trans ft).mono (by intro A hA h;rcases h with h|h <;> omega)
#print axioms move_step
#print axioms move_loop
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def setupCode : List (BitVec 32) := [0xfb040e13,0x20eb7,0x260e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x7e37,0xe0e13,0x1eb7,0x800e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x66e37,0xe0e13,0x8e3303,0x6eb823,0xebc23,0x20eb023,0x20eb423,0x20eb823,0x20ebc23,0x8e37,0x4b8e0e13,0x8eb7,0x5e8e8e93,0x1ac00913]
sym_block setupRun := symRun {noAlias:=true} setupCode (pcOf 46862) 100
def tailCode : List (BitVec 32) := [0x22137,0x10113,0x293,0xf04d206f]
sym_block tailRun := symRun {noAlias:=true} tailCode (pcOf 46901) 20

theorem setup_mem (s : MachineState) (h8 : s.getReg .x8=BitVec.ofNat 64 2984) (A : Nat) (hA : A < 2^64) :
    (setupRun.res.toState s).getMem (BitVec.ofNat 64 A) =
      if A = 2104 then 0#64 else if A = 2096 then 0#64 else if A = 2088 then 0#64 else if A = 2080 then 0#64
      else if A = 2072 then 0#64 else if A = 2064 then s.getMem (BitVec.ofNat 64 417800)
      else if A = 2056 then s.getMem (BitVec.ofNat 64 28680) else if A = 2048 then s.getMem (BitVec.ofNat 64 28672)
      else if A = 131736 then s.getMem (BitVec.ofNat 64 2960) else if A = 131728 then s.getMem (BitVec.ofNat 64 2952)
      else if A = 131688 then s.getMem (BitVec.ofNat 64 2912) else if A = 131680 then s.getMem (BitVec.ofNat 64 2904)
      else s.getMem (BitVec.ofNat 64 A) := by
  have e0 : (18446744073709554520#64 : BitVec 64) = BitVec.ofNat 64 2904 := by decide
  have e1 : (18446744073709554528#64 : BitVec 64) = BitVec.ofNat 64 2912 := by decide
  have e2 : (18446744073709554568#64 : BitVec 64) = BitVec.ofNat 64 2952 := by decide
  have e3 : (18446744073709554576#64 : BitVec 64) = BitVec.ofNat 64 2960 := by decide
  simp only [Result.toState_getMem,setupRun.res]
  t3n [h8]
  rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA), e0, e1, e2, e3]
set_option maxRecDepth 100000 in
theorem setup_steps {im : Image} (hc : CodeAt im (pcOf 46862) setupCode)
    (s : MachineState) (hp : s.pc=pcOf 46862) (h8 : s.getReg .x8=BitVec.ofNat 64 2984) :
    ∃t,Steps im s 33 33 t ∧ t.pc=pcOf 46895 ∧
      t.getReg .x28=33976 ∧ t.getReg .x29=34280 ∧ t.getReg .x18=428 ∧
      (∀o,o=0 ∨ o=8 ∨ o=48 ∨ o=56 → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (2904+o))) ∧
      (∀i<2,t.getMem (BitVec.ofNat 64 (2048+8*i))=s.getMem (BitVec.ofNat 64 (0x7000+8*i))) ∧
      t.getMem (BitVec.ofNat 64 2064)=s.getMem (BitVec.ofNat 64 0x66008) ∧
      (∀ i : Nat, 3 ≤ i → i < 8 → t.getMem (BitVec.ofNat 64 (2048+8*i))=0) ∧
      RegsExcept s t [.x6,.x7,.x18,.x28,.x29] ∧
      Frame s t (fun A=>A=0x20260 ∨ A=0x20268 ∨ A=0x20290 ∨ A=0x20298 ∨ (2048≤A ∧ A<2112)) := by
  refine ⟨_,symRun_sound setupRun hc s hp ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setupRun.res,rv_simp,accessValid_iff,MEMORY_BYTES,h8]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro o ho
    rw [setup_mem s h8 _ (by omega)]
    rcases ho with rfl|rfl|rfl|rfl <;> (norm_num; try rfl)
  · intro i hi
    rw [setup_mem s h8 _ (by omega)]
    interval_cases i <;> (norm_num; try rfl)
  · rw [setup_mem s h8 _ (by omega)]; norm_num; try rfl
  · intro i hlo hhi
    rw [setup_mem s h8 _ (by omega)]
    interval_cases i <;> (norm_num; try rfl)
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    rw [setup_mem s h8 A hA]
    split_ifs <;> first | rfl | omega

theorem tail_steps {im : Image} (hc : CodeAt im (pcOf 46901) tailCode)
    (s : MachineState) (hp : s.pc=pcOf 46901) :
    ∃t,Steps im s 4 4 t ∧ t.pc=pcOf 249 ∧ t.getReg .x2=0x22000 ∧
      t.getReg .x5=0 ∧ RegsExcept s t [.x2,.x5] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound tailRun hc s hp ?_,rfl,rfl,rfl,?_,?_⟩
  · simp [tailRun.res,rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms setup_steps
#print axioms tail_steps
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
structure Code (im : Image) : Prop where
  setup : CodeAt im (pcOf 46862) setupCode
  move : CodeAt im (pcOf 46895) moveCode
  tail : CodeAt im (pcOf 46901) tailCode

theorem steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46862) (h8 : s.getReg .x8=BitVec.ofNat 64 2984) :
    ∃t,Steps im s 2605 2605 t ∧ t.pc=pcOf 249 ∧ t.getReg .x2=0x22000 ∧ t.getReg .x5=0 ∧
      (∀o,(o=0 ∨ o=8 ∨ o=48 ∨ o=56) → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (2904+o))) ∧
      (∀i,i<2 → t.getMem (BitVec.ofNat 64 (2048+8*i))=s.getMem (BitVec.ofNat 64 (0x7000+8*i))) ∧
      t.getMem 2064=s.getMem 0x66008 ∧
      (∀ i : Nat, 3 ≤ i → i < 8 → t.getMem (BitVec.ofNat 64 (2048+8*i))=0) ∧
      (∀i,i<428 → t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i))) ∧
      RegsExcept s t [.x2,.x5,.x6,.x7,.x18,.x28,.x29] ∧
      Frame s t (fun A=>A=0x20260 ∨ A=0x20268 ∨ A=0x20290 ∨ A=0x20298 ∨ (2048≤A ∧ A<2112) ∨ (30864≤A ∧ A<34288)) := by
  obtain ⟨u,su,pu,u28,u29,u18,roots,rho,dc,z,ru,fu⟩:=setup_steps hc.setup s hp h8
  obtain ⟨v,uv,pv,v28,v29,v18,mv,rv,fv⟩:=move_loop hc.move 30560 30864 (by decide) (by decide) (by decide) (by decide)
    427 u (by decide) pu u28 u29 u18
  obtain ⟨t,vt,pt,t2,t5,rt,ft⟩:=tail_steps hc.tail v pv
  have gm : ∀A,A<2^64 → ¬(30864≤A ∧ A<34288) → t.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A) := by
    intro A hA hn
    rw [ft.get hA (by simp),fv.get hA (by simpa using hn)]
  refine ⟨t,by convert su.trans (uv.trans vt) using 1 <;> norm_num,pt,t2,t5,?_,?_,?_,?_,?_,?_,?_⟩
  · intro o ho
    rw [gm _ (by rcases ho with rfl|rfl|rfl|rfl <;> decide) (by rcases ho with rfl|rfl|rfl|rfl <;> decide)]
    exact roots o ho
  · intro i hi
    rw [gm _ (by omega) (by omega)];exact rho i hi
  · rw [show (2064:Word)=BitVec.ofNat 64 2064 by rfl,gm _ (by decide) (by decide)];exact dc
  · intro i hi hi'
    rw [gm _ (by omega) (by omega)];exact z i hi hi'
  · intro i hi
    rw [ft.get (by omega) (by simp),mv i (by omega),fu.get (by omega) (by omega)]
  · exact ((ru.trans rv).trans rt).mono (by decide)
  · exact ((fu.trans fv).trans ft).mono (by intro A hA h;rcases h with (h|h)|h <;> first | tauto | omega)
#print axioms steps
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedZero
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem clear_witness {im : Image} (p : Word) (hc : CodeAt im p words)
    (s : MachineState) (hp : s.pc=p) (h28 : s.getReg .x28=1152) (h29 : s.getReg .x29=11064) :
    ∃t,Steps im s 3717 3717 t ∧ t.pc=p+12 ∧
      (∀A,A%8=0 → 1152≤A → A<11064 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>1152≤A ∧ A<11064) := by
  obtain ⟨t,st,pt,r28,mt,rt,ft⟩:=loop p hc 1152 (by decide) 1238 s (by decide) hp h28 h29
  refine ⟨t,st,pt,?_,rt,ft⟩
  intro A ha hlo hhi
  have he : 1152+8*((A-1152)/8)=A := by omega
  rw [←he];exact mt _ (by omega)

theorem clear_witness_final {im : Image} (p : Word) (hc : CodeAt im p words)
    (s : MachineState) (hp : s.pc=p) (h28 : s.getReg .x28=1152) (h29 : s.getReg .x29=11000) :
    ∃t,Steps im s 3693 3693 t ∧ t.pc=p+12 ∧
      (∀A,A%8=0 → 1152≤A → A<11000 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>1152≤A ∧ A<11000) := by
  obtain ⟨t,st,pt,r28,mt,rt,ft⟩:=loop p hc 1152 (by decide) 1230 s (by decide) hp h28 h29
  refine ⟨t,st,pt,?_,rt,ft⟩
  intro A ha hlo hhi
  have he : 1152+8*((A-1152)/8)=A := by omega
  rw [←he];exact mt _ (by omega)

structure ClearCode (im : Image) : Prop where
  accepted : CodeAt im (pcOf 45232) acceptedCode
  firstZero : CodeAt im (pcOf 45254) words
  finalScatter : CodeAt im (pcOf 46980) finalScatterCode
  finalZero : CodeAt im (pcOf 47001) words
  back : CodeAt im (pcOf 47004) [0xcb4fe06f]

theorem accepted_clear {im : Image} (hc : ClearCode im)
    (s : MachineState) (hp : s.pc=pcOf 45232) (h17 : s.getReg .x17=0x20160) :
    ∃t,Steps im s 3739 3739 t ∧ t.pc=pcOf 45257 ∧
      (∀A,A%8=0 → 1152≤A → A<11064 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      t.getMem 0x66020=0 ∧ t.getMem 0x66008=s.getReg .x19 ∧
      t.getMem 0x66010=s.getMem 0x20160 >>> 33 ∧
      t.getMem 0x20550=s.getMem 0x20160 >>> 33 ∧
      (∀i,i<4 → t.getMem (BitVec.ofNat 64 (96+8*i))=s.getMem (BitVec.ofNat 64 (0x20160+8*i))) ∧
      RegsExcept s t [.x6,.x22,.x28,.x29] ∧
      Frame s t (fun A=>A=0x66020 ∨ A=0x66008 ∨ A=0x66010 ∨ A=0x20550 ∨ (96≤A ∧ A<128) ∨ (1152≤A ∧ A<11064)) := by
  obtain ⟨u,su,pu,u28,u29,mode,ctr,index,idx,digest,ru,fu⟩:=accepted_steps hc.accepted s hp h17
  obtain ⟨t,ut,pt,zeros,rt,ft⟩:=clear_witness (pcOf 45254) hc.firstZero u pu u28 u29
  refine ⟨t,by convert su.trans ut using 1,pt,zeros,?_,?_,?_,?_,?_,(ru.trans rt).mono (by decide),?_⟩
  · exact (ft.get (by decide) (by decide)).trans mode
  · exact (ft.get (by decide) (by decide)).trans ctr
  · exact (ft.get (by decide) (by decide)).trans index
  · exact (ft.get (by decide) (by decide)).trans idx
  · intro i hi;rw [ft.get (by omega) (by omega)];exact digest i hi
  · exact (fu.trans ft).mono (by intro A hA h;tauto)

theorem final_clear {im : Image} (hc : ClearCode im)
    (s : MachineState) (hp : s.pc=pcOf 46980) :
    ∃t,Steps im s 3715 3715 t ∧ t.pc=pcOf 45257 ∧
      (∀A,A%8=0 → 1152≤A → A<11000 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      t.getMem 0x66018=s.getMem 1184 ∧ t.getMem 0x66020=1 ∧
      (∀i,i<4 → t.getMem (BitVec.ofNat 64 (0x20160+8*i))=s.getMem (BitVec.ofNat 64 (96+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧
      Frame s t (fun A=>A=0x66018 ∨ A=0x66020 ∨ (0x20160≤A ∧ A<0x20180) ∨ (1152≤A ∧ A<11000)) := by
  obtain ⟨u,su,pu,u28,u29,ctr,mode,digest,ru,fu⟩:=finalScatter_steps hc.finalScatter s hp
  obtain ⟨v,uv,pv,zeros,rv,fv⟩:=clear_witness_final (pcOf 47001) hc.finalZero u pu u28 u29
  have jump : Steps im v 1 1 (v.setPC (pcOf 45257)) := by
    obtain ⟨imm,hd,ho⟩:=jalTo_sound (show jalTo (0xcb4fe06f#32) 47004=some 45257 by decide)
    exact jal_x0_step hc.back hd ho v pv
  refine ⟨v.setPC (pcOf 45257),by convert su.trans (uv.trans jump) using 1,rfl,zeros,?_,?_,?_,(ru.trans rv).mono (by decide),?_⟩
  · exact (fv.get (by decide) (by decide)).trans ctr
  · exact (fv.get (by decide) (by decide)).trans mode
  · intro i hi;exact (fv.get (by omega) (by omega)).trans (digest i hi)
  · exact (fu.trans fv).mono (by intro A hA h;tauto)
#print axioms clear_witness
#print axioms accepted_clear
#print axioms final_clear
end ClaudeWCT.W9.Machine.Expand.SharedZero

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem SharedHandoff.code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : SharedHandoff.Code im := by
  constructor
  · exact SharedCounterHooks.code_slice (off:=1806) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1839) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1845) hc (by decide +kernel) (by decide +kernel)
theorem SharedHandoff.installed_code : SharedHandoff.Code Images.expandImage := SharedHandoff.code_of_driver codeAt_expand_shared_driver

theorem SharedZero.code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : SharedZero.ClearCode im := by
  constructor
  · exact SharedCounterHooks.code_slice (off:=176) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=198) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1924) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1945) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1948) hc (by decide +kernel) (by decide +kernel)
theorem SharedZero.installed_code : SharedZero.ClearCode Images.expandImage := SharedZero.code_of_driver codeAt_expand_shared_driver

theorem SharedScatter.after_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (pcOf 46509) SharedScatter.afterCode := by
  exact SharedCounterHooks.code_slice (off:=1453) hc (by decide +kernel) (by decide +kernel)
theorem SharedScatter.finish_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (pcOf 47005) SharedScatter.finishCode := by
  exact SharedCounterHooks.code_slice (off:=1949) hc (by decide +kernel) (by decide +kernel)
theorem SharedScatter.installed_after : CodeAt Images.expandImage (pcOf 46509) SharedScatter.afterCode := SharedScatter.after_of_driver codeAt_expand_shared_driver
theorem SharedScatter.installed_finish : CodeAt Images.expandImage (pcOf 47005) SharedScatter.finishCode := SharedScatter.finish_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem expand_steps {im : Image} (hc : CodeAt im (pcOf 45226) expandCode)
    (s : MachineState) (hp : s.pc=pcOf 45226) :
    Steps im s 1 1 (s.setPC (pcOf 45232)) := by
  exact ClaudeWCT.W9.Machine.Expand.jal_x0_step (imm:=24) hc (by rfl) (by decide) s hp

end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def rawSlots (k child : Nat) (values : Fin 6→SigGolfCandidate.T3.Digest)
    (path : Nat→SigGolfCandidate.T3.Digest) : List (Nat×SigGolfCandidate.T3.Digest) :=
  ((List.finRange 6).flatMap fun i=>[(V3.chainOffset k i.val+48,values i),
    (V3.regionOffset k+V3.leafSlot i.val,values i)]) ++
  ((List.range (SharedV3.lastLevel k+1)).map fun l=>(V3.regionOffset k+SharedV3.sibOff child l,path l)) ++
  [(SharedV3.topOtherOff k child,path (SharedV3.lastLevel k+1))]

theorem rawSlots_written (k : Fin 9) (child : Fin 128)
    (values : Fin 6→SigGolfCandidate.T3.Digest) (path : Nat→SigGolfCandidate.T3.Digest)
    (p : Nat×SigGolfCandidate.T3.Digest) (hp:p∈rawSlots k.val child.val values path)
    (half : Nat) (hh:half<2) : PreciseCoordinateW k.val child.val (2904+p.1+8*half) := by
  unfold rawSlots at hp
  simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (⟨i,hi,hp⟩|⟨l,hl,hp⟩)|hp
  · rcases hp with rfl|rfl
    · rw [←chainDestination_source k i]
      apply Or.inl;apply Or.inl;apply Or.inl
      refine ⟨i.val,i.isLt,?_⟩
      interval_cases half
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
    · by_cases hz:i.val=0
      · have ie:i=0:=Fin.ext hz
        subst i
        change PreciseCoordinateW k.val child.val (2904+(V3.regionOffset k.val+688)+8*half)
        rw [show V3.regionOffset k.val+688=V3.chainOffset k.val 0+48 by unfold V3.chainOffset;omega,
          show 2904+(V3.chainOffset k.val 0+48)=coordRegion k.val+688 by
            simpa only [Fin.val_zero] using (chainDestination_source k (0:Fin 6)).symm]
        apply Or.inl;apply Or.inl;apply Or.inl
        refine ⟨0,by decide,?_⟩
        interval_cases half
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
      · rw [←leafDestination_source k i (by omega)]
        apply Or.inl;apply Or.inl;apply Or.inl
        refine ⟨i.val,i.isLt,Or.inr (Or.inr ⟨by omega,?_⟩)⟩
        interval_cases half
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
  · subst p
    have hlt:l<SharedV3.lastLevel k.val+1:=List.mem_range.mp hl
    by_cases h5:l<5
    · rw [←Nat.add_assoc,←pathDestination_source k child ⟨l,h5⟩]
      simp only [Fin.val_mk]
      apply Or.inl;apply Or.inl;apply Or.inr
      refine ⟨l,h5,?_⟩
      interval_cases half
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · have hn:¬firstCoord k.val:=by
        intro h
        have hf:SharedV3.first k.val=true:=by simpa [SharedV3.first,firstCoord] using h
        simp [SharedV3.lastLevel,hf] at hlt
        omega
      have hl5:l=5:=by unfold SharedV3.lastLevel at hlt;split at hlt <;> omega
      subst l
      rw [←Nat.add_assoc,←sixthDestination_source k child]
      apply Or.inl;apply Or.inr
      refine ⟨hn,?_⟩
      interval_cases half
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  · subst p
    rw [←topDest_source k child]
    interval_cases half
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

#print axioms rawSlots_written
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedDigestCode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open Sign.SharedDigestBoundary
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem success_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (pcOf 45226) expandCode := by
  exact SharedCounterHooks.code_slice (off:=170) hc (by decide +kernel) (by decide +kernel)
theorem failure_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (failPC true) failureCode := by
  exact SharedCounterHooks.code_slice (off:=173) hc (by decide +kernel) (by decide +kernel)
theorem failure_ecall_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (pcOf 45231) [0x73] := by
  exact SharedCounterHooks.code_slice (off:=175) hc (by decide +kernel) (by decide +kernel)
theorem installed_success : CodeAt Images.expandImage (pcOf 45226) expandCode := success_of_driver codeAt_expand_shared_driver
theorem installed_failure : CodeAt Images.expandImage (failPC true) failureCode := failure_of_driver codeAt_expand_shared_driver
theorem installed_failure_ecall : CodeAt Images.expandImage (pcOf 45231) [0x73] := failure_ecall_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand.SharedDigestCode

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (bytes_length_e extractByte_bytesToWordLE_e)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def DB : Nat := 16747408

theorem getMem {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (A : Nat) (hA:A<2^64) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=
      if 0x7000≤A ∧ A<0x7000+5248 ∧ (A-0x7000)%8=0 then bytesToWordLE ((bytes b).drop (A-0x7000) |>.take 8)
      else if 0xA0≤A ∧ A<0xB0 ∧ (A-0xA0)%8=0 then bytesToWordLE ((bytes pk).drop (A-0xA0) |>.take 8)
      else if 0x6620≤A ∧ A<0x6640 ∧ (A-0x6620)%8=0 then bytesToWordLE ((bytes m).drop (A-0x6620) |>.take 8)
      else if DB≤A ∧ A<DB+29808 ∧ (A-DB)%8=0 then bytesToWordLE (im.data.drop (A-DB) |>.take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg,getMem_writeBytesAsWords _ _ 0x7000 A (by rw[bytes_length_e];decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw[bytes_length_e];decide) hA,
    getMem_writeBytesAsWords _ _ 0x6620 A (by rw[bytes_length_e];decide) hA,hb,
    getMem_writeBytesAsWords _ _ DB A (by rw[hlen];decide) hA,
    bytes_length_e,bytes_length_e,bytes_length_e,hlen]
  rfl

theorem dataByte {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (i : Nat) (hi:i<29808) :
    (w9init im m pk b).getByte (BitVec.ofNat 64 (DB+i))=im.data.getD i 0 := by
  rw [getByte_eq_word _ _ (by unfold DB;omega),getMem hlen hb _ _ _ _ (by unfold DB;omega),
    if_neg (by unfold DB;omega),if_neg (by unfold DB;omega),if_neg (by unfold DB;omega),
    if_pos (by unfold DB;omega),extractByte_bytesToWordLE_e _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_take,List.getElem?_drop,
    if_pos (Nat.mod_lt (DB+i) (show 0<8 by decide))]
  congr 2
  unfold DB
  omega

theorem signatureWord {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (i : Nat) (hi:i<656) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 (0x7000+8*i))=b.extractLsb' (64*i) 64 := by
  rw [getMem hlen hb _ _ _ _ (by omega),if_pos (by omega),
    show 0x7000+8*i-0x7000=8*i by omega]
  exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e b i (by omega)

#print axioms getMem
#print axioms dataByte
#print axioms signatureWord
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Sign.SharedDigest
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def DataAt (s : MachineState) : Prop := ∀i,i<2160 → s.getByte (BitVec.ofNat 64 (DB+i))=Images.expandSharedData.getD i 0

theorem ranks_data (f : Fin 563) : Images.expandSharedData.getD f.val 0=BitVec.ofNat 8 (rankByte f.val) := by
  have h:∀f:Fin 563,Images.expandSharedData.getD f.val 0=BitVec.ofNat 8 (rankByte f.val):=by decide +kernel
  exact h f

theorem correction_data (k : Fin 9) (j : Fin 32) : Images.expandSharedData.getD (correctionOffset true k.val+j.val) 0=BitVec.ofNat 8 (correctionByte k.val j.val) := by
  have h:∀k:Fin 9,∀j:Fin 32,Images.expandSharedData.getD (correctionOffset true k.val+j.val) 0=BitVec.ofNat 8 (correctionByte k.val j.val):=by decide +kernel
  exact h k j

theorem DataAt.tables {s : MachineState} (h:DataAt s) : TablesAt true s := by
  constructor
  · intro f hf
    rw [show tableBase true=DB by rfl,h f (by omega)]
    exact ranks_data ⟨f,hf⟩
  · intro k hk j hj
    have hb:correctionOffset true k≤1568:=by
      simp only [correctionOffset,↓reduceIte];split <;> omega
    rw [show tableBase true=DB by rfl,Nat.add_assoc,h _ (by omega)]
    exact correction_data ⟨k,hk⟩ ⟨j,hj⟩

#print axioms ranks_data
#print axioms correction_data
#print axioms DataAt.tables
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem tail_steps {im : Image} (hc : CodeAt im (pcOf 1) frontTail) (s : MachineState)
    (hpc : s.pc = pcOf 1) (hx5 : s.getReg .x5 = 0) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 42719 ∧ t.getReg .x5 = 0 ∧
      t.getMem (BitVec.ofNat 64 0x800) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 0x808) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 0x6620) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 0x6628) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 0x6630) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 0x6638) ∧
      RegsExcept s t [.x5, .x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound h2_front hc s hpc
    (by simp [h2_front.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, h2_front.res, E.eval]
  · simp [h2_front.res, rv_simp, hx5]
  iterate 8
    · simp only [Result.toState_getMem, h2_front.res, DIG]
      t3n []
  · ex_regs h2_front.res
  · intro A hA hn
    simp only [DIG] at hn
    simp only [Result.toState_getMem, h2_front.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]

#print axioms tail_steps
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def Writes (A : Nat) : Prop := A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨
  A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 ∨ A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8

theorem setup {im : Image} (hf:CodeAt im (pcOf 1) frontTail) (hz:CodeAt im (pcOf 42719) zeroBlk)
    (hj:CodeAt im (pcOf 30) [0x7892b06f]) (s : MachineState) (hp:s.pc=pcOf 1) (hx5:s.getReg .x5=0) :
    ∃t,Steps im s 37 37 t ∧ t.pc=pcOf 45056 ∧ t.getReg .x5=0 ∧
      (∀A, A=0x800 ∨ A=DIG → t.getMem (BitVec.ofNat 64 A)=s.getMem 0x7000) ∧
      (∀A, A=0x808 ∨ A=DIG+8 → t.getMem (BitVec.ofNat 64 A)=s.getMem 0x7008) ∧
      (∀k,k<4 → t.getMem (BitVec.ofNat 64 (DIG+32+8*k))=s.getMem (BitVec.ofNat 64 (0x6620+8*k))) ∧
      (∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      RegsExcept s t [.x5,.x6,.x7,.x19,.x29,.x30] ∧ Frame s t Writes := by
  obtain ⟨u,su,up,u5,a0,a8,d0,d8,d32,d40,d48,d56,ru,fu⟩:=tail_steps hf s hp hx5
  obtain ⟨v,uv,vp,v19,z,rv,fv⟩:=zero_spec hz u up
  have jump : Steps im v 1 1 (v.setPC (pcOf 45056)) := by
    obtain ⟨imm,hd,hoff⟩:=jalTo_sound (show jalTo (0x7892b06f#32) 30=some 45056 by decide)
    exact jal_x0_step hj hd hoff v vp
  have g:∀A,A<2^64 → ¬(A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8) → v.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A):=fv
  refine ⟨v.setPC (pcOf 45056),su.trans (uv.trans jump),rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · rw[MachineState.getReg_setPC,rv.get (by decide),u5]
  · intro A h;rcases h with rfl|rfl
    · exact (g _ (by decide) (by simp[DIG])).trans a0
    · exact (g _ (by decide) (by simp[DIG])).trans d0
  · intro A h;rcases h with rfl|rfl
    · exact (g _ (by decide) (by simp[DIG])).trans a8
    · exact (g _ (by decide) (by simp[DIG])).trans d8
  · intro k hk
    rw[MachineState.getMem_setPC,g _ (by unfold DIG;omega) (by unfold DIG;omega)]
    interval_cases k
    · exact d32
    · exact d40
    · exact d48
    · exact d56
  · intro A h;exact z A (by rcases h with rfl|rfl|rfl|rfl <;> decide) h
  · exact (ru.trans rv).mono (by simp)
  · exact (fu.trans fv).mono (by intro A hA h;unfold Writes;rcases h with h|h <;> rcases h with h|h|h|h|h|h|h|h <;> omega)

#print axioms setup
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (bytes_length_e extractByte_bytesToWordLE_e)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem prefixData {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (pref tail : List (BitVec 8)) (hp:pref.length=2160) (hd:im.data=pref++tail)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ∀i,i<2160 → (w9init im m pk b).getByte (BitVec.ofNat 64 (DB+i))=pref.getD i 0 := by
  intro i hi
  rw [dataByte hlen hb m pk b i (by omega),hd]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append,hp,if_pos hi]

theorem msgWord {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (i : Nat) (hi:i<4) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 (0x6620+8*i))=m.extractLsb' (64*i) 64 := by
  rw [getMem hlen hb _ _ _ _ (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega),
    show 0x6620+8*i-0x6620=8*i by omega]
  exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e m i (by omega)

theorem zero {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (A : Nat) (hA:A<DB)
    (hs:A<0x7000 ∨ 0x7000+5248≤A) (hp:A<0xA0 ∨ 0xB0≤A)
    (hm:A<0x6620 ∨ 0x6640≤A) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=0 := by
  rw[getMem hlen hb _ _ _ _ (by unfold DB at hA;omega),
    if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

#print axioms prefixData
#print axioms msgWord
#print axioms zero
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem invalid_front {im : Image} (he:CodeAt im (pcOf 0) [entryWord])
    (ht:CodeAt im (pcOf 44096) tailWords) (hg:CodeAt im (pcOf 44106) guardWords)
    (hj:CodeAt im (pcOf 44192) [0xb08d506f]) (s : MachineState) (hp:s.pc=pcOf 0)
    (H : Nat) (hlo:5832≤H) (hhi:H<65536) (hh:s.getMem 0x8478 >>> 48=BitVec.ofNat 64 H) :
    ∃t,Steps im s 15 15 t ∧ t.pc=pcOf 354 ∧
      RegsExcept s t [.x6,.x7,.x15,.x28,.x29,.x30] ∧ Frame s t (fun A=>A=policyAddress) := by
  obtain ⟨u,su,up,u6,u7,u28,um,ru,fu⟩:=tail_full ht (s.setPC (pcOf 44096)) rfl
  obtain ⟨v,uv,vp,rv,fv⟩:=guard_spec hg u up H hhi (u28.trans hh)
  rw[if_neg (by omega)] at vp
  have jump:Steps im v 1 1 (v.setPC (pcOf 354)) := by
    obtain ⟨imm,hd,hoff⟩:=jalTo_sound (show jalTo (0xb08d506f#32) 44192=some 354 by decide)
    exact jal_x0_step hj hd hoff v vp
  refine ⟨v.setPC (pcOf 354),(entry_step he s hp).trans (su.trans (uv.trans jump)),rfl,?_,?_⟩
  · exact (ru.trans rv).mono (by simp)
  · exact (fu.trans fv).mono (by intro A hA h;exact h.elim id False.elim)

#print axioms invalid_front
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_tail : CodeAt Images.expandImage (pcOf 1) frontTail := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_zero : CodeAt Images.expandImage (pcOf 42719) zeroBlk := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_jump : CodeAt Images.expandImage (pcOf 30) [0x7892b06f] := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_invalid : CodeAt Images.expandImage (pcOf 44192) [0xb08d506f] := by
  apply codeAt_expand_current_chunk <;> decide +kernel
#print axioms installed_tail
#print axioms installed_zero
#print axioms installed_jump
#print axioms installed_invalid
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem dataBase_of_length {im:Image} (h:im.data.length=29808) : dataBase im=DB := by
  unfold dataBase
  rw[h]
  rfl

theorem installed_dataBase : dataBase Images.expandImage=DB :=
  dataBase_of_length Images.expandData_length

theorem initial_data (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    DataAt (w9init Images.expandImage m pk b) := by
  exact prefixData Images.expandData_length installed_dataBase Images.expandSharedData
    (Images.expandPrefixData++Images.expandLegacyData) Images.expandSharedData_length
    (by change Images.expandData=Images.expandSharedData++(Images.expandPrefixData++Images.expandLegacyData)
        simp only[Images.expandData,List.append_assoc]) m pk b

#print axioms installed_dataBase
#print axioms initial_data
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def InflatedAt (s : MachineState) (b : SharedCodec.CBytes) : Prop :=
  ∀k,k<332 → DigAt s (0x7000+16*k)
    (SharedCodec.inflatedRead (0:Digest) (SharedCodec.digC b) k)

theorem InflatedAt.value {s : MachineState} {b : SharedCodec.CBytes} (h : InflatedAt s b)
    (k : Fin 9) (i : Fin 6) :
    DigAt s (SharedScatter.coordSource k.val+16*i.val)
      (Paired.coordinateValues (SharedCodec.sigDecC b).forest k i) := by
  have hh:=h (1+13*k.val+i.val) (by have:=k.isLt;have:=i.isLt;omega)
  rw [inflated_coordinate_value] at hh
  convert hh using 1 <;> unfold SharedScatter.coordSource <;> omega

theorem InflatedAt.path {s : MachineState} {b : SharedCodec.CBytes} (h : InflatedAt s b)
    (k : Fin 9) (level : Nat) (hl : level < if k.val<8 ∧ k.val%2=0 then 6 else 7) :
    DigAt s (SharedScatter.coordSource k.val+96+16*level)
      (Paired.coordinatePath (SharedCodec.sigDecC b).forest k level) := by
  have hb:level<7:=by split_ifs at hl <;> omega
  have hh:=h (1+13*k.val+6+level) (by have:=k.isLt;omega)
  rw [inflated_coordinate_path b k level hl] at hh
  convert hh using 1 <;> unfold SharedScatter.coordSource <;> omega
#print axioms InflatedAt.value
#print axioms InflatedAt.path
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem sourceReadout_of_fields (w : W9Machine.WBytes) (s : MachineState) (k : Fin 9)
    (child : Fin 128) (values : Fin 6→Digest) (path : Nat→Digest)
    (hv : ∀i:Fin 6,DigAt s (coordSource k.val+16*i.val) (values i))
    (hp : ∀l,l<SharedV3.lastLevel k.val+2 → DigAt s (coordSource k.val+96+16*l) (path l))
    (hc : ∀i:Fin 6,wdig w (V3.chainOffset k.val i.val+48)=values i)
    (he : ∀i:Fin 6,wdig w (V3.regionOffset k.val+V3.leafSlot i.val)=values i)
    (hs : ∀l,l<SharedV3.lastLevel k.val+1 → wdig w (V3.regionOffset k.val+SharedV3.sibOff child.val l)=path l)
    (ht : wdig w (SharedV3.topOtherOff k.val child.val)=path (SharedV3.lastLevel k.val+1)) :
    SourceReadout w s k.val child.val := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi; rw[hc ⟨i,hi⟩];exact hv ⟨i,hi⟩
  · intro i hi hip;rw[he ⟨i,hi⟩];exact hv ⟨i,hi⟩
  · intro l hl
    have hb:l<SharedV3.lastLevel k.val+1:=by unfold SharedV3.lastLevel;split_ifs <;> omega
    rw[hs l hb];exact hp l (by omega)
  · intro hn
    have hf:SharedV3.first k.val=false:=by simpa[SharedV3.first,firstCoord] using hn
    have hl:SharedV3.lastLevel k.val=5:=by simp[SharedV3.lastLevel,hf]
    rw[hs 5 (by omega)]
    simpa using hp 5 (by omega)
  · rw[ht,topInput_source k]
    simpa only [Nat.add_assoc] using hp (SharedV3.lastLevel k.val+1) (by omega)
#print axioms sourceReadout_of_fields
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.T3M Paired W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem canonical_sourceReadout (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s : MachineState) (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest) (k : Fin 9) :
    SourceReadout (witEnc output witness) s k.val
      (SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val) := by
  let child : Fin 128 := ⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
    coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
  have hc:child.val=SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val:=coordPhysical_source _ _
  rw[←hc]
  apply sourceReadout_of_fields (witEnc output witness) s k child
    (coordinateValues witness.signature.forest k) (coordinatePath witness.signature.forest k)
  · intro i;rw[hforest];exact hin.value k i
  · intro l hl
    rw[hforest]
    apply hin.path k l
    simp only [SharedV3.lastLevel,SharedV3.first,decide_eq_true_eq] at hl
    split_ifs at hl ⊢ with h <;> simp_all
  · exact wchainValue_witEnc output witness k
  · exact wleafValue_witEnc output witness k
  · intro l hl
    rw[hc]
    exact wsibling_witEnc output witness k l hl
  · rw[hc]
    exact wtopOther_witEnc output witness k
#print axioms canonical_sourceReadout
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.Research.SharedPathPacking
open ClaudeWCT.W9.Machine.Expand.SharedScatter
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem plans_data (child : Fin 128) (j : Fin 5) :
    Images.expandSharedData.getD (1024+5*(child.val%32)+j.val) 0=
      BitVec.ofNat 8 (packedSlots child.val j.val) := by
  have h:∀child:Fin 128,∀j:Fin 5,
      Images.expandSharedData.getD (1024+5*(child.val%32)+j.val) 0=
      BitVec.ofNat 8 (packedSlots child.val j.val):=by decide +kernel
  exact h child j

theorem DataAt.plans {s : MachineState} (h:DataAt s) : SharedScatter.PlanAt s := by
  intro child j hj
  have hm:=Nat.mod_lt child.val (by decide:0<32)
  rw [show 16748432+5*(child.val%32)+j=DB+(1024+5*(child.val%32)+j) by unfold DB;omega,
    h _ (by omega)]
  exact plans_data child ⟨j,hj⟩
#print axioms plans_data
#print axioms DataAt.plans
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! Stage 2 (C3) seam to the paired witness readout of `ClaudeWCT/W9/T3M/Witness/Honest.lean`. The honest witness word
at `WIT + 24` (the L3 encoding row tweak's high word) is the C3 pad, LE64 1. Neither forest pass writes it: in the
search pass it still holds the cleared 0 (`SharedForestRun.Inv` does not track it), and the final pass restores it
(`finishCode`). The next two theorems are the only places where the expander proofs depend on how `Honest.lean`
states the pad; the `first` alternatives accept the plausible shapes of the readout lemma's new hypothesis. -/

/-- The 64-bit witness word at offset 24 is the L3 row tweak's high word. -/
theorem witWord24_eq_wbcHigh (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) :
    w.extractLsb' (8*24) 64 = ClaudeWCT.W9.T3M.wbcHigh w index 3 := by
  have h0 : ClaudeWCT.W9.T3M.rowBlock index 3 = 0 := by
    first | rfl | simp [ClaudeWCT.W9.T3M.rowBlock]
  unfold ClaudeWCT.W9.T3M.wbcHigh ClaudeWCT.W9.T3M.wdig
  rw [h0]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, show 64+j<128 by omega]
  congr 1
  omega

/-- The honest paired witness carries the C3 pad LE64 1 at `WIT + 24` (from `Paired.wbcHigh_witEnc`, the paired
counterpart of `wbcHigh_witEnc` in `Witness/Honest.lean`). -/
theorem witPad24_witEnc (output : HashOutput) (witness : SharedForest.Witness) :
    (Paired.witEnc output witness).extractLsb' (8*24) 64 = 1#64 := by
  rw [witWord24_eq_wbcHigh _ (WCT9.digestIndex output)]
  first
  | exact Paired.wbcHigh_witEnc output witness 3
  | exact Paired.wbcHigh_witEnc (output:=output) (w:=witness) 3
  | exact Paired.wbcHigh_witEnc 3

/-- The witness prefix word at `off` after a pass that wrote only the forest slots over a cleared prefix: the
original word, except the counter word (`off = 32`, unless the counter is 0) and the C3 pad (`off = 24`). -/
theorem prefix_of_slots_c3 (output : HashOutput) (witness : SharedForest.Witness)
    (s t : MachineState) (W : Nat→Prop)
    (hslots : ∀p∈Paired.forestSlots output witness.signature,∀half,half<2→W (2904+p.1+8*half))
    (hread : ∀A,W A→W9Machine.OrigW (Paired.witEnc output witness) t A)
    (hframe : ∀A,A<2^64→¬W A→t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A))
    (hzero : ∀ (off : Nat), off + 8 ≤ 8096 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (2904+off))=0)
    (off:Nat) (hb:off+8≤8096) (ha:off%8=0) (hc:off≠32∨witness.counters 3=0) (hp:off≠24) :
    W9Machine.OrigW (Paired.witEnc output witness) t (2904+off) := by
  first
  | exact PairedReadout.original_prefix_of_slots output witness s t W hslots hread hframe hzero off hb ha hc hp
  | exact PairedReadout.original_prefix_of_slots output witness s t W hslots hread hframe hzero off hb ha ⟨hc,hp⟩
  | exact PairedReadout.original_prefix_of_slots output witness s t W hslots hread hframe hzero off hb ha hp hc
  | exact PairedReadout.original_prefix_of_slots output witness s t W hslots hread hframe hzero off hb ha ⟨hp,hc⟩
  | exact PairedReadout.original_prefix_of_slots output witness s t W hslots hread hframe hzero off hb ha hc
#print axioms witWord24_eq_wbcHigh
#print axioms witPad24_witEnc
#print axioms prefix_of_slots_c3

theorem ScatterInv.original_prefix (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s t : MachineState)
    (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hi : ScatterInv s (SharedForest.rawChildFromOutput output) 9 t)
    (hz : ∀ (off : Nat), off + 8 ≤ 8096 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (2904+off))=0)
    (off : Nat) (hb : off+8≤8096) (ha : off%8=0) (hc : off≠32∨witness.counters 3=0) (hp : off≠24) :
    W9Machine.OrigW (Paired.witEnc output witness) t (2904+off) := by
  let writes := fun A => ∃k:Fin 9,k.val<9 ∧
    PreciseCoordinateW k.val (coordPhysical k.val (SharedForest.rawChildFromOutput output k).val) A
  apply prefix_of_slots_c3 output witness s t writes _ _ _ hz off hb ha hc hp
  · intro p hp half hh
    obtain ⟨k,hk,hp⟩:=List.mem_flatMap.mp hp
    refine ⟨k,k.isLt,?_⟩
    let child:Fin 128:=⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
      coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
    apply rawSlots_written k child (Paired.coordinateValues witness.signature.forest k)
      (Paired.coordinatePath witness.signature.forest k) p _ half hh
    simpa only [Paired.coordinateSlots,rawSlots,child,coordPhysical_source] using hp
  · intro A hA
    obtain ⟨k,hk,hw⟩:=hA
    let child:Fin 128:=⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
      coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
    apply CoordinateReadout.original k child (hi.readout k hk) _ A hw
    simpa only [child,coordPhysical_source] using canonical_sourceReadout output witness b s hin hforest k
  · intro A hA hn
    exact hi.exactFrame.get hA hn
#print axioms ScatterInv.original_prefix
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem serializedWord_congr (r q : Nat→BitVec 64) (k : Nat) (hk:k<664)
    (h : ∀ j, j < 656 → r j = q j) : serializedWord r k=serializedWord q k := by
  unfold serializedWord
  split_ifs <;> first | rfl | rw[h _ (by omega)]

theorem hints_word (b : SharedCodec.CBytes) :
    b.extractLsb' (64*655) 64 >>> 48 = (b.extractLsb' (8*5246) 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,
    hj,decide_true,Bool.true_and]
  by_cases h:j<16
  · rw[show decide (48+j<64)=true from decide_eq_true (by omega),
      show decide (j<16)=true from decide_eq_true h]
    simp only [Bool.true_and]
    congr 1
    omega
  · rw[show decide (48+j<64)=false from decide_eq_false (by omega),
      show decide (j<16)=false from decide_eq_false h]
    simp

theorem serializedWord_eq (read : Nat→BitVec 64) (k : Nat) :
    serializedWord read k=SharedCodec.serializedWord read k := by rfl

theorem inflatedAt_of_words (s : MachineState) (b : SharedCodec.CBytes)
    (hw : ∀ k, k < 664 → s.getMem (BitVec.ofNat 64 (0x7000+8*k))=
      serializedWord (fun j=>b.extractLsb' (64*j) 64) k) : InflatedAt s b := by
  intro k hk
  have hlo:=hw (2*k) (by omega)
  have hhi:=hw (2*k+1) (by omega)
  rw [serializedWord_eq] at hlo hhi
  constructor
  · rw [show 0x7000+16*k=0x7000+8*(2*k) by omega]
    exact hlo.trans (by simpa only [Nat.add_zero,Nat.mul_zero] using
      SharedCodec.serializedWord_digC b k 0 (by decide))
  · rw [show 0x7000+16*k+8=0x7000+8*(2*k+1) by omega]
    exact hhi.trans (by simpa only [Nat.mul_one] using
      SharedCodec.serializedWord_digC b k 1 (by decide))

#print axioms serializedWord_congr
#print axioms hints_word
#print axioms inflatedAt_of_words
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem rawAt_of_fields {s : MachineState} {index : Nat} {raw : Fin 9→Fin 128}
    {ranks : Fin 9→Fin 563} (hf : SharedForestRun.Fields index raw ranks s) : RawAt s raw := by
  intro k
  convert hf.raw k using 1 <;> fin_cases k <;> rfl

section topzero
open SigGolfCandidate.T3 SigGolfCandidate.T3M ClaudeWCT.W9.T3M SigGolfCandidate.Research
/-- Pairing stage 1: with a zero top path, the witness's top path area words are zero. -/
theorem topArea_zero_word (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (htop : ∀ j, (witness.signature.layers 0).path j = 0) (off : Nat) (h1 : 8096 ≤ off) (h2 : off + 8 ≤ 8864) :
    (ClaudeWCT.W9.T3M.Paired.witEnc output witness).extractLsb' (8*off) 64 = 0 := by
  rw [ClaudeWCT.W9.T3M.Paired.word_witEnc_tail output witness off h1]
  unfold ClaudeWCT.W9.T3M.witEnc
  rw [show (64:Nat) = 8*8 from rfl, extract_readLE_lt _ 23236 (witList_readLE_lt _ _) off 8]
  have hw : ((ClaudeWCT.W9.T3M.witList output (ClaudeWCT.W9.T3M.Paired.mainWitness witness)).drop off).take 8 = zeros 8 := by
    have := win_topPath output (ClaudeWCT.W9.T3M.Paired.mainWitness witness) (off - 8096) 8 (by omega)
    rw [show ClaudeWCT.W9.T3M.layerBase 0 + (off-8096) = off by simp [ClaudeWCT.W9.T3M.layerBase]; omega] at this
    change window _ off 8 = _
    rw [this]
    unfold topPathBytes
    rw [window_map_range _ _ _ _ (by rw [pathSlots_top]; omega)]
    apply List.ext_getElem (by simp [zeros])
    intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range, zeros, List.getElem_replicate]
    unfold topPathByte
    split
    · rename_i j _
      change (SphincsSecurity.bytesLE 16 ((witness.signature.layers 0).path j)).getD _ 0 = 0
      rw [htop j, bytesLE_zero16]
      unfold zero16
      generalize off - 8096 + i - _ = n
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    · rfl
  rw [hw]; rfl
end topzero

theorem ScatterInv.forest_pre (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (index : Nat) (s t u : MachineState)
    (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (ht : ScatterInv s (SharedForest.rawChildFromOutput output) 9 t)
    (hfields : SharedForestRun.Fields index (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s)
    (uf : Frame t u (fun _=>False)) (up : u.pc=pcOf 46513)
    (hz : ∀ (off : Nat), off + 8 ≤ 8160 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (2904+off))=0)
    (hc3 : witness.counters 3=0) (htop : ∀ j, (witness.signature.layers 0).path j = 0) :
    SharedForestRun.Inv (Paired.witEnc output witness) index (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) u 0
      (SharedV3.initialPair (Paired.witEnc output witness)) u := by
  have hframe:Frame s u ScatterW:=
    (ht.frame.trans uf).mono (by intro A hA h;rcases h with h|h;exact h;exact h.elim)
  apply SharedForestRun.initial_of_original _ _ _ _ u up
  · exact SharedForestRun.fields_frame hframe hfields
  · intro A hA hB h8 hpad
    by_cases hlo : A-2904+8 ≤ 8096
    swap
    · unfold W9Machine.OrigW
      rw [show A - 0xB58 = A - 2904 by rfl, topArea_zero_word output witness htop _ (by omega) (by omega),
        hframe.get (by omega) (by unfold ScatterW; omega), show A = 2904 + (A - 2904) by omega]
      exact hz _ (by omega) (by omega)
    have ho:A-2904+8≤8096:=hlo
    have he:2904+(A-2904)=A:=by omega
    have hw:=ScatterInv.original_prefix output witness b s t hin hforest ht
      (fun off h1 h2 => hz off (by omega) h2) (A-2904) ho
      (by omega) (Or.inr hc3) (by omega)
    rw[he] at hw
    unfold W9Machine.OrigW at hw ⊢
    rw[uf.get (by omega) (fun h=>h)]
    exact hw
#print axioms rawAt_of_fields
#print axioms ScatterInv.forest_pre
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem hints_of_signature (s : MachineState) (b : SharedCodec.CBytes)
    (hsig : ∀ j, j < 656 → s.getMem (BitVec.ofNat 64 (0x7000+8*j))=b.extractLsb' (64*j) 64) :
    s.getMem 0x8478 >>> 48=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat := by
  have hh : s.getMem 0x8478=b.extractLsb' (64*655) 64 := hsig 655 (by decide)
  rw [hh,hints_word]
  change (b.extractLsb' (8*5246) 16).setWidth 64=BitVec.ofNat 64 (b.extractLsb' (8*5246) 16).toNat
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]

theorem inflatedAt_of_readout (s t : MachineState) (b : SharedCodec.CBytes)
    (hsig : ∀ j, j < 656 → s.getMem (BitVec.ofNat 64 (0x7000+8*j))=b.extractLsb' (64*j) 64)
    (hout : ∀ k, k < 664 → t.getMem (BitVec.ofNat 64 (0x7000+8*k))=
      serializedWord (fun j=>s.getMem (BitVec.ofNat 64 (0x7000+8*j))) k) : InflatedAt t b := by
  apply inflatedAt_of_words
  intro k hk
  exact (hout k hk).trans (serializedWord_congr _ _ k hk hsig)

theorem InflatedAt.frame {s t : MachineState} {b : SharedCodec.CBytes} (h : InflatedAt s b)
    {W : Nat→Prop} (hf : Frame s t W)
    (hn : ∀A,0x7000≤A → A<0x84c0 → ¬W A) : InflatedAt t b := by
  intro k hk
  have hh:=h k hk
  constructor
  · rw[hf.get (by omega) (hn _ (by omega) (by omega))]
    exact hh.1
  · rw[hf.get (by omega) (hn _ (by omega) (by omega))]
    exact hh.2
#print axioms hints_of_signature
#print axioms inflatedAt_of_readout
#print axioms InflatedAt.frame
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem scatter_forest_pre {im : Image} (hc : ∀k:Fin 9,CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) afterCode)
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec.CBytes)
    (index : Nat) (s : MachineState) (hp : s.pc=pcOf 45257)
    (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hfields : SharedForestRun.Fields index (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s)
    (hplan : PlanAt s) (hmode : s.getMem 417824=0)
    (hz : ∀ (off : Nat), off + 8 ≤ 8160 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (2904+off))=0)
    (hc3 : witness.counters 3=0) (htop : ∀ j, (witness.signature.layers 0).path j = 0) :
    ∃u, Steps im s 1256 1433 u ∧
      SharedForestRun.Inv (Paired.witEnc output witness) index (SharedForest.rawChildFromOutput output)
        (fun k=>SharedForest.forestRank output k.val) u 0
        (SharedV3.initialPair (Paired.witEnc output witness)) u ∧ Frame s u ScatterW := by
  obtain ⟨t,st,ht⟩:=scatter_steps hc s _ (rawAt_of_fields hfields) hplan hp
  obtain ⟨u,tu,up,ur,uf⟩:=after_steps ha t ht.pc
  have hm:t.getMem 417824=0:=by
    exact (ht.frame.get (A := 417824) (by decide) (by unfold ScatterW;omega)).trans hmode
  have hpc:u.pc=pcOf 46513:=by simpa only [hm,ite_true] using up
  have hframe:Frame s u ScatterW:=
    (ht.frame.trans uf).mono (by intro A hA h;rcases h with h|h;exact h;exact h.elim)
  refine ⟨u,st.trans tu,?_,hframe⟩
  exact ScatterInv.forest_pre output witness b index s t u hin hforest ht hfields uf hpc hz hc3 htop
#print axioms scatter_forest_pre
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def ForestAt (s : MachineState) (b : SharedCodec.CBytes) : Prop :=
  ∀k,k<118 → DigAt s (0x7000+16*k)
    (SharedCodec.inflatedRead (0:Digest) (SharedCodec.digC b) k)

theorem ForestAt.value {s : MachineState} {b : SharedCodec.CBytes} (h : ForestAt s b)
    (k : Fin 9) (i : Fin 6) :
    DigAt s (SharedScatter.coordSource k.val+16*i.val)
      (Paired.coordinateValues (SharedCodec.sigDecC b).forest k i) := by
  have hh:=h (1+13*k.val+i.val) (by have:=k.isLt;have:=i.isLt;omega)
  rw [inflated_coordinate_value] at hh
  convert hh using 1 <;> unfold SharedScatter.coordSource <;> omega

theorem ForestAt.path {s : MachineState} {b : SharedCodec.CBytes} (h : ForestAt s b)
    (k : Fin 9) (level : Nat) (hl : level < if k.val<8 ∧ k.val%2=0 then 6 else 7) :
    DigAt s (SharedScatter.coordSource k.val+96+16*level)
      (Paired.coordinatePath (SharedCodec.sigDecC b).forest k level) := by
  have hb:level<7:=by split_ifs at hl <;> omega
  have hh:=h (1+13*k.val+6+level) (by have:=k.isLt;omega)
  rw [inflated_coordinate_path b k level hl] at hh
  convert hh using 1 <;> unfold SharedScatter.coordSource <;> omega
#print axioms ForestAt.value
#print axioms ForestAt.path
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.T3M Paired W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem canonical_sourceReadout_forest (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s : MachineState) (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest) (k : Fin 9) :
    SourceReadout (witEnc output witness) s k.val
      (SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val) := by
  let child : Fin 128 := ⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
    coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
  have hc:child.val=SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val:=coordPhysical_source _ _
  rw[←hc]
  apply sourceReadout_of_fields (witEnc output witness) s k child
    (coordinateValues witness.signature.forest k) (coordinatePath witness.signature.forest k)
  · intro i;rw[hforest];exact hin.value k i
  · intro l hl
    rw[hforest]
    apply hin.path k l
    simp only [SharedV3.lastLevel,SharedV3.first,decide_eq_true_eq] at hl
    split_ifs at hl ⊢ with h <;> simp_all
  · exact wchainValue_witEnc output witness k
  · exact wleafValue_witEnc output witness k
  · intro l hl
    rw[hc]
    exact wsibling_witEnc output witness k l hl
  · rw[hc]
    exact wtopOther_witEnc output witness k
#print axioms canonical_sourceReadout_forest
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ScatterInv.original_prefix_forest (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s t : MachineState)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hi : ScatterInv s (SharedForest.rawChildFromOutput output) 9 t)
    (hz : ∀ (off : Nat), off + 8 ≤ 8096 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (2904+off))=0)
    (off : Nat) (hb : off+8≤8096) (ha : off%8=0) (hc : off≠32∨witness.counters 3=0) (hp : off≠24) :
    W9Machine.OrigW (Paired.witEnc output witness) t (2904+off) := by
  let writes := fun A => ∃k:Fin 9,k.val<9 ∧
    PreciseCoordinateW k.val (coordPhysical k.val (SharedForest.rawChildFromOutput output k).val) A
  apply prefix_of_slots_c3 output witness s t writes _ _ _ hz off hb ha hc hp
  · intro p hp half hh
    obtain ⟨k,hk,hp⟩:=List.mem_flatMap.mp hp
    refine ⟨k,k.isLt,?_⟩
    let child:Fin 128:=⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
      coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
    apply rawSlots_written k child (Paired.coordinateValues witness.signature.forest k)
      (Paired.coordinatePath witness.signature.forest k) p _ half hh
    simpa only [Paired.coordinateSlots,rawSlots,child,coordPhysical_source] using hp
  · intro A hA
    obtain ⟨k,hk,hw⟩:=hA
    let child:Fin 128:=⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
      coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
    apply CoordinateReadout.original k child (hi.readout k hk) _ A hw
    simpa only [child,coordPhysical_source] using canonical_sourceReadout_forest output witness b s hin hforest k
  · intro A hA hn
    exact hi.exactFrame.get hA hn
#print axioms ScatterInv.original_prefix_forest
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M

theorem InflatedAt.forest {s:MachineState} {b:SharedCodec.CBytes} (h:InflatedAt s b) : ForestAt s b :=
  fun k hk=>h k (by omega)

theorem ForestAt.frame {s t:MachineState} {b:SharedCodec.CBytes} (h:ForestAt s b)
    {W:Nat → Prop} (hf:Frame s t W)
    (hn:∀A,0x7000≤A → A<0x7760 → ¬W A) : ForestAt t b := by
  intro k hk
  have hh:=h k hk
  constructor
  · rw[hf.get (by omega) (hn _ (by omega) (by omega))]
    exact hh.1
  · rw[hf.get (by omega) (hn _ (by omega) (by omega))]
    exact hh.2
#print axioms InflatedAt.forest
#print axioms ForestAt.frame
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def Work (A : Nat) : Prop :=
  A=SharedCompact.policyAddress ∨ (0x70d0≤A ∧ A<0x84c0) ∨ Writes A

structure Prepared (s0:MachineState) (message:SigGolfCandidate.T3.Message) (b:SharedCodec.CBytes) (s:MachineState) : Prop where
  pc : s.pc=pcOf 45056
  x5 : s.getReg .x5=0
  rho : DigAt s DIG (SharedCodec.sigDecC b).rho
  msg : ∀k,k < 4 → s.getMem (BitVec.ofNat 64 (DIG+32+8*k))=message.extractLsb' (64*k) 64
  inflated : SharedCompact.InflatedAt s b
  hints : s.getMem (BitVec.ofNat 64 SharedCompact.policyAddress)=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat
  data : SharedInit.DataAt s
  frame : Frame s0 s Work
  setupZero : ∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0

theorem prepare {im:Image} (he:CodeAt im (pcOf 0) [SharedCompact.entryWord])
    (hc:SharedCompact.AdapterCodeAt im) (hf:CodeAt im (pcOf 1) frontTail)
    (hz:CodeAt im (pcOf 42719) zeroBlk) (hj:CodeAt im (pcOf 30) [0x7892b06f])
    (s:MachineState) (message:SigGolfCandidate.T3.Message) (b:SharedCodec.CBytes)
    (hp:s.pc=pcOf 0) (h5:s.getReg .x5=0)
    (hb:∀k,k < 656 → s.getMem (BitVec.ofNat 64 (0x7000+8*k))=b.extractLsb' (64*k) 64)
    (hm:∀k,k < 4 → s.getMem (BitVec.ofNat 64 (0x6620+8*k))=message.extractLsb' (64*k) 64)
    (hd:SharedInit.DataAt s) (hh:(SharedCodec.sigDecC b).policyHints.toNat<5832) :
    ∃t,Steps im s 3249 3249 t ∧ Prepared s message b t := by
  obtain ⟨u,su,up,uz,ur,uh,ub,uf⟩:=SharedCompact.front_readout he hc s hp
    (SharedCodec.sigDecC b).policyHints.toNat hh (SharedCompact.hints_of_signature s b hb)
  have ui:SharedCompact.InflatedAt u b:=SharedCompact.inflatedAt_of_readout s u b hb ub
  obtain ⟨t,ut,tp,t5,t0,t8,tm,tz,tr,tf⟩:=setup hf hz hj u up (ur.get (by decide) |>.trans h5)
  refine ⟨t,su.trans ut,⟨tp,t5,?_,?_,?_,?_,?_,?_,tz⟩⟩
  · have hr:=ui 0 (by decide)
    change DigAt u 0x7000 (SharedCodec.sigDecC b).rho at hr
    exact ⟨(t0 DIG (Or.inr rfl)).trans hr.1,(t8 (DIG+8) (Or.inr rfl)).trans hr.2⟩
  · intro k hk
    exact (tm k hk).trans ((uf.get (by omega) (by unfold SharedCompact.policyAddress;omega)).trans (hm k hk))
  · exact ui.frame tf (by intro A hA hB hw;unfold Writes at hw;simp only [DIG] at hw;omega)
  · exact (tf.get (by unfold SharedCompact.policyAddress;omega) (by unfold Writes SharedCompact.policyAddress DIG;omega)).trans uh
  · intro i hi
    have x:=hd i hi
    have hm : t.getByte (BitVec.ofNat 64 (SharedInit.DB+i))=s.getByte (BitVec.ofNat 64 (SharedInit.DB+i)) :=
      (uf.trans tf).getByte (by unfold SharedInit.DB;omega) (by
        intro h;rcases h with h|h
        · unfold SharedCompact.policyAddress SharedInit.DB at h;omega
        · unfold Writes SharedInit.DB DIG at h;omega)
    exact hm.trans x
  · exact (uf.trans tf).mono (by
      intro A hA h
      rcases h with (h|h)|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))

#print axioms prepare
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem DataAt.frame {s t:MachineState} {W:Nat → Prop} (h:DataAt s)
    (hf:Frame s t W) (hn:∀A,DB≤A → A<DB+2160 → ¬W A) : DataAt t := by
  intro i hi
  have hm : t.getByte (BitVec.ofNat 64 (DB+i))=s.getByte (BitVec.ofNat 64 (DB+i)) :=
    hf.getByte (by unfold DB;omega) (hn _ (by unfold DB;omega) (by unfold DB;omega))
  exact hm.trans (h i hi)
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def SearchWrites (A:Nat) : Prop := Work A ∨ SharedDigest.writes A
structure Searched (s0:MachineState) (b:SharedCodec.CBytes)
    (r:Option (BitVec 32 × BitVec 256)) (s:MachineState) : Prop where
  x5 : s.getReg .x5=0
  inflated : SharedCompact.InflatedAt s b
  hints : s.getMem (BitVec.ofNat 64 SharedCompact.policyAddress)=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat
  data : SharedInit.DataAt s
  frame : Frame s0 s SearchWrites
  setupZero : ∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0
  result : match r with
    | none => s.pc=pcOf (SharedDigest.fail true)
    | some (c,a) => s.pc=pcOf (SharedDigest.accepted true) ∧ s.getReg .x19=BitVec.ofNat 64 c.toNat ∧
      c.toNat < 2^21 ∧ SigGolfCandidate.Research.SharedForest.digestAccepted a=true ∧ OutAt s SigGolfCandidate.T3M.Search.NBUF a

  resultR17 : match r with
    | none => True
    | some _ => s.getReg .x17=BitVec.ofNat 64 SigGolfCandidate.T3M.Search.NBUF

theorem search_prepared {im:Image} {sk:BitVec 256}
    (hl:SigGolfCandidate.T3M.Verify.LookOK im (SharedDigest.look true))
    {s0 s:MachineState} {message:SigGolfCandidate.T3.Message} {b:SharedCodec.CBytes}
    (hp:Prepared s0 message b s) :
    TBSim im sk s (2^21*200+12)
      (SigGolfCandidate.Research.SharedForest.sharedDigestSearch (SharedCodec.sigDecC b).rho message 0 (2^21))
      (Searched s0 b) := by
  have hpre:SharedDigest.Pre true (SharedCodec.sigDecC b).rho message s:=
    ⟨hp.x5,hp.rho,hp.msg,hp.data.tables⟩
  exact (SharedDigest.search_good true hl hpre hp.pc).mono (by omega) (by
    intro r t ht
    refine ⟨ht.x5,?_,?_,?_,hp.frame.trans ht.frame,?_,?_,?_⟩
    · exact hp.inflated.frame ht.frame (by intro A hA hB hw;simp only [SharedDigest.writes,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF,SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF] at hw;omega)
    · exact (ht.frame.get (by unfold SharedCompact.policyAddress;omega)
        (by simp only [SharedDigest.writes,SharedCompact.policyAddress,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF,SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF];omega)).trans hp.hints
    · exact hp.data.frame ht.frame (by intro A hA hB hw;simp only [SharedDigest.writes,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF,SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF] at hw;unfold SharedInit.DB at hA hB;omega)
    · intro A ha
      rw [ht.frame.get (by rcases ha with rfl|rfl|rfl|rfl <;> decide)
        (by rcases ha with rfl|rfl|rfl|rfl <;> simp [SharedDigest.writes,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF,SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF])]
      exact hp.setupZero A ha
    · cases r with
      | none => exact ht.result.1
      | some p => exact ht.result
    · cases r <;> exact ht.resultR17)
#print axioms search_prepared
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem legacyByte {im : Image} (hlen : im.data.length = 29808)
    (pre : List (BitVec 8)) (hp : pre.length = 25712)
    (hd : im.data = pre ++ Images.expandLegacyData)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (i : Nat) (hi : i < 4096) :
    (w9init im m pk b).getByte (BitVec.ofNat 64 (TOP_DATA + i)) = Images.expandLegacyData.getD i 0 := by
  rw [show TOP_DATA + i = DB + (25712+i) by unfold TOP_DATA DB; omega,
    dataByte hlen (dataBase_of_length hlen) m pk b _ (by omega), hd]
  exact getD_prefixed pre Images.expandLegacyData 25712 i hp

theorem initial_tables_of_data {im : Image} (hlen : im.data.length = 29808)
    (pre : List (BitVec 8)) (hp : pre.length = 25712)
    (hd : im.data = pre ++ Images.expandLegacyData)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    TableOK (w9init im m pk b) ∧ CfTableOK 0 (w9init im m pk b) ∧
      Reward.RewardTablesOK (w9init im m pk b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [legacyByte hlen pre hp hd m pk b i (by omega)]
    exact expandLegacyData_table i hi
  · intro i hi hj
    rw [legacyByte hlen pre hp hd m pk b i (by omega)]
    exact expandLegacyData_cf i hi hj
  · intro i hi hj
    rw [legacyByte hlen pre hp hd m pk b i (by omega)]
    exact expandLegacyData_reward i hi hj

theorem initial_tables (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    TableOK (w9init Images.expandImage m pk b) ∧ CfTableOK 0 (w9init Images.expandImage m pk b) ∧
      Reward.RewardTablesOK (w9init Images.expandImage m pk b) := by
  exact initial_tables_of_data Images.expandData_length
    (Images.expandSharedData ++ Images.expandPrefixData)
    (by simp only [List.length_append, Images.expandSharedData_length, Images.expandPrefixData_length])
    (by rfl) m pk b
#print axioms initial_tables
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Layer Digest chainCount height)
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem inflated_main (b : SharedCodec.CBytes) (i : Nat) (hi : 114 ≤ i) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) (i+4)=SharedCodec.digC b i := by
  unfold SharedCodec.inflatedRead SharedCodec.internalDummy SharedCodec.externalFullIndex
  simp only [show ¬(i+4=13 ∨ i+4=39 ∨ i+4=65 ∨ i+4=91) by omega,decide_false,Bool.false_eq_true,if_false,
    if_pos (show 13 < i+4 by omega),if_pos (show 39 < i+4 by omega),if_pos (show 65 < i+4 by omega),if_pos (show 91 < i+4 by omega)]
  congr 1

theorem lP_shared (lay : Layer) :
    SigGolfCandidate.T3M.Expand.lP lay=30864+16*(SharedCodec.layIdx lay-114) ∧
    114 ≤ SharedCodec.layIdx lay ∧ SharedCodec.layIdx lay+chainCount lay+height lay ≤ 328 := by
  fin_cases lay <;> decide

theorem main_readout {b : SharedCodec.CBytes} {s t : MachineState}
    (hsource : SharedCompact.InflatedAt s b)
    (hmove : ∀i<428,t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i))) :
    SigGolfCandidate.T3M.Expand.BC.SigLayersAt t (SharedForest.mainSignature (SharedCodec.sigDecC b)) := by
  have hrows : ∀i<214,DigAt t (30864+16*i) (SharedCodec.digC b (114+i)) := by
    intro i hi
    have h:=hsource (118+i) (by omega)
    rw [show 118+i=(114+i)+4 by omega,inflated_main b _ (by omega)] at h
    have ha:0x7000+16*(114+i+4)=30560+16*i:=by omega
    rw [ha] at h
    refine ⟨?_,?_⟩
    · have hm:=hmove (2*i) (by omega)
      rw [show 30864+8*(2*i)=30864+16*i by omega,show 30560+8*(2*i)=30560+16*i by omega] at hm
      exact hm.trans h.1
    · have hm:=hmove (2*i+1) (by omega)
      rw [show 30864+8*(2*i+1)=30864+16*i+8 by omega,show 30560+8*(2*i+1)=30560+16*i+8 by omega] at hm
      exact hm.trans h.2
  intro lay
  obtain ⟨hp,hl,hh⟩:=lP_shared lay
  constructor
  · intro i hi
    have h:=hrows (SharedCodec.layIdx lay-114+i) (by omega)
    rw [show 114+(SharedCodec.layIdx lay-114+i)=SharedCodec.layIdx lay+i by omega,
      show 30864+16*(SharedCodec.layIdx lay-114+i)=SigGolfCandidate.T3M.Expand.lP lay+16*i by rw[hp];omega] at h
    exact h
  · intro j hj
    have h:=hrows (SharedCodec.layIdx lay-114+chainCount lay+j) (by omega)
    rw [show 114+(SharedCodec.layIdx lay-114+chainCount lay+j)=SharedCodec.layIdx lay+chainCount lay+j by omega,
      show 30864+16*(SharedCodec.layIdx lay-114+chainCount lay+j)=SigGolfCandidate.T3M.Expand.lP lay+16*chainCount lay+16*j by rw[hp];omega] at h
    exact h
#print axioms main_readout
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M.Search (ENC NODE)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def Writes (A : Nat) : Prop :=
  A=0x20260 ∨ A=0x20268 ∨ A=0x20290 ∨ A=0x20298 ∨ (2048≤A ∧ A<2112) ∨ (30864≤A ∧ A<34288)

theorem layer_inv {b : SharedCodec.CBytes} {s t : MachineState} {index : Nat} {pair : Digest × Digest}
    (hp : t.pc=pcOf 249) (h5 : t.getReg .x5=0) (hi : index<2^31)
    (hidx : s.getMem (BitVec.ofNat 64 SigGolfCandidate.T3M.Expand.IDXV)=BitVec.ofNat 64 index)
    (hin : SharedCompact.InflatedAt s b)
    (hL : DigAt s 2904 pair.1) (hR : DigAt s 2952 pair.2)
    (hroots : ∀o,(o=0 ∨ o=8 ∨ o=48 ∨ o=56) → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (2904+o)))
    (hmove : ∀i,i<428 → t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i)))
    (hf : Frame s t Writes)
    (hc32 : ∃x<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x)
    (hz : SigGolfCandidate.T3M.Expand.BC.LZero s)
    (htab : Search.TableOK s) (hcf : Search.CfTableOK 0 s) (hrew : Search.Reward.RewardTablesOK s)
    (hhint : (SharedCodec.sigDecC b).policyHints.toNat<5832)
    (hhmem : s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat) :
    SigGolfCandidate.T3M.Expand.SharedLayers.LInv (SharedForest.mainSignature (SharedCodec.sigDecC b))
      (SharedCodec.sigDecC b).policyHints index 4 (.pair pair.1 pair.2) t := by
  have keep (A : Nat) (ha : A<2^64) (hw : ¬Writes A) := hf.get ha hw
  refine ⟨⟨hp,by decide,h5,hi,?_,?_,?_,?_,?_,main_readout hin hmove,?_,?_,?_,?_⟩,hhint,?_⟩
  · exact (keep _ (by decide) (by unfold Writes; decide)).trans hidx
  · exact ⟨(hroots 0 (by simp)).trans hL.1,(hroots 8 (by simp)).trans hL.2⟩
  · intro _
    exact ⟨(hroots 48 (by simp)).trans hR.1,(hroots 56 (by simp)).trans hR.2⟩
  · intro h;omega
  · rcases hc32 with ⟨x,hx,hm⟩
    exact ⟨x,hx,(keep _ (by decide) (by unfold Writes; decide)).trans hm⟩
  · exact ⟨(keep _ (by decide) (by unfold Writes; decide)).trans hz.c0,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.c8,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.n32,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.n40,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.e40⟩
  · exact htab.frame hf (by intro i hi;unfold Writes Search.TOP_DATA;omega)
  · exact hcf.frame hf (by intro i hi hj;unfold Writes Search.TOP_DATA;omega)
  · exact hrew.frame hf (by intro i hi hj;unfold Writes Search.TOP_DATA;omega)
  · exact (keep _ (by decide) (by unfold Writes; decide)).trans hhmem
#print axioms layer_inv
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem shifted_data_mem {im ref : Image} (hlen : im.data.length=29808)
    (pre : List (BitVec 8)) (hp : pre.length=2160) (hd : im.data=pre++ref.data)
    (href : ExpandDataOK ref) (m : Message) (pk : PublicKey) (b : Bytes 5248)
    (A : Nat) (hlo : Compact2.LPLAN≤A) (hhi : A<Compact2.LPLAN+27648) (hal : A%8=0) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=
      (w9init ref m pk (0 : Bytes 5312)).getMem (BitVec.ofNat 64 A) := by
  rw [getMem hlen (dataBase_of_length hlen) m pk b A (by unfold Compact2.LPLAN at *;omega),
    if_neg (by unfold Compact2.LPLAN at *;omega),if_neg (by unfold Compact2.LPLAN at *;omega),
    if_neg (by unfold Compact2.LPLAN at *;omega),if_pos (by unfold Compact2.LPLAN DB at *;omega),
    w9init_data href m pk (0 : Bytes 5312) A hlo hhi (by unfold Compact2.LPLAN;omega),hd]
  rw [show A-DB=2160+(A-Compact2.LPLAN) by unfold DB Compact2.LPLAN at *;omega,
    ←List.drop_drop,List.drop_left' hp]

theorem initial_plans_of_data {im ref : Image} (hlen : im.data.length=29808)
    (pre : List (BitVec 8)) (hp : pre.length=2160) (hd : im.data=pre++ref.data)
    (href : ExpandDataOK ref) (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ClaudeWCT.W9.Machine.Expand.PlanAt (w9init im m pk b) ∧ Compact2.LPlanAt (w9init im m pk b) := by
  constructor
  · intro k hk
    rw [shifted_data_mem hlen pre hp hd href m pk b _ (by unfold PLAN Compact2.LPLAN;omega)
      (by unfold PLAN Compact2.LPLAN;omega) (by unfold PLAN;omega)]
    exact w9init_plan href m pk (0 : Bytes 5312) k hk
  · intro k hk
    rw [shifted_data_mem hlen pre hp hd href m pk b _ (by omega)
      (by unfold Compact2.LPLAN;omega) (by unfold Compact2.LPLAN;omega)]
    exact w9init_lplan href m pk (0 : Bytes 5312) k hk

theorem reference_data_ok : ExpandDataOK (⟨[],Images.expandPrefixData++Images.expandLegacyData⟩ : Image) := by
  change Images.expandPrefixData++Images.expandLegacyData = _
  have hp : Images.expandPrefixData = lplanBytes++planBytes++expCostBytes++hdrBankBytes := by
    unfold Images.expandPrefixData lplanBytes planBytes expCostBytes hdrBankBytes
    rw [←List.flatten_append,←List.flatten_append,←List.flatten_append]
    rfl
  rw [hp]

theorem initial_plans (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ClaudeWCT.W9.Machine.Expand.PlanAt (w9init Images.expandImage m pk b) ∧
      Compact2.LPlanAt (w9init Images.expandImage m pk b) := by
  exact initial_plans_of_data (ref:=⟨[],Images.expandPrefixData++Images.expandLegacyData⟩)
    Images.expandData_length Images.expandSharedData Images.expandSharedData_length
    (by change (Images.expandSharedData++Images.expandPrefixData)++Images.expandLegacyData = _;rw[List.append_assoc])
    reference_data_ok m pk b
theorem initial_toptab (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    Compact2.TopTabAt (w9init Images.expandImage m pk b) := by
  have he (A : Nat) (hl : Compact2.LPLAN ≤ A) (hh : A < Compact2.LPLAN+27648) (hm : A % 8 = 0) :=
    shifted_data_mem (im:=Images.expandImage) (ref:=⟨[],Images.expandPrefixData++Images.expandLegacyData⟩)
      Images.expandData_length Images.expandSharedData Images.expandSharedData_length
      (by change (Images.expandSharedData++Images.expandPrefixData)++Images.expandLegacyData = _;rw[List.append_assoc])
      reference_data_ok m pk b A hl hh hm
  constructor
  · intro k hk
    rw [he _ (by unfold Compact2.TOPA Compact2.LPLAN;omega) (by unfold Compact2.TOPA Compact2.LPLAN;omega) (by unfold Compact2.TOPA;omega)]
    exact (w9init_toptab reference_data_ok m pk (0 : Bytes 5312)).1 k hk
  · intro k hk
    rw [he _ (by unfold Compact2.TOPB Compact2.LPLAN;omega) (by unfold Compact2.TOPB Compact2.LPLAN;omega) (by unfold Compact2.TOPB;omega)]
    exact (w9init_toptab reference_data_ok m pk (0 : Bytes 5312)).2 k hk
#print axioms initial_toptab
#print axioms initial_plans
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open ClaudeWCT.W9.T3M SigGolfCandidate.Research

theorem decoded_projection (b : SharedCodec.CBytes) :
    SharedForest.fillTopSignature (SharedCodec.sigDecC b) 0 = SharedCodec.sigDecC b := by
  have hset (x : BitVec 112) : ClaudeWCT.WCT9.setTop (x.setWidth 128) 0=x.setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    have hx := x.isLt
    simp only [ClaudeWCT.WCT9.setTop,BitVec.toNat_ofNat,BitVec.toNat_setWidth,
      Nat.zero_mod,Nat.zero_mul,Nat.add_zero]
    omega
  apply congrArg (fun layers => SharedForest.Signature.mk (SharedCodec.sigDecC b).rho
    (SharedCodec.sigDecC b).policyHints (SharedCodec.sigDecC b).forest layers)
  funext lay
  apply congrArg (fun path => SigGolfCandidate.T3.LayerSignature.mk
    ((SharedCodec.sigDecC b).layers lay).values path)
  funext j
  change (if lay.val=0 ∧ j.val=11 then
    ClaudeWCT.WCT9.setTop (((SharedCodec.sigDecC b).layers lay).path j) 0 else
    ((SharedCodec.sigDecC b).layers lay).path j) = _
  split
  next h =>
    have hl : lay=0 := Fin.ext h.1
    subst lay
    have hj : j.val=11 := h.2
    simpa only [SharedCodec.sigDecC,SharedCodec.layIdx,List.getElem_cons_zero,
      Matrix.cons_val_zero,SigGolfCandidate.T3.chainCount,hj,Nat.reduceAdd,
      SharedCodec.digC,show ¬(179<179) by decide,if_false,if_pos rfl,ite_true] using
      hset (b.extractLsb' (128*327) 112)
  next => rfl

theorem main_projection (b : SharedCodec.CBytes) :
    ClaudeWCT.WCT9.fillTop (SharedForest.mainSignature (SharedCodec.sigDecC b)) 0 =
      SharedForest.mainSignature (SharedCodec.sigDecC b) := by
  exact congrArg SharedForest.mainSignature (decoded_projection b)

#print axioms decoded_projection
#print axioms main_projection
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (ENC NODE)
open SigGolfCandidate.T3M.Expand (CHAIN)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem public_key_of_length {im : Image} (hlen : im.data.length=29808)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    DigAt (w9init im m pk b) 0xA0 pk := by
  have hword (i : Nat) (hi : i<2) :
      (w9init im m pk b).getMem (BitVec.ofNat 64 (0xA0+8*i))=pk.extractLsb' (64*i) 64 := by
    rw [getMem hlen (dataBase_of_length hlen) m pk b _ (by omega),
      if_neg (by omega),if_pos (by omega),show 0xA0+8*i-0xA0=8*i by omega]
    exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e pk i (by omega)
  exact ⟨hword 0 (by decide),hword 1 (by decide)⟩

theorem region_zero_of_length {im : Image} (hlen : im.data.length=29808)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ∀A,0x2c48≤A → A<0x61c8 → (w9init im m pk b).getMem (BitVec.ofNat 64 A)=0 := by
  intro A hlo hhi
  exact zero hlen (dataBase_of_length hlen) m pk b A
    (by unfold DB;omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))

theorem layer_zero_of_length {im : Image} (hlen : im.data.length=29808)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    SigGolfCandidate.T3M.Expand.BC.LZero (w9init im m pk b) := by
  constructor <;> apply zero hlen (dataBase_of_length hlen) m pk b <;>
    simp only [CHAIN,NODE,ENC,DB] <;> omega

theorem counter_of_length {im : Image} (hlen : im.data.length=29808)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ∃x<2^32,(w9init im m pk b).getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x := by
  refine ⟨0,by decide,?_⟩
  apply zero hlen (dataBase_of_length hlen) m pk b <;> simp only [ENC,DB] <;> omega

theorem initial_thresholds (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    (∀r,r<48 → (w9init Images.expandImage m pk b).getByte (BitVec.ofNat 64 (16749456+r))=
      BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 1 r)) ∧
    (∀r,r<35 → (w9init Images.expandImage m pk b).getByte (BitVec.ofNat 64 (16749520+r))=
      BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 2 r)) := by
  have h : SharedValidate.Tables (w9init Images.expandImage m pk b) := initial_data m pk b
  exact ⟨h.first,h.second⟩

#print axioms public_key_of_length
#print axioms region_zero_of_length
#print axioms layer_zero_of_length
#print axioms counter_of_length
#print axioms initial_thresholds
end ClaudeWCT.W9.Machine.Expand.SharedInit
