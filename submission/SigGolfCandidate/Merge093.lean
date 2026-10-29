import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge061
import SigGolfCandidate.Merge092

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_H2Front ====
section


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

/-- Final pass (words 47005..47011, then the `end` routine 43071..43076; 47012 is the halting `ecall`): restore
the L3 counter word at `WIT + 32` from `0x66018` and, stage 2 (C3), the L3 encoding row tweak's high word at `WIT + 24`
(a witness pad, honest LE64 1), which the final clear of `[WIT, WIT + 8256)` erased; the halt flag `t0 = 1` is stored
there. Word 47011 (e7b) jumps to `end`, which writes the choice hint byte (the flag word's low byte) at
`WIT + 22312` and sets `a0 := 0`. -/
def finishCode : List (BitVec 32) := bv_list% 32 [0x66e37,0x18e3303,0xfb040e93,0x26eb023,0x100293,0x5ebc23,0xa70fc06f]
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
theorem finish0_steps {im : Image} (hc : CodeAt im (pcOf 47005) finishCode)
    (s : MachineState) (hpc : s.pc=pcOf 47005) (h8 : s.getReg .x8=BitVec.ofNat 64 2984) :
    ∃t, Steps im s 7 7 t ∧ t.pc=pcOf 43071 ∧
      t.getMem (BitVec.ofNat 64 2936)=s.getMem (BitVec.ofNat 64 417816) ∧ t.getMem (BitVec.ofNat 64 2928)=1#64 ∧
      t.getReg .x5=1#64 ∧
      RegsExcept s t [.x5,.x6,.x28,.x29] ∧ Frame s t (fun A=>A=2936 ∨ A=2928) := by
  refine ⟨_,symRun_sound finishRun hc s hpc (by simp [finishRun.res,rv_simp,h8,accessValid_iff,MEMORY_BYTES]),?_,?_,?_,?_,?_,?_⟩
  · simp [finishRun.res, Result.toState_pc, E.eval]
  · rw [finish_mem s h8 2936 (by norm_num), if_neg (by norm_num), if_pos rfl]
  · rw [finish_mem s h8 2928 (by norm_num), if_pos rfl]
  · simp [finishRun.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    rw [finish_mem s h8 A hA, if_neg (by omega), if_neg (by omega)]
theorem finish_steps {im : Image} (hc : CodeAt im (pcOf 47005) finishCode) (he : CodeAt im (pcOf 43071) endCode)
    (s : MachineState) (hpc : s.pc=pcOf 47005) (h8 : s.getReg .x8=BitVec.ofNat 64 2984) :
    ∃t, Steps im s 13 13 t ∧ t.pc=pcOf 49400 ∧
      t.getMem (BitVec.ofNat 64 2936)=s.getMem (BitVec.ofNat 64 417816) ∧ t.getMem (BitVec.ofNat 64 2928)=1#64 ∧
      t.getMem (BitVec.ofNat 64 25216)=replaceByte (s.getMem (BitVec.ofNat 64 25216)) 0 (flagByte s) ∧
      t.getReg .x5=1#64 ∧ t.getReg .x10=0#64 ∧
      RegsExcept s t [.x5,.x6,.x10,.x28,.x29] ∧ Frame s t (fun A=>A=2936 ∨ A=2928 ∨ A=25216) := by
  obtain ⟨u,su,pu,u36,u28,u5,ru,fu⟩ := finish0_steps hc s hpc h8
  obtain ⟨t,st,pt,t10,t25,rt,ft⟩ := end_steps he u pu
  have hflag : flagByte u=flagByte s := by
    unfold flagByte; rw [fu.get (by norm_num) (by norm_num)]
  have hw : u.getMem (BitVec.ofNat 64 25216)=s.getMem (BitVec.ofNat 64 25216) := fu.get (by norm_num) (by norm_num)
  refine ⟨t,su.trans st,pt,?_,?_,?_,?_,t10,(ru.trans rt).mono (by decide),?_⟩
  · rw [ft.get (by norm_num) (by norm_num)]; exact u36
  · rw [ft.get (by norm_num) (by norm_num)]; exact u28
  · rw [t25,hw,hflag]
  · rw [rt.get (by decide)]; exact u5
  · exact (fu.trans ft).mono (fun A _ h => by rcases h with (h|h)|h <;> simp_all)
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
    destination (coordRegion k.val) 49 (child.val/32)=
      2904+V3.regionOffset k.val+SharedV3.sibOff child.val 5 := by
  rw [coordRegion_source]
  simp [destination,SharedV3.sibOff,SharedV3.blkOff,Nat.add_assoc]

theorem topDest_source (k : Fin 9) (child : Fin 128) :
    topDest k.val child.val=2904+SharedV3.topOtherOff k.val child.val := by
  have h : ∀k : Fin 9,∀child : Fin 128,
      topDest k.val child.val=2904+SharedV3.topOtherOff k.val child.val := by
    intro k;fin_cases k <;> decide +kernel
  exact h k child

/-- r3w (witness stack): chain value `i` of a coordinate at `valOff i = wctChainOff i + wctValueOff i`
(`640, 504, 576, 400, 472, 368`), written in an `omega`-friendly closed form. -/
theorem chainDestination_source (k : Fin 9) (i : Fin 6) :
    coordRegion k.val+(640+40*(i.val-(i.val-1))+72*(i.val/5)-52*i.val-124*(i.val%2))=2904+(V3.chainOffset k.val i.val+ClaudeWCT.W9.T3M.wctValueOff i.val) := by
  rw [coordRegion_source]
  simp only [V3.chainOffset]
  obtain ⟨i, hi⟩ := i
  interval_cases i <;>
    simp (config := {decide := true}) [ClaudeWCT.W9.T3M.wctChainOff, ClaudeWCT.W9.T3M.wctValueOff,
      ClaudeWCT.WCT9.ftsIsG] <;> omega

theorem leafDestination_source (k : Fin 9) (i : Fin 6) (hi : 0 < i.val) :
    coordRegion k.val+672+16*i.val=2904+(V3.regionOffset k.val+V3.leafSlot i.val) := by
  rw [coordRegion_source]
  simp [V3.leafSlot,Nat.ne_of_gt hi,Nat.add_assoc]

theorem topInput_source (k : Fin 9) : topInput k.val=96+16*(SharedV3.lastLevel k.val+1) := by
  fin_cases k <;> rfl
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

structure SourceReadout (w : W9Machine.WBytes) (s : MachineState) (k child : Nat) : Prop where
  values : ∀i<6,DigAt s (coordSource k+16*i) (wdig w (V3.chainOffset k i+ClaudeWCT.W9.T3M.wctValueOff i))
  ends : ∀i<6,0 < i → DigAt s (coordSource k+16*i) (wdig w (V3.regionOffset k+V3.leafSlot i))
  paths : ∀i<5,DigAt s (coordSource k+96+16*i) (wdig w (V3.regionOffset k+SharedV3.sibOff child i))
  sixth : ¬firstCoord k → DigAt s (coordSource k+176) (wdig w (V3.regionOffset k+SharedV3.sibOff child 5))
  top : DigAt s (coordSource k+topInput k) (wdig w (SharedV3.topOtherOff k child))

theorem orig_word {w : W9Machine.WBytes} {t : MachineState} (off half : Nat) (hh : half<2)
    (hm : t.getMem (BitVec.ofNat 64 (2904+off+8*half))=(wdig w off).extractLsb' (64*half) 64) :
    W9Machine.OrigWD 1224 w t (2904+off+8*half) := by
  unfold W9Machine.OrigWD
  rw [hm, show 2904+off+8*half+1224-0x1020 = off+8*half by omega]
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
    W9Machine.OrigWD 1224 w t A := by
  have hv : ∀i<6,∀half<2,W9Machine.OrigWD 1224 w t (coordRegion k.val+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8*half) := by
    intro i hi half hh
    rw [chainDestination_source k ⟨i,hi⟩]
    apply orig_word _ half hh
    rw [←chainDestination_source k ⟨i,hi⟩,h.values i hi half hh]
    exact digAt_half (hs.values i hi) half hh
  have he : ∀i<6,0 < i → ∀half<2,W9Machine.OrigWD 1224 w t (coordRegion k.val+672+16*i+8*half) := by
    intro i hi hip half hh
    rw [leafDestination_source k ⟨i,hi⟩ hip]
    apply orig_word _ half hh
    rw [←leafDestination_source k ⟨i,hi⟩ hip,h.ends i hi hip half hh]
    exact digAt_half (hs.ends i hi hip) half hh
  have hp : ∀i<5,∀half<2,W9Machine.OrigWD 1224 w t (pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+8*half) := by
    intro i hi half hh
    rw [pathDestination_source k child ⟨i,hi⟩]
    rw [Nat.add_assoc 2904]
    apply orig_word _ half hh
    rw [←Nat.add_assoc 2904,←pathDestination_source k child ⟨i,hi⟩,h.paths i hi half hh]
    exact digAt_half (hs.paths i hi) half hh
  have h6 : ¬firstCoord k.val → ∀half<2,W9Machine.OrigWD 1224 w t (destination (coordRegion k.val) 49 (child.val/32)+8*half) := by
    intro hn half hh
    rw [sixthDestination_source k child,Nat.add_assoc 2904]
    apply orig_word _ half hh
    rw [←Nat.add_assoc 2904,←sixthDestination_source k child,h.sixth hn half hh]
    exact digAt_half (hs.sixth hn) half hh
  have ht : ∀half<2,W9Machine.OrigWD 1224 w t (topDest k.val child.val+8*half) := by
    intro half hh
    rw [topDest_source k child]
    apply orig_word _ half hh
    rw [←topDest_source k child,h.top half hh]
    exact digAt_half hs.top half hh
  rcases hA with ((ha|ha)|ha)|ha|ha
  · obtain ⟨i,hi,ha⟩:=ha
    rcases ha with ha|ha|⟨hip,ha|ha⟩
    · subst A;simpa using hv i hi 0 (by decide)
    · rw [ha,show coordRegion k.val+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2)+8)=coordRegion k.val+(640+40*(i-(i-1))+72*(i/5)-52*i-124*(i%2))+8 by omega]
      simpa using hv i hi 1 (by decide)
    · subst A;simpa using he i hi hip 0 (by decide)
    · rw [ha,show coordRegion k.val+680+16*i=coordRegion k.val+672+16*i+8 by omega]
      simpa using he i hi hip 1 (by decide)
  · obtain ⟨i,hi,ha|ha⟩:=ha
    · subst A;simpa using hp i hi 0 (by decide)
    · subst A;simpa using hp i hi 1 (by decide)
  · obtain ⟨hn,ha|ha⟩:=ha
    · subst A;simpa using h6 hn 0 (by decide)
    · subst A;simpa using h6 hn 1 (by decide)
  · subst A;simpa using ht 0 (by decide)
  · subst A;simpa using ht 1 (by decide)
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
end ClaudeWCT.W9.Machine.Expand.SharedZero

-- V74: old radix-20 SharedValidate (pre-v6) removed; the v6 validate routine is SharedValidateV6 (CanonV6Validate.lean).

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
def expandTierCode : List (BitVec 32) :=
  [0xcfba8b13,0x000b5463,0x00000b13,0x00cb0b13,0x00020e37,0x2d6e3023,
   0x002b0b13,0x2d6e3423,0x037b0b13,0x00066e37,0x036e3423,0xc00fe06f]
def expandTierHeadCode : List (BitVec 32) := expandTierCode.take 2
def expandTierZeroCode : List (BitVec 32) := (expandTierCode.drop 2).take 1
def expandTierBodyCode : List (BitVec 32) := expandTierCode.drop 3
sym_block expandTierHead := symRun {noAlias:=true} expandTierHeadCode (pcOf 47013) 20
sym_block expandTierZero := symRun {noAlias:=true} expandTierZeroCode (pcOf 47015) 20
sym_block expandTierBody := symRun {noAlias:=true} expandTierBodyCode (pcOf 47016) 40
theorem expandTier_headAt {im : Image} (h : CodeAt im (pcOf 47013) expandTierCode) :
    CodeAt im (pcOf 47013) expandTierHeadCode := by
  exact ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.code_slice (off := 0) h (by decide) (by decide)
theorem expandTier_zeroAt {im : Image} (h : CodeAt im (pcOf 47013) expandTierCode) :
    CodeAt im (pcOf 47015) expandTierZeroCode := by
  simpa using ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.code_slice (off := 2) h (by decide) (by decide)
theorem expandTier_bodyAt {im : Image} (h : CodeAt im (pcOf 47013) expandTierCode) :
    CodeAt im (pcOf 47016) expandTierBodyCode := by
  simpa using ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.code_slice (off := 3) h (by decide) (by decide)

theorem expandTier_head_steps {im : Image} (hcode : CodeAt im (pcOf 47013) expandTierHeadCode)
    (s : MachineState) (hp : s.pc = pcOf 47013) (j : Nat) (hj : j ≤ 777)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (if j < 773 then 47015 else 47016) ∧
      t.getReg .x22 = BitVec.ofNat 64 j + BitVec.ofNat 64 (2^64-773) ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound expandTierHead hcode s hp (by simp [expandTierHead.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,expandTierHead.res,E.eval,CmpOp.eval,rv_simp,h21]
    rw [tier_slt_all ⟨j,by omega⟩]
    by_cases h : j < 773 <;> simp [h]
  · simp [expandTierHead.res,rv_simp,h21]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A _ _;rfl

theorem expandTier_zero_steps {im : Image} (hcode : CodeAt im (pcOf 47015) expandTierZeroCode)
    (s : MachineState) (hp : s.pc = pcOf 47015) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 47016 ∧ t.getReg .x22 = 0 ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound expandTierZero hcode s hp (by simp [expandTierZero.res,rv_simp]),
    rfl,by simp [expandTierZero.res,rv_simp],?_,fun _ _ _ => rfl⟩
  intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl

theorem expandTier_body_steps {im : Image} (hcode : CodeAt im (pcOf 47016) expandTierBodyCode)
    (s : MachineState) (hp : s.pc = pcOf 47016) (extra : Nat) (he : extra ≤ 4)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 extra) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf 45232 ∧
      t.getMem (0x202c0#64) = BitVec.ofNat 64 (12+extra) ∧
      t.getMem (0x202c8#64) = BitVec.ofNat 64 (14+extra) ∧
      t.getMem (0x66028#64) = BitVec.ofNat 64 (69+extra) ∧
      RegsExcept s t [.x22,.x28] ∧
      Frame s t (fun A => A=0x202c0 ∨ A=0x202c8 ∨ A=0x66028) := by
  refine ⟨_,symRun_sound expandTierBody hcode s hp
    (by simp [expandTierBody.res,rv_simp,h22,accessValid_iff,MEMORY_BYTES];omega),
    rfl,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_getMem,expandTierBody.res]
    t3n [h22]
    simp [BitVec.ofNat_add_ofNat]
  · simp only [Result.toState_getMem,expandTierBody.res]
    t3n [h22]
    simp [BitVec.ofNat_add_ofNat]
  · simp only [Result.toState_getMem,expandTierBody.res]
    t3n [h22]
    simp [BitVec.ofNat_add_ofNat]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,expandTierBody.res]
    t3n [h22]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    simp only [if_neg (by omega)]
theorem expand_jump {im : Image} (hc : CodeAt im (pcOf 45226) expandCode)
    (s : MachineState) (hp : s.pc=pcOf 45226) :
    Steps im s 1 1 (s.setPC (pcOf 47013)) := by
  exact ClaudeWCT.W9.Machine.Expand.jal_x0_step (imm:=7148) hc (by rfl) (by decide) s hp

theorem expand_steps {im : Image} (hc : CodeAt im (pcOf 45226) expandCode)
    (htier : CodeAt im (pcOf 47013) expandTierCode)
    (s : MachineState) (hp : s.pc=pcOf 45226) (j : Nat) (hj : j ≤ 777)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 j) :
    ∃ t k, Steps im s k k t ∧ k ≤ 13 ∧ t.pc = pcOf 45232 ∧
      t.getMem (0x202c0#64) = BitVec.ofNat 64 (12+(j-773)) ∧
      t.getMem (0x202c8#64) = BitVec.ofNat 64 (14+(j-773)) ∧
      t.getMem (0x66028#64) = BitVec.ofNat 64 (69+(j-773)) ∧
      RegsExcept s t [.x22,.x28] ∧
      Frame s t (fun A => A=0x202c0 ∨ A=0x202c8 ∨ A=0x66028) := by
  let a := s.setPC (pcOf 47013)
  have sa := expand_jump hc s hp
  have ra : RegsExcept s a [] := fun _ _ => rfl
  have fa : Frame s a (fun _ => False) := fun _ _ _ => rfl
  obtain ⟨b,ab,bp,b22,br,bf⟩ := expandTier_head_steps (expandTier_headAt htier) a rfl j hj
    (by simpa [a] using h21)
  by_cases hlow : j < 773
  · have bp' : b.pc = pcOf 47015 := by simpa [hlow] using bp
    obtain ⟨c,bc,cp,c22,cr,cf⟩ := expandTier_zero_steps (expandTier_zeroAt htier) b bp'
    have he : j-773=0 := by omega
    obtain ⟨t,ct,tp,tl,th,tpool,tr,tf⟩ := expandTier_body_steps (expandTier_bodyAt htier) c cp
      (j-773) (by omega) (by simpa [he] using c22)
    refine ⟨t,13,((sa.trans ab).trans bc).trans ct,by decide,tp,tl,th,tpool,?_,?_⟩
    · exact (((ra.trans br).trans cr).trans tr).mono (by simp)
    · exact (((fa.trans bf).trans cf).trans tf).mono (by tauto)
  · have bp' : b.pc = pcOf 47016 := by simpa [hlow] using bp
    have bx22 : b.getReg .x22 = BitVec.ofNat 64 (j-773) := by
      have hslt : BitVec.slt (BitVec.ofNat 64 j + BitVec.ofNat 64 (2^64-773)) (0#64) = false := by
        simpa [hlow] using tier_slt_all ⟨j,by omega⟩
      have he := tier_extra_word j hj
      rw [hslt] at he
      simp only [if_false] at he
      exact b22.trans he
    obtain ⟨t,bt,tp,tl,th,tpool,tr,tf⟩ := expandTier_body_steps (expandTier_bodyAt htier) b bp'
      (j-773) (by omega) bx22
    refine ⟨t,12,(sa.trans ab).trans bt,by decide,tp,tl,th,tpool,?_,?_⟩
    · exact ((ra.trans br).trans tr).mono (by simp)
    · exact ((fa.trans bf).trans tf).mono (by tauto)

end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def rawSlots (k child : Nat) (values : Fin 6→SigGolfCandidate.T3.Digest)
    (path : Nat→SigGolfCandidate.T3.Digest) : List (Nat×SigGolfCandidate.T3.Digest) :=
  ((List.finRange 6).flatMap fun i=>[(V3.chainOffset k i.val+ClaudeWCT.W9.T3M.wctValueOff i.val,values i),
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
        change PreciseCoordinateW k.val child.val (2904+(V3.regionOffset k.val+640)+8*half)
        rw [show V3.regionOffset k.val+640=V3.chainOffset k.val 0+ClaudeWCT.W9.T3M.wctValueOff 0 by
            unfold V3.chainOffset; simp (config := {decide := true}) [ClaudeWCT.W9.T3M.wctChainOff, ClaudeWCT.W9.T3M.wctValueOff],
          show 2904+(V3.chainOffset k.val 0+ClaudeWCT.W9.T3M.wctValueOff 0)=coordRegion k.val+640 by
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
theorem installed_tier : CodeAt Images.expandImage (pcOf 47013) expandTierCode := by
  apply SigGolfCandidate.T3M.codeAt_expand_last <;> decide +kernel
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
/-- img-v6: the expand data starts with the 128-byte Zt table (`ZeroCap.ZT 354`), 128 bytes below `DB`. -/
def DB0 : Nat := 16747280
theorem zt_length : Images.expandZtData.length = 128 := by rfl

theorem getMem {im : Image} (hlen:im.data.length=29936) (hb:dataBase im=DB0)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) (A : Nat) (hA:A<2^64) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=
      if 0x7000≤A ∧ A<0x7000+5200 ∧ (A-0x7000)%8=0 then bytesToWordLE ((bytes b).drop (A-0x7000) |>.take 8)
      else if 0xA0≤A ∧ A<0xB0 ∧ (A-0xA0)%8=0 then bytesToWordLE ((bytes pk).drop (A-0xA0) |>.take 8)
      else if 0x6620≤A ∧ A<0x6640 ∧ (A-0x6620)%8=0 then bytesToWordLE ((bytes m).drop (A-0x6620) |>.take 8)
      else if DB0≤A ∧ A<DB0+29936 ∧ (A-DB0)%8=0 then bytesToWordLE (im.data.drop (A-DB0) |>.take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg,getMem_writeBytesAsWords _ _ 0x7000 A (by rw[bytes_length_e];decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw[bytes_length_e];decide) hA,
    getMem_writeBytesAsWords _ _ 0x6620 A (by rw[bytes_length_e];decide) hA,hb,
    getMem_writeBytesAsWords _ _ DB0 A (by rw[hlen];decide) hA,
    bytes_length_e,bytes_length_e,bytes_length_e,hlen]
  rfl

theorem dataByte {im : Image} (hlen:im.data.length=29936) (hb:dataBase im=DB0)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) (i : Nat) (hi:i<29936) :
    (w9init im m pk b).getByte (BitVec.ofNat 64 (DB0+i))=im.data.getD i 0 := by
  rw [getByte_eq_word _ _ (by unfold DB0;omega),getMem hlen hb _ _ _ _ (by unfold DB0;omega),
    if_neg (by unfold DB0;omega),if_neg (by unfold DB0;omega),if_neg (by unfold DB0;omega),
    if_pos (by unfold DB0;omega),extractByte_bytesToWordLE_e _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_take,List.getElem?_drop,
    if_pos (Nat.mod_lt (DB0+i) (show 0<8 by decide))]
  congr 2
  unfold DB0
  omega

theorem signatureWord {im : Image} (hlen:im.data.length=29936) (hb:dataBase im=DB0)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) (i : Nat) (hi:i<649) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 (0x7000+8*i))=b.extractLsb' (64*i) 64 := by
  rw [getMem hlen hb _ _ _ _ (by omega),if_pos (by omega),
    show 0x7000+8*i-0x7000=8*i by omega]
  exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e b i (by omega)

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

end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (bytes_length_e extractByte_bytesToWordLE_e)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem prefixData {im : Image} (hlen:im.data.length=29936) (hb:dataBase im=DB0)
    (zt pref tail : List (BitVec 8)) (hz:zt.length=128) (hp:pref.length=2160) (hd:im.data=zt++(pref++tail))
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    ∀i,i<2160 → (w9init im m pk b).getByte (BitVec.ofNat 64 (DB+i))=pref.getD i 0 := by
  intro i hi
  rw [show DB+i=DB0+(128+i) by unfold DB DB0;omega,dataByte hlen hb m pk b (128+i) (by omega),hd,
    SigGolfCandidate.T3M.Search.getD_prefixed zt _ 128 i hz]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append,hp,if_pos hi]

theorem msgWord {im : Image} (hlen:im.data.length=29936) (hb:dataBase im=DB0)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) (i : Nat) (hi:i<4) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 (0x6620+8*i))=m.extractLsb' (64*i) 64 := by
  rw [getMem hlen hb _ _ _ _ (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega),
    show 0x6620+8*i-0x6620=8*i by omega]
  exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e m i (by omega)

theorem zero {im : Image} (hlen:im.data.length=29936) (hb:dataBase im=DB0)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) (A : Nat) (hA:A<DB0)
    (hs:A<0x7000 ∨ 0x7000+5248≤A) (hp:A<0xA0 ∨ 0xB0≤A)
    (hm:A<0x6620 ∨ 0x6640≤A) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=0 := by
  rw[getMem hlen hb _ _ _ _ (by unfold DB0 at hA;omega),
    if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- T51: invalid_front (#938's adapter reject path) deleted: DEC rejects a hint >= 7744 itself (PrePass.dec_reject).
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
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem dataBase_of_length {im:Image} (h:im.data.length=29936) : dataBase im=DB0 := by
  unfold dataBase
  rw[h]
  rfl

theorem installed_dataBase : dataBase Images.expandImage=DB0 :=
  dataBase_of_length Images.expandData_length

theorem initial_data (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    DataAt (w9init Images.expandImage m pk b) := by
  exact prefixData Images.expandData_length installed_dataBase Images.expandZtData Images.expandSharedData
    (Images.expandPrefixData++Images.expandLegacyData) SharedInit.zt_length Images.expandSharedData_length
    (by simp only [Images.expandImage, Images.expandData, List.append_assoc]) m pk b

/-- img-v6: the Zt table (`ZeroCap.ZT 354 = DB0`) is the first 128 data bytes. -/
theorem zt_data : ∀ r < 128, Images.expandZtData.getD r 0 = SigGolfCandidate.T3M.Search.ZeroCap.ztByte r := by
  decide +kernel

theorem initial_zt (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    SigGolfCandidate.T3M.Search.ZeroCap.ZtOK 354 (w9init Images.expandImage m pk b) := by
  intro r hr
  rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 + r = DB0 + r by
      unfold SigGolfCandidate.T3M.Search.ZeroCap.ZT DB0; simp,
    dataByte Images.expandData_length installed_dataBase m pk b r (by omega)]
  have hd : Images.expandImage.data = Images.expandZtData ++ (Images.expandSharedData ++ Images.expandPrefixData ++
      Images.expandLegacyData) := rfl
  rw [hd, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [SharedInit.zt_length]; exact hr),
    ← List.getD_eq_getElem?_getD]
  exact zt_data r hr

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
/-- Slot 0 is `rho` (kernel-cheap: through `inflatedRead_internal`, not by unfolding `digC`). -/
theorem InflatedAt.rho {s : MachineState} {b : SharedCodec.CBytes} (h : InflatedAt s b) :
    DigAt s 0x7000 (SharedCodec.sigDecC b).rho := by
  have hr := h 0 (by decide)
  have e : SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) 0 = SharedCodec.digC b 0 := by
    have := SharedCodec.inflatedRead_internal (0 : Digest) (SharedCodec.digC b) 0
    rwa [show SharedCodec.internalFullIndex 0 = 0 from rfl] at this
  rw [e, show 0x7000 + 16 * 0 = 0x7000 from rfl] at hr
  exact hr
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
    (hc : ∀i:Fin 6,wdig w (V3.chainOffset k.val i.val+ClaudeWCT.W9.T3M.wctValueOff i.val)=values i)
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
    (hread : ∀A,W A→W9Machine.OrigWD 1224 (Paired.witEnc output witness) t A)
    (hframe : ∀A,A<2^64→¬W A→t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A))
    (hzero : ∀ (off : Nat), off + 8 ≤ 7664 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (2904+off))=0)
    (off:Nat) (hb:off+8≤7664) (ha:off%8=0) (hc:off≠32∨witness.counters 3=0) (hp:off≠24) :
    W9Machine.OrigWD 1224 (Paired.witEnc output witness) t (2904+off) := by
  -- r3w: the expander's copy of `PairedReadout.original_prefix_of_slots` in the expand FTS frame (2904 = 4128 - 1224).
  by_cases hw:W (2904+off)
  · exact hread _ hw
  have hf:∀p∈Paired.forestSlots output witness.signature,off+8≤p.1∨p.1+16≤off:=by
    intro p hp
    have hal: p.1%8=0:=(PairedReadout.forestSlot_layout output witness.signature p hp).1
    by_contra hn
    have he:off=p.1∨off=p.1+8:=by omega
    rcases he with he|he
    · exact hw (by simpa[he] using hslots p hp 0 (by decide))
    · exact hw (by simpa[he,Nat.add_assoc] using hslots p hp 1 (by decide))
  have hz:(Paired.witEnc output witness).extractLsb' (8*off) 64=0:=by
    change (Paired.witEnc output witness).extractLsb' (8*off) (8*8)=0
    rw [PairedReadout.witEnc_extract output witness _ _ (Or.inl (by unfold choiceOff; omega))]
    change (PairedReadout.prefixEnc (PairedReadout.countedPrefix (witness.counters 3)
      (PairedReadout.readSlot (Paired.forestSlots output witness.signature))) output
      (Paired.mainWitness witness)).extractLsb' _ (8*8)=0
    refine PairedReadout.extract_prefixEnc_free _ _ _ _ _ _ hb ?_ (by omega) hf
    rcases hc with hc|hc
    · omega
    · exact Or.inr (Or.inr hc)
  unfold W9Machine.OrigWD
  rw[hframe _ (by omega) hw,hzero off hb ha,show 2904+off+1224-0x1020=off by omega,hz]

theorem ScatterInv.original_prefix (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s t : MachineState)
    (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hi : ScatterInv s (SharedForest.rawChildFromOutput output) 9 t)
    (hz : ∀ (off : Nat), off + 8 ≤ 8096 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (2904+off))=0)
    (off : Nat) (hb : off+8≤7664) (ha : off%8=0) (hc : off≠32∨witness.counters 3=0) (hp : off≠24) :
    W9Machine.OrigWD 1224 (Paired.witEnc output witness) t (2904+off) := by
  let writes := fun A => ∃k:Fin 9,k.val<9 ∧
    PreciseCoordinateW k.val (coordPhysical k.val (SharedForest.rawChildFromOutput output k).val) A
  apply prefix_of_slots_c3 output witness s t writes _ _ _ (fun o h1 h2 => hz o (by omega) h2) off hb ha hc hp
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
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- T51: the #938 5,248-byte readout lemmas (serializedWord_congr, hints_word, inflatedAt_of_words) are gone:
-- DEC (Expand_PrePassInit) writes the inflated slot layout directly.
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
    (htop : ∀ j, (witness.signature.layers 0).path j = 0) (off : Nat) (h1 : 7664 ≤ off) (h2 : off + 8 ≤ 8336) :
    (ClaudeWCT.W9.T3M.Paired.witEnc output witness).extractLsb' (8*off) 64 = 0 := by
  rw [ClaudeWCT.W9.T3M.Paired.word_witEnc_tail output witness off h1
    (Or.inl (by simp only [ClaudeWCT.W9.T3M.choiceOff]; omega))]
  unfold ClaudeWCT.W9.T3M.witEnc
  rw [show (64:Nat) = 8*8 from rfl, extract_readLE_lt _ 22012 (witList_readLE_lt _ _) off 8]
  have hw : ((ClaudeWCT.W9.T3M.witList output (ClaudeWCT.W9.T3M.Paired.mainWitness witness)).drop off).take 8 = zeros 8 := by
    have := win_topPath output (ClaudeWCT.W9.T3M.Paired.mainWitness witness) (off - 7664) 8 (by omega)
    rw [show ClaudeWCT.W9.T3M.layerBase 0 + (off-7664) = off by simp [ClaudeWCT.W9.T3M.layerBase]; omega] at this
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
      generalize off - 7664 + i - _ = n
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    · rfl
  rw [hw]; rfl
end topzero

/-- img-v6 (r3w FTS geometry, regions 848 bytes): no scatter write reaches the last 48 bytes of coordinate
region 0 ([10568, 10616): the witness top area just above the FTS block). -/
theorem preciseCoordinateW_tail (k : Fin 9) (child : Fin 128) (A : Nat)
    (h : PreciseCoordinateW k.val child.val A) : A + 8 ≤ 10568 := by
  have hr : coordRegion k.val ≤ 9768 := by unfold coordRegion; omega
  rcases h with (h|⟨hf,h⟩)|h|h
  · rcases h with h|h
    · obtain ⟨i,hi,h⟩:=h
      rcases h with h|h|⟨_,h|h⟩ <;> (interval_cases i <;> omega)
    · obtain ⟨i,hi,h⟩:=h
      have hb:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
      change coordRegion k.val ≤ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧
        pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16 ≤ coordRegion k.val+320 at hb
      omega
  · have hk : k.val ≠ 0 := by intro h0; apply hf; unfold firstCoord; omega
    have : coordRegion k.val ≤ 8920 := by unfold coordRegion; omega
    have hc := Nat.mod_lt (child.val/32) (by decide : 0<2)
    unfold SixthW destination at h
    omega
  · have hb:=topDest_bound k child; omega
  · have hb:=topDest_bound k child; omega

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
    by_cases hlo : A-2904+8 ≤ 7664
    swap
    · unfold W9Machine.OrigWD
      have hex : Frame s u (fun A=>∃k:Fin 9,k.val<9 ∧
          PreciseCoordinateW k.val (coordPhysical k.val (SharedForest.rawChildFromOutput output k).val) A) :=
        (ht.exactFrame.trans uf).mono (by intro A hA h;rcases h with h|h;exact h;exact h.elim)
      rw [show A + 1224 - 0x1020 = A - 2904 by omega, topArea_zero_word output witness htop _ (by omega) (by omega),
        hex.get (by omega) (by
          rintro ⟨k,_,hk⟩
          have := preciseCoordinateW_tail k ⟨_, coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩ A hk
          omega), show A = 2904 + (A - 2904) by omega]
      exact hz _ (by omega) (by omega)
    have ho:A-2904+8≤7664:=hlo
    have he:2904+(A-2904)=A:=by omega
    have hw:=ScatterInv.original_prefix output witness b s t hin hforest ht
      (fun off h1 h2 => hz off (by omega) h2) (A-2904) ho
      (by omega) (Or.inr hc3) (by omega)
    rw[he] at hw
    unfold W9Machine.OrigWD at hw ⊢
    rw[uf.get (by omega) (fun h=>h)]
    exact hw
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

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
    (off : Nat) (hb : off+8≤7664) (ha : off%8=0) (hc : off≠32∨witness.counters 3=0) (hp : off≠24) :
    W9Machine.OrigWD 1224 (Paired.witEnc output witness) t (2904+off) := by
  let writes := fun A => ∃k:Fin 9,k.val<9 ∧
    PreciseCoordinateW k.val (coordPhysical k.val (SharedForest.rawChildFromOutput output k).val) A
  apply prefix_of_slots_c3 output witness s t writes _ _ _ (fun o h1 h2 => hz o (by omega) h2) off hb ha hc hp
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

/-- T51: the front after DEC (word 0 -> DEC 54569 -> `j 1`): from word 1 with the inflated slot layout and the hint
already written (`Expand_PrePassInit.dec_init`), the front tail + zero block + `j 45056` (37 steps). `s0` is the real
initial state; DEC wrote only the hint word and `[0x70d0, 0x84c0)`. -/
theorem prepare {im:Image}
    (hf:CodeAt im (pcOf 1) frontTail)
    (hz:CodeAt im (pcOf 42719) zeroBlk) (hj:CodeAt im (pcOf 30) [0x7892b06f])
    (s0 s:MachineState) (message:SigGolfCandidate.T3.Message) (b:SharedCodec.CBytes)
    (hp:s.pc=pcOf 1) (h5:s.getReg .x5=0)
    (hin:SharedCompact.InflatedAt s b)
    (hh:s.getMem (BitVec.ofNat 64 SharedCompact.policyAddress)=
      BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hm:∀k,k < 4 → s.getMem (BitVec.ofNat 64 (0x6620+8*k))=message.extractLsb' (64*k) 64)
    (hd:SharedInit.DataAt s)
    (hf0:Frame s0 s (fun A=>A=SharedCompact.policyAddress ∨ (0x70d0≤A ∧ A<0x84c0))) :
    ∃t,Steps im s 37 37 t ∧ Prepared s0 message b t := by
  obtain ⟨t,ut,tp,t5,t0,t8,tm,tz,tr,tf⟩:=setup hf hz hj s hp h5
  refine ⟨t,ut,⟨tp,t5,?_,?_,?_,?_,?_,?_,tz⟩⟩
  · have hr:=hin.rho
    exact ⟨(t0 DIG (Or.inr rfl)).trans hr.1,(t8 (DIG+8) (Or.inr rfl)).trans hr.2⟩
  · intro k hk
    exact (tm k hk).trans (hm k hk)
  · exact hin.frame tf (by intro A hA hB hw;unfold Writes at hw;simp only [DIG] at hw;omega)
  · exact (tf.get (by unfold SharedCompact.policyAddress;omega) (by unfold Writes SharedCompact.policyAddress DIG;omega)).trans hh
  · intro i hi
    have x:=hd i hi
    have hm : t.getByte (BitVec.ofNat 64 (SharedInit.DB+i))=s.getByte (BitVec.ofNat 64 (SharedInit.DB+i)) :=
      tf.getByte (by unfold SharedInit.DB;omega) (by unfold Writes SharedInit.DB DIG;omega)
    exact hm.trans x
  · exact (hf0.trans tf).mono (by
      intro A hA h
      rcases h with (h|h)|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))

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
      c.toNat < 2^21 ∧ SigGolfCandidate.Research.SharedForest.digestAccepted a=true ∧ OutAt s SigGolfCandidate.T3M.Search.NBUF a ∧
      s.getReg .x21=BitVec.ofNat 64 (SigGolfCandidate.Research.SharedForest.jointAccountingCost a)

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
      | some p =>
        refine ⟨ht.result.1,ht.result.2.1,ht.result.2.2.1,ht.result.2.2.2.1,ht.result.2.2.2.2,?_⟩
        simpa only [SharedDigest.sumReg,ite_true] using ht.resultCost
    · cases r <;> exact ht.resultR17)
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem legacyByte {im : Image} (hlen : im.data.length = 29936)
    (pre : List (BitVec 8)) (hp : pre.length = 25840)
    (hd : im.data = pre ++ Images.expandLegacyData)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) (i : Nat) (hi : i < 4096) :
    (w9init im m pk b).getByte (BitVec.ofNat 64 (TOP_DATA + i)) = Images.expandLegacyData.getD i 0 := by
  rw [show TOP_DATA + i = DB0 + (25840+i) by unfold TOP_DATA DB0; omega,
    dataByte hlen (dataBase_of_length hlen) m pk b _ (by omega), hd]
  exact getD_prefixed pre Images.expandLegacyData 25840 i hp

theorem initial_tables_of_data {im : Image} (hlen : im.data.length = 29936)
    (pre : List (BitVec 8)) (hp : pre.length = 25840)
    (hd : im.data = pre ++ Images.expandLegacyData)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
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

theorem initial_tables (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    TableOK (w9init Images.expandImage m pk b) ∧ CfTableOK 0 (w9init Images.expandImage m pk b) ∧
      Reward.RewardTablesOK (w9init Images.expandImage m pk b) := by
  exact initial_tables_of_data Images.expandData_length
    (Images.expandZtData ++ (Images.expandSharedData ++ Images.expandPrefixData))
    (by simp only [List.length_append, SharedInit.zt_length, Images.expandSharedData_length,
      Images.expandPrefixData_length])
    (by simp only [Images.expandImage, Images.expandData, List.append_assoc]) m pk b
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Layer Digest chainCount height)
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- T51: the expander's slots of layer `lay` (#938's lower-layer slots kept; the top path follows the 51 values):
digest `layIdx lay + i` sits at slot `internalFullIndex (layIdx lay) + i`, and the forest code's move by 19 slots puts
slot 118 at `lP 0 = 30864`. -/
theorem lP_shared (lay : Layer) :
    SigGolfCandidate.T3M.Expand.lP lay=30864+16*(SharedCodec.internalFullIndex (SharedCodec.layIdx lay)-118) ∧
    118 ≤ SharedCodec.internalFullIndex (SharedCodec.layIdx lay) ∧
    SharedCodec.internalFullIndex (SharedCodec.layIdx lay)+chainCount lay+height lay ≤ 332 ∧
    ∀ i, i<chainCount lay+height lay →
      SharedCodec.internalFullIndex (SharedCodec.layIdx lay+i)=SharedCodec.internalFullIndex (SharedCodec.layIdx lay)+i := by
  fin_cases lay <;> refine ⟨rfl,by decide,by decide,?_⟩ <;> intro i hi <;>
    simp only [chainCount,height,SharedCodec.layIdx,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.cons_val] at hi ⊢ <;>
    unfold SharedCodec.internalFullIndex <;> split_ifs <;> omega

theorem inflated_main (b : SharedCodec.CBytes) (lay : Layer) (i : Nat) (hi : i<chainCount lay+height lay) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) (SharedCodec.internalFullIndex (SharedCodec.layIdx lay)+i)=
      SharedCodec.digC b (SharedCodec.layIdx lay+i) := by
  rw [← (lP_shared lay).2.2.2 i hi]
  exact SharedCodec.inflatedRead_internal _ _ _

theorem main_readout {b : SharedCodec.CBytes} {s t : MachineState}
    (hsource : SharedCompact.InflatedAt s b)
    (hmove : ∀i<428,t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i))) :
    SigGolfCandidate.T3M.Expand.BC.SigLayersAt t (SharedForest.mainSignature (SharedCodec.sigDecC b)) := by
  have hrows : ∀i<214,DigAt t (30864+16*i) (SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) (118+i)) := by
    intro i hi
    have h:=hsource (118+i) (by omega)
    have ha:0x7000+16*(118+i)=30560+16*i:=by omega
    rw [ha] at h
    refine ⟨?_,?_⟩
    · have hm:=hmove (2*i) (by omega)
      rw [show 30864+8*(2*i)=30864+16*i by omega,show 30560+8*(2*i)=30560+16*i by omega] at hm
      exact hm.trans h.1
    · have hm:=hmove (2*i+1) (by omega)
      rw [show 30864+8*(2*i+1)=30864+16*i+8 by omega,show 30560+8*(2*i+1)=30560+16*i+8 by omega] at hm
      exact hm.trans h.2
  intro lay
  obtain ⟨hp,hl,hh,_⟩:=lP_shared lay
  constructor
  · intro i hi
    have h:=hrows (SharedCodec.internalFullIndex (SharedCodec.layIdx lay)-118+i) (by omega)
    rw [show 118+(SharedCodec.internalFullIndex (SharedCodec.layIdx lay)-118+i)=
        SharedCodec.internalFullIndex (SharedCodec.layIdx lay)+i by omega, inflated_main b lay i (by omega),
      show 30864+16*(SharedCodec.internalFullIndex (SharedCodec.layIdx lay)-118+i)=
        SigGolfCandidate.T3M.Expand.lP lay+16*i by rw[hp];omega] at h
    exact h
  · intro j hj
    have h:=hrows (SharedCodec.internalFullIndex (SharedCodec.layIdx lay)-118+chainCount lay+j) (by omega)
    rw [show 118+(SharedCodec.internalFullIndex (SharedCodec.layIdx lay)-118+chainCount lay+j)=
        SharedCodec.internalFullIndex (SharedCodec.layIdx lay)+(chainCount lay+j) by omega,
      inflated_main b lay (chainCount lay+j) (by omega),
      show 30864+16*(SharedCodec.internalFullIndex (SharedCodec.layIdx lay)-118+chainCount lay+j)=
        SigGolfCandidate.T3M.Expand.lP lay+16*chainCount lay+16*j by rw[hp];omega,
      show SharedCodec.layIdx lay+(chainCount lay+j)=SharedCodec.layIdx lay+chainCount lay+j by omega] at h
    exact h
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
    (hhint : (SharedCodec.sigDecC b).policyHints.toNat<7744)
    (hhmem : s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hzt : SigGolfCandidate.T3M.Search.ZeroCap.ZtOK 354 s)
    (ht51 : SigGolfCandidate.T3M.Search.T51.T51TableW 0xFF9E00 s) :
    SigGolfCandidate.T3M.Expand.SharedLayers.LInv (SharedForest.mainSignature (SharedCodec.sigDecC b))
      (SharedCodec.sigDecC b).policyHints index 4 (.pair pair.1 pair.2) t := by
  have keep (A : Nat) (ha : A<2^64) (hw : ¬Writes A) := hf.get ha hw
  refine ⟨⟨hp,by decide,h5,hi,?_,?_,?_,?_,?_,main_readout hin hmove,?_,?_,?_,?_⟩,by omega,?_,?_,?_⟩
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
  · exact hzt.frame hf (by
      intro r hr hw
      rw [show SigGolfCandidate.T3M.Search.ZeroCap.ZT 354 = 16747280 from rfl] at hw
      unfold Writes at hw
      omega)
  · exact ht51.frame hf (by decide) (by decide) (fun k hk => by unfold Writes; omega)
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem shifted_data_mem {im ref : Image} (hlen : im.data.length=29936)
    (pre : List (BitVec 8)) (hp : pre.length=2288) (hd : im.data=pre++ref.data)
    (href : ExpandDataOK ref) (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes)
    (A : Nat) (hlo : Compact2.LPLAN≤A) (hhi : A<Compact2.LPLAN+27648) (hal : A%8=0) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=
      (w9init ref m pk (0 : Bytes 5312)).getMem (BitVec.ofNat 64 A) := by
  rw [getMem hlen (dataBase_of_length hlen) m pk b A (by unfold Compact2.LPLAN at *;omega),
    if_neg (by unfold Compact2.LPLAN at *;omega),if_neg (by unfold Compact2.LPLAN at *;omega),
    if_neg (by unfold Compact2.LPLAN at *;omega),if_pos (by unfold Compact2.LPLAN DB0 at *;omega),
    w9init_data href m pk (0 : Bytes 5312) A hlo hhi (by unfold Compact2.LPLAN;omega),hd]
  rw [show A-DB0=2288+(A-Compact2.LPLAN) by unfold DB0 Compact2.LPLAN at *;omega,
    ←List.drop_drop,List.drop_left' hp]

theorem initial_plans_of_data {im ref : Image} (hlen : im.data.length=29936)
    (pre : List (BitVec 8)) (hp : pre.length=2288) (hd : im.data=pre++ref.data)
    (href : ExpandDataOK ref) (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
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

theorem initial_plans (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    ClaudeWCT.W9.Machine.Expand.PlanAt (w9init Images.expandImage m pk b) ∧
      Compact2.LPlanAt (w9init Images.expandImage m pk b) := by
  exact initial_plans_of_data (ref:=⟨[],Images.expandPrefixData++Images.expandLegacyData⟩)
    Images.expandData_length (Images.expandZtData++Images.expandSharedData)
    (by simp only [List.length_append, SharedInit.zt_length, Images.expandSharedData_length])
    (by simp only [Images.expandImage, Images.expandData, List.append_assoc])
    reference_data_ok m pk b
theorem initial_toptab (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    Compact2.TopTabAt (w9init Images.expandImage m pk b) := by
  have he (A : Nat) (hl : Compact2.LPLAN ≤ A) (hh : A < Compact2.LPLAN+27648) (hm : A % 8 = 0) :=
    shifted_data_mem (im:=Images.expandImage) (ref:=⟨[],Images.expandPrefixData++Images.expandLegacyData⟩)
      Images.expandData_length (Images.expandZtData++Images.expandSharedData)
      (by simp only [List.length_append, SharedInit.zt_length, Images.expandSharedData_length])
      (by simp only [Images.expandImage, Images.expandData, List.append_assoc])
      reference_data_ok m pk b A hl hh hm
  constructor
  · intro k hk
    rw [he _ (by unfold Compact2.TOPA Compact2.LPLAN;omega) (by unfold Compact2.TOPA Compact2.LPLAN;omega) (by unfold Compact2.TOPA;omega)]
    exact (w9init_toptab reference_data_ok m pk (0 : Bytes 5312)).1 k hk
  · intro k hk
    rw [he _ (by unfold Compact2.TOPB Compact2.LPLAN;omega) (by unfold Compact2.TOPB Compact2.LPLAN;omega) (by unfold Compact2.TOPB;omega)]
    exact (w9init_toptab reference_data_ok m pk (0 : Bytes 5312)).2 k hk
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open ClaudeWCT.W9.T3M SigGolfCandidate.Research

/-- img-v6: the 5,248-byte image is only used on `b48 = sigBC48 (sigDecC b)`, whose top field is < 2^109
(`fill_sigDecC`); the projection is a hypothesis here. -/
theorem main_projection (b : SharedCodec.CBytes)
    (hfill : SharedForest.fillTopSignature (SharedCodec.sigDecC b) 0 = SharedCodec.sigDecC b) :
    ClaudeWCT.WCT9.fillTop (SharedForest.mainSignature (SharedCodec.sigDecC b)) 0 =
      SharedForest.mainSignature (SharedCodec.sigDecC b) := by
  exact congrArg SharedForest.mainSignature hfill

end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (ENC NODE)
open SigGolfCandidate.T3M.Expand (CHAIN)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem public_key_of_length {im : Image} (hlen : im.data.length=29936)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    DigAt (w9init im m pk b) 0xA0 pk := by
  have hword (i : Nat) (hi : i<2) :
      (w9init im m pk b).getMem (BitVec.ofNat 64 (0xA0+8*i))=pk.extractLsb' (64*i) 64 := by
    rw [getMem hlen (dataBase_of_length hlen) m pk b _ (by omega),
      if_neg (by omega),if_pos (by omega),show 0xA0+8*i-0xA0=8*i by omega]
    exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e pk i (by omega)
  exact ⟨hword 0 (by decide),hword 1 (by decide)⟩

theorem region_zero_of_length {im : Image} (hlen : im.data.length=29936)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    ∀A,0x2c48≤A → A<0x61c8 → (w9init im m pk b).getMem (BitVec.ofNat 64 A)=0 := by
  intro A hlo hhi
  exact zero hlen (dataBase_of_length hlen) m pk b A
    (by unfold DB0;omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))

theorem layer_zero_of_length {im : Image} (hlen : im.data.length=29936)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    SigGolfCandidate.T3M.Expand.BC.LZero (w9init im m pk b) := by
  constructor <;> apply zero hlen (dataBase_of_length hlen) m pk b <;>
    simp only [CHAIN,NODE,ENC,DB0] <;> omega

theorem counter_of_length {im : Image} (hlen : im.data.length=29936)
    (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    ∃x<2^32,(w9init im m pk b).getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x := by
  refine ⟨0,by decide,?_⟩
  apply zero hlen (dataBase_of_length hlen) m pk b <;> simp only [ENC,DB0] <;> omega

theorem initial_thresholds (m : Message) (pk : PublicKey) (b : ClaudeWCT.W9.T3M.SharedCodec.CBytes) :
    (∀r,r<56 → (w9init Images.expandImage m pk b).getByte (BitVec.ofNat 64 (16749456+r))=
      BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 1 r)) ∧
    (∀r,r<41 → (w9init Images.expandImage m pk b).getByte (BitVec.ofNat 64 (16749520+r))=
      BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 2 r)) := by
  have h : SharedValidate.Tables (w9init Images.expandImage m pk b) := initial_data m pk b
  exact ⟨h.first,h.second⟩

end ClaudeWCT.W9.Machine.Expand.SharedInit
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_H2Search ====
section

/-! # H2 expander: the candidate search after the layers (words 342, 42795..42840)

At word 342 the old expander compared the root with the public key. Word 342 now jumps to 42795: candidate 0 is
that comparison; on a mismatch the code finds the top sibling's high word in the last hashed block (offset 8 or
56 by the top leaf's bit 11 = index bit 30), and for `c = 1, 2, ...` adds `2^48` to it, stores it, hashes the
block and compares the 16-byte answer with the key. On a match it stores the word at the sibling's witness slot
(0x2c48 + 8 or + 56) and goes to the success halt (351); after 524,287 candidates it goes to the failure halt
(354). -/

section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (ex_valid ex_ne ex_beq tb_shortHash_bind')
open SigGolfCandidate.T3 (Digest HashOutput M Layer height route header zero16 pad64 shortHash)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

def srchCode : List (BitVec 32) :=
  [134711, 638455315, 167775891, 964227, 9352963, 930563, 13834339, 9319171, 14881891, 2329763951, 134711,
    1426984467, 930563, 31675155, 1274643, 8389523, 201827, 58721171, 134711, 537792019, 8261171, 16311,
    3297742739, 8359859, 930691, 1050515, 0x03079793, 132407, 537199891, 67110291, 132663, 604374547, 1052435, 0x000108b7,
    15958963, 8269859, 115, 406275, 13833827, 8794883, 14878819, 2035475, 4280246499, 2199740527, 8368163,
    2178769007]
def srS1 : List (BitVec 32) := srchCode.take 7
def srS2 : List (BitVec 32) := (srchCode.drop 7).take 2
def srM1 : List (BitVec 32) := (srchCode.drop 10).take 7
def srM2 : List (BitVec 32) := (srchCode.drop 17).take 1
def srSD : List (BitVec 32) := (srchCode.drop 18).take 16
def srL1 : List (BitVec 32) := (srchCode.drop 34).take 2
def srL2 : List (BitVec 32) := (srchCode.drop 37).take 2
def srL3 : List (BitVec 32) := (srchCode.drop 39).take 2
def srL4 : List (BitVec 32) := (srchCode.drop 41).take 2
def srF1 : List (BitVec 32) := (srchCode.drop 44).take 1
/-- The H2 core can be entered after a separate policy-validation prefix. -/
def SrchCoreAt (im : Image) : Prop := CodeAt im (pcOf 42795) srchCode

section code
variable {im : Image} (hS : SrchCoreAt im)
include hS
theorem codeAt_srch (k n : Nat) (hk : k + n ≤ 46) :
    CodeAt im (pcOf (42795 + k)) ((srchCode.drop k).take n) := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  have e1 : (pcOf 42795).toNat = 0x1000 + 4 * 42795 := by rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e2 : (pcOf (42795 + k)).toNat = 0x1000 + 4 * (42795 + k) := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hl : srchCode.length = 46 := rfl
  refine ⟨by omega, by omega, by simp only [List.length_take, List.length_drop, hl]; omega, ?_⟩
  rw [e2, show (0x1000 + 4 * (42795 + k) - 0x1000) / 4 = (0x1000 + 4 * 42795 - 0x1000) / 4 + k by omega,
    ← List.drop_drop]
  rw [e1] at h4
  obtain ⟨t, ht⟩ := h4
  refine ⟨((srchCode.drop k).drop n) ++ t, ?_⟩
  rw [← ht, List.drop_append_of_le_length (by rw [hl]; omega), ← List.append_assoc, List.take_append_drop]
end code

sym_block h2_S1 := symRun { noAlias := true } srS1 (pcOf 42795) 50
sym_block h2_S2 := symRun { noAlias := true } srS2 (pcOf 42802) 50
sym_block h2_M1 := symRun { noAlias := true } srM1 (pcOf 42805) 50
sym_block h2_M2 := symRun { noAlias := true } srM2 (pcOf 42812) 50
sym_block h2_SD := symRun { noAlias := true } srSD (pcOf 42813) 50
sym_block h2_L1 := symRun { noAlias := true } srL1 (pcOf 42829) 50
sym_block h2_L2 := symRun { noAlias := true } srL2 (pcOf 42832) 50
sym_block h2_L3 := symRun { noAlias := true } srL3 (pcOf 42834) 50
sym_block h2_L4 := symRun { noAlias := true } srL4 (pcOf 42836) 50
sym_block h2_F1 := symRun { noAlias := true } srF1 (pcOf 42839) 50

section specs
variable {im : Image} (hS : SrchCoreAt im) (s : MachineState)
include hS

theorem jal_at (n m : Nat) (hn : 42795 ≤ n) (hn' : n < 42795 + 46) (w : BitVec 32)
    (hw : (srchCode.drop (n - 42795)).take 1 = [w]) (hj : jalTo w n = some m) (hpc : s.pc = pcOf n) :
    Steps im s 1 1 (s.setPC (pcOf m)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound hj
  have hc := codeAt_srch hS (n - 42795) 1 (by omega)
  rw [hw, show 42795 + (n - 42795) = n by omega] at hc
  exact jal_x0_step hc hd hoff s hpc

theorem s1_spec (hpc : s.pc = pcOf 42795) :
    ∃ t, Steps im s 7 7 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 0xA0) then pcOf 42802 else pcOf 42805) ∧
      t.getReg .x28 = BitVec.ofNat 64 ENC ∧ t.getReg .x13 = s.getMem (BitVec.ofNat 64 0xA0) ∧
      t.getReg .x14 = s.getMem (BitVec.ofNat 64 0xA8) ∧
      RegsExcept s t [.x6, .x13, .x14, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_S1 (codeAt_srch hS 0 7 (by decide)) s hpc
    (by simp [h2_S1.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_S1.res, E.eval, CmpOp.eval, rebase, rv_simp, ENC]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp [h2_S1.res, rv_simp]
  · simp [h2_S1.res, rv_simp]
  · simp [h2_S1.res, rv_simp]
  · ex_regs h2_S1.res
  · intro A _ _; simp [h2_S1.res, rv_simp]

theorem s2_spec (hpc : s.pc = pcOf 42802) (h28 : s.getReg .x28 = BitVec.ofNat 64 ENC) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getReg .x14 then pcOf 42804 else pcOf 42805) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_S2 (codeAt_srch hS 7 2 (by decide)) s hpc
    (by simp [h2_S2.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, ENC]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_S2.res, E.eval, CmpOp.eval, rebase, rv_simp, ENC, h28]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs h2_S2.res
  · intro A _ _; simp [h2_S2.res, rv_simp]

theorem m1_spec (hpc : s.pc = pcOf 42805) :
    ∃ t, Steps im s 7 7 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 0x20550)) >>> 30 &&& 1 = 0 then pcOf 42812 else pcOf 42813) ∧
      t.getReg .x7 = BitVec.ofNat 64 8 ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_M1 (codeAt_srch hS 10 7 (by decide)) s hpc
    (by simp [h2_M1.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_M1.res, E.eval, CmpOp.eval, BinOp.eval, rebase, rv_simp]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp [h2_M1.res, rv_simp]
  · ex_regs h2_M1.res
  · intro A _ _; simp [h2_M1.res, rv_simp]

theorem m2_spec (hpc : s.pc = pcOf 42812) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42813 ∧ t.getReg .x7 = BitVec.ofNat 64 56 ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_M2 (codeAt_srch hS 17 1 (by decide)) s hpc
    (by simp [h2_M2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, h2_M2.res, E.eval]
  · simp [h2_M2.res, rv_simp]
  · ex_regs h2_M2.res
  · intro A _ _; simp [h2_M2.res, rv_simp]

theorem sd_spec (hpc : s.pc = pcOf 42813) (off : Nat) (hoff : off = 8 ∨ off = 56)
    (h7 : s.getReg .x7 = BitVec.ofNat 64 off) :
    ∃ t, Steps im s 16 16 t ∧ t.pc = pcOf 42829 ∧
      t.getReg .x28 = BitVec.ofNat 64 (NODE + off) ∧ t.getReg .x31 = BitVec.ofNat 64 (0x2c48 + off) ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 (NODE + off)) ∧
      t.getReg .x15 = BitVec.ofNat 64 (2 ^ 48) ∧ t.getReg .x10 = BitVec.ofNat 64 NODE ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getReg .x30 = BitVec.ofNat 64 1 ∧ t.getReg .x17 = BitVec.ofNat 64 65536 ∧
      RegsExcept s t [.x7, .x10, .x11, .x12, .x15, .x17, .x28, .x30, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_SD (codeAt_srch hS 18 16 (by decide)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [h2_SD.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h7, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    t3n [h7]
    all_goals first | omega | skip
  · simp [Result.toState_pc, h2_SD.res, E.eval]
  · simp only [Result.toState_getReg, h2_SD.res]; t3n [h7]
    all_goals (try simp only [NODE]); all_goals (try rw [Nat.add_comm])
  · simp only [Result.toState_getReg, h2_SD.res]; t3n [h7]
    all_goals (try simp only [NODE]); all_goals (try rw [Nat.add_comm])
  · simp only [Result.toState_getReg, h2_SD.res]; t3n [h7]
    all_goals (try simp only [NODE]); all_goals (try rw [Nat.add_comm])
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · simp only [Result.toState_getReg, h2_SD.res]; t3n []
  · ex_regs h2_SD.res
  · intro A _ _; simp [h2_SD.res, rv_simp]

theorem l1_spec (hpc : s.pc = pcOf 42829) (B W D : Nat) (hB : B % 8 = 0) (hB' : B + 8 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 B) (h7 : s.getReg .x7 = BitVec.ofNat 64 W)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 D) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 42831 ∧ t.getReg .x7 = BitVec.ofNat 64 (W + D) ∧
      t.getMem (BitVec.ofNat 64 B) = BitVec.ofNat 64 (W + D) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun A => A = B) := by
  refine ⟨_, symRun_sound h2_L1 (codeAt_srch hS 34 2 (by decide)) s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [h2_L1.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h28, h7, h15, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    t3n [h28, h7, h15]
    all_goals first | omega | skip
  · simp [Result.toState_pc, h2_L1.res, E.eval]
  · simp only [Result.toState_getReg, h2_L1.res]; t3n [h7, h15]
  · simp only [Result.toState_getMem, h2_L1.res]; t3n [h28, h7, h15]; simp
  · ex_regs h2_L1.res
  · intro A hA hn
    simp only [Result.toState_getMem, h2_L1.res]
    t3n [h28]
    rw [if_neg (by omega)]

theorem l2_spec (hpc : s.pc = pcOf 42832) (h12 : s.getReg .x12 = BitVec.ofNat 64 NOUT) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 NOUT) = s.getReg .x13 then pcOf 42834 else pcOf 42836) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_L2 (codeAt_srch hS 37 2 (by decide)) s hpc
    (by simp [h2_L2.res, rv_simp, accessValid_iff, MEMORY_BYTES, h12, NOUT]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_L2.res, E.eval, CmpOp.eval, rebase, rv_simp, NOUT, h12]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs h2_L2.res
  · intro A _ _; simp [h2_L2.res, rv_simp]

theorem l3_spec (hpc : s.pc = pcOf 42834) (h12 : s.getReg .x12 = BitVec.ofNat 64 NOUT) :
    ∃ t, Steps im s 2 2 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (NOUT + 8)) = s.getReg .x14 then pcOf 42839 else pcOf 42836) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_L3 (codeAt_srch hS 39 2 (by decide)) s hpc
    (by simp [h2_L3.res, rv_simp, accessValid_iff, MEMORY_BYTES, h12, NOUT]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_L3.res, E.eval, CmpOp.eval, rebase, rv_simp, NOUT, h12]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs h2_L3.res
  · intro A _ _; simp [h2_L3.res, rv_simp]

theorem l4_spec (hpc : s.pc = pcOf 42836) (c : Nat) (hc : c < 65536)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 c) (h17 : s.getReg .x17 = BitVec.ofNat 64 65536) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if c + 1 < 65536 then pcOf 42829 else pcOf 42838) ∧
      t.getReg .x30 = BitVec.ofNat 64 (c + 1) ∧ RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_L4 (codeAt_srch hS 41 2 (by decide)) s hpc (by simp [h2_L4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h2_L4.res, E.eval, CmpOp.eval, BinOp.eval, rebase, rv_simp, h30, h17,
      ofNat_add_ofNat]
    have e : BitVec.ult (BitVec.ofNat 64 (c + 1)) (BitVec.ofNat 64 65536) = decide (c + 1 < 65536) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp only [Result.toState_getReg, h2_L4.res]; t3n [h30]
  · ex_regs h2_L4.res
  · intro A _ _; simp [h2_L4.res, rv_simp]

theorem f1_spec (hpc : s.pc = pcOf 42839) (WW : Nat) (hW : WW % 8 = 0) (hW' : WW + 8 ≤ 2 ^ 24)
    (h31 : s.getReg .x31 = BitVec.ofNat 64 WW) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42840 ∧ t.getMem (BitVec.ofNat 64 WW) = s.getReg .x7 ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A = WW) := by
  refine ⟨_, symRun_sound h2_F1 (codeAt_srch hS 44 1 (by decide)) s hpc ?_, ?_, ?_, ?_, ?_⟩
  · simp only [h2_F1.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h31, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    t3n [h31]
    all_goals first | omega | skip
  · simp [Result.toState_pc, h2_F1.res, E.eval]
  · simp only [Result.toState_getMem, h2_F1.res]; t3n [h31]; simp
  · ex_regs h2_F1.res
  · intro A hA hn
    simp only [Result.toState_getMem, h2_F1.res]
    t3n [h31]
    rw [if_neg (by omega)]
end specs


/-! ### The searched block and the candidate words -/

def topHdr (index : Nat) : BitVec 128 :=
  SigGolfCandidate.T3.nodeTweak 3 (0 : Layer).val (route index 0).2
    (2 ^ (height 0 - WCT9.topJ.val - 1) + (route index 0).1 / 2 ^ (WCT9.topJ.val + 1))
/-- The input of the top layer's last node hash with sibling `o`. -/
def topIn (index : Nat) (v o : Digest) : List UInt8 :=
  let pair := if (route index 0).1 / 2 ^ WCT9.topJ.val % 2 = 0 then (v, o) else (o, v)
  bytesLE 16 pair.1 ++ bytesLE 16 (topHdr index) ++ zero16 ++ bytesLE 16 pair.2
/-- C4 (adapted from b3cc11b): the top root (heap 1) keeps the low half, so `topNode` is a plain `shortHash`. -/
theorem topNode_eq (index : Nat) (v o : Digest) : WCT9.topNode index v o = shortHash (topIn index v o) := by
  have hl : (route index 0).1 < 4096 := by
    have h1 : (route index 0).1 = index / 2 ^ 19 % 2 ^ 12 := rfl
    rw [h1]; exact Nat.mod_lt _ (by norm_num)
  have h0 : (route index 0).1 / 2 ^ (WCT9.topJ.val + 1) = 0 := Nat.div_eq_of_lt (by simp [WCT9.topJ]; omega)
  have hh : SigGolfCandidate.T3.nodeHalfHigh 3 (0 : Layer).val
      (2 ^ (height 0 - WCT9.topJ.val - 1) + (route index 0).1 / 2 ^ (WCT9.topJ.val + 1)) = false := by
    rw [h0]; decide
  unfold WCT9.topNode SigGolfCandidate.T3.nodeHash topIn topHdr
  rw [hh, SigGolfCandidate.T3.projHash_false]
theorem topIn_length (index : Nat) (v o : Digest) : (topIn index v o).length = 64 := by
  unfold topIn; simp [bytesLE_length, zero16]
def lo64 (d : Digest) : Word := d.extractLsb' 0 64
def hi64 (d : Digest) : Word := d.extractLsb' 64 64
def bitc (index : Nat) : Prop := (route index 0).1 / 2 ^ WCT9.topJ.val % 2 = 0
instance (index : Nat) : Decidable (bitc index) := by unfold bitc; infer_instance
def blkW (index : Nat) (v o : Digest) : List Word :=
  if bitc index then [lo64 v, hi64 v, lo64 (topHdr index), hi64 (topHdr index), 0, 0, lo64 o, hi64 o]
  else [lo64 o, hi64 o, lo64 (topHdr index), hi64 (topHdr index), 0, 0, lo64 v, hi64 v]
theorem wordsOf_topIn (index : Nat) (v o : Digest) : wordsOf (topIn index v o) = blkW index v o := by
  unfold topIn blkW bitc
  split <;>
  · rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
      wordsOf_bytesLE16]
    rename_i h
    simp only [h, ↓reduceIte, lo64, hi64, List.cons_append, List.nil_append]
/-- Offset of the sibling's high word in the block (and in its witness block). -/
def sOff (index : Nat) : Nat := if bitc index then 56 else 8
def bwi (index : Nat) : Nat := if bitc index then 7 else 1
theorem sOff_bwi (index : Nat) : sOff index = 8 * bwi index := by unfold sOff bwi; split <;> rfl
theorem blkW_hi (index : Nat) (v o : Digest) : (blkW index v o).getD (bwi index) 0 = hi64 o := by
  unfold blkW bwi; split <;> rfl
theorem blkW_other (index : Nat) (v o o' : Digest) (hlo : lo64 o = lo64 o') (i : Nat) (hi : i ≠ bwi index) :
    (blkW index v o).getD i 0 = (blkW index v o').getD i 0 := by
  unfold blkW; unfold bwi at hi
  split
  · rename_i h; rw [if_pos h] at hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp_all
  · rename_i h; rw [if_neg h] at hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp_all
theorem blkW_length (index : Nat) (v o : Digest) : (blkW index v o).length = 8 := by
  unfold blkW; split <;> rfl

theorem lo64_setTop (d : Digest) (c : Nat) : lo64 (WCT9.setTop d c) = lo64 d := by
  refine BitVec.eq_of_toNat_eq ?_
  unfold lo64
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftRight_zero,
    WCT9.setTop_toNat]
  have e : (2 : Nat) ^ 112 = 2 ^ 64 * 2 ^ 48 := by rw [← pow_add]
  rw [e]
  generalize (2 : Nat) ^ 64 = A
  generalize (2 : Nat) ^ 48 = B
  rw [show c % 2 ^ 16 * (A * B) = (c % 2 ^ 16 * B) * A by rw [Nat.mul_comm A B, ← Nat.mul_assoc],
    Nat.add_mul_mod_self_right, Nat.mod_mul_right_mod]
/-- The candidate words: the sibling's high word with the omitted 16 bits (T51: bits 112..127) set to `c`. -/
def wn (d : Digest) (c : Nat) : Nat := d.toNat % 2 ^ 112 / 2 ^ 64 + c * 2 ^ 48
theorem wn_lt (d : Digest) (c : Nat) (hc : c < 2 ^ 16) : wn d c < 2 ^ 64 := by
  unfold wn
  have h1 : d.toNat % 2 ^ 112 / 2 ^ 64 < 2 ^ 48 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    exact lt_of_lt_of_eq (Nat.mod_lt _ (by positivity)) (by norm_num)
  have h2 : c * 2 ^ 48 ≤ (2 ^ 16 - 1) * 2 ^ 48 := Nat.mul_le_mul_right _ (by omega)
  have h3 : (2 ^ 16 - 1) * 2 ^ 48 + 2 ^ 48 = (2 : Nat) ^ 64 := by norm_num
  omega
theorem hi64_setTop (d : Digest) (c : Nat) (hc : c < 2 ^ 16) :
    hi64 (WCT9.setTop d c) = BitVec.ofNat 64 (wn d c) := by
  refine BitVec.eq_of_toNat_eq ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wn_lt d c hc)]
  unfold hi64
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, WCT9.setTop_toNat, Nat.mod_eq_of_lt hc]
  have e : (2 : Nat) ^ 112 = 2 ^ 48 * 2 ^ 64 := by rw [← pow_add]
  rw [show c * 2 ^ 112 = (c * 2 ^ 48) * 2 ^ 64 by rw [e, Nat.mul_assoc],
    Nat.add_mul_div_right _ _ (by positivity)]
  exact Nat.mod_eq_of_lt (wn_lt d c hc)
theorem wn_succ (d : Digest) (c : Nat) : wn d c + 2 ^ 48 = wn d (c + 1) := by unfold wn; ring

/-- The sibling's high word sits 8 bytes past its witness slot offset. -/
theorem sOff_eq (index : Nat) :
    sOff index = SigGolfCandidate.T3M.Expand.sideOff (route index 0).1 11 + 8 := by
  unfold sOff SigGolfCandidate.T3M.Expand.sideOff
  have e : bitc index ↔ (route index 0).1 / 2 ^ 11 % 2 = 0 := Iff.rfl
  by_cases h : bitc index
  · rw [e] at h; rw [if_pos (e.mpr h), if_neg (by omega)]
  · rw [e] at h; rw [if_neg (fun h' => h (e.mp h')), if_pos (by omega)]
theorem bitc_iff (index : Nat) : bitc index ↔ index / 2 ^ 30 % 2 = 0 := by
  unfold bitc
  rw [show (route index 0).1 = index / 2 ^ 19 % 2 ^ 12 from rfl, show WCT9.topJ.val = 11 from rfl,
    show (2 : Nat) ^ 12 = 2 ^ 11 * 2 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod,
    Nat.div_div_eq_div_mul, ← pow_add]

/-! ### The loop -/

structure SInv (index : Nat) (v sib pk : Digest) (s8 : MachineState) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 42829
  x5 : t.getReg .x5 = 0
  x30 : t.getReg .x30 = BitVec.ofNat 64 c
  x7 : t.getReg .x7 = BitVec.ofNat 64 (wn sib (c - 1))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (NODE + sOff index)
  x31 : t.getReg .x31 = BitVec.ofNat 64 (0x2c48 + sOff index)
  x10 : t.getReg .x10 = BitVec.ofNat 64 NODE
  x11 : t.getReg .x11 = BitVec.ofNat 64 64
  x12 : t.getReg .x12 = BitVec.ofNat 64 NOUT
  x13 : t.getReg .x13 = lo64 pk
  x14 : t.getReg .x14 = hi64 pk
  x15 : t.getReg .x15 = BitVec.ofNat 64 (2 ^ 48)
  x17 : t.getReg .x17 = BitVec.ofNat 64 65536
  hc1 : 1 ≤ c
  hc2 : c < 65536
  blk : ∀ i < 8, t.getMem (BitVec.ofNat 64 (NODE + 8 * i)) = (blkW index v (WCT9.setTop sib (c - 1))).getD i 0
  frame : Frame s8 t (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32))

def SQ (index : Nat) (sib : Digest) (s8 : MachineState) : Option Nat → MachineState → Prop
  | none, t => t.pc = pcOf 354
  | some c, t => t.pc = pcOf 351 ∧ (c = 0 → Frame s8 t (fun _ => False)) ∧
      (c ≠ 0 → c < 65536 ∧ t.getMem (BitVec.ofNat 64 (0x2c48 + sOff index)) = hi64 (WCT9.setTop sib c) ∧
        Frame s8 t (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨
          A = 0x2c48 + sOff index))

theorem pk_split (root pk : Digest) : root = pk ↔ lo64 root = lo64 pk ∧ hi64 root = hi64 pk := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h : i < 64
    · have := congrArg (fun x => x.getLsbD i) h0
      simpa [lo64, BitVec.getLsbD_extractLsb', h] using this
    · have := congrArg (fun x => x.getLsbD (i - 64)) h1
      simp [hi64, BitVec.getLsbD_extractLsb', show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega] at this
      simpa using this

theorem a_lo (a : BitVec 256) : lo64 (a.extractLsb' 0 128) = a.extractLsb' 0 64 := by
  refine BitVec.eq_of_toNat_eq ?_
  simp only [lo64, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
theorem a_hi (a : BitVec 256) : hi64 (a.extractLsb' 0 128) = a.extractLsb' 64 64 := by
  refine BitVec.eq_of_toNat_eq ?_
  simp only [hi64, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]

section loop
variable {im : Image} (hS : SrchCoreAt im) {sk : BitVec 256} (index : Nat) (v sib pk : Digest) (s8 : MachineState)
include hS

omit hS in
theorem sOff_cases (index : Nat) : sOff index = 8 ∨ sOff index = 56 := by unfold sOff; split <;> simp

theorem search_loop : ∀ fuel c t, c + fuel = 65536 → SInv index v sib pk s8 c t →
    TBSim im sk t (fuel * 30) (WCT9.searchTop index v sib pk fuel c) (SQ index sib s8) := by
  intro fuel
  induction fuel with
  | zero => intro c t hcf hI; have := hI.hc2; omega
  | succ fuel ih =>
    intro c t hcf hI
    have hcs : c < 2 ^ 16 := by have := hI.hc2; omega
    have hso := sOff_cases index
    obtain ⟨t1, st1, p1, x7', mB, r1, f1⟩ := l1_spec hS t hI.pc (NODE + sOff index) (wn sib (c - 1)) (2 ^ 48)
      (by rcases hso with h | h <;> rw [h] <;> decide) (by rcases hso with h | h <;> rw [h] <;> decide)
      hI.x28 hI.x7 hI.x15
    rw [show wn sib (c - 1) + 2 ^ 48 = wn sib c by rw [wn_succ]; congr 1; have := hI.hc1; omega] at x7' mB
    have hblk1 : ∀ i < 8, t1.getMem (BitVec.ofNat 64 (NODE + 8 * i)) =
        (blkW index v (WCT9.setTop sib c)).getD i 0 := by
      intro i hi
      by_cases hib : i = bwi index
      · subst hib
        rw [← sOff_bwi, mB, blkW_hi, hi64_setTop _ _ hcs]
      · rw [f1.get (by simp only [NODE]; omega) (by rw [sOff_bwi]; omega), hI.blk i hi,
          blkW_other index v _ _ ((lo64_setTop _ _).trans (lo64_setTop _ _).symm) i hib]
    have g1 : ∀ r, r ≠ .x7 → t1.getReg r = t.getReg r := fun r hr => r1.get (by simpa using hr)
    have hq : hashInput t1 = toQ (pad64 (topIn index v (WCT9.setTop sib c))) := by
      rw [pad64_of_aligned _ (by rw [topIn_length])]
      refine hashInput_toQ t1 _ 0 NODE (topIn_length _ _ _) (by rw [g1 _ (by decide)]; exact hI.x10) (by decide)
        (by decide) (by rw [g1 _ (by decide)]; exact hI.x11) (by decide) ?_
      have hr := readWords_ext t1 (blkW index v (WCT9.setTop sib c)) NODE
        (fun i hi => by rw [blkW_length] at hi; exact hblk1 i hi)
      rw [blkW_length] at hr
      rw [wordsOf_topIn]
      exact hr
    have hv : hashArgumentsValid t1 = true :=
      hashArgs_const t1 NODE 64 NOUT (by rw [g1 _ (by decide)]; exact hI.x10) (by rw [g1 _ (by decide)]; exact hI.x11)
        (by rw [g1 _ (by decide)]; exact hI.x12) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hf1 : fetch im t1 = some (.base .ECALL) := by
      have hc := codeAt_srch hS 36 1 (by decide)
      exact (hc.fetch t1 p1).trans rfl
    unfold WCT9.searchTop
    rw [topNode_eq]
    refine (TBSim.steps st1 (tb_shortHash_bind' (W := fuel * 30 + 7) hf1 (by rw [g1 _ (by decide)]; exact hI.x5) hv hq
      (fun a => ?_))).mono ?_ (fun _ _ h => h)
    rotate_left
    · rw [pad64_of_aligned _ (by rw [topIn_length]), blocks_toQ ⟨by rw [topIn_length]; omega,
        by rw [topIn_length]⟩, topIn_length]; omega
    set t2 := writeHash t1 a with ht2
    have p2 : t2.pc = pcOf 42832 := by rw [ht2, pc_writeHash, p1]; rfl
    have g2 : ∀ r, r ≠ .x7 → t2.getReg r = t.getReg r := fun r hr => by rw [ht2, getReg_writeHash]; exact g1 r hr
    have fw := Frame.writeHash t1 a NOUT (by rw [g1 _ (by decide)]; exact hI.x12) (by decide)
    have hlo : t2.getMem (BitVec.ofNat 64 NOUT) = a.extractLsb' 0 64 := by
      have := (DigAt.writeHash_lo t1 a NOUT (by rw [g1 _ (by decide)]; exact hI.x12) (by decide)).1
      rw [this, ← a_lo]; rfl
    have hhi : t2.getMem (BitVec.ofNat 64 (NOUT + 8)) = a.extractLsb' 64 64 := by
      have := (DigAt.writeHash_lo t1 a NOUT (by rw [g1 _ (by decide)]; exact hI.x12) (by decide)).2
      rw [this, ← a_hi]; rfl
    obtain ⟨t3, st3, p3, r3, f3⟩ := l2_spec hS t2 p2 (by rw [g2 _ (by decide)]; exact hI.x12)
    rw [hlo, g2 _ (by decide), hI.x13] at p3
    have hsplit := pk_split (a.extractLsb' 0 128) pk
    rw [a_lo, a_hi] at hsplit
    have F3 : Frame s8 t3 (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) := by
      refine (((hI.frame.trans f1).trans fw).trans f3).mono (fun A _ h => ?_)
      rcases h with ((h | h) | h) | h
      · exact h
      · left; subst h; rcases hso with e | e <;> rw [e] <;> simp only [NODE] <;> omega
      · right; exact h
      · exact h.elim
    have g3 : ∀ r, r ≠ .x7 → r ≠ .x6 → t3.getReg r = t.getReg r := fun r h7 h6 => by
      rw [r3.get (by simpa using h6)]; exact g2 r h7
    have next : ∀ (u : MachineState), u.pc = pcOf 42836 →
        (∀ r, r ≠ .x7 → r ≠ .x6 → u.getReg r = t.getReg r) → u.getReg .x7 = BitVec.ofNat 64 (wn sib c) →
        (∀ i < 8, u.getMem (BitVec.ofNat 64 (NODE + 8 * i)) = (blkW index v (WCT9.setTop sib c)).getD i 0) →
        Frame s8 u (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) →
        TBSim im sk u (fuel * 30 + 3) (WCT9.searchTop index v sib pk fuel (c + 1)) (SQ index sib s8) := by
      intro u pu gu x7u blku Fu
      obtain ⟨t4, st4, p4, x30', r4, f4⟩ := l4_spec hS u pu c hI.hc2
        (by rw [gu _ (by decide) (by decide)]; exact hI.x30) (by rw [gu _ (by decide) (by decide)]; exact hI.x17)
      by_cases hlast : c + 1 < 65536
      · rw [if_pos hlast] at p4
        have g4 : ∀ r, r ≠ .x30 → t4.getReg r = u.getReg r := fun r hr => r4.get (by simpa using hr)
        have hI' : SInv index v sib pk s8 (c + 1) t4 := by
          refine ⟨p4, ?_, x30', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hlast, ?_, ?_⟩
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x5
          · rw [g4 _ (by decide), x7u]; rfl
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x28
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x31
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x10
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x11
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x12
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x13
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x14
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x15
          · rw [g4 _ (by decide), gu _ (by decide) (by decide)]; exact hI.x17
          · intro i hi; rw [f4.get (by simp only [NODE]; omega) (fun h => h), blku i hi, Nat.add_sub_cancel]
          · exact (Fu.trans f4).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)
        exact (TBSim.steps st4 (ih (c + 1) t4 (by omega) hI')).mono (by omega) (fun _ _ h => h)
      · rw [if_neg hlast] at p4
        have hfuel : fuel = 0 := by omega
        subst hfuel
        have st5 := jal_at hS t4 42838 354 (by decide) (by decide) 2199740527 rfl (by decide) p4
        unfold WCT9.searchTop
        exact (TBSim.steps (st4.trans st5) (TBSim.pure (show (t4.setPC (pcOf 354)).pc = pcOf 354 from rfl))).mono
          (by omega) (fun _ _ h => h)
    by_cases hl : a.extractLsb' 0 64 = lo64 pk
    · rw [if_pos hl] at p3
      obtain ⟨t4, st4, p4, r4, f4⟩ := l3_spec hS t3 p3 (by rw [g3 _ (by decide) (by decide)]; exact hI.x12)
      rw [f3.get (by decide) (by simp), hhi, r3.get (by decide), g2 _ (by decide), hI.x14] at p4
      by_cases hh : a.extractLsb' 64 64 = hi64 pk
      · rw [if_pos hh] at p4
        have hroot : a.extractLsb' 0 128 = pk := hsplit.mpr ⟨hl, hh⟩
        rw [if_pos hroot]
        obtain ⟨t5, st5, p5, m5, r5, f5⟩ := f1_spec hS t4 p4 (0x2c48 + sOff index)
          (by rcases hso with e | e <;> rw [e] <;> decide) (by rcases hso with e | e <;> rw [e] <;> decide)
          (by rw [r4.get (by decide), g3 _ (by decide) (by decide)]; exact hI.x31)
        have st6 := jal_at hS t5 42840 351 (by decide) (by decide) 2178769007 rfl (by decide) p5
        refine (TBSim.steps (st3.trans (st4.trans (st5.trans st6))) (TBSim.pure ⟨rfl,
          fun h => absurd h (by have := hI.hc1; omega), fun _ => ⟨hI.hc2, ?_, ?_⟩⟩)).mono (by omega)
          (fun _ _ h => h)
        · show t5.getMem _ = _
          rw [m5, r4.get (by decide), r3.get (by decide), ht2, getReg_writeHash, x7', hi64_setTop _ _ hcs]
        · show Frame s8 (t5.setPC (pcOf 351)) _
          refine ((F3.trans f4).trans f5).mono (fun A _ h => ?_)
          rcases h with (h | h) | h
          · rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · exact h.elim
          · exact Or.inr (Or.inr h)
      · rw [if_neg hh] at p4
        have hroot : a.extractLsb' 0 128 ≠ pk := fun h => hh (hsplit.mp h).2
        rw [if_neg hroot]
        refine (TBSim.steps (st3.trans st4) (next t4 p4 ?_ ?_ ?_ ?_)).mono (by omega) (fun _ _ h => h)
        · intro r h7 h6; rw [r4.get (by simpa using h6)]; exact g3 r h7 h6
        · rw [r4.get (by decide), r3.get (by decide), ht2, getReg_writeHash, x7']
        · intro i hi
          rw [f4.get (by simp only [NODE]; omega) (fun h => h), f3.get (by simp only [NODE]; omega) (fun h => h),
            ht2, fw.get (by simp only [NODE]; omega) (by simp only [NODE, NOUT]; omega), hblk1 i hi]
        · exact (F3.trans f4).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)
    · rw [if_neg hl] at p3
      have hroot : a.extractLsb' 0 128 ≠ pk := fun h => hl (hsplit.mp h).1
      rw [if_neg hroot]
      refine (TBSim.steps st3 (next t3 p3 (fun r h7 h6 => g3 r h7 h6) ?_ ?_ F3)).mono (by omega)
        (fun _ _ h => h)
      · rw [r3.get (by decide), ht2, getReg_writeHash, x7']
      · intro i hi
        rw [f3.get (by simp only [NODE]; omega) (fun h => h), ht2,
          fw.get (by simp only [NODE]; omega) (by simp only [NODE, NOUT]; omega), hblk1 i hi]
end loop


theorem shr_and (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x >>> 30 &&& 1) = BitVec.ofNat 64 (x / 2 ^ 30 % 2) := by
  show (BitVec.ofNat 64 x >>> 30 &&& 1#64) = _
  refine BitVec.eq_of_toNat_eq ?_
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, pow_one,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num) : x / 2 ^ 30 % 2 < 2 ^ 64)]

theorem search_entry_core {im : Image} (hS : SrchCoreAt im) {sk : BitVec 256} (index : Nat) (hidx : index < 2 ^ 31)
    (v sib root0 pk : Digest) (hsib : WCT9.setTop sib 0 = sib) (s8 : MachineState) (hpc : s8.pc = pcOf 42795)
    (hx5 : s8.getReg .x5 = 0) (henc : DigAt s8 ENC root0)
    (hpk0 : s8.getMem (BitVec.ofNat 64 0xA0) = lo64 pk) (hpk1 : s8.getMem (BitVec.ofNat 64 0xA8) = hi64 pk)
    (hix : s8.getMem (BitVec.ofNat 64 0x20550) = BitVec.ofNat 64 index)
    (hblk : ∀ i < 8, s8.getMem (BitVec.ofNat 64 (NODE + 8 * i)) = (blkW index v sib).getD i 0) :
    TBSim im sk s8 (65535 * 30 + 100)
      (if root0 = pk then pure (some 0) else WCT9.searchTop index v sib pk WCT9.searchFuel 1) (SQ index sib s8) := by
  have st0 : Steps im s8 0 0 s8 := Steps.refl s8
  set u0 := s8 with hu0
  have gu0 : ∀ A, u0.getMem A = s8.getMem A := fun _ => rfl
  have ru0 : ∀ r, u0.getReg r = s8.getReg r := fun _ => rfl
  obtain ⟨u1, st1, p1, x28, x13, x14, r1, f1⟩ := s1_spec hS u0 hpc
  rw [gu0, gu0, henc.1, hpk0] at p1
  rw [gu0, hpk0] at x13
  rw [gu0, hpk1] at x14
  have hsplit := pk_split root0 pk
  have miss : root0 ≠ pk → ∀ (u : MachineState) (k : Nat), Steps im s8 k k u → k ≤ 12 → u.pc = pcOf 42805 →
      (∀ r, r ≠ .x6 → r ≠ .x13 → r ≠ .x14 → r ≠ .x28 → r ≠ .x29 → u.getReg r = s8.getReg r) →
      u.getReg .x13 = lo64 pk → u.getReg .x14 = hi64 pk → Frame s8 u (fun _ => False) →
      TBSim im sk s8 (65535 * 30 + 100)
        (if root0 = pk then pure (some 0) else WCT9.searchTop index v sib pk WCT9.searchFuel 1) (SQ index sib s8) := by
    intro hne u k stu hk pu gu u13 u14 fu
    rw [if_neg hne]
    obtain ⟨u2, st2, p2, x7a, r2, f2⟩ := m1_spec hS u pu
    rw [fu.get (by decide) (fun h => h), hix, shr_and index (by omega)] at p2
    have hbit : (BitVec.ofNat 64 (index / 2 ^ 30 % 2) = 0) ↔ bitc index := by
      rw [bitc_iff]
      constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this; omega
      · intro h; rw [h]; rfl
    -- reach the setup block with x7 = sOff index
    obtain ⟨u3, k3, st3, hk3, p3, x7b, r3, f3⟩ : ∃ u3 k3, Steps im u2 k3 k3 u3 ∧ k3 ≤ 1 ∧ u3.pc = pcOf 42813 ∧
        u3.getReg .x7 = BitVec.ofNat 64 (sOff index) ∧ RegsExcept u2 u3 [.x7] ∧ Frame u2 u3 (fun _ => False) := by
      by_cases hb : bitc index
      · rw [if_pos (hbit.mpr hb)] at p2
        obtain ⟨u3, st3, p3, x7b, r3, f3⟩ := m2_spec hS u2 p2
        refine ⟨u3, 1, st3, le_rfl, p3, ?_, r3, f3⟩
        rw [x7b]; unfold sOff; rw [if_pos hb]
      · rw [if_neg (fun h => hb (hbit.mp h))] at p2
        refine ⟨u2, 0, Steps.refl u2, by omega, p2, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
        rw [x7a]; unfold sOff; rw [if_neg hb]
    obtain ⟨u4, st4, p4, x28', x31', x7', x15', x10', x11', x12', x30', x17', r4, f4⟩ :=
      sd_spec hS u3 p3 (sOff index) (sOff_cases index) x7b
    have F4 : Frame s8 u4 (fun _ => False) :=
      (((fu.trans f2).trans f3).trans f4).mono (fun A _ h => by
        rcases h with ((h | h) | h) | h <;> exact h)
    have g4 : ∀ r, r ∉ [Reg.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x17, .x28, .x29, .x30, .x31] →
        u4.getReg r = s8.getReg r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [r4.get (by simp [hr]),
        r3.get (by simp [hr]), r2.get (by simp [hr]),
        gu r hr.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.1]
    have F3 : Frame s8 u3 (fun _ => False) :=
      ((fu.trans f2).trans f3).mono (fun A _ h => by rcases h with (h | h) | h <;> exact h)
    have hI : SInv index v sib pk s8 1 u4 := by
      refine ⟨p4, ?_, x30', ?_, x28', x31', x10', x11', x12', ?_, ?_, x15', x17', le_rfl, by decide, ?_, ?_⟩
      · rw [g4 _ (by decide)]; exact hx5
      · rw [x7', F3.get (show NODE + sOff index < 2 ^ 64 by unfold sOff; split <;> simp only [NODE] <;> omega)
          (fun h => h),
          sOff_bwi, hblk _ (by unfold bwi; split <;> omega), blkW_hi, show 1 - 1 = 0 from rfl]
        have e := hi64_setTop sib 0 (by decide)
        rw [hsib] at e
        exact e
      · rw [r4.get (by decide), r3.get (by decide), r2.get (by decide)]; exact u13
      · rw [r4.get (by decide), r3.get (by decide), r2.get (by decide)]; exact u14
      · intro i hi; rw [F4.get (by simp only [NODE]; omega) (fun h => h), hblk i hi, show 1 - 1 = 0 from rfl, hsib]
      · exact F4.mono (fun A _ h => h.elim)
    have hloop := search_loop hS (sk := sk) index v sib pk s8 65535 1 u4 (by decide) hI
    refine (TBSim.steps (stu.trans (st2.trans (st3.trans st4))) hloop).mono ?_ (fun _ _ h => h)
    omega
  by_cases hl : root0.extractLsb' 0 64 = lo64 pk
  · rw [if_pos hl] at p1
    obtain ⟨u2, st2, p2, r2, f2⟩ := s2_spec hS u1 p1 x28
    rw [f1.get (by decide) (fun h => h), gu0, henc.2] at p2
    rw [x14] at p2
    by_cases hh : root0.extractLsb' 64 64 = hi64 pk
    · rw [if_pos hh] at p2
      have hroot : root0 = pk := hsplit.mpr ⟨hl, hh⟩
      rw [if_pos hroot]
      have st3 := jal_at hS u2 42804 351 (by decide) (by decide) 2329763951 rfl (by decide) p2
      refine (TBSim.steps (st0.trans (st1.trans (st2.trans st3))) (TBSim.pure ⟨rfl, fun _ => ?_,
        fun h => absurd rfl h⟩)).mono (by omega) (fun _ _ h => h)
      intro A hA hn
      show u2.getMem _ = s8.getMem _
      exact (f1.trans f2) A hA (fun h => by rcases h with h | h <;> exact h)
    · rw [if_neg hh] at p2
      exact miss (fun h => hh (hsplit.mp h).2) u2 _ (st0.trans (st1.trans st2)) (by omega) p2
        (fun r h6 h13 h14 h28 h29 => by rw [r2.get (by simpa using h6), r1.get (by simp [h6, h13, h14, h28, h29]), ru0])
        (by rw [r2.get (by decide)]; exact x13) (by rw [r2.get (by decide)]; exact x14)
        ((f1.trans f2).mono (fun A _ h => by rcases h with h | h <;> exact h))
  · rw [if_neg hl] at p1
    exact miss (fun h => hl (hsplit.mp h).1) u1 _ (st0.trans st1) (by omega) p1
      (fun r h6 h13 h14 h28 h29 => by rw [r1.get (by simp [h6, h13, h14, h28, h29]), ru0]) x13 x14 f1


/-! ### The top layer's last block, as the search reads it -/

theorem topBlk_words (sig : WCT9.Signature) (index : Nat) (v : Digest) (t : MachineState)
    (h : SigGolfCandidate.T3M.Expand.TopBlkG (WCT9.toT3Signature sig) index 0 v t) :
    t.readWords (BitVec.ofNat 64 NODE) 8 = blkW index v (WCT9.topSib sig) := by
  rw [← wordsOf_topIn]
  unfold SigGolfCandidate.T3M.Expand.TopBlkG at h
  have hl : SigGolfCandidate.T3M.Expand.lpath (WCT9.toT3Signature sig) 0 11 = WCT9.topSib sig := by
    unfold SigGolfCandidate.T3M.Expand.lpath; rw [dif_pos (by decide)]; rfl
  rw [h, hl]
  unfold topIn topHdr
  have h11 : WCT9.topJ.val = 11 := rfl
  simp only [h11]
  by_cases hc : (route index 0).1 / 2 ^ 11 % 2 = 0
  · simp only [hc, ↓reduceIte]
  · simp only [hc, ↓reduceIte]

theorem topBlk_get (sig : WCT9.Signature) (index : Nat) (v : Digest) (t : MachineState)
    (h : SigGolfCandidate.T3M.Expand.TopBlkG (WCT9.toT3Signature sig) index 0 v t) :
    ∀ i < 8, t.getMem (BitVec.ofNat 64 (NODE + 8 * i)) = (blkW index v (WCT9.topSib sig)).getD i 0 := by
  intro i hi
  have e := topBlk_words sig index v t h
  rw [readWords_eight] at e
  rw [← e]
  interval_cases i <;> rfl

/-! ### The reference expander split at the old front -/

end ClaudeWCT.W9.Machine.Expand
end

namespace ClaudeWCT.W9.Machine.Expand.SharedControl
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem validate_code : CodeAt Images.expandImage (pcOf 342) [0x7ec2d06f] := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem validate_step (s : MachineState) (hp:s.pc=pcOf 342) :
    Steps Images.expandImage s 1 1 (s.setPC (pcOf 46929)) := by
  obtain ⟨imm,hd,hoff⟩ := jalTo_sound (show jalTo (0x7ec2d06f#32) 342=some 46929 by decide)
  exact jal_x0_step validate_code hd hoff s hp
theorem compact_code : CodeAt Images.expandImage (pcOf 351) [0x4d52706f] := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem scatter_code : CodeAt Images.expandImage (pcOf 43761) [0x24c0306f] := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_srchCore : SrchCoreAt Images.expandImage := by
  apply codeAt_expand_current_chunk <;> decide +kernel
end ClaudeWCT.W9.Machine.Expand.SharedControl
end
-- ==== merged from T3M_Submission ====
section

section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy
theorem layoutValid_of_data_length (image : Riscv.Image) (layout : Layout)
    (sizes : Sizes) (d : Nat) (hd : image.data.length = d) :
    Riscv.layoutValid layout sizes image ↔
      (Riscv.layoutBuffers layout sizes).all (fun buffer =>
        decide (buffer.1 % 8 = 0 ∧ buffer.1 + buffer.2 ≤
          16 * ((MEMORY_BYTES - d) / 16))) = true ∧
      Riscv.buffersDisjoint (Riscv.layoutBuffers layout sizes) = true := by
  unfold Riscv.layoutValid Riscv.dataBase
  rw [hd]
end SigGolfCandidate.T3M
end
section
set_option maxRecDepth 10000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy
def submission : Submission where
  sizes := ⟨5310, 22012, 131072⟩
  layout := ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩
  image
    | .keygen => Images.keygenImage
    | .sign => Images.signImage
    | .expand => Images.expandImage
    | .verify => Images.verifyImage
@[simp] theorem submission_sizes : submission.sizes = ⟨5310, 22012, 131072⟩ := rfl
@[simp] theorem submission_layout : submission.layout = ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ := rfl
@[simp] theorem submission_keygen : submission.image .keygen = Images.keygenImage := rfl
@[simp] theorem submission_sign : submission.image .sign = Images.signImage := rfl
@[simp] theorem submission_expand : submission.image .expand = Images.expandImage := rfl
@[simp] theorem submission_verify : submission.image .verify = Images.verifyImage := rfl
theorem submission_keygen_valid :
    (submission.image .keygen).Valid submission.sizes submission.layout := by
  rw [submission_keygen, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.keygenImage.code.length = 1177 from Images.keygenCode_length,
    show Images.keygenImage.data.length = 0 from Images.keygenData_length]
  rw [layoutValid_of_data_length _ _ _ 0 Images.keygenData_length]
  decide +kernel
theorem submission_sign_valid :
    (submission.image .sign).Valid submission.sizes submission.layout := by
  rw [submission_sign, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.signImage.code.length = 25046 from Images.signCode_length,
    show Images.signImage.data.length = 86144 from Images.signData_length]
  rw [layoutValid_of_data_length _ _ _ 86144 Images.signData_length]
  decide +kernel
theorem submission_expand_valid :
    (submission.image .expand).Valid submission.sizes submission.layout := by
  rw [submission_expand, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.expandImage.code.length = 254656 from Images.expandCode_length,
    show Images.expandImage.data.length = 29936 from Images.expandData_length]
  rw [layoutValid_of_data_length _ _ _ 29936 Images.expandData_length]
  decide +kernel
set_option maxRecDepth 200000 in
theorem submission_verify_valid :
    (submission.image .verify).Valid submission.sizes submission.layout := by
  rw [submission_verify, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.verifyImage.code.length = 257258 from Images.verifyCode_length,
    show Images.verifyImage.data.length = 16928 from Images.verifyData_length]
  rw [layoutValid_of_data_length _ _ _ 16928 Images.verifyData_length]
  decide +kernel
theorem submission_admissible : submission.Admissible := by
  refine ⟨by unfold Sizes.Valid; decide, ?_⟩
  intro phase
  cases phase
  · exact submission_keygen_valid
  · exact submission_sign_valid
  · exact submission_expand_valid
  · exact submission_verify_valid
end SigGolfCandidate.T3M
end

/-! Concrete image wrapper for the paired forest candidate. The exported
challenge submission remains separate until every certificate premise is closed. -/
namespace SigGolfCandidate.T3M.Paired
open SigGolfCandidate.Legacy

def submission : Submission where
  sizes := ⟨5195, 22012, 131072⟩
  layout := ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩
  image := SigGolfCandidate.T3M.submission.image

@[simp] theorem submission_sizes : submission.sizes = ⟨5195, 22012, 131072⟩ := rfl
@[simp] theorem submission_layout : submission.layout = ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x1020⟩ := rfl
@[simp] theorem submission_image : submission.image = SigGolfCandidate.T3M.submission.image := rfl
@[simp] theorem submission_keygen : submission.image .keygen = Images.keygenImage := rfl
@[simp] theorem submission_sign : submission.image .sign = Images.signImage := rfl
@[simp] theorem submission_expand : submission.image .expand = Images.expandImage := rfl
@[simp] theorem submission_verify : submission.image .verify = Images.verifyImage := rfl

end SigGolfCandidate.T3M.Paired

namespace SigGolfCandidate.T3M.Paired
open SigGolfCandidate.Legacy
set_option maxRecDepth 200000
theorem submission_keygen_valid :
    (submission.image .keygen).Valid submission.sizes submission.layout := by
  rw [submission_keygen, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.keygenImage.code.length = 1177 from Images.keygenCode_length,
    show Images.keygenImage.data.length = 0 from Images.keygenData_length]
  rw [layoutValid_of_data_length _ _ _ 0 Images.keygenData_length]
  decide +kernel
theorem submission_sign_valid :
    (submission.image .sign).Valid submission.sizes submission.layout := by
  rw [submission_sign, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.signImage.code.length = 25046 from Images.signCode_length,
    show Images.signImage.data.length = 86144 from Images.signData_length]
  rw [layoutValid_of_data_length _ _ _ 86144 Images.signData_length]
  decide +kernel
theorem submission_expand_valid :
    (submission.image .expand).Valid submission.sizes submission.layout := by
  rw [submission_expand, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.expandImage.code.length = 254656 from Images.expandCode_length,
    show Images.expandImage.data.length = 29936 from Images.expandData_length]
  rw [layoutValid_of_data_length _ _ _ 29936 Images.expandData_length]
  decide +kernel
set_option maxRecDepth 200000 in
theorem submission_verify_valid :
    (submission.image .verify).Valid submission.sizes submission.layout := by
  rw [submission_verify, submission_sizes, submission_layout]
  rw [Riscv.Image.Valid]
  rw [Riscv.Image.byteSize,
    show Images.verifyImage.code.length = 257258 from Images.verifyCode_length,
    show Images.verifyImage.data.length = 16928 from Images.verifyData_length]
  rw [layoutValid_of_data_length _ _ _ 16928 Images.verifyData_length]
  decide +kernel
theorem submission_admissible : submission.Admissible := by
  refine ⟨by unfold Sizes.Valid; decide, ?_⟩
  intro phase
  cases phase
  · exact submission_keygen_valid
  · exact submission_sign_valid
  · exact submission_expand_valid
  · exact submission_verify_valid
end SigGolfCandidate.T3M.Paired
end
