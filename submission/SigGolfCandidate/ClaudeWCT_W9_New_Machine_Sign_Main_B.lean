import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_Main_A

set_option Elab.async false


namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure ExtraCode (im : Image) : Prop where
  front : CodeAt im (pcOf 22100) frontCode
  copyA : CodeAt im (pcOf 22107) copy22107Code
  zero : CodeAt im (pcOf 22115) zeroCode
  hint : CodeAt im (pcOf 22124) hintCode
  donePrep : CodeAt im (pcOf 22164) donePrepCode
  copyB : CodeAt im (pcOf 22171) copy22171Code
  doneExit : CodeAt im (pcOf 22179) doneExitCode

theorem entry_steps {im : Image} (hc : ExtraCode im)
    (s : MachineState) (hp : s.pc=pcOf 22100) (left right : Digest)
    (hl : DigAt s ENC left) (hr : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 28 28 t ∧ t.pc=pcOf 22128 ∧ t.getReg .x8=1 ∧
      DigAt t (0x66000+160) left ∧ DigAt t (0x66000+176) right ∧
      t.getMem (0x66000#64)=0 ∧
      (∀ i,i<43 → t.getByte (BitVec.ofNat 64 (DIGITS+i))=0) ∧
      RegsExcept s t [.x6,.x7,.x8,.x28,.x29] ∧
      Frame s t (fun A => A=0x66000 ∨ 0x66000+160≤A ∧ A<0x66000+192 ∨ DIGITS≤A ∧ A<DIGITS+56) := by
  obtain ⟨a,sa,pa,a8,a28,a29,ar,af⟩ := front_steps hc.front s hp
  obtain ⟨b,ab,pb,bl,br,brs,bf⟩ := copy22107_steps hc.copyA a pa (0x66000+160)
    (by decide) (by decide) (by decide) (by decide) a28 a29 left right
    (hl.frame af (by decide) (fun h => h) (fun h => h))
    (hr.frame af (by decide) (fun h => h) (fun h => h))
  obtain ⟨c,bc,pc,cz,cr,cf⟩ := zero_steps hc.zero b pb
  obtain ⟨t,ct,pt,t8,th,tr,tf⟩ := hint_steps hc.hint c pc
  have ft : Frame b t (fun A => DIGITS≤A ∧ A<DIGITS+56 ∨ A=0x66000) := (cf.trans tf).mono (by tauto)
  refine ⟨t,sa.trans (ab.trans (bc.trans ct)),pt,t8,?_,?_,th,?_,?_,?_⟩
  · exact bl.frame ft (by decide) (by unfold DIGITS; omega) (by unfold DIGITS; omega)
  · exact br.frame ft (by decide) (by unfold DIGITS; omega) (by unfold DIGITS; omega)
  · intro i hi
    rw [tf.getByte (by unfold DIGITS; omega) (by unfold DIGITS; omega)]
    rw [getByte_eq_word c (DIGITS+i) (by unfold DIGITS; omega)]
    rw [show (DIGITS+i)/8*8=DIGITS+8*(i/8) by unfold DIGITS; omega,cz _ (by omega)]
    simp [extractByte]
  · exact (((ar.trans brs).trans cr).trans tr).mono (by simp)
  · exact (((af.trans bf).trans cf).trans tf).mono (by intros A hA hw; rcases hw with ((hw|hw)|hw)|hw <;> tauto)

theorem done_steps {im : Image} (hc : ExtraCode im)
    (s : MachineState) (hp : s.pc=pcOf 22164) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (left right : Digest)
    (hleft : DigAt s ENC left) (hright : DigAt s (ENC+48) right) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=(if lay<3 then pcOf 22128 else pcOf 22182) ∧
      t.getReg .x8=BitVec.ofNat 64 (lay+1) ∧
      DigAt t (0x66000+64+32*(lay-1)) left ∧ DigAt t (0x66000+80+32*(lay-1)) right ∧
      RegsExcept s t [.x6,.x7,.x8,.x28,.x29,.x30] ∧
      Frame s t (fun A => 0x66000+64+32*(lay-1)≤A ∧ A<0x66000+96+32*(lay-1)) := by
  obtain ⟨a,sa,pa,a28,a29,ar,af⟩ := donePrep_steps hc.donePrep s hp lay hl hh h8
  obtain ⟨b,ab,pb,bl,br,brs,bf⟩ := copy22171_steps hc.copyB a pa (0x66000+64+32*(lay-1))
    (by omega) (by omega) (by omega) (by interval_cases lay <;> decide) a28 a29 left right
    (hleft.frame af (by decide) (fun h => h) (fun h => h))
    (hright.frame af (by decide) (fun h => h) (fun h => h))
  have b8 : b.getReg .x8=BitVec.ofNat 64 lay := (brs.get (by decide)).trans ((ar.get (by decide)).trans h8)
  obtain ⟨t,bt,pt,t8,tr,tf⟩ := doneExit_steps hc.doneExit b pb lay hl hh b8
  refine ⟨t,sa.trans (ab.trans bt),pt,t8,bl.frame tf (by omega) (fun h => h) (fun h => h),?_,?_,?_⟩
  · have h := br.frame tf (by omega) (fun h => h) (fun h => h)
    convert h using 1 <;> omega
  · exact ((ar.trans brs).trans tr).mono (by simp)
  · exact ((af.trans bf).trans tf).mono (by
      intros A hA hw
      rcases hw with (hw|hw)|hw
      · exact hw.elim
      · omega
      · exact hw.elim)
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_extraCode : ExtraCode Images.signImage := by
  constructor
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
abbrev buffer (lay i d : Nat) : Nat := 0x6e000+8192*lay+128*i+16*d
def stepCode : List (BitVec 32) := bv_list% 32 [0x431313,0x6c0e33,0xe3303,0x8e3383,0x6bb023,0x7bb423,0x1b0b13,0x10b8b93,0x80c0c13,0x1a8a93,0x2b00313,0xfc6ae8e3]
sym_block step := symRun { noAlias := true } stepCode (pcOf 22436) 100

theorem step_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (s : MachineState) (hp : s.pc=pcOf 22436) (lay i d sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hi : i<43) (hd : d<8)
    (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (h6 : s.getReg .x6=BitVec.ofNat 64 d) (h21 : s.getReg .x21=BitVec.ofNat 64 i)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (h23 : s.getReg .x23=BitVec.ofNat 64 (sb+16*i))
    (h24 : s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0)) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=(if i+1<43 then pcOf 22435 else pcOf 22448) ∧
      t.getReg .x21=BitVec.ofNat 64 (i+1) ∧ t.getReg .x22=BitVec.ofNat 64 (DIGITS+i+1) ∧
      t.getReg .x23=BitVec.ofNat 64 (sb+16*(i+1)) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay (i+1) 0) ∧
      t.getMem (BitVec.ofNat 64 (sb+16*i))=s.getMem (BitVec.ofNat 64 (buffer lay i d)) ∧
      t.getMem (BitVec.ofNat 64 (sb+16*i+8))=s.getMem (BitVec.ofNat 64 (buffer lay i d+8)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => A=sb+16*i ∨ A=sb+16*i+8) := by
  have ho : Oblig.all s step.res.st.obl := by
    simp only [step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    omega
  refine ⟨_,symRun_sound step hc s hp ho,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS,pcOf]
    simp [BitVec.ult,toNat_ofNat_lt (show i+1<2^64 by omega)]
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    try omega
  · simp only [Result.toState_getReg,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    omega
  · simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    rw [if_neg (by omega),if_pos (by omega)]
    simp [Nat.mul_comm]
  · simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    simp [Nat.mul_comm]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,step.res]
    t3n [h6,h21,h22,h23,h24,buffer,DIGITS]
    rw [if_neg (by omega),if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem byte_steps {im : Image} (hc : CodeAt im (pcOf 22435) [0xb4303])
    (s : MachineState) (hp : s.pc=pcOf 22435) (i d : Nat) (hi : i<43) (hd : d<8)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 d) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22436 ∧ t.getReg .x6=BitVec.ofNat 64 d ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hoff : s.getReg .x22+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 (DIGITS+i) := by
    rw [h22]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have st := steps_lbu (rd := .x6) (rs := .x22) (off := 0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by unfold DIGITS; omega)]; simp [MEMORY_BYTES,DIGITS]; omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 22436; rw [hp]; rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn; simp

theorem iteration_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303])
    (s : MachineState) (hp : s.pc=pcOf 22435) (lay i d sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hi : i<43) (hd : d<8)
    (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (h21 : s.getReg .x21=BitVec.ofNat 64 i)
    (h22 : s.getReg .x22=BitVec.ofNat 64 (DIGITS+i))
    (h23 : s.getReg .x23=BitVec.ofNat 64 (sb+16*i))
    (h24 : s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS+i))=BitVec.ofNat 8 d)
    (v : Digest) (hv : DigAt s (buffer lay i d) v) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=(if i+1<43 then pcOf 22435 else pcOf 22448) ∧
      t.getReg .x21=BitVec.ofNat 64 (i+1) ∧ t.getReg .x22=BitVec.ofNat 64 (DIGITS+i+1) ∧
      t.getReg .x23=BitVec.ofNat 64 (sb+16*(i+1)) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay (i+1) 0) ∧
      DigAt t (sb+16*i) v ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => A=sb+16*i ∨ A=sb+16*i+8) := by
  obtain ⟨a,sa,ap,a6,ar,af⟩ := byte_steps hbcode s hp i d hi hd h22 hb
  obtain ⟨t,aToT,tp,t21,t22,t23,t24,tl,tr,ts,tf⟩ := step_steps hc a ap lay i d sb hl hh hi hd hsb hsb' hsb8
    a6 ((ar.get (by decide)).trans h21) ((ar.get (by decide)).trans h22)
    ((ar.get (by decide)).trans h23) ((ar.get (by decide)).trans h24)
  have va := hv.frame af (by unfold buffer; omega) (fun h => h) (fun h => h)
  exact ⟨t,sa.trans aToT,tp,t21,t22,t23,t24,⟨tl.trans va.1,tr.trans va.2⟩,
    (ar.trans ts).mono (by simp),(af.trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem loop_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (lay sb : Nat)
    (hl : 1≤lay) (hh : lay≤3) (hsb : 0x7000 ≤ sb) (hsb' : sb+16*43≤0x9000) (hsb8 : sb%8=0)
    (digits : Nat→Nat) (prefixes : Nat→Nat→Digest) (hd : ∀ j,j<43 → digits j<8) :
    ∀ count i, i+count=43 → ∀ s : MachineState,
      s.pc=(if i<43 then pcOf 22435 else pcOf 22448) →
      s.getReg .x21=BitVec.ofNat 64 i → s.getReg .x22=BitVec.ofNat 64 (DIGITS+i) →
      s.getReg .x23=BitVec.ofNat 64 (sb+16*i) →
      s.getReg .x24=BitVec.ofNat 64 (buffer lay i 0) →
      (∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits j)) →
      (∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay j d) (prefixes j d)) →
      ∃ t, Steps im s (13*count) (13*count) t ∧ t.pc=pcOf 22448 ∧
        (∀ j,i≤j → j<43 → DigAt t (sb+16*j) (prefixes j (digits j))) ∧
        RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
        Frame s t (fun A => sb+16*i≤A ∧ A<sb+16*43) := by
  intro count
  induction count with
  | zero =>
      intro i hi s hp h21 h22 h23 h24 hb hv
      have hi' : i=43 := by omega
      refine ⟨s,Steps.refl _,by simpa [hi'] using hp,?_,?_,?_⟩
      · intro j hj hj'; omega
      · intro r hr; rfl
      · intro A hA hn; rfl
  | succ count ih =>
      intro i hcount s hp h21 h22 h23 h24 hb hv
      have hi : i<43 := by omega
      obtain ⟨a,sa,ap,a21,a22,a23,a24,av,ar,af⟩ := iteration_steps hc hbcode s
        (by simpa [hi] using hp) lay i (digits i) sb hl hh hi (hd i hi) hsb hsb' hsb8
        h21 h22 h23 h24 (hb i hi) (prefixes i (digits i)) (hv i hi _ (hd i hi))
      obtain ⟨t,aToT,tp,tv,tr,tf⟩ := ih (i+1) (by omega) a ap a21
        (by simpa [Nat.add_assoc] using a22) a23 a24
        (by
          intro j hj
          rw [af.getByte (by unfold DIGITS; omega) (by unfold DIGITS; omega)]
          exact hb j hj)
        (by
          intro j hj d hd
          exact (hv j hj d hd).frame af (by unfold buffer; omega)
            (by unfold buffer; omega) (by unfold buffer; omega))
      refine ⟨t,?_,tp,?_,(ar.trans tr).mono (by simp),?_⟩
      · convert sa.trans aToT using 1 <;> omega
      · intro j hij hj
        by_cases he : j=i
        · subst j
          exact av.frame tf (by omega) (by omega) (by omega)
        · exact tv j (by omega) hj
      · exact (af.trans tf).mono (by intro A hA h; rcases h with h|h <;> omega)
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def metaAddr (lay : Layer) : Nat := 0x66000+64+32*(lay.val-1)
def metaW (lay : Layer) (A : Nat) : Prop := metaAddr lay≤A ∧ A < metaAddr lay+32
structure Stored (lay : Layer) (index : Nat) (p : PreparedLower) (t : MachineState) : Prop where
  plen : p.prefixes.length=43
  saved : ∀ i,i<43 → ∀ k,k≤7 → DigAt t (SharedPrefixes.buffer lay.val i k) ((p.prefixes.getD i []).getD k 0)
  path : DigsAt t (sigBase lay.val+16*43) ((List.range (height lay)).map fun j => (p.levels.getD j []).getD ((route index lay).1/2^j ^^^ 1) 0)
  left : DigAt t (metaAddr lay) (topPair lay p.levels).1
  right : DigAt t (metaAddr lay+16) (topPair lay p.levels).2
structure OnePost (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (index : Nat)
    (s : MachineState) (p : PreparedLower) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=(if lay.val<3 then pcOf 22128 else pcOf 22182)
  layer : t.getReg .x8=BitVec.ofNat 64 (lay.val+1)
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  zero : ∀ i,i<43 → t.getByte (BitVec.ofNat 64 (DIGITS+i))=0
  stored : Stored lay index p t
  frame : Frame s t (fun A => SharedLowTree.AllW lay (route index lay).2 (sigBase lay.val) A ∨ metaW lay A)
  precise : Frame s t (fun A => SharedLowTree.TreeWrites lay A ∨ metaW lay A)

theorem one_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hlay : lay≠0) {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (btCost+47) (buildTreePrefixes lay (route index lay).2 (route index lay).1)
      (OnePost (cfFlag := cfFlag) sk cache lay index s) := by
  have h0 : lay.val≠0 := fun h => hlay (Fin.ext h)
  have hl := lay.isLt
  obtain ⟨a,k,sa,hk,ha⟩ := setup hc s hpc lay hlay index hi h8 hidx
  have hpre := ha.btPre hlay hi h8 hb hz
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (ha.frame.get (by decide) (fun h => h)).trans hidx
  have hsel : SharedPrefixes.selectionWord (a.getMem 0x20550) lay.val=BitVec.ofNat 64 (route index lay).1 := by
    rw [aidx]; exact SharedPrefixes.selection_route index hi lay hlay
  have ht := SharedLowTree.buildTreePrefixes_tbsim hlow hlevels hsub hcopy hchain hpref hseed hhook
    hpre ha.pc ha.ret hsel
  refine TBSim.mono (TBSim.steps sa (TBSim.post_steps (k := 18) (c := 18) ht (fun p u hu => ?_))) (by omega) (fun _ _ h => h)
  have u8 : u.getReg .x8=BitVec.ofNat 64 lay.val := (hu.regs.get (by decide)).trans hpre.x8
  obtain ⟨t,ut,pt,t8,tl,tr,trs,tf⟩ := done_steps he u hu.pc lay.val (by omega) (by omega) u8
    (topPair lay p.levels).1 (topPair lay p.levels).2 hu.left hu.right
  have tf' : Frame u t (metaW lay) := tf.mono (by unfold metaW metaAddr; intros A hA h; omega)
  have fm : Frame s t (fun A => SharedLowTree.AllW lay (route index lay).2 (sigBase lay.val) A ∨ metaW lay A) :=
    ((ha.frame.trans hu.frame).trans tf').mono (by intros A hA h; rcases h with (h|h)|h <;> tauto)
  refine ⟨t,ut,pt,t8,?_,?_,?_,?_,fm,?_⟩
  · exact hu.base.frame tf' trs (by decide) (by
      intro A hA hb hw
      unfold BaseA NeverW at hb
      unfold metaW metaAddr at hw
      simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA] at hb
      omega)
  · change t.getMem (BitVec.ofNat 64 0x20550)=BitVec.ofNat 64 index
    rw [fm.get (A := 0x20550) (by decide) ?_]; exact hidx
    unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
    fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT]
  · intro i hI
    rw [fm.getByte (by unfold DIGITS; omega) ?_]; exact hz i hI
    unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
    fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT,DIGITS] <;> omega
  · refine ⟨hu.plen,?_,?_,?_,?_⟩
    · intro i hI j hj
      have hbound := SharedPrefixes.buffer_bounds (by omega : 1≤lay.val) (by omega : lay.val≤3) hI (by omega : j<8)
      exact (hu.saved i hI j hj).frame tf' (by omega) (by unfold metaW metaAddr; omega) (by unfold metaW metaAddr; omega)
    · refine hu.path.frame tf' ?_ ?_
      · simp only [List.length_map,List.length_range]; fin_cases lay <;> decide
      · intro A hA hA'
        simp only [List.length_map,List.length_range] at hA'
        unfold metaW metaAddr
        fin_cases lay <;> simp_all [sigBase,height] <;> omega
    · exact tl
    · convert tr using 1 <;> unfold metaAddr <;> omega
  · exact ((ha.frame.trans hu.precise).trans tf').mono (by intros A hA h; rcases h with (h|h)|h <;> tauto)
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def setupACode : List (BitVec 32) := bv_list% 32 [0xa93,0x20b37,0x420b0b13,0x8bb7,0xcb0b8b93,0xfff40313,0x30e63]
sym_block setupA := symRun { noAlias := true } setupACode (pcOf 22418) 100
def setupBCode : List (BitVec 32) := bv_list% 32 [0x8bb7,0xfd0b8b93,0xffe40313,0x30663]
sym_block setupB := symRun { noAlias := true } setupBCode (pcOf 22425) 100
def setupCCode : List (BitVec 32) := bv_list% 32 [0x8bb7,0x2e0b8b93]
sym_block setupC := symRun { noAlias := true } setupCCode (pcOf 22429) 100
def setupDCode : List (BitVec 32) := bv_list% 32 [0x6ec37,0xc0c13,0xd41313,0x6c0c33]
sym_block setupD := symRun { noAlias := true } setupDCode (pcOf 22431) 100
def sigBase (lay : Nat) : Nat := if lay=1 then 0x7cb0 else if lay=2 then 0x7fd0 else 0x82e0
structure SetupCode (im : Image) : Prop where
  a : CodeAt im (pcOf 22418) setupACode
  b : CodeAt im (pcOf 22425) setupBCode
  c : CodeAt im (pcOf 22429) setupCCode
  d : CodeAt im (pcOf 22431) setupDCode
theorem setupA_steps {im : Image} (hc : CodeAt im (pcOf 22418) setupACode)
    (s : MachineState) (hp : s.pc=pcOf 22418) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 7 7 t ∧ t.pc=(if lay=1 then pcOf 22431 else pcOf 22425) ∧ t.getReg .x21=0 ∧ t.getReg .x22=BitVec.ofNat 64 DIGITS ∧ t.getReg .x23=BitVec.ofNat 64 0x7cb0 ∧ RegsExcept s t [.x6,.x21,.x22,.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupA hc s hp (by simp [setupA.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupA.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupA.res,rv_simp]
theorem setupB_steps {im : Image} (hc : CodeAt im (pcOf 22425) setupBCode)
    (s : MachineState) (hp : s.pc=pcOf 22425) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=(if lay=2 then pcOf 22431 else pcOf 22429) ∧ t.getReg .x23=BitVec.ofNat 64 0x7fd0 ∧ RegsExcept s t [.x6,.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupB hc s hp (by simp [setupB.res,rv_simp]),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupB.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupB.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupB.res,rv_simp]
theorem setupC_steps {im : Image} (hc : CodeAt im (pcOf 22429) setupCCode)
    (s : MachineState) (hp : s.pc=pcOf 22429)  :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22431 ∧ t.getReg .x23=BitVec.ofNat 64 0x82e0 ∧ RegsExcept s t [.x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupC hc s hp (by simp [setupC.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [setupC.res,rv_simp]
  · simp [setupC.res,rv_simp]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupC.res,rv_simp]
theorem setupD_steps {im : Image} (hc : CodeAt im (pcOf 22431) setupDCode)
    (s : MachineState) (hp : s.pc=pcOf 22431) (lay : Nat) (hl : 1≤lay) (hh : lay≤3) (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf 22435 ∧ t.getReg .x24=BitVec.ofNat 64 (buffer lay 0 0) ∧ RegsExcept s t [.x6,.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound setupD hc s hp (by simp [setupD.res,rv_simp]),?_,?_,?_,?_⟩
  · interval_cases lay <;> simp_all [setupD.res,rv_simp,DIGITS,buffer]
  · interval_cases lay <;> simp_all [setupD.res,rv_simp,DIGITS,buffer]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; simp [setupD.res,rv_simp]
theorem setup_steps {im : Image} (hc : SetupCode im)
    (s : MachineState) (hp : s.pc=pcOf 22418) (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t k, Steps im s k k t ∧ k≤17 ∧ t.pc=pcOf 22435 ∧ t.getReg .x21=0 ∧
      t.getReg .x22=BitVec.ofNat 64 DIGITS ∧ t.getReg .x23=BitVec.ofNat 64 (sigBase lay) ∧
      t.getReg .x24=BitVec.ofNat 64 (buffer lay 0 0) ∧
      RegsExcept s t [.x6,.x21,.x22,.x23,.x24] ∧ Frame s t (fun _ => False) := by
  obtain ⟨a,sa,ap,a21,a22,a23,ar,af⟩ := setupA_steps hc.a s hp lay hl hh h8
  have a8 := (ar.get (by decide)).trans h8
  interval_cases lay
  · obtain ⟨t,at',tp,t24,tr,tf⟩ := setupD_steps hc.d a (by simpa using ap) 1 (by decide) (by decide) a8
    exact ⟨t,11,sa.trans at',by decide,tp,(tr.get (by decide)).trans a21,(tr.get (by decide)).trans a22,
      (tr.get (by decide)).trans a23,t24,(ar.trans tr).mono (by simp),(af.trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b23,br,bf⟩ := setupB_steps hc.b a (by simpa using ap) 2 (by decide) (by decide) a8
    obtain ⟨t,bt,tp,t24,tr,tf⟩ := setupD_steps hc.d b (by simpa using bp) 2 (by decide) (by decide) ((br.get (by decide)).trans a8)
    exact ⟨t,15,sa.trans (ab.trans bt),by decide,tp,
      (tr.get (by decide)).trans ((br.get (by decide)).trans a21),
      (tr.get (by decide)).trans ((br.get (by decide)).trans a22),
      (tr.get (by decide)).trans b23,t24,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b23,br,bf⟩ := setupB_steps hc.b a (by simpa using ap) 3 (by decide) (by decide) a8
    obtain ⟨c,bc,cp,c23,cr,cf⟩ := setupC_steps hc.c b (by simpa using bp)
    obtain ⟨t,ct,tp,t24,tr,tf⟩ := setupD_steps hc.d c cp 3 (by decide) (by decide)
      ((cr.get (by decide)).trans ((br.get (by decide)).trans a8))
    exact ⟨t,17,sa.trans (ab.trans (bc.trans ct)),by decide,tp,
      (tr.get (by decide)).trans ((cr.get (by decide)).trans ((br.get (by decide)).trans a21)),
      (tr.get (by decide)).trans ((cr.get (by decide)).trans ((br.get (by decide)).trans a22)),
      (tr.get (by decide)).trans c23,t24,(((ar.trans br).trans cr).trans tr).mono (by simp),
      (((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem reveal_steps {im : Image} (hc : CodeAt im (pcOf 22436) stepCode)
    (hbcode : CodeAt im (pcOf 22435) [0xb4303]) (hsetup : SetupCode im)
    (lay : Nat) (hl : 1≤lay) (hh : lay≤3)
    (digits : Nat→Nat) (prefixes : Nat→Nat→Digest) (hd : ∀ j,j<43 → digits j<8)
    (s : MachineState) (hp : s.pc=pcOf 22418) (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hb : ∀ j,j<43 → s.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (digits j))
    (hv : ∀ j,j<43 → ∀ d,d<8 → DigAt s (buffer lay j d) (prefixes j d)) :
    ∃ t k, Steps im s k k t ∧ k≤576 ∧ t.pc=pcOf 22448 ∧
      DigsAt t (sigBase lay) ((List.range 43).map fun i => prefixes i (digits i)) ∧
      RegsExcept s t [.x6,.x7,.x21,.x22,.x23,.x24,.x28] ∧
      Frame s t (fun A => sigBase lay≤A ∧ A<sigBase lay+688) := by
  obtain ⟨a,k,sa,hk,ap,a21,a22,a23,a24,ar,af⟩ := setup_steps hsetup s hp lay hl hh h8
  obtain ⟨t,aToT,tp,tv,tr,tf⟩ := loop_steps hc hbcode lay (sigBase lay) hl hh
    (by interval_cases lay <;> decide) (by interval_cases lay <;> decide) (by interval_cases lay <;> decide)
    digits prefixes hd 43 0 (by decide) a (by simpa using ap) a21
    (by simpa using a22) (by simpa using a23) a24
    (by intro j hj; rw [af.getByte (by unfold DIGITS; omega) (fun h => h)]; exact hb j hj)
    (by intro j hj d hd; exact (hv j hj d hd).frame af (by unfold buffer; omega) (fun h => h) (fun h => h))
  refine ⟨t,k+559,sa.trans aToT,by omega,tp,?_,(ar.trans tr).mono (by simp),?_⟩
  · intro i hi
    have hi' : i<43 := by simpa using hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map,List.getElem_range]
    exact tv i (by omega) hi'
  · exact (af.trans tf).mono (by intro A hA h; rcases h with h|h; exact h.elim; simpa using h)
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedReveal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_setupCode : SetupCode Images.signImage := by
  constructor
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_byteCode : CodeAt Images.signImage (pcOf 22435) [0xb4303] := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_stepCode : CodeAt Images.signImage (pcOf 22436) stepCode := by
  apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedReveal

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem Stored.after {sk : SecretKey} {cache : Bytes 131072} {index : Nat} {lay other : Layer}
    (hl : lay≠0) (ho : other≠0) (hne : lay≠other) {s t : MachineState} {p q : PreparedLower}
    (h : Stored other index p s) (ht : OnePost (cfFlag := cfFlag) sk cache lay index s q t) : Stored other index p t := by
  have hl0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have ho0 : other.val≠0 := fun h => ho (Fin.ext h)
  have hlb := lay.isLt
  have hob := other.isLt
  refine ⟨h.plen,?_,?_,?_,?_⟩
  · intro i hi k hk
    have b := SharedPrefixes.buffer_bounds (by omega : 1≤other.val) (by omega : other.val≤3) hi (by omega : k<8)
    refine (h.saved i hi k hk).frame ht.precise (by omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_other_prefix lay other hne ho (i := i) (k := k) hi (by omega) 0 (by decide) (by simpa using ha)
      · unfold metaW metaAddr at ha; omega
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_other_prefix lay other hne ho (i := i) (k := k) hi (by omega) 1 (by decide) (by simpa using ha)
      · unfold metaW metaAddr at ha; omega
  · refine h.path.frame ht.frame ?_ ?_
    · simp only [List.length_map,List.length_range]; fin_cases other <;> decide
    · intro A ha hw
      simp only [List.length_map,List.length_range] at hw
      unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
      fin_cases lay <;> fin_cases other <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT] <;> omega
  · refine h.left.frame ht.precise (by unfold metaAddr; omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
  · refine h.right.frame ht.precise (by unfold metaAddr; omega) ?_ ?_
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
    · rintro (ha|ha)
      · exact SharedLowTree.TreeWrites.not_metadata lay hl (by unfold metaAddr; omega) (by unfold metaAddr; omega) ha
      · unfold metaW metaAddr at ha
        fin_cases lay <;> fin_cases other <;> simp_all
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def RootsWrites (A : Nat) : Prop := A < 0x66000 ∨ (0x66040≤A ∧ A<0x660a0) ∨ (0x70000≤A ∧ A<0x76000)
structure RootsPost (sk : SecretKey) (cache : Bytes 131072) (index : Nat)
    (s : MachineState) (p : PreparedRoots) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=pcOf 22182
  layer : t.getReg .x8=4
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  one : Stored 1 index p.one t
  two : Stored 2 index p.two t
  three : Stored 3 index p.three t
  frame : Frame s t RootsWrites
  counterMem : t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32))

theorem OnePost.counterMem {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower}
    (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) :
    t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32)) := by
  apply h.frame.get (by unfold ENC; decide)
  unfold SharedLowTree.AllW SharedLowTree.BtW SharedLowTree.BScr LevW btLev metaW metaAddr
  fin_cases lay <;> simp_all [sigBase,height,LOW,PRIV,SEEDS,CHAIN,LEAFPK,LOUT,DUMMY,ENC,NODE,NOUT] <;> omega

theorem OnePost.rootsFrame {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} (hl : lay≠0)
    {index : Nat} {s t : MachineState} {p : PreparedLower} (h : OnePost (cfFlag := cfFlag) sk cache lay index s p t) :
    Frame s t RootsWrites := by
  have h0 : lay.val≠0 := fun h => hl (Fin.ext h)
  have hbound := lay.isLt
  exact h.precise.mono (by unfold SharedLowTree.TreeWrites metaW metaAddr RootsWrites; intros A hA h; omega)

theorem prepareRoots_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) (s : MachineState) (hpc : s.pc=pcOf 22128)
    (h8 : s.getReg .x8=1) (hidx : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hb : Base (cfFlag := cfFlag) sk cache s) (hz : ∀ i,i<43 → s.getByte (BitVec.ofNat 64 (DIGITS+i))=0) :
    TBSim im sk s (3*(btCost+47)) (prepareRoots index) (RootsPost (cfFlag := cfFlag) sk cache index s) := by
  have r1 := one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    (lay := 1) (by decide) hi s hpc h8 hidx hb hz
  unfold prepareRoots
  refine TBSim.mono (TBSim.bind r1 (fun p1 t1 h1 =>
    TBSim.bind (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
      (lay := 2) (by decide) hi t1 (by simpa using h1.pc) h1.layer h1.indexMem h1.base h1.zero)
      (fun p2 t2 h2 => TBSim.bind
        (one_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
          (lay := 3) (by decide) hi t2 (by simpa using h2.pc) h2.layer h2.indexMem h2.base h2.zero)
        (fun p3 t3 h3 => TBSim.pure ?_)))) (by omega) (fun _ _ h => h)
  refine ⟨by simpa using h3.pc,by simpa using h3.layer,h3.base,h3.indexMem,?_,?_,h3.stored,?_,?_⟩
  · exact (h1.stored.after (by decide) (by decide) (by decide) h2).after
      (by decide) (by decide) (by decide) h3
  · exact h2.stored.after (by decide) (by decide) (by decide) h3
  · exact (((h1.rootsFrame (by decide)).trans (h2.rootsFrame (by decide))).trans
      (h3.rootsFrame (by decide))).mono (by intro A hA h; rcases h with (h|h)|h <;> exact h)
  · exact (h3.counterMem (by decide)).trans ((h2.counterMem (by decide)).trans (h1.counterMem (by decide)))
end SigGolfCandidate.T3M.Sign.SharedRootControl

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def introCode : List (BitVec 32) := bv_list% 32 [0x413,0x493,0xc00793,0x3600d13,0x3300d93,0x9200893,0x20e37,0x550e0e13,0xe3903,0x1395913,0x90713,0x66eb7,0x40e8e93,0x541393,0x7e8eb3,0x20e37,0x260e0e13]
sym_block introBlock := symRun { noAlias := true } introCode (pcOf 22182) 100
def copyCode : List (BitVec 32) := bv_list% 32 [0xeb303,0x8eb383,0x6e3023,0x7e3423,0x10eb303,0x18eb383,0x26e3823,0x27e3c23,0xf1dea0ef]
sym_block copyBlock := symRun { noAlias := true } copyCode (pcOf 22199) 100
structure IntroPost (index : Nat) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 22199
  x8 : t.getReg .x8=0
  x9 : t.getReg .x9=0
  x14 : t.getReg .x14=BitVec.ofNat 64 (index/2^19)
  x15 : t.getReg .x15=12
  x17 : t.getReg .x17=146
  x18 : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  x26 : t.getReg .x26=54
  x27 : t.getReg .x27=51
  x28 : t.getReg .x28=BitVec.ofNat 64 ENC
  x29 : t.getReg .x29=BitVec.ofNat 64 0x66040
  regs : RegsExcept s t [.x7,.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun _ => False)
theorem intro_steps {im : Image} (hc : CodeAt im (pcOf 22182) introCode)
    (s : MachineState) (hp : s.pc=pcOf 22182) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps im s 17 17 t ∧ IntroPost index s t := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hidx
  refine ⟨_,symRun_sound introBlock hc s hp (by simp [introBlock.res,rv_simp]),?_⟩
  constructor
  all_goals first
    | solve | (simp only [Result.toState_getReg,introBlock.res]; t3n [hidx,ENC])
    | solve | (simp [introBlock.res,rv_simp])
    | solve | (intro r hr; cases r <;> simp at hr <;> rfl)
    | solve | (intro A hA hn; simp [introBlock.res,rv_simp])
    | (simp only [Result.toState_getReg,introBlock.res]; t3n [hidx,ENC];
       apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight,toNat_ofNat_lt (show index<2^64 by omega),Nat.shiftRight_eq_div_pow]; omega)

theorem copy_steps {im : Image} (hc : CodeAt im (pcOf 22199) copyCode)
    (s : MachineState) (hp : s.pc=pcOf 22199)
    (h28 : s.getReg .x28=BitVec.ofNat 64 ENC) (h29 : s.getReg .x29=BitVec.ofNat 64 0x66040)
    (left right : Digest) (hl : DigAt s 0x66040 left) (hr : DigAt s 0x66050 right) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 646 ∧ t.getReg .x1=pcOf 22208 ∧
      DigAt t ENC left ∧ DigAt t (ENC+48) right ∧
      RegsExcept s t [.x1,.x6,.x7] ∧
      Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56) := by
  have ho : Oblig.all s copyBlock.res.st.obl := by
    simp [copyBlock.res,rv_simp,h28,h29,ENC]
    decide
  refine ⟨_,symRun_sound copyBlock hc s hp ho,?_,?_,?_,?_,?_,?_⟩
  · simp [copyBlock.res,rv_simp]
  · simp [copyBlock.res,rv_simp,pcOf]
  · constructor
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hl.1
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hl.2
  · constructor
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hr.1
    · simp only [Result.toState_getMem,copyBlock.res]; t3n [h28,h29,ENC]; exact hr.2
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,copyBlock.res]
    t3n [h28,h29,ENC]
    unfold ENC at hn
    repeat rw [if_neg (by omega)]
end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Code (im : Image) : Prop where
  intro : CodeAt im (pcOf 22182) introCode
  copy : CodeAt im (pcOf 22199) copyCode
structure Post (index : Nat) (left right : Digest) (s t : MachineState) : Prop where
  pc : t.pc=pcOf 646
  ret : t.getReg .x1=pcOf 22208
  x8 : t.getReg .x8=0
  x9 : t.getReg .x9=0
  x14 : t.getReg .x14=BitVec.ofNat 64 (index/2^19)
  x15 : t.getReg .x15=12
  x17 : t.getReg .x17=146
  x18 : t.getReg .x18=BitVec.ofNat 64 (index/2^19)
  x26 : t.getReg .x26=54
  x27 : t.getReg .x27=51
  left : DigAt t ENC left
  right : DigAt t (ENC+48) right
  regs : RegsExcept s t [.x1,.x6,.x7,.x8,.x9,.x14,.x15,.x17,.x18,.x26,.x27,.x28,.x29]
  frame : Frame s t (fun A => A=ENC ∨ A=ENC+8 ∨ A=ENC+48 ∨ A=ENC+56)
theorem steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 22182) (index : Nat) (hi : index<2^31)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (left right : Digest)
    (hl : DigAt s 0x66040 left) (hr : DigAt s 0x66050 right) :
    ∃ t, Steps im s 26 26 t ∧ Post index left right s t := by
  obtain ⟨a,sa,ha⟩ := intro_steps hc.intro s hp index hi hidx
  obtain ⟨t,at',tp,tret,tl,tr,trs,tf⟩ := copy_steps hc.copy a ha.pc ha.x28 ha.x29 left right
    (hl.frame ha.frame (by decide) (fun h => h) (fun h => h))
    (hr.frame ha.frame (by decide) (fun h => h) (fun h => h))
  refine ⟨t,sa.trans at',tp,tret,?_,?_,?_,?_,?_,?_,?_,?_,tl,tr,?_,?_⟩
  · exact (trs.get (by decide)).trans ha.x8
  · exact (trs.get (by decide)).trans ha.x9
  · exact (trs.get (by decide)).trans ha.x14
  · exact (trs.get (by decide)).trans ha.x15
  · exact (trs.get (by decide)).trans ha.x17
  · exact (trs.get (by decide)).trans ha.x18
  · exact (trs.get (by decide)).trans ha.x26
  · exact (trs.get (by decide)).trans ha.x27
  · exact (ha.regs.trans trs).mono (by simp)
  · exact (ha.frame.trans tf).mono (by tauto)
end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedTopSetup
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_code : Code Images.signImage := by
  constructor
  · apply codeAt_sign_current_slice <;> decide +kernel
  · apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedTopSetup

namespace SigGolfCandidate.T3M.Sign.SharedResidual
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def read22230Code : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3303,0x18e3383,0x63e663]
sym_block read22230 := symRun { noAlias := true } read22230Code (pcOf 22230) 100
def zero22230Code : List (BitVec 32) := bv_list% 32 [0x313,0x80006f]
sym_block zero22230 := symRun { noAlias := true } zero22230Code (pcOf 22235) 100
def sub22230Code : List (BitVec 32) := bv_list% 32 [0x40730333]
sym_block sub22230 := symRun { noAlias := true } sub22230Code (pcOf 22237) 100
def store22230Code : List (BitVec 32) := bv_list% 32 [0x6e3423]
sym_block store22230 := symRun { noAlias := true } store22230Code (pcOf 22238) 100
structure Code22230 (im : Image) : Prop where
  read : CodeAt im (pcOf 22230) read22230Code
  zero : CodeAt im (pcOf 22235) zero22230Code
  sub : CodeAt im (pcOf 22237) sub22230Code
  store : CodeAt im (pcOf 22238) store22230Code

theorem read22230_steps {im : Image} (hc : CodeAt im (pcOf 22230) read22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22230) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 5 5 t ∧ t.pc=(if c<r then pcOf 22237 else pcOf 22235) ∧
      t.getReg .x6=BitVec.ofNat 64 r ∧ t.getReg .x7=BitVec.ofNat 64 c ∧ t.getReg .x28=BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound read22230 hc s hp (by simp [read22230.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [read22230.res,rv_simp,hrm,hcm,pcOf,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),toNat_ofNat_lt (show c<2^64 by omega)]
  · simp [read22230.res,rv_simp,hrm]
  · simp [read22230.res,rv_simp,hcm]
  · simp [read22230.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [read22230.res,rv_simp]

theorem zero22230_steps {im : Image} (hc : CodeAt im (pcOf 22235) zero22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22235) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22238 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound zero22230 hc s hp (by simp [zero22230.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero22230.res,rv_simp]
  · simp [zero22230.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [zero22230.res,rv_simp]

theorem sub22230_steps {im : Image} (hc : CodeAt im (pcOf 22237) sub22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22237) (r c : Nat) (hr : r<2^32) (hc' : c≤r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22238 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound sub22230 hc s hp (by simp [sub22230.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [sub22230.res,rv_simp]
  · simp only [Result.toState_getReg,sub22230.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [sub22230.res,rv_simp]

theorem store22230_steps {im : Image} (hc : CodeAt im (pcOf 22238) store22230Code)
    (s : MachineState) (hp : s.pc=pcOf 22238) (v : BitVec 64)
    (h6 : s.getReg .x6=v) (h28 : s.getReg .x28=BitVec.ofNat 64 0x66000) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22239 ∧ t.getMem (0x66008#64)=v ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound store22230 hc s hp (by simp [store22230.res,rv_simp,h28]; decide),?_,?_,?_,?_⟩
  · simp [store22230.res,rv_simp]
  · simp [store22230.res,rv_simp,h6,h28]
  · intro q hq; cases q <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,store22230.res]; t3n [h28]
    rw [if_neg (by omega)]

theorem residual22230_steps {im : Image} (hc : Code22230 im)
    (s : MachineState) (hp : s.pc=pcOf 22230) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t k, Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22239 ∧ t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  obtain ⟨a,sa,ap,a6,a7,a28,ar,af⟩ := read22230_steps hc.read s hp r c hr hc' hrm hcm
  by_cases hcr : c<r
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := sub22230_steps hc.sub a (by simpa [hcr] using ap) r c hr (by omega) a6 a7
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22230_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,7,sa.trans (ab.trans bt),by decide,tp,tv,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := zero22230_steps hc.zero a (by simpa [hcr] using ap)
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22230_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,8,sa.trans (ab.trans bt),by decide,tp,by simpa [Nat.sub_eq_zero_of_le (by omega : r≤c)] using tv,
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
def read22448Code : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3303,0x18e3383,0x63e663]
sym_block read22448 := symRun { noAlias := true } read22448Code (pcOf 22448) 100
def zero22448Code : List (BitVec 32) := bv_list% 32 [0x313,0x80006f]
sym_block zero22448 := symRun { noAlias := true } zero22448Code (pcOf 22453) 100
def sub22448Code : List (BitVec 32) := bv_list% 32 [0x40730333]
sym_block sub22448 := symRun { noAlias := true } sub22448Code (pcOf 22455) 100
def store22448Code : List (BitVec 32) := bv_list% 32 [0x6e3423]
sym_block store22448 := symRun { noAlias := true } store22448Code (pcOf 22456) 100
structure Code22448 (im : Image) : Prop where
  read : CodeAt im (pcOf 22448) read22448Code
  zero : CodeAt im (pcOf 22453) zero22448Code
  sub : CodeAt im (pcOf 22455) sub22448Code
  store : CodeAt im (pcOf 22456) store22448Code

theorem read22448_steps {im : Image} (hc : CodeAt im (pcOf 22448) read22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22448) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 5 5 t ∧ t.pc=(if c<r then pcOf 22455 else pcOf 22453) ∧
      t.getReg .x6=BitVec.ofNat 64 r ∧ t.getReg .x7=BitVec.ofNat 64 c ∧ t.getReg .x28=BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound read22448 hc s hp (by simp [read22448.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [read22448.res,rv_simp,hrm,hcm,pcOf,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),toNat_ofNat_lt (show c<2^64 by omega)]
  · simp [read22448.res,rv_simp,hrm]
  · simp [read22448.res,rv_simp,hcm]
  · simp [read22448.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [read22448.res,rv_simp]

theorem zero22448_steps {im : Image} (hc : CodeAt im (pcOf 22453) zero22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22453) :
    ∃ t, Steps im s 2 2 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound zero22448 hc s hp (by simp [zero22448.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [zero22448.res,rv_simp]
  · simp [zero22448.res,rv_simp]
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [zero22448.res,rv_simp]

theorem sub22448_steps {im : Image} (hc : CodeAt im (pcOf 22455) sub22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22455) (r c : Nat) (hr : r<2^32) (hc' : c≤r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound sub22448 hc s hp (by simp [sub22448.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [sub22448.res,rv_simp]
  · simp only [Result.toState_getReg,sub22448.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; simp [sub22448.res,rv_simp]

theorem store22448_steps {im : Image} (hc : CodeAt im (pcOf 22456) store22448Code)
    (s : MachineState) (hp : s.pc=pcOf 22456) (v : BitVec 64)
    (h6 : s.getReg .x6=v) (h28 : s.getReg .x28=BitVec.ofNat 64 0x66000) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 22457 ∧ t.getMem (0x66008#64)=v ∧
      RegsExcept s t [] ∧ Frame s t (fun A => A=0x66008) := by
  refine ⟨_,symRun_sound store22448 hc s hp (by simp [store22448.res,rv_simp,h28]; decide),?_,?_,?_,?_⟩
  · simp [store22448.res,rv_simp]
  · simp [store22448.res,rv_simp,h6,h28]
  · intro q hq; cases q <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,store22448.res]; t3n [h28]
    rw [if_neg (by omega)]

theorem residual22448_steps {im : Image} (hc : Code22448 im)
    (s : MachineState) (hp : s.pc=pcOf 22448) (r c : Nat) (hr : r<2^32) (hc' : c<2^32)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) (hcm : s.getMem (0x66018#64)=BitVec.ofNat 64 c) :
    ∃ t k, Steps im s k k t ∧ k≤8 ∧ t.pc=pcOf 22457 ∧ t.getMem (0x66008#64)=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  obtain ⟨a,sa,ap,a6,a7,a28,ar,af⟩ := read22448_steps hc.read s hp r c hr hc' hrm hcm
  by_cases hcr : c<r
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := sub22448_steps hc.sub a (by simpa [hcr] using ap) r c hr (by omega) a6 a7
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22448_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,7,sa.trans (ab.trans bt),by decide,tp,tv,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨b,ab,bp,b6,br,bf⟩ := zero22448_steps hc.zero a (by simpa [hcr] using ap)
    obtain ⟨t,bt,tp,tv,tr,tf⟩ := store22448_steps hc.store b bp _ b6 ((br.get (by decide)).trans a28)
    exact ⟨t,8,sa.trans (ab.trans bt),by decide,tp,by simpa [Nat.sub_eq_zero_of_le (by omega : r≤c)] using tv,
      ((ar.trans br).trans tr).mono (by simp),((af.trans bf).trans tf).mono (by tauto)⟩
end SigGolfCandidate.T3M.Sign.SharedResidual

namespace SigGolfCandidate.T3M.Sign.SharedRootControl
variable {cfFlag : Nat}
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Keygen
open SigGolfCandidate.T3 (Layer Digest route height)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.Machine.Sign
open Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def EntryWrites (A : Nat) : Prop := A=0x66000 ∨ 0x660a0≤A ∧ A<0x660c0 ∨ DIGITS≤A ∧ A<DIGITS+56
structure BuiltPost (sk : SecretKey) (cache : Bytes 131072) (index : Nat) (forest : Digest×Digest)
    (s : MachineState) (p : PreparedRoots) (t : MachineState) (cfFlag : Nat := 1) : Prop where
  pc : t.pc=pcOf 22182
  layer : t.getReg .x8=4
  base : Base (cfFlag := cfFlag) sk cache t
  indexMem : t.getMem 0x20550=BitVec.ofNat 64 index
  one : Stored 1 index p.one t
  two : Stored 2 index p.two t
  three : Stored 3 index p.three t
  hintZero : t.getMem (0x66000#64)=0
  forestL : DigAt t 0x660a0 forest.1
  forestR : DigAt t 0x660b0 forest.2
  frame : Frame s t (fun A => EntryWrites A ∨ RootsWrites A)
  counterMem : t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32))

theorem entry_roots_tbsim {im : Image} (hc : Code im) (he : ExtraCode im)
    (hlow : SharedLowCode.Code im) (hlevels : SharedTreeCode.Code im 1013)
    (hsub : SharedLeafCode.Code im 1013) (hcopy : CodeAt im (pcOf (1013+61)) Seed.sub61)
    (hchain : SharedChain.Code im) (hpref : SharedChain.PrefixCode im)
    (hseed : SharedSeed.Code im) (hhook : CodeAt im (pcOf 1055) seedHookCode)
    {sk : SecretKey} {cache : Bytes 131072} {index : Nat} (hi : index<2^31)
    (forest : Digest×Digest) (s : MachineState) (hpc : s.pc=pcOf 22100)
    (hidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hb : Base (cfFlag := cfFlag) sk cache s)
    (hl : DigAt s ENC forest.1) (hr : DigAt s (ENC+48) forest.2) :
    TBSim im sk s (28+3*(btCost+47)) (prepareRoots index) (BuiltPost (cfFlag := cfFlag) sk cache index forest s) := by
  obtain ⟨a,sa,ap,a8,al,ar,az,ad,ars,af⟩ := entry_steps he s hpc forest.1 forest.2 hl hr
  have af' : Frame s a EntryWrites := af.mono (by unfold EntryWrites; intros A hA h; exact h)
  have abase : Base (cfFlag := cfFlag) sk cache a := hb.frame af' ars (by decide) (by
    intro A hA hbase hw
    unfold BaseA NeverW at hbase
    unfold EntryWrites at hw
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,NBUF,Search.TOP_DATA,DIGITS] at hbase hw
    omega)
  have aidx : a.getMem 0x20550=BitVec.ofNat 64 index :=
    (af'.get (A := 0x20550) (by decide) (by unfold EntryWrites DIGITS; omega)).trans hidx
  refine (TBSim.steps sa (prepareRoots_tbsim hc he hlow hlevels hsub hcopy hchain hpref hseed hhook
    hi a ap a8 aidx abase ad)).mono (le_refl _) ?_
  intro p t ht
  refine ⟨ht.pc,ht.layer,ht.base,ht.indexMem,ht.one,ht.two,ht.three,?_,?_,?_,af'.trans ht.frame,?_⟩
  · exact (ht.frame.get (A := 0x66000) (by decide) (by unfold RootsWrites; decide)).trans az
  · exact al.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
  · exact ar.frame ht.frame (by decide) (by unfold RootsWrites; decide) (by unfold RootsWrites; decide)
  · exact ht.counterMem.trans (af'.get (A := ENC+32) (by unfold ENC; decide) (by unfold EntryWrites ENC DIGITS; decide))
#print axioms entry_roots_tbsim
end SigGolfCandidate.T3M.Sign.SharedRootControl


namespace SigGolfCandidate.T3M.Sign.SharedTopDigits
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def saveCode : List (BitVec 32) := bv_list% 32 [0x20e37,0x420e0e13,0x66eb7,0x100e8e93,0xe3303,0x6eb023,0x8e3303,0x6eb423,0x10e3303,0x6eb823,0x18e3303,0x6ebc23,0x20e3303,0x26eb023,0x28e3303,0x26eb423,0x30e3303,0x26eb823]
sym_block save := symRun { noAlias := true } saveCode (pcOf 22208) 100
theorem save_steps {im : Image} (hc : CodeAt im (pcOf 22208) saveCode)
    (s : MachineState) (hp : s.pc=pcOf 22208) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22226 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (0x66100+8*i))=s.getMem (BitVec.ofNat 64 (DIGITS+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => 0x66100≤A ∧ A<0x66100+56) := by
  refine ⟨_,symRun_sound save hc s hp (by simp [save.res,rv_simp]; try decide),?_,?_,?_,?_⟩
  · simp [save.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [save.res,rv_simp,DIGITS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,save.res]
    t3n [DIGITS]
    try unfold DIGITS at hn
    repeat rw [if_neg (by omega)]
#print axioms save_steps
def restoreCode : List (BitVec 32) := bv_list% 32 [0x66e37,0x100e0e13,0x20eb7,0x420e8e93,0xe3303,0x6eb023,0x8e3303,0x6eb423,0x10e3303,0x6eb823,0x18e3303,0x6ebc23,0x20e3303,0x26eb023,0x28e3303,0x26eb423,0x30e3303,0x26eb823]
sym_block restore := symRun { noAlias := true } restoreCode (pcOf 22460) 100
theorem restore_steps {im : Image} (hc : CodeAt im (pcOf 22460) restoreCode)
    (s : MachineState) (hp : s.pc=pcOf 22460) :
    ∃ t, Steps im s 18 18 t ∧ t.pc=pcOf 22478 ∧
      (∀ i,i<7 → t.getMem (BitVec.ofNat 64 (DIGITS+8*i))=s.getMem (BitVec.ofNat 64 (0x66100+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => DIGITS≤A ∧ A<DIGITS+56) := by
  refine ⟨_,symRun_sound restore hc s hp (by simp [restore.res,rv_simp]; try decide),?_,?_,?_,?_⟩
  · simp [restore.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [restore.res,rv_simp,DIGITS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,restore.res]
    t3n [DIGITS]
    try unfold DIGITS at hn
    repeat rw [if_neg (by omega)]
#print axioms restore_steps
end SigGolfCandidate.T3M.Sign.SharedTopDigits


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def cst (n : Nat) : E := .c (BitVec.ofNat 64 n)
def rfs (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def thCode : List (BitVec 32) := bv_list% 32 [0xfff40313,0x30e63,0xffe40313,0xc030c63,0x1600313,0x1c6a7263,0xa0e93,0x1c00006f,0x3800313,0x1a6a7a63,0xe93,0x2600313,0x1a6a6663,0x100e93,0x2700313,0x1a6a6063,0x200e93,0x2800313,0x186a6a63,0x300e93,0x2900313,0x186a6463,0x400e93,0x2a00313,0x166a6e63,0x500e93,0x2b00313,0x166a6863,0x600e93,0x2c00313,0x166a6263,0x700e93,0x2d00313,0x146a6c63,0x800e93,0x2f00313,0x146a6663,0x900e93,0x3000313,0x146a6063,0xa00e93,0x3100313,0x126a6a63,0xb00e93,0x3300313,0x126a6463,0xc00e93,0x3400313,0x106a6e63,0xd00e93,0x3600313,0x106a6863,0xe00e93,0x3700313,0x106a6263,0xf00e93,0xfc0006f,0x2900313,0xe6a7863,0xe93,0x1400313,0xe6a6463,0x100e93,0x1500313,0xc6a6e63,0x200e93,0x1600313,0xc6a6863,0x300e93,0x1700313,0xc6a6263,0x400e93,0x1800313,0xa6a6c63,0x500e93,0x1900313,0xa6a6663,0x600e93,0x1a00313,0xa6a6063,0x700e93,0x1b00313,0x86a6a63,0x800e93,0x1c00313,0x86a6463,0x900e93,0x1d00313,0x66a6e63,0xa00e93,0x1e00313,0x66a6863,0xb00e93,0x1f00313,0x66a6263,0xc00e93,0x2100313,0x46a6c63,0xd00e93,0x2200313,0x46a6663,0xe00e93,0x2300313,0x46a6063,0xf00e93,0x2500313,0x26a6a63,0x1000e93,0x2600313,0x26a6463,0x1100e93,0x2700313,0x6a6e63,0x1200e93,0x2800313,0x6a6863,0x1300e93,0x80006f,0x945fd06f,0xf44fd06f]
/-- The img-v6 threshold routine `th` (appended, 24851..24970): `t4 := threshold(s0, s4)`; L1 cascade at 24859
(residual < 56), L2 at 24908 (residual < 41), L3 at 24855 (floor = residual < 22), failure 24969 (`jal 22490`),
result 24970 (`jal 22363`). -/
def lookT (n : Nat) : Option (BitVec 32) := if 24851 ≤ n then thCode[n-24851]? else none
def ends1 : List Nat := [38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 51, 52, 54, 55]
def ends2 : List Nat := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 37, 38, 39, 40]
def dirs (m v : Nat) : List Dir := [.br false] ++ List.replicate v (.br false) ++ (if v < m then [.br true] else [])
def resL (ends : List Nat) (m bound v : Nat) : PRes :=
  ⟨⟨rfs [(.x6,cst (ends.getD (if v < m then v else m-1) 0)),(.x29,cst v)],[],[]⟩,pcOf 22363,false,
    (if v < m then 6+3*v else 5+3*m),(if v < m then 6+3*v else 5+3*m),
    (if v < m then [⟨.ltu,.reg .x20,cst (ends.getD v 0),true⟩] else []) ++
    ((List.range v).reverse.map (fun i => ⟨.ltu,.reg .x20,cst (ends.getD i 0),false⟩)) ++
    [⟨.geu,.reg .x20,cst bound,false⟩],none⟩
theorem checked1 : (List.range 16).all (fun v =>
    optBeq (run lookT [22363] 24859 (dirs 15 v)) (resL ends1 15 56 v)) = true := by decide +kernel
theorem checked2 : (List.range 20).all (fun v =>
    optBeq (run lookT [22363] 24908 (dirs 19 v)) (resL ends2 19 41 v)) = true := by decide +kernel
theorem code_lookT {im : Image} (hc : CodeAt im (pcOf 24851) thCode) : LookOK im lookT := by
  intro n w hw
  unfold lookT at hw
  split at hw
  · rename_i hn
    have hlen := (List.getElem?_eq_some_iff.mp hw).1
    obtain ⟨rest,hrest⟩ := hc.2.2.2
    have hpref : thCode ++ rest = im.code.drop 24851 := by simpa [pcOf] using hrest
    have hget : (im.code.drop 24851)[n-24851]? = some w := by
      rw [← hpref,List.getElem?_append_left hlen]; exact hw
    simpa [List.getElem?_drop,Nat.add_sub_cancel' hn] using hget
  · cases hw
theorem floorL_steps {im : Image} (hc : CodeAt im (pcOf 24851) thCode) (ends : List Nat) (m bound start : Nat)
    (hchk : (List.range (m+1)).all (fun v =>
      optBeq (run lookT [22363] start (dirs m v)) (resL ends m bound v)) = true)
    (hm : 0 < m) (hlen : ends.length=m) (hlt : ∀ i, i < m → ends.getD i 0<2^64) (hb : bound<2^64)
    (s : MachineState) (hp : s.pc=pcOf start) (r v : Nat)
    (hv : v ≤ m) (hr : r<bound)
    (hupper : v < m → r<ends.getD v 0)
    (hlower : ∀ i,i < v → ends.getD i 0≤r)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t k, Steps im s k k t ∧ k≤5+3*m ∧ t.pc=pcOf 22363 ∧
      t.getReg .x29=BitVec.ofNat 64 v ∧ RegsExcept s t [.x6,.x29] ∧ Frame s t (fun _ => False) := by
  have hh := optBeq_eq (List.all_eq_true.mp hchk v (List.mem_range.mpr (by omega)))
  have hob : ∀ o∈(resL ends m bound v).st.obl,o.holds s := by simp [resL]
  have hbr : ∀ b∈(resL ends m bound v).brs,b.holds s := by
    intro b hb
    simp only [resL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with (hb|hb)|rfl
    · split at hb
      · rename_i hvm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        subst hb
        simp only [Br.holds,E.eval,cst,CmpOp.eval,h20]
        have he := hlt v hvm
        simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show r<2^64 by omega),Nat.mod_eq_of_lt he,decide_eq_true_eq]
        exact hupper hvm
      · simp at hb
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
      have hi : i < v := List.mem_range.mp (List.mem_reverse.mp hi)
      have he := hlt i (by omega)
      simp only [Br.holds,E.eval,cst,CmpOp.eval,h20]
      simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show r<2^64 by omega),Nat.mod_eq_of_lt he,decide_eq_false_iff_not]
      exact Nat.not_lt.mpr (hlower i hi)
    · simp [Br.holds,E.eval,cst,CmpOp.eval,h20,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega)]
      omega
  refine ⟨(resL ends m bound v).toState s,_,(run_sound (code_lookT hc) hh s hp hob hbr).1,?_,rfl,rfl,?_,?_⟩
  · simp only [resL]; split <;> omega
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; rfl
end SigGolfCandidate.T3M.Sign.SharedFloor


namespace SigGolfCandidate.T3M.Sign.SharedResidual
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed22230 : Code22230 Images.signImage := by
  constructor <;> apply codeAt_sign_current_slice <;> decide +kernel
theorem installed22448 : Code22448 Images.signImage := by
  constructor <;> apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedResidual
namespace SigGolfCandidate.T3M.Sign.SharedTopDigits
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem installed_save : CodeAt Images.signImage (pcOf 22208) saveCode := by
  apply codeAt_sign_current_slice <;> decide +kernel
theorem installed_restore : CodeAt Images.signImage (pcOf 22460) restoreCode := by
  apply codeAt_sign_current_slice <;> decide +kernel
end SigGolfCandidate.T3M.Sign.SharedTopDigits


namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def selectACode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x8e3a03,0x0c10206f]
sym_block selectA := symRun { noAlias := true } selectACode (pcOf 22240) 100
def dispACode : List (BitVec 32) := bv_list% 32 [0xfff40313,0x30e63]
sym_block dispA := symRun { noAlias := true } dispACode (pcOf 24851) 100
def selectBCode : List (BitVec 32) := bv_list% 32 [0xffe40313,0xc030c63]
sym_block selectB := symRun { noAlias := true } selectBCode (pcOf 24853) 100
def guard3Code : List (BitVec 32) := bv_list% 32 [0x1600313,0x1c6a7263]
sym_block guard3 := symRun { noAlias := true } guard3Code (pcOf 24855) 100
def return3Code : List (BitVec 32) := bv_list% 32 [0xa0e93,0x1c00006f]
sym_block return3 := symRun { noAlias := true } return3Code (pcOf 24857) 100
def finCode : List (BitVec 32) := bv_list% 32 [0xf44fd06f]
sym_block fin := symRun { noAlias := true } finCode (pcOf 24970) 100

theorem selectA_steps {im : Image} (hc : CodeAt im (pcOf 22240) selectACode)
    (s : MachineState) (hp : s.pc=pcOf 22240) (r : Nat)
    (hr : s.getMem (0x66008#64)=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 24851 ∧
      t.getReg .x20=BitVec.ofNat 64 r ∧ RegsExcept s t [.x20,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound selectA hc s hp (by simp [selectA.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [selectA.res,rv_simp]
  · simp [selectA.res,rv_simp,hr]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem dispA_steps {im : Image} (hc : CodeAt im (pcOf 24851) dispACode)
    (s : MachineState) (hp : s.pc=pcOf 24851) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=(if lay=1 then pcOf 24859 else pcOf 24853) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound dispA hc s hp (by simp [dispA.res,rv_simp]),?_,?_,?_⟩
  · rcases hl with ⟨hlo,hhi⟩
    interval_cases lay <;> simp [dispA.res,rv_simp,h8]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem selectB_steps {im : Image} (hc : CodeAt im (pcOf 24853) selectBCode)
    (s : MachineState) (hp : s.pc=pcOf 24853) (lay : Nat) (hl : lay=2 ∨ lay=3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=(if lay=2 then pcOf 24908 else pcOf 24855) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound selectB hc s hp (by simp [selectB.res,rv_simp]),?_,?_,?_⟩
  · rcases hl with rfl|rfl <;> simp [selectB.res,rv_simp,h8]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem guard3_steps {im : Image} (hc : CodeAt im (pcOf 24855) guard3Code)
    (s : MachineState) (hp : s.pc=pcOf 24855) (r : Nat) (hr : r<22)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 24857 ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound guard3 hc s hp (by simp [guard3.res,rv_simp]),?_,?_,?_⟩
  · simp [guard3.res,rv_simp,h20,BitVec.ult,toNat_ofNat_lt (show r<2^64 by omega),hr]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem return3_steps {im : Image} (hc : CodeAt im (pcOf 24857) return3Code)
    (s : MachineState) (hp : s.pc=pcOf 24857) (r : Nat)
    (h20 : s.getReg .x20=BitVec.ofNat 64 r) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 24970 ∧ t.getReg .x29=BitVec.ofNat 64 r ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound return3 hc s hp (by simp [return3.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [return3.res,rv_simp]
  · simp [return3.res,rv_simp,h20]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl

theorem fin_steps {im : Image} (hc : CodeAt im (pcOf 24970) finCode)
    (s : MachineState) (hp : s.pc=pcOf 24970) :
    ∃ t,Steps im s 1 1 t ∧ t.pc=pcOf 22363 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound fin hc s hp (by simp [fin.res,rv_simp]),?_,?_,?_⟩
  · simp [fin.res,rv_simp]
  · intro q hq;cases q <;> simp at hq <;> rfl
  · intro A hA hn;rfl
end SigGolfCandidate.T3M.Sign.SharedFloor

namespace SigGolfCandidate.T3M.Sign.SharedFloor
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen
open ClaudeWCT.WCT9
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem threshold1_range : ∀ r,r<56 →
    CanonicalPolicy.threshold 1 r≤15 ∧ (CanonicalPolicy.threshold 1 r<15 → r<ends1.getD (CanonicalPolicy.threshold 1 r) 0) ∧
      ∀ i,i<CanonicalPolicy.threshold 1 r → ends1.getD i 0≤r := by decide +kernel
theorem threshold2_range : ∀ r,r<41 →
    CanonicalPolicy.threshold 2 r≤19 ∧ (CanonicalPolicy.threshold 2 r<19 → r<ends2.getD (CanonicalPolicy.threshold 2 r) 0) ∧
      ∀ i,i<CanonicalPolicy.threshold 2 r → ends2.getD i 0≤r := by decide +kernel
theorem ends1_lt : ∀ i, i<15 → ends1.getD i 0<2^64 := by decide +kernel
theorem ends2_lt : ∀ i, i<19 → ends2.getD i 0<2^64 := by decide +kernel

structure DispatchCode (im : Image) : Prop where
  selectA : CodeAt im (pcOf 22240) selectACode
  dispA : CodeAt im (pcOf 24851) dispACode
  selectB : CodeAt im (pcOf 24853) selectBCode
  guard3 : CodeAt im (pcOf 24855) guard3Code
  return3 : CodeAt im (pcOf 24857) return3Code
  fin : CodeAt im (pcOf 24970) finCode
  th : CodeAt im (pcOf 24851) thCode

theorem threshold_steps {im : Image} (hc : DispatchCode im)
    (s : MachineState) (hp : s.pc=pcOf 22240) (lay r : Nat) (hl : 1≤lay ∧ lay≤3)
    (hr : r < if lay=1 then 56 else if lay=2 then 41 else 22)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay)
    (hrm : s.getMem (0x66008#64)=BitVec.ofNat 64 r) :
    ∃ t k,Steps im s k k t ∧ k≤70 ∧ t.pc=pcOf 22363 ∧
      t.getReg .x29=BitVec.ofNat 64 (CanonicalPolicy.threshold lay r) ∧
      RegsExcept s t [.x6,.x20,.x28,.x29] ∧ Frame s t (fun _ => False) := by
  obtain ⟨a,sa,ap,a20,ar,af⟩ := selectA_steps hc.selectA s hp r hrm
  have a8 := (ar.get (by decide : RiscvZkvm.Rv64.Reg.x8 ∉ [.x20,.x28])).trans h8
  obtain ⟨b,ab,bp,br,bf⟩ := dispA_steps hc.dispA a ap lay hl a8
  have b20 := (br.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans a20
  have b8 := (br.get (by decide : RiscvZkvm.Rv64.Reg.x8 ∉ [.x6])).trans a8
  rcases hl with ⟨hlo,hhi⟩
  interval_cases lay
  · have ht := threshold1_range r (by simpa using hr)
    obtain ⟨t,k,bt,hk,tp,t29,tr,tf⟩ := floorL_steps hc.th ends1 15 56 24859 checked1 (by decide) rfl ends1_lt
      (by decide) b (by simpa using bp) r _ ht.1 (by simpa using hr) ht.2.1 ht.2.2 b20
    exact ⟨t,4+2+k,(sa.trans ab).trans bt,by omega,tp,t29,((ar.trans br).trans tr).mono (by simp),
      ((af.trans bf).trans tf).mono (by tauto)⟩
  · obtain ⟨c,bc,cp,cr,cf⟩ := selectB_steps hc.selectB b (by simpa using bp) 2 (by simp) b8
    have c20 := (cr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans b20
    have ht := threshold2_range r (by simpa using hr)
    obtain ⟨t,k,ct,hk,tp,t29,tr,tf⟩ := floorL_steps hc.th ends2 19 41 24908 checked2 (by decide) rfl ends2_lt
      (by decide) c (by simpa using cp) r _ ht.1 (by simpa using hr) ht.2.1 ht.2.2 c20
    exact ⟨t,4+2+2+k,((sa.trans ab).trans bc).trans ct,by omega,tp,t29,
      (((ar.trans br).trans cr).trans tr).mono (by simp),(((af.trans bf).trans cf).trans tf).mono (by tauto)⟩
  · obtain ⟨c,bc,cp,cr,cf⟩ := selectB_steps hc.selectB b (by simpa using bp) 3 (by simp) b8
    have c20 := (cr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans b20
    obtain ⟨d,cd,dp,dr,df⟩ := guard3_steps hc.guard3 c (by simpa using cp) r (by simpa using hr) c20
    have d20 := (dr.get (by decide : RiscvZkvm.Rv64.Reg.x20 ∉ [.x6])).trans c20
    obtain ⟨e,de,ep,e29,er,ef⟩ := return3_steps hc.return3 d dp r d20
    obtain ⟨t,et,tp,tr,tf⟩ := fin_steps hc.fin e ep
    refine ⟨t,13,((((sa.trans ab).trans bc).trans cd).trans de).trans et,by decide,tp,?_,
      (((((ar.trans br).trans cr).trans dr).trans er).trans tr).mono (by simp),
      (((((af.trans bf).trans cf).trans df).trans ef).trans tf).mono (by tauto)⟩
    rw [tr.get (by decide),e29]
    simp [CanonicalPolicy.threshold,show r≤21 by simp at hr;omega]
#print axioms threshold_steps
end SigGolfCandidate.T3M.Sign.SharedFloor
