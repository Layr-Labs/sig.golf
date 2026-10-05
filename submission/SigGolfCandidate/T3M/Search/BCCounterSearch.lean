import SigGolfCandidate.T3M.Search.CounterSearch
import SigGolfCandidate.T3.Nonbinary.CreditFilter
import SigGolfCandidate.ClaudeWCT.WCT9.Core

section

section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def setupCode : List (BitVec 32) := [197907,230803,1555,17828371]
def preCode : List (BitVec 32) := [0x7f57e13,3022355,32378419]
def loadCode : List (BitVec 32) := [0x83e4e03]
def postCode : List (BitVec 32) := [29754931,7689491,60136979,29713715,7722387,0xfffa0a13,0xfc0a1ce3]
def tailCode : List (BitVec 32) := [3505683,0xffee0e13,1981971,29754931,2446611,3505683,0xffee0e13,1981971,29754931,2446611,0xffe50e13,1981971,29754931,9846291,0xa0e1e63]
def okCode : List (BitVec 32) := [2579,0xf11ff06f]
def h0Code : List (BitVec 32) := [0x960410e3]
def luiCode : List (BitVec 32) := [0xffff37]
def flagCode : List (BitVec 32) := [662654467]
def beqCode : List (BitVec 32) := [0x940e0ae3]
def ld1Code : List (BitVec 32) := [663696131]
def ld2Code : List (BitVec 32) := [672084867]
def dumCode : List (BitVec 32) := [0x8000c93,2579,0xeedff06f]
def nopCode : List (BitVec 32) := [19,19,19,19,19]
def cfLayout : Rv.Layout := [(0,setupCode),(4,preCode),(7,loadCode),(8,postCode),(15,tailCode),(30,okCode),(32,h0Code),
  (33,luiCode),(34,flagCode),(35,beqCode),(36,ld1Code),(37,ld2Code),(38,dumCode),(41,nopCode)]
theorem cfLayout_ok : layoutOk 0 cfLayout = true := by decide +kernel
theorem cfLayout_code : topSeg392 = layoutCode cfLayout := by decide +kernel
theorem code_cf {image : Image} {b : Nat} (hK : KernAt image b) (i o : Nat) (seg : List (BitVec 32))
    (h : cfLayout[i]? = some (o, seg)) : CodeAt image (pcOf (b + 392 + o)) seg := by
  have hc := codeAt_top392 hK
  rw [cfLayout_code] at hc
  exact codeAt_sublayout hc cfLayout_ok (i := i) (o := o) (seg := seg) h
theorem code_setup {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 392)) setupCode := by
  simpa using code_cf hK 0 0 setupCode (by kernel_rfl)
theorem code_pre {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 396)) preCode := by
  simpa [Nat.add_assoc] using code_cf hK 1 4 preCode (by kernel_rfl)
theorem code_load {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 399)) loadCode := by
  simpa [Nat.add_assoc] using code_cf hK 2 7 loadCode (by kernel_rfl)
theorem code_post {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 400)) postCode := by
  simpa [Nat.add_assoc] using code_cf hK 3 8 postCode (by kernel_rfl)
theorem code_tail {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 407)) tailCode := by
  simpa [Nat.add_assoc] using code_cf hK 4 15 tailCode (by kernel_rfl)
theorem code_ok {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 422)) okCode := by
  simpa [Nat.add_assoc] using code_cf hK 5 30 okCode (by kernel_rfl)
theorem code_h0 {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 424)) h0Code := by
  simpa [Nat.add_assoc] using code_cf hK 6 32 h0Code (by kernel_rfl)
theorem code_lui {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 425)) luiCode := by
  simpa [Nat.add_assoc] using code_cf hK 7 33 luiCode (by kernel_rfl)
theorem code_flag {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 426)) flagCode := by
  simpa [Nat.add_assoc] using code_cf hK 8 34 flagCode (by kernel_rfl)
theorem code_beq {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 427)) beqCode := by
  simpa [Nat.add_assoc] using code_cf hK 9 35 beqCode (by kernel_rfl)
theorem code_ld1 {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 428)) ld1Code := by
  simpa [Nat.add_assoc] using code_cf hK 10 36 ld1Code (by kernel_rfl)
theorem code_ld2 {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 429)) ld2Code := by
  simpa [Nat.add_assoc] using code_cf hK 11 37 ld2Code (by kernel_rfl)
theorem code_dum {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 430)) dumCode := by
  simpa [Nat.add_assoc] using code_cf hK 12 38 dumCode (by kernel_rfl)
sym_block cs354 := symRun {noAlias:=true} setupCode (pcOf (354+392)) 200
sym_block cs543 := symRun {noAlias:=true} setupCode (pcOf (543+392)) 200
theorem run_setup {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} setupCode (pcOf (b+392)) 200 =
      some ⟨cs354.res.st,.c (pcOf (b+396)),cs354.res.stop,cs354.res.steps,cs354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact cs354.trans (congrArg some (by kernel_rfl))
  · exact cs543.trans (congrArg some (by kernel_rfl))
sym_block cp354 := symRun {noAlias:=true} preCode (pcOf (354+396)) 200
sym_block cp543 := symRun {noAlias:=true} preCode (pcOf (543+396)) 200
theorem run_pre {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} preCode (pcOf (b+396)) 200 =
      some ⟨cp354.res.st,.c (pcOf (b+399)),cp354.res.stop,cp354.res.steps,cp354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact cp354.trans (congrArg some (by kernel_rfl))
  · exact cp543.trans (congrArg some (by kernel_rfl))
sym_block cq354 := symRun {noAlias:=true} postCode (pcOf (354+400)) 200
sym_block cq543 := symRun {noAlias:=true} postCode (pcOf (543+400)) 200
def postEnd (b : Nat) : E := rebase cq354.res.pc (pcOf (b+396)) (pcOf (b+407))
theorem run_post {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} postCode (pcOf (b+400)) 200 =
      some ⟨cq354.res.st,postEnd b,cq354.res.stop,cq354.res.steps,cq354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact cq354.trans (congrArg some (by kernel_rfl))
  · exact cq543.trans (congrArg some (by kernel_rfl))
sym_block ct354 := symRun {noAlias:=true} tailCode (pcOf (354+407)) 200
sym_block ct543 := symRun {noAlias:=true} tailCode (pcOf (543+407)) 200
def tailEnd (b : Nat) : E := rebase ct354.res.pc (pcOf (b+468)) (pcOf (b+422))
theorem run_tail {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} tailCode (pcOf (b+407)) 200 =
      some ⟨ct354.res.st,tailEnd b,ct354.res.stop,ct354.res.steps,ct354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact ct354.trans (congrArg some (by kernel_rfl))
  · exact ct543.trans (congrArg some (by kernel_rfl))
sym_block co354 := symRun {noAlias:=true} okCode (pcOf (354+422)) 200
sym_block co543 := symRun {noAlias:=true} okCode (pcOf (543+422)) 200
theorem run_ok {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} okCode (pcOf (b+422)) 200 =
      some ⟨co354.res.st,.c (pcOf (b+363)),co354.res.stop,co354.res.steps,co354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact co354.trans (congrArg some (by kernel_rfl))
  · exact co543.trans (congrArg some (by kernel_rfl))
sym_block ch354 := symRun {noAlias:=true} h0Code (pcOf (354+424)) 200
sym_block ch543 := symRun {noAlias:=true} h0Code (pcOf (543+424)) 200
def h0End (b : Nat) : E := rebase ch354.res.pc (pcOf (b+0)) (pcOf (b+425))
theorem run_h0 {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} h0Code (pcOf (b+424)) 200 =
      some ⟨ch354.res.st,h0End b,ch354.res.stop,ch354.res.steps,ch354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact ch354.trans (congrArg some (by kernel_rfl))
  · exact ch543.trans (congrArg some (by kernel_rfl))
sym_block cl354 := symRun {noAlias:=true} luiCode (pcOf (354+425)) 200
sym_block cl543 := symRun {noAlias:=true} luiCode (pcOf (543+425)) 200
theorem run_lui {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} luiCode (pcOf (b+425)) 200 =
      some ⟨cl354.res.st,.c (pcOf (b+426)),cl354.res.stop,cl354.res.steps,cl354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact cl354.trans (congrArg some (by kernel_rfl))
  · exact cl543.trans (congrArg some (by kernel_rfl))
sym_block cb354 := symRun {noAlias:=true} beqCode (pcOf (354+427)) 200
sym_block cb543 := symRun {noAlias:=true} beqCode (pcOf (543+427)) 200
def beqEnd (b : Nat) : E := rebase cb354.res.pc (pcOf (b+0)) (pcOf (b+428))
theorem run_beq {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} beqCode (pcOf (b+427)) 200 =
      some ⟨cb354.res.st,beqEnd b,cb354.res.stop,cb354.res.steps,cb354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact cb354.trans (congrArg some (by kernel_rfl))
  · exact cb543.trans (congrArg some (by kernel_rfl))
sym_block cd354 := symRun {noAlias:=true} dumCode (pcOf (354+430)) 200
sym_block cd543 := symRun {noAlias:=true} dumCode (pcOf (543+430)) 200
theorem run_dum {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} dumCode (pcOf (b+430)) 200 =
      some ⟨cd354.res.st,.c (pcOf (b+363)),cd354.res.stop,cd354.res.steps,cd354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact cd354.trans (congrArg some (by kernel_rfl))
  · exact cd543.trans (congrArg some (by kernel_rfl))
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
variable {image : Image} {b : Nat}
theorem setup_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 392)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (b + 396) ∧ t.getReg .x10 = s.getReg .x6 ∧
      t.getReg .x11 = s.getReg .x7 ∧ t.getReg .x12 = 0 ∧ t.getReg .x20 = 17#64 ∧
      RegsExcept s t [.x10, .x11, .x12, .x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_setup hK.2) (code_setup hK) s hpc (by simp [cs354.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cs354.res, rv_simp]
  · simp [cs354.res, rv_simp]
  · simp [cs354.res, rv_simp]
  · simp [cs354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [cs354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cs354.res, rv_simp]
theorem pre_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 396)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 399) ∧
      t.getReg .x28 = ((s.getReg .x10 &&& 127#64) <<< 2) + s.getReg .x30 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_pre hK.2) (code_pre hK) s hpc (by simp [cp354.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cp354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [cp354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cp354.res, rv_simp]
theorem ok_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 422)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 363) ∧ t.getReg .x20 = 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ok hK.2) (code_ok hK) s hpc (by simp [co354.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [co354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [co354.res, rv_simp] <;> rfl
  · intro A _ _; simp [co354.res, rv_simp]
theorem dum_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 430)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 363) ∧ t.getReg .x20 = 0 ∧ t.getReg .x25 = 128#64 ∧
      RegsExcept s t [.x20, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_dum hK.2) (code_dum hK) s hpc (by simp [cd354.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cd354.res, rv_simp]
  · simp [cd354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [cd354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cd354.res, rv_simp]
theorem lui_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 425)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 426) ∧ t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_lui hK.2) (code_lui hK) s hpc (by simp [cl354.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cl354.res, rv_simp, TOP_DATA]
  · intro r hr; simp at hr; cases r <;> simp_all [cl354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cl354.res, rv_simp]
theorem h0_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 424)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lay = 0 then pcOf (b + 425) else pcOf (b + 0)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_h0 hK.2) (code_h0 hK) s hpc (by simp [ch354.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, h0End, rebase, ch354.res, E.eval, CmpOp.eval, h8]
    by_cases h : lay = 0
    · subst h; simp
    · have h' : BitVec.ofNat 64 lay ≠ 0#64 := by rw [ne_eq, ofNat_eq_iff]; omega
      simp [h', h]
  · intro r hr; cases r <;> simp_all [ch354.res, rv_simp] <;> rfl
  · intro A _ _; simp [ch354.res, rv_simp]
theorem beq_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 427)) (f : Nat)
    (hf : f < 256) (h28 : s.getReg .x28 = BitVec.ofNat 64 f) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if f = 0 then pcOf (b + 0) else pcOf (b + 428)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_beq hK.2) (code_beq hK) s hpc (by simp [cb354.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, beqEnd, rebase, cb354.res, E.eval, CmpOp.eval, h28]
    by_cases h : f = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 f == 0#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      simp [this, h]
  · intro r hr; cases r <;> simp_all [cb354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cb354.res, rv_simp]
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
theorem steps_ld {s : MachineState} {pc : Word} {w : BitVec 32}
    (hc : CodeAt image pc [w]) (hpc : s.pc = pc) {rd rs : Reg} {off : BitVec 12}
    (hdec : decodeInstruction w = some (.base (.LD rd rs off)))
    (hv : accessValid (s.getReg rs + signExtend12 off) 8 = true) :
    Steps image s 1 1 ((s.setReg rd (s.getMem (s.getReg rs + signExtend12 off))).setPC (s.pc + 4)) := by
  have hf : fetch image s = some (.base (.LD rd rs off)) := (hc.fetch s hpc).trans hdec
  have hcl : classify (.base (.LD rd rs off)) = some (.load .d rd rs (signExtend12 off)) := rfl
  have hs : ordinaryStep s (.base (.LD rd rs off)) =
      some ((s.setReg rd (s.getMem (s.getReg rs + signExtend12 off))).setPC (s.pc + 4)) := by
    rw [classify_sound hcl]
    simp only [Micro.exec, LoadKind.width, hv, if_true, LoadKind.read]
  exact Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl rfl
theorem load_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 399)) (A : Nat)
    (hA : A + 131 < 16777216) (h28 : s.getReg .x28 = BitVec.ofNat 64 A) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 400) ∧
      t.getReg .x28 = (s.getByte (BitVec.ofNat 64 (A + 131))).zeroExtend 64 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have he : signExtend12 (131 : BitVec 12) = (131 : Word) := rfl
  have ha : s.getReg .x28 + signExtend12 131 = BitVec.ofNat 64 (A + 131) := by
    rw [h28, he]; exact ofNat_add_ofNat A 131
  have hv : accessValid (s.getReg .x28 + signExtend12 131) 1 = true := by
    rw [ha]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show A + 131 < 2 ^ 64 by omega), Nat.mod_one,
      and_true, true_and]
    omega
  have hd : decodeInstruction (138300931 : BitVec 32) = some (.base (.LBU .x28 .x28 131)) := rfl
  have hs := steps_lbu (code_load hK) hpc hd hv
  rw [ha] at hs
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · change s.pc + 4 = _; rw [hpc, pcOf_add4]
  · change (s.setReg .x28 _).getReg .x28 = _
    exact MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ Reg.x0)
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; simp [MachineState.setReg, MachineState.setPC, MachineState.getMem]
theorem flag_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 426))
    (h30 : s.getReg .x30 = BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 427) ∧
      t.getReg .x28 = (s.getByte (BitVec.ofNat 64 (TOP_DATA + 631))).zeroExtend 64 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have he : signExtend12 (631 : BitVec 12) = (631 : Word) := rfl
  have ha : s.getReg .x30 + signExtend12 631 = BitVec.ofNat 64 (TOP_DATA + 631) := by
    rw [h30, he]; exact ofNat_add_ofNat _ 631
  have hv : accessValid (s.getReg .x30 + signExtend12 631) 1 = true := by
    rw [ha]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show TOP_DATA + 631 < 2 ^ 64 by unfold TOP_DATA; omega),
      Nat.mod_one, and_true, true_and]
    unfold TOP_DATA; omega
  have hd : decodeInstruction (662654467 : BitVec 32) = some (.base (.LBU .x28 .x30 631)) := rfl
  have hs := steps_lbu (code_flag hK) hpc hd hv
  rw [ha] at hs
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · change s.pc + 4 = _; rw [hpc, pcOf_add4]
  · change (s.setReg .x28 _).getReg .x28 = _
    exact MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ Reg.x0)
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; simp [MachineState.setReg, MachineState.setPC, MachineState.getMem]
theorem ld_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 428))
    (h30 : s.getReg .x30 = BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 430) ∧
      t.getReg .x6 = s.getMem (BitVec.ofNat 64 (TOP_DATA + 632)) ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 (TOP_DATA + 640)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  have he1 : signExtend12 (632 : BitVec 12) = (632 : Word) := rfl
  have he2 : signExtend12 (640 : BitVec 12) = (640 : Word) := rfl
  have ha1 : s.getReg .x30 + signExtend12 632 = BitVec.ofNat 64 (TOP_DATA + 632) := by
    rw [h30, he1]; exact ofNat_add_ofNat _ 632
  have hv1 : accessValid (s.getReg .x30 + signExtend12 632) 8 = true := by
    rw [ha1]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show TOP_DATA + 632 < 2 ^ 64 by unfold TOP_DATA; omega)]
    unfold TOP_DATA; omega
  have hd1 : decodeInstruction (663696131 : BitVec 32) = some (.base (.LD .x6 .x30 632)) := rfl
  have hs1 := steps_ld (code_ld1 hK) hpc hd1 hv1
  rw [ha1] at hs1
  have hp1 : ((s.setReg .x6 (s.getMem (BitVec.ofNat 64 (TOP_DATA + 632)))).setPC (s.pc + 4)).pc = pcOf (b + 429) := by
    change s.pc + 4 = _; rw [hpc, pcOf_add4]
  have h30' : ((s.setReg .x6 (s.getMem (BitVec.ofNat 64 (TOP_DATA + 632)))).setPC (s.pc + 4)).getReg .x30 =
      BitVec.ofNat 64 TOP_DATA := by
    change (s.setReg .x6 (s.getMem (BitVec.ofNat 64 (TOP_DATA + 632)))).getReg .x30 = _
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]; exact h30
  have ha2 : ((s.setReg .x6 (s.getMem (BitVec.ofNat 64 (TOP_DATA + 632)))).setPC (s.pc + 4)).getReg .x30 +
      signExtend12 640 = BitVec.ofNat 64 (TOP_DATA + 640) := by
    rw [h30', he2]; exact ofNat_add_ofNat _ 640
  have hv2 : accessValid (((s.setReg .x6 (s.getMem (BitVec.ofNat 64 (TOP_DATA + 632)))).setPC (s.pc + 4)).getReg .x30 +
      signExtend12 640) 8 = true := by
    rw [ha2]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show TOP_DATA + 640 < 2 ^ 64 by unfold TOP_DATA; omega)]
    unfold TOP_DATA; omega
  have hd2 : decodeInstruction (672084867 : BitVec 32) = some (.base (.LD .x7 .x30 640)) := rfl
  have hs2 := steps_ld (code_ld2 hK) hp1 hd2 hv2
  rw [ha2] at hs2
  refine ⟨_, Steps.of_eq (hs1.trans hs2) rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change ((s.setReg .x6 (s.getMem (BitVec.ofNat 64 (TOP_DATA + 632)))).setPC (s.pc + 4)).pc + 4 = _
    rw [hp1, pcOf_add4]
  · simp [MachineState.setReg, MachineState.setPC, MachineState.getReg]
  · simp [MachineState.setReg, MachineState.setPC, MachineState.getReg, MachineState.getMem]
  · intro q hq
    simp only [List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil] at hq
    simp [MachineState.setReg, MachineState.setPC, MachineState.getReg, Function.update, hq.1, hq.2.1]
  · intro A _ _; simp [MachineState.setReg, MachineState.setPC, MachineState.getMem]
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
theorem ofNat_dec (n : Nat) (hn : 1 ≤ n) (hn' : n < 2 ^ 64) :
    BitVec.ofNat 64 n + 18446744073709551615#64 = BitVec.ofNat 64 (n - 1) := by
  rw [show (18446744073709551615#64) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, ofNat_add_ofNat, ofNat_eq_iff]
  omega
theorem ofNat_sub1 (n : Nat) (hn : 1 ≤ n) (hn' : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
  have h : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - 1) + 1#64 := by
    rw [show (1#64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]; congr 1; omega
  rw [h, BitVec.add_sub_cancel]
theorem post_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 400)) (n : Nat)
    (hn : 1 ≤ n) (hn' : n ≤ 17) (h20 : s.getReg .x20 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = (if n = 1 then pcOf (b + 407) else pcOf (b + 396)) ∧
      t.getReg .x12 = s.getReg .x12 + s.getReg .x28 ∧
      t.getReg .x10 = (s.getReg .x10 >>> 7 ||| s.getReg .x11 <<< 57) ∧
      t.getReg .x11 = s.getReg .x11 >>> 7 ∧ t.getReg .x20 = BitVec.ofNat 64 (n - 1) ∧
      RegsExcept s t [.x10, .x11, .x12, .x20, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_post hK.2) (code_post hK) s hpc (by simp [cq354.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, postEnd, rebase, cq354.res, E.eval, CmpOp.eval, BinOp.eval, h20]
    rw [ofNat_dec n hn (by omega)]
    by_cases h : n = 1
    · subst h; simp
    · have h' : BitVec.ofNat 64 (n - 1) ≠ 0#64 := by rw [ne_eq, ofNat_eq_iff]; omega
      simp [h', h]
  · simp [cq354.res, rv_simp]
  · simp [cq354.res, rv_simp]
  · simp [cq354.res, rv_simp]
  · simp [cq354.res, rv_simp]
    rw [h20]
    exact ofNat_sub1 n hn (by omega)
  · intro r hr; simp at hr; cases r <;> simp_all [cq354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cq354.res, rv_simp]
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
def tailCredit (X : Nat) : Nat :=
  (if X % 4 = 2 then 1 else 0) + (if X / 4 % 4 = 2 then 1 else 0) + (if X / 16 = 2 then 1 else 0)
theorem eq2_ofNat (d : Nat) (hd : d < 4) :
    (if ((BitVec.ofNat 64 d) - 2#64).ult 1#64 = true then 1#64 else 0#64) =
      BitVec.ofNat 64 (if d = 2 then 1 else 0) := by
  interval_cases d <;> decide
theorem tail_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 407)) (X C : Nat)
    (hX : X < 64) (hC : C < 64) (h10 : s.getReg .x10 = BitVec.ofNat 64 X)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 C) :
    ∃ t, Steps image s 15 15 t ∧
      t.pc = (if C + tailCredit X < 9 then pcOf (b + 468) else pcOf (b + 422)) ∧
      t.getReg .x12 = BitVec.ofNat 64 (C + tailCredit X) ∧
      RegsExcept s t [.x10, .x12, .x28] ∧ Frame s t (fun _ => False) := by
  have e0 : (BitVec.ofNat 64 X &&& 3#64) = BitVec.ofNat 64 (X % 4) := ofNat_and_mask X 2 (by decide)
  have e1 : (BitVec.ofNat 64 X >>> 2 &&& 3#64) = BitVec.ofNat 64 (X / 4 % 4) := by
    rw [ofNat_shr X 2 (by omega)]; exact ofNat_and_mask _ 2 (by decide)
  have e2 : BitVec.ofNat 64 X >>> 4 = BitVec.ofNat 64 (X / 16) := ofNat_shr X 4 (by omega)
  refine ⟨_, symRun_sound (run_tail hK.2) (code_tail hK) s hpc (by simp [ct354.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [tailEnd, rebase, ct354.res, rv_simp, E.eval, CmpOp.eval, BinOp.eval, h10, h12]
    rw [e1, e2, eq2_ofNat _ (by omega), eq2_ofNat _ (by omega), eq2_ofNat _ (by omega), ofNat_add_ofNat,
      ofNat_add_ofNat, ofNat_add_ofNat]
    have ht : C + (if X % 4 = 2 then 1 else 0) + (if X / 4 % 4 = 2 then 1 else 0) + (if X / 16 = 2 then 1 else 0) =
        C + tailCredit X := by unfold tailCredit; omega
    rw [ht]
    have hlt : (BitVec.ofNat 64 (C + tailCredit X)).ult 9#64 = decide (C + tailCredit X < 9) := by
      have : tailCredit X ≤ 3 := by unfold tailCredit; split_ifs <;> omega
      simp only [BitVec.ult, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hlt]
    by_cases h : C + tailCredit X < 9 <;> simp [h]
  · simp [ct354.res, rv_simp, h10, h12]
    rw [e1, e2, eq2_ofNat _ (by omega), eq2_ofNat _ (by omega), eq2_ofNat _ (by omega), ofNat_add_ofNat,
      ofNat_add_ofNat, ofNat_add_ofNat]
    unfold tailCredit; congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [ct354.res, rv_simp] <;> rfl
  · intro A _ _; simp [ct354.res, rv_simp]
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def creditSum (v : Digest) (k : Nat) : Nat := ((List.range k).map fun j => rankCredit (topRank v j)).sum
theorem creditSum_succ (v : Digest) (k : Nat) :
    creditSum v (k + 1) = creditSum v k + rankCredit (topRank v k) := by
  simp [creditSum, List.range_succ]
theorem rankCredit_le (r : Nat) : rankCredit r ≤ 3 := by unfold rankCredit; split_ifs <;> omega
theorem creditSum_le (v : Digest) (k : Nat) : creditSum v k ≤ 3 * k := by
  induction k with
  | zero => simp [creditSum]
  | succ k ih => rw [creditSum_succ]; have := rankCredit_le (topRank v k); omega
private def cf (v : Digest) (i : Nat) : Nat := if T3.coreDigit 0 v i = (if i < 51 then 3 else 2) then 1 else 0
private theorem cf_rank (v : Digest) (k i : Nat) (hk : k < 17) (hi : i < 3) :
    cf v (3 * k + i) = if rankDigit (topRank v k) i = 3 then 1 else 0 := by
  unfold cf
  rw [if_pos (show 3 * k + i < 51 by omega), TopUnpack.source_rank_digit v k i hk hi]
private theorem range_three (n : Nat) : List.range (n + 3) = List.range n ++ [n, n + 1, n + 2] := by
  simp [List.range_succ]
theorem rankCredit_digits (r : Nat) :
    rankCredit r = (if rankDigit r 0 = 3 then 1 else 0) + (if rankDigit r 1 = 3 then 1 else 0) +
      (if rankDigit r 2 = 3 then 1 else 0) := by
  simp [rankCredit, rankDigit] <;> rfl
private theorem cf_groups (v : Digest) : ∀ k, k ≤ 17 → ((List.range (3 * k)).map (cf v)).sum = creditSum v k := by
  intro k
  induction k with
  | zero => intro _; simp [creditSum]
  | succ k ih =>
      intro hk
      rw [show 3 * (k + 1) = 3 * k + 3 by omega, range_three, List.map_append, List.sum_append, ih (by omega),
        creditSum_succ, rankCredit_digits]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [show 3 * k = 3 * k + 0 by omega, cf_rank v k 0 (by omega) (by omega), cf_rank v k 1 (by omega) (by omega),
        cf_rank v k 2 (by omega) (by omega)]
      omega
theorem topCredit_split (v : Digest) (hv : v.toNat < 2 ^ 125) :
    T3.topCredit v = creditSum v 17 + tailCredit (v.toNat / 2 ^ 119) := by
  have h : T3.topCredit v = ((List.range 54).map (cf v)).sum := rfl
  rw [h, show (54 : Nat) = 51 + 3 from rfl, range_three, List.map_append, List.sum_append,
    show (51 : Nat) = 3 * 17 from rfl, cf_groups v 17 le_rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  unfold cf tailCredit
  simp only [T3.coreDigit, if_pos rfl, show ¬ (51 : Nat) < 51 by omega, show ¬ (3 * 17 + 1 : Nat) < 51 by omega,
    show ¬ (3 * 17 + 2 : Nat) < 51 by omega, if_false]
  have e3 : v.toNat / 2 ^ 123 < 4 := by omega
  have hX2 : v.toNat / 2 ^ 119 / 4 % 4 = v.toNat / 2 ^ 121 % 4 := by
    rw [Nat.div_div_eq_div_mul]; norm_num
  have hX3 : v.toNat / 2 ^ 119 / 16 = v.toNat / 2 ^ 123 % 4 := by
    rw [Nat.div_div_eq_div_mul, Nat.mod_eq_of_lt e3]; norm_num
  rw [hX2, hX3]
  norm_num
  ring
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
abbrev Changed : List Reg := [.x10, .x11, .x12, .x20, .x28]
structure LInv (b : Nat) (s0 : MachineState) (v : Digest) (k : Nat) (t : MachineState) : Prop where
  bound : k ≤ 17
  pc : t.pc = if k < 17 then pcOf (b + 396) else pcOf (b + 407)
  lo : t.getReg .x10 = BitVec.ofNat 64 (v.toNat / 2 ^ (7 * k))
  hi : t.getReg .x11 = BitVec.ofNat 64 (v.toNat / 2 ^ (7 * k) / 2 ^ 64)
  acc : t.getReg .x12 = BitVec.ofNat 64 (creditSum v k)
  cnt : t.getReg .x20 = BitVec.ofNat 64 (17 - k)
  tab : t.getReg .x30 = BitVec.ofNat 64 TOP_DATA
  regs : RegsExcept s0 t Changed
  frame : Frame s0 t (fun _ => False)
theorem ptr_credit (X : Nat) :
    ((BitVec.ofNat 64 X &&& 127#64) <<< 2) + BitVec.ofNat 64 TOP_DATA = BitVec.ofNat 64 (TOP_DATA + 4 * (X % 128)) := by
  rw [ofNat_and127, ofNat_shl, ofNat_add_ofNat]
  congr 1
  omega
theorem zext_ofNat8 (c : Nat) (hc : c < 256) : (BitVec.ofNat 8 c).zeroExtend 64 = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
theorem table_credit_byte (s : MachineState) (ht : TableOK s) (r : Nat) (hr : r < 125) :
    s.getByte (BitVec.ofNat 64 (TOP_DATA + 4 * r + 131)) = BitVec.ofNat 8 (rankCredit r) := by
  have h := ht (128 + 4 * r + 3) (by omega)
  rw [show TOP_DATA + (128 + 4 * r + 3) = TOP_DATA + 4 * r + 131 by omega] at h
  rw [h]
  unfold tableByte
  simp only [show ¬ 128 + 4 * r + 3 < 128 by omega, if_false, show 128 + 4 * r + 3 < 628 by omega, if_true]
  have h1 : (128 + 4 * r + 3 - 128) % 4 = 3 := by omega
  have h2 : (128 + 4 * r + 3 - 128) / 4 = r := by omega
  rw [h1, h2, if_neg (by omega)]
theorem loop_body (hK : KernAt image b) {s0 t : MachineState} (ht : TableOK s0) (v : Digest)
    (hvalid : T3.topRanksValid v = true) (k : Nat) (hk : k < 17) (hI : LInv b s0 v k t) :
    ∃ u, Steps image t 11 11 u ∧ LInv b s0 v (k + 1) u := by
  have pc := hI.pc
  rw [if_pos hk] at pc
  obtain ⟨t1, s1, p1, a28, r1, f1⟩ := pre_spec hK t pc
  have rankbound : topRank v k < 125 := by
    have hv := (List.all_eq_true.mp hvalid) k (List.mem_range.mpr hk)
    exact of_decide_eq_true hv
  have hp1 : t1.getReg .x28 = BitVec.ofNat 64 (TOP_DATA + 4 * topRank v k) := by
    rw [a28, hI.lo, hI.tab, ptr_credit]
    rfl
  obtain ⟨t2, s2, p2, a28', r2, f2⟩ := load_spec hK t1 p1 (TOP_DATA + 4 * topRank v k)
    (by unfold TOP_DATA; omega) hp1
  have table1 : TableOK t1 := ht.frame (W := fun _ => False) ((hI.frame.trans f1).mono (by simp)) (by intro j hj h; exact h)
  rw [table_credit_byte t1 table1 _ rankbound, zext_ofNat8 _ (by have := rankCredit_le (topRank v k); omega)] at a28'
  obtain ⟨u, s3, p3, g12, g10, g11, g20, r3, f3⟩ := post_spec hK t2 p2 (17 - k) (by omega) (by omega)
    (by rw [r2.get (by decide), r1.get (by decide), hI.cnt])
  refine ⟨u, (s1.trans s2).trans s3, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [p3]
    by_cases h16 : k = 16
    · subst h16; simp
    · rw [if_neg (by omega), if_pos (by omega)]
  · rw [g10, r2.get (by decide), r1.get (by decide), hI.lo, r2.get (by decide), r1.get (by decide), hI.hi,
      TopUnpack.pair_shift]
    apply congrArg (BitVec.ofNat 64)
    rw [Nat.div_div_eq_div_mul, ← pow_add, show 7 * k + 7 = 7 * (k + 1) by omega]
  · have hv := v.isLt
    have hx := Nat.div_le_self v.toNat (2 ^ (7 * k))
    have hh : v.toNat / 2 ^ (7 * k) / 2 ^ 64 < 2 ^ 64 := by omega
    rw [g11, r2.get (by decide), r1.get (by decide), hI.hi, ofNat_shr _ _ hh]
    apply congrArg (BitVec.ofNat 64)
    simp only [Nat.div_div_eq_div_mul]
    apply congrArg (fun d => v.toNat / d)
    simp only [← pow_add]
    congr 1 <;> omega
  · rw [g12, r2.get (by decide), r1.get (by decide), hI.acc, a28', ofNat_add_ofNat, creditSum_succ]
  · rw [g20]; congr 1
  · rw [r3.get (by decide), r2.get (by decide), r1.get (by decide), hI.tab]
  · exact ((hI.regs.trans r1).trans r2 |>.trans r3).mono (by decide)
  · exact ((hI.frame.trans f1).trans f2 |>.trans f3).mono (by simp)
theorem loop_iter (hK : KernAt image b) {s0 t : MachineState} (ht : TableOK s0) (v : Digest)
    (hvalid : T3.topRanksValid v = true) (hI : LInv b s0 v 0 t) (n : Nat) (hn : n ≤ 17) :
    ∃ u, Steps image t (11 * n) (11 * n) u ∧ LInv b s0 v n u := by
  induction n with
  | zero => exact ⟨t, Steps.refl t, hI⟩
  | succ n ih =>
      obtain ⟨u, hs, hu⟩ := ih (by omega)
      obtain ⟨w, hw, hwI⟩ := loop_body hK ht v hvalid n (by omega) hu
      exact ⟨w, (hs.trans hw).of_eq (by omega) (by omega), hwI⟩
theorem credit_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 392)) (v : Digest)
    (hv : v.toNat < 2 ^ 125) (hvalid : T3.topRanksValid v = true) (ht : TableOK s)
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s (if T3.topCredit v < 9 then 206 else 208) (if T3.topCredit v < 9 then 206 else 208) t ∧
      t.pc = (if T3.topCredit v < 9 then pcOf (b + 468) else pcOf (b + 363)) ∧
      (¬ T3.topCredit v < 9 → t.getReg .x20 = 0) ∧
      RegsExcept s t Changed ∧ Frame s t (fun _ => False) := by
  have h6' : s.getReg .x6 = BitVec.ofNat 64 v.toNat := by
    rw [h6]; apply BitVec.eq_of_toNat_eq; simp
  have h7' : s.getReg .x7 = BitVec.ofNat 64 (v.toNat / 2 ^ 64) := by
    rw [h7]; apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]
  obtain ⟨t0, s0', p0, g10, g11, g12, g20, r0, f0⟩ := setup_spec hK s hpc
  have hI : LInv b s v 0 t0 := by
    refine ⟨by omega, by simpa using p0, ?_, ?_, ?_, ?_, ?_, r0.mono (by decide), f0⟩
    · simpa using g10.trans h6'
    · simpa using g11.trans h7'
    · rw [g12]; try rfl
    · rw [g20]; try rfl
    · rw [r0.get (by decide), h30]
  obtain ⟨m, sm, hm⟩ := loop_iter hK ht v hvalid hI 17 le_rfl
  have pm : m.pc = pcOf (b + 407) := by simpa using hm.pc
  have hX : v.toNat / 2 ^ 119 < 64 := by omega
  obtain ⟨t1, s1, p1, g12', r1, f1⟩ := tail_spec hK m pm (v.toNat / 2 ^ 119) (creditSum v 17) hX
    (by have := creditSum_le v 17; omega) (by simpa using hm.lo) hm.acc
  rw [← topCredit_split v hv] at p1
  by_cases hc : T3.topCredit v < 9
  · rw [if_pos hc] at p1
    refine ⟨t1, ?_, by rw [if_pos hc, p1], fun h => absurd hc h, ?_, ?_⟩
    · rw [if_pos hc]; exact (s0'.trans (sm.trans s1)).of_eq (by norm_num) (by norm_num)
    · exact (hm.regs.trans r1).mono (by decide)
    · exact (hm.frame.trans f1).mono (by simp)
  · rw [if_neg hc] at p1
    obtain ⟨t2, s2, p2, g20', r2, f2⟩ := ok_spec hK t1 p1
    refine ⟨t2, ?_, by rw [if_neg hc, p2], fun _ => g20', ?_, ?_⟩
    · rw [if_neg hc]; exact (s0'.trans ((sm.trans s1).trans s2)).of_eq (by norm_num) (by norm_num)
    · exact ((hm.regs.trans r1).trans r2).mono (by decide)
    · exact ((hm.frame.trans f1).trans f2).mono (by simp)
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
def dummyDigest : Digest := BitVec.ofNat 128 dummyDigestNat
theorem cf_byte (s : MachineState) (flag : Nat) (h : CfTableOK flag s) (i : Nat) (hi : 628 ≤ i) (hj : i < 648) :
    s.getByte (BitVec.ofNat 64 (TOP_DATA + i)) = cfByte flag i := h i hi hj
private theorem extractByte_toNat'' (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
private theorem word_ext_bytes' {w₁ w₂ : Word} (h : ∀ j < 8, extractByte w₁ j = extractByte w₂ j) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have e := fun j (hj : j < 8) => congrArg BitVec.toNat (h j hj)
  simp only [extractByte_toNat''] at e
  have h0 := e 0 (by decide); have h1 := e 1 (by decide); have h2 := e 2 (by decide)
  have h3 := e 3 (by decide); have h4 := e 4 (by decide); have h5 := e 5 (by decide)
  have h6 := e 6 (by decide); have h7 := e 7 (by decide)
  simp only [Nat.reducePow, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  have := w₁.isLt; have := w₂.isLt
  omega
theorem mem_word (s : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 < 2 ^ 64) (w : Word)
    (h : ∀ j < 8, s.getByte (BitVec.ofNat 64 (A + j)) = extractByte w j) :
    s.getMem (BitVec.ofNat 64 A) = w := by
  apply word_ext_bytes'
  intro j hj
  rw [← h j hj, getByte_eq_word s (A + j) (by omega)]
  rw [show (A + j) / 8 * 8 = A by omega, show (A + j) % 8 = j by omega]
theorem mem_dummy_lo (s : MachineState) (flag : Nat) (h : CfTableOK flag s) :
    s.getMem (BitVec.ofNat 64 (TOP_DATA + 632)) = dummyDigest.extractLsb' 0 64 := by
  apply mem_word s _ (by unfold TOP_DATA; omega) (by unfold TOP_DATA; omega)
  intro j hj
  rw [show TOP_DATA + 632 + j = TOP_DATA + (632 + j) by omega, cf_byte s flag h _ (by omega) (by omega)]
  unfold cfByte
  rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  interval_cases j <;> decide
theorem mem_dummy_hi (s : MachineState) (flag : Nat) (h : CfTableOK flag s) :
    s.getMem (BitVec.ofNat 64 (TOP_DATA + 640)) = dummyDigest.extractLsb' 64 64 := by
  apply mem_word s _ (by unfold TOP_DATA; omega) (by unfold TOP_DATA; omega)
  intro j hj
  rw [show TOP_DATA + 640 + j = TOP_DATA + (640 + j) by omega, cf_byte s flag h _ (by omega) (by omega)]
  unfold cfByte
  rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  interval_cases j <;> decide
theorem flag_byte (s : MachineState) (flag : Nat) (hf : flag < 256) (h : CfTableOK flag s) :
    (s.getByte (BitVec.ofNat 64 (TOP_DATA + 631))).zeroExtend 64 = BitVec.ofNat 64 flag := by
  rw [cf_byte s flag h 631 (by omega) (by omega)]
  unfold cfByte
  rw [if_pos rfl]
  exact zext_ofNat8 flag hf
theorem exhaust_fail (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 424)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (flag : Nat) (hf : flag < 256)
    (hcf : CfTableOK flag s) (hfl : lay ≠ 0 ∨ flag = 0) :
    ∃ n t, n ≤ 4 ∧ Steps image s n n t ∧ t.pc = pcOf (b + 0) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ := h0_spec hK s hpc lay hl h8
  by_cases hz : lay = 0
  · rw [if_pos hz] at p0
    have hf0 : flag = 0 := by rcases hfl with h | h; exact absurd hz h; exact h
    obtain ⟨t1, s1, p1, g30, r1, f1⟩ := lui_spec hK t0 p0
    obtain ⟨t2, s2, p2, g28, r2, f2⟩ := flag_spec hK t1 p1 g30
    have hcf2 : CfTableOK flag t1 := hcf.frame (W := fun _ => False) ((f0.trans f1).mono (by simp))
      (by intro j _ _ h; exact h)
    rw [flag_byte t1 flag hf hcf2] at g28
    obtain ⟨t3, s3, p3, r3, f3⟩ := beq_spec hK t2 p2 flag hf g28
    rw [if_pos hf0] at p3
    refine ⟨4, t3, le_rfl, (s0.trans (s1.trans (s2.trans s3))).of_eq (by norm_num) (by norm_num), p3, ?_, ?_⟩
    · exact (((r0.trans r1).trans r2).trans r3).mono (by decide)
    · exact (((f0.trans f1).trans f2).trans f3).mono (by simp)
  · rw [if_neg hz] at p0
    exact ⟨1, t0, by omega, s0, p0, r0.mono (by decide), f0⟩
theorem exhaust_dummy (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 424))
    (h8 : s.getReg .x8 = BitVec.ofNat 64 0) (flag : Nat) (hf : flag < 256) (hcf : CfTableOK flag s)
    (hfl : flag ≠ 0) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 363) ∧
      t.getReg .x6 = dummyDigest.extractLsb' 0 64 ∧ t.getReg .x7 = dummyDigest.extractLsb' 64 64 ∧
      t.getReg .x20 = 0 ∧ t.getReg .x25 = 128#64 ∧ t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
      RegsExcept s t [.x6, .x7, .x20, .x25, .x28, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ := h0_spec hK s hpc 0 (by omega) h8
  rw [if_pos rfl] at p0
  obtain ⟨t1, s1, p1, g30, r1, f1⟩ := lui_spec hK t0 p0
  obtain ⟨t2, s2, p2, g28, r2, f2⟩ := flag_spec hK t1 p1 g30
  have hcf1 : CfTableOK flag t1 := hcf.frame (W := fun _ => False) ((f0.trans f1).mono (by simp))
    (by intro j _ _ h; exact h)
  rw [flag_byte t1 flag hf hcf1] at g28
  obtain ⟨t3, s3, p3, r3, f3⟩ := beq_spec hK t2 p2 flag hf g28
  rw [if_neg hfl] at p3
  obtain ⟨t4, s4, p4, g6, g7, r4, f4⟩ := ld_spec hK t3 p3 (by rw [r3.get (by decide), r2.get (by decide), g30])
  have hcf3 : CfTableOK flag t3 := hcf1.frame (W := fun _ => False) ((f2.trans f3).mono (by simp))
    (by intro j _ _ h; exact h)
  rw [mem_dummy_lo t3 flag hcf3] at g6
  rw [mem_dummy_hi t3 flag hcf3] at g7
  obtain ⟨t5, s5, p5, g20, g25, r5, f5⟩ := dum_spec hK t4 p4
  refine ⟨t5, (s0.trans (s1.trans (s2.trans (s3.trans (s4.trans s5))))).of_eq (by norm_num) (by norm_num), p5,
    ?_, ?_, g20, g25, ?_, ?_, ?_⟩
  · rw [r5.get (by decide), g6]
  · rw [r5.get (by decide), g7]
  · rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide), g30]
  · exact (((((r0.trans r1).trans r2).trans r3).trans r4).trans r5).mono (by decide)
  · exact (((((f0.trans f1).trans f2).trans f3).trans f4).trans f5).mono (by simp)
theorem dummy_lt : dummyDigest.toNat < 2 ^ 125 := by decide
theorem dummy_valid : T3.topRanksValid dummyDigest = true := by decide
theorem dummy_digits : topDigits dummyDigest = T3.dummyTop := by decide
end SigGolfCandidate.T3M.Search.Credit
end
end

section




section
namespace SigGolfCandidate.T3M.Search.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT
def left : WCT9.LayerMsg → Digest
  | .forest root => root
  | .pair l _ => l
def right : WCT9.LayerMsg → Digest
  | .forest _ => 0
  | .pair _ r => r
theorem counterWords (c : BitVec 32) :
    wordsOf (bytesLE 4 c ++ bytesLE 12 (0 : BitVec 96)) = [BitVec.ofNat 64 c.toNat, 0] := by
  have hc : T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
    simp
  rw [show bytesLE 12 (0 : BitVec 96) = List.replicate 4 0 ++ List.replicate 8 0 by decide,
    ← List.append_assoc, wordsOf_append8 _ _ (by simp [bytesLE_length]), hc]
  rfl
theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    wordsOf (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c)) =
      [(left msg).extractLsb' 0 64, (left msg).extractLsb' 64 64,
        BitVec.ofNat 64 (hdr0 4 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf),
        BitVec.ofNat 64 c.toNat, 0, (right msg).extractLsb' 0 64, (right msg).extractLsb' 64 64] := by
  cases msg with
  | forest root => simpa [WCT9.layerEncodingInput, left, right] using Search.wordsOf_encodingInput lay tree leaf root c
  | pair l r =>
    change wordsOf (T3.pad64 (WCT9.pairEncodingInputP lay tree leaf l r c 0)) = _
    rw [pad64_of_aligned _ (by simp [WCT9.pairEncodingInputP, bytesLE_length])]
    have he : WCT9.pairEncodingInputP lay tree leaf l r c 0 =
        (bytesLE 16 l ++ bytesLE 16 (T3.header 4 lay.val tree 0 leaf)) ++
          (bytesLE 4 c ++ bytesLE 12 (0 : BitVec 96)) ++ bytesLE 16 r := by
      simp only [WCT9.pairEncodingInputP, List.append_assoc]
    rw [he, wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_bytesLE16, wordsOf_header, counterWords, wordsOf_bytesLE16]
    rfl
theorem encodingInput_length (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c)).length = 64 := by
  cases msg with
  | forest root => exact Search.encodingInput_length lay tree leaf root c
  | pair l r =>
    change (T3.pad64 (WCT9.pairEncodingInputP lay tree leaf l r c 0)).length = 64
    rw [pad64_of_aligned _ (by simp [WCT9.pairEncodingInputP, bytesLE_length])]
    simp [WCT9.pairEncodingInputP, bytesLE_length]
theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (c : BitVec 32) :
    (toQ (T3.pad64 (WCT9.layerEncodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl := encodingInput_length lay tree leaf msg c
  rw [blocks_toQ (by rw [Aligned, hl]; omega), hl]
end SigGolfCandidate.T3M.Search.BC
end
section
namespace SigGolfCandidate.T3M.Search.BC
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT
set_option linter.unusedSimpArgs false
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : WCT9.LayerMsg
  ret : Nat
def csT (lay : Layer) : Nat := if lay = 0 then 408 else 158
def csOk (lay : Layer) : Nat := if lay = 0 then 1516 else 967
def cfFlag (b : Nat) : Nat := if b = 543 then 1 else 0
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨ DigW A
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target A.lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  m0 : s.getMem (BitVec.ofNat 64 ENC) = (left A.msg).extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = (left A.msg).extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right A.msg).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right A.msg).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 113)
  hi : i ≤ 2 ^ 22
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 A.lay.val A.tree 0)
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 A.tree A.leaf)
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t CsW
def DummyOut (A : CsArgs) (s0 t : MachineState) : Prop :=
  t.pc = pcOf A.ret ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧
    (t.getReg .x25).toNat ≤ 128
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if A.lay = 0 ∧ b = 543 then DummyOut A s0 t else
      t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, T3.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧ (t.getReg .x25).toNat ≤ T3.target A.lay
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 A.lay.val A.tree 0)
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 A.tree A.leaf)
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u CsW
theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr
section trial
variable {image : Image} {b : Nat} {sk : BitVec 256}
theorem cs_next {A : CsArgs} {s0 u : MachineState} {i F W : Nat} {Q : Option (BitVec 32 × List Nat) → MachineState → Prop}
    (hK : KernAt image b) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 468)) (hi : i < 2 ^ 22)
    (ih : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t W (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg (i + 1) F) Q) :
    TBSim image sk u (2 + W) (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg (i + 1) F) Q := by
  obtain ⟨t1, s1, p1, h19, r1, f1⟩ := cs468_spec hK u hpc i hu.x19
  refine TBSim.steps s1 (ih t1 ⟨p1, by omega, h19, ?_, ?_, ⟨i, by omega, ?_⟩, ?_, ?_⟩)
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h16]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h24]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.c32]
  · exact (hu.regs.trans r1).mono (by decide)
  · exact (hu.frame.trans f1).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 54 else 43 := by
  fin_cases lay <;> rfl
theorem target_lt (lay : Layer) : T3.target lay < 2 ^ 63 := by
  fin_cases lay <;> decide
theorem getD_map_range {f : Nat → Nat} {n j : Nat} (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]
theorem cs_success {A : CsArgs} {s0 u : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 438)) (hi : i < 2 ^ 22) (hlz : A.lay ≠ 0)
    (v : Digest) (S : Nat) (ds : List Nat) (hdec : T3.decode A.lay v = some ds)
    (hds : ds = lowDigits v ++ [T3.target A.lay - S]) (hS : S ≤ T3.target A.lay)
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h25 : u.getReg .x25 = BitVec.ofNat 64 S) :
    TBSim image sk u 810 (pure (some (BitVec.ofNat 32 i, ds))) (CsPost image b A s0) := by
  have hl0 : A.lay.val ≠ 0 := fun h => hlz (Fin.ext h)
  obtain ⟨k, t, st, kle, tpc, tdig, tchk, tr, tf⟩ := cs_tail hK u hpc v A.lay.val
    (T3.target A.lay) S A.ret A.lay.isLt (target_lt _) (fun _ => hS)
    (by rw [hu.reg (by decide), hpre.x1]) (by rw [hu.reg (by decide), hpre.x8])
    (by rw [hu.reg (by decide), hpre.x17]) h25
    (by rw [hu.reg (by decide), hpre.x26, chainCount_eq]; simp [hlz, hl0])
    (by rw [hu.reg (by decide), hpre.x27, csN4]; simp [hlz, hl0]) h6 h7
  rw [if_neg hl0] at kle tdig
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine (TBSim.steps st (TBSim.pure ?_)).mono kle (fun _ _ h => h)
  refine ⟨tpc, by rw [hc]; exact hi, by rw [hc, tr.get (by decide), hu.x19], ?_, ⟨v, hdec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc, tf.get (by simp only [ENC]; omega) (by simp only [DigW, DIGITS, ENC]; omega), hu.c32]
  · rw [hds, chainCount_eq, if_neg hlz]
    simp [lowDigits_length]
  · intro j hj
    rw [chainCount_eq, if_neg hlz] at hj
    rw [hds]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length]; exact hj), lowDigits_eq, getD_map_range hj]
      simpa only [if_neg hl0] using tdig j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [lowDigits_length]), lowDigits_length]
      simpa using tchk hl0
  · exact (hu.regs.trans tr).mono (by decide)
  · exact (hu.frame.trans tf).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [tr.get (by decide), h25, BitVec.toNat_ofNat]
    have := target_lt A.lay
    omega
theorem TrialSt.table {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : TableOK s0) : TableOK u :=
  ht.frame hu.frame (by intro j hj; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
theorem TrialSt.cf {A : CsArgs} {s0 u : MachineState} {i : Nat} {flag : Nat}
    (hu : TrialSt b A s0 i u) (ht : CfTableOK flag s0) : CfTableOK flag u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
theorem cs_top_success {A : CsArgs} {s0 u : MachineState} {i : Nat} (hK : KernAt image b)
    (hpre : CsPre b A s0) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 363))
    (hi : i < 2 ^ 22) (hlz : A.lay = 0) (v : Digest) (hv : v.toNat < 2 ^ 125)
    (hvalid : T3.topRanksValid v = true) (hdec : T3.decode A.lay v = some (topDigits v))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h30 : u.getReg .x30 = BitVec.ofNat 64 TOP_DATA) (h25 : u.getReg .x25 = 128#64) (h20 : u.getReg .x20 = 0) :
    TBSim image sk u 301 (pure (some (BitVec.ofNat 32 i, topDigits v))) (CsPost image b A s0) := by
  obtain ⟨t, st, tpc, tdig, tr, tf⟩ := topUnpack_spec hK u v hv hvalid (hu.table hpre.table) hpc h6 h7 h30 h20
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine TBSim.steps st (TBSim.pure ?_)
  refine ⟨?_, by rw [hc]; exact hi, ?_, ?_, ⟨v, hdec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tpc, hu.reg (by decide), hpre.x1, pcOf_and_not1]
  · rw [hc, tr.get (by decide), hu.x19]
  · rw [hc, tf.get (by unfold ENC; omega) (by unfold TopUnpack.Writes DIGITS ENC; omega), hu.c32]
  · rw [hlz, topDigits_length]; rfl
  · intro j hj
    rw [hlz] at hj
    change j < 54 at hj
    rw [tdig j hj]
    simp only [topDigits, getD_map_range hj]
  · exact (hu.regs.trans tr).mono (by decide)
  · exact (hu.frame.trans tf).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [tr.get (by decide), h25, hlz]; decide
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < 2 ^ 22) :
    ∃ t2, Steps image t 10 10 t2 ∧ t2.pc = pcOf (b + 123) ∧ fetch image t2 = some (.base .ECALL) ∧
      t2.getReg .x5 = 0 ∧ hashArgumentsValid t2 = true ∧
      hashInput t2 = toQ (T3.pad64 (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i))) ∧
      t2.getReg .x12 = BitVec.ofNat 64 EOUT ∧ TrialSt b A s0 i t2 := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := cs113_spec hK t hI.pc i hI.hi hI.x19
  rw [if_neg (by omega)] at p1
  obtain ⟨x, hx, hx32⟩ := hI.c32
  obtain ⟨t2, s2, p2, c32, h10, h11, h12, r2, f2⟩ := cs115_spec hK t1 p1 i x (by omega) hx
    (by rw [r1.get (by decide), hI.x19]) (by rw [f1.get (by simp only [ENC]; omega) (by simp), hx32])
  have fr : Frame s0 t2 CsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
    simp only [or_false] at h; rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h)))
  have mem : ∀ A, A < 2 ^ 64 → ¬ CsW A → t2.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => fr.get hA hn
  have hT : TrialSt b A s0 i t2 := by
    refine ⟨?_, ?_, ?_, c32, ((hI.regs.trans r1).trans r2).mono (by decide), fr⟩
    · rw [r2.get (by decide), r1.get (by decide), hI.x19]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h16]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h24]
  refine ⟨t2, s1.trans s2, p2, (codeAt_k_123 hK).fetch _ p2, by rw [hT.reg (by decide), hpre.x5],
    hashArgs_const t2 ENC 64 EOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, h12, hT⟩
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine hashInput_toQ t2 _ 0 ENC (encodingInput_length _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [readWords_eight, wordsOf_encodingInput, hc]
  have nw : ∀ A, A = ENC ∨ A = ENC + 8 ∨ A = ENC + 40 ∨ A = ENC + 48 ∨ A = ENC + 56 → ¬ CsW A := by
    intro A hA; simp only [CsW, DigW, ENC, EOUT, DIGITS] at hA ⊢; omega
  rw [mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hT.h16, hT.h24, c32, mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hpre.m0, hpre.m8, hpre.z40, hpre.r48, hpre.r56]
theorem TrialSt.hash {A : CsArgs} {s0 t2 : MachineState} {i : Nat} (hT : TrialSt b A s0 i t2)
    (h12 : t2.getReg .x12 = BitVec.ofNat 64 EOUT) (a : BitVec 256) : TrialSt b A s0 i (writeHash t2 a) := by
  have fw := Frame.writeHash t2 a EOUT h12 (by decide)
  refine ⟨by rw [getReg_writeHash, hT.x19], ?_, ?_, ?_, ?_, ?_⟩
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h16]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h24]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.c32]
  · intro r hr; rw [getReg_writeHash]; exact hT.regs r hr
  · exact (hT.frame.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem cfFlag_lt (b : Nat) : cfFlag b < 256 := by unfold cfFlag; split <;> omega
theorem searchDecode_top (v : Digest) :
    T3.searchDecode 0 v = if T3.topCredit v < 9 then none else T3.decode 0 v := by
  unfold T3.searchDecode T3.encCredit T3.creditFloor
  simp
theorem cs_exhaust {A : CsArgs} {s0 t : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i = 2 ^ 22) :
    TBSim image sk t (0 * csT A.lay + csOk A.lay) (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg i 0)
      (CsPost image b A s0) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := cs113_spec hK t hI.pc i hI.hi hI.x19
  rw [if_pos hi] at p1
  have h8 : t1.getReg .x8 = BitVec.ofNat 64 A.lay.val := by
    rw [r1.get (by decide), hI.regs.get (by decide), hpre.x8]
  have fr1 : Frame s0 t1 CsW := (hI.frame.trans f1).mono (fun A _ h => by simp only [or_false] at h; exact h)
  have hcf1 : CfTableOK (cfFlag b) t1 :=
    hpre.cf.frame fr1 (by intro j hj hj'; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
  have prog : WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg i 0 = pure none := rfl
  rw [prog]
  by_cases hd : A.lay = 0 ∧ b = 543
  · have hfl : cfFlag b ≠ 0 := by unfold cfFlag; rw [if_pos hd.2]; omega
    obtain ⟨t2, s2, p2, g6, g7, g20, g25, g30, r2, f2⟩ := Credit.exhaust_dummy hK t1 p1
      (by rw [h8, hd.1]; rfl) (cfFlag b) (cfFlag_lt b) hcf1 hfl
    have ht2 : TableOK t2 := hpre.table.frame (fr1.trans f2 |>.mono (fun A _ h => by
      simp only [or_false] at h; exact h)) (by intro j hj; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
    obtain ⟨t3, s3, p3, dig3, r3, f3⟩ := topUnpack_spec hK t2 Credit.dummyDigest Credit.dummy_lt
      Credit.dummy_valid ht2 p2 g6 g7 g30 g20
    refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure ?_)).mono ?_ (fun _ _ h => h)
    · change (if A.lay = 0 ∧ b = 543 then DummyOut A s0 t3 else _)
      rw [if_pos hd]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [p3, r2.get (by decide), r1.get (by decide), hI.regs.get (by decide), hpre.x1, pcOf_and_not1]
      · intro j hj
        rw [dig3 j hj, ← Credit.dummy_digits]
        simp only [topDigits, getD_map_range hj]
      · obtain ⟨x, hx, hx32⟩ := hI.c32
        rw [f3.get (by unfold ENC; omega) (by unfold TopUnpack.Writes DIGITS ENC; omega),
          f2.get (by unfold ENC; omega) (by simp), f1.get (by unfold ENC; omega) (by simp), hx32,
          BitVec.toNat_ofNat]
        omega
      · exact (((hI.regs.trans r1).trans r2).trans r3).mono (by decide)
      · exact ((fr1.trans f2).trans f3).mono (fun A _ h => by
          rcases h with (h | h) | h
          · exact h
          · exact absurd h id
          · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
      · rw [r3.get (by decide), g25]; decide
    · unfold csOk; rw [if_pos hd.1]; omega
  · have hfl : A.lay.val ≠ 0 ∨ cfFlag b = 0 := by
      by_cases hz : A.lay = 0
      · right; unfold cfFlag; rw [if_neg (fun h => hd ⟨hz, h⟩)]
      · left; exact fun h => hz (Fin.ext h)
    obtain ⟨n, t2, hn, s2, p2, r2, f2⟩ := Credit.exhaust_fail hK t1 p1 A.lay.val A.lay.isLt h8 (cfFlag b)
      (cfFlag_lt b) hcf1 hfl
    obtain ⟨t3, s3, p3, h5, h10, hf⟩ := cs0_spec hK t2 p2
    refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure ?_)).mono ?_ (fun _ _ h => h)
    · change (if A.lay = 0 ∧ b = 543 then DummyOut A s0 t3 else _)
      rw [if_neg hd]
      exact ⟨p3, h5, h10, hf⟩
    · unfold csOk; split_ifs <;> omega
theorem cs_loop {A : CsArgs} {s0 : MachineState} (hK : KernAt image b) (hpre : CsPre b A s0) :
    ∀ F i t, i + F = 2 ^ 22 → CsInv b A s0 i t →
      TBSim image sk t (F * csT A.lay + csOk A.lay) (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg i F)
        (CsPost image b A s0) := by
  have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; rw [h]; rfl
  intro F
  induction F with
  | zero =>
    intro i t h hI
    exact cs_exhaust hK hpre hI (by omega)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 22 := by omega
    obtain ⟨t2, s2, p2, hf, h5, hv, hq, h12, hT⟩ := cs_answer hK hpre hI hi
    have prog : WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg i (F + 1) =
        (T3.shortHash (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i)) >>= fun answer =>
          match T3.searchDecode A.lay answer with
          | none => WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg (i + 1) F
          | some digits => pure (some (BitVec.ofNat 32 i, digits))) := rfl
    have ih' : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t (F * csT A.lay + csOk A.lay)
        (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg (i + 1) F) (CsPost image b A s0) :=
      fun t ht => ih (i + 1) t (by omega) ht
    rw [prog]
    refine (TBSim.steps s2 (TBSim.shortHash_bind hf h5 hv hq
      (W := F * csT A.lay + csOk A.lay + (csT A.lay - 18)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_encodingInput, Nat.succ_mul]; unfold csT; split_ifs <;> omega
    set v := a.extractLsb' 0 128 with hvdef
    have hT3 := hT.hash h12 a
    have p3 : (writeHash t2 a).pc = pcOf (b + 124) := by rw [pc_writeHash, p2, pcOf_add4]
    have hd := DigAt.writeHash_lo t2 a EOUT h12 (by decide)
    obtain ⟨t4, s4, p4, h6, h7, h25, r4, f4⟩ := cs124_spec hK (writeHash t2 a) p3 A.lay.val A.lay.isLt
      (by rw [hT3.reg (by decide), hpre.x8])
    rw [hd.1] at h6
    rw [hd.2] at h7
    have hT4 := hT3.step r4 (by decide) f4
    by_cases hlz : A.lay = 0
    · rw [if_pos (hl0.2 hlz)] at p4
      have hdec := decode_top_lookup v
      rw [← hlz] at hdec
      have hsd : T3.searchDecode A.lay v = if T3.topCredit v < 9 then none else T3.decode A.lay v := by
        rw [hlz]; exact searchDecode_top v
      rw [hsd]
      obtain ⟨t5, s5, p5, r5, f5⟩ := cs263_spec hK t4 p4 v h7
      have hT5 := hT4.step r5 (by decide) f5
      by_cases hr : v.toNat < 2 ^ 125
      · rw [if_pos hr] at p5
        obtain ⟨t6, s6, p6, h25', h30', r6, f6⟩ := topCheck_spec hK t5 v hr p5
          (by rw [r5.get (by decide), h6]) (by rw [r5.get (by decide), h7])
          (by rw [hT5.reg (by decide), hpre.x17, hlz]; rfl) (hT5.table hpre.table).sum
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : topLookupSum v = 128
        · rw [if_pos hs] at p6
          have hd' : T3.decode A.lay v = some (topDigits v) := by rw [hdec, if_pos ⟨hr, hs⟩]
          have hvalid := ((topLookupSum_eq_iff v).mp hs).1
          obtain ⟨t7, s7, p7, r7, f7⟩ := TopUnpack.jump_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          obtain ⟨t8, s8, p8, g20, r8, f8⟩ := Credit.credit_spec hK t7 p7 v hr hvalid (hT7.table hpre.table)
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
            (by rw [r7.get (by decide), h30'])
          have hT8 := hT7.step r8 (by decide) f8
          by_cases hc : T3.topCredit v < 9
          · rw [if_pos hc] at p8 s8
            rw [if_pos hc]
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_next hK hT8 p8 hi ih')).mono ?_
              (fun _ _ h => h)
            unfold csT; rw [if_pos hlz]; omega
          · rw [if_neg hc] at p8 s8
            rw [if_neg hc, hd']
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_top_success hK hpre hT8 p8 hi hlz v hr
              hvalid hd'
              (by rw [r8.get (by decide), r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
              (by rw [r8.get (by decide), r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
              (by rw [r8.get (by decide), r7.get (by decide), h30'])
              (by rw [r8.get (by decide), r7.get (by decide)]; simpa only [hs] using h25') (g20 hc))).mono ?_
              (fun _ _ h => h)
            unfold csT csOk; rw [if_pos hlz, if_pos hlz]; omega
        · rw [if_neg hs] at p6
          have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hs h.2)]
          rw [hd', ite_self]
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          unfold csT; rw [if_pos hlz]; omega
      · rw [if_neg hr] at p5
        have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hr h.1)]
        rw [hd', ite_self]
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        unfold csT; rw [if_pos hlz]; omega
    · rw [if_neg (fun h => hlz (hl0.1 h))] at p4
      rw [SigGolfCandidate.T3.Nonbinary.searchDecode_lower hlz v]
      have hdec := decode_low A.lay hlz v
      obtain ⟨t5, s5, p5, r5, f5⟩ := cs130_spec hK t4 p4 v h7
      have hT5 := hT4.step r5 (by decide) f5
      by_cases hr : v.toNat < 2 ^ 126
      · rw [if_pos hr] at p5
        obtain ⟨t6, s6, p6, h25', r6, f6⟩ := cs132_spec hK t5 p5 v (T3.target A.lay) (target_lt _)
          (by rw [r5.get (by decide), h6]) (by rw [r5.get (by decide), h7]) (by rw [r5.get (by decide), h25])
          (by rw [hT5.reg (by decide), hpre.x17])
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : (lowDigits v).sum ≤ T3.target A.lay ∧ T3.target A.lay - (lowDigits v).sum < 8
        · rw [if_pos hs] at p6
          obtain ⟨t7, s7, p7, r7, f7⟩ := cs262_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          have hd' : T3.decode A.lay v = some (lowDigits v ++ [T3.target A.lay - (lowDigits v).sum]) := by
            rw [hdec, if_pos ⟨hr, hs⟩]
          rw [hd']
          refine (TBSim.steps (((s4.trans s5).trans s6).trans s7) (cs_success hK hpre hT7 p7 hi hlz v _ _ hd' rfl hs.1
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
            (by rw [r7.get (by decide), h25']))).mono ?_ (fun _ _ h => h)
          unfold csT csOk; rw [if_neg hlz, if_neg hlz]; omega
        · rw [if_neg hs] at p6
          have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hs h.2)]
          rw [hd']
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          unfold csT; rw [if_neg hlz]; omega
      · rw [if_neg hr] at p5
        have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hr h.1)]
        rw [hd']
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        unfold csT; rw [if_neg hlz]; omega
theorem counterSearch_tbsim {A : CsArgs} {s0 : MachineState} (hK : KernAt image b) (hpre : CsPre b A s0) :
    TBSim image sk s0 (10 + 2 ^ 22 * csT A.lay + csOk A.lay)
      (WCT9.layerCounterSearch A.lay A.tree A.leaf A.msg 0 T3.counterLimit) (CsPost image b A s0) := by
  obtain ⟨t, st, pt, h16, h24, h19, rt, ft⟩ := cs103_spec hK s0 hpre.pc A.lay.val A.tree A.leaf A.lay.isLt
    hpre.htree hpre.hleaf hpre.x8 hpre.x9 hpre.x18
  have hI : CsInv b A s0 0 t := by
    refine ⟨pt, by norm_num, h19, h16, h24, ?_, rt.mono (by decide), ft.mono (fun A _ h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))⟩
    obtain ⟨x, hx, hx32⟩ := hpre.c32
    exact ⟨x, hx, by rw [ft.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), hx32]⟩
  have := TBSim.steps st (cs_loop (sk := sk) hK hpre (2 ^ 22) 0 t (by norm_num) hI)
  exact this.mono (le_of_eq (by ring)) (fun _ _ h => h)
end trial
structure FailedAt (b : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 2)
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
structure CsPreS (b : Nat) (s : MachineState) (lay : Layer) (tree leaf : Nat) (message : WCT9.LayerMsg) (ret : Nat) :
    Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 lay)
  htree : tree < 2 ^ 32
  hleaf : leaf < 2 ^ 32
  msg : DigAt s ENC (left message)
  c32 : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right message).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right message).extractLsb' 64 64
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
def DummyOutS (s : MachineState) (ret : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
    (t.getReg .x25).toNat ≤ 128
def CsPostS (b : Nat) (s : MachineState) (lay : Layer) (ret : Nat) :
    Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => if lay = 0 ∧ b = 543 then DummyOutS s ret t else FailedAt b t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧ (∃ v, T3.decode lay v = some ds) ∧
      (∀ i < T3.chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ T3.target lay
def csCostS (lay : Layer) : Nat := T3.counterLimit * (if lay = 0 then 412 else 160) + 2000
theorem CsPreS.toCsPre {b : Nat} {s : MachineState} {lay : Layer} {tree leaf : Nat} {msg : WCT9.LayerMsg} {ret : Nat}
    (h : CsPreS b s lay tree leaf msg ret) : CsPre b ⟨lay, tree, leaf, msg, ret⟩ s :=
  ⟨h.pc, h.x1, h.x5, h.x8, h.x9, h.x18, h.x17, h.x26, h.x27, h.htree, h.hleaf, h.msg.1, h.msg.2,
    ⟨_, h.c32, (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm⟩, h.z40, h.r48, h.r56, h.table, h.cf⟩
theorem counterSearch_spec {image : Image} {b : Nat} {sk : BitVec 256} (hK : KernAt image b)
    (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (ret : Nat)
    (h : CsPreS b s lay tree leaf msg ret) :
    TBSim image sk s (csCostS lay) (WCT9.layerCounterSearch lay tree leaf msg 0 T3.counterLimit) (CsPostS b s lay ret) := by
  refine (counterSearch_tbsim (sk := sk) hK h.toCsPre).mono ?_ (fun r t ht => ?_)
  · show 10 + 2 ^ 22 * csT lay + csOk lay ≤ 2 ^ 22 * (if lay = 0 then 412 else 160) + 2000
    unfold csT csOk
    split_ifs <;> omega
  · rcases r with _ | ⟨c, ds⟩
    · change (if lay = 0 ∧ b = 543 then DummyOut _ s t else _) at ht
      show (if lay = 0 ∧ b = 543 then DummyOutS s ret t else FailedAt b t)
      split_ifs at ht ⊢ with hd
      · obtain ⟨tpc, dig, c32, hr, hf, h25⟩ := ht
        exact ⟨tpc, by rw [hr.get (by decide), h.x5], dig, c32, hr, hf, h25⟩
      · exact ⟨ht.1, ht.2.1, ht.2.2.1⟩
    · obtain ⟨tpc, hc, _, h32, hdec, _, hdig, hr, hf, h25⟩ := ht
      refine ⟨tpc, ?_, hdec, hdig, ?_, hr, hf, h25⟩
      · rw [hr.get (by decide), h.x5]
      · rw [h32, BitVec.toNat_ofNat]
        omega
end SigGolfCandidate.T3M.Search.BC
end
end
