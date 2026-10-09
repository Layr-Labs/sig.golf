import SigGolfCandidate.T3M.Search.TopUnpack
import SigGolfCandidate.T3.Nonbinary.LowerLayout

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
def dumCode : List (BitVec 32) := [0x8100c93,2579,0xeedff06f]
def alignCode : List (BitVec 32) := [1281555,66985491,29573939,1282963,2347923]
def cfLayout : Rv.Layout := [(0,setupCode),(4,preCode),(7,loadCode),(8,postCode),(15,tailCode),(30,okCode),(32,h0Code),
  (33,luiCode),(34,flagCode),(35,beqCode),(36,ld1Code),(37,ld2Code),(38,dumCode),(41,alignCode)]
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
theorem code_align {image : Image} {b : Nat} (hK : KernAt image b) : CodeAt image (pcOf (b + 433)) alignCode := by
  simpa [Nat.add_assoc] using code_cf hK 13 41 alignCode (by kernel_rfl)
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
  refine ⟨_, symRun_sound (run_setup hK.2.1) (code_setup hK) s hpc (by simp [cs354.res, rv_simp]),
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
  refine ⟨_, symRun_sound (run_pre hK.2.1) (code_pre hK) s hpc (by simp [cp354.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cp354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [cp354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cp354.res, rv_simp]
theorem ok_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 422)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 363) ∧ t.getReg .x20 = 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ok hK.2.1) (code_ok hK) s hpc (by simp [co354.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [co354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [co354.res, rv_simp] <;> rfl
  · intro A _ _; simp [co354.res, rv_simp]
theorem dum_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 430)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 363) ∧ t.getReg .x20 = 0 ∧ t.getReg .x25 = 129#64 ∧
      RegsExcept s t [.x20, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_dum hK.2.1) (code_dum hK) s hpc (by simp [cd354.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cd354.res, rv_simp]
  · simp [cd354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [cd354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cd354.res, rv_simp]
theorem lui_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 425)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 426) ∧ t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_lui hK.2.1) (code_lui hK) s hpc (by simp [cl354.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cl354.res, rv_simp, TOP_DATA]
  · intro r hr; simp at hr; cases r <;> simp_all [cl354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cl354.res, rv_simp]
theorem h0_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 424)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lay = 0 then pcOf (b + 425) else pcOf (b + 0)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_h0 hK.2.1) (code_h0 hK) s hpc (by simp [ch354.res, rv_simp]),
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
  refine ⟨_, symRun_sound (run_beq hK.2.1) (code_beq hK) s hpc (by simp [cb354.res, rv_simp]),
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
  refine ⟨_, symRun_sound (run_post hK.2.1) (code_post hK) s hpc (by simp [cq354.res, rv_simp]),
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
  refine ⟨_, symRun_sound (run_tail hK.2.1) (code_tail hK) s hpc (by simp [ct354.res, rv_simp]), ?_, ?_, ?_, ?_⟩
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
private def cf (v : Digest) (i : Nat) : Nat := if T3.coreDigit 0 (T3.topFlip v) i = (if i < 51 then 3 else 2) then 1 else 0
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
    T3.topCredit (T3.topFlip v) = creditSum v 17 + tailCredit (v.toNat / 2 ^ 119) := by
  have h : T3.topCredit (T3.topFlip v) = ((List.range 54).map (cf v)).sum := rfl
  rw [h, show (54 : Nat) = 51 + 3 from rfl, range_three, List.map_append, List.sum_append,
    show (51 : Nat) = 3 * 17 from rfl, cf_groups v 17 le_rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  unfold cf tailCredit
  simp only [T3.coreDigit, T3.topCode_topFlip, if_pos rfl, show ¬ (51 : Nat) < 51 by omega, show ¬ (3 * 17 + 1 : Nat) < 51 by omega,
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
    (hvalid : T3.topRanksValid (T3.topFlip v) = true) (k : Nat) (hk : k < 17) (hI : LInv b s0 v k t) :
    ∃ u, Steps image t 11 11 u ∧ LInv b s0 v (k + 1) u := by
  have pc := hI.pc
  rw [if_pos hk] at pc
  obtain ⟨t1, s1, p1, a28, r1, f1⟩ := pre_spec hK t pc
  have rankbound : topRank v k < 125 := by
    have hv := (List.all_eq_true.mp hvalid) k (List.mem_range.mpr hk)
    simpa only [T3.topCode_topFlip, topRank] using of_decide_eq_true hv
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
    (hvalid : T3.topRanksValid (T3.topFlip v) = true) (hI : LInv b s0 v 0 t) (n : Nat) (hn : n ≤ 17) :
    ∃ u, Steps image t (11 * n) (11 * n) u ∧ LInv b s0 v n u := by
  induction n with
  | zero => exact ⟨t, Steps.refl t, hI⟩
  | succ n ih =>
      obtain ⟨u, hs, hu⟩ := ih (by omega)
      obtain ⟨w, hw, hwI⟩ := loop_body hK ht v hvalid n (by omega) hu
      exact ⟨w, (hs.trans hw).of_eq (by omega) (by omega), hwI⟩
theorem credit_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 392)) (v : Digest)
    (hv : v.toNat < 2 ^ 125) (hvalid : T3.topRanksValid (T3.topFlip v) = true) (ht : TableOK s)
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s (if T3.topCredit (T3.topFlip v) < 9 then 206 else 208) (if T3.topCredit (T3.topFlip v) < 9 then 206 else 208) t ∧
      t.pc = (if T3.topCredit (T3.topFlip v) < 9 then pcOf (b + 468) else pcOf (b + 363)) ∧
      (¬ T3.topCredit (T3.topFlip v) < 9 → t.getReg .x20 = 0) ∧
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
  by_cases hc : T3.topCredit (T3.topFlip v) < 9
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
      t.getReg .x20 = 0 ∧ t.getReg .x25 = 129#64 ∧ t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
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
theorem dummy_valid : T3.topRanksValid (T3.topFlip dummyDigest) = true := by decide
theorem dummy_digits : topDigits (T3.topFlip dummyDigest) = T3.dummyTop := by decide
end SigGolfCandidate.T3M.Search.Credit
end
section
namespace SigGolfCandidate.T3M.Search.Credit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}
sym_block ca354 := symRun {noAlias:=true} alignCode (pcOf (354+433)) 200
sym_block ca543 := symRun {noAlias:=true} alignCode (pcOf (543+433)) 200
theorem run_align {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} alignCode (pcOf (b+433)) 200 =
      some ⟨ca354.res.st,.c (pcOf (b+438)),ca354.res.stop,ca354.res.steps,ca354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact ca354.trans (congrArg some (by kernel_rfl))
  · exact ca543.trans (congrArg some (by kernel_rfl))
theorem getLsbD_add_one_zero (x : BitVec 64) : (x + 1#64).getLsbD 0 = !x.getLsbD 0 := by
  simp only [BitVec.getLsbD, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.testBit_zero, Nat.testBit_zero]
  have h : (x.toNat + 1 % 2 ^ 64) % 2 ^ 64 % 2 = (x.toNat + 1) % 2 := by
    rw [show 1 % 2 ^ 64 = 1 from rfl, Nat.mod_mod_of_dvd _ (by norm_num)]
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h0 | h0 <;> simp [Nat.add_mod, h0]
theorem align_lo (v : Digest) (hv : T3.lowerSpare v) :
    v.extractLsb' 0 64 ^^^ (v.extractLsb' 64 64 + 1#64) <<< 63 =
      (BitVec.ofNat 128 (T3.lowerWord v)).extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, T3.testBit_lowerWord]
  simp only [hj, decide_true, Bool.true_and, show j < 128 from by omega]
  by_cases h63 : j = 63
  · subst h63
    have hb := getLsbD_add_one_zero (v.extractLsb' 64 64)
    simp only [Nat.sub_self] at hb ⊢
    rw [hb, BitVec.getLsbD_extractLsb']
    have h63 : v.toNat.testBit 63 = true := by
      unfold T3.lowerSpare at hv
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, hv.1]
      rfl
    simp [BitVec.getElem_eq_testBit_toNat, h63]
  · have hlt : j < 63 := by omega
    simp [hlt, BitVec.getLsbD]
    intro _; omega
theorem align_hi (v : Digest) :
    v.extractLsb' 64 64 <<< 1 >>> 2 =
      (BitVec.ofNat 128 (T3.lowerWord v)).extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, T3.testBit_lowerWord]
  simp only [hj, decide_true, Bool.true_and, show 64 + j < 128 from by omega, show ¬ 64 + j < 63 from by omega,
    if_false]
  by_cases h62 : j < 62
  · simp [show 2 + j < 64 from by omega, show ¬ 2 + j < 1 from by omega, show 64 + j < 126 from by omega,
      BitVec.getLsbD, show 1 + j < 64 from by omega, show 64 + (1 + j) = 64 + j + 1 from by omega]
  · simp [show ¬ 2 + j < 64 from by omega, show ¬ 64 + j < 126 from by omega]
theorem align_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 433)) (v : Digest)
    (hv : T3.lowerSpare v) (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf (b + 438) ∧
      t.getReg .x6 = (BitVec.ofNat 128 (T3.lowerWord v)).extractLsb' 0 64 ∧
      t.getReg .x7 = (BitVec.ofNat 128 (T3.lowerWord v)).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_align hK.2.1) (code_align hK) s hpc (by simp [ca354.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [Result.toState_getReg, ca354.res]
    simp only [rv_simp, h6, h7]
    rw [← align_lo v hv]
    rfl
  · simp only [Result.toState_getReg, ca354.res]
    simp only [rv_simp, h7]
    rw [← align_hi v]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [ca354.res, rv_simp] <;> rfl
  · intro A _ _; simp [ca354.res, rv_simp]
end SigGolfCandidate.T3M.Search.Credit
end
