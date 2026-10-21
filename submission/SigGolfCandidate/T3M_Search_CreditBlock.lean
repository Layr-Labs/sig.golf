import SigGolfCandidate.T3M_Search_TopUnpack
import SigGolfCandidate.T3_Nonbinary_LowerLayout

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
def tailCode : List (BitVec 32) := [0x757e13,0xffae0e13,1981971,29754931,0x355513,0x757e13,0xffae0e13,1981971,29754931,0x355513,0xffa50e13,1981971,29754931,9846291,0xa0e1e63]
def okCode : List (BitVec 32) := [2579,0xf11ff06f]
def h0Code : List (BitVec 32) := [0x960410e3]
/-- Campaign T51: expand (b = 354) word b + 425 is `j b` (top exhaustion rejects); sign keeps `lui t5, 0xfff`. -/
def luiCode (b : Nat) : List (BitVec 32) := if b = 354 then [0x95dff06f] else [0xffff37]
def flagCode : List (BitVec 32) := [662654467]
def beqCode : List (BitVec 32) := [0x940e0ae3]
def ld1Code : List (BitVec 32) := [663696131]
def ld2Code : List (BitVec 32) := [672084867]
/-- Campaign T51: sign (b = 543) words b + 430, 431 are `li t3, 2 ; j 21230` (dead dummy path into the T51 unpacker). -/
def dumCode (b : Nat) : List (BitVec 32) :=
  if b = 354 then [0x8100c93,2579,0xeedff06f] else [0x200e13,0x4811306f,0xeedff06f]
def alignCode : List (BitVec 32) := [1281555,66985491,29573939,1282963,2347923]
def cfLayout (b : Nat) : Rv.Layout := [(0,setupCode),(4,preCode),(7,loadCode),(8,postCode),(15,tailCode),(30,okCode),
  (32,h0Code),(33,luiCode b),(34,flagCode),(35,beqCode),(36,ld1Code),(37,ld2Code),(38,dumCode b),(41,alignCode)]
theorem cfLayout_ok (b : Nat) : layoutOk 0 (cfLayout b) = true := by
  by_cases hb : b = 354 <;> simp only [cfLayout, luiCode, dumCode, hb, if_true, if_false] <;> decide +kernel
theorem cfLayout_code {b : Nat} (hb : b = 354 ∨ b = 543) : topSeg392 b = layoutCode (cfLayout b) := by
  rcases hb with rfl | rfl <;> decide +kernel
theorem code_cf {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (i o : Nat) (seg : List (BitVec 32))
    (h : (cfLayout b)[i]? = some (o, seg)) : CodeAt image (pcOf (b + 392 + o)) seg := by
  have hc := codeAt_top392 hK
  rw [cfLayout_code hK.2.1] at hc
  exact codeAt_sublayout hc (cfLayout_ok b) (i := i) (o := o) (seg := seg) h
theorem code_setup {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 392)) setupCode := by
  simpa using code_cf hK 0 0 setupCode (by rfl)
theorem code_pre {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 396)) preCode := by
  simpa [Nat.add_assoc] using code_cf hK 1 4 preCode (by rfl)
theorem code_load {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 399)) loadCode := by
  simpa [Nat.add_assoc] using code_cf hK 2 7 loadCode (by rfl)
theorem code_post {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 400)) postCode := by
  simpa [Nat.add_assoc] using code_cf hK 3 8 postCode (by rfl)
theorem code_tail {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 407)) tailCode := by
  simpa [Nat.add_assoc] using code_cf hK 4 15 tailCode (by rfl)
theorem code_ok {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 422)) okCode := by
  simpa [Nat.add_assoc] using code_cf hK 5 30 okCode (by rfl)
theorem code_h0 {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 424)) h0Code := by
  simpa [Nat.add_assoc] using code_cf hK 6 32 h0Code (by rfl)
theorem code_lui {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 425)) (luiCode b) := by
  simpa [Nat.add_assoc] using code_cf hK 7 33 (luiCode b) (by rfl)
theorem code_flag {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 426)) flagCode := by
  simpa [Nat.add_assoc] using code_cf hK 8 34 flagCode (by rfl)
theorem code_beq {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 427)) beqCode := by
  simpa [Nat.add_assoc] using code_cf hK 9 35 beqCode (by rfl)
theorem code_ld1 {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 428)) ld1Code := by
  simpa [Nat.add_assoc] using code_cf hK 10 36 ld1Code (by rfl)
theorem code_ld2 {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 429)) ld2Code := by
  simpa [Nat.add_assoc] using code_cf hK 11 37 ld2Code (by rfl)
theorem code_dum {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 430)) (dumCode b) := by
  simpa [Nat.add_assoc] using code_cf hK 12 38 (dumCode b) (by rfl)
theorem code_align {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) : CodeAt image (pcOf (b + 433)) alignCode := by
  simpa [Nat.add_assoc] using code_cf hK 13 41 alignCode (by rfl)
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
sym_block cl543 := symRun {noAlias:=true} (luiCode 543) (pcOf (543+425)) 200
sym_block cj354 := symRun {noAlias:=true} (luiCode 354) (pcOf (354+425)) 200
sym_block cb354 := symRun {noAlias:=true} beqCode (pcOf (354+427)) 200
sym_block cb543 := symRun {noAlias:=true} beqCode (pcOf (543+427)) 200
def beqEnd (b : Nat) : E := rebase cb354.res.pc (pcOf (b+0)) (pcOf (b+428))
theorem run_beq {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} beqCode (pcOf (b+427)) 200 =
      some ⟨cb354.res.st,beqEnd b,cb354.res.stop,cb354.res.steps,cb354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact cb354.trans (congrArg some (by kernel_rfl))
  · exact cb543.trans (congrArg some (by kernel_rfl))
sym_block cd354 := symRun {noAlias:=true} (dumCode 354) (pcOf (354+430)) 200
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
theorem setup_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 392)) :
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
theorem pre_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 396)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 399) ∧
      t.getReg .x28 = ((s.getReg .x10 &&& 127#64) <<< 2) + s.getReg .x30 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_pre hK.2.1) (code_pre hK) s hpc (by simp [cp354.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cp354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [cp354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cp354.res, rv_simp]
theorem ok_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 422)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 363) ∧ t.getReg .x20 = 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ok hK.2.1) (code_ok hK) s hpc (by simp [co354.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [co354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [co354.res, rv_simp] <;> rfl
  · intro A _ _; simp [co354.res, rv_simp]
/-- The legacy dummy fallback (expand only; the sign words are the T51 ones). -/
theorem dum_spec {rewardCondition : Prop} (hK : KernAt image 354 rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (354 + 430)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (354 + 363) ∧ t.getReg .x20 = 0 ∧ t.getReg .x25 = 129#64 ∧
      RegsExcept s t [.x20, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound cd354 (code_dum hK) s hpc (by simp [cd354.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cd354.res, rv_simp]
  · simp [cd354.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [cd354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cd354.res, rv_simp]
theorem lui_spec {rewardCondition : Prop} (hK : KernAt image 543 rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (543 + 425)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (543 + 426) ∧ t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound cl543 (code_lui hK) s hpc (by simp [cl543.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [cl543.res, rv_simp, TOP_DATA]
  · intro r hr; simp at hr; cases r <;> simp_all [cl543.res, rv_simp] <;> rfl
  · intro A _ _; simp [cl543.res, rv_simp]
/-- Campaign T51: the expand top exhaustion jumps straight to the reject (`j 354`). -/
theorem j425_spec {rewardCondition : Prop} (hK : KernAt image 354 rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (354 + 425)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (354 + 0) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound cj354 (code_lui hK) s hpc (by simp [cj354.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro r hr; cases r <;> simp_all [cj354.res, rv_simp] <;> rfl
  · intro A _ _; simp [cj354.res, rv_simp]
theorem h0_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 424)) (lay : Nat)
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
theorem beq_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 427)) (f : Nat)
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
theorem load_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 399)) (A : Nat)
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
theorem flag_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 426))
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
theorem ld_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 428))
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
theorem post_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 400)) (n : Nat)
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
/-- Campaign T8D (NF17): credits of the three raw radix-8 digits above bit 119 (`X = v / 2^119`): chain 53 at
`X % 8`, chain 51 at `X / 8 % 8`, chain 52 at `X / 64`; credit digit 6. -/
def tailCredit (X : Nat) : Nat :=
  (if X % 8 = 6 then 1 else 0) + (if X / 8 % 8 = 6 then 1 else 0) + (if X / 64 = 6 then 1 else 0)
theorem eq6_ofNat (d : Nat) (hd : d < 8) :
    (if ((BitVec.ofNat 64 d) - 6#64).ult 1#64 = true then 1#64 else 0#64) =
      BitVec.ofNat 64 (if d = 6 then 1 else 0) := by
  interval_cases d <;> decide
theorem eq6_ofNat' (d : Nat) (hd : d < 8) :
    (if ((BitVec.ofNat 64 d) + 18446744073709551610#64).ult 1#64 = true then 1#64 else 0#64) =
      BitVec.ofNat 64 (if d = 6 then 1 else 0) := by
  interval_cases d <;> decide
theorem tail_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 407)) (X C : Nat)
    (hX : X < 512) (hC : C < 64) (h10 : s.getReg .x10 = BitVec.ofNat 64 X)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 C) :
    ∃ t, Steps image s 15 15 t ∧
      t.pc = (if C + tailCredit X < 9 then pcOf (b + 468) else pcOf (b + 422)) ∧
      t.getReg .x12 = BitVec.ofNat 64 (C + tailCredit X) ∧
      RegsExcept s t [.x10, .x12, .x28] ∧ Frame s t (fun _ => False) := by
  have e1 : BitVec.ofNat 64 X >>> 3 = BitVec.ofNat 64 (X / 8) := by
    rw [ofNat_shr X 3 (by omega)]; norm_num
  have e2 : BitVec.ofNat 64 (X / 8) >>> 3 = BitVec.ofNat 64 (X / 64) := by
    rw [ofNat_shr _ 3 (by omega), Nat.div_div_eq_div_mul]; norm_num
  have ht3 : tailCredit X ≤ 3 := by unfold tailCredit; split_ifs <;> omega
  have hsum : C + (if X % 8 = 6 then 1 else 0) + (if X / 8 % 8 = 6 then 1 else 0) + (if X / 64 = 6 then 1 else 0) =
      C + tailCredit X := by unfold tailCredit; omega
  refine ⟨_, symRun_sound (run_tail hK.2.1) (code_tail hK) s hpc (by simp [ct354.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [tailEnd, rebase, ct354.res, rv_simp, E.eval, CmpOp.eval, BinOp.eval, h10, h12, e1, e2]
    first
      | rw [eq6_ofNat _ (by omega), eq6_ofNat _ (by omega), eq6_ofNat _ (by omega)]
      | rw [eq6_ofNat' _ (by omega), eq6_ofNat' _ (by omega), eq6_ofNat' _ (by omega)]
    rw [ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat, hsum]
    have hlt : (BitVec.ofNat 64 (C + tailCredit X)).ult 9#64 = decide (C + tailCredit X < 9) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hlt]
    by_cases h : C + tailCredit X < 9 <;> simp [h]
  · simp [ct354.res, rv_simp, h10, h12, e1, e2]
    first
      | rw [eq6_ofNat _ (by omega), eq6_ofNat _ (by omega), eq6_ofNat _ (by omega)]
      | rw [eq6_ofNat' _ (by omega), eq6_ofNat' _ (by omega), eq6_ofNat' _ (by omega)]
    rw [ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat, hsum]
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
private def cf (v : Digest) (i : Nat) : Nat := if T3.coreDigit 0 (T3.topFlip v) i = (if i < 51 then 3 else 6) then 1 else 0
private theorem range_three (n : Nat) : List.range (n + 3) = List.range n ++ [n, n + 1, n + 2] := by
  simp [List.range_succ]
theorem rankCredit_digits (r : Nat) :
    rankCredit r = (if rankDigit r 0 = 3 then 1 else 0) + (if rankDigit r 1 = 3 then 1 else 0) +
      (if rankDigit r 2 = 3 then 1 else 0) := by
  simp [rankCredit, rankDigit] <;> rfl

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
theorem flagOK_byte (s : MachineState) (flag : Nat) (hf : flag < 256) (h : CfFlagOK flag s) :
    (s.getByte (BitVec.ofNat 64 (TOP_DATA + 631))).zeroExtend 64 = BitVec.ofNat 64 flag := by
  unfold CfFlagOK at h; rw [h]; exact zext_ofNat8 flag hf
/-- Exhaustion of the counter window (T51: the expand top branch jumps straight to the reject). Needs only the choice
flag byte (`CfFlagOK`; a `CfTableOK` coerces). -/
theorem exhaust_fail {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 424)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (flag : Nat) (hf : flag < 256)
    (hcf : CfFlagOK flag s) (hfl : lay ≠ 0 ∨ flag = 0) :
    ∃ n t, n ≤ 4 ∧ Steps image s n n t ∧ t.pc = pcOf (b + 0) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ := h0_spec hK s hpc lay hl h8
  by_cases hz : lay = 0
  · rw [if_pos hz] at p0
    have hf0 : flag = 0 := by rcases hfl with h | h; exact absurd hz h; exact h
    rcases hK.2.1 with rfl | rfl
    · obtain ⟨t1, s1, p1, r1, f1⟩ := j425_spec hK t0 p0
      exact ⟨2, t1, by omega, (s0.trans s1).of_eq rfl rfl, p1, (r0.trans r1).mono (by decide),
        (f0.trans f1).mono (by simp)⟩
    · obtain ⟨t1, s1, p1, g30, r1, f1⟩ := lui_spec hK t0 p0
      obtain ⟨t2, s2, p2, g28, r2, f2⟩ := flag_spec hK t1 p1 g30
      have hcf2 : CfFlagOK flag t1 := hcf.frame (W := fun _ => False) ((f0.trans f1).mono (by simp))
        (by intro j _ _ h; exact h)
      rw [flagOK_byte t1 flag hf hcf2] at g28
      obtain ⟨t3, s3, p3, r3, f3⟩ := beq_spec hK t2 p2 flag hf g28
      rw [if_pos hf0] at p3
      refine ⟨4, t3, le_rfl, (s0.trans (s1.trans (s2.trans s3))).of_eq (by norm_num) (by norm_num), p3, ?_, ?_⟩
      · exact (((r0.trans r1).trans r2).trans r3).mono (by decide)
      · exact (((f0.trans f1).trans f2).trans f3).mono (by simp)
  · rw [if_neg hz] at p0
    exact ⟨1, t0, by omega, s0, p0, r0.mono (by decide), f0⟩

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
theorem align_spec {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (s : MachineState) (hpc : s.pc = pcOf (b + 433)) (v : Digest)
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

/-! ## T51 digit unpacker (campaign T51, stream SIGNA; `t51kernel.py` build_unpack)
Two segments: `A` (112 words) at `U_ENTRY` and `B` (54 words) at `uc`; between them the instance's split hook (sign:
the jump at 21342, `uj = 1`; expand: contiguous, `uj = 0`). Writes `DIGITS[0..50]` and returns through `ra`. -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem bv_remu (n r : Nat) (hn : n < 2 ^ 64) (hr : 0 < r) (hr' : r < 2 ^ 64) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 r) = BitVec.ofNat 64 (n % r) := by
  unfold rv64_remu
  have h0 : (BitVec.ofNat 64 r == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [h0]; simp only [Bool.false_eq_true, if_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, toNat_ofNat_lt hn, toNat_ofNat_lt hr', toNat_ofNat_lt (by
    exact lt_of_le_of_lt (Nat.mod_le _ _) hn)]
theorem bv_divu (n r : Nat) (hn : n < 2 ^ 64) (hr : 0 < r) (hr' : r < 2 ^ 64) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 r) = BitVec.ofNat 64 (n / r) := by
  unfold rv64_divu
  have h0 : (BitVec.ofNat 64 r == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [h0]; simp only [Bool.false_eq_true, if_false]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, toNat_ofNat_lt hn, toNat_ofNat_lt hr', toNat_ofNat_lt (by
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
theorem trunc8 (x : Nat) : (BitVec.ofNat 64 x).truncate 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
/-- One division step `op x29|x28, x28, R` followed by `sb t4, o(a0)`: `rd := op n r`, byte `o` := `x29`. -/
theorem divsb {image : Image} {s : MachineState} {pc : Word} {w0 w1 : BitVec 32} {R rd : Reg}
    {i0 : Instruction} {op : BinOp} {f1 : BitVec 12} {o r n m : Nat}
    (hc : CodeAt image pc [w0, w1]) (hpc : s.pc = pc)
    (hd0 : decodeInstruction w0 = some i0) (hc0 : classify i0 = some (.alu rd op (.reg .x28) (.reg R)))
    (hcy : instructionCycles i0 = 4)
    (hop : op.eval (BitVec.ofNat 64 n) (BitVec.ofNat 64 r) = BitVec.ofNat 64 m) (hm : m < 2 ^ 64)
    (hrd : rd = .x28 ∨ rd = .x29)
    (hd1 : decodeInstruction w1 = some (.base (.SB .x10 .x29 f1)))
    (ho1 : signExtend12 f1 = BitVec.ofNat 64 o) (ho : o < 64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 DIGITS) (hRv : s.getReg R = BitVec.ofNat 64 r) (hR : R ≠ rd)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 n)
    (h29 : rd = .x28 → s.getReg .x29 = BitVec.ofNat 64 m) :
    ∃ t, Steps image s 2 5 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg rd = BitVec.ofNat 64 m ∧
      t.getByte (BitVec.ofNat 64 (DIGITS + o)) = BitVec.ofNat 8 m ∧
      (∀ B, B < 2 ^ 64 → B ≠ DIGITS + o → t.getByte (BitVec.ofNat 64 B) = s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [rd] ∧ Frame s t (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := by
  have hD : DIGITS = 0x20420 := rfl
  have hd : ∀ {pc' : Word} {w : BitVec 32} {ws : List (BitVec 32)}, CodeAt image pc' (w :: ws) →
      CodeAt image pc' [w] := fun {pc'} {w} {ws} h => by
    have h' : CodeAt image pc' ([] ++ [w] ++ ws) := by simpa using h
    simpa using CodeAt.drop_prefix h'
  have c1 := hc.tail
  have gne : ∀ (x : MachineState) (r q : Reg) (v : Word), q ≠ r → (x.setReg r v).getReg q = x.getReg q :=
    fun x r q v h => MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have geq : ∀ (x : MachineState) (r : Reg) (v : Word), r ≠ .x0 → (x.setReg r v).getReg r = v :=
    fun x r v h => MachineState.getReg_setReg_eq h
  have hrd0 : rd ≠ .x0 := by rcases hrd with rfl | rfl <;> decide
  have st0 := step_alu (hd hc) hpc hd0 hc0
  generalize hu1 : (s.setReg rd (op.eval ((Src.reg .x28).eval s) ((Src.reg R).eval s))).setPC
    (s.pc + 4) = u1 at st0
  have g1d : u1.getReg rd = BitVec.ofNat 64 m := by
    rw [← hu1, getReg_setPC', geq _ _ _ hrd0]
    show op.eval (s.getReg .x28) (s.getReg R) = _
    rw [h28, hRv, hop]
  have g1 : ∀ q, q ≠ rd → u1.getReg q = s.getReg q := fun q hq => by rw [← hu1, getReg_setPC', gne _ _ _ _ hq]
  have g29 : u1.getReg .x29 = BitVec.ofNat 64 m := by
    rcases hrd with h | h
    · subst h; rw [g1 .x29 (by decide), h29 rfl]
    · subst h; exact g1d
  have p1 : u1.pc = pc + 4 := by rw [← hu1]; show s.pc + 4 = _; rw [hpc]
  have b1 : ∀ a, u1.getByte a = s.getByte a := fun a => by rw [← hu1, getByte_setPC, getByte_setReg]
  have m1 : ∀ a, u1.getMem a = s.getMem a := fun a => by rw [← hu1, getMem_setPC']; cases rd <;> rfl
  have h10' : u1.getReg .x10 = BitVec.ofNat 64 DIGITS := by
    rw [g1 .x10 (by rcases hrd with rfl | rfl <;> decide), h10]
  have a1 : u1.getReg .x10 + signExtend12 f1 = BitVec.ofNat 64 (DIGITS + o) := by
    rw [h10', ho1, ofNat_add_ofNat]
  have v1 : accessValid (u1.getReg .x10 + signExtend12 f1) 1 = true := by
    rw [a1]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show DIGITS + o < 2 ^ 64 by omega)]
    omega
  have st1 := steps_sb (hd c1) p1 hd1 v1
  generalize hu2 : (u1.setByte (u1.getReg .x10 + signExtend12 f1) ((u1.getReg .x29).truncate 8)).setPC
    (u1.pc + 4) = u2 at st1
  have g2 : ∀ q, u2.getReg q = u1.getReg q := fun q => by rw [← hu2, getReg_setPC', getReg_setByte]
  refine ⟨u2, (st0.trans st1).of_eq rfl (by rw [hcy]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hu2]; show u1.pc + 4 = _; rw [p1]
  · rw [g2, g1d]
  · rw [← hu2, getByte_setPC, a1, g29, trunc8, getByte_setByte _ _ _ (by omega) (by omega), if_pos rfl]
  · intro B hB hne
    rw [← hu2, getByte_setPC, a1, getByte_setByte _ _ _ (by omega) hB, if_neg hne, b1]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [g2, g1 q hq]
  · intro A hA hn
    rw [← hu2, getMem_setPC', a1, getMem_setByte _ _ _ (by omega) hA _ (by unfold DIGITS at hn; omega), m1]
theorem take2 {image : Image} {pc : Word} {a b : BitVec 32} {rest : List (BitVec 32)}
    (h : CodeAt image pc (a :: b :: rest)) : CodeAt image pc [a, b] := by
  have h' : CodeAt image pc ([] ++ [a, b] ++ rest) := by simpa using h
  simpa using CodeAt.drop_prefix h'
/-- A digit triple `remu t4,t3,R ; sb o ; [split] ; divu t3,t3,R ; remu t4,t3,R ; sb o+1 ; divu t4,t3,R ; sb o+2`
(radix `r` in `R`), with an `m`-step transfer `pcA + 8 → pcB` between the first two words and the rest. -/
theorem trip {image : Image} {s : MachineState} {pcA pcB : Word} {w0 w1 w2 w3 w4 w5 w6 : BitVec 32} {R : Reg}
    {f1 f2 f3 : BitVec 12} {o r n m : Nat}
    (hcA : CodeAt image pcA [w0, w1]) (hcB : CodeAt image pcB [w2, w3, w4, w5, w6]) (hpc : s.pc = pcA)
    (hmid : ∀ x : MachineState, x.pc = pcA + 4 + 4 → ∃ y, Steps image x m m y ∧ y.pc = pcB ∧ RegsExcept x y [] ∧
      Frame x y (fun _ => False))
    (hd0 : decodeInstruction w0 = some (.base (.REMU .x29 .x28 R)))
    (hd1 : decodeInstruction w1 = some (.base (.SB .x10 .x29 f1)))
    (hd2 : decodeInstruction w2 = some (.base (.DIVU .x28 .x28 R)))
    (hd3 : decodeInstruction w3 = some (.base (.REMU .x29 .x28 R)))
    (hd4 : decodeInstruction w4 = some (.base (.SB .x10 .x29 f2)))
    (hd5 : decodeInstruction w5 = some (.base (.DIVU .x29 .x28 R)))
    (hd6 : decodeInstruction w6 = some (.base (.SB .x10 .x29 f3)))
    (hR : R ≠ .x0 ∧ R ≠ .x28 ∧ R ≠ .x29 ∧ R ≠ .x10)
    (ho1 : signExtend12 f1 = BitVec.ofNat 64 o) (ho2 : signExtend12 f2 = BitVec.ofNat 64 (o + 1))
    (ho3 : signExtend12 f3 = BitVec.ofNat 64 (o + 2)) (ho : o + 2 < 64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 DIGITS) (hRv : s.getReg R = BitVec.ofNat 64 r) (hr : 0 < r ∧ r < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    ∃ t, Steps image s (7 + m) (19 + m) t ∧ t.pc = pcB + 4 + 4 + 4 + 4 + 4 ∧
      t.getByte (BitVec.ofNat 64 (DIGITS + o)) = BitVec.ofNat 8 (n % r) ∧
      t.getByte (BitVec.ofNat 64 (DIGITS + (o + 1))) = BitVec.ofNat 8 (n / r % r) ∧
      t.getByte (BitVec.ofNat 64 (DIGITS + (o + 2))) = BitVec.ofNat 8 (n / r / r) ∧
      (∀ B, B < 2 ^ 64 → ¬ (DIGITS + o ≤ B ∧ B < DIGITS + o + 3) →
        t.getByte (BitVec.ofNat 64 B) = s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := by
  have hD : DIGITS = 0x20420 := rfl
  have hd : ∀ {pc' : Word} {w : BitVec 32} {ws : List (BitVec 32)}, CodeAt image pc' (w :: ws) →
      CodeAt image pc' [w] := fun {pc'} {w} {ws} h => by
    have h' : CodeAt image pc' ([] ++ [w] ++ ws) := by simpa using h
    simpa using CodeAt.drop_prefix h'
  have hR' : r < 2 ^ 64 := by omega
  have hnr : n % r < 2 ^ 64 := by have := Nat.mod_lt n hr.1; omega
  have hn1 : n / r < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  have hn1r : n / r % r < 2 ^ 64 := by have := Nat.mod_lt (n / r) hr.1; omega
  have hn2 : n / r / r < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hn1
  -- first pair (remu, sb o)
  obtain ⟨u1, s1, p1, x1, b1, bf1, r1, f1'⟩ := divsb (rd := .x29) (op := .remu) (m := n % r) hcA hpc hd0 rfl rfl
    (by show rv64_remu _ _ = _; rw [bv_remu _ _ hn hr.1 hR']) hnr (Or.inr rfl) hd1 ho1 (by omega) h10 hRv hR.2.2.1
    h28 (fun h => by cases h)
  obtain ⟨u2, s2, p2, r2, f2⟩ := hmid u1 p1
  -- divu t3, t3, R
  have st3 := step_alu (hd hcB) p2 hd2 rfl
  have hcy3 : instructionCycles (.base (.DIVU .x28 .x28 R)) = 4 := rfl
  rw [hcy3] at st3
  generalize hu3 : (u2.setReg .x28 (BinOp.divu.eval ((Src.reg .x28).eval u2) ((Src.reg R).eval u2))).setPC
    (u2.pc + 4) = u3 at st3
  have gne : ∀ (x : MachineState) (r q : Reg) (v : Word), q ≠ r → (x.setReg r v).getReg q = x.getReg q :=
    fun x r q v h => MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have u2R : ∀ q, q ≠ .x29 → u2.getReg q = s.getReg q := fun q hq => by
    rw [r2 q (by simp), r1 q (by simp [hq])]
  have g3 : u3.getReg .x28 = BitVec.ofNat 64 (n / r) := by
    rw [← hu3, getReg_setPC', MachineState.getReg_setReg_eq (by decide)]
    show rv64_divu (u2.getReg .x28) (u2.getReg R) = _
    rw [u2R .x28 (by decide), u2R R hR.2.2.1, h28, hRv, bv_divu _ _ hn hr.1 hR']
  have r3 : ∀ q, q ≠ .x28 → u3.getReg q = u2.getReg q := fun q hq => by rw [← hu3, getReg_setPC', gne _ _ _ _ hq]
  have p3 : u3.pc = pcB + 4 := by rw [← hu3]; show u2.pc + 4 = _; rw [p2]
  have b3 : ∀ a, u3.getByte a = u2.getByte a := fun a => by rw [← hu3, getByte_setPC, getByte_setReg]
  have m3 : ∀ a, u3.getMem a = u2.getMem a := fun a => by rw [← hu3, getMem_setPC']; rfl
  have cB1 := take2 hcB.tail
  have cB3 := hcB.tail.tail.tail
  -- (remu, sb o+1)
  obtain ⟨u4, s4, p4, x4, b4, bf4, r4, f4⟩ := divsb (rd := .x29) (op := .remu) (m := n / r % r) cB1 p3 hd3 rfl rfl
    (by show rv64_remu _ _ = _; rw [bv_remu _ _ hn1 hr.1 hR']) hn1r (Or.inr rfl) hd4 ho2 (by omega)
    (by rw [r3 .x10 (by decide), u2R .x10 (by decide), h10]) (by rw [r3 R hR.2.1, u2R R hR.2.2.1, hRv])
    hR.2.2.1 g3 (fun h => by cases h)
  -- (divu t4, sb o+2)
  obtain ⟨u5, s5, p5, x5, b5, bf5, r5, f5⟩ := divsb (rd := .x29) (op := .divu) (m := n / r / r) cB3
    (by rw [p4]) hd5 rfl rfl
    (by show rv64_divu _ _ = _; rw [bv_divu _ _ hn1 hr.1 hR']) hn2 (Or.inr rfl) hd6 ho3 (by omega)
    (by rw [r4 .x10 (by decide), r3 .x10 (by decide), u2R .x10 (by decide), h10])
    (by rw [r4 R (by simp [hR.2.2.1]), r3 R hR.2.1, u2R R hR.2.2.1, hRv]) hR.2.2.1
    (by rw [r4 .x28 (by decide), g3]) (fun h => by cases h)
  have hall : ∀ B, B < 2 ^ 64 → ¬ (DIGITS + o ≤ B ∧ B < DIGITS + o + 3) →
      u5.getByte (BitVec.ofNat 64 B) = s.getByte (BitVec.ofNat 64 B) := by
    intro B hB hn'
    rw [bf5 B hB (by omega), bf4 B hB (by omega), b3, f2.getByte hB (fun h => h), bf1 B hB (by omega)]
  refine ⟨u5, ((((s1.trans s2).trans st3).trans s4).trans s5).of_eq (by omega) (by omega), ?_, ?_, ?_, ?_, hall, ?_, ?_⟩
  · exact p5
  · rw [bf5 _ (by omega) (by omega), bf4 _ (by omega) (by omega), b3, f2.getByte (by omega) (fun h => h), b1]
  · rw [bf5 _ (by omega) (by omega), b4]
  · exact b5
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [r5 q (by simp [hq.2]), r4 q (by simp [hq.2]), r3 q hq.1, r2 q (by simp), r1 q (by simp [hq.2])]
  · intro A hA hn'
    rw [f5.get hA hn', f4.get hA hn', m3, f2.get hA (fun h => h), f1'.get hA hn']
end SigGolfCandidate.T3M.Search.T51
end

section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def kUp1 : List (BitVec 32) := [0x20537,0x42050513]
def kUsb : List (BitVec 32) := [0x3c50923]
def kUp2 : List (BitVec 32) := [0x600f13,0x500593,0x3f35c93,0x139e93,0x1dcecb3]
def kUg0 : List (BitVec 32) := [0xff37e13,0xfd8e0e13]
def kUs0a : List (BitVec 32) := [0x3ee7eb3,0x1d50023]
def kUs0b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d500a3,0x3ee5eb3,0x1d50123]
def kUg1 : List (BitVec 32) := [0x835e13,0xffe7e13]
def kUs1a : List (BitVec 32) := [0x3ee7eb3,0x1d501a3]
def kUs1b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d50223,0x3ee5eb3,0x1d502a3]
def kUg2 : List (BitVec 32) := [0x1035e13,0xffe7e13]
def kUs2a : List (BitVec 32) := [0x3ee7eb3,0x1d50323]
def kUs2b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d503a3,0x3ee5eb3,0x1d50423]
def kUg3 : List (BitVec 32) := [0x1835e13,0xffe7e13]
def kUs3a : List (BitVec 32) := [0x3ee7eb3,0x1d504a3]
def kUs3b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d50523,0x3ee5eb3,0x1d505a3]
def kUg4 : List (BitVec 32) := [0x2035e13,0xffe7e13]
def kUs4a : List (BitVec 32) := [0x3ee7eb3,0x1d50623]
def kUs4b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d506a3,0x3ee5eb3,0x1d50723]
def kUg5 : List (BitVec 32) := [0x2835e13,0xffe7e13]
def kUs5a : List (BitVec 32) := [0x3ee7eb3,0x1d507a3]
def kUs5b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d50823,0x3ee5eb3,0x1d508a3]
def kUg6 : List (BitVec 32) := [0x3035e13,0xffe7e13]
def kUs6a : List (BitVec 32) := [0x3ee7eb3,0x1d50923]
def kUs6b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d509a3,0x3ee5eb3,0x1d50a23]
def kUg7 : List (BitVec 32) := [0x303de13,0xffe7e13]
def kUs7a : List (BitVec 32) := [0x3ee7eb3,0x1d50aa3]
def kUs7b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d50b23,0x3ee5eb3,0x1d50ba3]
def kUg8 : List (BitVec 32) := [0x383de13]
def kUs8a : List (BitVec 32) := [0x3ee7eb3,0x1d50c23]
def kUs8b : List (BitVec 32) := [0x3ee5e33,0x3ee7eb3,0x1d50ca3,0x3ee5eb3,0x1d50d23]
def kUg9 : List (BitVec 32) := [0x7fcfe13,0x7fe4e13]
def kUs9a : List (BitVec 32) := [0x2be7eb3,0x1d50da3]
def kUs9b : List (BitVec 32) := [0x2be5e33,0x2be7eb3,0x1d50e23,0x2be5eb3,0x1d50ea3]
def kUg10 : List (BitVec 32) := [0x7cde13,0x7fe7e13,0x7fe4e13]
def kUs10a : List (BitVec 32) := [0x2be7eb3,0x1d50f23]
def kUs10b : List (BitVec 32) := [0x2be5e33,0x2be7eb3,0x1d50fa3,0x2be5eb3,0x3d50023]
def kUg11 : List (BitVec 32) := [0xecde13,0x7fe7e13,0x7fe4e13]
def kUs11a : List (BitVec 32) := [0x2be7eb3,0x3d500a3]
def kUs11b : List (BitVec 32) := [0x2be5e33,0x2be7eb3,0x3d50123,0x2be5eb3,0x3d501a3]
def kUg12 : List (BitVec 32) := [0x15cde13,0x7fe7e13,0x7fe4e13]
def kUs12a : List (BitVec 32) := [0x2be7eb3,0x3d50223]
def kUs12b : List (BitVec 32) := [0x2be5e33,0x2be7eb3,0x3d502a3,0x2be5eb3,0x3d50323]
def kUg13 : List (BitVec 32) := [0x1ccde13,0x7fe7e13,0x7fe4e13]
def kUs13a : List (BitVec 32) := [0x2be7eb3,0x3d503a3]
def kUs13b : List (BitVec 32) := [0x2be5e33,0x2be7eb3,0x3d50423,0x2be5eb3,0x3d504a3]
def kUg14 : List (BitVec 32) := [0x23cde13,0x7fe7e13,0x7fe4e13]
def kUs14a : List (BitVec 32) := [0x2be7eb3,0x3d50523]
def kUs14b : List (BitVec 32) := [0x2be5e33,0x2be7eb3,0x3d505a3,0x2be5eb3,0x3d50623]
def kUg15 : List (BitVec 32) := [0x2acde13,0x7fe7e13,0x7fe4e13]
def kUs15a : List (BitVec 32) := [0x2be7eb3,0x3d506a3]
def kUs15b : List (BitVec 32) := [0x2be5e33,0x2be7eb3,0x3d50723,0x2be5eb3,0x3d507a3]
def kUr7 : List (BitVec 32) := [0x3835e13,0x7fe7e13,0x7fe4e13,0x700f13]
def kUr7a : List (BitVec 32) := [0x3ee7eb3,0x3d50823]
def kUr7b : List (BitVec 32) := [0x3ee5eb3,0x3d508a3]
def kUret : List (BitVec 32) := [0x8067]
/-- Fine layout of the first unpacker segment (112 words at `U_ENTRY`). -/
def uLA : Rv.Layout := [(0, kUp1), (2, kUsb), (3, kUp2), (8, kUg0), (10, kUs0a), (12, kUs0b), (17, kUg1), (19, kUs1a), (21, kUs1b), (26, kUg2), (28, kUs2a), (30, kUs2b), (35, kUg3), (37, kUs3a), (39, kUs3b), (44, kUg4), (46, kUs4a), (48, kUs4b), (53, kUg5), (55, kUs5a), (57, kUs5b), (62, kUg6), (64, kUs6a), (66, kUs6b), (71, kUg7), (73, kUs7a), (75, kUs7b), (80, kUg8), (81, kUs8a), (83, kUs8b), (88, kUg9), (90, kUs9a), (92, kUs9b), (97, kUg10), (100, kUs10a), (102, kUs10b), (107, kUg11), (110, kUs11a)]
/-- Fine layout of the second unpacker segment (54 words at `uc`). -/
def uLB : Rv.Layout := [(0, kUs11b), (5, kUg12), (8, kUs12a), (10, kUs12b), (15, kUg13), (18, kUs13a), (20, kUs13b), (25, kUg14), (28, kUs14a), (30, kUs14b), (35, kUg15), (38, kUs15a), (40, kUs15b), (45, kUr7), (49, kUr7a), (51, kUr7b), (53, kUret)]
def uCodeA : List (BitVec 32) := layoutCode uLA
def uCodeB : List (BitVec 32) := layoutCode uLB
theorem uLA_ok : layoutOk 0 uLA = true := by decide +kernel
theorem uLB_ok : layoutOk 0 uLB = true := by decide +kernel
abbrev uRegs : List Reg := [.x10, .x11, .x25, .x28, .x29, .x30]
/-- The unpacker is installed for instance `P` (segment `A` at `ub`, segment `B` at `uc`, `uj`-step transfer). -/
structure T51UAt (image : Image) (P : KInst) : Prop where
  codeA : CodeAt image (pcOf P.ub) uCodeA
  codeB : CodeAt image (pcOf P.uc) uCodeB
  ubLt : P.ub + 112 < 2 ^ 40
  ucLt : P.uc + 54 < 2 ^ 40
  hJ : ∀ s : MachineState, s.pc = pcOf (P.ub + 112) → ∃ t, Steps image s P.uj P.uj t ∧ t.pc = pcOf P.uc ∧
    RegsExcept s t [] ∧ Frame s t (fun _ => False)
theorem codeAt_ua {image : Image} {P : KInst} (h : T51UAt image P) (i : Nat) {o : Nat} {seg : List (BitVec 32)}
    (hi : uLA[i]? = some (o, seg)) : CodeAt image (pcOf (P.ub + o)) seg :=
  codeAt_sublayout h.codeA uLA_ok hi
theorem codeAt_ub {image : Image} {P : KInst} (h : T51UAt image P) (i : Nat) {o : Nat} {seg : List (BitVec 32)}
    (hi : uLB[i]? = some (o, seg)) : CodeAt image (pcOf (P.uc + o)) seg :=
  codeAt_sublayout h.codeB uLB_ok hi
sym_block kUp1Run := symRun { noAlias := true } kUp1 0 10
theorem run_kUp1 (pc : Word) : symRun { noAlias := true } kUp1 pc 10 =
    some ⟨kUp1Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUp1_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUp1) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x10 = BitVec.ofNat 64 DIGITS ∧ RegsExcept s t [.x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUp1 pc) hc s hpc (by simp [kUp1Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUp1Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUp1Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUp1Run.res, rv_simp]
sym_block kUp2Run := symRun { noAlias := true } kUp2 0 10
theorem run_kUp2 (pc : Word) : symRun { noAlias := true } kUp2 pc 10 =
    some ⟨kUp2Run.res.st, .c (pc + 4 + 4 + 4 + 4 + 4), .endOfCode, 5, 5⟩ := by
  rfl
theorem kUp2_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUp2) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc + 4 + 4 + 4 + 4 + 4 ∧ (t.getReg .x30 = 6#64 ∧ t.getReg .x11 = 5#64 ∧ t.getReg .x25 = (s.getReg .x6 >>> 63) ||| (s.getReg .x7 <<< 1)) ∧ RegsExcept s t [.x11, .x25, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUp2 pc) hc s hpc (by simp [kUp2Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUp2Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUp2Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUp2Run.res, rv_simp]
sym_block kUg0Run := symRun { noAlias := true } kUg0 0 10
theorem run_kUg0 (pc : Word) : symRun { noAlias := true } kUg0 pc 10 =
    some ⟨kUg0Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg0_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg0) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 &&& 255#64) - 40#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg0 pc) hc s hpc (by simp [kUg0Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg0Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg0Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg0Run.res, rv_simp]
sym_block kUg7Run := symRun { noAlias := true } kUg7 0 10
theorem run_kUg7 (pc : Word) : symRun { noAlias := true } kUg7 pc 10 =
    some ⟨kUg7Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg7_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg7) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x7 >>> 48) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg7 pc) hc s hpc (by simp [kUg7Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg7Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg7Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg7Run.res, rv_simp]
sym_block kUg8Run := symRun { noAlias := true } kUg8 0 10
theorem run_kUg8 (pc : Word) : symRun { noAlias := true } kUg8 pc 10 =
    some ⟨kUg8Run.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by
  rfl
theorem kUg8_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg8) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x28 = s.getReg .x7 >>> 56 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg8 pc) hc s hpc (by simp [kUg8Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg8Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg8Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg8Run.res, rv_simp]
sym_block kUg9Run := symRun { noAlias := true } kUg9 0 10
theorem run_kUg9 (pc : Word) : symRun { noAlias := true } kUg9 pc 10 =
    some ⟨kUg9Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg9_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg9) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x25 &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg9 pc) hc s hpc (by simp [kUg9Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg9Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg9Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg9Run.res, rv_simp]
sym_block kUr7Run := symRun { noAlias := true } kUr7 0 10
theorem run_kUr7 (pc : Word) : symRun { noAlias := true } kUr7 pc 10 =
    some ⟨kUr7Run.res.st, .c (pc + 4 + 4 + 4 + 4), .endOfCode, 4, 4⟩ := by
  rfl
theorem kUr7_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUr7) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pc + 4 + 4 + 4 + 4 ∧ (t.getReg .x28 = ((s.getReg .x6 >>> 56) &&& 127#64) ^^^ 127#64 ∧ t.getReg .x30 = 7#64) ∧ RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUr7 pc) hc s hpc (by simp [kUr7Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUr7Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUr7Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUr7Run.res, rv_simp]
sym_block kUg1Run := symRun { noAlias := true } kUg1 0 10
theorem run_kUg1 (pc : Word) : symRun { noAlias := true } kUg1 pc 10 =
    some ⟨kUg1Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg1_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg1) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 8) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg1 pc) hc s hpc (by simp [kUg1Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg1Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg1Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg1Run.res, rv_simp]
sym_block kUg2Run := symRun { noAlias := true } kUg2 0 10
theorem run_kUg2 (pc : Word) : symRun { noAlias := true } kUg2 pc 10 =
    some ⟨kUg2Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg2_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg2) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 16) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg2 pc) hc s hpc (by simp [kUg2Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg2Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg2Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg2Run.res, rv_simp]
sym_block kUg3Run := symRun { noAlias := true } kUg3 0 10
theorem run_kUg3 (pc : Word) : symRun { noAlias := true } kUg3 pc 10 =
    some ⟨kUg3Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg3_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg3) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 24) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg3 pc) hc s hpc (by simp [kUg3Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg3Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg3Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg3Run.res, rv_simp]
sym_block kUg4Run := symRun { noAlias := true } kUg4 0 10
theorem run_kUg4 (pc : Word) : symRun { noAlias := true } kUg4 pc 10 =
    some ⟨kUg4Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg4_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg4) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 32) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg4 pc) hc s hpc (by simp [kUg4Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg4Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg4Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg4Run.res, rv_simp]
sym_block kUg5Run := symRun { noAlias := true } kUg5 0 10
theorem run_kUg5 (pc : Word) : symRun { noAlias := true } kUg5 pc 10 =
    some ⟨kUg5Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg5_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg5) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 40) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg5 pc) hc s hpc (by simp [kUg5Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg5Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg5Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg5Run.res, rv_simp]
sym_block kUg6Run := symRun { noAlias := true } kUg6 0 10
theorem run_kUg6 (pc : Word) : symRun { noAlias := true } kUg6 pc 10 =
    some ⟨kUg6Run.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by
  rfl
theorem kUg6_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg6) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧ t.getReg .x28 = (s.getReg .x6 >>> 48) &&& 255#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg6 pc) hc s hpc (by simp [kUg6Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg6Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg6Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg6Run.res, rv_simp]
sym_block kUg10Run := symRun { noAlias := true } kUg10 0 10
theorem run_kUg10 (pc : Word) : symRun { noAlias := true } kUg10 pc 10 =
    some ⟨kUg10Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem kUg10_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg10) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 7) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg10 pc) hc s hpc (by simp [kUg10Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg10Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg10Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg10Run.res, rv_simp]
sym_block kUg11Run := symRun { noAlias := true } kUg11 0 10
theorem run_kUg11 (pc : Word) : symRun { noAlias := true } kUg11 pc 10 =
    some ⟨kUg11Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem kUg11_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg11) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 14) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg11 pc) hc s hpc (by simp [kUg11Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg11Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg11Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg11Run.res, rv_simp]
sym_block kUg12Run := symRun { noAlias := true } kUg12 0 10
theorem run_kUg12 (pc : Word) : symRun { noAlias := true } kUg12 pc 10 =
    some ⟨kUg12Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem kUg12_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg12) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 21) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg12 pc) hc s hpc (by simp [kUg12Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg12Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg12Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg12Run.res, rv_simp]
sym_block kUg13Run := symRun { noAlias := true } kUg13 0 10
theorem run_kUg13 (pc : Word) : symRun { noAlias := true } kUg13 pc 10 =
    some ⟨kUg13Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem kUg13_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg13) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 28) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg13 pc) hc s hpc (by simp [kUg13Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg13Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg13Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg13Run.res, rv_simp]
sym_block kUg14Run := symRun { noAlias := true } kUg14 0 10
theorem run_kUg14 (pc : Word) : symRun { noAlias := true } kUg14 pc 10 =
    some ⟨kUg14Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem kUg14_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg14) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 35) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg14 pc) hc s hpc (by simp [kUg14Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg14Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg14Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg14Run.res, rv_simp]
sym_block kUg15Run := symRun { noAlias := true } kUg15 0 10
theorem run_kUg15 (pc : Word) : symRun { noAlias := true } kUg15 pc 10 =
    some ⟨kUg15Run.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by
  rfl
theorem kUg15_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUg15) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧ t.getReg .x28 = ((s.getReg .x25 >>> 42) &&& 127#64) ^^^ 127#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_kUg15 pc) hc s hpc (by simp [kUg15Run.res, rv_simp]), by simp [rv_simp], ?_, ?_, ?_⟩
  · simp only [rv_simp, kUg15Run.res, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] <;> first | rfl | (exact ⟨trivial, trivial, trivial⟩) | (exact ⟨trivial, trivial⟩) | (refine ⟨?_, ?_, ?_⟩ <;> rfl) | (refine ⟨?_, ?_⟩ <;> rfl) | skip
  · intro r hr; simp at hr; cases r <;> simp_all [kUg15Run.res, rv_simp] <;> rfl
  · intro A _ _; simp [kUg15Run.res, rv_simp]
end SigGolfCandidate.T3M.Search.T51
end

section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! ### Unpacker values and digits -/
theorem fld_lo (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    (v.extractLsb' 0 64 >>> S) &&& BitVec.ofNat 64 (2 ^ w - 1) = BitVec.ofNat 64 (v.toNat / 2 ^ S % 2 ^ w) := by
  rw [bv_and_mask _ w (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, lo_field v S w h]
theorem fld_hi (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    (v.extractLsb' 64 64 >>> S) &&& BitVec.ofNat 64 (2 ^ w - 1) = BitVec.ofNat 64 (v.toNat / 2 ^ (64 + S) % 2 ^ w) := by
  rw [bv_and_mask _ w (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hi_field v S w h]
theorem fld_t5 (v : Digest) (S w : Nat) (h : S + w ≤ 64) :
    (BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 2 ^ 64) >>> S) &&& BitVec.ofNat 64 (2 ^ w - 1) =
      BitVec.ofNat 64 (v.toNat / 2 ^ (63 + S) % 2 ^ w) := by
  rw [bv_and_mask _ w (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_ofNat_lt (t5_lt v),
    t5_field v S w h]
theorem xor127 (x : Nat) (hx : x < 128) : BitVec.ofNat 64 x ^^^ 127#64 = BitVec.ofNat 64 (127 - x) := by
  apply BitVec.eq_of_toNat_eq
  have h : ∀ x < 128, x ^^^ 127 = 127 - x := by decide
  rw [BitVec.toNat_xor, toNat_ofNat_lt (show x < 2 ^ 64 by omega), toNat_ofNat_lt (show 127 < 2 ^ 64 by norm_num),
    toNat_ofNat_lt (show 127 - x < 2 ^ 64 by omega), h x hx]
theorem r6Rank_0 (v : Digest) : T3.r6Rank v 0 = v.toNat % 256 - 40 := by
  unfold T3.r6Rank; simp [r6Raw_eq v 0 (by norm_num), T3.r6Shift]
theorem r6Rank_g (v : Digest) (g : Nat) (h1 : 1 ≤ g) (h6 : g ≤ 6) : T3.r6Rank v g = v.toNat / 2 ^ (8 * g) % 256 := by
  unfold T3.r6Rank
  rw [if_neg (by omega), r6Raw_eq v g (by omega)]
  simp [T3.r6Shift, show g < 7 by omega]
theorem r6Rank_7 (v : Digest) : T3.r6Rank v 7 = v.toNat / 2 ^ 112 % 256 := by
  unfold T3.r6Rank; rw [if_neg (by norm_num), r6Raw_eq v 7 (by norm_num)]; rfl
theorem r6Rank_8 (v : Digest) : T3.r6Rank v 8 = v.toNat / 2 ^ 120 % 256 := by
  unfold T3.r6Rank; rw [if_neg (by norm_num), r6Raw_eq v 8 (by norm_num)]; rfl
theorem r6Rank_lt (v : Digest) (g : Nat) : T3.r6Rank v g < 256 := by
  unfold T3.r6Rank T3.r6Raw; split_ifs <;> omega
theorem r5Rank_lt (v : Digest) (q : Nat) : T3.r5Rank v q < 128 := by
  unfold T3.r5Rank; omega
theorem r7Rank_lt (v : Digest) : T3.r7Rank v < 128 := by
  unfold T3.r7Rank; omega
theorem g0_valid {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    40 ≤ v.toNat % 256 := by
  have hv := (decode_top_eq hd).1
  obtain ⟨h6, _, _⟩ := valid_groups hv
  have := h6 0 (by norm_num)
  unfold T3.r6Valid at this
  rw [r6Raw_eq v 0 (by norm_num)] at this
  simpa [T3.r6Shift] using this
theorem udig6 {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) (g m : Nat)
    (hm : m = 3 * g) (hg : g < 9) :
    ds.getD m 0 = T3.r6Rank v g % 6 ∧ ds.getD (m + 1) 0 = T3.r6Rank v g / 6 % 6 ∧
      ds.getD (m + 2) 0 = T3.r6Rank v g / 6 / 6 := by
  subst hm
  have hv := (decode_top_eq hd).1
  obtain ⟨h6, _, _⟩ := valid_groups hv
  have hr := ((gIdx_r6 v g hg).2 (h6 g hg)).2
  have c0 := coreDigit_r6g v g 0 hg (by norm_num)
  have c1 := coreDigit_r6g v g 1 hg (by norm_num)
  have c2 := coreDigit_r6g v g 2 hg (by norm_num)
  simp only [add_zero, pow_zero, Nat.div_one, pow_one] at c0 c1 c2
  refine ⟨?_, ?_, ?_⟩
  · rw [ds_getD_data hd _ (by omega), c0]
  · rw [ds_getD_data hd _ (by omega), c1]
  · rw [ds_getD_data hd _ (by omega), c2]; norm_num; omega
theorem udig5 {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) (q m : Nat)
    (hm : m = 3 * q) (hq : 9 ≤ q ∧ q < 16) :
    ds.getD m 0 = T3.r5Rank v q % 5 ∧ ds.getD (m + 1) 0 = T3.r5Rank v q / 5 % 5 ∧
      ds.getD (m + 2) 0 = T3.r5Rank v q / 5 / 5 := by
  subst hm
  have hv := (decode_top_eq hd).1
  obtain ⟨_, h5, _⟩ := valid_groups hv
  have hr := h5 q hq.1 hq.2
  have c0 := coreDigit_r5g v q 0 hq (by norm_num)
  have c1 := coreDigit_r5g v q 1 hq (by norm_num)
  have c2 := coreDigit_r5g v q 2 hq (by norm_num)
  simp only [add_zero, pow_zero, Nat.div_one, pow_one] at c0 c1 c2
  refine ⟨?_, ?_, ?_⟩
  · rw [ds_getD_data hd _ (by omega), c0]
  · rw [ds_getD_data hd _ (by omega), c1]
  · rw [ds_getD_data hd _ (by omega), c2]; norm_num; omega
theorem udig7 {v : Digest} {ds : List Nat} (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    ds.getD 48 0 = T3.r7Rank v % 7 ∧ ds.getD 49 0 = T3.r7Rank v / 7 := by
  have hv := (decode_top_eq hd).1
  obtain ⟨_, _, h7⟩ := valid_groups hv
  refine ⟨?_, ?_⟩
  · rw [ds_getD_data hd 48 (by norm_num), coreDigit_48]
  · rw [ds_getD_data hd 49 (by norm_num), coreDigit_49]; omega
/-! ### Digit-buffer invariant -/
def DInv (t : MachineState) (ds : List Nat) (m : Nat) : Prop :=
  ∀ j, (j < m ∨ j = 50) → t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)
theorem DInv.frame {t t' : MachineState} {ds : List Nat} {m : Nat} (h : DInv t ds m) (hm : m ≤ 50)
    (hf : Frame t t' (fun _ => False)) : DInv t' ds m := by
  intro j hj
  have hD : DIGITS = 0x20420 := rfl
  have hj50 : j ≤ 50 := by rcases hj with hj | hj <;> omega
  rw [hf.getByte (by omega) (fun h => h)]
  exact h j hj
theorem DInv.step {t t' : MachineState} {ds : List Nat} {m r n : Nat} (h : DInv t ds m) (hm : m + 3 ≤ 50)
    (hb0 : t'.getByte (BitVec.ofNat 64 (DIGITS + m)) = BitVec.ofNat 8 (n % r))
    (hb1 : t'.getByte (BitVec.ofNat 64 (DIGITS + (m + 1))) = BitVec.ofNat 8 (n / r % r))
    (hb2 : t'.getByte (BitVec.ofNat 64 (DIGITS + (m + 2))) = BitVec.ofNat 8 (n / r / r))
    (hfr : ∀ B, B < 2 ^ 64 → ¬ (DIGITS + m ≤ B ∧ B < DIGITS + m + 3) →
      t'.getByte (BitVec.ofNat 64 B) = t.getByte (BitVec.ofNat 64 B))
    (hdig : ds.getD m 0 = n % r ∧ ds.getD (m + 1) 0 = n / r % r ∧ ds.getD (m + 2) 0 = n / r / r) :
    DInv t' ds (m + 3) := by
  intro j hj
  have hD : DIGITS = 0x20420 := rfl
  by_cases hjm : j < m ∨ j = 50
  · have hj50 : j ≤ 50 := by rcases hjm with hj | hj <;> omega
    have hn : ¬ (DIGITS + m ≤ DIGITS + j ∧ DIGITS + j < DIGITS + m + 3) := by
      rcases hjm with hj | hj <;> omega
    rw [hfr _ (by omega) hn]; exact h j hjm
  · have : j = m ∨ j = m + 1 ∨ j = m + 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [hb0, hdig.1]
    · rw [hb1, hdig.2.1]
    · rw [hb2, hdig.2.2]
theorem ret_spec {image : Image} {pc : Word} (hc : CodeAt image pc kUret) (s : MachineState) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = s.getReg .x1 &&& 18446744073709551614#64 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
  have hrun : symRun { noAlias := true } kUret pc 10 =
      some ⟨SymState.init, .bin .and (.reg .x1) (.c 18446744073709551614#64), .jump, 1, 1⟩ := rfl
  refine ⟨_, symRun_sound hrun hc s hpc (by simp [rv_simp, SymState.init]), ?_, ?_, ?_⟩
  · simp only [rv_simp]
  · intro r _; simp only [rv_simp, SymState.init]; cases r <;> rfl
  · intro A _ _; simp only [rv_simp, SymState.init]
theorem mid0 {image : Image} (k : Nat) :
    ∀ x : MachineState, x.pc = pcOf k + 4 + 4 → ∃ y, Steps image x 0 0 y ∧ y.pc = pcOf (k + 2) ∧
      RegsExcept x y [] ∧ Frame x y (fun _ => False) :=
  fun x hx => ⟨x, Steps.refl _, by rw [hx, pcOf_4, pcOf_4], RegsExcept.refl _ _, Frame.refl _ _⟩
/-- The T51 unpacker: from `U_ENTRY` with a decoded word `v` in `x6`, `x7` and its checksum digit in `x28`, write the
51 digits to `DIGITS` and return through `ra`. -/
theorem unpack {image : Image} {P : KInst} (hU : T51UAt image P) (u : MachineState) (hpc : u.pc = pcOf P.ub)
    (v : Digest) (ds : List Nat) (hd : WCT9.CanonicalPolicy.decode 0 v = some ds)
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h28 : u.getReg .x28 = BitVec.ofNat 64 (ds.getD 50 0)) :
    ∃ t, Steps image u (166 + P.uj) (364 + P.uj) t ∧ t.pc = u.getReg .x1 &&& ~~~1#64 ∧
      (∀ j < 51, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept u t uRegs ∧ Frame u t (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := by
  have hub := hU.ubLt
  have huc := hU.ucLt
  have hD : DIGITS = 0x20420 := rfl
  have hvl := v.isLt
  obtain ⟨c1, s1, p1, x10_1, r1, f1⟩ := kUp1_spec (codeAt_ua hU 0 rfl) u hpc
  have p1' : c1.pc = pcOf (P.ub + 2) := by rw [p1, pcOf_4, pcOf_4]
  have v50 : accessValid (c1.getReg .x10 + signExtend12 (50#12)) 1 = true := by
    rw [x10_1, show signExtend12 (50#12) = BitVec.ofNat 64 50 from rfl, ofNat_add_ofNat]
    simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt (show DIGITS + 50 < 2 ^ 64 by omega)]
    omega
  have sb50 := steps_sb (rs1 := .x10) (rs2 := .x28) (off := 50#12) (codeAt_ua hU 1 rfl) p1' rfl v50
  generalize hc2 : (c1.setByte (c1.getReg .x10 + signExtend12 (50#12)) ((c1.getReg .x28).truncate 8)).setPC
    (c1.pc + 4) = c2 at sb50
  have a50 : c1.getReg .x10 + signExtend12 (50#12) = BitVec.ofNat 64 (DIGITS + 50) := by
    rw [x10_1, show signExtend12 (50#12) = BitVec.ofNat 64 50 from rfl, ofNat_add_ofNat]
  have p2 : c2.pc = pcOf (P.ub + 3) := by rw [← hc2]; show c1.pc + 4 = _; rw [p1', pcOf_4]
  have r2 : RegsExcept c1 c2 [] := fun q _ => by rw [← hc2, getReg_setPC', getReg_setByte]
  have b2 : c2.getByte (BitVec.ofNat 64 (DIGITS + 50)) = BitVec.ofNat 8 (ds.getD 50 0) := by
    rw [← hc2, getByte_setPC, a50, getByte_setByte _ _ _ (by omega) (by omega), if_pos rfl,
      r1 .x28 (by decide), h28, trunc8]
  have f2 : Frame c1 c2 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := by
    intro A hA hn
    rw [← hc2, getMem_setPC', a50, getMem_setByte _ _ _ (by omega) hA _ (by omega)]
  obtain ⟨c3, s3, p3, ⟨x30_3, x11_3, x25_3⟩, r3, f3⟩ := kUp2_spec (codeAt_ua hU 2 rfl) c2 p2
  have c3x6 : c3.getReg .x6 = v.extractLsb' 0 64 := by
    rw [r3 .x6 (by decide), r2 .x6 (by decide), r1 .x6 (by decide), h6]
  have c3x7 : c3.getReg .x7 = v.extractLsb' 64 64 := by
    rw [r3 .x7 (by decide), r2 .x7 (by decide), r1 .x7 (by decide), h7]
  have c3x10 : c3.getReg .x10 = BitVec.ofNat 64 DIGITS := by rw [r3 .x10 (by decide), r2 .x10 (by decide), x10_1]
  have c3x25 : c3.getReg .x25 = BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 2 ^ 64) := by
    rw [x25_3, r2 .x6 (by decide), r2 .x7 (by decide), r1 .x6 (by decide), r1 .x7 (by decide), h6, h7, t5_val]
  have c3x30 : c3.getReg .x30 = BitVec.ofNat 64 6 := x30_3
  have c3x11 : c3.getReg .x11 = BitVec.ofNat 64 5 := x11_3
  have Dc : DInv c3 ds 0 := by
    intro j hj
    have hj' : j = 50 := by omega
    subst hj'
    rw [f3.getByte (by omega) (fun h => h), b2]
  have Rc : RegsExcept c3 c3 [.x28, .x29] := RegsExcept.refl _ _
  have Fc : Frame c3 c3 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) := Frame.refl _ _
  have p3' : c3.pc = pcOf (P.ub + 8) := by rw [p3]; simp only [pcOf_4]
  -- group 0
  obtain ⟨a0, sa0, pa0, va, ra0, fa0⟩ := kUg0_spec (codeAt_ua hU 3 rfl) c3 p3'
  have Ra0 : RegsExcept c3 a0 [.x28, .x29] := (Rc.trans ra0).mono (by decide)
  have n0 : a0.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 0) := by
    rw [va, Rc .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      bv_and_mask _ 8 (by norm_num), lo_mod v 8 (by norm_num), show (40#64 : Word) = BitVec.ofNat 64 40 from rfl,
      bv_sub _ _ (by have := g0_valid hd; omega) (by omega), r6Rank_0]
    try norm_num
  have pa0' : a0.pc = pcOf (P.ub + 10) := by rw [pa0]; simp only [pcOf_4]
  obtain ⟨t0, st0, pt0, b0_0, b1_0, b2_0, bf0, rt0, ft0⟩ :=
    trip (R := .x30) (o := 0) (r := 6) (codeAt_ua hU 4 rfl) (codeAt_ua hU 5 rfl) pa0' (mid0 (P.ub + 10))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra0 .x10 (by decide), c3x10])
      (by rw [Ra0 .x30 (by decide), c3x30]) (by norm_num) n0 (by have := r6Rank_lt v 0; omega)
  have D0 : DInv t0 ds (0 + 3) :=
    DInv.step (Dc.frame (by norm_num) fa0) (by norm_num) b0_0 b1_0 b2_0 bf0 (udig6 hd 0 0 rfl (by norm_num))
  have R0 : RegsExcept c3 t0 [.x28, .x29] := (Ra0.trans rt0).mono (by decide)
  have F0 : Frame c3 t0 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((Fc.trans fa0).trans ft0).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt0' : t0.pc = pcOf (P.ub + 17) := by rw [pt0]; simp only [pcOf_4]
  -- group 1
  obtain ⟨a1, sa1, pa1, va, ra1, fa1⟩ := kUg1_spec (codeAt_ua hU 6 rfl) t0 pt0'
  have Ra1 : RegsExcept c3 a1 [.x28, .x29] := (R0.trans ra1).mono (by decide)
  have n1 : a1.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 1) := by
    rw [va, R0 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 8 8 (by norm_num), r6Rank_g v 1 (by norm_num) (by norm_num)]
    try norm_num
  have pa1' : a1.pc = pcOf (P.ub + 19) := by rw [pa1]; simp only [pcOf_4]
  obtain ⟨t1, st1, pt1, b0_1, b1_1, b2_1, bf1, rt1, ft1⟩ :=
    trip (R := .x30) (o := 3) (r := 6) (codeAt_ua hU 7 rfl) (codeAt_ua hU 8 rfl) pa1' (mid0 (P.ub + 19))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra1 .x10 (by decide), c3x10])
      (by rw [Ra1 .x30 (by decide), c3x30]) (by norm_num) n1 (by have := r6Rank_lt v 1; omega)
  have D1 : DInv t1 ds (3 + 3) :=
    DInv.step (D0.frame (by norm_num) fa1) (by norm_num) b0_1 b1_1 b2_1 bf1 (udig6 hd 1 3 rfl (by norm_num))
  have R1 : RegsExcept c3 t1 [.x28, .x29] := (Ra1.trans rt1).mono (by decide)
  have F1 : Frame c3 t1 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F0.trans fa1).trans ft1).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt1' : t1.pc = pcOf (P.ub + 26) := by rw [pt1]; simp only [pcOf_4]
  -- group 2
  obtain ⟨a2, sa2, pa2, va, ra2, fa2⟩ := kUg2_spec (codeAt_ua hU 9 rfl) t1 pt1'
  have Ra2 : RegsExcept c3 a2 [.x28, .x29] := (R1.trans ra2).mono (by decide)
  have n2 : a2.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 2) := by
    rw [va, R1 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 16 8 (by norm_num), r6Rank_g v 2 (by norm_num) (by norm_num)]
    try norm_num
  have pa2' : a2.pc = pcOf (P.ub + 28) := by rw [pa2]; simp only [pcOf_4]
  obtain ⟨t2, st2, pt2, b0_2, b1_2, b2_2, bf2, rt2, ft2⟩ :=
    trip (R := .x30) (o := 6) (r := 6) (codeAt_ua hU 10 rfl) (codeAt_ua hU 11 rfl) pa2' (mid0 (P.ub + 28))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra2 .x10 (by decide), c3x10])
      (by rw [Ra2 .x30 (by decide), c3x30]) (by norm_num) n2 (by have := r6Rank_lt v 2; omega)
  have D2 : DInv t2 ds (6 + 3) :=
    DInv.step (D1.frame (by norm_num) fa2) (by norm_num) b0_2 b1_2 b2_2 bf2 (udig6 hd 2 6 rfl (by norm_num))
  have R2 : RegsExcept c3 t2 [.x28, .x29] := (Ra2.trans rt2).mono (by decide)
  have F2 : Frame c3 t2 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F1.trans fa2).trans ft2).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt2' : t2.pc = pcOf (P.ub + 35) := by rw [pt2]; simp only [pcOf_4]
  -- group 3
  obtain ⟨a3, sa3, pa3, va, ra3, fa3⟩ := kUg3_spec (codeAt_ua hU 12 rfl) t2 pt2'
  have Ra3 : RegsExcept c3 a3 [.x28, .x29] := (R2.trans ra3).mono (by decide)
  have n3 : a3.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 3) := by
    rw [va, R2 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 24 8 (by norm_num), r6Rank_g v 3 (by norm_num) (by norm_num)]
    try norm_num
  have pa3' : a3.pc = pcOf (P.ub + 37) := by rw [pa3]; simp only [pcOf_4]
  obtain ⟨t3, st3, pt3, b0_3, b1_3, b2_3, bf3, rt3, ft3⟩ :=
    trip (R := .x30) (o := 9) (r := 6) (codeAt_ua hU 13 rfl) (codeAt_ua hU 14 rfl) pa3' (mid0 (P.ub + 37))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra3 .x10 (by decide), c3x10])
      (by rw [Ra3 .x30 (by decide), c3x30]) (by norm_num) n3 (by have := r6Rank_lt v 3; omega)
  have D3 : DInv t3 ds (9 + 3) :=
    DInv.step (D2.frame (by norm_num) fa3) (by norm_num) b0_3 b1_3 b2_3 bf3 (udig6 hd 3 9 rfl (by norm_num))
  have R3 : RegsExcept c3 t3 [.x28, .x29] := (Ra3.trans rt3).mono (by decide)
  have F3 : Frame c3 t3 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F2.trans fa3).trans ft3).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt3' : t3.pc = pcOf (P.ub + 44) := by rw [pt3]; simp only [pcOf_4]
  -- group 4
  obtain ⟨a4, sa4, pa4, va, ra4, fa4⟩ := kUg4_spec (codeAt_ua hU 15 rfl) t3 pt3'
  have Ra4 : RegsExcept c3 a4 [.x28, .x29] := (R3.trans ra4).mono (by decide)
  have n4 : a4.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 4) := by
    rw [va, R3 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 32 8 (by norm_num), r6Rank_g v 4 (by norm_num) (by norm_num)]
    try norm_num
  have pa4' : a4.pc = pcOf (P.ub + 46) := by rw [pa4]; simp only [pcOf_4]
  obtain ⟨t4, st4, pt4, b0_4, b1_4, b2_4, bf4, rt4, ft4⟩ :=
    trip (R := .x30) (o := 12) (r := 6) (codeAt_ua hU 16 rfl) (codeAt_ua hU 17 rfl) pa4' (mid0 (P.ub + 46))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra4 .x10 (by decide), c3x10])
      (by rw [Ra4 .x30 (by decide), c3x30]) (by norm_num) n4 (by have := r6Rank_lt v 4; omega)
  have D4 : DInv t4 ds (12 + 3) :=
    DInv.step (D3.frame (by norm_num) fa4) (by norm_num) b0_4 b1_4 b2_4 bf4 (udig6 hd 4 12 rfl (by norm_num))
  have R4 : RegsExcept c3 t4 [.x28, .x29] := (Ra4.trans rt4).mono (by decide)
  have F4 : Frame c3 t4 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F3.trans fa4).trans ft4).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt4' : t4.pc = pcOf (P.ub + 53) := by rw [pt4]; simp only [pcOf_4]
  -- group 5
  obtain ⟨a5, sa5, pa5, va, ra5, fa5⟩ := kUg5_spec (codeAt_ua hU 18 rfl) t4 pt4'
  have Ra5 : RegsExcept c3 a5 [.x28, .x29] := (R4.trans ra5).mono (by decide)
  have n5 : a5.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 5) := by
    rw [va, R4 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 40 8 (by norm_num), r6Rank_g v 5 (by norm_num) (by norm_num)]
    try norm_num
  have pa5' : a5.pc = pcOf (P.ub + 55) := by rw [pa5]; simp only [pcOf_4]
  obtain ⟨t5, st5, pt5, b0_5, b1_5, b2_5, bf5, rt5, ft5⟩ :=
    trip (R := .x30) (o := 15) (r := 6) (codeAt_ua hU 19 rfl) (codeAt_ua hU 20 rfl) pa5' (mid0 (P.ub + 55))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra5 .x10 (by decide), c3x10])
      (by rw [Ra5 .x30 (by decide), c3x30]) (by norm_num) n5 (by have := r6Rank_lt v 5; omega)
  have D5 : DInv t5 ds (15 + 3) :=
    DInv.step (D4.frame (by norm_num) fa5) (by norm_num) b0_5 b1_5 b2_5 bf5 (udig6 hd 5 15 rfl (by norm_num))
  have R5 : RegsExcept c3 t5 [.x28, .x29] := (Ra5.trans rt5).mono (by decide)
  have F5 : Frame c3 t5 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F4.trans fa5).trans ft5).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt5' : t5.pc = pcOf (P.ub + 62) := by rw [pt5]; simp only [pcOf_4]
  -- group 6
  obtain ⟨a6, sa6, pa6, va, ra6, fa6⟩ := kUg6_spec (codeAt_ua hU 21 rfl) t5 pt5'
  have Ra6 : RegsExcept c3 a6 [.x28, .x29] := (R5.trans ra6).mono (by decide)
  have n6 : a6.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 6) := by
    rw [va, R5 .x6 (by decide), c3x6, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_lo v 48 8 (by norm_num), r6Rank_g v 6 (by norm_num) (by norm_num)]
    try norm_num
  have pa6' : a6.pc = pcOf (P.ub + 64) := by rw [pa6]; simp only [pcOf_4]
  obtain ⟨t6, st6, pt6, b0_6, b1_6, b2_6, bf6, rt6, ft6⟩ :=
    trip (R := .x30) (o := 18) (r := 6) (codeAt_ua hU 22 rfl) (codeAt_ua hU 23 rfl) pa6' (mid0 (P.ub + 64))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra6 .x10 (by decide), c3x10])
      (by rw [Ra6 .x30 (by decide), c3x30]) (by norm_num) n6 (by have := r6Rank_lt v 6; omega)
  have D6 : DInv t6 ds (18 + 3) :=
    DInv.step (D5.frame (by norm_num) fa6) (by norm_num) b0_6 b1_6 b2_6 bf6 (udig6 hd 6 18 rfl (by norm_num))
  have R6 : RegsExcept c3 t6 [.x28, .x29] := (Ra6.trans rt6).mono (by decide)
  have F6 : Frame c3 t6 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F5.trans fa6).trans ft6).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt6' : t6.pc = pcOf (P.ub + 71) := by rw [pt6]; simp only [pcOf_4]
  -- group 7
  obtain ⟨a7, sa7, pa7, va, ra7, fa7⟩ := kUg7_spec (codeAt_ua hU 24 rfl) t6 pt6'
  have Ra7 : RegsExcept c3 a7 [.x28, .x29] := (R6.trans ra7).mono (by decide)
  have n7 : a7.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 7) := by
    rw [va, R6 .x7 (by decide), c3x7, show (255#64 : Word) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl,
      fld_hi v 48 8 (by norm_num), r6Rank_7]
    try norm_num
  have pa7' : a7.pc = pcOf (P.ub + 73) := by rw [pa7]; simp only [pcOf_4]
  obtain ⟨t7, st7, pt7, b0_7, b1_7, b2_7, bf7, rt7, ft7⟩ :=
    trip (R := .x30) (o := 21) (r := 6) (codeAt_ua hU 25 rfl) (codeAt_ua hU 26 rfl) pa7' (mid0 (P.ub + 73))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra7 .x10 (by decide), c3x10])
      (by rw [Ra7 .x30 (by decide), c3x30]) (by norm_num) n7 (by have := r6Rank_lt v 7; omega)
  have D7 : DInv t7 ds (21 + 3) :=
    DInv.step (D6.frame (by norm_num) fa7) (by norm_num) b0_7 b1_7 b2_7 bf7 (udig6 hd 7 21 rfl (by norm_num))
  have R7 : RegsExcept c3 t7 [.x28, .x29] := (Ra7.trans rt7).mono (by decide)
  have F7 : Frame c3 t7 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F6.trans fa7).trans ft7).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt7' : t7.pc = pcOf (P.ub + 80) := by rw [pt7]; simp only [pcOf_4]
  -- group 8
  obtain ⟨a8, sa8, pa8, va, ra8, fa8⟩ := kUg8_spec (codeAt_ua hU 27 rfl) t7 pt7'
  have Ra8 : RegsExcept c3 a8 [.x28, .x29] := (R7.trans ra8).mono (by decide)
  have n8 : a8.getReg .x28 = BitVec.ofNat 64 (T3.r6Rank v 8) := by
    rw [va, R7 .x7 (by decide), c3x7, r6Rank_8]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    omega
  have pa8' : a8.pc = pcOf (P.ub + 81) := by rw [pa8]; simp only [pcOf_4]
  obtain ⟨t8, st8, pt8, b0_8, b1_8, b2_8, bf8, rt8, ft8⟩ :=
    trip (R := .x30) (o := 24) (r := 6) (codeAt_ua hU 28 rfl) (codeAt_ua hU 29 rfl) pa8' (mid0 (P.ub + 81))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra8 .x10 (by decide), c3x10])
      (by rw [Ra8 .x30 (by decide), c3x30]) (by norm_num) n8 (by have := r6Rank_lt v 8; omega)
  have D8 : DInv t8 ds (24 + 3) :=
    DInv.step (D7.frame (by norm_num) fa8) (by norm_num) b0_8 b1_8 b2_8 bf8 (udig6 hd 8 24 rfl (by norm_num))
  have R8 : RegsExcept c3 t8 [.x28, .x29] := (Ra8.trans rt8).mono (by decide)
  have F8 : Frame c3 t8 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F7.trans fa8).trans ft8).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt8' : t8.pc = pcOf (P.ub + 88) := by rw [pt8]; simp only [pcOf_4]
  -- group 9
  obtain ⟨a9, sa9, pa9, va, ra9, fa9⟩ := kUg9_spec (codeAt_ua hU 30 rfl) t8 pt8'
  have Ra9 : RegsExcept c3 a9 [.x28, .x29] := (R8.trans ra9).mono (by decide)
  have n9 : a9.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 9) := by
    rw [va, R8 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      bv_and_mask _ 7 (by norm_num), toNat_ofNat_lt (t5_lt v), t5_mod v 7 (by norm_num),
      show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ 63 % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 9 (by norm_num)]
    try norm_num
  have pa9' : a9.pc = pcOf (P.ub + 90) := by rw [pa9]; simp only [pcOf_4]
  obtain ⟨t9, st9, pt9, b0_9, b1_9, b2_9, bf9, rt9, ft9⟩ :=
    trip (R := .x11) (o := 27) (r := 5) (codeAt_ua hU 31 rfl) (codeAt_ua hU 32 rfl) pa9' (mid0 (P.ub + 90))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra9 .x10 (by decide), c3x10])
      (by rw [Ra9 .x11 (by decide), c3x11]) (by norm_num) n9 (by have := r5Rank_lt v 9; omega)
  have D9 : DInv t9 ds (27 + 3) :=
    DInv.step (D8.frame (by norm_num) fa9) (by norm_num) b0_9 b1_9 b2_9 bf9 (udig5 hd 9 27 rfl (by norm_num))
  have R9 : RegsExcept c3 t9 [.x28, .x29] := (Ra9.trans rt9).mono (by decide)
  have F9 : Frame c3 t9 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F8.trans fa9).trans ft9).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt9' : t9.pc = pcOf (P.ub + 97) := by rw [pt9]; simp only [pcOf_4]
  -- group 10
  obtain ⟨a10, sa10, pa10, va, ra10, fa10⟩ := kUg10_spec (codeAt_ua hU 33 rfl) t9 pt9'
  have Ra10 : RegsExcept c3 a10 [.x28, .x29] := (R9.trans ra10).mono (by decide)
  have n10 : a10.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 10) := by
    rw [va, R9 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 7 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 7) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 10 (by norm_num)]
    try norm_num
  have pa10' : a10.pc = pcOf (P.ub + 100) := by rw [pa10]; simp only [pcOf_4]
  obtain ⟨t10, st10, pt10, b0_10, b1_10, b2_10, bf10, rt10, ft10⟩ :=
    trip (R := .x11) (o := 30) (r := 5) (codeAt_ua hU 34 rfl) (codeAt_ua hU 35 rfl) pa10' (mid0 (P.ub + 100))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra10 .x10 (by decide), c3x10])
      (by rw [Ra10 .x11 (by decide), c3x11]) (by norm_num) n10 (by have := r5Rank_lt v 10; omega)
  have D10 : DInv t10 ds (30 + 3) :=
    DInv.step (D9.frame (by norm_num) fa10) (by norm_num) b0_10 b1_10 b2_10 bf10 (udig5 hd 10 30 rfl (by norm_num))
  have R10 : RegsExcept c3 t10 [.x28, .x29] := (Ra10.trans rt10).mono (by decide)
  have F10 : Frame c3 t10 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F9.trans fa10).trans ft10).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt10' : t10.pc = pcOf (P.ub + 107) := by rw [pt10]; simp only [pcOf_4]
  -- group 11
  obtain ⟨a11, sa11, pa11, va, ra11, fa11⟩ := kUg11_spec (codeAt_ua hU 36 rfl) t10 pt10'
  have Ra11 : RegsExcept c3 a11 [.x28, .x29] := (R10.trans ra11).mono (by decide)
  have n11 : a11.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 11) := by
    rw [va, R10 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 14 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 14) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 11 (by norm_num)]
    try norm_num
  have pa11' : a11.pc = pcOf (P.ub + 110) := by rw [pa11]; simp only [pcOf_4]
  obtain ⟨t11, st11, pt11, b0_11, b1_11, b2_11, bf11, rt11, ft11⟩ :=
    trip (R := .x11) (o := 33) (r := 5) (codeAt_ua hU 37 rfl) (codeAt_ub hU 0 rfl) pa11' (fun x hx => hU.hJ x (by rw [hx, pcOf_4, pcOf_4]))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra11 .x10 (by decide), c3x10])
      (by rw [Ra11 .x11 (by decide), c3x11]) (by norm_num) n11 (by have := r5Rank_lt v 11; omega)
  have D11 : DInv t11 ds (33 + 3) :=
    DInv.step (D10.frame (by norm_num) fa11) (by norm_num) b0_11 b1_11 b2_11 bf11 (udig5 hd 11 33 rfl (by norm_num))
  have R11 : RegsExcept c3 t11 [.x28, .x29] := (Ra11.trans rt11).mono (by decide)
  have F11 : Frame c3 t11 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F10.trans fa11).trans ft11).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt11' : t11.pc = pcOf (P.uc + 5) := by rw [pt11]; simp only [pcOf_4]
  -- group 12
  obtain ⟨a12, sa12, pa12, va, ra12, fa12⟩ := kUg12_spec (codeAt_ub hU 1 rfl) t11 pt11'
  have Ra12 : RegsExcept c3 a12 [.x28, .x29] := (R11.trans ra12).mono (by decide)
  have n12 : a12.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 12) := by
    rw [va, R11 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 21 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 21) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 12 (by norm_num)]
    try norm_num
  have pa12' : a12.pc = pcOf (P.uc + 8) := by rw [pa12]; simp only [pcOf_4]
  obtain ⟨t12, st12, pt12, b0_12, b1_12, b2_12, bf12, rt12, ft12⟩ :=
    trip (R := .x11) (o := 36) (r := 5) (codeAt_ub hU 2 rfl) (codeAt_ub hU 3 rfl) pa12' (mid0 (P.uc + 8))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra12 .x10 (by decide), c3x10])
      (by rw [Ra12 .x11 (by decide), c3x11]) (by norm_num) n12 (by have := r5Rank_lt v 12; omega)
  have D12 : DInv t12 ds (36 + 3) :=
    DInv.step (D11.frame (by norm_num) fa12) (by norm_num) b0_12 b1_12 b2_12 bf12 (udig5 hd 12 36 rfl (by norm_num))
  have R12 : RegsExcept c3 t12 [.x28, .x29] := (Ra12.trans rt12).mono (by decide)
  have F12 : Frame c3 t12 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F11.trans fa12).trans ft12).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt12' : t12.pc = pcOf (P.uc + 15) := by rw [pt12]; simp only [pcOf_4]
  -- group 13
  obtain ⟨a13, sa13, pa13, va, ra13, fa13⟩ := kUg13_spec (codeAt_ub hU 4 rfl) t12 pt12'
  have Ra13 : RegsExcept c3 a13 [.x28, .x29] := (R12.trans ra13).mono (by decide)
  have n13 : a13.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 13) := by
    rw [va, R12 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 28 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 28) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 13 (by norm_num)]
    try norm_num
  have pa13' : a13.pc = pcOf (P.uc + 18) := by rw [pa13]; simp only [pcOf_4]
  obtain ⟨t13, st13, pt13, b0_13, b1_13, b2_13, bf13, rt13, ft13⟩ :=
    trip (R := .x11) (o := 39) (r := 5) (codeAt_ub hU 5 rfl) (codeAt_ub hU 6 rfl) pa13' (mid0 (P.uc + 18))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra13 .x10 (by decide), c3x10])
      (by rw [Ra13 .x11 (by decide), c3x11]) (by norm_num) n13 (by have := r5Rank_lt v 13; omega)
  have D13 : DInv t13 ds (39 + 3) :=
    DInv.step (D12.frame (by norm_num) fa13) (by norm_num) b0_13 b1_13 b2_13 bf13 (udig5 hd 13 39 rfl (by norm_num))
  have R13 : RegsExcept c3 t13 [.x28, .x29] := (Ra13.trans rt13).mono (by decide)
  have F13 : Frame c3 t13 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F12.trans fa13).trans ft13).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt13' : t13.pc = pcOf (P.uc + 25) := by rw [pt13]; simp only [pcOf_4]
  -- group 14
  obtain ⟨a14, sa14, pa14, va, ra14, fa14⟩ := kUg14_spec (codeAt_ub hU 7 rfl) t13 pt13'
  have Ra14 : RegsExcept c3 a14 [.x28, .x29] := (R13.trans ra14).mono (by decide)
  have n14 : a14.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 14) := by
    rw [va, R13 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 35 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 35) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 14 (by norm_num)]
    try norm_num
  have pa14' : a14.pc = pcOf (P.uc + 28) := by rw [pa14]; simp only [pcOf_4]
  obtain ⟨t14, st14, pt14, b0_14, b1_14, b2_14, bf14, rt14, ft14⟩ :=
    trip (R := .x11) (o := 42) (r := 5) (codeAt_ub hU 8 rfl) (codeAt_ub hU 9 rfl) pa14' (mid0 (P.uc + 28))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra14 .x10 (by decide), c3x10])
      (by rw [Ra14 .x11 (by decide), c3x11]) (by norm_num) n14 (by have := r5Rank_lt v 14; omega)
  have D14 : DInv t14 ds (42 + 3) :=
    DInv.step (D13.frame (by norm_num) fa14) (by norm_num) b0_14 b1_14 b2_14 bf14 (udig5 hd 14 42 rfl (by norm_num))
  have R14 : RegsExcept c3 t14 [.x28, .x29] := (Ra14.trans rt14).mono (by decide)
  have F14 : Frame c3 t14 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F13.trans fa14).trans ft14).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt14' : t14.pc = pcOf (P.uc + 35) := by rw [pt14]; simp only [pcOf_4]
  -- group 15
  obtain ⟨a15, sa15, pa15, va, ra15, fa15⟩ := kUg15_spec (codeAt_ub hU 10 rfl) t14 pt14'
  have Ra15 : RegsExcept c3 a15 [.x28, .x29] := (R14.trans ra15).mono (by decide)
  have n15 : a15.getReg .x28 = BitVec.ofNat 64 (T3.r5Rank v 15) := by
    rw [va, R14 .x25 (by decide), c3x25, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_t5 v 42 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ (63 + 42) % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r5Rank_eq v 15 (by norm_num)]
    try norm_num
  have pa15' : a15.pc = pcOf (P.uc + 38) := by rw [pa15]; simp only [pcOf_4]
  obtain ⟨t15, st15, pt15, b0_15, b1_15, b2_15, bf15, rt15, ft15⟩ :=
    trip (R := .x11) (o := 45) (r := 5) (codeAt_ub hU 11 rfl) (codeAt_ub hU 12 rfl) pa15' (mid0 (P.uc + 38))
      rfl rfl rfl rfl rfl rfl rfl (by decide) rfl rfl rfl (by norm_num) (by rw [Ra15 .x10 (by decide), c3x10])
      (by rw [Ra15 .x11 (by decide), c3x11]) (by norm_num) n15 (by have := r5Rank_lt v 15; omega)
  have D15 : DInv t15 ds (45 + 3) :=
    DInv.step (D14.frame (by norm_num) fa15) (by norm_num) b0_15 b1_15 b2_15 bf15 (udig5 hd 15 45 rfl (by norm_num))
  have R15 : RegsExcept c3 t15 [.x28, .x29] := (Ra15.trans rt15).mono (by decide)
  have F15 : Frame c3 t15 (fun A => DIGITS ≤ A ∧ A < DIGITS + 64) :=
    ((F14.trans fa15).trans ft15).mono (fun _ _ h => by simp only [or_false] at h; rcases h with h | h <;> exact h)
  have pt15' : t15.pc = pcOf (P.uc + 45) := by rw [pt15]; simp only [pcOf_4]
  -- r7 pair
  obtain ⟨a16, sa16, pa16, ⟨va16, v30⟩, ra16, fa16⟩ := kUr7_spec (codeAt_ub hU 13 rfl) t15 pt15'
  have Ra16 : RegsExcept c3 a16 [.x28, .x29, .x30] := (R15.trans ra16).mono (by decide)
  have n16 : a16.getReg .x28 = BitVec.ofNat 64 (T3.r7Rank v) := by
    rw [va16, R15 .x6 (by decide), c3x6, show (127#64 : Word) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      fld_lo v 56 7 (by norm_num), show (BitVec.ofNat 64 (2 ^ 7 - 1) : Word) = 127#64 from rfl,
      xor127 (v.toNat / 2 ^ 56 % 2 ^ 7) (Nat.mod_lt _ (by norm_num)), r7Rank_eq v]
    try norm_num
  have pa16' : a16.pc = pcOf (P.uc + 49) := by rw [pa16]; simp only [pcOf_4]
  have h7lt := r7Rank_lt v
  obtain ⟨u1, su1, pu1, xu1, bu1, bfu1, ru1, fu1⟩ := divsb (rd := .x29) (op := .remu) (m := T3.r7Rank v % 7)
    (R := .x30) (o := 48) (r := 7) (n := T3.r7Rank v)
    (codeAt_ub hU 14 rfl) pa16' rfl rfl rfl
    (by show rv64_remu _ _ = _; rw [bv_remu _ _ (by omega) (by norm_num) (by norm_num)]) (by omega) (Or.inr rfl)
    rfl rfl (by norm_num) (by rw [Ra16 .x10 (by decide), c3x10]) v30 (by decide) n16 (fun h => by cases h)
  obtain ⟨u2, su2, pu2, xu2, bu2, bfu2, ru2, fu2⟩ := divsb (rd := .x29) (op := .divu) (m := T3.r7Rank v / 7)
    (R := .x30) (o := 49) (r := 7) (n := T3.r7Rank v)
    (codeAt_ub hU 15 rfl) (by rw [pu1, pcOf_4, pcOf_4]) rfl rfl rfl
    (by show rv64_divu _ _ = _; rw [bv_divu _ _ (by omega) (by norm_num) (by norm_num)]) (by omega) (Or.inr rfl)
    rfl rfl (by norm_num) (by rw [ru1 .x10 (by decide), Ra16 .x10 (by decide), c3x10])
    (by rw [ru1 .x30 (by decide), v30]) (by decide) (by rw [ru1 .x28 (by decide), n16]) (fun h => by cases h)
  obtain ⟨t, sret, pret, rret, fret⟩ := ret_spec (codeAt_ub hU 16 rfl) u2 (by rw [pu2, pcOf_4, pcOf_4])
  have D7 := udig7 hd
  refine ⟨t, (((((((((((((((((((((((((((((((((((((((s1.trans sb50).trans s3).trans sa0).trans st0).trans sa1).trans st1).trans sa2).trans st2).trans sa3).trans st3).trans sa4).trans st4).trans sa5).trans st5).trans sa6).trans st6).trans sa7).trans st7).trans sa8).trans st8).trans sa9).trans st9).trans sa10).trans st10).trans sa11).trans st11).trans sa12).trans st12).trans sa13).trans st13).trans sa14).trans st14).trans sa15).trans st15).trans sa16).trans su1).trans su2).trans sret)).of_eq (by omega) (by omega), ?_, ?_, ?_, ?_⟩
  · rw [pret, ru2 .x1 (by decide), ru1 .x1 (by decide), Ra16 .x1 (by decide), r3 .x1 (by decide), r2 .x1 (by decide),
      r1 .x1 (by decide)]; rfl
  · intro j hj
    rw [fret.getByte (by omega) (fun h => h)]
    by_cases h49 : j = 49
    · subst h49; rw [bu2, D7.2]
    rw [bfu2 _ (by omega) (by omega)]
    by_cases h48 : j = 48
    · subst h48; rw [bu1, D7.1]
    rw [bfu1 _ (by omega) (by omega), fa16.getByte (by omega) (fun h => h)]
    exact D15 j (by omega)
  · exact (((((r1.trans r2).trans r3).trans Ra16).trans ru1).trans ru2).trans rret |>.mono (by decide)
  · exact (((((((f1.trans f2).trans f3).trans F15).trans fa16).trans fu1).trans fu2).trans fret).mono (fun A _ h => by
      simp only [or_false, false_or, or_self] at h; exact h)
end SigGolfCandidate.T3M.Search.T51
end

/-! ## The two T51 kernel instances (sign, expand) and their hooks -/
section
namespace SigGolfCandidate.T3M.Search.T51
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
/-- Sign instance: `K_ENTRY` 1798, `U_ENTRY` 21230 (split jump at 21342 to 21852), block 0xFFF800 (TOP_DATA + 2048),
credit 0x66018, reject continuation 1011 (`b + 468`, b = 543). -/
def signInst : KInst :=
  ⟨1798, 21230, 21852, 1, 0xFFF800, 0x66018, 1011, 0x1000537, 0x8a050513, 0x1df3c23, 0x5c51206f, 0x9b4ff06f⟩
/-- Expand instance: `K_ENTRY` 54176, `U_ENTRY` 54356 (contiguous unpacker), RAM block 0xA0000, credit 0x66040,
reject continuation 822 (`b + 468`, b = 354). -/
def expandInst : KInst :=
  ⟨54176, 54356, 54468, 0, 0xA0000, 0x66040, 822, 0xa0537, 0xa050513, 0x5df3023, 0xf40006f, 0xc59cb06f⟩
def jal1 (n : Nat) : List (BitVec 32) := [BitVec.ofNat 32 n]
theorem jump_hook {image : Image} {w : BitVec 32} {k t : Nat} {off : Nat}
    (hrun : ∀ pc : Word, symRun { noAlias := true } [w] pc 10 = some ⟨SymState.init, .c (pc + BitVec.ofNat 64 off), .jump, 1, 1⟩)
    (hc : CodeAt image (pcOf k) [w]) (hk : 0x1000 + 4 * k < 2 ^ 64) (ht : 0x1000 + 4 * t < 2 ^ 64)
    (hoff : (0x1000 + 4 * k + off) % 2 ^ 64 = 0x1000 + 4 * t) :
    ∀ s : MachineState, s.pc = pcOf k → ∃ u, Steps image s 1 1 u ∧ u.pc = pcOf t ∧ RegsExcept s u [] ∧
      Frame s u (fun _ => False) := by
  intro s hs
  obtain ⟨u, su, pu, ru, fu⟩ := jal_spec (hrun _) hc s hs
  refine ⟨u, su, ?_, ru, fu⟩
  rw [pu]
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega
sym_block eSRun := symRun { noAlias := true } [(0x1000537 : BitVec 32), 0x8a050513] 0 10
sym_block eERun := symRun { noAlias := true } [(0xa0537 : BitVec 32), 0xa050513] 0 10
theorem run_eS (pc : Word) : symRun { noAlias := true } [(0x1000537 : BitVec 32), 0x8a050513] pc 10 =
    some ⟨eSRun.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl
theorem run_eE (pc : Word) : symRun { noAlias := true } [(0xa0537 : BitVec 32), 0xa050513] pc 10 =
    some ⟨eERun.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl
theorem sign_hE {image : Image} (hc : CodeAt image (pcOf 1798) [(0x1000537 : BitVec 32), 0x8a050513]) :
    ∀ s : MachineState, s.pc = pcOf 1798 → ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (1798 + 2) ∧
      t.getReg .x10 = BitVec.ofNat 64 (0xFFF800 + 160) ∧ RegsExcept s t [.x10] ∧ Frame s t (fun _ => False) := by
  intro s hs
  refine ⟨_, symRun_sound (run_eS _) hc s hs (by simp [eSRun.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [rv_simp, pcOf_4, pcOf_4']
  · simp only [rv_simp, eSRun.res] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [eSRun.res, rv_simp] <;> rfl
  · intro A _ _; simp [eSRun.res, rv_simp]
theorem expand_hE {image : Image} (hc : CodeAt image (pcOf 54176) [(0xa0537 : BitVec 32), 0xa050513]) :
    ∀ s : MachineState, s.pc = pcOf 54176 → ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (54176 + 2) ∧
      t.getReg .x10 = BitVec.ofNat 64 (0xA0000 + 160) ∧ RegsExcept s t [.x10] ∧ Frame s t (fun _ => False) := by
  intro s hs
  refine ⟨_, symRun_sound (run_eE _) hc s hs (by simp [eERun.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [rv_simp, pcOf_4, pcOf_4']
  · simp only [rv_simp, eERun.res] <;> rfl
  · intro r hr; simp at hr; cases r <;> simp_all [eERun.res, rv_simp] <;> rfl
  · intro A _ _; simp [eERun.res, rv_simp]
theorem cr_hook {image : Image} {w : BitVec 32} {off : BitVec 12} {k c : Nat}
    (hc : CodeAt image (pcOf k) [w]) (hdec : decodeInstruction w = some (.base (.SD .x30 .x29 off)))
    (hoff : signExtend12 off = BitVec.ofNat 64 c) (hal : (0x66000 + c) % 8 = 0) (hlt : 0x66000 + c + 8 ≤ 2 ^ 24) :
    ∀ s : MachineState, s.pc = pcOf k → s.getReg .x30 = BitVec.ofNat 64 0x66000 →
      ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (k + 1) ∧ t.getMem (BitVec.ofNat 64 (0x66000 + c)) = s.getReg .x29 ∧
        RegsExcept s t [] ∧ Frame s t (fun A => A = 0x66000 + c) := by
  intro s hs h30
  obtain ⟨t, st, pt, mt, rt, ft⟩ := sd_spec hc hs hdec hoff h30 hal hlt
  exact ⟨t, st, by rw [pt, pcOf_4], mt, rt, ft⟩
theorem signKAt {image : Image} (hc : CodeAt image (pcOf 1798) (kCode signInst)) : T51KAt image signInst where
  code := hc
  kbLt := by norm_num [signInst]
  blk8 := by norm_num [signInst]
  blkLt := by norm_num [signInst]
  credit8 := by norm_num [signInst]
  creditLt := by norm_num [signInst]
  creditNe := by norm_num [signInst]
  hE := sign_hE (codeAt_sublayout hc (kLF_ok _) (i := 0) rfl)
  hCr := cr_hook (k := 1798 + 117) (c := 24) (codeAt_sublayout hc (kLF_ok _) (i := 32) rfl) rfl rfl
    (by norm_num [signInst]) (by norm_num [signInst])
  hU := jump_hook (off := 77252) (fun _ => rfl) (codeAt_sublayout hc (kLF_ok _) (i := 34) rfl) (by norm_num [signInst])
    (by norm_num [signInst]) (by norm_num [signInst])
  hN := jump_hook (off := 18446744073709547956) (fun _ => rfl) (codeAt_sublayout hc (kLF_ok _) (i := 40) rfl)
    (by norm_num [signInst]) (by norm_num [signInst]) (by norm_num [signInst])
theorem expandKAt {image : Image} (hc : CodeAt image (pcOf 54176) (kCode expandInst)) : T51KAt image expandInst where
  code := hc
  kbLt := by norm_num [expandInst]
  blk8 := by norm_num [expandInst]
  blkLt := by norm_num [expandInst]
  credit8 := by norm_num [expandInst]
  creditLt := by norm_num [expandInst]
  creditNe := by norm_num [expandInst]
  hE := expand_hE (codeAt_sublayout hc (kLF_ok _) (i := 0) rfl)
  hCr := cr_hook (k := 54176 + 117) (c := 64) (codeAt_sublayout hc (kLF_ok _) (i := 32) rfl) rfl rfl
    (by norm_num [expandInst]) (by norm_num [expandInst])
  hU := jump_hook (off := 244) (fun _ => rfl) (codeAt_sublayout hc (kLF_ok _) (i := 34) rfl) (by norm_num [expandInst])
    (by norm_num [expandInst]) (by norm_num [expandInst])
  hN := jump_hook (off := 18446744073709337688) (fun _ => rfl) (codeAt_sublayout hc (kLF_ok _) (i := 40) rfl)
    (by norm_num [expandInst]) (by norm_num [expandInst]) (by norm_num [expandInst])
/-- The sign unpacker's split jump `j 21852` at 21342. -/
def uJumpS : List (BitVec 32) := [0x7f80006f]
theorem signUAt {image : Image} (hA : CodeAt image (pcOf 21230) uCodeA) (hJ : CodeAt image (pcOf 21342) uJumpS)
    (hB : CodeAt image (pcOf 21852) uCodeB) : T51UAt image signInst where
  codeA := hA
  codeB := hB
  ubLt := by norm_num [signInst]
  ucLt := by norm_num [signInst]
  hJ := jump_hook (off := 2040) (fun _ => rfl) hJ (by norm_num [signInst]) (by norm_num [signInst]) (by norm_num [signInst])
theorem expandUAt {image : Image} (hA : CodeAt image (pcOf 54356) uCodeA)
    (hB : CodeAt image (pcOf 54468) uCodeB) : T51UAt image expandInst where
  codeA := hA
  codeB := hB
  ubLt := by norm_num [expandInst]
  ucLt := by norm_num [expandInst]
  hJ := fun s hs => ⟨s, Steps.refl _, hs, RegsExcept.refl _ _, Frame.refl _ _⟩
end SigGolfCandidate.T3M.Search.T51
end
