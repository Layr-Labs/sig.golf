import SigGolfCandidate.SimCore
import SigGolfCandidate.Merge046
set_option debug.skipKernelTC false
namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
attribute [rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.toState_getMem Result.pc Result.st Result.steps Result.cycles Result.stop
  SymState.regs SymState.mem SymState.obl BitVec.ofNat_eq_ofNat
end SigGolfCandidate.Rv

namespace MachineCounterCaps
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace sign
def hookCode : List (BitVec 32) := [0xa80006f]
sym_block hook := symRun {noAlias:=true} hookCode (pcOf 26061) 20
def firstCode : List (BitVec 32) := [0x143313,0x31a63]
sym_block first := symRun {noAlias:=true} firstCode (pcOf 26103) 20
def secondCode : List (BitVec 32) := [0x343313,0x31a63]
sym_block second := symRun {noAlias:=true} secondCode (pcOf 26105) 20
def lastCode : List (BitVec 32) := [0x360337,0xf51ff06f]
sym_block last := symRun {noAlias:=true} lastCode (pcOf 26107) 20
def topCode : List (BitVec 32) := [0x200337,0xf49ff06f]
sym_block top := symRun {noAlias:=true} topCode (pcOf 26109) 20
def midCode : List (BitVec 32) := [0x1c0337,0xf41ff06f]
sym_block mid := symRun {noAlias:=true} midCode (pcOf 26111) 20
def cmpCode : List (BitVec 32) := [0x69e463]
sym_block cmp := symRun {noAlias:=true} cmpCode (pcOf 26064) 20
theorem top_value (s : MachineState) : (top.res.toState s).getReg .x6 = 2097152#64 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem top_pc (s : MachineState) : (top.res.toState s).pc = pcOf 26064 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem mid_value (s : MachineState) : (mid.res.toState s).getReg .x6 = 1835008#64 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem mid_pc (s : MachineState) : (mid.res.toState s).pc = pcOf 26064 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem last_value (s : MachineState) : (last.res.toState s).getReg .x6 = 3538944#64 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem last_pc (s : MachineState) : (last.res.toState s).pc = pcOf 26064 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem first_pc (s : MachineState) (h : s.getReg .x8 = 0#64) : (first.res.toState s).pc = pcOf 26109 := by
  simp [first.res, rv_simp, h]
theorem second_pc (s : MachineState) (h : s.getReg .x8 = 3#64) : (second.res.toState s).pc = pcOf 26107 := by
  simp [second.res, rv_simp, h]
theorem selector_steps {image : Image} (s : MachineState) (lay : Nat) (hl : lay < 4)
    (hc_hook : CodeAt image (pcOf 26061) hookCode)
    (hc_first : CodeAt image (pcOf 26103) firstCode)
    (hc_second : CodeAt image (pcOf 26105) secondCode)
    (hc_last : CodeAt image (pcOf 26107) lastCode)
    (hc_top : CodeAt image (pcOf 26109) topCode)
    (hc_mid : CodeAt image (pcOf 26111) midCode)
    (hc_cmp : CodeAt image (pcOf 26064) cmpCode)
    (hp : s.pc = pcOf 26061) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ k t, Steps image s k k t ∧ k ≤ 7 ∧ t.pc = pcOf 26064 ∧
      t.getReg .x6 = BitVec.ofNat 64 (if lay=0 then 2^21 else if lay=3 then 27*2^17 else 7*2^18) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  interval_cases lay
  ·
    let t0 := hook.res.toState s
    have hs0 := symRun_sound hook hc_hook s (by simp_all [rv_simp, hp]) (by simp [hook.res, rv_simp])
    let t1 := first.res.toState t0
    have hs1 := symRun_sound first hc_first t0 (by simp_all [rv_simp, hook.res, h8, t0]) (by simp [first.res, rv_simp])
    let t2 := top.res.toState t1
    have hs2 := symRun_sound top hc_top t1 (by simp_all [rv_simp, hook.res, first.res, h8, t0, t1]) (by simp [top.res, rv_simp])
    refine ⟨_, t2, ((hs0).trans hs1).trans hs2, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8]
    · simp [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8]
    · simp [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8] <;> rfl
    · intro A _ _; simp [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8]
  ·
    let t0 := hook.res.toState s
    have hs0 := symRun_sound hook hc_hook s (by simp_all [rv_simp, hp]) (by simp [hook.res, rv_simp])
    let t1 := first.res.toState t0
    have hs1 := symRun_sound first hc_first t0 (by simp_all [rv_simp, hook.res, h8, t0]) (by simp [first.res, rv_simp])
    let t2 := second.res.toState t1
    have hs2 := symRun_sound second hc_second t1 (by simp_all [rv_simp, hook.res, first.res, h8, t0, t1]) (by simp [second.res, rv_simp])
    let t3 := mid.res.toState t2
    have hs3 := symRun_sound mid hc_mid t2 (by simp_all [rv_simp, hook.res, first.res, second.res, h8, t0, t1, t2]) (by simp [mid.res, rv_simp])
    refine ⟨_, t3, (((hs0).trans hs1).trans hs2).trans hs3, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8] <;> rfl
    · intro A _ _; simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
  ·
    let t0 := hook.res.toState s
    have hs0 := symRun_sound hook hc_hook s (by simp_all [rv_simp, hp]) (by simp [hook.res, rv_simp])
    let t1 := first.res.toState t0
    have hs1 := symRun_sound first hc_first t0 (by simp_all [rv_simp, hook.res, h8, t0]) (by simp [first.res, rv_simp])
    let t2 := second.res.toState t1
    have hs2 := symRun_sound second hc_second t1 (by simp_all [rv_simp, hook.res, first.res, h8, t0, t1]) (by simp [second.res, rv_simp])
    let t3 := mid.res.toState t2
    have hs3 := symRun_sound mid hc_mid t2 (by simp_all [rv_simp, hook.res, first.res, second.res, h8, t0, t1, t2]) (by simp [mid.res, rv_simp])
    refine ⟨_, t3, (((hs0).trans hs1).trans hs2).trans hs3, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8] <;> rfl
    · intro A _ _; simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
  ·
    let t0 := hook.res.toState s
    have hs0 := symRun_sound hook hc_hook s (by simp_all [rv_simp, hp]) (by simp [hook.res, rv_simp])
    let t1 := first.res.toState t0
    have hs1 := symRun_sound first hc_first t0 (by simp_all [rv_simp, hook.res, h8, t0]) (by simp [first.res, rv_simp])
    let t2 := second.res.toState t1
    have hs2 := symRun_sound second hc_second t1 (by simp_all [rv_simp, hook.res, first.res, h8, t0, t1]) (by simp [second.res, rv_simp])
    let t3 := last.res.toState t2
    have hs3 := symRun_sound last hc_last t2 (by simp_all [rv_simp, hook.res, first.res, second.res, h8, t0, t1, t2]) (by simp [last.res, rv_simp])
    refine ⟨_, t3, (((hs0).trans hs1).trans hs2).trans hs3, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8] <;> rfl
    · intro A _ _; simp [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8]
#print axioms selector_steps
end sign
namespace expand
def hookCode : List (BitVec 32) := [0xa80006f]
sym_block hook := symRun {noAlias:=true} hookCode (pcOf 88200) 20
def firstCode : List (BitVec 32) := [0x143313,0x31a63]
sym_block first := symRun {noAlias:=true} firstCode (pcOf 88242) 20
def secondCode : List (BitVec 32) := [0x343313,0x31a63]
sym_block second := symRun {noAlias:=true} secondCode (pcOf 88244) 20
def lastCode : List (BitVec 32) := [0x360337,0xf51ff06f]
sym_block last := symRun {noAlias:=true} lastCode (pcOf 88246) 20
def topCode : List (BitVec 32) := [0x200337,0xf49ff06f]
sym_block top := symRun {noAlias:=true} topCode (pcOf 88248) 20
def midCode : List (BitVec 32) := [0x1c0337,0xf41ff06f]
sym_block mid := symRun {noAlias:=true} midCode (pcOf 88250) 20
def cmpCode : List (BitVec 32) := [0x69e463]
sym_block cmp := symRun {noAlias:=true} cmpCode (pcOf 88203) 20
theorem top_value (s : MachineState) : (top.res.toState s).getReg .x6 = 2097152#64 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem top_pc (s : MachineState) : (top.res.toState s).pc = pcOf 88203 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem mid_value (s : MachineState) : (mid.res.toState s).getReg .x6 = 1835008#64 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem mid_pc (s : MachineState) : (mid.res.toState s).pc = pcOf 88203 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem last_value (s : MachineState) : (last.res.toState s).getReg .x6 = 3538944#64 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem last_pc (s : MachineState) : (last.res.toState s).pc = pcOf 88203 := by
  simp [rv_simp, top.res, mid.res, last.res]
theorem first_pc (s : MachineState) (h : s.getReg .x8 = 0#64) : (first.res.toState s).pc = pcOf 88248 := by
  simp [first.res, rv_simp, h]
theorem second_pc (s : MachineState) (h : s.getReg .x8 = 3#64) : (second.res.toState s).pc = pcOf 88246 := by
  simp [second.res, rv_simp, h]
theorem selector_steps {image : Image} (s : MachineState) (lay : Nat) (hl : lay < 4)
    (hc_hook : CodeAt image (pcOf 88200) hookCode)
    (hc_first : CodeAt image (pcOf 88242) firstCode)
    (hc_second : CodeAt image (pcOf 88244) secondCode)
    (hc_last : CodeAt image (pcOf 88246) lastCode)
    (hc_top : CodeAt image (pcOf 88248) topCode)
    (hc_mid : CodeAt image (pcOf 88250) midCode)
    (hc_cmp : CodeAt image (pcOf 88203) cmpCode)
    (hp : s.pc = pcOf 88200) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ k t, Steps image s k k t ∧ k ≤ 7 ∧ t.pc = pcOf 88203 ∧
      t.getReg .x6 = BitVec.ofNat 64 (if lay=0 then 2^21 else if lay=3 then 27*2^17 else 7*2^18) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  interval_cases lay
  ·
    let t0 := hook.res.toState s
    have hs0 := symRun_sound hook hc_hook s (by simp_all [rv_simp, hp]) (by simp [hook.res, rv_simp])
    let t1 := first.res.toState t0
    have hs1 := symRun_sound first hc_first t0 (by simp_all [rv_simp, hook.res, h8, t0]) (by simp [first.res, rv_simp])
    let t2 := top.res.toState t1
    have hs2 := symRun_sound top hc_top t1 (by simp_all [rv_simp, hook.res, first.res, h8, t0, t1]) (by simp [top.res, rv_simp])
    refine ⟨_, t2, ((hs0).trans hs1).trans hs2, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8]
    · simp [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8]
    · simp [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8] <;> rfl
    · intro A _ _; simp [t0, t1, t2, hook.res, first.res, top.res, rv_simp, h8]
  ·
    let t0 := hook.res.toState s
    have hs0 := symRun_sound hook hc_hook s (by simp_all [rv_simp, hp]) (by simp [hook.res, rv_simp])
    let t1 := first.res.toState t0
    have hs1 := symRun_sound first hc_first t0 (by simp_all [rv_simp, hook.res, h8, t0]) (by simp [first.res, rv_simp])
    let t2 := second.res.toState t1
    have hs2 := symRun_sound second hc_second t1 (by simp_all [rv_simp, hook.res, first.res, h8, t0, t1]) (by simp [second.res, rv_simp])
    let t3 := mid.res.toState t2
    have hs3 := symRun_sound mid hc_mid t2 (by simp_all [rv_simp, hook.res, first.res, second.res, h8, t0, t1, t2]) (by simp [mid.res, rv_simp])
    refine ⟨_, t3, (((hs0).trans hs1).trans hs2).trans hs3, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8] <;> rfl
    · intro A _ _; simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
  ·
    let t0 := hook.res.toState s
    have hs0 := symRun_sound hook hc_hook s (by simp_all [rv_simp, hp]) (by simp [hook.res, rv_simp])
    let t1 := first.res.toState t0
    have hs1 := symRun_sound first hc_first t0 (by simp_all [rv_simp, hook.res, h8, t0]) (by simp [first.res, rv_simp])
    let t2 := second.res.toState t1
    have hs2 := symRun_sound second hc_second t1 (by simp_all [rv_simp, hook.res, first.res, h8, t0, t1]) (by simp [second.res, rv_simp])
    let t3 := mid.res.toState t2
    have hs3 := symRun_sound mid hc_mid t2 (by simp_all [rv_simp, hook.res, first.res, second.res, h8, t0, t1, t2]) (by simp [mid.res, rv_simp])
    refine ⟨_, t3, (((hs0).trans hs1).trans hs2).trans hs3, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8] <;> rfl
    · intro A _ _; simp [t0, t1, t2, t3, hook.res, first.res, second.res, mid.res, rv_simp, h8]
  ·
    let t0 := hook.res.toState s
    have hs0 := symRun_sound hook hc_hook s (by simp_all [rv_simp, hp]) (by simp [hook.res, rv_simp])
    let t1 := first.res.toState t0
    have hs1 := symRun_sound first hc_first t0 (by simp_all [rv_simp, hook.res, h8, t0]) (by simp [first.res, rv_simp])
    let t2 := second.res.toState t1
    have hs2 := symRun_sound second hc_second t1 (by simp_all [rv_simp, hook.res, first.res, h8, t0, t1]) (by simp [second.res, rv_simp])
    let t3 := last.res.toState t2
    have hs3 := symRun_sound last hc_last t2 (by simp_all [rv_simp, hook.res, first.res, second.res, h8, t0, t1, t2]) (by simp [last.res, rv_simp])
    refine ⟨_, t3, (((hs0).trans hs1).trans hs2).trans hs3, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8]
    · simp [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8]
    · intro r hr; cases r <;> simp_all [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8] <;> rfl
    · intro A _ _; simp [t0, t1, t2, t3, hook.res, first.res, second.res, last.res, rv_simp, h8]
#print axioms selector_steps
end expand
end MachineCounterCaps
