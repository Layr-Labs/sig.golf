import SigGolfCandidate.Choice.ProducerSelectorTail

namespace SigGolfCandidate.Choice.ProducerSelector
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Search.Reward
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.WCT9
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] words

def headCode : List (BitVec 32) := words.take 2
sym_block headBase := symRun {noAlias:=true} headCode 0#64 3
def headResult (b : Nat) : Result :=
  ⟨headBase.res.st, E.ite .eq (.bin .srl (.reg .x7) (.c 62)) (.c 0)
    (.c (pcOf (b+147))) (.c (pcOf (b+2))), .branch, 2, 2⟩
theorem head_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} headCode (pcOf b) 3 = some (headResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem head_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (hpc : s.pc=pcOf b)
    (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc=(if Selector.group v=0 then pcOf (b+147) else pcOf (b+2)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  have hc' : CodeAt image (pcOf b) headCode := by simpa [headCode] using slice hc 0 2 (by decide)
  refine ⟨_,symRun_sound (head_run b hb) hc' s hpc
    (by simp [headResult,headBase.res,rv_simp]),?_,?_,?_⟩
  · by_cases hg : v.extractLsb' 64 64 >>> 62 = (0#64)
    all_goals simp [headResult,headBase.res,rv_simp,h7,Selector.group,hg]
  · intro r hr; cases r <;> simp_all [headResult,headBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl

def initCode : List (BitVec 32) := (words.drop 2).take 8
sym_block initBase := symRun {noAlias:=true} initCode 0#64 10
def initResult (b : Nat) : Result := {initBase.res with pc:=.c (pcOf (b+10))}
theorem init_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} initCode (pcOf (b+2)) 10 = some (initResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem init_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (hpc : s.pc=pcOf (b+2))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    ∃ t, Steps image s 8 8 t ∧ t.pc=pcOf (b+10) ∧
      t.getReg .x6=(T3.topFlip v).extractLsb' 0 64 ∧
      t.getReg .x7=(T3.topFlip v).extractLsb' 64 64 ∧
      t.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048) ∧
      t.getReg .x25=0 ∧ t.getReg .x20=0 ∧
      RegsExcept s t [.x6,.x7,.x11,.x20,.x25,.x28] ∧ Frame s t (fun _=>False) := by
  have hlo : (T3.topFlip v).extractLsb' 0 64=v.extractLsb' 0 64 ^^^ BitVec.ofNat 64 (2^64-1) := by
    rw [T3.topFlip,BitVec.extractLsb'_xor]; congr 1
  have hhi : (T3.topFlip v).extractLsb' 64 64=v.extractLsb' 64 64 ^^^ BitVec.ofNat 64 (2^55-1) := by
    rw [T3.topFlip,BitVec.extractLsb'_xor]; congr 1
  refine ⟨_,symRun_sound (init_run b hb) (slice hc 2 8 (by decide)) s hpc
    (by simp [initResult,initBase.res,rv_simp]),rfl,?_,?_,rfl,rfl,rfl,?_,?_⟩
  · simp [initResult,initBase.res,rv_simp,h6,hlo]
  · simp [initResult,initBase.res,rv_simp,h7,hhi]
  · intro r hr; cases r <;> simp_all [initResult,initBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl

def chooseCode (low : Bool) : List (BitVec 32) :=
  (words.drop (if low then 147 else 151)).take (if low then 4 else 3)
sym_block chooseLow := symRun {noAlias:=true} (chooseCode true) 0#64 6
sym_block chooseHigh := symRun {noAlias:=true} (chooseCode false) 0#64 6
def chooseResult (b : Nat) (low : Bool) : Result :=
  ⟨(if low then chooseLow.res.st else chooseHigh.res.st), .c (pcOf (b+154)),
    (if low then .jump else .endOfCode), (if low then 4 else 3), (if low then 4 else 3)⟩
theorem choose_run (b : Nat) (hb : Allowed b) (low : Bool) :
    symRun {noAlias:=true} (chooseCode low) (pcOf (b+if low then 147 else 151)) 6 = some (chooseResult b low) := by
  rcases hb with rfl|rfl <;> cases low <;> kernel_rfl

theorem choose_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (answer : BitVec 256) (low : Bool)
    (hpc : s.pc=pcOf (b+if low then 147 else 151))
    (h12 : s.getReg .x12=BitVec.ofNat 64 EOUT)
    (hlo : DigAt s EOUT (answer.extractLsb' 0 128))
    (hhi : DigAt s (EOUT+16) (answer.extractLsb' 128 128)) :
    ∃ t, Steps image s (if low then 4 else 3) (if low then 4 else 3) t ∧ t.pc=pcOf (b+154) ∧
      t.getReg .x6=(if low then answer.extractLsb' 0 128 else answer.extractLsb' 128 128).extractLsb' 0 64 ∧
      t.getReg .x7=(if low then answer.extractLsb' 0 128 else answer.extractLsb' 128 128).extractLsb' 64 64 ∧
      t.getReg .x29=(if low then 0 else 16) ∧
      RegsExcept s t [.x6,.x7,.x29] ∧ Frame s t (fun _=>False) := by
  have hc' := slice hc (if low then 147 else 151) (if low then 4 else 3) (by cases low <;> decide)
  refine ⟨_,symRun_sound (choose_run b hb low) hc' s hpc ?_,?_,?_,?_,?_,?_,?_⟩
  · cases low <;> simp [chooseResult,chooseLow.res,chooseHigh.res,rv_simp,h12,accessValid_iff,MEMORY_BYTES,EOUT]
  · cases low <;> rfl
  · cases low
    · simpa [chooseResult,chooseHigh.res,rv_simp,h12,EOUT] using hhi.1
    · simpa [chooseResult,chooseLow.res,rv_simp,h12,EOUT] using hlo.1
  · cases low
    · simpa [chooseResult,chooseHigh.res,rv_simp,h12,EOUT] using hhi.2
    · simpa [chooseResult,chooseLow.res,rv_simp,h12,EOUT] using hlo.2
  · cases low <;> rfl
  · intro r hr; cases low <;> cases r <;> simp_all [chooseResult,chooseLow.res,chooseHigh.res,rv_simp] <;> rfl
  · intro A _ _; cases low <;> rfl

end SigGolfCandidate.Choice.ProducerSelector
#print axioms SigGolfCandidate.Choice.ProducerSelector.head_spec
#print axioms SigGolfCandidate.Choice.ProducerSelector.init_spec
#print axioms SigGolfCandidate.Choice.ProducerSelector.choose_spec
