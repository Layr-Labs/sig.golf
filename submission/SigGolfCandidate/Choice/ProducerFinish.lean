import SigGolfCandidate.Choice.ProducerSelectorImages

/-! The expander copies the saved canonical selector into the spare witness word
before its existing successful exit. No additional hash query is made. -/
namespace SigGolfCandidate.Choice.ProducerFinish
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option Elab.async false
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

def words : List (BitVec 32) := [0x20e37,0x458e3e03,0x53c03423]

theorem jump_at : CodeAt Images.expandImage (pcOf 43763) [0x6e00006f] := by
  apply codeAt_slice (by decide)
  change (Images.expandCode.drop 43763).take 1=[0x6e00006f]
  rw [Images.Slices.expandCode_drop_eq _ (by decide)]
  decide +kernel

theorem body_at : CodeAt Images.expandImage (pcOf 44203) words := by
  apply codeAt_slice (by decide)
  change (Images.expandCode.drop 44203).take words.length=words
  rw [Images.Slices.expandCode_drop_eq _ (by decide)]
  decide +kernel

theorem halt_at : CodeAt Images.expandImage (pcOf 44206) [0x73] := by
  apply codeAt_slice (by decide)
  change (Images.expandCode.drop 44206).take 1=[0x73]
  rw [Images.Slices.expandCode_drop_eq _ (by decide)]
  decide +kernel

def At (im : Image) : Prop :=
  CodeAt im (pcOf 43763) [0x6e00006f] ∧ CodeAt im (pcOf 44203) words ∧
    CodeAt im (pcOf 44206) [0x73]

theorem at_expand : At Images.expandImage := ⟨jump_at,body_at,halt_at⟩

def jumpResult : Result := ⟨SymState.init,.c (pcOf 44203),.jump,1,1⟩
theorem jump_run : symRun {noAlias:=true} [0x6e00006f] (pcOf 43763) 2=some jumpResult := by
  kernel_rfl

theorem jump_spec {im : Image} (ha : At im) (s : MachineState) (hpc : s.pc=pcOf 43763) :
    ∃ t, Steps im s 1 1 t ∧ t.pc=pcOf 44203 ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound jump_run ha.1 s hpc
    (by simp [jumpResult,SymState.init,rv_simp]),rfl,?_,?_⟩
  · intro r _; cases r <;> rfl
  · intro A _ _; rfl

sym_block body := symRun {noAlias:=true} words (pcOf 44203) 4

theorem body_spec {im : Image} (ha : At im) (s : MachineState) (hpc : s.pc=pcOf 44203) (hint : Word)
    (hh : s.getMem (BitVec.ofNat 64 ProducerSelector.HINT)=hint) :
    ∃ t, Steps im s 3 3 t ∧ t.pc=pcOf 44206 ∧
      t.getMem (BitVec.ofNat 64 1320)=hint ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=1320) := by
  refine ⟨_,symRun_sound body ha.2.1 s hpc
    (by simp [body.res,rv_simp,accessValid_iff,MEMORY_BYTES]),?_,?_,?_,?_⟩
  · rfl
  · simpa [body.res,rv_simp,ProducerSelector.HINT] using hh
  · intro r hr; cases r <;> simp_all [body.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,body.res]
    t3n []
    rw [if_neg (by omega)]

/-- Four ordinary instructions transfer the selector and reach the successful
ECALL, preserving every register other than x28 and every other memory word. -/
theorem finish_spec_of {im : Image} (ha : At im) (s : MachineState) (hpc : s.pc=pcOf 43763) (hint : Word)
    (hh : s.getMem (BitVec.ofNat 64 ProducerSelector.HINT)=hint) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf 44206 ∧
      t.getMem (BitVec.ofNat 64 1320)=hint ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=1320) ∧
      fetch im t=some (.base .ECALL) := by
  obtain ⟨u,su,pu,ru,fu⟩ := jump_spec ha s hpc
  obtain ⟨t,st,pt,ht,rt,ft⟩ := body_spec ha u pu hint
    (by rw [fu.get (by decide) (by simp)]; exact hh)
  exact ⟨t,su.trans st,pt,ht,(ru.trans rt).mono (by simp),
    (fu.trans ft).mono (by simp),ha.2.2.fetch _ pt⟩

theorem finish_spec (s : MachineState) (hpc : s.pc=pcOf 43763) (hint : Word)
    (hh : s.getMem (BitVec.ofNat 64 ProducerSelector.HINT)=hint) :
    ∃ t, Steps Images.expandImage s 4 4 t ∧ t.pc=pcOf 44206 ∧
      t.getMem (BitVec.ofNat 64 1320)=hint ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=1320) ∧
      fetch Images.expandImage t=some (.base .ECALL) :=
  finish_spec_of at_expand s hpc hint hh

end SigGolfCandidate.Choice.ProducerFinish
#print axioms SigGolfCandidate.Choice.ProducerFinish.finish_spec
