import SigGolfCandidate.Choice.ProducerSelectorClosed
import SigGolfCandidate.T3M.ImageSlice
import SigGolfCandidate.T3M.Images.Slices

namespace SigGolfCandidate.Choice.ProducerSelector
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

theorem code_length (b : Nat) : (code b).length=157 := by
  simp [code,words_length]

theorem at_sign : FullAt Images.signImage 21942 := by
  apply codeAt_slice
  · rw [code_length]; decide
  · change (Images.signCode.drop 21942).take (code 21942).length=code 21942
    rw [code_length,Images.Slices.signCode_drop_eq _ (by decide)]
    decide +kernel

theorem at_expand : FullAt Images.expandImage 44046 := by
  apply codeAt_slice
  · rw [code_length]; decide
  · change (Images.expandCode.drop 44046).take (code 44046).length=code 44046
    rw [code_length,Images.Slices.expandCode_drop_eq _ (by decide)]
    decide +kernel

def entryPC (b : Nat) : Nat := if b=21942 then 1523 else 1272
def entryWord (b : Nat) : BitVec 32 := if b=21942 then 0x70d1306f else 0x4592906f
def EntryAt (image : Image) (b : Nat) : Prop := CodeAt image (pcOf (entryPC b)) [entryWord b]

theorem entry_at_sign : EntryAt Images.signImage 21942 := by
  apply codeAt_slice (by decide +kernel)
  change (Images.signCode.drop 1523).take 1=[entryWord 21942]
  rw [Images.Slices.signCode_drop_eq _ (by decide)]
  decide +kernel

theorem entry_at_expand : EntryAt Images.expandImage 44046 := by
  apply codeAt_slice (by decide +kernel)
  change (Images.expandCode.drop 1272).take 1=[entryWord 44046]
  rw [Images.Slices.expandCode_drop_eq _ (by decide)]
  decide +kernel

def entryResult (b : Nat) : Result := ⟨SymState.init,.c (pcOf b),.jump,1,1⟩
theorem entry_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} [entryWord b] (pcOf (entryPC b)) 2=some (entryResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem entry_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : EntryAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (entryPC b)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf b ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (entry_run b hb) hc s hpc
    (by simp [entryResult,SymState.init,rv_simp]),rfl,?_,?_⟩
  · intro r _; cases r <;> rfl
  · intro A _ _; rfl

end SigGolfCandidate.Choice.ProducerSelector
#print axioms SigGolfCandidate.Choice.ProducerSelector.at_sign
#print axioms SigGolfCandidate.Choice.ProducerSelector.at_expand
#print axioms SigGolfCandidate.Choice.ProducerSelector.entry_at_sign
#print axioms SigGolfCandidate.Choice.ProducerSelector.entry_at_expand
#print axioms SigGolfCandidate.Choice.ProducerSelector.entry_spec
