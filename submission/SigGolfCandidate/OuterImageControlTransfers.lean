import SigGolfCandidate.OuterImageHelpers
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImageControlTransfers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterImages

theorem word (a : Nat) (w : BitVec 32) (ha : a<235776) (hw : ∀ old,expandPatch a old=w) :
    CodeAt expandImage (pcOf a) [w] := by
  apply OuterImageHelpers.expand_chunk a [w] (by simp only [List.length_singleton];omega)
  intro i hi old
  have hi0 : i=0 := by simp only [List.length_singleton] at hi;omega
  subst i
  exact hw old

#check word

theorem entry : CodeAt expandImage (pcOf 0) [jump 0 88300] := word 0 (jump 0 88300) (by decide) (by intro old;rfl)
#check entry
theorem post_jump : CodeAt expandImage (pcOf 84218) [jump 84218 88260] := word 84218 (jump 84218 88260) (by decide) (by intro old;rfl)
#check post_jump
theorem post_halt : CodeAt expandImage (pcOf 88280) [0x73] := word 88280 0x73 (by decide) (by intro old;rfl)
#check post_halt
theorem unpack_return : CodeAt expandImage (pcOf 88338) [jump 88338 87500] := word 88338 (jump 88338 87500) (by decide) (by intro old;rfl)

#check unpack_return

theorem sign_halt : CodeAt signImage (pcOf 26240) [0x73] := by
  apply CodeAt.of_append
    (pre:=(Images.signCode.take 26156).mapIdx signPatch ++ OuterSignImageLayout.code ++ OuterCodecMachine.packCode)
    (post:=Images.signCode.drop 26241)
    (by simp [signImage,signCode,List.append_assoc])
  · simp only [List.length_append,List.length_mapIdx,List.length_take,Images.signCode_length,pcOf]
    decide +kernel
  · simp only [List.length_append,List.length_mapIdx,List.length_take,Images.signCode_length]
    decide +kernel

#print axioms entry
#print axioms post_jump
#print axioms post_halt
#print axioms unpack_return
#print axioms sign_halt
end OuterImageControlTransfers
