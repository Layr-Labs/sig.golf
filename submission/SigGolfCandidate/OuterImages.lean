import SigGolfCandidate.OuterSharedBank
import SigGolfCandidate.OuterSignImageLayout
import SigGolfCandidate.OuterCodecMachine
import SigGolfCandidate.OuterNoncePostMachine
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterImages
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind

def jump (site target : Nat) : BitVec 32 := encJal 0 (jOff site target)
def logicalChild (block : Nat) : Nat := block/2+64*(block%2)

def signPatch (i : Nat) (w : BitVec 32) : BitVec 32 :=
  if i=1977 then w-BitVec.ofNat 32 (2^20)
  else if i=25338 then jump i 26156
  else if i=25963 then jump i 26207
  else w

def signCode : List (BitVec 32) := Images.signCode.mapIdx signPatch++OuterSignImageLayout.code++OuterCodecMachine.packCode++[0x73]

def expandPatch (i : Nat) (w : BitVec 32) : BitVec 32 :=
  if i=0 then jump 0 88300
  else if i=54334 then w-BitVec.ofNat 32 (2^20)
  else if i=84218 then jump i 88260
  else if 88260 ≤ i  ∧  i < 88280 then OuterNoncePostMachine.postCode.getD (i-88260) 0
  else if i=88280 then 0x73
  else if 88300 ≤ i  ∧  i < 88338 then OuterCodecMachine.unpackCode.getD (i-88300) 0
  else if i=88338 then jump i 87500
  else w

def expandPrefix : List (BitVec 32) := (Images.expandCode.take 235776).mapIdx expandPatch
def bBank : List (BitVec 32) := (List.range 128).flatMap (fun b=>OuterNodeBankLayout.bWords (logicalChild b))
def cBank : List (BitVec 32) := (List.range 128).flatMap (fun b=>OuterNodeBankLayout.cWords (logicalChild b))
def gap : List (BitVec 32) := (Images.expandCode.drop 243968).take 2496
def expandCode : List (BitVec 32) := expandPrefix++cBank++gap++bBank

def signImage : SigGolfCandidate.Legacy.Riscv.Image := ⟨signCode,Images.signData⟩
def expandImage : SigGolfCandidate.Legacy.Riscv.Image := ⟨expandCode,Images.expandData⟩
def images : ClaudeWCT.W9.T3M.Images := ⟨signImage,expandImage,Images.verifyImage⟩

theorem sign_length : signCode.length=26241 := by
  simp only [signCode,List.length_append,List.length_mapIdx,Images.signCode_length]
  decide +kernel

theorem prefix_length : expandPrefix.length=235776 := by
  simp only [expandPrefix,List.length_mapIdx,List.length_take,Images.expandCode_length]
  decide +kernel

theorem banks_length : bBank.length=8192  ∧  cBank.length=8192 := by decide +kernel

theorem gap_length : gap.length=2496 := by
  simp only [gap,List.length_take,List.length_drop,Images.expandCode_length]
  decide +kernel

theorem expand_length : expandCode.length=254656 := by
  simp only [expandCode,List.length_append,prefix_length,banks_length.1,banks_length.2,gap_length]

theorem expand_payload : 4*expandImage.code.length+expandImage.data.length=1048560 := by
  simp only [expandImage,expand_length,Images.expandData_length]

theorem verify_unchanged : images.verify=Images.verifyImage := rfl

#print axioms sign_length
#print axioms expand_length
#print axioms expand_payload
end OuterImages
