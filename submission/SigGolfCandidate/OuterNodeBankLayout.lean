import SigGolfCandidate.OuterNodeHelper
import SigGolfCandidate.Merge091
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
namespace OuterNodeBankLayout
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeHelper

def bSite (j : Nat) : Nat := W9Drv.SharedBProof.ecIdx j 6
def cSite (j : Nat) : Nat := W9Drv.SharedCProof.ecIdx j 6

def patch (old : List (BitVec 32)) (site : Nat) (helper : List (BitVec 32)) : List (BitVec 32) :=
  old.take site++[0x80006f]++(old.drop (site+1)).take 1++helper++old.drop (site+2+helper.length)

def bWords (j : Nat) : List (BitVec 32) := patch (W9Drv.SharedBProof.childWords j) (bSite j) bCode
def cWords (j : Nat) : List (BitVec 32) := patch (W9Drv.SharedCProof.childWords j) (cSite j) cCode

theorem b_space : ∀ j : Fin 128,
    (W9Drv.SharedBProof.childWords j.val).length=64 ∧ bSite j.val+2+bCode.length≤64 ∧
    ((W9Drv.SharedBProof.childWords j.val).drop (bSite j.val+2)).take bCode.length=
      List.replicate bCode.length 0x13 := by decide +kernel

theorem c_space : ∀ j : Fin 128,
    (W9Drv.SharedCProof.childWords j.val).length=64 ∧ cSite j.val+2+cCode.length≤64 ∧
    ((W9Drv.SharedCProof.childWords j.val).drop (cSite j.val+2)).take cCode.length=
      List.replicate cCode.length 0x13 := by decide +kernel

theorem b_slices : ∀ j : Fin 128,
    (bWords j.val).length=64 ∧
    ((bWords j.val).drop (bSite j.val+2)).take bCode.length=bCode ∧
    (bWords j.val).take (bSite j.val)=(W9Drv.SharedBProof.childWords j.val).take (bSite j.val) ∧
    (bWords j.val)[bSite j.val]?=some 0x80006f ∧
    (bWords j.val)[bSite j.val+1]?=(W9Drv.SharedBProof.childWords j.val)[bSite j.val+1]? := by decide +kernel

theorem c_slices : ∀ j : Fin 128,
    (cWords j.val).length=64 ∧
    ((cWords j.val).drop (cSite j.val+2)).take cCode.length=cCode ∧
    (cWords j.val).take (cSite j.val)=(W9Drv.SharedCProof.childWords j.val).take (cSite j.val) ∧
    (cWords j.val)[cSite j.val]?=some 0x80006f ∧
    (cWords j.val)[cSite j.val+1]?=(W9Drv.SharedCProof.childWords j.val)[cSite j.val+1]? := by decide +kernel

theorem b_helper_code {im : Image} (j : Fin 128)
    (hc : CodeAt im (pcOf (W9Drv.SharedBProof.childBase j.val)) (bWords j.val)) :
    CodeAt im (pcOf (W9Drv.SharedBProof.childBase j.val+bSite j.val+2)) bCode := by
  have hs:=b_slices j
  have hb:=b_space j
  have h:=SigGolfCandidate.FtsGrind.codeAt_sub (bSite j.val+2) hc (by rw [hs.1];omega) hs.2.1
  simpa only [Nat.add_assoc] using h

theorem c_helper_code {im : Image} (j : Fin 128)
    (hc : CodeAt im (pcOf (W9Drv.SharedCProof.childBase j.val)) (cWords j.val)) :
    CodeAt im (pcOf (W9Drv.SharedCProof.childBase j.val+cSite j.val+2)) cCode := by
  have hs:=c_slices j
  have hb:=c_space j
  have h:=SigGolfCandidate.FtsGrind.codeAt_sub (cSite j.val+2) hc (by rw [hs.1];omega) hs.2.1
  simpa only [Nat.add_assoc] using h

#print axioms b_helper_code
#print axioms c_helper_code

#print axioms b_space
#print axioms c_space
#print axioms b_slices
#print axioms c_slices
end OuterNodeBankLayout
