import SigGolfCandidate.OuterWitnessNonceWords
import SigGolfCandidate.OuterWitnessReadout
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterWitnessOuterPad
open RiscvZkvm.Rv64 SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open OuterExpand

def coord (k : Fin 5) : Fin 9:=⟨outerCoord k.val,by fin_cases k <;> decide⟩
theorem first_false (k : Fin 5) : SharedV3.first (coord k).val=false := by fin_cases k <;> decide

theorem high_free : ∀k : Fin 5,∀c : Fin 5,
    outerNoncePos k.val+8+8≤outerNoncePos c.val ∨ outerNoncePos c.val+8≤outerNoncePos k.val+8 := by decide +kernel

theorem old_zero (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (k : Fin 5) :
    W9Machine.wdig (witEncF16 output w) (outerNoncePos k.val)=0 := by
  have hp:=pathReadout_witEncF16 output w (coord k)
  have hl : 5≤SharedV3.lastLevel (coord k).val:=by simp only [SharedV3.lastLevel,first_false,if_false];decide
  have hz:=hp.nodePads 5 hl (by decide) (by decide) (by decide)
  simpa only [SharedV3.nodePad,SharedV3.blkOff,show ¬(5:Nat)<5 by decide,if_false,coord,outerNoncePos] using hz

theorem pad (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (k : Fin 5) (child : Nat) :
    SharedV3.nodePad (witEncOuter output w ns) (coord k).val child 5=nDig (ns.getD k.val 0) := by
  change W9Machine.wdig (witEncOuter output w ns) (outerNoncePos k.val)=_
  have hlo : (W9Machine.wdig (witEncOuter output w ns) (outerNoncePos k.val)).extractLsb' 0 64=
      BitVec.ofNat 64 (ns.getD k.val 0):=by
    rw [W9Machine.wdig_lo]
    exact OuterWitnessNonceWords.word output w ns k
  have hhi : (W9Machine.wdig (witEncOuter output w ns) (outerNoncePos k.val)).extractLsb' 64 64=0:=by
    rw [PairedReadout.wdig_hi_extract]
    rw [OuterWitnessFreePadded.extract output w ns (outerNoncePos k.val+8) 8 (by
      intro c hc
      exact high_free k ⟨c,hc⟩)]
    rw [←PairedReadout.wdig_hi_extract]
    exact congrArg (fun d : Digest=>d.extractLsb' 64 64) (old_zero output w k)
  apply BitVec.eq_of_toNat_eq
  have hl:=congrArg BitVec.toNat hlo
  have hh:=congrArg BitVec.toNat hhi
  have hz : (0 : BitVec 64).toNat=0:=rfl
  rw [hz] at hh
  have hd:=(W9Machine.wdig (witEncOuter output w ns) (outerNoncePos k.val)).isLt
  simp only [nDig,BitVec.toNat_ofNat,BitVec.extractLsb'_toNat,Nat.shiftRight_zero,Nat.shiftRight_eq_div_pow,
    Nat.reducePow,BitVec.toNat_zero,Nat.div_one] at hl hh hd ⊢
  omega
#print axioms old_zero
#print axioms pad
end OuterWitnessOuterPad
