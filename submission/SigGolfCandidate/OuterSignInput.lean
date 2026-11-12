import SigGolfCandidate.OuterSignPlainFinish
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignInput
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.FtsGrind
variable {tb ret heap A D : Nat} {pre mid right : List UInt8} {s u : MachineState}
  (F : SignIn tb ret heap A D pre mid right s)
  (hr : RegsExcept s u [.x16,.x17])
  (hf : Frame s u (fun X=>X=1104 ∨ X=1112 ∨ X=1136))
  (hA : 2048≤A) (hAi : A<2^20) (hD : 2048≤D) (hDi : D<2^20)
include F hr hf hA hAi hD hDi

theorem plain : OuterSignPlain.Input A D (pre++mid++right) u := by
  have g : ∀ r,r∉[Reg.x16,.x17]→u.getReg r=s.getReg r:=hr
  refine ⟨by rw [g _ (by decide)];exact F.x5,by rw [g _ (by decide)];exact F.x10,
    by rw [g _ (by decide)];exact F.x11,by rw [g _ (by decide)];exact F.x12,
    by simp only [List.length_append,F.lpre,F.lmid,F.lright],?_,hA,hAi,F.hA,hD,hDi,F.hD⟩
  have nb : ∀ X,A≤X→X<A+64→¬(X=1104 ∨ X=1112 ∨ X=1136) := by intros;omega
  rw [show (8:Nat)=4+(2+2) from rfl,readWords_add,readWords_add,
    frame_readWordsG hf A 4 (by have:=F.hA2;omega) (fun i hi=>nb _ (by omega) (by omega)),
    show A+8*4=A+32 by omega,
    frame_readWordsG hf (A+32) 2 (by have:=F.hA2;omega) (fun i hi=>nb _ (by omega) (by omega)),
    show A+32+8*2=A+48 by omega,
    frame_readWordsG hf (A+48) 2 (by have:=F.hA2;omega) (fun i hi=>nb _ (by omega) (by omega)),
    F.mpre,F.mmid,F.mright,wordsOf_append _ _ (by simp [List.length_append,F.lpre,F.lmid]),wordsOf_append _ _ (by simp [F.lpre]),List.append_assoc]

theorem search : OuterNodeSearchInvariant.Input A D pre right u := by
  have g : ∀ r,r∉[Reg.x16,.x17]→u.getReg r=s.getReg r:=hr
  refine ⟨by rw [g _ (by decide)];exact F.x5,by rw [g _ (by decide)];exact F.x10,
    by rw [g _ (by decide)];exact F.x11,by rw [g _ (by decide)];exact F.x12,F.lpre,F.lright,?_,?_,hA,hAi,F.hA,hD,hDi,F.hD,F.hAD.symm⟩
  · rw [frame_readWordsG hf A 4 (by have:=F.hA2;omega) (by intros;omega)]
    exact F.mpre
  · rw [frame_readWordsG hf (A+48) 2 (by have:=F.hA2;omega) (by intros;omega)]
    exact F.mright
#print axioms plain
#print axioms search
end OuterSignInput
