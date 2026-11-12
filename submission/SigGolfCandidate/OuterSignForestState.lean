import SigGolfCandidate.OuterSignForestGood
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignForestState
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Sign (Base BaseA NeverW FLEAF ENC)
open SigGolfCandidate.T3M.Keygen (PRIV REGION NODE CHAIN ZDIG)
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedCoordinate

def Writes (A : Nat) : Prop:=WriteArea A ∨ FinalW A ∨ A=1152 ∨ A=1160

theorem coordinate_area {c A : Nat} (hc : c<9) (h : OuterSignCoordinate.coordinateW c A) :
    WriteArea A ∨ A=1152 ∨ A=1160 := by
  have ho : coordinateW c A ∨ A=1152 ∨ A=1160 := by
    unfold OuterSignCoordinate.coordinateW OuterSignCoordinate.allWrites OuterSignCoordinate.writes
      coordinateW allWrites at *
    tauto
  rcases ho with ho|ho|ho
  · exact Or.inl (coordinate_write_area hc ho)
  · exact Or.inr (Or.inl ho)
  · exact Or.inr (Or.inr ho)

theorem write_frame {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : OuterSignForestGood.ClosedPost sk a s rv t) : Frame s t Writes := by
  apply h.frame.mono
  intro A hA hw
  rcases hw with hw|hw|hw|hw|⟨c,hc,hw⟩|hw
  · exact Or.inl (Or.inr (by subst A;decide))
  · exact Or.inl (Or.inr (by subst A;decide))
  · exact Or.inl (Or.inr (by subst A;decide))
  · exact Or.inl (Or.inr (by subst A;decide))
  · rcases coordinate_area hc hw with hw|hw|hw
    · exact Or.inl hw
    · exact Or.inr (Or.inr (Or.inl hw))
    · exact Or.inr (Or.inr (Or.inr hw))
  · exact Or.inr (Or.inl hw)

theorem base {sk a : BitVec 256} {cache : Bytes 131072} {cfFlag : Nat}
    {s t : MachineState} {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (hb : Base (cfFlag:=cfFlag) sk cache s) (h : OuterSignForestGood.ClosedPost sk a s rv t) :
    Base (cfFlag:=cfFlag) sk cache t := by
  apply SharedState.base_frame_mem hb (write_frame h) h.x5
  intro A hA hb hw
  unfold BaseA NeverW at hb
  unfold Writes WriteArea FinalW at hw
  simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,SigGolfCandidate.T3M.Sign.NBUF,Search.TOP_DATA,SIG,FOUT] at hb hw
  omega

theorem rho {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : OuterSignForestGood.ClosedPost sk a s rv t) {rho : BitVec 128} (hr : DigAt s SIG rho) : DigAt t SIG rho :=
  hr.frame (write_frame h) (by unfold SIG;decide)
    (by unfold Writes WriteArea FinalW SIG FOUT;decide) (by unfold Writes WriteArea FinalW SIG FOUT;decide)

theorem counter {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : OuterSignForestGood.ClosedPost sk a s rv t) :
    t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32)) :=
  (write_frame h).get (by unfold ENC;decide) (by unfold Writes WriteArea FinalW SIG FOUT ENC;decide)

theorem index {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : OuterSignForestGood.ClosedPost sk a s rv t) : t.getMem 0x20550=s.getMem 0x20550 :=
  (write_frame h).get (A:=0x20550) (by decide) (by unfold Writes WriteArea FinalW SIG FOUT;decide)
#print axioms write_frame
#print axioms base
#print axioms rho
#print axioms counter
#print axioms index
end OuterSignForestState
