import SigGolfCandidate.Merge123
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterVerifyBudget
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route leafHash pad64)
open ClaudeWCT.WCT9 (LayerMsg)

def CreditFloors74 (floors : Layer→Nat) : Prop:=
  (∀lay,floors lay≤301) ∧ 73≤((List.finRange 4).map floors).sum

theorem after_good (floors : SigGolfCandidate.T3.Layer → Nat) (hcredit : CreditFloors74 floors) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (Q : Prop) (hQ : Q) (a : HashOutput)
    (top : Digest × Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ top u) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) u 8050 13750 Q 5231
      (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb) := by
  have hidx : ClaudeWCT.WCT9.digestIndex a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ top.1 top.2 u hidx h.glob h.idx h.pc h.left h.right h.wit h.base h.a1
    h.s10 h.heapTwo h.heapThree h.heapFour h.heapFive h.coordStep h.topBase h.top h.top8 h.a2 h.d0
  have hg := layers_good floors hcredit.1 w pk _ hidx Q hQ 4 le_rfl (.pair top.1 top.2) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb =
      ccM (BC.layerLoop w (ClaudeWCT.WCT9.digestIndex a) 4 (.pair top.1 top.2)) (kFin pk) := by
    unfold afterFts
    rw [ccM_bind]
    rfl
  rw [e]
  rw [lFuel_4, lCyc_4, lCycA_4 floors hcredit.1] at hg
  have htotal := hcredit.2
  exact GoodQP.stepsQ hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)

theorem installed_good (floors : Layer→Nat) (hcredit : CreditFloors74 floors)
    (message : Message) (pk : PublicKey) (witness : ClaudeWCT.W9.T3M.WBytes) (state : MachineState)
    (hstate : initialState submission .verify (message,pk,witness)=some state) :
    GoodQP
      (W9Fin.V7.Canonical.Pre (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh witness))
        SigGolfCandidate.Research.SharedForest.jointAccountingCost 776 message witness)
      state 10083 15784 True 6873
      (ccM (ClaudeWCT.W9.T3M.Paired.verifyP message pk witness) Kb) := by
  have H:=W9Fin.V7.Canonical.verify_good (cap:=776) (ovh:=855) (aG:=5231)
    (P:=fun w=>HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) W9Fin.V7.prefixGood
    (fun _=>W9Fin.V7.Canonical.fts_installed)
    (fun pk w Q hQ answer top state hstate=>after_good floors hcredit pk w Q hQ answer top state hstate)
    (fun _ _ _=>rfl) message pk witness state hstate
  rw [←W9Fin.V7.Canonical.paired_verifyP_eq] at H
  exact H
#print axioms after_good
#print axioms installed_good
end OuterVerifyBudget
