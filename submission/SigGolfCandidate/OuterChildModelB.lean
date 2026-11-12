import SigGolfCandidate.OuterChildModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterChildModelB
open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedBProof
open SigGolfCandidate.T3 (Digest M shortHash)
open SigGolfCandidate.FtsGrind

theorem program_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9)
    (raw : Fin 128) (ends : List Digest) (hf : SharedV3.first k.val=false) (hc : k.val≠8) :
    OuterChildModel.childProgram w index k raw ends=
      (OuterCopyChildB.program k.val index (SharedV3.physical k.val raw.val)
        (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends)
        (SharedV3.nodePad w k.val (SharedV3.physical k.val raw.val))
        (SharedV3.sibling w k.val (SharedV3.physical k.val raw.val))
        (SharedV3.nodeTw w k.val (SharedV3.physical k.val raw.val)) >>=fun r=>pure (r.2.2.2,r.1,r.2.1,r.2.2.1)) := by
  unfold OuterChildModel.childProgram OuterChildModel.child OuterCopyChildB.program OuterCopyTailB.program OuterNodeBankTailB.program level2C
  rw [(OuterChildModel.widths k).1,(OuterChildModel.widths k).2]
  simp only [SharedV3.lastLevel, hf, Bool.false_eq_true, ↓reduceIte, hc]
  have he : V3.leafInput k.val index raw.val (SharedV3.leafPad w k.val) ends =
      leafBytes (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends) := rfl
  rw [he]
  have h3 : W9Drv.ChildProof.heapOf 3 (SharedV3.physical k.val raw.val) =
      (128 + SharedV3.physical k.val raw.val) / 2 ^ (3 + 1) := W9Drv.ChildProof.heapOf_eq _ 3 (by decide)
  simp only [show List.range 5 = [0,1,2,3,4] from rfl, show List.range 2 = [0,1] from rfl,
    show List.range' 4 1 = [4] from rfl,
    List.foldlM_cons, List.foldlM_nil, SharedV3.childStepG, show (0:Nat) ≠ 3 by decide, show (0:Nat) ≠ 2 by decide,
    show (1:Nat) ≠ 2 by decide, false_and, true_and, if_false,
    show (1:Nat) ≠ 3 by decide, show (2:Nat) ≠ 3 by decide, show (4:Nat) ≠ 3 by decide, ↓reduceIte, bind_assoc,
    bind_map_left, pure_bind, childLevelP_eq, shared_input _ _ _ _ _ 0 (by decide),
    shared_input _ _ _ _ _ 1 (by decide), shared_input _ _ _ _ _ 2 (by decide),
    shared_input _ _ _ _ _ 4 (by decide), childLevelHi, hiSel]
  have h2 : W9Drv.ChildProof.heapOf 2 (SharedV3.physical k.val raw.val) =
      (128 + SharedV3.physical k.val raw.val) / 2 ^ (2 + 1) := W9Drv.ChildProof.heapOf_eq _ 2 (by decide)
  have h2' : ∀ j : Nat, 16 + j / 8 = (128 + j) / 8 := fun j => by omega
  have h3' : ∀ j : Nat, 8 + j / 16 = (128 + j) / 16 := fun j => by omega
  congr 1; funext v0; congr 1; funext v1
  by_cases hk4 : k.val < 4
  · first
      | (exfalso; omega)
      | (simp only [hk4, decide_true, if_true, and_true, true_and, bind_assoc, pure_bind, pre2C, right2C, preC, rightC,
          bitAt, nodeHeader, hpOf, SharedV3.nodeHPad, show (2:Nat) < 4 by decide, show (3:Nat) < 4 by decide,
          ↓reduceIte, selD, SigGolfCandidate.FtsGrind.halfOf, hiSel, heapOf, W9Drv.ChildProof.heapOf, Nat.reducePow,
          Nat.reduceSub, Nat.reduceAdd, h2', h3', show ∀ j : Nat, 2+j/64=(128+j)/64 from fun j=>by omega]
         rfl)
  · simp only [hk4, decide_false, Bool.false_eq_true, if_false, and_false, bind_assoc, bind_map_left,
      SharedV3.hashSel, V3.hashHi, SigGolfCandidate.T3.shortHash, pure_bind]
    rcases Bool.eq_false_or_eq_true (SharedV3.hiOut (SharedV3.physical k.val raw.val) (2 + 1)) with hh | hh
    all_goals simp only [hh, if_true, if_false, Bool.false_eq_true, bind_assoc, pure_bind, preC, rightC, bitAt,
      nodeHeader, hpOf, SharedV3.nodeHPad, show (3:Nat) < 4 by decide, ↓reduceIte, selD, hiSel,
      heapOf, W9Drv.ChildProof.heapOf, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, h2', h3', show ∀ j : Nat, 2+j/64=(128+j)/64 from fun j=>by omega]
    all_goals rfl

#print axioms program_eq
end OuterChildModelB
