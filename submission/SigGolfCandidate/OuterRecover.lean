import SigGolfCandidate.OuterCoordinateCorrectness
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterRecover
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest OuterCoordinateCorrectness
abbrev A := SigGolfCandidate.T3.Correctness.Answers

def recover (index coord : Nat) (selected : Child) (word : Rank) (values : Fin 6 → Digest)
    (path : Nat → Digest) (prev : PairRoot) : M (PairRoot × Nat × Nat × Nat) := do
  let inner←recoverSharedInner false index coord selected word values path prev
  let lr:=if selected.val/32%2=0 then (inner.1,path 5) else (path 5,inner.1)
  let outer←OuterGroundCore.nodeAt coord index (2+selected.val/64) lr.1 lr.2
  pure (if selected.val/64%2=0 then (outer.2,path 6) else (path 6,outer.2),inner.2.1,inner.2.2,outer.1)

theorem heap_pair7 (f : Nat → Digest) (selected level : Nat) (hs : selected<128) (hl : level<7) :
    (if selected/2^level%2=0 then
      (f ((128+selected)/2^level),f (((128+selected)/2^level) ^^^ 1)) else
      (f (((128+selected)/2^level) ^^^ 1),f ((128+selected)/2^level)))=
      (f (2*((128+selected)/2^(level+1))),f (2*((128+selected)/2^(level+1))+1)) := by
  have hp : selected/2^level%2=(128+selected)/2^level%2 := by interval_cases level <;> norm_num <;> omega
  rw [hp,sibling_pair f ((128+selected)/2^level)]
  have hd : (128+selected)/2^level/2=(128+selected)/2^(level+1) := by rw [Nat.div_div_eq_div_mul,pow_succ]
  rw [hd]

theorem honest (answers : A) (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (values : Fin 6 → Digest) (path : Nat → Digest)
    (hv : ∀ i,values i=chainValue answers index coord (rawChild false selected.val) word i)
    (hp : ∀ level,level<7→path level=authAt (nodes answers index coord pads) selected.val level) :
    (evalWithAnswerFn answers (recover index coord selected word values path (pads (selected.val/64)))).1=
      ((nodes answers index coord pads).getD 2 0,(nodes answers index coord pads).getD 3 0) := by
  have hin:=recover_inner answers index coord selected word pads values path hv (fun l hl => hp l (by omega))
  unfold recover
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  rw [hin,hp 5 (by decide),hp 6 (by decide)]
  unfold authAt
  have he : (128+selected.val)/2^(5+1)=2+selected.val/64 := by norm_num;omega
  have hlr:=heap_pair7 (fun j => (nodes answers index coord pads).getD j 0) selected.val 5 selected.isLt (by decide)
  rw [he] at hlr
  norm_num only [Nat.reducePow] at hlr
  change (if selected.val/64%2=0 then
    ((evalWithAnswerFn answers (OuterGroundCore.nodeAt coord index (2+selected.val/64)
      (if selected.val/32%2=0 then ((nodes answers index coord pads).getD ((128+selected.val)/32) 0,
        (nodes answers index coord pads).getD (((128+selected.val)/32) ^^^ 1) 0) else
        ((nodes answers index coord pads).getD (((128+selected.val)/32) ^^^ 1) 0,
          (nodes answers index coord pads).getD ((128+selected.val)/32) 0)).1
      (if selected.val/32%2=0 then ((nodes answers index coord pads).getD ((128+selected.val)/32) 0,
        (nodes answers index coord pads).getD (((128+selected.val)/32) ^^^ 1) 0) else
        ((nodes answers index coord pads).getD (((128+selected.val)/32) ^^^ 1) 0,
          (nodes answers index coord pads).getD ((128+selected.val)/32) 0)).2)).2,
      (nodes answers index coord pads).getD (((128+selected.val)/64) ^^^ 1) 0) else _) = _
  norm_num only [Nat.reducePow]
  rw [hlr]
  by_cases h : selected.val<64
  · have hq : selected.val/64=0 := by omega
    have hq' : (128+selected.val)/64=2 := by omega
    simp only [hq,hq',Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod,Nat.reduceEqDiff,↓reduceIte]
    rw [←top2]
    rfl
  · have hq : selected.val/64=1 := by have := selected.isLt;omega
    have hq' : (128+selected.val)/64=3 := by have := selected.isLt;omega
    simp only [hq,hq',Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod,Nat.reduceEqDiff,↓reduceIte]
    rw [←top3]
    rfl

#print axioms honest
end OuterRecover
