import SigGolfCandidate.OuterGroundReplay
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterFixedRecover
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest

def recover (index coord : Nat) (selected : Child) (word : Rank) (values : Fin 6→Digest)
    (path : Nat→Digest) (n3 n2 n5 : Nat) (prev : PairRoot) : M PairRoot := do
  let inner←recoverSharedInnerN false index coord selected word values path n3 n2 prev
  let lr:=if selected.val/32%2=0 then (inner,path 5) else (path 5,inner)
  let outer←OuterGroundCore.hashN coord index (2+selected.val/64) n5 lr.1 lr.2
  pure (if selected.val/64%2=0 then (outer,path 6) else (path 6,outer))

theorem eval_recover (answers : Answers) (index coord : Nat) (selected : Child) (word : Rank)
    (values : Fin 6→Digest) (path : Nat→Digest) (prev : PairRoot) :
    let r:=evalWithAnswerFn answers (OuterRecover.recover index coord selected word values path prev)
    evalWithAnswerFn answers (recover index coord selected word values path r.2.1 r.2.2.1 r.2.2.2 prev)=r.1 := by
  unfold OuterRecover.recover recover
  simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
  rw [eval_recoverSharedInnerN]
  rw [(OuterGroundReplay.node_answer answers coord index _ _ _).2]
#print axioms eval_recover
end OuterFixedRecover
