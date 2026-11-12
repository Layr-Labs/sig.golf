import SigGolfCandidate.OuterCanonNodeExists
import SigGolfCandidate.OuterScanSelected
import SigGolfCandidate.OuterNodeReference
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option maxErrors 20
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction

theorem outer_step (answers : Answers) (labels : Labels) (ha : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (c : Nat)
    (hf : Extract.Paired.first coord.val=false) (hc : c<2)
    (n : WctNodePos) (hn : ftsNodeAt index coord 5 c=some n) :
    evalWithAnswerFn answers (OuterGroundCore.nodeAt coord.val index.val (2+c)
      (ftsLabel labels index coord 5 (2*c)) (ftsLabel labels index coord 5 (2*c+1)))=
      (wSelNonce labels n,Extract.Paired.proj (.wctNode index.val coord.val 5 c)
        (labels (.wctNode (wSelNode labels n)))) := by
  obtain ⟨m,hm,hmi,hmc,hml,hmx⟩:=OuterCanonBase.ftsNodeAt_some index coord 5 c (by decide) (by norm_num;omega)
  rw [hm] at hn
  obtain rfl:=Option.some.inj hn
  let left:=ftsLabel labels index coord 5 (2*c)
  let right:=ftsLabel labels index coord 5 (2*c+1)
  let response:=OuterGroundDeterministic.response answers coord.val index.val (2+c) left right
  have hcap : wTrialCap m.1.coord.val m.1.level.val=OuterGroundCore.cap coord.val := by
    rw [hmc,hml]
    unfold wTrialCap
    rw [if_pos ⟨rfl,hf⟩]
  have ht : ∀k,k≤wSelNonce labels m → response k=
      Extract.Paired.proj (.wctNode index.val coord.val 5 c) (labels (.wctNode (wWithNonce m k))) := by
    intro k hk
    have hact:=wActive_trial_of_le (labels:=labels) (n:=m) hk
    have hs:=wSelNonce_lt labels m
    have hb:=wTrialCap_le m.1.coord.val m.1.level.val
    have hx : cell (secretsOf answers) (.wctNode (wWithNonce m k)) labels=
        pad64 (WCT9.wctTopInput coord.val index.val (2+c) left (BitVec.ofNat 128 (k%2^64)) right) := by
      rw [cell_wctNode_active hact,wWithNonce_nonce m (by omega)]
      simp only [wWithNonce_index,wWithNonce_coord,wWithNonce_level,wWithNonce_idx,hmi,hmc,hml,hmx,
        show (7:Nat)-5-1=1 by decide,show (2:Nat)^1=2 by decide,
        if_neg (by decide : ¬(5:Nat)=4),
        if_pos (show OuterExtractGround.ftsNonceLevel coord.val 5 from Or.inr ⟨rfl,hf⟩)]
      rfl
    have he:=ha (.wctNode (wWithNonce m k))
    rw [hx] at he
    change evalWithAnswerFn answers (OuterGroundCore.hashN coord.val index.val (2+c) k left right)=_
    rw [OuterNodeReference.hash_response,OuterNodeValue.projection coord.val index.val c coord.isLt hf hc,he]
  have hfail : ∀k,wTrialFails labels m k ↔ OuterGroundCore.zeroOk coord.val
      (Extract.Paired.proj (.wctNode index.val coord.val 5 c) (labels (.wctNode (wWithNonce m k))))=false := by
    intro k
    unfold wTrialFails
    simp only [Node.toPos,hmi,hmc,hml,hmx,if_true]
  have hs:=wSelNonce_lt labels m
  have hspec:=wSelNonce_spec labels m
  have hscan : OuterGroundDeterministic.scan coord.val response (OuterGroundCore.cap coord.val-1) 0=
      (wSelNonce labels m,response (wSelNonce labels m)) := by
    apply OuterGroundDeterministic.scan_selected coord.val response _ _ _ (Nat.zero_le _) (by omega)
    · intro k _ hk
      rw [ht k (by omega)]
      exact (hfail k).mp (hspec.1 k hk)
    · rcases hspec.2 with hp|hp
      · left
        rw [ht _ le_rfl]
        have hh:=mt (hfail _).mpr hp
        simpa using hh
      · right
        omega
  rw [OuterGroundCore.nodeAt,OuterGroundDeterministic.eval_search]
  change OuterGroundDeterministic.scan coord.val response (OuterGroundCore.cap coord.val-1) 0=_
  rw [hscan,ht _ le_rfl]
  rfl
#print axioms outer_step
end OuterCanonBase.Paired
