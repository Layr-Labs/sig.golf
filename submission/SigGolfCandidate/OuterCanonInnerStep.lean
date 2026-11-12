import SigGolfCandidate.OuterCanonNodeExists
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
theorem inner_step (answers : Answers) (labels : Labels) (ha : Agrees answers labels)
    (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hg : Extract.Paired.ftsNonceLevel coord.val level)
    (hc : c < 2^(6-level)) (n : WctNodePos) (hn : ftsNodeAt index coord level c = some n) :
    evalWithAnswerFn answers (WCT9.ftsNodeAt coord.val index.val (2^(6-level)+c)
      (ftsLabel labels index coord level (2*c)) (ftsLabel labels index coord level (2*c+1))) =
      (wSelNonce labels n, Extract.Paired.proj (.wctNode index.val coord.val level c)
        (labels (.wctNode (wSelNode labels n)))) := by
  have h23 := Extract.Paired.ftsNonceLevel_le hg
  have hgr := (Extract.Paired.ftsNonceLevel_node (coord := coord.val) (by omega) hc).mp hg
  obtain ⟨m, hm, hmi, hmc, hml, hmx⟩ := OuterCanonBase.ftsNodeAt_some index coord level c (by omega)
    (by rwa [show 7-level-1=6-level by omega])
  rw [hm] at hn
  obtain rfl := Option.some.inj hn
  have hcap : WCT9.ftsNonceCap coord.val (2^(6-level)+c) = wTrialCap m.1.coord.val m.1.level.val := by
    unfold wTrialCap OuterCanonBase.wTrialCap
    rw [hml,hmc,if_neg (by omega : ¬(level=5 ∧ Extract.Paired.first coord.val=false)),if_pos hg, Extract.Paired.ftsNonceCap_level coord.val level c (by omega) hc]
  have hproj : ∀ y, Extract.Paired.proj (.wctNode index.val coord.val level c) y = WCT9.ftsHalf (2^(6-level)+c) y :=
    fun y => by rw [Extract.Paired.proj_wctNode_packed index.val coord.val level c h23.2 hc]
  have htrial : ∀ k ≤ wSelNonce labels m, evalWithAnswerFn answers (WCT9.ftsNodeHashN coord.val index.val
      (2^(6-level)+c) k (ftsLabel labels index coord level (2*c)) (ftsLabel labels index coord level (2*c+1))) =
      Extract.Paired.proj (.wctNode index.val coord.val level c) (labels (.wctNode (wWithNonce m k))) := by
    intro k hk
    have hact := wActive_trial_of_le (labels := labels) (n := m) hk
    have hs := wSelNonce_lt labels m
    have hcl := wTrialCap_le m.1.coord.val m.1.level.val
    have hx : cell (secretsOf answers) (.wctNode (wWithNonce m k)) labels =
        pad64 (WCT9.ftsNodeInputN coord.val index.val (2^(6-level)+c) k
          (ftsLabel labels index coord level (2*c)) (ftsLabel labels index coord level (2*c+1))) := by
      rw [cell_wctNode_active hact, wWithNonce_nonce m (by omega)]
      simp only [wWithNonce_index, wWithNonce_coord, wWithNonce_level, wWithNonce_idx, hmi, hmc, hml, hmx,
        show 7-level-1=6-level by omega, if_neg (show level ≠ 4 by omega), if_pos (show OuterExtractGround.ftsNonceLevel coord.val level from Or.inl hg)]
      rfl
    have he := ha (.wctNode (wWithNonce m k))
    rw [hx] at he
    unfold WCT9.ftsNodeHashN
    rw [WCT9.eval_ftsHash, he, hproj]
  have hfail : ∀ k, wTrialFails labels m k ↔ WCT9.ftsZeroOk coord.val (2^(6-level)+c)
      (Extract.Paired.proj (.wctNode index.val coord.val level c) (labels (.wctNode (wWithNonce m k)))) = false := by
    intro k
    unfold wTrialFails
    simp only [Node.toPos, hmi, hmc, hml, hmx]
    rw [if_neg (show level≠5 by omega),Extract.Paired.ftsZeroOk_level coord.val level c (by omega) hc]
  rw [Extract.Paired.ftsNodeAt_groundG hgr]
  have hs := wSelNonce_lt labels m
  have hspec := wSelNonce_spec labels m
  have hres := Extract.Paired.eval_ftsNonceSearch_eq answers coord.val index.val (2^(6-level)+c)
    (ftsLabel labels index coord level (2*c)) (ftsLabel labels index coord level (2*c+1))
    (fun k => evalWithAnswerFn answers (WCT9.ftsNodeHashN coord.val index.val (2^(6-level)+c) k
      (ftsLabel labels index coord level (2*c)) (ftsLabel labels index coord level (2*c+1)))) (fun _ => rfl)
    (WCT9.ftsNonceCap coord.val (2^(6-level)+c) - 1) 0 (wSelNonce labels m) (Nat.zero_le _) (by omega)
    (fun k _ hk => by rw [htrial k (by omega)]; exact (hfail k).mp (hspec.1 k hk))
    (by
      rcases hspec.2 with h' | h'
      · left
        rw [htrial _ le_rfl]
        have := mt (hfail _).mpr h'
        simpa using this
      · right; omega)
  rw [hres, htrial _ le_rfl]
  rfl


#print axioms inner_step
end OuterCanonBase.Paired
