import SigGolfCandidate.Research.V7Composed198Gate
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.PairRows
import SigGolfCandidate.ClaudeWCT.WCT9.Cost
import SigGolfCandidate.ClaudeWCT.WCT9.Omit

section
namespace ClaudeWCT.W9.T3.FullCacheExpansionCost
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query)
open SigGolfCandidate.T3.FullCacheExpansionCost (foldlM_cost_ge privatePair_cost)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem shortHash_cost (answers : SigGolfCandidate.T3.Correctness.Answers) (x : HashInput) :
    cost answers (shortHash x) = (pad64 x).length / 64 := by
  unfold shortHash
  rw [cost_bind, cost_pure, Nat.add_zero]
  unfold publicHash
  rw [cost_query]
  rfl
theorem projHash_cost (answers : SigGolfCandidate.T3.Correctness.Answers) (high : Bool) (x : HashInput) :
    cost answers (projHash high x) = (pad64 x).length / 64 := by
  unfold projHash
  rw [cost_bind, cost_pure, Nat.add_zero]
  unfold publicHash
  rw [cost_query]
  rfl
theorem pad64_length_ge (x : HashInput) (hx : 0 < x.length) : 64 ≤ (pad64 x).length := by
  simp only [pad64, List.length_append, List.length_replicate]
  omega
theorem leafHash_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (ends : List Digest) : 1 ≤ cost answers (ClaudeWCT.WCT9.leafHash index coord selected ends) := by
  unfold ClaudeWCT.WCT9.leafHash
  rw [shortHash_cost]
  refine le_trans (by norm_num) (Nat.div_le_div_right (c := 64) (pad64_length_ge _ ?_))
  simp only [List.length_append, SphincsSecurity.bytesLE_length]
  omega
theorem leafHashP_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (pad : Digest) (ends : List Digest) : 1 ≤ cost answers (ClaudeWCT.WCT9.leafHashP index coord selected pad ends) := by
  unfold ClaudeWCT.WCT9.leafHashP ClaudeWCT.WCT9.leafInputP
  rw [shortHash_cost]
  refine le_trans (by norm_num) (Nat.div_le_div_right (c := 64) (pad64_length_ge _ ?_))
  simp only [List.length_append, SphincsSecurity.bytesLE_length]
  omega
/-- C1: an FTS hash (either half) costs one compression per 64-byte block, like `shortHash`. -/
theorem ftsHash_cost (answers : SigGolfCandidate.T3.Correctness.Answers) (heap : Nat) (x : HashInput) :
    cost answers (ClaudeWCT.WCT9.ftsHash heap x) = (pad64 x).length / 64 := by
  rw [ClaudeWCT.WCT9.ftsHash_eq]
  split
  · unfold ClaudeWCT.WCT9.highHash
    rw [cost_bind, cost_pure, Nat.add_zero]
    unfold publicHash
    rw [cost_query]
    rfl
  · exact shortHash_cost answers x
/-- C1: the paired leaf of heap `heap` (either half) costs at least one compression. -/
theorem leafHashH_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (heap index coord selected : Nat)
    (pad : Digest) (ends : List Digest) :
    1 ≤ cost answers (ClaudeWCT.WCT9.leafHashH heap index coord selected pad ends) := by
  unfold ClaudeWCT.WCT9.leafHashH ClaudeWCT.WCT9.leafInputP
  rw [ftsHash_cost]
  refine le_trans (by norm_num) (Nat.div_le_div_right (c := 64) (pad64_length_ge _ ?_))
  simp only [List.length_append, SphincsSecurity.bytesLE_length]
  omega
theorem chain_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected i start count : Nat)
    (value : Digest) : count ≤ cost answers (ClaudeWCT.WCT9.chain index coord selected i start count value) := by
  unfold ClaudeWCT.WCT9.chain
  refine le_trans (by simp) (foldlM_cost_ge answers _ 1 (fun state step => ?_) (List.range' start count) value)
  rw [shortHash_cost]
  have hpos : 0 < (ClaudeWCT.WCT9.chainInput index coord selected i step state).length := by
    simp only [ClaudeWCT.WCT9.chainInput, List.length_append, SphincsSecurity.bytesLE_length]
    omega
  have := pad64_length_ge _ hpos
  omega
theorem buildChildF_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (word : ClaudeWCT.WCT9.Rank) (coefs : List Digest) (padL : Digest) :
    25 ≤ cost answers (ClaudeWCT.WCT9.buildChildF index coord selected word coefs padL) := by
  unfold ClaudeWCT.WCT9.buildChildF
  rw [cost_bind, cost_bind, cost_pure, Nat.add_zero]
  refine le_trans (by norm_num) (Nat.add_le_add (foldlM_cost_ge answers _ 4 (fun state i => ?_) (List.finRange 6) _)
    (leafHashP_cost_ge answers index coord selected padL _))
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact le_trans (by omega) (Nat.add_le_add (chain_cost_ge answers _ _ _ _ _ _ _) (chain_cost_ge answers _ _ _ _ _ _ _))
theorem buildChildH_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (heap index coord selected : Nat)
    (word : ClaudeWCT.WCT9.Rank) (coefs : List Digest) (padL : Digest) :
    25 ≤ cost answers (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs padL) := by
  unfold ClaudeWCT.WCT9.buildChildH
  rw [cost_bind, cost_bind, cost_pure, Nat.add_zero]
  refine le_trans (by norm_num) (Nat.add_le_add (foldlM_cost_ge answers _ 4 (fun state i => ?_) (List.finRange 6) _)
    (leafHashH_cost_ge answers heap index coord selected padL _))
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact le_trans (by omega) (Nat.add_le_add (chain_cost_ge answers _ _ _ _ _ _ _) (chain_cost_ge answers _ _ _ _ _ _ _))
theorem buildCoordinateF_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (coord : ClaudeWCT.WCT9.Coord) (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank)
    (prev : Digest × Digest) :
    3200 ≤ cost answers (ClaudeWCT.WCT9.buildCoordinateF index coord selected word prev) := by
  unfold ClaudeWCT.WCT9.buildCoordinateF
  rw [cost_bind, cost_bind]
  refine le_trans ?_ (Nat.le_add_left _ _)
  refine le_trans ?_ (Nat.le_add_right _ _)
  refine le_trans (by simp) (foldlM_cost_ge answers _ 25 (fun state j => ?_) (List.range 128) _)
  rw [cost_bind]
  exact le_trans (buildChildF_cost_ge answers index coord.val j word _ _) (Nat.le_add_right _ _)
theorem forestRows_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    28800 ≤ cost answers (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows
  apply (show 28800 = (List.finRange 9).length * 3200 by decide).le.trans
  apply foldlM_cost_ge
  intro state coord
  unfold ClaudeWCT.WCT9.openingStep
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact buildCoordinateF_cost_ge answers index coord _ _ _
theorem signForest_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    28800 ≤ cost answers (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest
  rw [cost_bind]
  exact (forestRows_cost_ge answers index output).trans (Nat.le_add_right _ _)
theorem signPayload_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (cache : Cache)
    (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) = some sig) :
    28800 ≤ cost answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs
  rw [cost_bind]
  cases hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [cost_bind, hd]
      have h := signForest_cost_ge answers (ClaudeWCT.WCT9.digestIndex output) output
      omega
end ClaudeWCT.W9.T3.FullCacheExpansionCost
end
section
namespace ClaudeWCT.W9.T3.ExpansionBudget
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit assembledSignature honestTop
  signForest_root assembled_forest_recovery toT3Signature)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query cost_bound)
open SigGolfCandidate.T3.Correctness (Answers cacheRegion maskedTop PiecesAgree CacheTagCorrect
  keygen_correct keygen_cache_tag privateMac_count)
open SigGolfCandidate.T3.Cost (CBound GoodQuery Bound ValidDigits recoverLayerCost recoveryLayersCost
  leafHashCost bound_chain bound_leafHash bound_nodeHash bound_recoverLayer sum_finRange remaining_steps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bound_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length = chainCount lay) (hsum : digits.sum = target lay) :
    CBound (fun _ => True) (recoverLayerCost lay) (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun i => maxDigit lay i.val - digits.getD i.val 0) (fun i _ => ClaudeWCT.WCT9.Cost.bound_chainW _ _ _ _ _ _ _)).bind'
    (l := leafHashCost lay + height lay) (fun ends hends => ?_) ?_
  · refine (ClaudeWCT.WCT9.Cost.bound_lowerLeafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind
        (fun top _ => .pure _ 0 trivial)).mono_k (by simp)
    exact ClaudeWCT.WCT9.Cost.bound_lowerNodeHash _ _ _ _ _
  · rw [sum_finRange (chainCount lay) (fun i => maxDigit lay i - digits.getD i 0),
      remaining_steps lay digits hd hlen hsum]
    simp only [recoverLayerCost]
    omega
theorem expandLayersBC_cost_le (answers : Answers) (cache : Cache) (index : Nat)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg pieces,
      evalWithAnswerFn answers (ClaudeWCT.WCT9.signLayersBC cache index n msg) = some pieces →
      ∀ sig : Signature, PiecesAgree (toT3Signature sig) pieces n →
        cost answers (ClaudeWCT.WCT9.expandLayersBC sig index n msg) ≤
          cost answers (ClaudeWCT.WCT9.signLayersBC cache index n msg) + recoveryLayersCost n := by
  intro n
  induction n with
  | zero =>
      intro _ msg pieces _ sig _
      simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_pure, recoveryLayersCost]
      omega
  | succ n ih =>
      intro hn msg pieces he sig hagree
      have hsource := he
      simp only [ClaudeWCT.WCT9.signLayersBC, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0 (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n))) with
      | none =>
          by_cases hn0 : n = 0
          · subst n
            simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_bind, hs, cost_pure,
              if_true]
            omega
          · simp only [hs, hn0, if_false, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (ClaudeWCT.WCT9.layerCounterSearch_some answers (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
            (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n)) 0 counter digits
            (by have := ClaudeWCT.WCT9.searchLimit_le (Fin.ofNat 4 n); unfold counterLimit at this; omega) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hls := decode_length_sum hd
          simp only [hs] at he
          by_cases hn0 : n = 0
          · subst n
            have hrec := cost_bound answers (bound_recoverLayer (toT3Signature sig) index (Fin.ofNat 4 0)
              digits hvalid hls.1 hls.2)
            simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_bind, hs, if_true,
              cost_pure, recoveryLayersCost, cost_bind, Nat.add_zero, Option.map_some, Option.getD_some]
            omega
          · have hrec := cost_bound answers (bound_recoverLayerPair sig index (Fin.ofNat 4 n)
              digits hvalid hls.1 hls.2)
            have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := by
              intro h
              have hv := congrArg Fin.val h
              simp only [Fin.val_ofNat, Fin.val_zero] at hv
              omega
            simp only [hn0, if_false, evalWithAnswerFn_bind,
              ClaudeWCT.WCT9.eval_buildTreeP_result answers hlay _ _ digits hvalid (route_leaf_bound index _),
              ClaudeWCT.WCT9.topPair_take, ClaudeWCT.WCT9.map_range_take_path] at he
            cases hp : evalWithAnswerFn answers (ClaudeWCT.WCT9.signLayersBC cache index n
              (.pair (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                (ClaudeWCT.WCT9.wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).1
                (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                  (ClaudeWCT.WCT9.wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).2)) with
            | none => simp only [hp, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                simp only [hp, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst pieces
                have hlen := ClaudeWCT.WCT9.signLayersBC_length answers cache index n _ previous hp
                change PiecesAgree (toT3Signature sig) (previous ++ [ClaudeWCT.WCT9.wotsPieces answers (Fin.ofNat 4 n)
                  (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits]) (n + 1) at hagree
                have hlayer := PiecesAgree.last hlen (by omega) hagree
                have hrecover : evalWithAnswerFn answers
                    (ClaudeWCT.WCT9.recoverLayerPair sig index (Fin.ofNat 4 n) digits) =
                    ClaudeWCT.WCT9.builtPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
                  apply ClaudeWCT.WCT9.eval_recoverLayerPair_honest answers sig index (Fin.ofNat 4 n) digits hvalid
                  · intro i
                    change ((toT3Signature sig).layers (Fin.ofNat 4 n)).values i = _
                    rw [hlayer]
                    simp [piecesSignature, ClaudeWCT.WCT9.wotsPieces, SigGolfCandidate.T3.Correctness.treeValue]
                  · intro j
                    change ((toT3Signature sig).layers (Fin.ofNat 4 n)).path j = _
                    rw [hlayer]
                    simp [piecesSignature, ClaudeWCT.WCT9.wotsPieces, SigGolfCandidate.T3.Correctness.treeValue]
                have hprevious := ih (by omega) _ previous hp sig (PiecesAgree.prefix hlen hagree)
                unfold ClaudeWCT.WCT9.builtPair at hrecover
                simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_bind, hs, hn0,
                  if_false, hrecover, hp, ClaudeWCT.WCT9.eval_buildTreeP_result answers hlay _ _ digits hvalid
                    (route_leaf_bound index _), ClaudeWCT.WCT9.topPair_take, recoveryLayersCost]
                cases hx : evalWithAnswerFn answers (ClaudeWCT.WCT9.expandLayersBC sig index n
                    (.pair (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                      (ClaudeWCT.WCT9.wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).1
                      (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                        (ClaudeWCT.WCT9.wotsTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).2)) <;>
                  simp only [cost_pure, Nat.add_zero] <;> omega
theorem expand_cost_step (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) = some (counter, output)) :
    cost answers (ClaudeWCT.WCT9.expandWith digestAttemptLimit message pk sig) =
      cost answers (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output) +
      cost answers (ClaudeWCT.WCT9.expandLayersBC sig (ClaudeWCT.WCT9.digestIndex output) 4
        (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) := by
  simp only [ClaudeWCT.WCT9.expandWith, cost_bind, hd]
  split
  · split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
  · simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem signPayload_cost_step (answers : Answers) (cache : Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) = some (counter, output)) :
    cost answers (signPayload cache message) =
      cost answers (privateNonce message) +
      cost answers (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output) +
      cost answers (ClaudeWCT.WCT9.signLayersBC cache (ClaudeWCT.WCT9.digestIndex output) 4
        (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).2.1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).2.2)) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [cost_bind, hd]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem expandWith_cost_le_payload_add_of (ftsRec : Nat)
    (hrecFts : ∀ sig index output, ∃ post,
      CBound post ftsRec (ClaudeWCT.WCT9.recoverFts sig index output))
    (hbudget : ftsRec + recoveryLayersCost 4 ≤ 622)
    (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (ClaudeWCT.WCT9.expandWith digestAttemptLimit message pk sig) ≤
      cost answers (signPayload cache message) + 622 := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers
    (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
      digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers
        (ClaudeWCT.WCT9.signLayersBC cache (ClaudeWCT.WCT9.digestIndex output) 4
          (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).2.1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).2.2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some pieces =>
          simp only [hl, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          have hforest := assembled_forest_recovery answers
            (evalWithAnswerFn answers (privateNonce message)) (ClaudeWCT.WCT9.digestIndex output) output pieces
          have hindex : ClaudeWCT.WCT9.digestIndex output < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt output
          have hlayer := expandLayersBC_cost_le answers cache (ClaudeWCT.WCT9.digestIndex output)
            hcache hindex 4 (by decide) _ pieces hl
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).1 pieces)
            (fun _ _ => rfl)
          obtain ⟨post, hrecBound⟩ := hrecFts
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).1
              pieces)
            (ClaudeWCT.WCT9.digestIndex output) output
          have hrec := cost_bound answers hrecBound
          have hexpand := expand_cost_step answers message pk
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (ClaudeWCT.WCT9.digestIndex output) output)).1
              pieces)
            counter output (by simpa only [ClaudeWCT.WCT9.assembledSignature_rho] using hd)
          rw [hexpand, signPayload_cost_step answers cache message counter output hd]
          simp only [ClaudeWCT.WCT9.assembledSignature_rho] at hrec hlayer ⊢
          rw [hforest]
          omega
theorem cost_map' {α β : Type} (answers : Answers) (f : α → β) (x : M α) :
    cost answers (f <$> x) = cost answers x := by
  rw [map_eq_bind_pure_comp, cost_bind]
  simp
theorem cost_topNode (answers : Answers) (index : Nat) (v o : Digest) :
    cost answers (ClaudeWCT.WCT9.topNode index v o) = 1 := by
  apply le_antisymm (cost_bound answers (ClaudeWCT.WCT9.Cost.bound_topNode index v o))
  unfold ClaudeWCT.WCT9.topNode nodeHash
  rw [ClaudeWCT.W9.T3.FullCacheExpansionCost.projHash_cost]
  refine le_trans (by norm_num) (Nat.div_le_div_right (c := 64)
    (ClaudeWCT.W9.T3.FullCacheExpansionCost.pad64_length_ge _ ?_))
  simp only [List.length_append, SphincsSecurity.bytesLE_length, zero16, List.length_replicate]
  omega
theorem cost_expandLayersT_other (answers : Answers) (s : Signature) (index : Nat) (o o' : Digest) :
    ∀ n msg, cost answers (ClaudeWCT.WCT9.expandLayersT s index o n msg) =
      cost answers (ClaudeWCT.WCT9.expandLayersT s index o' n msg) := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
    intro msg
    simp only [ClaudeWCT.WCT9.expandLayersT, cost_bind]
    congr 1
    cases hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0
        (ClaudeWCT.WCT9.searchLimit (Fin.ofNat 4 n))) with
    | none => rfl
    | some found =>
      obtain ⟨counter, digits⟩ := found
      by_cases hn : n = 0
      · subst hn
        simp only [if_true, cost_bind, cost_topNode, cost_pure]
      · simp only [hn, if_false, cost_bind]
        rw [ih]
        congr 1
        congr 1
        split <;> split <;> simp
theorem cost_bind_le {α β : Type} (answers : Answers) (x : M α) (f : α → M β) (k : Nat)
    (h : cost answers (f (evalWithAnswerFn answers x)) ≤ k) : cost answers (x >>= f) ≤ cost answers x + k := by
  rw [cost_bind]; omega
theorem expandS_cost_le (answers : Answers) (message : Message) (pk : Digest) (sig : Signature) :
    cost answers (ClaudeWCT.WCT9.expandS digestAttemptLimit message pk sig) ≤
      cost answers (ClaudeWCT.WCT9.expandWith digestAttemptLimit message pk sig) + ClaudeWCT.WCT9.searchFuel := by
  have hrho : (ClaudeWCT.WCT9.proj sig).rho = sig.rho := rfl
  have hfts : ClaudeWCT.WCT9.recoverFts (ClaudeWCT.WCT9.proj sig) = ClaudeWCT.WCT9.recoverFts sig := rfl
  cases hd : evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) with
  | none =>
    unfold ClaudeWCT.WCT9.expandS ClaudeWCT.WCT9.expandWith
    simp only [cost_bind, hrho, hd, cost_pure]
    omega
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [expand_cost_step answers message pk sig counter output hd]
    have hC : cost answers (ClaudeWCT.WCT9.expandLayersBC sig (ClaudeWCT.WCT9.digestIndex output) 4
        (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) =
        cost answers (ClaudeWCT.WCT9.expandLayersT (ClaudeWCT.WCT9.proj sig) (ClaudeWCT.WCT9.digestIndex output)
          (ClaudeWCT.WCT9.topSib (ClaudeWCT.WCT9.proj sig)) 4
          (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) := by
      rw [ClaudeWCT.WCT9.expandLayersBC_eq_T sig _ 4 le_rfl, cost_map',
        cost_expandLayersT_other answers _ _ (ClaudeWCT.WCT9.topSib sig) (ClaudeWCT.WCT9.topSib (ClaudeWCT.WCT9.proj sig))]
    unfold ClaudeWCT.WCT9.expandS
    simp only [hrho]
    refine le_trans (cost_bind_le answers _ _ (cost answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output) +
      cost answers (ClaudeWCT.WCT9.expandLayersT (ClaudeWCT.WCT9.proj sig) (ClaudeWCT.WCT9.digestIndex output)
          (ClaudeWCT.WCT9.topSib (ClaudeWCT.WCT9.proj sig)) 4
          (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) +
      ClaudeWCT.WCT9.searchFuel) ?_) (by omega)
    simp only [hd, hfts]
    refine le_trans (cost_bind_le answers _ _ (
      cost answers (ClaudeWCT.WCT9.expandLayersT (ClaudeWCT.WCT9.proj sig) (ClaudeWCT.WCT9.digestIndex output)
          (ClaudeWCT.WCT9.topSib (ClaudeWCT.WCT9.proj sig)) 4
          (.pair (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).1 (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (ClaudeWCT.WCT9.digestIndex output) output)).2)) +
      ClaudeWCT.WCT9.searchFuel) ?_) (by omega)
    refine le_trans (cost_bind_le answers _ _ ClaudeWCT.WCT9.searchFuel ?_) (by omega)
    try dsimp only
    split
    · split
      · simp
      · refine le_trans (cost_bind_le answers _ _ 0 ?_) ?_
        · try dsimp only
          split <;> simp
        · rw [Nat.add_zero]
          exact cost_bound answers (ClaudeWCT.WCT9.Cost.bound_searchTop _ _ _ _ _ _)
    · simp
theorem expand_cost_le_expandWith (answers : Answers) (message : Message) (pk : Digest) (sig : Signature) :
    cost answers (expand message pk sig) ≤
      cost answers (ClaudeWCT.WCT9.expandWith digestAttemptLimit message pk sig) + ClaudeWCT.WCT9.searchFuel := by
  unfold ClaudeWCT.WCT9.Rev3.expand
  rw [cost_map']
  exact expandS_cost_le answers message pk sig
theorem expand_cost_le_payload_add_of (ftsRec : Nat)
    (hrecFts : ∀ sig index output, ∃ post,
      CBound post ftsRec (ClaudeWCT.WCT9.recoverFts sig index output))
    (hbudget : ftsRec + recoveryLayersCost 4 ≤ 622)
    (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + 622 + ClaudeWCT.WCT9.searchFuel :=
  (expand_cost_le_expandWith answers message pk sig).trans
    (Nat.add_le_add_right
      (expandWith_cost_le_payload_add_of ftsRec hrecFts hbudget answers cache message sig hcache he pk) _)
theorem sign_cost_ge_mac (answers : Answers) (cache : Cache) (message : Message) :
    2 ≤ cost answers (sign cache message) := by
  have hmac : cost answers (privateMac cache.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac]
  omega
theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers keygen).2 message) =
      2 + cost answers (signPayload (evalWithAnswerFn answers keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers keygen).2.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac, ← hvalid, ne_eq,
    not_true_eq_false, ite_false]
  rfl
theorem expand_cost_le_eight_sign_of (ftsRec : Nat)
    (hrecFts : ∀ sig index output, ∃ post,
      CBound post ftsRec (ClaudeWCT.WCT9.recoverFts sig index output))
    (hbudget : ftsRec + recoveryLayersCost 4 ≤ 622)
    (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers keygen).1 sig) ≤
      8 * cost answers (sign (evalWithAnswerFn answers keygen).2 message) := by
  have hk := keygen_correct answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers keygen).2 message) =
      some sig := by
    rw [show sign (evalWithAnswerFn answers keygen).2 message =
      ClaudeWCT.WCT9.signWith digestAttemptLimit (evalWithAnswerFn answers keygen).2 message from rfl,
      ClaudeWCT.WCT9.signWith_valid_cache digestAttemptLimit answers _ message
        (keygen_cache_tag answers)] at hs
    exact hs
  have h := expand_cost_le_payload_add_of ftsRec hrecFts hbudget answers (evalWithAnswerFn answers keygen).2
    message sig hk.2.1 hs' (evalWithAnswerFn answers keygen).1
  have hmin := ClaudeWCT.W9.T3.FullCacheExpansionCost.signPayload_cost_ge answers
    (evalWithAnswerFn answers keygen).2 message sig hs'
  rw [sign_cost_honest]
  unfold ClaudeWCT.WCT9.searchFuel at h
  omega
theorem recoverFts_budget : 140 + recoveryLayersCost 4 ≤ 622 := by
  have h := SigGolfCandidate.T3.Cost.recoveryLayersCost_four
  omega
theorem expand_cost_le_payload_add (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + 622 + ClaudeWCT.WCT9.searchFuel :=
  expand_cost_le_payload_add_of 140
    (fun sig index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_recoverFts sig index output⟩) recoverFts_budget
    answers cache message sig hcache he pk
theorem expand_cost_le_eight_sign (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers keygen).1 sig) ≤
      8 * cost answers (sign (evalWithAnswerFn answers keygen).2 message) :=
  expand_cost_le_eight_sign_of 140
    (fun sig index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_recoverFts sig index output⟩) recoverFts_budget
    answers message sig hs
end ClaudeWCT.W9.T3.ExpansionBudget
end

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
open SigGolfCandidate.T3.FullCacheExpansionCost (foldlM_cost_ge)
open ClaudeWCT.W9.T3.FullCacheExpansionCost (buildChildF_cost_ge buildChildH_cost_ge)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem buildSharedCoordinate_cost_ge (answers : Answers) (first : Bool) (index coord : Nat)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    3200 ≤ cost answers (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  rw [cost_bind, cost_bind]
  refine le_trans ?_ (Nat.le_add_left _ _)
  refine le_trans ?_ (Nat.le_add_right _ _)
  refine le_trans (by simp) (foldlM_cost_ge answers _ 25 (fun state j => ?_) (List.range 128) _)
  rw [cost_bind]
  exact le_trans (buildChildH_cost_ge answers (128 + j) index coord (rawChild first j) word _ _) (Nat.le_add_right _ _)

theorem buildPair_cost_ge (answers : Answers) (index pair : Nat) (selected : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    6400 ≤ cost answers (buildPair index pair selected aWord bWord prev) := by
  unfold buildPair
  simp only [cost_bind, cost_pure, Nat.add_zero]
  have h0 := buildSharedCoordinate_cost_ge answers true index (2*pair) (firstChild selected) aWord (fun _ => prev)
  have h1 := buildSharedCoordinate_cost_ge answers false index (2*pair+1) (secondChild selected) bWord
    (nodesPair (evalWithAnswerFn answers
      (buildSharedCoordinate true index (2*pair) (firstChild selected) aWord (fun _ => prev))).1)
  omega

theorem buildSingleton_cost_ge (answers : Answers) (index : Nat) (selected : Child)
    (word : Rank) (prev : PairRoot) :
    3200 ≤ cost answers (buildSingleton index selected word prev) := by
  unfold buildSingleton
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact buildSharedCoordinate_cost_ge answers false index 8 selected word (fun _ => prev)

theorem buildForest_cost_ge (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    28800 ≤ cost answers (buildForest index selected words) := by
  unfold buildForest
  rw [cost_bind]
  have h0 := foldlM_cost_ge answers
    (fun (state : List PairOpening × PairRoot) (pair : Fin 4) => do
      let built ← buildPair index pair.val (selected.pairs pair)
        (words.first pair) (words.second pair) state.2
      pure (state.1 ++ [built.1], built.2))
    6400 (fun state pair => ?_) (List.finRange 4) ([], ftsStart)
  have h1 := buildSingleton_cost_ge answers index selected.singleton words.singleton
    (evalWithAnswerFn answers ((List.finRange 4).foldlM
      (fun (state : List PairOpening × PairRoot) pair => do
        let built ← buildPair index pair.val (selected.pairs pair)
          (words.first pair) (words.second pair) state.2
        pure (state.1 ++ [built.1], built.2)) ([], ftsStart))).2
  · simp only [List.length_finRange] at h0
    simp only [cost_bind, cost_pure, Nat.add_zero]
    omega
  · simp only [cost_bind, cost_pure, Nat.add_zero]
    exact buildPair_cost_ge answers index pair.val (selected.pairs pair) (words.first pair) (words.second pair) state.2

#print axioms buildForest_cost_ge
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
open ClaudeWCT.W9.T3.ExpansionBudget (cost_bind_le cost_topNode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem cost_recoverHintedLayers_other (answers : Answers) (sig : Signature)
    (index : Nat) (other other' : Digest) :
    ∀ n msg, cost answers (recoverHintedLayers sig index other n msg) =
      cost answers (recoverHintedLayers sig index other' n msg) := by
  intro n
  induction n with
  | zero => intro msg; rfl
  | succ n ih =>
    intro msg
    simp only [recoverHintedLayers, cost_bind]
    congr 1
    cases hs : evalWithAnswerFn answers (CanonicalPolicy.layerCounterSearchAt (Fin.ofNat 4 n)
      (hintFloor sig.policyHints (Fin.ofNat 4 n)) (route index (Fin.ofNat 4 n)).2
      (route index (Fin.ofNat 4 n)).1 msg 0 (searchLimit (Fin.ofNat 4 n))) with
    | none => rfl
    | some found =>
      obtain ⟨counter, digits⟩ := found
      by_cases hn : n = 0
      · subst hn
        simp only [if_true, cost_bind, cost_topNode, cost_pure]
      · simp only [hn, if_false, cost_bind]
        rw [ih]
        congr 1
        congr 1
        split <;> split <;> simp

theorem expand_cost_le_recovery (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) =
      some (counter, output)) :
    cost answers (expand message pk sig) ≤
      cost answers (sharedDigestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (recoverForest (digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) sig.forest) +
      cost answers (recoverHintedLayers sig (digestIndex output) ((sig.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (digestIndex output)
            (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) + searchFuel := by
  unfold expand
  split
  · simp only [cost_pure]; omega
  · simp only [cost_bind, nonce_retained, hd,
      show (fillTopSignature sig 0).forest = sig.forest from rfl]
    rw [recoverHintedLayers_fill _ _ _ _ _ le_rfl,
      cost_recoverHintedLayers_other answers sig (digestIndex output)
        (((fillTopSignature sig 0).layers 0).path topJ) ((sig.layers 0).path topJ)]
    simp only [Nat.add_assoc]
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    apply Nat.add_le_add_left
    split
    · split
      · simp only [cost_pure]; exact Nat.zero_le _
      · split
        · simp only [cost_pure]; exact Nat.zero_le _
        · refine le_trans (cost_bind_le answers _ _ 0 ?_) ?_
          · split <;> simp only [cost_pure, le_refl]
          · rw [Nat.add_zero]
            exact cost_bound answers (ClaudeWCT.WCT9.Cost.bound_searchTop ..)
    · simp only [cost_pure]; exact Nat.zero_le _

#print axioms cost_recoverHintedLayers_other
#print axioms expand_cost_le_recovery
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_cost (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    cost answers (signFromOutput cache rho counter output) =
      cost answers (buildForest (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output)) +
      cost answers (prepareRoots (digestIndex output)) +
      cost answers (searchPreparedLayers cache (digestIndex output)
        (evalWithAnswerFn answers (prepareRoots (digestIndex output)))
        (evalWithAnswerFn answers (buildForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output))).2) := by
  simp only [signFromOutput, cost_bind]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]

theorem signFromOutput_cost_ge (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    28800 ≤ cost answers (signFromOutput cache rho counter output) := by
  rw [signFromOutput_cost]
  have h := buildForest_cost_ge answers (digestIndex output) (forestSelectionFromOutput output) (forestWordsFromOutput output)
  omega

theorem signFromOutput_recovery_cost_le (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    cost answers (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
        (evalWithAnswerFn answers (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)) ≤
      cost answers (signFromOutput cache rho counter output) + 1616 := by
  let index := digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output) (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    have hf := searchPreparedLayers_some answers cache index prepared built.2 layers hs
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    let sig : Signature := ⟨rho, layers.policyHints, built.1,
      fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
    have hp : ∀ lay, lay ≠ 0 → evalWithAnswerFn answers
        (recoverLayerPair (mainSignature sig) index lay (layers.digits.getD lay.val [])) =
        builtPair answers lay (route index lay).2 := by
      intro lay _
      apply recoverLayerPair_wotsPieces answers sig index lay _ (hf.validDigits lay)
      change piecesSignature lay (layers.pieces.getD lay.val ([], [])) = _
      rw [hf.honest_pieces hcache (digestIndex_lt output)]
    have hm0 : topPair 1 prepared.one.levels = builtPair answers 1 (route index 1).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 1
    have hm1 : topPair 2 prepared.two.levels = builtPair answers 2 (route index 2).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 2
    have hm2 : topPair 3 prepared.three.levels = builtPair answers 3 (route index 3).2 := by
      dsimp only [prepared]; rw [prepareRoots_result]; exact fixedPrepared_pair answers index 3
    have hc := hf.recovery_cost_le sig ((sig.layers 0).path topJ) rfl hm0 hm1 hm2 hp
    have hforest : evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
      (forestWordsFromOutput output) built.1) = built.2 := recoverForest_honest answers index _ _
    change cost answers (recoverHintedLayers sig index ((sig.layers 0).path topJ) 4
      (.pair (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
        (forestWordsFromOutput output) built.1)).1
        (evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
          (forestWordsFromOutput output) built.1)).2)) ≤ _
    rw [hforest, signFromOutput_cost]
    dsimp only [index, prepared, built] at hc ⊢
    omega

theorem signPayload_cost_step (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message))
      message 0 digestAttemptLimit) = some (counter, output)) :
    cost answers (signPayload cache message) = cost answers (privateNonce message) +
      cost answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) +
      cost answers (signFromOutput cache (evalWithAnswerFn answers (privateNonce message)) counter output) := by
  simp only [signPayload, cost_bind, hd]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]

theorem expand_cost_le_payload_add (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (sig : Signature)
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + 1900 + searchFuel := by
  unfold signPayload at he
  simp only [evalWithAnswerFn_bind] at he
  let rho := evalWithAnswerFn answers (privateNonce message)
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
    obtain ⟨counter, output⟩ := found
    dsimp only [rho] at hd
    simp only [hd, evalWithAnswerFn_bind] at he
    cases hs : evalWithAnswerFn answers (signFromOutput cache rho counter output) with
    | none =>
      dsimp only [rho] at hs
      simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some original =>
      have hr := signFromOutput_recovery_cost_le answers cache hcache rho counter output original hs
      have hh := signFromOutput_recovery answers cache hcache rho counter output original hs
      dsimp only [rho] at hs
      simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
      subst sig
      have hd' : evalWithAnswerFn answers (sharedDigestSearch original.signature.rho message 0 digestAttemptLimit) =
          some (counter, output) := by rw [hh.1]; exact hd
      have hx := expand_cost_le_recovery answers message pk original.signature counter output hd'
      have hf := cost_bound answers (bound_recoverForest (digestIndex output)
        (forestSelectionFromOutput output) (forestWordsFromOutput output) original.signature.forest)
      rw [hh.1] at hx
      rw [signPayload_cost_step answers cache message counter output hd]
      dsimp only [rho] at hx hr
      omega

#print axioms signFromOutput_recovery_cost_le
#print axioms expand_cost_le_payload_add
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signPayload_cost_ge (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    28800 ≤ cost answers (signPayload cache message) := by
  unfold signPayload at hs
  simp only [evalWithAnswerFn_bind] at hs
  cases hd : evalWithAnswerFn answers (sharedDigestSearch
    (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
    obtain ⟨counter, output⟩ := found
    rw [signPayload_cost_step answers cache message counter output hd]
    have h := signFromOutput_cost_ge answers cache
      (evalWithAnswerFn answers (privateNonce message)) counter output
    omega

theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) =
      2 + cost answers (signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [sign, cost_bind, hmac, ← hvalid, ne_eq, not_true_eq_false, ite_false]

theorem expand_cost_le_eight_sign (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1 sig) ≤
      8 * cost answers (sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) = some sig := by
    simp only [CacheTagCorrect] at hvalid
    simpa only [sign, evalWithAnswerFn_bind, ← hvalid, ne_eq, not_true_eq_false, ite_false] using hs
  have hk := SigGolfCandidate.T3.Correctness.keygen_correct answers
  have h := expand_cost_le_payload_add answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 hk.2.1
    message sig hs' (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).1
  have hmin := signPayload_cost_ge answers (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message sig hs'
  rw [sign_cost_honest]
  unfold searchFuel at h
  omega

#print axioms expand_cost_le_eight_sign
end SigGolfCandidate.Research.SharedForest
