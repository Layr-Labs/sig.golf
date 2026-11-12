import SigGolfCandidate.Merge058
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option debug.skipKernelTC false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace QueryChargeResearch
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Correctness

def calls {α : Type} (answers : Answers) (program : M α) : Nat :=
  (evalWithAnswerFn answers (countWith (fun _ => 1) program)).2

theorem counted_fst {α : Type} (answers : Answers) (program : M α) :
    (evalWithAnswerFn answers (countWith (fun _ => 1) program)).1 = evalWithAnswerFn answers program := by
  have h := congrArg (evalWithAnswerFn answers) (fst_countWith (fun _ => 1) program)
  simpa only [evalWithAnswerFn_map] using h

@[simp] theorem calls_pure {α : Type} (answers : Answers) (v : α) :
    calls answers (pure v : M α) = 0 := rfl

theorem calls_bind {α β : Type} (answers : Answers) (first : M α) (next : α → M β) :
    calls answers (first >>= next) = calls answers first + calls answers (next (evalWithAnswerFn answers first)) := by
  unfold calls
  rw [countWith_bind, evalWithAnswerFn_bind, evalWithAnswerFn_map]
  rw [show (evalWithAnswerFn answers (countWith (fun _ => 1) first)).1 = evalWithAnswerFn answers first from counted_fst answers first]

@[simp] theorem calls_query (answers : Answers) (q : Cost.Query) :
    calls answers (SigGolfCandidate.T3.Spec.query q) = 1 := by
  unfold calls
  rw [countWith_query, evalWithAnswerFn_map]

theorem foldlM_calls_ge {α β : Type} (answers : Answers) (f : β → α → M β) (k : Nat)
    (h : ∀ state value, k ≤ calls answers (f state value)) (values : List α) (init : β) :
    values.length*k ≤ calls answers (values.foldlM f init) := by
  induction values generalizing init with
  | nil => simp only [List.foldlM_nil, calls_pure, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons value values ih =>
      rw [List.foldlM_cons, calls_bind, List.length_cons, Nat.add_mul, Nat.one_mul]
      simpa only [Nat.add_comm] using Nat.add_le_add (h init value) (ih (evalWithAnswerFn answers (f init value)))

open ClaudeWCT.WCT9

theorem halfHash_calls (answers : Answers) (high : Bool) (input : HashInput) :
    calls answers (halfHash high input) = 1 := by
  cases high with
  | false =>
    change calls answers (SigGolfCandidate.T3.Spec.query (.inl (.inr (pad64 input))) >>= fun a => pure (a.extractLsb' 0 128)) = 1
    rw [calls_bind, calls_query, calls_pure]
  | true =>
    change calls answers (SigGolfCandidate.T3.Spec.query (.inl (.inr (pad64 input))) >>= fun a => pure (a.extractLsb' 128 128)) = 1
    rw [calls_bind, calls_query, calls_pure]

theorem chainW_calls_ge (answers : Answers) (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    count ≤ calls answers (chainW lay tree leaf i start count value) := by
  unfold chainW
  have h := foldlM_calls_ge answers (fun value step => halfHash (chainHigh lay i step) (chainInputW lay tree leaf i step value))
    1 (fun _ _ => by rw [halfHash_calls]) (List.range' start count) value
  simpa only [List.length_range', Nat.mul_one] using h
#print axioms chainW_calls_ge

theorem mapM_calls_ge {α β : Type} (answers : Answers) (f : α → M β) (k : Nat)
    (h : ∀ value, k ≤ calls answers (f value)) (values : List α) :
    values.length*k ≤ calls answers (values.mapM f) := by
  induction values with
  | nil => simp
  | cons value values ih =>
    rw [List.mapM_cons, calls_bind]
    simp only [calls_bind, calls_pure, Nat.add_zero, List.length_cons, Nat.add_mul, Nat.one_mul]
    simpa only [Nat.add_comm] using Nat.add_le_add (h value) ih

namespace S
open SigGolfCandidate.Research.SharedForest

theorem chainPrefixes_calls_ge (answers : Answers) (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    count ≤ calls answers (chainPrefixes lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [chainPrefixes, calls_bind, halfHash_calls, calls_pure, Nat.add_zero]
    have h := ih (start+1) (evalWithAnswerFn answers (halfHash (chainHigh lay i start) (chainInputW lay tree leaf i start value)))
    omega

theorem buildLeafPrefixes_calls_ge (answers : Answers) (lay : Layer) (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : List Digest) :
    301 ≤ calls answers (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  rw [calls_bind]
  generalize hr : evalWithAnswerFn answers (lowerCoefs lay tree leaf carry) = pair
  obtain ⟨coefs, carry'⟩ := pair
  dsimp only
  rw [calls_bind]
  have hmap : 301 ≤ calls answers ((List.range (chainCount lay)).mapM fun i =>
      chainPrefixes lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed coefs lay leaf i)) := by
    have h := mapM_calls_ge answers (fun i => chainPrefixes lay tree leaf i 0 (maxDigit lay i)
        (lowerFamilySeed coefs lay leaf i)) 7
      (fun i => by simpa [maxDigit, hlay] using chainPrefixes_calls_ge answers lay tree leaf i 0 7 (lowerFamilySeed coefs lay leaf i))
      (List.range (chainCount lay))
    have hc : chainCount lay = 43 := by fin_cases lay <;> simp_all [chainCount]
    simpa [hc] using h
  omega

theorem buildLeafPF_calls_ge (answers : Answers) (lay : Layer) (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : List Digest) :
    301 ≤ calls answers (buildLeafPF lay tree leaf [] carry) := by
  unfold buildLeafPF
  rw [calls_bind]
  generalize hr : evalWithAnswerFn answers (lowerCoefs lay tree leaf carry) = pair
  obtain ⟨coefs, carry'⟩ := pair
  dsimp only
  rw [calls_bind]
  let f : (List Digest × List Digest) → Nat → M (List Digest × List Digest) := fun state i => do
    let value ← chainW lay tree leaf i 0 0 (lowerFamilySeed coefs lay leaf i)
    let last ← chainW lay tree leaf i 0 (maxDigit lay i) value
    pure (state.1 ++ [last], state.2 ++ [value])
  have hfold : 301 ≤ calls answers ((List.range (chainCount lay)).foldlM f ([], [])) := by
    have h := foldlM_calls_ge answers f 7 (fun state i => by
      dsimp [f]
      simp only [calls_bind, calls_pure, Nat.add_zero]
      have hm : maxDigit lay i = 7 := by simp [maxDigit, hlay]
      rw [hm]
      have hh := chainW_calls_ge answers lay tree leaf i 0 7
        (evalWithAnswerFn answers (chainW lay tree leaf i 0 0 (lowerFamilySeed coefs lay leaf i)))
      have hz : evalWithAnswerFn answers (chainW lay tree leaf i 0 0 (lowerFamilySeed coefs lay leaf i)) = lowerFamilySeed coefs lay leaf i := rfl
      rw [hz] at hh
      simp only [evalWithAnswerFn_pure]
      omega) (List.range (chainCount lay)) ([], [])
    have hc : chainCount lay = 43 := by fin_cases lay <;> simp_all [chainCount]
    simpa [hc] using h
  change 301 ≤ _ + (calls answers ((List.range (chainCount lay)).foldlM f ([], [])) + _)
  omega

#print axioms buildLeafPF_calls_ge

theorem buildTreePrefixes_calls_ge (answers : Answers) (lay : Layer) (hlay : lay ≠ 0)
    (tree selected : Nat) :
    2 ^ height lay * 301 ≤ calls answers (buildTreePrefixes lay tree selected) := by
  let f : (List Digest × List (List Digest) × List Digest) → Nat →
      M (List Digest × List (List Digest) × List Digest) := fun state leaf => do
    let ((root, prefixes), carry) ←
      if leaf = selected then buildLeafPrefixes lay tree leaf state.2.2
      else do
        let ((root, _), carry) ← buildLeafPF lay tree leaf [] state.2.2
        pure ((root, []), carry)
    pure (state.1 ++ [root], if leaf = selected then prefixes else state.2.1, carry)
  have hfold := foldlM_calls_ge answers f 301 (fun state leaf => by
    dsimp only [f]
    by_cases h : leaf = selected
    · simp only [if_pos h, calls_bind, calls_pure, Nat.add_zero]
      exact buildLeafPrefixes_calls_ge answers lay hlay tree leaf state.2.2
    · simp only [if_neg h, calls_bind, calls_pure, Nat.add_zero]
      exact buildLeafPF_calls_ge answers lay hlay tree leaf state.2.2)
    (List.range (2 ^ height lay)) ([], [], [])
  simp only [List.length_range] at hfold
  unfold buildTreePrefixes
  rw [calls_bind]
  change 2 ^ height lay * 301 ≤ calls answers ((List.range (2 ^ height lay)).foldlM f ([], [], [])) + _
  exact hfold.trans (Nat.le_add_right _ _)

theorem prepareRoots_calls_ge (answers : Answers) (index : Nat) :
    77056 ≤ calls answers (prepareRoots index) := by
  have h1 := buildTreePrefixes_calls_ge answers 1 (by decide) (route index 1).2 (route index 1).1
  have h2 := buildTreePrefixes_calls_ge answers 2 (by decide) (route index 2).2 (route index 2).1
  have h3 := buildTreePrefixes_calls_ge answers 3 (by decide) (route index 3).2 (route index 3).1
  change 38528 ≤ _ at h1
  change 19264 ≤ _ at h2 h3
  simp only [prepareRoots, calls_bind, calls_pure, Nat.add_zero]
  omega
#print axioms prepareRoots_calls_ge

theorem signFromOutput_calls_ge (answers : Answers) (cache : Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) :
    77056 ≤ calls answers (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  rw [calls_bind, calls_bind answers (prepareRoots (digestIndex output))]
  have h := prepareRoots_calls_ge answers (digestIndex output)
  omega

theorem digest_calls (answers : Answers) (rho : Digest) (message : Message) (counter : BitVec 32) :
    calls answers (digest rho message counter) = 1 := by
  change calls answers (SigGolfCandidate.T3.Spec.query (.inl (.inr _))) = 1
  exact calls_query answers _

theorem digestSearch_none_calls_ge (answers : Answers) (rho : Digest) (message : Message)
    (counter fuel : Nat) (hn : evalWithAnswerFn answers (sharedDigestSearch rho message counter fuel) = none) :
    fuel ≤ calls answers (sharedDigestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    simp only [sharedDigestSearch, evalWithAnswerFn_bind] at hn
    rw [sharedDigestSearch, calls_bind, digest_calls]
    cases ha : digestAccepted (evalWithAnswerFn answers (digest rho message (BitVec.ofNat 32 counter))) with
    | false =>
      simp only [ha, Bool.false_eq_true, if_false] at hn ⊢
      have h := ih (counter+1) hn
      omega
    | true =>
      simp only [ha, if_true, evalWithAnswerFn_pure, reduceCtorEq] at hn

theorem signPayload_calls_ge (answers : Answers) (cache : Cache) (message : Message) :
    65536 ≤ calls answers (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  rw [calls_bind]
  generalize hr : evalWithAnswerFn answers (privateNonce message) = rho
  rw [calls_bind answers (sharedDigestSearch rho message 0 digestAttemptLimit)]
  cases hd : evalWithAnswerFn answers (sharedDigestSearch rho message 0 digestAttemptLimit) with
  | none =>
    simp only [hd, calls_pure, Nat.add_zero]
    have h := digestSearch_none_calls_ge answers rho message 0 digestAttemptLimit hd
    have hcap : 65536 ≤ digestAttemptLimit := by decide
    omega
  | some found =>
    obtain ⟨counter, output⟩ := found
    simp only [hd]
    rw [calls_bind answers (signFromOutput cache rho counter output)]
    have h := signFromOutput_calls_ge answers cache rho counter output
    omega
#print axioms signPayload_calls_ge
end S
#print axioms S.buildLeafPrefixes_calls_ge
end QueryChargeResearch

namespace QueryChargeResearch
open OracleComp OracleSpec OracleComp.EvalDist SigGolfCandidate.T3 SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Security
open SphincsSecurity.QueryCap

#check Derivation.charged
#print SigGolfCandidate.T3.Security.SourceReplay.IsHash
noncomputable def fill (state : LazyPrivate.State) : Answers
  | .inl (.inl n) => (SigGolfCandidate.T3.Security.SourceReplay.known state (.inl (.inl n))).getD (by change Fin (n+1); exact 0)
  | .inl (.inr k) => (SigGolfCandidate.T3.Security.SourceReplay.known state (.inl (.inr k))).getD (by change BitVec 256; exact 0)
  | .inr c => (SigGolfCandidate.T3.Security.SourceReplay.known state (.inr c)).getD (by change BitVec 256; exact 0)

theorem fill_known (state : LazyPrivate.State) (input : Spec.Domain) (answer : Spec.Range input)
    (h : SigGolfCandidate.T3.Security.SourceReplay.known state input = some answer) : fill state input = answer := by
  cases input with
  | inl input => cases input <;> simp_all [fill]
  | inr c => simp_all [fill]

theorem resolves_eval {α : Type} {state : LazyPrivate.State} {p : M α} {value : α}
    (h : SigGolfCandidate.T3.Security.SourceReplay.Resolves state p value) : evalWithAnswerFn (fill state) p = value := by
  induction h with
  | pure value => rfl
  | query input answer ha next value ht ih =>
    rw [evalWithAnswerFn_bind]
    change evalWithAnswerFn (fill state) (next (fill state input)) = value
    rw [fill_known state input answer ha]
    exact ih

theorem counted_hash {α : Type} (p : M α) (hp : SigGolfCandidate.T3.Security.SourceReplay.HashOnly p) :
    SigGolfCandidate.T3.Security.SourceReplay.HashOnly (counted Derivation.charged p) := by
  unfold SigGolfCandidate.T3.Security.SourceReplay.HashOnly at hp ⊢
  induction p using OracleComp.inductionOn with
  | pure value => simp [counted_pure, SigGolfCandidate.T3.Security.SourceReplay.HashOnly]
  | query_bind input next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp
    rw [counted_query_bind]
    exact SigGolfCandidate.T3.Security.SourceQueries.bind_allowed _ (by simpa using hp.1) (fun a =>
      SigGolfCandidate.T3.Security.SourceQueries.bind_allowed _ (ih a (hp.2 a)) (fun _ => SigGolfCandidate.T3.Security.SourceQueries.pure_allowed _ _))


theorem charge_hash (input : Spec.Domain) (h : SigGolfCandidate.T3.Security.SourceReplay.IsHash input) :
    FullGame.queryCharge input = 1 := by
  cases input with
  | inl input => cases input <;> simp_all [FullGame.queryCharge, Derivation.charged, SigGolfCandidate.T3.Security.SourceReplay.IsHash]
  | inr c => rfl

theorem counted_eval {α : Type} (answers : Answers) (p : M α)
    (hp : SigGolfCandidate.T3.Security.SourceReplay.HashOnly p) :
    evalWithAnswerFn answers (counted Derivation.charged p) = (evalWithAnswerFn answers p, calls answers p) := by
  unfold SigGolfCandidate.T3.Security.SourceReplay.HashOnly at hp
  induction p using OracleComp.inductionOn with
  | pure value => simp [counted_pure, calls_pure]
  | query_bind input next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp
    rw [counted_query_bind]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [ih _ (hp.2 _)]
    have hc := charge_hash input hp.1
    simp only [FullGame.queryCharge] at hc
    simp only [hc, evalWithAnswerFn_bind, calls_bind, calls_query]


theorem run_calls {α : Type} (p : M α) (hp : SigGolfCandidate.T3.Security.SourceReplay.HashOnly p)
    (before : CountedPrivate.State) (result : α × CountedPrivate.State)
    (hr : result ∈ support (CountedPrivate.run p before)) :
    ∃ answers : Answers, result.2.1 = before.1 + calls answers p := by
  rw [CountedPrivate.run, support_map] at hr
  obtain ⟨middle, hm, rfl⟩ := hr
  let answers := fill middle.2
  have he := resolves_eval (SigGolfCandidate.T3.Security.SourceReplay.resolves_of_run
    (counted Derivation.charged p) (counted_hash p hp) before.2 middle hm)
  have hc := congrArg Prod.snd (he.symm.trans (counted_eval answers p hp))
  exact ⟨answers, congrArg (fun n => before.1 + n) hc⟩

theorem payload_run_charge (cache : Cache) (message : Message) (before : CountedPrivate.State)
    (result : Option SigGolfCandidate.Research.SharedForest.Signature × CountedPrivate.State)
    (hr : result ∈ support (CountedPrivate.run (SigGolfCandidate.Research.SharedForest.signPayload cache message) before)) :
    before.1 + 65536 ≤ result.2.1 := by
  obtain ⟨answers, hc⟩ := run_calls _
    (ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref.shared_signPayload_hashOnly cache message) before result hr
  have h := S.signPayload_calls_ge answers cache message
  omega


attribute [local instance] Classical.propDecidable

noncomputable local instance (priority := 100000) cacheEq : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

set_option maxHeartbeats 400000 in
theorem authenticated_charge (published : Cache) (request : SigGolfCandidate.T3.Security.Request)
    (before : CountedPrivate.State)
    (result : Option SigGolfCandidate.Research.SharedForest.Signature × CountedPrivate.State)
    (hr : result ∈ support (CountedPrivate.run
      (ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign published request) before)) :
    before.1 + (if request.cache = published then 65536 else 0) ≤ result.2.1 := by
  classical
  by_cases hc : request.cache = published
  · simp only [hc, if_true]
    unfold ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign at hr
    rw [CountedPrivate.run_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    simp only [hc, if_true] at hr
    have hpay := payload_run_charge published request.message mid.2 result hr
    have hmac := CountedPrivate.count_monotone _ before mid hm
    omega
  · simp only [hc, if_false, Nat.add_zero]
    exact CountedPrivate.count_monotone _ before result hr

#print axioms authenticated_charge
end QueryChargeResearch

namespace QueryChargeResearch
open OracleComp OracleSpec OracleComp.EvalDist SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired (Requests)
attribute [local instance] Classical.propDecidable

noncomputable local instance (priority := 100000) cacheEqInteraction : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

noncomputable def goodRequests (published : Cache) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) : Nat :=
  (log.filter fun entry => decide (entry.1.cache = published)).length

noncomputable def interactionRun {α : Type} (published : Cache)
    (program : OracleComp ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction α)
    (before : CountedPrivate.State) :=
  ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (fun input => CountedPrivate.handler (.inl input))
    (fun request => simulateQ CountedPrivate.handler
      (ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign published request)) program before

set_option maxHeartbeats 400000 in
theorem interaction_charge {α : Type} (published : Cache)
    (program : OracleComp ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction α) :
    ∀ before result, result ∈ support (interactionRun published program before) →
      before.1 + 65536 * goodRequests published result.1.2 ≤ result.2.1 := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    intro before result hr
    rw [interactionRun, ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_pure,
      support_pure, Set.mem_singleton_iff] at hr
    subst result
    simp [goodRequests]
  | query_bind input next ih =>
    intro before result hr
    cases input with
    | inl input =>
      rw [interactionRun, ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_public,
        mem_support_bind_iff] at hr
      obtain ⟨mid, hm, hr⟩ := hr
      have ht := ih mid.1 mid.2 result hr
      change mid ∈ support (CountedPrivate.run (liftM (Spec.query (.inl input))) before) at hm
      have hq := CountedPrivate.count_monotone _ before mid hm
      omega
    | inr request =>
      rw [interactionRun, ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_request,
        CountedPrivate.run_simulate, mem_support_bind_iff] at hr
      obtain ⟨mid, hm, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨tail, ht, rfl⟩ := hr
      have hi := ih mid.1 mid.2 tail ht
      have hs := authenticated_charge published request before mid hm
      by_cases hc : request.cache = published
      · simp [goodRequests, hc] at hi hs ⊢
        have hsum := (Nat.add_le_add_right hs (65536 * goodRequests published tail.1.2)).trans hi
        simpa [goodRequests, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
      · simp [goodRequests, hc] at hi hs ⊢
        exact (Nat.add_le_add_right hs _).trans hi


theorem interaction_slots {α : Type} (published : Cache)
    (program : OracleComp ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction α)
    (before : CountedPrivate.State) (result : (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × CountedPrivate.State)
    (hr : result ∈ support (interactionRun published program before)) (q : Nat)
    (hq : result.2.1 ≤ q) (hlife : result.1.2.length ≤ 2^32) :
    goodRequests published result.1.2 ≤ min (2^32) (q / 65536) := by
  have hc : 65536 * goodRequests published result.1.2 ≤ q :=
    (Nat.le_add_left _ _).trans ((interaction_charge published program before result hr).trans hq)
  apply le_min
  · unfold goodRequests
    exact (List.length_filter_le _ _).trans hlife
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 65536)).2
    simpa only [Nat.mul_comm] using hc

#print axioms authenticated_charge
#print axioms interaction_charge
#print axioms interaction_slots
end QueryChargeResearch


namespace QueryChargeResearch.Potential40
open ClaudeWCT
open ClaudeWCT.W9.T3.Security.FtsOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem rawChildBase_ok (k : Fin 9) : SharedForest.rawChildBase k.val+7 ≤ 33 ∨
    64 ≤ SharedForest.rawChildBase k.val := by
  have h:∀k : Fin 9,SharedForest.rawChildBase k.val+7 ≤ 33 ∨ 64 ≤ SharedForest.rawChildBase k.val:=by decide +kernel
  exact h k

theorem rankBase_ok (k : Fin 9) : SharedForest.rankBase k.val+10 ≤ 33 ∨
    64 ≤ SharedForest.rankBase k.val := by
  have h:∀k : Fin 9,SharedForest.rankBase k.val+10 ≤ 33 ∨ 64 ≤ SharedForest.rankBase k.val:=by decide +kernel
  exact h k

theorem rawChild_xor (o : HashOutput) {j : Nat} (hj:j < 2^31) (k : Fin 9) :
    SharedForest.rawChildFromOutput (o ^^^ idxMask j) k=SharedForest.rawChildFromOutput o k := by
  apply Fin.ext
  simp only[SharedForest.rawChildFromOutput,toNat_xor_idxMask o hj]
  exact read_xor _ _ _ 7 hj (rawChildBase_ok k)

theorem rawRank_xor (o : HashOutput) {j : Nat} (hj:j < 2^31) (k : Fin 9) :
    SharedForest.rawForestRank (o ^^^ idxMask j) k.val=SharedForest.rawForestRank o k.val := by
  simp only[SharedForest.rawForestRank,toNat_xor_idxMask o hj]
  exact read_xor _ _ _ 10 hj (rankBase_ok k)

theorem digestAccepted_xor (o : HashOutput) {j : Nat} (hj:j < 2^31) :
    SharedForest.digestAccepted (o ^^^ idxMask j)=SharedForest.digestAccepted o := by
  have hr:∀k : Fin 9,SharedForest.forestRank (o ^^^ idxMask j) k.val=SharedForest.forestRank o k.val:=fun k=>by
    apply Fin.ext
    simp only[SharedForest.forestRank,rawRank_xor o hj k]
  have hc:SharedForest.jointAccountingCost (o ^^^ idxMask j)=SharedForest.jointAccountingCost o:=by
    unfold SharedForest.jointAccountingCost
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    simp only[SharedForest.coordinateAccountingCost,hr k,rawChild_xor o hj k]
  have ha:SharedForest.ranksAccepted (o ^^^ idxMask j)=SharedForest.ranksAccepted o:=by
    simp only[SharedForest.ranksAccepted,rawRank_xor o hj]
  have hg:(o.toNat ^^^ j*2^33)/2^242%16384=o.toNat/2^242%16384:=
    read_xor _ _ 242 14 hj (Or.inr (by omega))
  simp only[SharedForest.digestAccepted,toNat_xor_idxMask o hj,hg,hc,ha]

theorem expect_adm_le (X : Fin (2^31) → ℝ≥0∞) (Y M : ℝ≥0∞)
    (hX:∑i,pIdx*X i ≤ M) (hY:Y ≤ M) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun o=>if SharedForest.digestAccepted o=true then X (idxF o) else Y) ≤ M :=
  expect_adm_le_gen SharedForest.digestAccepted (fun o _ hj=>digestAccepted_xor o hj) X Y M hX hY

end QueryChargeResearch.Potential40

namespace QueryChargeResearch.Potential40
open ClaudeWCT
open ClaudeWCT.W9.T3.Security.FtsOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
/-- The digest-search limit of the W9 signer. -/
abbrev lim : ℕ := WCT9.digestAttemptLimit

/-- The public-cache key of the digest query `(rho, m, c)`. -/
def digestKey (rho : Digest) (m : Message) (c : ℕ) : HashInput := pad64 (digestInput rho m (BitVec.ofNat 32 c))

/-- The nonce (`rho`) derived from a private nonce-table value (R6: `rhoMod` of the full output). -/
def rhoOf (h : HashOutput) : Digest := BitVec.ofNat 128 (rhoMod h)

/-- The private coordinate of the nonce of `m`. -/
def nonceCoord (m : Message) : Coordinate := .inr (.inl m)

/-- The digest search read from a public cache: `none` if it reaches an uncached query, `some none` if it exhausts
its fuel, `some (some o)` if it stops at the admissible output `o`. -/
def walk (rc : Sampling.RCache) (rho : Digest) (m : Message) : ℕ → ℕ → Option (Option HashOutput)
  | _, 0 => some none
  | c, f + 1 => match rc (digestKey rho m c) with
    | none => none
    | some o => if SharedForest.digestAccepted o = true then some (some o) else walk rc rho m (c + 1) f

/-- The honest digest index of `m` in the lazy state (if `m` was signed and its search stopped). -/
def honestIdx (s : LazyPrivate.State) (m : Message) : Option (Fin (2 ^ 31)) :=
  match (s.1 (nonceCoord m) : Option HashOutput) with
  | none => none
  | some h => match walk s.2 (rhoOf h) m 0 lim with
    | some (some o) => some (idxF o)
    | _ => none

/-- `x` is a cached admissible output with index `i`. -/
def admAt (x : Option HashOutput) (i : Fin (2 ^ 31)) : Bool :=
  match x with
  | none => false
  | some o => SharedForest.digestAccepted o && decide (idxF o = i)

/-- Cached admissible-at-`i` digest entries `(rho, m, c)` with `c0 ≤ c < lim`. -/
noncomputable def hits (rc : Sampling.RCache) (rho : Digest) (m : Message) (c0 : ℕ) (i : Fin (2 ^ 31)) : ℕ :=
  (Finset.univ.filter fun c : Fin lim => c0 ≤ c.val ∧ admAt (rc (digestKey rho m c.val)) i = true).card

/-- Pending mass at index `i`: cached admissible-at-`i` digest entries of messages with a hidden nonce. -/
noncomputable def pend (s : LazyPrivate.State) (i : Fin (2 ^ 31)) : ℕ :=
  ∑ m ∈ Finset.univ.filter (fun m : Message => (s.1 (nonceCoord m) : Option HashOutput) = none),
    ∑ rho : Digest, hits s.2 rho m 0 i

/-- Number of signed messages whose honest index is `i`. -/
noncomputable def cnt (s : LazyPrivate.State) (i : Fin (2 ^ 31)) : ℕ :=
  (Finset.univ.filter fun m : Message => honestIdx s m = some i).card

/-- `cnt` without the message `m₀`. -/
noncomputable def cntEx (s : LazyPrivate.State) (m₀ : Message) (i : Fin (2 ^ 31)) : ℕ :=
  (Finset.univ.filter fun m : Message => m ≠ m₀ ∧ honestIdx s m = some i).card

/-- The overflow potential: `r` signing slots and `q - n` charged queries left. -/
noncomputable def pot (q r n : ℕ) (s : LazyPrivate.State) : ℝ≥0∞ :=
  if n ≤ q then ∑ i, G 40 (cnt s i) r (pend s i) (q - n) else 0

/-- Every signed message's digest search is fully cached (true between oracle calls). -/
def Settled (s : LazyPrivate.State) : Prop :=
  ∀ m h, (s.1 (nonceCoord m) : Option HashOutput) = some h → walk s.2 (rhoOf h) m 0 lim ≠ none

/-- The FTS overflow event on a lazy state. -/
def Overflow (s : LazyPrivate.State) : Prop := ∃ i, 40 ≤ cnt s i

/-! ### Cache facts -/

/-- Cache extension. -/
def Ext (rc rc' : Sampling.RCache) : Prop := ∀ k o, rc k = some o → rc' k = some o

theorem ext_cacheQuery (rc : Sampling.RCache) (k : HashInput) (o : HashOutput) (hk : rc k = none) :
    Ext rc (rc.cacheQuery k o) := by
  intro k' o' h
  have hne : k' ≠ k := fun he => by rw [he, hk] at h; cases h
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact h

theorem walk_ext {rc rc' : Sampling.RCache} (he : Ext rc rc') (rho : Digest) (m : Message) :
    ∀ f c, walk rc rho m c f ≠ none → walk rc' rho m c f = walk rc rho m c f := by
  intro f
  induction f with
  | zero => intro c _; rfl
  | succ f ih =>
    intro c h
    simp only [walk] at h ⊢
    cases hc : rc (digestKey rho m c) with
    | none => rw [hc] at h; exact absurd rfl h
    | some o =>
      rw [hc] at h
      rw [he _ _ hc]
      simp only at h ⊢
      split_ifs with ha
      · rfl
      · rw [if_neg ha] at h; exact ih _ h

theorem digestInput_len (rho : Digest) (m : Message) (c : BitVec 32) : (digestInput rho m c).length = 64 := by
  simp only [digestInput, List.length_append, SphincsSecurity.bytesLE_length]

theorem pad64_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) = digestInput rho m c := by
  unfold pad64; rw [digestInput_len]; simp

theorem digestKey_injective {rho rho' : Digest} {m m' : Message} {c c' : ℕ} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : digestKey rho m c = digestKey rho' m' c') : rho = rho' ∧ m = m' ∧ c = c' := by
  unfold digestKey at h
  rw [pad64_digestInput, pad64_digestInput] at h
  obtain ⟨h1, h2, h3⟩ := SigGolfCandidate.T3.digestInput_injective h
  refine ⟨h1, h2, ?_⟩
  have := congrArg BitVec.toNat h3
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at this
  exact this

/-! ### Effect of one query on the counts -/

theorem honestIdx_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc')
    (hs : Settled (pc, rc)) (m : Message) : honestIdx (pc, rc') m = honestIdx (pc, rc) m := by
  unfold honestIdx
  dsimp only
  cases hm : (pc (nonceCoord m) : Option HashOutput) with
  | none => rfl
  | some h => dsimp only; rw [walk_ext he _ m lim 0 (hs m h hm)]

theorem settled_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc')
    (hs : Settled (pc, rc)) : Settled (pc, rc') := by
  intro m h hm
  rw [walk_ext he _ m lim 0 (hs m h hm)]
  exact hs m h hm

theorem cnt_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc')
    (hs : Settled (pc, rc)) (i : Fin (2 ^ 31)) : cnt (pc, rc') i = cnt (pc, rc) i := by
  unfold cnt
  simp only [honestIdx_ext he hs]

/-- Nonce entries unchanged: honest indices, pending mass and settledness are unchanged. -/
theorem nonce_same {pc pc' : LazyPrivate.PCache} (rc : Sampling.RCache)
    (h : ∀ m, (pc' (nonceCoord m) : Option HashOutput) = pc (nonceCoord m)) :
    honestIdx (pc', rc) = honestIdx (pc, rc) ∧ pend (pc', rc) = pend (pc, rc) ∧ (Settled (pc', rc) ↔ Settled (pc, rc)) := by
  refine ⟨funext fun m => ?_, funext fun i => ?_, ?_⟩
  · unfold honestIdx; simp only [h]
  · unfold pend; simp only [h]
  · unfold Settled; simp only [h]

theorem hits_insert_le (rc : Sampling.RCache) (k : HashInput) (o : HashOutput)
    (rho : Digest) (m : Message) (c0 : ℕ) (i : Fin (2 ^ 31)) :
    hits (rc.cacheQuery k o) rho m c0 i ≤ hits rc rho m c0 i +
      (Finset.univ.filter fun c : Fin lim => digestKey rho m c.val = k ∧ idxF o = i).card := by
  unfold hits
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hc ⊢
  by_cases hkc : digestKey rho m c.val = k
  · right
    refine ⟨hkc, ?_⟩
    have := hc.2
    rw [hkc, QueryCache.cacheQuery_self] at this
    simp only [admAt, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  · left
    refine ⟨hc.1, ?_⟩
    have := hc.2
    rwa [QueryCache.cacheQuery_of_ne _ _ hkc] at this

theorem key_mass_le (S : Finset Message) (k : HashInput) (o : HashOutput) (i : Fin (2 ^ 31)) :
    ∑ m ∈ S, ∑ rho : Digest, (Finset.univ.filter fun c : Fin lim => digestKey rho m c.val = k ∧ idxF o = i).card ≤
      (if idxF o = i then 1 else 0) := by
  by_cases hi : idxF o = i
  · rw [if_pos hi]
    have hle : ∀ m ∈ S, ∑ rho : Digest, (Finset.univ.filter fun c : Fin lim =>
        digestKey rho m c.val = k ∧ idxF o = i).card =
        (((Finset.univ : Finset Digest) ×ˢ (Finset.univ : Finset (Fin lim))).filter
          (fun p : Digest × Fin lim => digestKey p.1 m p.2.val = k)).card := by
      intro m _
      rw [Finset.card_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro rho _
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl (fun c _ => by simp only [hi, and_true])
    rw [Finset.sum_congr rfl hle]
    have hcard : ∑ m ∈ S, (((Finset.univ : Finset Digest) ×ˢ (Finset.univ : Finset (Fin lim))).filter
        (fun p : Digest × Fin lim => digestKey p.1 m p.2.val = k)).card =
        ((S ×ˢ ((Finset.univ : Finset Digest) ×ˢ (Finset.univ : Finset (Fin lim)))).filter
          (fun p : Message × Digest × Fin lim => digestKey p.2.1 p.1 p.2.2.val = k)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.card_filter]
    rw [hcard]
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    have hl : lim < 2 ^ 32 := by norm_num [lim, WCT9.digestAttemptLimit]
    obtain ⟨h1, h2, h3⟩ := digestKey_injective (lt_trans a.2.2.isLt hl) (lt_trans b.2.2.isLt hl)
      (ha.2.trans hb.2.symm)
    exact Prod.ext h2 (Prod.ext h1 (Fin.ext h3))
  · rw [if_neg hi]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro rho _
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ h
    exact hi h.2

theorem pend_insert_le (pc : LazyPrivate.PCache) (rc : Sampling.RCache) (k : HashInput) (o : HashOutput)
    (i : Fin (2 ^ 31)) :
    pend (pc, rc.cacheQuery k o) i ≤ pend (pc, rc) i + (if idxF o = i then 1 else 0) := by
  unfold pend
  refine le_trans ?_ (Nat.add_le_add_left
    (key_mass_le (Finset.univ.filter fun m : Message => (pc (nonceCoord m) : Option HashOutput) = none) k o i) _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro rho _
  exact hits_insert_le rc k o rho m 0 i

/-! ### One query -/

theorem sum_pIdx : ∑ _j : Fin (2 ^ 31), pIdx = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pIdx, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.mul_inv_cancel (by positivity) (by finiteness)]

theorem G_a_ite (k c r a b : ℕ) (P : Prop) [Decidable P] :
    G (k + 1) c r (a + if P then 1 else 0) b = G (k + 1) c r a b + if P then pNonce * G k c r a b else 0 := by
  split_ifs
  · exact G_a k c r a b
  · simp

theorem pot_mono_n (q r n : ℕ) (s : LazyPrivate.State) : pot q r (n + 1) s ≤ pot q r n s := by
  unfold pot
  split_ifs with h1 h2
  · exact Finset.sum_le_sum fun i _ => G_mono le_rfl le_rfl le_rfl (by omega)
  · omega
  · exact bot_le
  · exact le_rfl

theorem pot_mono_r (q r n : ℕ) (s : LazyPrivate.State) : pot q r n s ≤ pot q (r + 1) n s := by
  unfold pot
  split_ifs
  · exact Finset.sum_le_sum fun i _ => G_mono le_rfl (Nat.le_succ r) le_rfl le_rfl
  · exact le_rfl

theorem run_query_public (y : SphincsSecurity.OracleWorld.Domain) (n : ℕ) (s : LazyPrivate.State) :
    CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl y))) (n, s) =
      (fun res => (res.1, (n + FullGame.queryCharge (.inl y), (s.1, res.2)))) <$>
        (SphincsSecurity.romImpl y).run s.2 := by
  rw [CountedPrivate.run_query, LazyPrivate.run_query]
  simp only [PrivateTable.lazyImpl, StateT.run_mk, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]; rfl

theorem run_query_private (c : Coordinate) (n : ℕ) (s : LazyPrivate.State) :
    CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inr c))) (n, s) =
      (fun res => (res.1, (n + 1, (res.2, s.2)))) <$>
        (randomOracle (spec := Coordinate →ₒ HashOutput) c).run s.1 := by
  rw [CountedPrivate.run_query, LazyPrivate.run_query]
  simp only [PrivateTable.lazyImpl, StateT.run_mk, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]; rfl

theorem romImpl_unif_run (u : unifSpec.Domain) (rc : Sampling.RCache) :
    (SphincsSecurity.romImpl (.inl u)).run rc = (fun v => (v, rc)) <$> (liftM (unifSpec.query u) : ProbComp _) := by
  have hrun := unifFwdImpl.simulateQ_run (hashSpec := SphincsSecurity.HashSpec)
    (liftM (unifSpec.query u) : ProbComp _) rc
  simp only [simulateQ_spec_query] at hrun
  exact hrun

theorem private_support (c : Coordinate) (pc : LazyPrivate.PCache)
    (res : HashOutput × LazyPrivate.PCache)
    (hres : res ∈ support ((randomOracle (spec := Coordinate →ₒ HashOutput) c).run pc)) :
    ∀ c', c' ≠ c → res.2 c' = pc c' := by
  intro c' hne
  rw [randomOracle.run_eq] at hres
  cases hc : pc c with
  | some v =>
    rw [hc] at hres
    simp only [support_pure, Set.mem_singleton_iff] at hres
    subst hres; rfl
  | none =>
    rw [hc] at hres
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hres
    obtain ⟨v, _, rfl⟩ := hres
    exact QueryCache.cacheQuery_of_ne _ _ hne

/-- A query that is not a nonce query is a supermartingale step for `pot` and keeps `Settled`. -/
theorem query_step (q r : ℕ) (x : SigGolfCandidate.T3.Spec.Domain) (hx : ∀ m, x ≠ .inr (nonceCoord m))
    (n : ℕ) (s : LazyPrivate.State) (hs : Settled s) :
    expectedValue (CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query x)) (n, s))
        (fun res => pot q r res.2.1 res.2.2) ≤ pot q r n s ∧
      ∀ res ∈ support (CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query x)) (n, s)), Settled res.2.2 := by
  rcases s with ⟨pc, rc⟩
  rcases x with (u | k) | c
  · rw [run_query_public, romImpl_unif_run]
    simp only [Functor.map_map]
    refine ⟨?_, ?_⟩
    · rw [expectedValue_map]
      apply expectedValue_le_of_support
      intro v _
      simp [FullGame.queryCharge, Derivation.charged]
    · intro res hres
      rw [support_map] at hres
      obtain ⟨v, _, rfl⟩ := hres
      exact hs
  · rw [run_query_public]
    change expectedValue ((fun res => (res.1, (n + 1, (pc, res.2)))) <$> (randomOracle k).run rc) _ ≤ _ ∧
      ∀ res ∈ support ((fun res => (res.1, (n + 1, (pc, res.2)))) <$> (randomOracle k).run rc), _
    rw [randomOracle.run_eq]
    cases hk : rc k with
    | some v =>
      simp only [map_pure, expectedValue_pure, support_pure, Set.mem_singleton_iff, forall_eq]
      exact ⟨pot_mono_n q r n _, hs⟩
    | none =>
      simp only [map_bind, map_pure, expectedValue_bind, expectedValue_pure, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff]
      have hext : ∀ o, Ext rc (rc.cacheQuery k o) := fun o => ext_cacheQuery rc k o hk
      refine ⟨?_, ?_⟩
      · by_cases hq : n + 1 ≤ q
        · have hpt : ∀ o : HashOutput, pot q r (n + 1) (pc, rc.cacheQuery k o) ≤
              ∑ i, G 40 (cnt (pc, rc) i) r (pend (pc, rc) i) (q - (n + 1)) +
                pNonce * G 39 (cnt (pc, rc) (idxF o)) r (pend (pc, rc) (idxF o)) (q - (n + 1)) := by
            intro o
            unfold pot
            rw [if_pos hq]
            calc ∑ i, G 40 (cnt (pc, rc.cacheQuery k o) i) r (pend (pc, rc.cacheQuery k o) i) (q - (n + 1))
                ≤ ∑ i, G 40 (cnt (pc, rc) i) r (pend (pc, rc) i + if idxF o = i then 1 else 0) (q - (n + 1)) := by
                  apply Finset.sum_le_sum
                  intro i _
                  rw [cnt_ext (hext o) hs]
                  exact G_mono le_rfl le_rfl (pend_insert_le pc rc k o i) le_rfl
              _ = _ := by
                  simp only [G_a_ite, Finset.sum_add_distrib]
                  rw [Finset.sum_ite_eq]
                  simp
          calc expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun o => pot q r (n + 1) (pc, rc.cacheQuery k o))
              ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun o =>
                  ∑ i, G 40 (cnt (pc, rc) i) r (pend (pc, rc) i) (q - (n + 1)) +
                    pNonce * G 39 (cnt (pc, rc) (idxF o)) r (pend (pc, rc) (idxF o)) (q - (n + 1))) :=
                expectedValue_mono _ hpt
            _ = ∑ j, pIdx * (∑ i, G 40 (cnt (pc, rc) i) r (pend (pc, rc) i) (q - (n + 1)) +
                  pNonce * G 39 (cnt (pc, rc) j) r (pend (pc, rc) j) (q - (n + 1))) :=
                expect_idx (fun j => ∑ i, G 40 (cnt (pc, rc) i) r (pend (pc, rc) i) (q - (n + 1)) +
                  pNonce * G 39 (cnt (pc, rc) j) r (pend (pc, rc) j) (q - (n + 1)))
            _ = ∑ j, G 40 (cnt (pc, rc) j) r (pend (pc, rc) j) (q - (n + 1) + 1) := by
                simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pIdx, one_mul, G_b, pQuery,
                  ← mul_assoc]
            _ = pot q r n (pc, rc) := by
                unfold pot
                rw [if_pos (by omega), show q - (n + 1) + 1 = q - n by omega]
        · have h0 : ∀ o : HashOutput, pot q r (n + 1) (pc, rc.cacheQuery k o) = 0 := fun o => by
            unfold pot; rw [if_neg hq]
          simp only [h0]
          exact expectedValue_le_of_support fun _ _ => bot_le
      · rintro res ⟨o, _, rfl⟩
        exact settled_ext (hext o) hs
  · rw [run_query_private]
    have hc : ∀ m, c ≠ nonceCoord m := fun m he => hx m (by rw [he])
    have hsame : ∀ res ∈ support ((randomOracle (spec := Coordinate →ₒ HashOutput) c).run pc),
        ∀ m, (res.2 (nonceCoord m) : Option HashOutput) = pc (nonceCoord m) :=
      fun res hres m => private_support c pc res hres _ (hc m).symm
    refine ⟨?_, ?_⟩
    · rw [expectedValue_map]
      apply expectedValue_le_of_support
      intro res hres
      have hn := nonce_same rc (hsame res hres)
      refine le_trans (le_of_eq ?_) (pot_mono_n q r n (pc, rc))
      unfold pot cnt
      rw [hn.1, hn.2.1]
    · intro res hres
      rw [support_map] at hres
      obtain ⟨res, hres, rfl⟩ := hres
      exact (nonce_same rc (hsame res hres)).2.2.2 hs

/-! ### Programs without nonce queries -/

/-- The query is not a nonce query. -/
def NotNonce (x : SigGolfCandidate.T3.Spec.Domain) : Prop := ∀ m, x ≠ .inr (nonceCoord m)

/-- A program without nonce queries is a supermartingale for `pot` and keeps `Settled`. -/
theorem prog_step {α : Type} (q r : ℕ) (P : M α) (hP : AllQueriesSatisfy P NotNonce) :
    ∀ (n : ℕ) (s : LazyPrivate.State), Settled s →
      expectedValue (CountedPrivate.run P (n, s)) (fun res => pot q r res.2.1 res.2.2) ≤ pot q r n s ∧
      ∀ res ∈ support (CountedPrivate.run P (n, s)), Settled res.2.2 := by
  induction P using OracleComp.inductionOn with
  | pure a =>
    intro n s hs
    simp only [CountedPrivate.run_pure, expectedValue_pure, support_pure, Set.mem_singleton_iff, forall_eq]
    exact ⟨le_rfl, hs⟩
  | query_bind x next ih =>
    intro n s hs
    rw [allQueriesSatisfy_query_bind_iff] at hP
    obtain ⟨hx, hnext⟩ := hP
    have hq := query_step q r x hx n s hs
    rw [CountedPrivate.run_bind]
    refine ⟨?_, ?_⟩
    · rw [expectedValue_bind]
      exact le_trans (expectedValue_mono_of_support fun res hres =>
        (ih res.1 (hnext res.1) res.2.1 res.2.2 (hq.2 res hres)).1) hq.1
    · intro res hres
      rw [mem_support_bind_iff] at hres
      obtain ⟨mid, hmid, hres⟩ := hres
      exact (ih mid.1 (hnext mid.1) mid.2.1 mid.2.2 (hq.2 mid hmid)).2 res hres

theorem notNonce_of_avoids {α : Type} (P : M α) (h : ∀ m, NonceFreshness.Avoids m P) :
    AllQueriesSatisfy P NotNonce := by
  induction P using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind x next ih =>
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨fun m he => ?_, fun u => ih u fun m => ?_⟩
    · have := (allQueriesSatisfy_query_bind_iff _ _ _).1 (h m)
      exact this.1 he
    · exact ((allQueriesSatisfy_query_bind_iff _ _ _).1 (h m)).2 u

/-! ### The digest search of a freshly drawn nonce -/

/-- Every signed message other than `m₀` is settled. -/
def SettledEx (s : LazyPrivate.State) (m₀ : Message) : Prop :=
  ∀ m h, m ≠ m₀ → (s.1 (nonceCoord m) : Option HashOutput) = some h → walk s.2 (rhoOf h) m 0 lim ≠ none

/-- The first `c` digest queries of `(rho, m)` are cached and not admissible. -/
def Prefix (rc : Sampling.RCache) (rho : Digest) (m : Message) (c : ℕ) : Prop :=
  ∀ c' < c, ∃ o, rc (digestKey rho m c') = some o ∧ SharedForest.digestAccepted o = false

/-- The potential during the digest search of `m₀` (nonce `rho`) at counter `c`. -/
noncomputable def mid (q r : ℕ) (m₀ : Message) (rho : Digest) (c n : ℕ) (s : LazyPrivate.State) : ℝ≥0∞ :=
  if n ≤ q then ∑ i, (G 40 (cntEx s m₀ i) r (pend s i) (q - n) +
    (pIdx + hits s.2 rho m₀ c i) * G 39 (cntEx s m₀ i) r (pend s i) (q - n)) else 0

theorem lim_lt : lim < 2 ^ 32 := by norm_num [lim, WCT9.digestAttemptLimit]

theorem cnt_split (s : LazyPrivate.State) (m₀ : Message) (i : Fin (2 ^ 31)) :
    cnt s i = cntEx s m₀ i + if honestIdx s m₀ = some i then 1 else 0 := by
  unfold cnt cntEx
  rw [Finset.card_filter, Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ m₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ m₀)]
  have hsum : ∑ m ∈ Finset.univ.erase m₀, (if honestIdx s m = some i then 1 else 0) =
      ∑ m ∈ Finset.univ.erase m₀, (if m ≠ m₀ ∧ honestIdx s m = some i then 1 else 0) :=
    Finset.sum_congr rfl fun m hm => by simp [Finset.ne_of_mem_erase hm]
  rw [hsum]
  simp only [ne_eq, not_true_eq_false, false_and, if_false, zero_add]
  ring

theorem walk_prefix (rc : Sampling.RCache) (rho : Digest) (m : Message) :
    ∀ c, c ≤ lim → Prefix rc rho m c → walk rc rho m 0 lim = walk rc rho m c (lim - c) := by
  intro c
  induction c with
  | zero => intro _ _; rfl
  | succ c ih =>
    intro hc hp
    rw [ih (by omega) (fun c' hc' => hp c' (by omega)), show lim - c = (lim - (c + 1)) + 1 by omega]
    obtain ⟨o, ho, hna⟩ := hp c (by omega)
    simp only [walk, ho, hna, Bool.false_eq_true, if_false]

theorem honestIdx_ext_ex {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc') {m₀ : Message}
    (hs : SettledEx (pc, rc) m₀) (m : Message) (hm : m ≠ m₀) : honestIdx (pc, rc') m = honestIdx (pc, rc) m := by
  unfold honestIdx
  dsimp only
  cases hh : (pc (nonceCoord m) : Option HashOutput) with
  | none => rfl
  | some h => dsimp only; rw [walk_ext he _ m lim 0 (hs m h hm hh)]

theorem cntEx_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc') {m₀ : Message}
    (hs : SettledEx (pc, rc) m₀) (i : Fin (2 ^ 31)) : cntEx (pc, rc') m₀ i = cntEx (pc, rc) m₀ i := by
  unfold cntEx
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro m _
  constructor
  · rintro ⟨hm, h⟩; exact ⟨hm, (honestIdx_ext_ex he hs m hm) ▸ h⟩
  · rintro ⟨hm, h⟩; exact ⟨hm, (honestIdx_ext_ex he hs m hm).symm ▸ h⟩

theorem settledEx_ext {pc : LazyPrivate.PCache} {rc rc' : Sampling.RCache} (he : Ext rc rc') {m₀ : Message}
    (hs : SettledEx (pc, rc) m₀) : SettledEx (pc, rc') m₀ := by
  intro m h hm hh
  rw [walk_ext he _ m lim 0 (hs m h hm hh)]
  exact hs m h hm hh

theorem pend_insert_own (pc : LazyPrivate.PCache) (rc : Sampling.RCache) {m₀ : Message} {h₀ : HashOutput}
    (hn : (pc (nonceCoord m₀) : Option HashOutput) = some h₀) (rho : Digest) {c : ℕ} (hc : c < lim)
    (o : HashOutput) (i : Fin (2 ^ 31)) :
    pend (pc, rc.cacheQuery (digestKey rho m₀ c) o) i = pend (pc, rc) i := by
  unfold pend hits
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hne : m ≠ m₀ := fun he => by rw [he] at hm; rw [hm] at hn; cases hn
  apply Finset.sum_congr rfl
  intro rho' _
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c' _
  have hk : digestKey rho' m c'.val ≠ digestKey rho m₀ c := fun he =>
    hne (digestKey_injective (lt_trans c'.isLt lim_lt) (lt_trans hc lim_lt) he).2.1
  simp only [QueryCache.cacheQuery_of_ne _ _ hk]

theorem hits_succ_eq (rc : Sampling.RCache) (rho : Digest) (m : Message) (c : ℕ) (i : Fin (2 ^ 31))
    (h : admAt (rc (digestKey rho m c)) i = false) : hits rc rho m (c + 1) i = hits rc rho m c i := by
  unfold hits
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c' _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases Nat.lt_or_ge c c'.val with hlt | hge
    · omega
    · have : c'.val = c := by omega
      rw [this, h] at h2; cases h2

theorem hits_insert_succ (rc : Sampling.RCache) (rho : Digest) (m : Message) {c : ℕ} (hc : c < lim)
    (o : HashOutput) (i : Fin (2 ^ 31)) :
    hits (rc.cacheQuery (digestKey rho m c) o) rho m (c + 1) i = hits rc rho m (c + 1) i := by
  unfold hits
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c' _
  constructor
  · rintro ⟨h1, h2⟩
    have hk : digestKey rho m c'.val ≠ digestKey rho m c := fun he =>
      absurd (digestKey_injective (lt_trans c'.isLt lim_lt) (lt_trans hc lim_lt) he).2.2 (by omega)
    rw [QueryCache.cacheQuery_of_ne _ _ hk] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hk : digestKey rho m c'.val ≠ digestKey rho m c := fun he =>
      absurd (digestKey_injective (lt_trans c'.isLt lim_lt) (lt_trans hc lim_lt) he).2.2 (by omega)
    rw [QueryCache.cacheQuery_of_ne _ _ hk]
    exact ⟨h1, h2⟩

theorem hits_pos (rc : Sampling.RCache) (rho : Digest) (m : Message) {c : ℕ} (hc : c < lim) {o : HashOutput}
    (ho : rc (digestKey rho m c) = some o) (ha : SharedForest.digestAccepted o = true) :
    1 ≤ hits rc rho m c (idxF o) := by
  unfold hits
  apply Finset.card_pos.2
  refine ⟨⟨c, hc⟩, ?_⟩
  simp [ho, admAt, ha]

theorem cnt_le_G_stop (q r n : ℕ) (s : LazyPrivate.State) (m₀ : Message) (j : Fin (2 ^ 31))
    (hidx : honestIdx s m₀ = some j) :
    ∑ i, G 40 (cnt s i) r (pend s i) (q - n) =
      ∑ i, G 40 (cntEx s m₀ i) r (pend s i) (q - n) + G 39 (cntEx s m₀ j) r (pend s j) (q - n) := by
  have : ∀ i, G 40 (cnt s i) r (pend s i) (q - n) =
      G 40 (cntEx s m₀ i) r (pend s i) (q - n) + if j = i then G 39 (cntEx s m₀ i) r (pend s i) (q - n) else 0 := by
    intro i
    rw [cnt_split s m₀ i, hidx]
    by_cases hji : j = i
    · subst hji; simp [G_c]
    · simp [hji]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem charge_public (k : HashInput) : FullGame.queryCharge (.inl (.inr k)) = 1 := by
  simp [FullGame.queryCharge, Derivation.charged]

theorem digestSearch_succ_eq (rho : Digest) (m : Message) (c f : ℕ) : SharedForest.sharedDigestSearch rho m c (f + 1) =
    (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr (digestKey rho m c)))) >>= fun output =>
      if SharedForest.digestAccepted output = true then pure (some (BitVec.ofNat 32 c, output))
      else SharedForest.sharedDigestSearch rho m (c + 1) f) := rfl

theorem walk_stop (rc : Sampling.RCache) (rho : Digest) (m : Message) {c : ℕ} (hc : c < lim)
    (hp : Prefix rc rho m c) {o : HashOutput} (ho : rc (digestKey rho m c) = some o)
    (ha : SharedForest.digestAccepted o = true) : walk rc rho m 0 lim = some (some o) := by
  rw [walk_prefix rc rho m c hc.le hp, show lim - c = (lim - c - 1) + 1 by omega]
  simp only [walk, ho, ha, if_true]

theorem honestIdx_of_walk {pc : LazyPrivate.PCache} {rc : Sampling.RCache} {m₀ : Message} {h₀ : HashOutput}
    (hn : (pc (nonceCoord m₀) : Option HashOutput) = some h₀) {o : HashOutput}
    (hw : walk rc (rhoOf h₀) m₀ 0 lim = some (some o)) : honestIdx (pc, rc) m₀ = some (idxF o) := by
  unfold honestIdx; dsimp only; rw [hn]; dsimp only; rw [hw]

theorem settled_of_ex {pc : LazyPrivate.PCache} {rc : Sampling.RCache} {m₀ : Message} {h₀ : HashOutput}
    (hn : (pc (nonceCoord m₀) : Option HashOutput) = some h₀) (hse : SettledEx (pc, rc) m₀)
    (hw : walk rc (rhoOf h₀) m₀ 0 lim ≠ none) : Settled (pc, rc) := by
  intro m h hh
  by_cases hm : m = m₀
  · subst hm
    have : h = h₀ := by
      have h2 : (pc (nonceCoord m) : Option HashOutput) = some h := hh
      rw [hn] at h2; exact (Option.some.inj h2).symm
    subst this; exact hw
  · exact hse m h hm hh

/-- The potential after stopping at index `j`. -/
theorem pot_stop (q r n : ℕ) (s : LazyPrivate.State) (m₀ : Message) (j : Fin (2 ^ 31))
    (hidx : honestIdx s m₀ = some j) :
    pot q r n s = if n ≤ q then ∑ i, G 40 (cntEx s m₀ i) r (pend s i) (q - n) +
      G 39 (cntEx s m₀ j) r (pend s j) (q - n) else 0 := by
  unfold pot
  split_ifs
  · exact cnt_le_G_stop q r n s m₀ j hidx
  · rfl

theorem mid_mono_n (q r : ℕ) (m₀ : Message) (rho : Digest) (c n : ℕ) (s : LazyPrivate.State) :
    mid q r m₀ rho c (n + 1) s ≤ mid q r m₀ rho c n s := by
  unfold mid
  split_ifs with h1 h2
  · apply Finset.sum_le_sum
    intro i _
    exact add_le_add (G_mono le_rfl le_rfl le_rfl (by omega))
      (mul_le_mul' le_rfl (G_mono le_rfl le_rfl le_rfl (by omega)))
  · omega
  · exact bot_le
  · exact le_rfl

theorem stop_le_mid (q r n : ℕ) (s : LazyPrivate.State) (m₀ : Message) (rho : Digest) (c : ℕ) (j : Fin (2 ^ 31))
    (hpos : 1 ≤ hits s.2 rho m₀ c j) :
    (if n + 1 ≤ q then ∑ i, G 40 (cntEx s m₀ i) r (pend s i) (q - (n + 1)) +
      G 39 (cntEx s m₀ j) r (pend s j) (q - (n + 1)) else 0) ≤ mid q r m₀ rho c n s := by
  unfold mid
  split_ifs with h1 h2
  · rw [Finset.sum_add_distrib]
    refine add_le_add (Finset.sum_le_sum fun i _ => G_mono le_rfl le_rfl le_rfl (by omega)) ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => (pIdx + (hits s.2 rho m₀ c i : ℝ≥0∞)) *
      G 39 (cntEx s m₀ i) r (pend s i) (q - n)) (fun _ _ => bot_le) (Finset.mem_univ j))
    calc G 39 (cntEx s m₀ j) r (pend s j) (q - (n + 1)) ≤ 1 * G 39 (cntEx s m₀ j) r (pend s j) (q - n) := by
          rw [one_mul]; exact G_mono le_rfl le_rfl le_rfl (by omega)
      _ ≤ _ := by
          refine mul_le_mul' ?_ le_rfl
          exact le_add_left (by exact_mod_cast hpos)
  · omega
  · exact bot_le
  · exact le_rfl

/-- The digest search of a freshly drawn nonce: the potential is bounded by `mid`, and every signed message is
settled afterwards. -/
theorem search_step (q r : ℕ) (m₀ : Message) (h₀ : HashOutput) :
    ∀ (f c : ℕ), c + f = lim → ∀ (n : ℕ) (pc : LazyPrivate.PCache) (rc : Sampling.RCache),
      (pc (nonceCoord m₀) : Option HashOutput) = some h₀ → SettledEx (pc, rc) m₀ →
      Prefix rc (rhoOf h₀) m₀ c →
      expectedValue (CountedPrivate.run (SharedForest.sharedDigestSearch (rhoOf h₀) m₀ c f) (n, (pc, rc)))
          (fun res => pot q r res.2.1 res.2.2) ≤ mid q r m₀ (rhoOf h₀) c n (pc, rc) ∧
        ∀ res ∈ support (CountedPrivate.run (SharedForest.sharedDigestSearch (rhoOf h₀) m₀ c f) (n, (pc, rc))),
          Settled res.2.2 := by
  intro f
  induction f with
  | zero =>
    intro c hc n pc rc hn hse hpre
    have hcl : c = lim := by omega
    have hw : walk rc (rhoOf h₀) m₀ 0 lim = some none := by
      rw [walk_prefix rc _ m₀ c (by omega) hpre, hcl, Nat.sub_self]; rfl
    have hidx : honestIdx (pc, rc) m₀ = none := by
      unfold honestIdx; dsimp only; rw [hn]; dsimp only; rw [hw]
    rw [show SharedForest.sharedDigestSearch (rhoOf h₀) m₀ c 0 = pure none from rfl, CountedPrivate.run_pure]
    simp only [expectedValue_pure, support_pure, Set.mem_singleton_iff, forall_eq]
    refine ⟨?_, settled_of_ex hn hse (by rw [hw]; simp)⟩
    unfold pot mid
    split_ifs with hq
    · apply Finset.sum_le_sum
      intro i _
      rw [cnt_split _ m₀ i, hidx]
      simp only [reduceCtorEq, if_false, add_zero]
      exact le_self_add
    · exact le_rfl
  | succ f ih =>
    intro c hc n pc rc hn hse hpre
    have hcl : c < lim := by omega
    rw [digestSearch_succ_eq, CountedPrivate.run_bind, run_query_public, bind_map_left, charge_public]
    change expectedValue ((randomOracle (digestKey (rhoOf h₀) m₀ c)).run rc >>= _) _ ≤ _ ∧
      ∀ res ∈ support ((randomOracle (digestKey (rhoOf h₀) m₀ c)).run rc >>= _), _
    rw [randomOracle.run_eq]
    cases hk : rc (digestKey (rhoOf h₀) m₀ c) with
    | some o =>
      simp only [pure_bind]
      by_cases ha : SharedForest.digestAccepted o = true
      · simp only [ha, if_true, CountedPrivate.run_pure, expectedValue_pure, support_pure,
          Set.mem_singleton_iff, forall_eq]
        have hw := walk_stop rc (rhoOf h₀) m₀ hcl hpre hk ha
        have hidx := honestIdx_of_walk hn hw
        refine ⟨?_, settled_of_ex hn hse (by rw [hw]; simp)⟩
        rw [pot_stop q r (n + 1) _ m₀ _ hidx]
        exact stop_le_mid q r n _ m₀ _ c _ (hits_pos rc _ m₀ hcl hk ha)
      · simp only [ha, Bool.false_eq_true, if_false]
        have hna : SharedForest.digestAccepted o = false := by simpa using ha
        have hpre' : Prefix rc (rhoOf h₀) m₀ (c + 1) := by
          intro c' hc'
          rcases Nat.lt_or_ge c' c with h | h
          · exact hpre c' h
          · have : c' = c := by omega
            subst this; exact ⟨o, hk, hna⟩
        have hih := ih (c + 1) (by omega) (n + 1) pc rc hn hse hpre'
        refine ⟨le_trans hih.1 (le_trans (le_of_eq ?_) (mid_mono_n q r m₀ _ c n _)), hih.2⟩
        have hh : ∀ i, hits rc (rhoOf h₀) m₀ (c + 1) i = hits rc (rhoOf h₀) m₀ c i :=
          fun i => hits_succ_eq rc _ m₀ c i (by simp [hk, admAt, hna])
        unfold mid
        simp only [hh]
    | none =>
      simp only [bind_assoc, pure_bind, expectedValue_bind, mem_support_bind_iff]
      have hext : ∀ o, Ext rc (rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) := fun o => ext_cacheQuery rc _ o hk
      have hcont : ∀ o, SharedForest.digestAccepted o = false →
          expectedValue (CountedPrivate.run (SharedForest.sharedDigestSearch (rhoOf h₀) m₀ (c + 1) f)
            (n + 1, (pc, rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o))) (fun res => pot q r res.2.1 res.2.2) ≤
              mid q r m₀ (rhoOf h₀) c (n + 1) (pc, rc) ∧
          ∀ res ∈ support (CountedPrivate.run (SharedForest.sharedDigestSearch (rhoOf h₀) m₀ (c + 1) f)
            (n + 1, (pc, rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o))), Settled res.2.2 := by
        intro o hna
        have hpre' : Prefix (rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) (rhoOf h₀) m₀ (c + 1) := by
          intro c' hc'
          rcases Nat.lt_or_ge c' c with h | h
          · obtain ⟨o', ho', hna'⟩ := hpre c' h
            exact ⟨o', hext o _ _ ho', hna'⟩
          · have : c' = c := by omega
            subst this; exact ⟨o, QueryCache.cacheQuery_self _ _ _, hna⟩
        have hih := ih (c + 1) (by omega) (n + 1) pc _ hn (settledEx_ext (hext o) hse) hpre'
        refine ⟨le_trans hih.1 (le_of_eq ?_), hih.2⟩
        have hh : ∀ i, hits rc (rhoOf h₀) m₀ (c + 1) i = hits rc (rhoOf h₀) m₀ c i :=
          fun i => hits_succ_eq rc _ m₀ c i (by simp [hk, admAt])
        unfold mid
        simp only [cntEx_ext (hext o) hse, pend_insert_own pc rc hn _ hcl, hits_insert_succ rc _ m₀ hcl, hh]
      have hstop : ∀ o, SharedForest.digestAccepted o = true →
          pot q r (n + 1) (pc, rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) =
            if n + 1 ≤ q then ∑ i, G 40 (cntEx (pc, rc) m₀ i) r (pend (pc, rc) i) (q - (n + 1)) +
              G 39 (cntEx (pc, rc) m₀ (idxF o)) r (pend (pc, rc) (idxF o)) (q - (n + 1)) else 0 := by
        intro o ha
        have hw := walk_stop (rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) (rhoOf h₀) m₀ hcl
          (fun c' hc' => by obtain ⟨o', ho', hna'⟩ := hpre c' hc'; exact ⟨o', hext o _ _ ho', hna'⟩)
          (QueryCache.cacheQuery_self _ _ _) ha
        rw [pot_stop q r (n + 1) _ m₀ _ (honestIdx_of_walk hn hw)]
        simp only [cntEx_ext (hext o) hse, pend_insert_own pc rc hn _ hcl]
      refine ⟨?_, ?_⟩
      · refine le_trans ?_ (mid_mono_n q r m₀ _ c n _)
        refine le_trans (expectedValue_mono _ (g := fun o => _)
          (h := fun o => if SharedForest.digestAccepted o = true then
            (if n + 1 ≤ q then ∑ i, G 40 (cntEx (pc, rc) m₀ i) r (pend (pc, rc) i) (q - (n + 1)) +
              G 39 (cntEx (pc, rc) m₀ (idxF o)) r (pend (pc, rc) (idxF o)) (q - (n + 1)) else 0)
            else mid q r m₀ (rhoOf h₀) c (n + 1) (pc, rc)) fun o => ?_) ?_
        · by_cases ha : SharedForest.digestAccepted o = true
          · simp only [ha, if_true, CountedPrivate.run_pure, expectedValue_pure]
            exact le_of_eq (hstop o ha)
          · have hna : SharedForest.digestAccepted o = false := by simpa using ha
            simp only [hna, Bool.false_eq_true, if_false]
            exact (hcont o hna).1
        · change expectedValue ($ᵗ HashOutput : ProbComp HashOutput) _ ≤ _
          refine expect_adm_le (fun j => if n + 1 ≤ q then
            ∑ i, G 40 (cntEx (pc, rc) m₀ i) r (pend (pc, rc) i) (q - (n + 1)) +
              G 39 (cntEx (pc, rc) m₀ j) r (pend (pc, rc) j) (q - (n + 1)) else 0) _ _ ?_ le_rfl
          unfold mid
          split_ifs with hq
          · simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pIdx, one_mul]
            refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => mul_le_mul' le_self_add le_rfl)
          · simp
      · rintro res ⟨o, _, hres⟩
        by_cases ha : SharedForest.digestAccepted o = true
        · simp only [ha, if_true, CountedPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hres
          subst hres
          have hw := walk_stop (rc.cacheQuery (digestKey (rhoOf h₀) m₀ c) o) (rhoOf h₀) m₀ hcl
            (fun c' hc' => by obtain ⟨o', ho', hna'⟩ := hpre c' hc'; exact ⟨o', hext o _ _ ho', hna'⟩)
            (QueryCache.cacheQuery_self _ _ _) ha
          exact settled_of_ex hn (settledEx_ext (hext o) hse) (by rw [hw]; simp)
        · have hna : SharedForest.digestAccepted o = false := by simpa using ha
          simp only [hna, Bool.false_eq_true, if_false] at hres
          exact (hcont o hna).2 res hres

/-! ### Drawing a fresh nonce -/

/-- R6: the nonce `rhoOf h = rhoMod h` of a uniform 256-bit output has point masses at most `pNonce`
(`uniform_hash_mod_le`, `κ·2^-128 = ⌈2^256/R⌉/2^256 = pNonce`): an inequality, not a uniform law. -/
theorem expect_rho (f : Digest → ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun h => f (rhoOf h)) ≤ pNonce * ∑ rho, f rho := by
  refine (SigGolfCandidate.T3.Security.LazyPrivate.uniform_hash_mod_le f).trans (le_of_eq ?_)
  unfold expectedValue
  rw [tsum_fintype, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun rho _ => ?_
  rw [probOutput_uniformSample, Fintype.card_bitVec, SigGolfCandidate.T3.Security.LazyPrivate.rhoKappa, pNonce,
    Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, div_eq_mul_inv, show ((2 : ℝ≥0∞) ^ 256)⁻¹ = (2 ^ 128)⁻¹ * (2 ^ 128)⁻¹ by
      rw [← ENNReal.mul_inv (by left; positivity) (by left; finiteness), ← pow_add]]
  ring

theorem nonceCoord_injective {m m' : Message} (h : nonceCoord m = nonceCoord m') : m = m' := by
  unfold nonceCoord at h
  exact Sum.inl.inj (Sum.inr.inj h)


/-- Drawing the nonce of a fresh message consumes one signing slot and the message's pending entries. -/
theorem nonce_fresh_step (q r : ℕ) (m₀ : Message) (n : ℕ) (pc : LazyPrivate.PCache) (rc : Sampling.RCache)
    (hfresh : (pc (nonceCoord m₀) : Option HashOutput) = none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun h => mid q r m₀ (rhoOf h) 0 (n + 1) (pc.cacheQuery (nonceCoord m₀) h, rc)) ≤ pot q (r + 1) n (pc, rc) := by
  set S := Finset.univ.filter fun m : Message => (pc (nonceCoord m) : Option HashOutput) = none with hS
  set A' : Fin (2 ^ 31) → ℕ := fun i => ∑ m ∈ S.erase m₀, ∑ rho : Digest, hits rc rho m 0 i with hA'
  set D : Fin (2 ^ 31) → ℕ := fun i => ∑ rho : Digest, hits rc rho m₀ 0 i with hD
  have hsame : ∀ h m, m ≠ m₀ → ((pc.cacheQuery (nonceCoord m₀) h) (nonceCoord m) : Option HashOutput) =
      pc (nonceCoord m) := fun h m hm => QueryCache.cacheQuery_of_ne _ _ fun he => hm (nonceCoord_injective he)
  have hidx0 : honestIdx (pc, rc) m₀ = none := by unfold honestIdx; dsimp only; rw [hfresh]
  have hcnt : ∀ h i, cntEx (pc.cacheQuery (nonceCoord m₀) h, rc) m₀ i = cnt (pc, rc) i := by
    intro h i
    rw [cnt_split (pc, rc) m₀ i, hidx0]
    simp only [reduceCtorEq, if_false, add_zero]
    unfold cntEx
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro m _
    constructor
    · rintro ⟨hm, hh⟩
      refine ⟨hm, ?_⟩
      rw [← hh]; unfold honestIdx; dsimp only; rw [hsame h m hm]
    · rintro ⟨hm, hh⟩
      refine ⟨hm, ?_⟩
      rw [← hh]; unfold honestIdx; dsimp only; rw [hsame h m hm]
  have hpend : ∀ h i, pend (pc.cacheQuery (nonceCoord m₀) h, rc) i = A' i := by
    intro h i
    unfold pend
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hS]
    by_cases hm : m = m₀
    · subst hm; simp [QueryCache.cacheQuery_self]
    · simp [hm, hsame h m hm]
  have hpend0 : ∀ i, pend (pc, rc) i = A' i + D i := by
    intro i
    unfold pend
    rw [← Finset.sum_erase_add _ _ (show m₀ ∈ S by simp [hS, hfresh])]
  obtain ⟨F, hF⟩ : ∃ F : Digest → ℝ≥0∞, F = fun rho => if n + 1 ≤ q then ∑ i, (G 40 (cnt (pc, rc) i) r (A' i)
      (q - (n + 1)) + (pIdx + hits rc rho m₀ 0 i) * G 39 (cnt (pc, rc) i) r (A' i) (q - (n + 1))) else 0 := ⟨_, rfl⟩
  have hmid : (fun h => mid q r m₀ (rhoOf h) 0 (n + 1) (pc.cacheQuery (nonceCoord m₀) h, rc)) =
      fun h => F (rhoOf h) := by
    funext h
    rw [hF]
    unfold mid
    simp only [hcnt h, hpend h]
  rw [hmid]
  by_cases hq : n + 1 ≤ q
  · -- R6: the constant part is exact; only the hit count goes through the point-mass bound `expect_rho`.
    have hFg : (fun h : HashOutput => F (rhoOf h)) = fun h => (∑ i, (G 40 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) +
        pIdx * G 39 (cnt (pc, rc) i) r (A' i) (q - (n + 1)))) +
          ∑ i, (hits rc (rhoOf h) m₀ 0 i : ℝ≥0∞) * G 39 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) := by
      funext h
      rw [hF]
      simp only [hq, if_true, add_mul, ← add_assoc, Finset.sum_add_distrib]
    rw [hFg, expectedValue_add, expectedValue_const probFailure_eq_zero]
    refine (add_le_add le_rfl (expect_rho (fun rho => ∑ i, (hits rc rho m₀ 0 i : ℝ≥0∞) *
      G 39 (cnt (pc, rc) i) r (A' i) (q - (n + 1))))).trans ?_
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
    unfold pot
    rw [if_pos (by omega)]
    apply Finset.sum_le_sum
    intro i _
    calc G 40 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) + pIdx * G 39 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) +
          pNonce * ∑ rho : Digest, (hits rc rho m₀ 0 i : ℝ≥0∞) * G 39 (cnt (pc, rc) i) r (A' i) (q - (n + 1))
        = G 40 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) +
            (pIdx + (D i : ℝ≥0∞) * pNonce) * G 39 (cnt (pc, rc) i) r (A' i) (q - (n + 1)) := by
          rw [← Finset.sum_mul, hD]; push_cast; ring
      _ ≤ G 40 (cnt (pc, rc) i) (r + 1) (A' i + D i) (q - (n + 1)) := G_slot 39 _ r _ _ _
      _ ≤ G 40 (cnt (pc, rc) i) (r + 1) (pend (pc, rc) i) (q - n) := by
          rw [hpend0 i]; exact G_mono le_rfl le_rfl le_rfl (by omega)
  · refine (expect_rho F).trans ?_
    rw [hF]
    simp only [hq, if_false, Finset.sum_const_zero, mul_zero]
    exact bot_le


end QueryChargeResearch.Potential40

namespace QueryChargeResearch.Potential40
open ClaudeWCT
open ClaudeWCT.W9.T3.Security.FtsOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def payloadCont (cache : SigGolfCandidate.T3.Cache) (rho : Digest) :
    Option (BitVec 32 × HashOutput) → M (Option SharedForest.Signature)
  | none=>pure none
  | some (_,output)=>Bank.Paired.payAfterDigest cache rho output

def payloadForNonce (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (m : Message) : M (Option SharedForest.Signature) :=
  SharedForest.sharedDigestSearch rho m 0 lim >>= payloadCont cache rho

theorem signPayload_nonce (cache : SigGolfCandidate.T3.Cache) (m : Message) :
    SharedForest.signPayload cache m=(privateNonce m >>= fun rho=>payloadForNonce cache rho m) :=
  Bank.Paired.signPayload_factor cache m

theorem payloadForNonce_eq (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (m : Message) :
    payloadForNonce cache rho m=SharedForest.sharedDigestSearch rho m 0 lim >>= payloadCont cache rho:=rfl

theorem notNonce_public (input : HashInput) : NotNonce (.inl (.inr input)):=fun _ h=>by cases h

theorem payloadCont_notNonce (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (found : Option (BitVec 32 × HashOutput)) :
    AllQueriesSatisfy (payloadCont cache rho found) NotNonce := by
  rcases found with _|⟨_,output⟩
  · exact allQueriesSatisfy_pure _ _
  · exact notNonce_of_avoids _ (fun m=>Bank.Paired.payAvoids m cache rho output)

theorem search_notNonce (rho : Digest) (m : Message) (c f : Nat) :
    AllQueriesSatisfy (SharedForest.sharedDigestSearch rho m c f) NotNonce := by
  induction f generalizing c with
  | zero=>exact allQueriesSatisfy_pure _ _
  | succ f ih=>
    rw[digestSearch_succ_eq]
    refine SourceQueries.bind_allowed _ ?_ (fun a=>?_)
    · exact (allQueriesSatisfy_query_iff _ _).mpr (notNonce_public _)
    · split
      · exact allQueriesSatisfy_pure _ _
      · exact ih _

theorem payloadForNonce_notNonce (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (m : Message) :
    AllQueriesSatisfy (payloadForNonce cache rho m) NotNonce :=
  SourceQueries.bind_allowed _ (search_notNonce ..) (payloadCont_notNonce cache rho)
end QueryChargeResearch.Potential40

namespace QueryChargeResearch.Potential40
open ClaudeWCT
open ClaudeWCT.W9.T3.Security.FtsOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
/-- Signing one message uses at most one signing slot. -/
theorem payload_step (q r : ℕ) (cache : SigGolfCandidate.T3.Cache) (m : Message) (n : ℕ) (s : LazyPrivate.State)
    (hs : Settled s) :
    expectedValue (CountedPrivate.run (SharedForest.signPayload cache m) (n, s)) (fun res => pot q r res.2.1 res.2.2) ≤
        pot q (r + 1) n s ∧
      ∀ res ∈ support (CountedPrivate.run (SharedForest.signPayload cache m) (n, s)), Settled res.2.2 := by
  rcases s with ⟨pc, rc⟩
  rw [signPayload_nonce,
    show privateNonce m = (liftM (SigGolfCandidate.T3.Spec.query (.inr (nonceCoord m))) >>= fun h =>
      pure (rhoOf h)) from rfl, bind_assoc]
  simp only [pure_bind]
  rw [CountedPrivate.run_bind, run_query_private, bind_map_left, randomOracle.run_eq]
  split
  next h hk =>
    simp only [pure_bind]
    have := prog_step q r _ (payloadForNonce_notNonce cache (rhoOf h) m) (n + 1) (pc, rc) hs
    exact ⟨this.1.trans ((pot_mono_n q r n _).trans (pot_mono_r q r n _)), this.2⟩
  next hk =>
    simp only [bind_assoc, pure_bind, expectedValue_bind, mem_support_bind_iff]
    have hk' : (pc (nonceCoord m) : Option HashOutput) = none := hk
    have hstep : ∀ h : HashOutput, expectedValue (CountedPrivate.run
        (payloadForNonce cache (rhoOf h) m) (n + 1, (pc.cacheQuery (nonceCoord m) h, rc)))
          (fun res => pot q r res.2.1 res.2.2) ≤ mid q r m (rhoOf h) 0 (n + 1) (pc.cacheQuery (nonceCoord m) h, rc) ∧
        ∀ res ∈ support (CountedPrivate.run (payloadForNonce cache (rhoOf h) m)
          (n + 1, (pc.cacheQuery (nonceCoord m) h, rc))), Settled res.2.2 := by
      intro h
      have hex : SettledEx (pc.cacheQuery (nonceCoord m) h, rc) m := by
        intro m' h' hm' hh
        have : ((pc.cacheQuery (nonceCoord m) h) (nonceCoord m') : Option HashOutput) = pc (nonceCoord m') :=
          QueryCache.cacheQuery_of_ne _ _ fun he => hm' (nonceCoord_injective he)
        have hh' : (pc (nonceCoord m') : Option HashOutput) = some h' := by rw [← this]; exact hh
        exact hs m' h' hh'
      have hsr := search_step q r m h lim 0 (by simp) (n + 1) (pc.cacheQuery (nonceCoord m) h) rc
        (QueryCache.cacheQuery_self _ _ _) hex (fun c' hc' => absurd hc' (Nat.not_lt_zero _))
      rw [payloadForNonce_eq, CountedPrivate.run_bind]
      refine ⟨?_, ?_⟩
      · rw [expectedValue_bind]
        exact le_trans (expectedValue_mono_of_support fun res hres =>
          (prog_step q r _ (payloadCont_notNonce cache _ res.1) res.2.1 res.2.2 (hsr.2 res hres)).1) hsr.1
      · intro res hres
        rw [mem_support_bind_iff] at hres
        obtain ⟨mid', hmid', hres⟩ := hres
        exact (prog_step q r _ (payloadCont_notNonce cache _ mid'.1) mid'.2.1 mid'.2.2 (hsr.2 mid' hmid')).2 res hres
    refine ⟨?_, ?_⟩
    · change expectedValue ($ᵗ HashOutput : ProbComp HashOutput) _ ≤ _
      exact le_trans (expectedValue_mono _ fun h => (hstep h).1) (nonce_fresh_step q r m n pc rc hk')
    · rintro res ⟨h, _, hres⟩
      exact (hstep h).2 res hres

/-- A signing request (authenticated W9 signer) uses at most one signing slot. -/
theorem sign_step (q r : ℕ) (published : SigGolfCandidate.T3.Cache) (request : Request) (n : ℕ)
    (s : LazyPrivate.State) (hs : Settled s) :
    expectedValue (CountedPrivate.run (ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign published request) (n, s))
        (fun res => pot q r res.2.1 res.2.2) ≤ pot q (r + 1) n s ∧
      ∀ res ∈ support (CountedPrivate.run (ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign published request)
        (n, s)), Settled res.2.2 := by
  unfold ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign
  rw [CountedPrivate.run_bind]
  have hmac := prog_step q (r + 1) _ (notNonce_of_avoids _ fun m =>
    NonceFreshness.avoids_privateMac m request.cache.region) n s hs
  refine ⟨?_, ?_⟩
  · rw [expectedValue_bind]
    refine le_trans (expectedValue_mono_of_support fun res hres => ?_) hmac.1
    have hs' := hmac.2 res hres
    rcases Classical.em (request.cache = published) with hc | hc
    · rw [if_pos hc]; exact (payload_step q r _ _ res.2.1 res.2.2 hs').1
    · rw [if_neg hc]
      simp only [CountedPrivate.run_pure, expectedValue_pure]
      exact pot_mono_r q r _ _
  · intro res' hres'
    rw [mem_support_bind_iff] at hres'
    obtain ⟨res, hres, hres'⟩ := hres'
    have hs' := hmac.2 res hres
    rcases Classical.em (request.cache = published) with hc | hc
    · rw [if_pos hc] at hres'; exact (payload_step q r _ _ res.2.1 res.2.2 hs').2 res' hres'
    · rw [if_neg hc] at hres'
      simp only [CountedPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hres'
      subst hres'; exact hs'

/-! ### The adversary's interaction -/

/-- The potential after `len` of the `r` signing slots were used. -/
noncomputable def potL (q r len n : ℕ) (s : LazyPrivate.State) : ℝ≥0∞ :=
  if len ≤ r then pot q (r - len) n s else 0

theorem handler_run (x : SigGolfCandidate.T3.Spec.Domain) (st : CountedPrivate.State) :
    (CountedPrivate.handler x).run st = CountedPrivate.run (liftM (SigGolfCandidate.T3.Spec.query x)) st := rfl

/-- The whole interaction: each signing request uses one of `r` slots (the log records it). -/
theorem interaction_step {α : Type} (q : ℕ) (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction α) :
    ∀ (r n : ℕ) (s : LazyPrivate.State), Settled s →
      expectedValue (ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (fun input => CountedPrivate.handler (.inl input))
          (fun request => simulateQ CountedPrivate.handler
            (ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign published request)) program (n, s))
        (fun res => potL q r res.1.2.length res.2.1 res.2.2) ≤ pot q r n s ∧
      ∀ res ∈ support (ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run (fun input => CountedPrivate.handler (.inl input))
          (fun request => simulateQ CountedPrivate.handler
            (ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign published request)) program (n, s)),
        Settled res.2.2 := by
  induction program using OracleComp.inductionOn with
  | pure a =>
    intro r n s hs
    rw [ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_pure]
    simp only [expectedValue_pure, support_pure, Set.mem_singleton_iff, forall_eq, potL, List.length_nil,
      Nat.zero_le, if_true, Nat.sub_zero]
    exact ⟨le_rfl, hs⟩
  | query_bind x next ih =>
    intro r n s hs
    rcases x with input | request
    · rw [ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_public, handler_run]
      have hq := query_step q r (.inl input) (fun m h => by cases h) n s hs
      refine ⟨?_, ?_⟩
      · rw [expectedValue_bind]
        exact le_trans (expectedValue_mono_of_support fun res hres =>
          (ih res.1 r res.2.1 res.2.2 (hq.2 res hres)).1) hq.1
      · intro res hres
        rw [mem_support_bind_iff] at hres
        obtain ⟨mid', hmid', hres⟩ := hres
        exact (ih mid'.1 r mid'.2.1 mid'.2.2 (hq.2 mid' hmid')).2 res hres
    · rw [ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_request, CountedPrivate.run_simulate]
      refine ⟨?_, fun res hres => ?_⟩
      swap
      · rw [mem_support_bind_iff] at hres
        obtain ⟨mid', hmid', hres⟩ := hres
        rw [support_map] at hres
        obtain ⟨tail, htail, rfl⟩ := hres
        exact (ih mid'.1 r mid'.2.1 mid'.2.2 ((sign_step q r published request n s hs).2 mid' hmid')).2 tail htail
      rcases r with _ | r
      · have h0 : ∀ res : (α × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) × CountedPrivate.State,
            potL q 0 (res.1.2.length + 1) res.2.1 res.2.2 = 0 := fun res => by
          simp [potL]
        rw [expectedValue_bind]
        simp only [expectedValue_map, List.length_cons, h0]
        exact le_trans (expectedValue_le_of_support fun _ _ => (expectedValue_le_of_support fun _ _ => le_rfl)) bot_le
      · have hsign := sign_step q r published request n s hs
        rw [expectedValue_bind]
        simp only [expectedValue_map, List.length_cons]
        refine le_trans (expectedValue_mono_of_support fun res hres => ?_) hsign.1
        have hih := (ih res.1 r res.2.1 res.2.2 (hsign.2 res hres)).1
        refine le_of_eq_of_le ?_ hih
        congr 1
        funext tail
        simp only [potL, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-! ### The experiment -/

theorem allQ_mono' {α : Type} {P Q : SigGolfCandidate.T3.Spec.Domain → Prop} (h : ∀ x, P x → Q x) (p : M α)
    (hp : AllQueriesSatisfy p P) : AllQueriesSatisfy p Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind x next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp ⊢
    exact ⟨h x hp.1, fun u => ih u (hp.2 u)⟩

theorem keygen_notNonce : AllQueriesSatisfy SigGolfCandidate.T3.keygen NotNonce :=
  notNonce_of_avoids _ fun m => SigGolfCandidate.T3.Security.NonceFreshness.avoids_keygen m

theorem verdict_notNonce (pk : Digest) (result : Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP ×
    QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) :
    AllQueriesSatisfy (ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.verdict ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame.checker pk result)
      NotNonce :=
  allQ_mono' (fun x hx m he => by subst he; exact hx) _ (ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame.verdict_public pk result)

theorem verdict_win_len {Forgery : Type} (checker : ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.Checker Forgery) (pk : Digest)
    (result : Option Forgery × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (st : CountedPrivate.State)
    (res : Bool × CountedPrivate.State)
    (hres : res ∈ support (CountedPrivate.run (ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.verdict checker pk result) st))
    (hwin : res.1 = true) : result.2.length ≤ 2 ^ 32 := by
  unfold ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.verdict at hres
  split at hres
  · rw [CountedPrivate.run_bind, mem_support_bind_iff] at hres
    obtain ⟨mid', _, hres⟩ := hres
    rw [CountedPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1
  · rw [CountedPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres
    cases hwin

theorem settled_empty : Settled (∅, ∅) := fun m h hh => by cases hh

theorem one_le_pot {q r n : ℕ} {s : LazyPrivate.State} (hn : n ≤ q) (ho : Overflow s) : 1 ≤ pot q r n s := by
  obtain ⟨j, hj⟩ := ho
  unfold pot
  rw [if_pos hn]
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => G 40 (cnt s i) r (pend s i) (q - n))
    (fun _ _ => bot_le) (Finset.mem_univ j))
  refine le_trans ?_ (choose_le_G 40 (cnt s j) r (pend s j) (q - n))
  exact_mod_cast Nat.choose_pos hj


end QueryChargeResearch.Potential40

namespace QueryChargeResearch.ValidPotential40
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open QueryChargeResearch.Potential40
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable def goodPot (q r : Nat) (published : Cache)
    (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (n : Nat) (s : LazyPrivate.State) : ℝ≥0∞ :=
  if goodRequests published log ≤ r then pot q (r - goodRequests published log) n s else 0

theorem bad_request_step (q r : Nat) (published : Cache) (request : Request)
    (hc : request.cache ≠ published) (n : Nat) (s : LazyPrivate.State) (hs : Settled s) :
    expectedValue (CountedPrivate.run
      (ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign published request) (n,s))
      (fun res => pot q r res.2.1 res.2.2) ≤ pot q r n s := by
  unfold ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.authenticatedSign
  rw [CountedPrivate.run_bind, expectedValue_bind]
  simp only [hc, if_false, CountedPrivate.run_pure, expectedValue_pure]
  exact (prog_step q r _ (notNonce_of_avoids _ fun m =>
    NonceFreshness.avoids_privateMac m request.cache.region) n s hs).1

theorem good_cons_succ (q r : Nat) (published : Cache) (request : Request)
    (hc : request.cache = published) (sig : Option SigGolfCandidate.Research.SharedForest.Signature)
    (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (n : Nat) (s : LazyPrivate.State) :
    goodPot q (r+1) published (⟨request,sig⟩::log) n s = goodPot q r published log n s := by
  simp [goodPot, goodRequests, hc]

theorem good_cons_bad (q r : Nat) (published : Cache) (request : Request)
    (hc : request.cache ≠ published) (sig : Option SigGolfCandidate.Research.SharedForest.Signature)
    (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (n : Nat) (s : LazyPrivate.State) :
    goodPot q r published (⟨request,sig⟩::log) n s = goodPot q r published log n s := by
  simp [goodPot, goodRequests, hc]

theorem good_cons_zero (q : Nat) (published : Cache) (request : Request)
    (hc : request.cache = published) (sig : Option SigGolfCandidate.Research.SharedForest.Signature)
    (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) (n : Nat) (s : LazyPrivate.State) :
    goodPot q 0 published (⟨request,sig⟩::log) n s = 0 := by
  simp [goodPot, goodRequests, hc]

theorem interaction_good_step {α : Type} (q : Nat) (published : Cache)
    (program : OracleComp ClaudeWCT.W9.T3.Security.PairedOuter.LazyPrivate.Interaction α) :
    ∀ (r n : Nat) (s : LazyPrivate.State), Settled s →
      expectedValue (interactionRun published program (n,s))
        (fun res => goodPot q r published res.1.2 res.2.1 res.2.2) ≤ pot q r n s := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    intro r n s hs
    rw [interactionRun, ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_pure, expectedValue_pure]
    simp [goodPot, goodRequests]
  | query_bind x next ih =>
    intro r n s hs
    cases x with
    | inl input =>
      rw [interactionRun, ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_public, handler_run,
        expectedValue_bind]
      have hq := query_step q r (.inl input) (fun m h => by cases h) n s hs
      refine (expectedValue_mono_of_support fun res hres => ?_).trans hq.1
      exact ih res.1 r res.2.1 res.2.2 (hq.2 res hres)
    | inr request =>
      rw [interactionRun, ClaudeWCT.W9.T3.Security.PairedOuter.RequestHop.run_request,
        CountedPrivate.run_simulate, expectedValue_bind]
      simp only [expectedValue_map]
      by_cases hc : request.cache = published
      · cases r with
        | zero => simp only [good_cons_zero q published request hc]; simp [expectedValue]
        | succ r =>
          simp only [good_cons_succ q r published request hc]
          have hsign := sign_step q r published request n s hs
          refine (expectedValue_mono_of_support fun res hres => ?_).trans hsign.1
          exact ih res.1 r res.2.1 res.2.2 (hsign.2 res hres)
      · simp only [good_cons_bad q r published request hc]
        have hsign := sign_step q r published request n s hs
        refine (expectedValue_mono_of_support fun res hres => ?_).trans
          (bad_request_step q r published request hc n s hs)
        exact ih res.1 r res.2.1 res.2.2 (hsign.2 res hres)

#print axioms interaction_good_step
end QueryChargeResearch.ValidPotential40

namespace QueryChargeResearch.ValidPotential40
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open QueryChargeResearch.Potential40
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def slotCap (q : Nat) : Nat := min (2^32) (q / 65536)

/-- Slot-refined bound for the actual counted game, currently at the inherited overflow threshold51. -/
theorem counted_good_overflow_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
      ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.Counted.experiment
        ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame.checker adversary] ≤
      pot q (slotCap q) 0 (∅,∅) := by
  unfold ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.Counted.experiment
    ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.idealGame
  rw [← expectedValue_ite_one]
  have hkg := prog_step q (slotCap q) _ keygen_notNonce 0 (∅,∅) settled_empty
  rw [CountedPrivate.run_bind, expectedValue_bind]
  refine le_trans (expectedValue_mono_of_support fun kg hkg' => ?_) hkg.1
  have hs := hkg.2 kg hkg'
  rw [CountedPrivate.run_bind, expectedValue_bind, ← CountedPrivate.run_simulate,
    ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith_interpretation]
  have hint := interaction_good_step q kg.1.2 (adversary kg.1.1 kg.1.2) (slotCap q) kg.2.1 kg.2.2 hs
  refine le_trans (expectedValue_mono_of_support fun ir hir => ?_) hint
  have hset := (interaction_step q kg.1.2 (adversary kg.1.1 kg.1.2) 0 kg.2.1 kg.2.2 hs).2 ir hir
  by_cases hgood : goodRequests kg.1.2 ir.1.2 ≤ slotCap q
  · rw [goodPot, if_pos hgood]
    refine le_trans (expectedValue_mono _ fun res => ?_)
      (prog_step q (slotCap q - goodRequests kg.1.2 ir.1.2) _ (verdict_notNonce _ _) ir.2.1 ir.2.2 hset).1
    split_ifs with hE
    · exact one_le_pot hE.2.1 hE.2.2
    · exact bot_le
  · rw [goodPot, if_neg hgood]
    apply expectedValue_le_of_support
    intro res hres
    change (if res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 then (1 : ℝ≥0∞) else 0) ≤ 0
    have hn : ¬ (res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2) := by
      intro hE
      have hcount : ir.2.1 ≤ q := (CountedPrivate.count_monotone _ ir.2 res hres).trans hE.2.1
      have hlife := verdict_win_len _ _ _ _ _ hres hE.1
      have hslots := interaction_slots kg.1.2 (adversary kg.1.1 kg.1.2) kg.2 ir hir q hcount hlife
      exact hgood hslots
    rw [if_neg hn]

#print axioms counted_good_overflow_le
end QueryChargeResearch.ValidPotential40

set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace QueryDependentOverflow40

theorem constant_checked :
    (2 : ℝ)^31 * ((1 / (2 : ℝ)^47) + (1 / (2 : ℝ)^153)) *
      (2 + 1 / (2 : ℝ)^26)^39 / (Nat.factorial 40 : ℝ) ≤ 1 / (2 : ℝ)^136 := by
  norm_num

/-- Pure arithmetic research lemma. The charge assumption `r ≤ q / 2^16`
    still needs a proof for the relevant signing slots of the actual scheme. -/
theorem overflow_bound (q r p : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r) (hp0 : 0 ≤ p)
    (hcharge : r ≤ q / (2 : ℝ)^16) (hlife : r ≤ (2 : ℝ)^32)
    (hbudget : q ≤ (2 : ℝ)^127) (hp : p ≤ 1 / (2 : ℝ)^153) :
    (2 : ℝ)^31 * (r / (2 : ℝ)^31 + q*p)^40 / (Nat.factorial 40 : ℝ) ≤
      q / (2 : ℝ)^136 := by
  let μ := r / (2 : ℝ)^31 + q*p
  let B := 1 / (2 : ℝ)^47 + 1 / (2 : ℝ)^153
  let M := 2 + 1 / (2 : ℝ)^26
  have hμ0 : 0 ≤ μ := by dsimp [μ]; positivity
  have hμq : μ ≤ q*B := by
    calc μ ≤ (q / (2 : ℝ)^16) / (2 : ℝ)^31 + q*(1 / (2 : ℝ)^153) :=
        add_le_add (div_le_div_of_nonneg_right hcharge (by positivity))
          (mul_le_mul_of_nonneg_left hp hq)
      _ = q*B := by dsimp [B]; norm_num; ring
  have hμM : μ ≤ M := by
    have h1 : r / (2 : ℝ)^31 ≤ 2 := by
      have := div_le_div_of_nonneg_right hlife (show (0 : ℝ) ≤ 2^31 by positivity)
      norm_num at this ⊢; exact this
    have h2 : q*p ≤ 1 / (2 : ℝ)^26 := by
      calc q*p ≤ (2 : ℝ)^127*(1 / (2 : ℝ)^153) :=
          mul_le_mul hbudget hp hp0 (by positivity)
        _ = _ := by norm_num
    exact add_le_add h1 h2
  have hpow : μ^40 ≤ q*B*M^39 := by
    rw [pow_succ, mul_comm (μ^39) μ]
    exact mul_le_mul hμq (pow_le_pow_left₀ hμ0 hμM 39)
      (pow_nonneg hμ0 _) (by dsimp [B]; positivity)
  change (2 : ℝ)^31 * μ^40 / (Nat.factorial 40 : ℝ) ≤ q / (2 : ℝ)^136
  calc (2 : ℝ)^31 * μ^40 / (Nat.factorial 40 : ℝ) ≤
        (2 : ℝ)^31 * (q*B*M^39) / (Nat.factorial 40 : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = q*((2 : ℝ)^31*B*M^39 / (Nat.factorial 40 : ℝ)) := by ring
    _ ≤ q*(1 / (2 : ℝ)^136) := mul_le_mul_of_nonneg_left constant_checked hq
    _ = _ := by ring
#print axioms overflow_bound
end QueryDependentOverflow40

namespace QueryDependentOverflow40
open ENNReal ClaudeWCT.W9.T3.Security.FtsOverflow
set_option maxHeartbeats 0

theorem G40_bound (q r : Nat) (hcharge : r*65536 ≤ q) (hlife : r ≤ 2^32)
    (hbudget : q ≤ 2^127) :
    (2 : ℝ≥0∞)^31 * G 40 0 r 0 q ≤ (q : ℝ≥0∞) / 2^136 := by
  have hg : G 40 0 r 0 q ≤ (r*pIdx + q*pQuery)^40 / (Nat.factorial 40 : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
    simpa only [mul_comm] using G_initial_le 40 r q
  refine (mul_le_mul' (le_refl ((2 : ℝ≥0∞)^31)) hg).trans ?_
  have hpi : pIdx ≠ ∞ := by simp only [pIdx]; finiteness
  have hpq : pQuery ≠ ∞ := by simp only [pQuery, pIdx, pNonce]; finiteness
  have hrpi : (r : ℝ≥0∞)*pIdx ≠ ∞ := by finiteness
  have hqpq : (q : ℝ≥0∞)*pQuery ≠ ∞ := by finiteness
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_add hrpi hqpq, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have hp : pQuery.toReal ≤ 1 / (2 : ℝ)^153 := by
    norm_num [pQuery, pIdx, pNonce, SigGolfCandidate.T3.R,
      ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have hc : (r : ℝ) ≤ (q : ℝ) / (2 : ℝ)^16 := by
    have h : (r : ℝ)*65536 ≤ (q : ℝ) := by exact_mod_cast hcharge
    norm_num
    nlinarith
  have hl : (r : ℝ) ≤ (2 : ℝ)^32 := by exact_mod_cast hlife
  have hb : (q : ℝ) ≤ (2 : ℝ)^127 := by exact_mod_cast hbudget
  have h := overflow_bound (q : ℝ) (r : ℝ) pQuery.toReal (by positivity) (by positivity)
    ENNReal.toReal_nonneg hc hl hb hp
  simpa [pIdx, div_eq_mul_inv, mul_assoc] using h
#print axioms G40_bound
end QueryDependentOverflow40
namespace QueryChargeResearch.Potential40
open OracleComp OracleSpec ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.FtsOverflow
set_option maxHeartbeats 0

theorem pot_empty_eq (q r : Nat) : pot q r 0 (∅,∅) = (2 : ℝ≥0∞)^31 * G 40 0 r 0 q := by
  have hcnt : ∀ i, cnt (∅, ∅) i = 0 := by
    intro i
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _ h
    unfold honestIdx at h
    cases h
  have hpend : ∀ i, pend (∅, ∅) i = 0 := by
    intro i
    unfold pend hits
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro rho _
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ h
    cases h.2
  unfold pot
  rw [if_pos (Nat.zero_le _)]
  simp only [hcnt, hpend, Nat.sub_zero]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
end QueryChargeResearch.Potential40

namespace QueryChargeResearch.ValidPotential40
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open QueryChargeResearch.Potential40
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem counted_overflow40_query_bound (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q ≤ 2^127) :
    Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
      ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.Counted.experiment
        ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame.checker adversary] ≤ (q : ℝ≥0∞) / 2^136 := by
  have h := counted_good_overflow_le adversary q
  rw [pot_empty_eq] at h
  have hc : slotCap q * 65536 ≤ q :=
    (Nat.mul_le_mul_right 65536 (min_le_right (2^32) (q / 65536))).trans (Nat.div_mul_le_self q 65536)
  exact h.trans (QueryDependentOverflow40.G40_bound q (slotCap q) hc (min_le_left _ _) hq)

#print axioms counted_overflow40_query_bound
end QueryChargeResearch.ValidPotential40

namespace QueryChargeResearch.ValidPotential40
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open QueryChargeResearch.Potential40
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def overflowEvent (z : PairedOuter.PaddedGame.TraceResult) : Prop := Overflow z.2.2.base.source.2
theorem traced_ftsOverflow_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      (q : ℝ≥0∞) / 2^136 := by
  classical
  calc Pr[fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z | PairedOuter.PaddedGame.tracedExperiment adversary q hq]
      ≤ Pr[fun z : PairedOuter.PaddedGame.TraceResult =>
          (z.1, z.2.2.base.source).1 = true ∧ (z.1, z.2.2.base.source).2.1 ≤ q ∧
            Overflow (z.1, z.2.2.base.source).2.2 | PairedOuter.PaddedGame.tracedExperiment adversary q hq] :=
        ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.pmf_mono _ fun z hz => ⟨hz.1.1, hz.1.2.1, hz.2⟩
    _ = Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
          (liftM (PairedOuter.GameWith.Counted.experiment PairedOuter.PaddedGame.checker adversary) : PMF _)] := by
        rw [← ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.traced_counted adversary q hq, probEvent_map]
        rfl
    _ = Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
          PairedOuter.GameWith.Counted.experiment PairedOuter.PaddedGame.checker adversary] := by
        simp only [probEvent_eq_tsum_ite]
        rfl
    _ ≤ (q : ℝ≥0∞) / 2^136 := counted_overflow40_query_bound adversary q hq

/-- **FTS overflow bound** in `SeccLaw.completedExperiment` (the hook of `cleanWin_le_cases`, `small_route` and
`large_cert_bound`): at most `2^31 G(51; 2^32 signing slots, 2^127 queries) ≤ 2^31 (2 + 2^-32)^51 / 51! ≤ 2^-137`. -/
theorem fts_overflow_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ overflowEvent z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      (q : ℝ≥0∞) / 2^136 := by
  rw [PairedSeccLaw.completed_trace_event adversary q hq (fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z)]
  exact traced_ftsOverflow_le adversary q hq


#print axioms fts_overflow_le
end QueryChargeResearch.ValidPotential40

namespace QueryChargeResearch.Potential40
open OracleComp OracleSpec ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.FtsOverflow
set_option maxHeartbeats 0
noncomputable def lifetimeBound : ℝ≥0∞ := 2^31 * G 40 0 (2^32) 0 (2^127)
theorem lifetimeBound_le_real : lifetimeBound ≤ 2 ^ 31 * ((2 + (2 ^ 26)⁻¹) ^ 40 / (Nat.factorial 40 : ℝ≥0∞)) := by
  unfold lifetimeBound
  refine mul_le_mul' le_rfl ?_
  have hS : (((2 ^ 32 : ℕ) : ℝ≥0∞) * pIdx + ((2 ^ 127 : ℕ) : ℝ≥0∞) * pQuery) ≤ 2 + (2 ^ 26)⁻¹ := by
    have h1 : ((2 ^ 32 : ℕ) : ℝ≥0∞) * pIdx = 2 := by
      rw [pIdx, Nat.cast_pow, Nat.cast_ofNat, show (2 : ℝ≥0∞) ^ 32 = 2 * 2 ^ 31 by ring, mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by finiteness), mul_one]
    have hc : (2 ^ 256 + SigGolfCandidate.T3.R - 1) / SigGolfCandidate.T3.R =
        15557284462666655376466157833521152917877 := by
      norm_num [SigGolfCandidate.T3.R]
    have h2 : ((2 ^ 127 : ℕ) : ℝ≥0∞) * pQuery ≤ (2 ^ 26)⁻¹ := by
      rw [pQuery, pIdx, pNonce, hc, ← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
      simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
        ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
      norm_num
    rw [h1]
    exact add_le_add le_rfl h2
  have h := (G_initial_le 40 (2 ^ 32) (2 ^ 127)).trans (pow_le_pow_left' hS 40)
  rw [ENNReal.le_div_iff_mul_le (by left; exact_mod_cast (Nat.factorial_pos 40).ne') (by left; finiteness),
    mul_comm]
  exact h


theorem lifetimeBound_le : lifetimeBound ≤ (2^88)⁻¹ := by
  refine lifetimeBound_le_real.trans ?_
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num
#print axioms lifetimeBound_le
end QueryChargeResearch.Potential40

namespace QueryChargeResearch.ValidPotential40
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open QueryChargeResearch.Potential40
open ClaudeWCT.W9.T3.Security.FtsOverflow (G_mono)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 0

theorem counted_overflow40_lifetime_bound (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q ≤ 2^127) :
    Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
      ClaudeWCT.W9.T3.Security.PairedOuter.GameWith.Counted.experiment
        ClaudeWCT.W9.T3.Security.PairedOuter.PaddedGame.checker adversary] ≤ ((2 : ℝ≥0∞)^88)⁻¹ := by
  have h := counted_good_overflow_le adversary q
  rw [pot_empty_eq] at h
  exact h.trans ((mul_le_mul' le_rfl (G_mono le_rfl (min_le_left _ _) le_rfl hq)).trans lifetimeBound_le)
#print axioms counted_overflow40_lifetime_bound
end QueryChargeResearch.ValidPotential40

namespace QueryChargeResearch.Potential40
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem walk_eq_old (rc : Sampling.RCache) (rho : Digest) (m : Message) (c f : Nat) :
    walk rc rho m c f = ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.walk rc rho m c f := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    simp only [walk, ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.walk,
      digestKey, ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.digestKey]
    split <;> simp_all

theorem honestIdx_eq_old (s : LazyPrivate.State) (m : Message) :
    honestIdx s m = ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.honestIdx s m := by
  unfold honestIdx ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.honestIdx
  simp only [walk_eq_old]
  rfl
#print axioms honestIdx_eq_old
end QueryChargeResearch.Potential40

namespace QueryChargeResearch.ValidPotential40
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open QueryChargeResearch.Potential40
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem traced_ftsOverflow_lifetime (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      ((2 : ℝ≥0∞)^88)⁻¹ := by
  classical
  calc Pr[fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z | PairedOuter.PaddedGame.tracedExperiment adversary q hq]
      ≤ Pr[fun z : PairedOuter.PaddedGame.TraceResult =>
          (z.1, z.2.2.base.source).1 = true ∧ (z.1, z.2.2.base.source).2.1 ≤ q ∧
            Overflow (z.1, z.2.2.base.source).2.2 | PairedOuter.PaddedGame.tracedExperiment adversary q hq] :=
        ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.pmf_mono _ fun z hz => ⟨hz.1.1, hz.1.2.1, hz.2⟩
    _ = Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
          (liftM (PairedOuter.GameWith.Counted.experiment PairedOuter.PaddedGame.checker adversary) : PMF _)] := by
        rw [← ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.traced_counted adversary q hq, probEvent_map]
        rfl
    _ = Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
          PairedOuter.GameWith.Counted.experiment PairedOuter.PaddedGame.checker adversary] := by
        simp only [probEvent_eq_tsum_ite]
        rfl
    _ ≤ ((2 : ℝ≥0∞)^88)⁻¹ := counted_overflow40_lifetime_bound adversary q hq


theorem fts_overflow_lifetime (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2^127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ overflowEvent z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2 : ℝ≥0∞)^88)⁻¹ := by
  rw [PairedSeccLaw.completed_trace_event adversary q hq (fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z)]
  exact traced_ftsOverflow_lifetime adversary q hq

theorem ftsOverflow_answers (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127)
    (z : PairedOuter.PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support)
    (hno : ¬overflowEvent z.1) (i : Fin (2 ^ 31)) :
    (Finset.univ.filter fun m : Message =>
      (z.1.2.2.base.source.2.1 (nonceCoord m) : Option HashOutput) ≠ none ∧ ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.answerIdx z.2 m = some i).card ≤ 39 := by
  obtain ⟨htr, hagree⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  have hs := ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.traced_settled adversary q hq z.1 htr
  have hle : cnt z.1.2.2.base.source.2 i ≤ 39 := by
    by_contra h
    exact hno ⟨i, by omega⟩
  refine le_trans (le_of_eq ?_) hle
  unfold cnt
  simp only [honestIdx_eq_old]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro m _
  constructor
  · rintro ⟨hm, hi⟩
    rw [ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.honestIdx_eq_answerIdx z.2 _ hagree hs m hm]
    exact hi
  · intro hi
    have hm : (z.1.2.2.base.source.2.1 (nonceCoord m) : Option HashOutput) ≠ none := by
      intro hn
      unfold ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.honestIdx at hi
      change (z.1.2.2.base.source.2.1 (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.nonceCoord m) : Option HashOutput) = none at hn
      rw [hn] at hi
      cases hi
    exact ⟨hm, (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.honestIdx_eq_answerIdx z.2 _ hagree hs m hm) ▸ hi⟩


#print axioms fts_overflow_lifetime
#print axioms ftsOverflow_answers
end QueryChargeResearch.ValidPotential40

namespace QueryChargeResearch.ValidPotential40
open OracleComp OracleSpec OracleComp.EvalDist ENNReal SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open QueryChargeResearch.Potential40
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
/-- At most39distinct honest outputs at each index in the actual interaction log. -/
def LogNoOverflow (answers : Correctness.Answers) (log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests) : Prop :=
  ∀ j : Fin (2^31), ((WPair.Paired.loggedOutputs answers log).toFinset.filter
    fun out => ClaudeWCT.Bank.WCT.outIdx out = j).card ≤ 39
theorem logNoOverflow_of_not_ftsOverflow (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127)
    (z : PairedOuter.PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support)
    (hno : ¬overflowEvent z.1) (g : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (i : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)) (c : FirstHit.Recorded Bool)
    (hs : Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) g i c) :
    LogNoOverflow z.2 i.value.2 := by
  classical
  intro j
  obtain ⟨-, hagree⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  have hstate : c.state = z.1.2.2.base.source.2 := (congrArg FirstHit.Recorded.state hs.2.2.2).symm
  have hirun := FirstHit.recorded_support _ _ _ hs.2.1
  have hcrun := FirstHit.recorded_support _ _ _ hs.2.2.1
  have hext : SourceReplay.Extends i.state c.state := SourceReplay.run_extends _ i.state _ hcrun
  have hagree' : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer := by
    rw [hstate]; exact hagree
  -- every honest output of index j comes from a signed message counted by `ftsOverflow_answers`
  have hmsg : ∀ out ∈ (WPair.Paired.loggedOutputs z.2 i.value.2).toFinset.filter
      (fun out => ClaudeWCT.Bank.WCT.outIdx out = j), ∃ m : Message,
        (z.1.2.2.base.source.2.1 (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.nonceCoord m) : Option HashOutput) ≠ none ∧ ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.answerIdx z.2 m = some j ∧
        (evalWithAnswerFn z.2 (SigGolfCandidate.Research.SharedForest.sharedDigestSearch (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.rhoOf (z.2 (.inr (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.nonceCoord m)))) m 0 ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.lim)).map Prod.snd =
          some out := by
    intro out hout
    simp only [Finset.mem_filter, List.mem_toFinset] at hout
    obtain ⟨hmem, hidx⟩ := hout
    obtain ⟨entry, he, σ, hσ, hout⟩ := WPair.Paired.mem_loggedOutputs.mp hmem
    have hres := (Wots.PairedReference.logged_resolves g.value.2 (adversary g.value.1 g.value.2) g.state _ hirun entry he).mono hext
    rw [hσ] at hres
    obtain ⟨hn, hr⟩ := ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.resolves_sign_nonce c.state z.2 hagree' g.value.2 entry.1 σ hres
    refine ⟨entry.1.message, by rw [← hstate]; exact hn, ?_, ?_⟩
    · unfold ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.answerIdx
      have : (evalWithAnswerFn z.2 (SigGolfCandidate.Research.SharedForest.sharedDigestSearch (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.rhoOf (z.2 (.inr (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.nonceCoord entry.1.message))))
          entry.1.message 0 ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.lim)).map Prod.snd = some out := by
        rw [← hr]; exact hout
      cases hx : evalWithAnswerFn z.2 (SigGolfCandidate.Research.SharedForest.sharedDigestSearch (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.rhoOf (z.2 (.inr (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.nonceCoord entry.1.message))))
          entry.1.message 0 ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.lim) with
      | none => rw [hx] at this; cases this
      | some p =>
        rw [hx] at this
        simp only [Option.map_some, Option.some.injEq] at this ⊢
        rw [this]
        exact hidx
    · rw [← hr]; exact hout
  choose! f hf using hmsg
  have hcard := ftsOverflow_answers adversary q hq z hz hno j
  refine le_trans (Finset.card_le_card_of_injOn f ?_ ?_) hcard
  · intro out hout
    obtain ⟨h1, h2, _⟩ := hf out hout
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨h1, h2⟩
  · intro out hout out' hout' heq
    have e1 := (hf out hout).2.2
    have e2 := (hf out' hout').2.2
    rw [heq] at e1
    exact Option.some.inj (e1.symm.trans e2)

/-- Glue for case C: a clean win whose interaction log violates `LogNoOverflow` is an FTS overflow, so its
probability is at most `2^-137`. -/
theorem cleanWin_logOverflow_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1)
        g i c → LogNoOverflow z.2 i.value.2) | PairedSeccLaw.completedExperiment adversary q hq] ≤ (q : ℝ≥0∞) / 2^136 := by
  classical
  refine le_trans ?_ (fts_overflow_le adversary q hq)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support
  · by_cases hE : QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, Wots.PairedReference.GameSplit adversary
        (QueryRecorded.recordedTrace z.1) g i c → LogNoOverflow z.2 i.value.2)
    · have hF : QueryRecorded.CleanWin q z.1 ∧ overflowEvent z.1 := by
        refine ⟨hE.1, by_contra fun hno => hE.2 fun g i c hs => ?_⟩
        exact logNoOverflow_of_not_ftsOverflow adversary q hq z hz hno g i c hs
      rw [if_pos hE, if_pos hF]
    · simp only [hE, if_false]; exact bot_le
  · have hz0 : (PairedSeccLaw.completedExperiment adversary q hq) z = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hz
    simp only [PMF.probOutput_eq_apply, hz0, ite_self, le_refl]

theorem cleanWin_logOverflow_lifetime (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1)
        g i c → LogNoOverflow z.2 i.value.2) | PairedSeccLaw.completedExperiment adversary q hq] ≤ ((2 : ℝ≥0∞)^88)⁻¹ := by
  classical
  refine le_trans ?_ (fts_overflow_lifetime adversary q hq)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support
  · by_cases hE : QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, Wots.PairedReference.GameSplit adversary
        (QueryRecorded.recordedTrace z.1) g i c → LogNoOverflow z.2 i.value.2)
    · have hF : QueryRecorded.CleanWin q z.1 ∧ overflowEvent z.1 := by
        refine ⟨hE.1, by_contra fun hno => hE.2 fun g i c hs => ?_⟩
        exact logNoOverflow_of_not_ftsOverflow adversary q hq z hz hno g i c hs
      rw [if_pos hE, if_pos hF]
    · simp only [hE, if_false]; exact bot_le
  · have hz0 : (PairedSeccLaw.completedExperiment adversary q hq) z = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hz
    simp only [PMF.probOutput_eq_apply, hz0, ite_self, le_refl]

#print axioms logNoOverflow_of_not_ftsOverflow
#print axioms cleanWin_logOverflow_le
#print axioms cleanWin_logOverflow_lifetime

open ClaudeWCT.W9.T3.Security.FtsOverflow (G pQuery pIdx pNonce G_initial_le)

/-- Below256queries the charged signing-slot cap is zero, giving a much smaller overflow bound. -/
theorem G40_small (q : Nat) (hq : q < 256) :
    (2 : ℝ≥0∞)^31 * G 40 0 (slotCap q) 0 q ≤ (2^137)⁻¹ := by
  have hdiv : q / 65536 = 0 := Nat.div_eq_of_lt (hq.trans (by decide))
  have hcap : slotCap q = 0 := by simp [slotCap, hdiv]
  rw [hcap]
  have hp : (256 : ℝ≥0∞) * pQuery ≤ 1/32 := by
    rw [pQuery, pIdx, pNonce, ← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num [SigGolfCandidate.T3.R]
  have hmu : (q : ℝ≥0∞) * pQuery ≤ 1/32 :=
    (mul_le_mul' (by exact_mod_cast hq.le : (q : ℝ≥0∞) ≤ 256) le_rfl).trans hp
  have hf : (1 : ℝ≥0∞) ≤ Nat.factorial 40 := by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos 40))
  have hg : G 40 0 0 0 q ≤ (1/32 : ℝ≥0∞)^40 := by
    calc G 40 0 0 0 q = 1 * G 40 0 0 0 q := (one_mul _).symm
      _ ≤ (Nat.factorial 40 : ℝ≥0∞) * G 40 0 0 0 q := mul_le_mul' hf le_rfl
      _ ≤ ((q : ℝ≥0∞) * pQuery)^40 := by simpa [mul_comm] using G_initial_le 40 0 q
      _ ≤ (1/32 : ℝ≥0∞)^40 := pow_le_pow_left' hmu 40
  refine (mul_le_mul' le_rfl hg).trans ?_
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_div]

theorem counted_overflow40_small (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (hq : q < 256) :
    Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
      PairedOuter.GameWith.Counted.experiment PairedOuter.PaddedGame.checker adversary] ≤ (2^137)⁻¹ := by
  have h := counted_good_overflow_le adversary q
  rw [pot_empty_eq] at h
  exact h.trans (G40_small q hq)

theorem traced_ftsOverflow_small (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) (hsmall : q < 256) :
    Pr[fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      (2^137)⁻¹ := by
  classical
  calc Pr[fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z | PairedOuter.PaddedGame.tracedExperiment adversary q hq]
      ≤ Pr[fun z : PairedOuter.PaddedGame.TraceResult =>
          (z.1, z.2.2.base.source).1 = true ∧ (z.1, z.2.2.base.source).2.1 ≤ q ∧
            Overflow (z.1, z.2.2.base.source).2.2 | PairedOuter.PaddedGame.tracedExperiment adversary q hq] :=
        ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.pmf_mono _ fun z hz => ⟨hz.1.1, hz.1.2.1, hz.2⟩
    _ = Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
          (liftM (PairedOuter.GameWith.Counted.experiment PairedOuter.PaddedGame.checker adversary) : PMF _)] := by
        rw [← ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.traced_counted adversary q hq, probEvent_map]
        rfl
    _ = Pr[fun res => res.1 = true ∧ res.2.1 ≤ q ∧ Overflow res.2.2 |
          PairedOuter.GameWith.Counted.experiment PairedOuter.PaddedGame.checker adversary] := by
        simp only [probEvent_eq_tsum_ite]
        rfl
    _ ≤ (2^137)⁻¹ := counted_overflow40_small adversary q hsmall

/-- **FTS overflow bound** in `SeccLaw.completedExperiment` (the hook of `cleanWin_le_cases`, `small_route` and
`large_cert_bound`): at most `2^31 G(51; 2^32 signing slots, 2^127 queries) ≤ 2^31 (2 + 2^-32)^51 / 51! ≤ 2^-137`. -/
theorem fts_overflow_small (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) (hsmall : q < 256) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ overflowEvent z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      (2^137)⁻¹ := by
  rw [PairedSeccLaw.completed_trace_event adversary q hq (fun z => QueryRecorded.CleanWin q z ∧ overflowEvent z)]
  exact traced_ftsOverflow_small adversary q hq hsmall


theorem cleanWin_logOverflow_small (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : ℕ) (hq : q ≤ 2 ^ 127) (hsmall : q < 256) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, Wots.PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1)
        g i c → LogNoOverflow z.2 i.value.2) | PairedSeccLaw.completedExperiment adversary q hq] ≤ (2^137)⁻¹ := by
  classical
  refine le_trans ?_ (fts_overflow_small adversary q hq hsmall)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support
  · by_cases hE : QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, Wots.PairedReference.GameSplit adversary
        (QueryRecorded.recordedTrace z.1) g i c → LogNoOverflow z.2 i.value.2)
    · have hF : QueryRecorded.CleanWin q z.1 ∧ overflowEvent z.1 := by
        refine ⟨hE.1, by_contra fun hno => hE.2 fun g i c hs => ?_⟩
        exact logNoOverflow_of_not_ftsOverflow adversary q hq z hz hno g i c hs
      rw [if_pos hE, if_pos hF]
    · simp only [hE, if_false]; exact bot_le
  · have hz0 : (PairedSeccLaw.completedExperiment adversary q hq) z = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hz
    simp only [PMF.probOutput_eq_apply, hz0, ite_self, le_refl]
#print axioms G40_small
#print axioms cleanWin_logOverflow_small

/-- The39-output log guard implies the actual engine's overflow guard (also valid for the inherited50guard). -/
theorem LogNoOverflow.noOverflow {A : Correctness.Answers}
    {log : QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests} (h : LogNoOverflow A log) :
    ¬WPair.Paired.OverflowIn A log := by
  rintro ⟨i, hi⟩
  have hpos : 0 < ((WPair.Paired.loggedOutputs A log).toFinset.filter
      fun out => ClaudeWCT.WCT9.digestIndex out = i).card := by omega
  obtain ⟨out, hout⟩ := Finset.card_pos.mp hpos
  have he : ClaudeWCT.WCT9.digestIndex out = i := (Finset.mem_filter.mp hout).2
  have hib : i < 2^31 := he ▸ ClaudeWCT.WCT9.digestIndex_lt out
  have hj := h ⟨i, hib⟩
  have hp : ∀ out, ClaudeWCT.Bank.WCT.outIdx out = ⟨i, hib⟩ ↔ ClaudeWCT.WCT9.digestIndex out = i := fun out => Fin.ext_iff
  simp only [hp] at hj
  omega

theorem cleanWin_noOverflow_mono (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q ≤ 2^127) (B : ℝ≥0∞)
    (hb : Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬(∀ g i c, Wots.PairedReference.GameSplit adversary
      (QueryRecorded.recordedTrace z.1) g i c → LogNoOverflow z.2 i.value.2) |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ B) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ B := by
  refine le_trans (ClaudeWCT.W9.T3.Security.FtsOverflow.Paired.pmf_mono _ ?_) hb
  intro z hz
  refine ⟨hz.1, fun h => hz.2 ?_⟩
  intro g i c hs
  exact (h g i c hs).noOverflow

theorem cleanWin_noOverflow_query (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ (q : ℝ≥0∞)/2^136 :=
  cleanWin_noOverflow_mono adversary q hq _ (cleanWin_logOverflow_le adversary q hq)

theorem cleanWin_noOverflow_lifetime (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ (2^88)⁻¹ :=
  cleanWin_noOverflow_mono adversary q hq _ (cleanWin_logOverflow_lifetime adversary q hq)

theorem cleanWin_noOverflow_small (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP)
    (q : Nat) (hq : q ≤ 2^127) (hsmall : q < 256) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ (2^137)⁻¹ :=
  cleanWin_noOverflow_mono adversary q hq _ (cleanWin_logOverflow_small adversary q hq hsmall)

#print axioms cleanWin_noOverflow_query
#print axioms cleanWin_noOverflow_lifetime
#print axioms cleanWin_noOverflow_small
end QueryChargeResearch.ValidPotential40
