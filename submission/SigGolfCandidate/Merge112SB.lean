import SigGolfCandidate.Merge112S0
set_option debug.skipKernelTC true
set_option linter.all false

/-! # Z5 (B): lazy-cell potentials of the split

* `reference_pendingMarked_le` (future-marker bound L2): over every source chain, the pre-marker prefix count of a
  marked chain, in expectation, is at most `88·q/2^128` per encoding query. Each encoding cell that makes a new
  marker of chain `a` (at most 88/2^128 per chain, `markEntry_init_le`) charges the chain-`a` prefix rows already in
  the trace; those rows sum to at most the trace length ≤ q over the chains of the leaf. Template:
  `CanonicalRef.Contact93.lazy_cf_le` / `reference_cfInd_le` on `traced_spmf_history_potential_le` (Merge103),
  with `*_decisions` invariance lemmas for the new weight.
* `reference_contactFirst_pre_le`: `Contact93.reference_contactFirst_le` with the contacts counted only before
  their chain's first marker (`cfk_new` already gives `¬MarkerAt h` at the contact). -/

/-! ## Contact-first with pre-marker contacts (helpers)

The lazy potential is `Contact93.CFK`; the charge of a fresh encoding cell is `88` per chain contacted and not yet
marked (`preContacts`); along a run this is bounded by the monotone count `everPre` of chains contacted before
their marker on some prefix, whose final value is at most `Z5.preContactCount`. -/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93.Z5B
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Source chains contacted and not yet marked in `trace`. -/
noncomputable def preContacts (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
      ContactAt T messages trace (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
      ¬MarkerAt T messages trace (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)).card

/-- Source chains contacted before their marker on some prefix of `trace`. -/
noncomputable def everPre (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
      ∃ k, ContactAt T messages (trace.take k) (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
        ¬MarkerAt T messages (trace.take k) (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)).card

theorem take_exists_append {P : List Entry → Prop} {tr : List Entry} (rest : List Entry)
    (h : ∃ k, P (tr.take k)) : ∃ k, P ((tr ++ rest).take k) := by
  obtain ⟨k, hk⟩ := h
  by_cases hle : k ≤ tr.length
  · exact ⟨k, by rwa [List.take_append_of_le_length hle]⟩
  · refine ⟨tr.length, ?_⟩
    rw [List.take_append_of_le_length le_rfl, List.take_length]
    rwa [List.take_of_length_le (by omega)] at hk

theorem everPre_mono (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (tr rest : List Entry) :
    everPre T messages tr ≤ everPre T messages (tr ++ rest) := by
  unfold everPre
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, take_exists_append (P := fun l => ContactAt T messages l (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
    ¬MarkerAt T messages l (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)) rest hp.2⟩

theorem preContacts_le_everPre (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (tr : List Entry) :
    preContacts T messages tr ≤ everPre T messages tr := by
  unfold preContacts everPre
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, tr.length, by rw [List.take_length]; exact hp.2⟩

noncomputable def costP (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) : List Entry → List Entry → Nat
  | _, [] => 0
  | hist, e :: rest =>
      (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 88 * preContacts T messages hist else 0) + costP T messages F (hist ++ [e]) rest

theorem costP_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) :
    ∀ (trace hist : List Entry), costP T messages F hist trace ≤ 88 * trace.length * everPre T messages (hist ++ trace) := by
  intro trace
  induction trace with
  | nil => intro hist; simp [costP]
  | cons e rest ih =>
      intro hist
      unfold costP
      have h1 : preContacts T messages hist ≤ everPre T messages (hist ++ e :: rest) :=
        (preContacts_le_everPre T messages hist).trans (everPre_mono T messages _ _)
      have h2 := ih (hist ++ [e])
      rw [List.append_assoc, List.singleton_append] at h2
      have h3 : (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 88 * preContacts T messages hist else 0) ≤ 88 * preContacts T messages hist := by
        split_ifs <;> omega
      rw [List.length_cons]
      nlinarith

noncomputable def cfpCharge (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) : RefWorld.Domain → Nat
  | .inl (.inr x) => if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x then 88 * preContacts T messages h.toList else 0
  | _ => 0

theorem costP_step (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) (input : RefWorld.Domain)
    (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    costP T messages F h.toList (Lazy.obs input answer * tail).toList =
      cfpCharge T messages F h input + costP T messages F (h * Lazy.obs input answer).toList tail.toList := by
  rcases input with (n | x) | u
  · simp [Lazy.obs, cfpCharge]
  · simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, costP, cfpCharge]
  · simp [Lazy.obs, cfpCharge]

section Step
variable [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, Fintype k] [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, DecidableEq k]
theorem cfp_step (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 88 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, T (.inl (.inr x)))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T input).run allowed] *
        (if CFK T messages (h * Lazy.obs input result.1).toList then (1 : ENNReal) else 0) ≤
      (if CFK T messages h.toList then (1 : ENNReal) else 0) + (2 ^ 128 : ENNReal)⁻¹ * (cfpCharge T messages F h input : ENNReal) := by
  classical
  by_cases hold : CFK T messages h.toList
  · rw [if_pos hold]
    refine le_trans ?_ le_self_add
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl (indicator_le_one _)).trans ?_
    exact Lazy.tsum_probOutput_mul_le_self _ _
  rw [if_neg hold, zero_add]
  rcases input with (n | x) | u
  · rw [Lazy.lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
  · by_cases hx : Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x
    · rw [Lazy.lazyImpl_cell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T x hx, tsum_probOutput_map_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, cfpCharge, if_pos hx]
      set e₀ := Lazy.cellOf ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x hx with he₀
      have hx₀ : ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e₀.val = x := Lazy.cellOf_input ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x hx
      by_cases hq : ∃ ans₀, (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        refine le_trans (le_of_eq ?_) zero_le
        apply ENNReal.tsum_eq_zero.mpr
        intro ans
        by_cases hne : ans = ans₀
        · subst hne
          rw [if_neg, mul_zero]
          intro hnew
          obtain ⟨p, -, -, hme, hnm⟩ := cfk_new hold hnew
          rw [← hx₀] at hme
          exact hnm ((markerAt_iff T messages _ _).mpr ⟨_, hans₀, hme⟩)
        · rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne), zero_mul]
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        let S := Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
          WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages h.toList (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
            ¬MarkerAt T messages h.toList (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)
        calc _ = Pr[fun ans => CFK T messages (h.toList ++ [(x, ans)]) | cell (init e₀)] := by
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ans => ?_
              split_ifs <;> simp
          _ ≤ Pr[fun ans => ∃ p ∈ S, MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, ans) | cell (init e₀)] := by
              apply probEvent_mono
              intro ans _ hnew
              obtain ⟨p, hs, hcon, hme, hnm⟩ := cfk_new hold hnew
              refine ⟨p, ?_, hme⟩
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hs, hcon, hnm⟩
          _ ≤ ∑ p ∈ S, Pr[fun ans => MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, ans) | cell (init e₀)] :=
              probEvent_exists_finset_le_sum S _ _
          _ ≤ ∑ p ∈ S, 88 / (2 : ENNReal) ^ 128 := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hsrc : WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := by
                simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
                exact hp.1
              rw [← hx₀]
              exact (probEvent_mono fun ans _ h => ⟨hsrc, h⟩).trans (hcell e₀ p)
          _ = (2 ^ 128 : ENNReal)⁻¹ * ((88 * preContacts T messages h.toList : Nat) : ENNReal) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              unfold preContacts
              push_cast
              rw [div_eq_mul_inv]
              ring
    · rw [Lazy.lazyImpl_other ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T x hx, tsum_probOutput_pure_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      rw [if_neg]
      · exact zero_le
      · intro hnew
        obtain ⟨p, hs, -, hme, -⟩ := cfk_new hold hnew
        exact hother x hx p ⟨hs, hme⟩
  · rw [Lazy.lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le

theorem lazy_cfp_le {α : Type} (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 88 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, T (.inl (.inr x)))))
    (C : OracleComp RefWorld α) :
    ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T) (SphincsSecurity.QueryPause.traced Lazy.obs C)).run
        init] * (if CFK T messages z.1.2.toList then (1 : ENNReal) else 0) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
        (SphincsSecurity.QueryPause.traced Lazy.obs C)).run init] *
          (costP T messages F [] z.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_history_potential_le Lazy.obs (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
    (fun h st => Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h st)
    (fun h st hc input result hr =>
      Lazy.consistent_step ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_injective T init h st hc input result hr)
    (fun C' h st hc => by
      rw [← Lazy.lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail (Lazy.aux T)
        (Lazy.aux_neverFail T) _ st (hc.nonempty ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F hinit)))
    (fun h _ => if CFK T messages h.toList then (1 : ENNReal) else 0) (2 ^ 128 : ENNReal)⁻¹
    (fun h tail => costP T messages F h.toList tail.toList) (cfpCharge T messages F)
    (fun h => by simp [costP]) (fun h input answer tail => costP_step T messages F h input answer tail)
    (fun h st hc input => cfp_step T messages F init hcell hother h st hc input)
    C 1 init (Lazy.consistent_one ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init)
  simp only [one_mul] at key
  rw [if_neg (by simpa using cfk_nil T messages), zero_add] at key
  simpa using key
end Step

section Congr
variable {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
  (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
  (hd : DecisionsAgree T T' messages)
  (hnon : ∀ query, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc query → T' query=T query)
include hm hd hnon

theorem everPre_decisions (trace : List Entry) : everPre T' messages' trace = everPre T messages trace := by
  unfold everPre
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun hp => exists_congr fun k => ?_
  rw [contact_decisions hm hd hnon _ _ hp, marker_decisions hm hd _ _ hp]
end Congr

noncomputable def cfpCost (s : RefSample) : ENNReal :=
  ((88 * s.trace.length * everPre s.answers (sourceMessages s.answers) s.trace : Nat) : ENNReal)

theorem cells_cfp_le [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          cfInd (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          cfpCost (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) := by
  have hleft := cell_transfer adversary q U hU privateTable pub cfInd
      (fun tr => if CFK (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr then (1:ENNReal) else 0)
      (fun y hy r => by
        unfold cfInd mkSample
        rw [propext (cfk_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)
          (overwrite_nonEnc privateTable pub _ y) _)])
  have hright := cell_transfer adversary q U hU privateTable pub cfpCost
      (fun tr => ((88*tr.length*everPre (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr:Nat):ENNReal))
      (fun y hy r => by
        unfold cfpCost mkSample
        rw [everPre_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)
          (overwrite_nonEnc privateTable pub _ y) _])
  rw [hleft,hright]
  refine (lazy_cfp_le (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells
    (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))))
    (cellInit_nonempty _)
    (fun e p => markEntry_init_le _ _ _ e p)
    (fun x hx p => markEntry_noncell _ _ x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  have := costP_le (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells z.1.2.toList []
  rw [List.nil_append] at this
  exact_mod_cast this

theorem reference_cfInd_pre_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * cfInd s ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * cfpCost s := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact reference_cells_le adversary q cfInd cfpCost _
    (fun privateTable pub => cells_cfp_le adversary q (PairedReference.referenceInputs adversary)
      Finset.subset_union_left privateTable pub)

theorem everPre_le_preContactCount (s : RefSample) :
    everPre s.answers (sourceMessages s.answers) s.trace ≤ Z5.preContactCount s := by
  unfold everPre Z5.preContactCount
  refine Finset.card_le_card_of_injOn (fun p => Enc.chainAt p) ?_ (fun p _ p' _ h => chainAt_injective h)
  intro p hp
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
  rw [Finset.mem_coe, Finset.mem_filter, Normalized.Contacts.mem_sourceChains7]
  exact hp

theorem cfpCost_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * cfpCost s ≤
      ((88 * q : Nat) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Z5.preContactCount s : ENNReal) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : PairedReference.referenceExperiment adversary q s = 0
  · simp [hs]
  · have hlen := PairedReference.reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    unfold cfpCost
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left _ hlen) (everPre_le_preContactCount s)

theorem contactFirst_pre_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        ∃ k, CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          ¬CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      88 * ((q : ENNReal) / 2 ^ 128) *
        ∑' s, PairedReference.referenceExperiment adversary q s * (Z5.preContactCount s : ENNReal) := by
  calc _ ≤ ∑' s, PairedReference.referenceExperiment adversary q s * cfInd s := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun s => ?_
        split_ifs with h
        · obtain ⟨a, ha, hcf⟩ := h
          obtain ⟨p, rfl⟩ := exists_chainAt ha
          rw [cfInd, if_pos ⟨p, ha, hcf⟩, mul_one, PMF.probOutput_eq_apply]
        · exact zero_le
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * cfpCost s := reference_cfInd_pre_le adversary q
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (((88 * q : Nat) : ENNReal) *
          ∑' s, PairedReference.referenceExperiment adversary q s * (Z5.preContactCount s : ENNReal)) :=
        mul_le_mul' le_rfl (cfpCost_le adversary q)
    _ = _ := by
        push_cast
        rw [div_eq_mul_inv]
        ring

/-! ## Future markers (helpers)

Lazy potential `pmW T h`: over source chains `p` marked in `h`, the chain-`p` rows of `h` before the first marker of
`p` (`ChainRow`: any chain row of `p`, which contains every prefix row). Rows do not change it; a fresh encoding
cell can newly mark chain `p` with probability ≤ 88/2^128 and then adds the chain-`p` rows of `h ++ [e]`; those
sum to at most `|h| + 1` over all chains, since a hash input is a chain row of at most one chain. The weight
depends on the answers only through the marker predicate, so it is invariant under the cell overwrite. -/

/-- `input` is a chain row of chain `a` (any step and value). -/
def ChainRow (a : ChainAddr) (input : HashInput) : Prop := ∃ step value, input = chainRowW a step value

noncomputable def rowsL (a : ChainAddr) (tr : List Entry) : Nat :=
  (tr.filter fun e => decide (ChainRow a e.1)).length

noncomputable def pmTerm (T : Answers) (tr : List Entry) (p : CanonGraph.LeafPos × Fin 58) : Nat :=
  if WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Normalized.Restart.MarkerAt T tr (Enc.chainAt p) then
    rowsL (Enc.chainAt p) (tr.take (Z5.stopIdx T tr (Enc.chainAt p)))
  else 0

noncomputable def pmW (T : Answers) (tr : List Entry) : Nat := ∑ p, pmTerm T tr p

theorem marker_append (T : Answers) (tr rest : List Entry) (a : ChainAddr)
    (h : Normalized.Restart.MarkerAt T tr a) : Normalized.Restart.MarkerAt T (tr ++ rest) a := by
  unfold Normalized.Restart.MarkerAt at h ⊢
  obtain ⟨entry, hmem, hme⟩ := (markerAt_iff _ _ _ _).mp h
  exact (markerAt_iff _ _ _ _).mpr ⟨entry, List.mem_append_left _ hmem, hme⟩

theorem marker_nil (T : Answers) (a : ChainAddr) : ¬Normalized.Restart.MarkerAt T [] a := by
  intro h
  unfold Normalized.Restart.MarkerAt at h
  obtain ⟨entry, hmem, -⟩ := (markerAt_iff _ _ _ _).mp h
  simp at hmem

theorem stopIdx_append (T : Answers) (tr rest : List Entry) (a : ChainAddr)
    (hm : Normalized.Restart.MarkerAt T tr a) :
    Z5.stopIdx T (tr ++ rest) a = Z5.stopIdx T tr a ∧ Z5.stopIdx T tr a ≤ tr.length := by
  have hex : ∃ k, Normalized.Restart.MarkerAt T (tr.take k) a := ⟨tr.length, by rwa [List.take_length]⟩
  have hle : Nat.find hex ≤ tr.length := Nat.find_min' hex (by rwa [List.take_length])
  have hex' : ∃ k, Normalized.Restart.MarkerAt T ((tr ++ rest).take k) a :=
    ⟨Nat.find hex, by rw [List.take_append_of_le_length hle]; exact Nat.find_spec hex⟩
  have h1 : Nat.find hex' ≤ Nat.find hex :=
    Nat.find_min' hex' (by rw [List.take_append_of_le_length hle]; exact Nat.find_spec hex)
  have h2 : Nat.find hex ≤ Nat.find hex' := by
    apply Nat.find_min' hex
    have := Nat.find_spec hex'
    rwa [List.take_append_of_le_length (h1.trans hle)] at this
  unfold Z5.stopIdx
  rw [dif_pos hex, dif_pos hex']
  exact ⟨le_antisymm h1 h2, hle⟩

/-- `Z5.stopIdx` for an arbitrary stop predicate. -/
noncomputable def gstop (P : List Entry → Prop) (tr : List Entry) : Nat :=
  if h : ∃ k, P (tr.take k) then Nat.find h else tr.length

theorem gstop_congr {P Q : List Entry → Prop} (h : ∀ l, P l ↔ Q l) (tr : List Entry) : gstop P tr = gstop Q tr := by
  have hPQ : P = Q := funext fun l => propext (h l)
  subst hPQ
  rfl

theorem stopIdx_congr {T T' : Answers} {a : ChainAddr}
    (h : ∀ tr, Normalized.Restart.MarkerAt T' tr a ↔ Normalized.Restart.MarkerAt T tr a) (tr : List Entry) :
    Z5.stopIdx T' tr a = Z5.stopIdx T tr a := by
  have e1 : Z5.stopIdx T' tr a = gstop (fun l => Normalized.Restart.MarkerAt T' l a) tr := rfl
  have e2 : Z5.stopIdx T tr a = gstop (fun l => Normalized.Restart.MarkerAt T l a) tr := rfl
  rw [e1, e2]
  exact gstop_congr h tr

theorem pmW_congr {T T' : Answers}
    (hmk : ∀ a, WotsExtract.SourceChain7 a → ∀ tr,
      Normalized.Restart.MarkerAt T' tr a ↔ Normalized.Restart.MarkerAt T tr a) (tr : List Entry) :
    pmW T' tr = pmW T tr := by
  unfold pmW
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold pmTerm
  by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
  · by_cases hm : Normalized.Restart.MarkerAt T tr (Enc.chainAt p)
    · rw [if_pos ⟨hs, (hmk _ hs tr).mpr hm⟩, if_pos ⟨hs, hm⟩, stopIdx_congr (hmk _ hs) tr]
    · rw [if_neg (fun h => hm ((hmk _ hs tr).mp h.2)), if_neg (fun h => hm h.2)]
  · rw [if_neg (fun h => hs h.1), if_neg (fun h => hs h.1)]

theorem pmW_nil (T : Answers) : pmW T [] = 0 := by
  unfold pmW
  refine Finset.sum_eq_zero fun p _ => ?_
  unfold pmTerm
  exact if_neg (fun h => marker_nil T _ h.2)

theorem rowsL_append_single (a : ChainAddr) (tr : List Entry) (e : Entry) :
    rowsL a (tr ++ [e]) = rowsL a tr + (if ChainRow a e.1 then 1 else 0) := by
  unfold rowsL
  by_cases h : ChainRow a e.1 <;> simp [List.filter_append, h]

theorem chainRow_unique {p p' : CanonGraph.LeafPos × Fin 58} {x : HashInput}
    (h : ChainRow (Enc.chainAt p) x) (h' : ChainRow (Enc.chainAt p') x) : p = p' := by
  obtain ⟨s, v, rfl⟩ := h
  obtain ⟨s', v', he⟩ := h'
  rw [chainRowW_eq, chainRowW_eq] at he
  obtain ⟨hh, -⟩ := chainInputW_fields he
  obtain ⟨hl, ht, hf, hi, -⟩ := chainHeader_fields hh
  rcases p with ⟨⟨lay, tree, leaf⟩, i⟩
  rcases p' with ⟨⟨lay', tree', leaf'⟩, i'⟩
  simp only [Enc.chainAt, Enc.leafOf] at hl ht hf hi
  have h1 : tree = tree' := by
    apply Fin.ext
    rwa [Nat.mod_eq_of_lt (lt_trans tree.isLt (by norm_num)),
      Nat.mod_eq_of_lt (lt_trans tree'.isLt (by norm_num))] at ht
  have h2 : leaf = leaf' := by
    apply Fin.ext
    rwa [Nat.mod_eq_of_lt (lt_trans leaf.isLt (by norm_num)),
      Nat.mod_eq_of_lt (lt_trans leaf'.isLt (by norm_num))] at hf
  have h3 : i = i' := by
    apply Fin.ext
    rwa [Nat.mod_eq_of_lt (lt_trans i.isLt (by norm_num)),
      Nat.mod_eq_of_lt (lt_trans i'.isLt (by norm_num))] at hi
  subst hl h1 h2 h3
  rfl

theorem chainRow_sum_le_one (x : HashInput) :
    ∑ p : CanonGraph.LeafPos × Fin 58, (if ChainRow (Enc.chainAt p) x then 1 else 0) ≤ 1 := by
  rw [← Finset.card_filter]
  apply Finset.card_le_one.mpr
  intro p hp p' hp'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
  exact chainRow_unique hp hp'

theorem rows_sum_le (tr : List Entry) :
    ∑ p : CanonGraph.LeafPos × Fin 58, rowsL (Enc.chainAt p) tr ≤ tr.length := by
  induction tr with
  | nil => simp [rowsL]
  | cons e rest ih =>
      have hcons : ∀ p : CanonGraph.LeafPos × Fin 58, rowsL (Enc.chainAt p) (e :: rest) =
          (if ChainRow (Enc.chainAt p) e.1 then 1 else 0) + rowsL (Enc.chainAt p) rest := by
        intro p
        unfold rowsL
        by_cases h : ChainRow (Enc.chainAt p) e.1 <;> simp [List.filter_cons, h, Nat.add_comm]
      simp only [hcons, Finset.sum_add_distrib, List.length_cons]
      have := chainRow_sum_le_one e.1
      omega

theorem pmTerm_append (T : Answers) (h : List Entry) (e : Entry) (p : CanonGraph.LeafPos × Fin 58) :
    pmTerm T (h ++ [e]) p ≤ pmTerm T h p +
      (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧ ¬Normalized.Restart.MarkerAt T h (Enc.chainAt p) ∧
          MarkEntry T (sourceMessages T) (Enc.chainAt p) e then rowsL (Enc.chainAt p) (h ++ [e]) else 0) := by
  unfold pmTerm
  by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
  · by_cases hm : Normalized.Restart.MarkerAt T h (Enc.chainAt p)
    · obtain ⟨hst, hle⟩ := stopIdx_append T h [e] _ hm
      rw [if_pos (show WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Normalized.Restart.MarkerAt T (h ++ [e]) (Enc.chainAt p)
          from ⟨hs, marker_append T h [e] _ hm⟩),
        if_pos (show WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Normalized.Restart.MarkerAt T h (Enc.chainAt p) from ⟨hs, hm⟩),
        hst, List.take_append_of_le_length hle]
      exact Nat.le_add_right _ _
    · rw [if_neg (show ¬(WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Normalized.Restart.MarkerAt T h (Enc.chainAt p))
          from fun h' => hm h'.2), zero_add]
      by_cases hme : MarkEntry T (sourceMessages T) (Enc.chainAt p) e
      · rw [if_pos (show WotsExtract.SourceChain7 (Enc.chainAt p) ∧ ¬Normalized.Restart.MarkerAt T h (Enc.chainAt p) ∧
            MarkEntry T (sourceMessages T) (Enc.chainAt p) e from ⟨hs, hm, hme⟩)]
        split_ifs
        · exact ((List.take_sublist _ _).filter _).length_le
        · exact Nat.zero_le _
      · have hm' : ¬Normalized.Restart.MarkerAt T (h ++ [e]) (Enc.chainAt p) := by
          intro hm'
          unfold Normalized.Restart.MarkerAt at hm hm'
          obtain ⟨entry, hmem, hme'⟩ := (markerAt_iff _ _ _ _).mp hm'
          rw [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | rfl
          · exact hm ((markerAt_iff _ _ _ _).mpr ⟨entry, hmem, hme'⟩)
          · exact hme hme'
        rw [if_neg (show ¬(WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Normalized.Restart.MarkerAt T (h ++ [e]) (Enc.chainAt p))
          from fun h' => hm' h'.2)]
        exact Nat.zero_le _
  · rw [if_neg (show ¬(WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Normalized.Restart.MarkerAt T (h ++ [e]) (Enc.chainAt p))
      from fun h' => hs h'.1)]
    exact Nat.zero_le _

theorem pmW_append (T : Answers) (h : List Entry) (e : Entry) :
    pmW T (h ++ [e]) ≤ pmW T h + ∑ p : CanonGraph.LeafPos × Fin 58,
      (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧ ¬Normalized.Restart.MarkerAt T h (Enc.chainAt p) ∧
          MarkEntry T (sourceMessages T) (Enc.chainAt p) e then rowsL (Enc.chainAt p) (h ++ [e]) else 0) := by
  unfold pmW
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun p _ => pmTerm_append T h e p

theorem tsum_potential_le {ι β : Type} [Fintype ι] (μ : SPMF β) (W : ENNReal) (f : β → ENNReal)
    (c : ι → ENNReal) (E : ι → β → Prop) (hpt : ∀ b, f b ≤ W + ∑ i, c i * (if E i b then 1 else 0)) :
    ∑' b, Pr[= b | μ] * f b ≤ W + ∑ i, c i * Pr[E i | μ] := by
  calc ∑' b, Pr[= b | μ] * f b
        ≤ ∑' b, (Pr[= b | μ] * W + ∑ i, c i * (if E i b then Pr[= b | μ] else 0)) := by
          refine ENNReal.tsum_le_tsum fun b => (mul_le_mul' le_rfl (hpt b)).trans (le_of_eq ?_)
          rw [mul_add, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> simp [mul_comm]
    _ = (∑' b, Pr[= b | μ] * W) + ∑ i, c i * Pr[E i | μ] := by
          rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.tsum_mul_left, probEvent_eq_tsum_ite]
    _ ≤ _ := add_le_add (Lazy.tsum_probOutput_mul_le_self _ _) le_rfl

theorem tsum_potential_nat {ι β : Type} [Fintype ι] (μ : SPMF β) (W : ℕ) (f : β → ℕ) (c : ι → ℕ)
    (g : ι → β → ℕ) (E : ι → β → Prop) (hpt : ∀ b, f b ≤ W + ∑ i, g i b) (hgc : ∀ i b, g i b ≤ c i)
    (hg : ∀ i b, ¬E i b → g i b = 0) (r : ENNReal)
    (hr : ∀ i, Pr[E i | μ] ≤ r) (n : ℕ) (hn : ∑ i, c i ≤ n) :
    ∑' b, Pr[= b | μ] * (f b : ENNReal) ≤ (W : ENNReal) + r * n := by
  have hpt' : ∀ b, (f b : ENNReal) ≤ (W : ENNReal) + ∑ i, (c i : ENNReal) * (if E i b then 1 else 0) := by
    intro b
    refine (Nat.cast_le.mpr (hpt b)).trans ?_
    push_cast
    refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
    by_cases hE : E i b
    · rw [if_pos hE, mul_one]
      exact Nat.cast_le.mpr (hgc i b)
    · rw [hg i b hE, if_neg hE]
      simp
  refine (tsum_potential_le μ (W : ENNReal) (fun b => (f b : ENNReal)) (fun i => (c i : ENNReal)) E hpt').trans
    (add_le_add le_rfl ?_)
  calc ∑ i, (c i : ENNReal) * Pr[E i | μ] ≤ ∑ i, (c i : ENNReal) * r :=
        Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (hr i)
    _ = r * ∑ i, (c i : ENNReal) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ ≤ r * n := mul_le_mul' le_rfl (by rw [← Nat.cast_sum]; exact Nat.cast_le.mpr hn)

noncomputable def pmCharge (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) : RefWorld.Domain → Nat
  | .inl (.inr x) => if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x then 88 * (h.toList.length + 1) else 0
  | _ => 0

noncomputable def pmCost (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) : List Entry → List Entry → Nat
  | _, [] => 0
  | hist, e :: rest =>
      (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 88 * (hist.length + 1) else 0) + pmCost F (hist ++ [e]) rest

theorem pmCost_step (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) (input : RefWorld.Domain)
    (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    pmCost F h.toList (Lazy.obs input answer * tail).toList =
      pmCharge F h input + pmCost F (h * Lazy.obs input answer).toList tail.toList := by
  rcases input with (n | x) | u
  · simp [Lazy.obs, pmCharge]
  · simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, pmCost, pmCharge]
  · simp [Lazy.obs, pmCharge]

section Step
variable [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, Fintype k] [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, DecidableEq k]

theorem pmCost_le (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) :
    ∀ (trace hist : List Entry), pmCost F hist trace ≤
      88 * (hist ++ trace).length * Lazy.cellCount ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F trace := by
  intro trace
  induction trace with
  | nil => intro hist; simp [pmCost]
  | cons e rest ih =>
      intro hist
      unfold pmCost
      have h2 := ih (hist ++ [e])
      rw [List.append_assoc, List.singleton_append] at h2
      have hL : hist.length + 1 ≤ (hist ++ e :: rest).length := by simp
      have hcc : Lazy.cellCount ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F (e :: rest) =
          (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 1 else 0) +
            Lazy.cellCount ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F rest := by
        unfold Lazy.cellCount
        by_cases hx : Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 <;>
          simp [List.filter_cons, hx, Nat.add_comm]
      rw [hcc]
      split_ifs <;> nlinarith

theorem pm_step (T : Answers) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkEntry T (sourceMessages T) (Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 88 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T (sourceMessages T) (Enc.chainAt p) (x, T (.inl (.inr x)))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput)
    (hc : Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T input).run allowed] *
        (pmW T (h * Lazy.obs input result.1).toList : ENNReal) ≤
      (pmW T h.toList : ENNReal) + (2 ^ 128 : ENNReal)⁻¹ * (pmCharge F h input : ENNReal) := by
  classical
  rcases input with (n | x) | u
  · rw [Lazy.lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one]
    exact (Lazy.tsum_probOutput_mul_le_self _ _).trans le_self_add
  · by_cases hx : Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x
    · rw [Lazy.lazyImpl_cell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T x hx, tsum_probOutput_map_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, pmCharge, if_pos hx]
      set e₀ := Lazy.cellOf ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x hx with he₀
      have hx₀ : ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e₀.val = x :=
        Lazy.cellOf_input ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x hx
      by_cases hq : ∃ ans₀, (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        refine le_trans ?_ le_self_add
        refine le_trans (ENNReal.tsum_le_tsum fun ans => ?_)
          (Lazy.tsum_probOutput_mul_le_self (cell {ans₀}) (pmW T h.toList : ENNReal))
        by_cases hne : ans = ans₀
        · subst hne
          refine mul_le_mul' le_rfl ?_
          have h1 := pmW_append T h.toList (x, ans)
          rw [Finset.sum_eq_zero (fun p _ => if_neg (fun hcond => hcond.2.1 (by
            unfold Normalized.Restart.MarkerAt
            exact (markerAt_iff _ _ _ _).mpr ⟨_, hans₀, by rw [hx₀]; exact hcond.2.2⟩))), add_zero] at h1
          exact_mod_cast h1
        · rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne), zero_mul, zero_mul]
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        let c : CanonGraph.LeafPos × Fin 58 → Nat := fun p =>
          rowsL (Enc.chainAt p) h.toList + (if ChainRow (Enc.chainAt p) x then 1 else 0)
        have hsum : ∑ p, c p ≤ h.toList.length + 1 := by
          simp only [c, Finset.sum_add_distrib]
          have := rows_sum_le h.toList
          have := chainRow_sum_le_one x
          omega
        have hpt : ∀ ans, pmW T (h.toList ++ [(x, ans)]) ≤ pmW T h.toList +
            ∑ p : CanonGraph.LeafPos × Fin 58, (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧
              MarkEntry T (sourceMessages T) (Enc.chainAt p) (x, ans) then c p else 0) := by
          intro ans
          have h1 := pmW_append T h.toList (x, ans)
          have h2 : ∑ p : CanonGraph.LeafPos × Fin 58, (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧
                ¬Normalized.Restart.MarkerAt T h.toList (Enc.chainAt p) ∧
                MarkEntry T (sourceMessages T) (Enc.chainAt p) (x, ans) then rowsL (Enc.chainAt p) (h.toList ++ [(x, ans)]) else 0) ≤
              ∑ p : CanonGraph.LeafPos × Fin 58, (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧
                MarkEntry T (sourceMessages T) (Enc.chainAt p) (x, ans) then c p else 0) := by
            refine Finset.sum_le_sum fun p _ => ?_
            split_ifs with ha hb hb
            · exact le_of_eq (rowsL_append_single _ _ _)
            · exact absurd ⟨ha.1, ha.2.2⟩ hb
            · exact Nat.zero_le _
            · exact le_rfl
          exact h1.trans (Nat.add_le_add_left h2 _)
        have hr : ∀ p : CanonGraph.LeafPos × Fin 58, Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
            MarkEntry T (sourceMessages T) (Enc.chainAt p) (x, ans) | cell (init e₀)] ≤ 88 / (2 : ENNReal) ^ 128 := by
          intro p
          rw [← hx₀]
          exact hcell e₀ p
        have key := tsum_potential_nat (cell (init e₀)) (pmW T h.toList) (fun ans => pmW T (h.toList ++ [(x, ans)])) c
          (fun p ans => if WotsExtract.SourceChain7 (Enc.chainAt p) ∧
              MarkEntry T (sourceMessages T) (Enc.chainAt p) (x, ans) then c p else 0)
          (fun p ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T (sourceMessages T) (Enc.chainAt p) (x, ans))
          hpt (fun p ans => by split_ifs <;> simp) (fun p ans hE => if_neg hE)
          (88 / (2 : ENNReal) ^ 128) hr (h.toList.length + 1) hsum
        refine key.trans (le_of_eq ?_)
        push_cast
        rw [div_eq_mul_inv]
        ring
    · rw [Lazy.lazyImpl_other ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T x hx, tsum_probOutput_pure_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      refine le_trans ?_ le_self_add
      have h1 := pmW_append T h.toList (x, T (.inl (.inr x)))
      rw [Finset.sum_eq_zero (fun p _ => if_neg (fun hcond => hother x hx p ⟨hcond.1, hcond.2.2⟩)), add_zero] at h1
      exact_mod_cast h1
  · rw [Lazy.lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one]
    exact (Lazy.tsum_probOutput_mul_le_self _ _).trans le_self_add

theorem lazy_pm_le {α : Type} (T : Answers) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkEntry T (sourceMessages T) (Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 88 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkEntry T (sourceMessages T) (Enc.chainAt p) (x, T (.inl (.inr x)))))
    (C : OracleComp RefWorld α) :
    ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T) (SphincsSecurity.QueryPause.traced Lazy.obs C)).run
        init] * (pmW T z.1.2.toList : ENNReal) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
        (SphincsSecurity.QueryPause.traced Lazy.obs C)).run init] *
          (pmCost F [] z.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_history_potential_le Lazy.obs (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
    (fun h st => Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h st)
    (fun h st hc input result hr =>
      Lazy.consistent_step ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_injective T init h st hc input result hr)
    (fun C' h st hc => by
      rw [← Lazy.lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail (Lazy.aux T)
        (Lazy.aux_neverFail T) _ st (hc.nonempty ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F hinit)))
    (fun h _ => (pmW T h.toList : ENNReal)) (2 ^ 128 : ENNReal)⁻¹
    (fun h tail => pmCost F h.toList tail.toList) (pmCharge F)
    (fun h => by simp [pmCost]) (fun h input answer tail => pmCost_step F h input answer tail)
    (fun h st hc input => pm_step T F init hcell hother h st hc input)
    C 1 init (Lazy.consistent_one ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init)
  simp only [one_mul, FreeMonoid.toList_one, pmW_nil, Nat.cast_zero, zero_add] at key
  exact key
end Step

noncomputable def pmS (s : RefSample) : ENNReal := (pmW s.answers s.trace : ENNReal)

noncomputable def pmFinal (s : RefSample) : ENNReal :=
  ((88 * s.trace.length * ClaudeWCT.W9.T3.Security.Wots.encodingCount s : Nat) : ENNReal)

theorem cells_pm_le [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          pmS (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          pmFinal (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) := by
  have hleft := cell_transfer adversary q U hU privateTable pub pmS
      (fun tr => (pmW (eagerAnswers U privateTable pub) tr : ENNReal))
      (fun y hy r => by
        unfold pmS mkSample
        rw [pmW_congr (fun a ha tr => marker_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy) tr a ha)])
  have hright := cell_transfer adversary q U hU privateTable pub pmFinal
      (fun tr => ((88 * tr.length * (tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y hy r => rfl)
  rw [hleft, hright]
  refine (lazy_pm_le (eagerAnswers U privateTable pub)
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells
    (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))))
    (cellInit_nonempty _)
    (fun e p => markEntry_init_le _ _ _ e p)
    (fun x hx p => markEntry_noncell _ _ x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  have h1 := pmCost_le (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells
    z.1.2.toList []
  rw [List.nil_append] at h1
  have h2 := Enc.cellCount_le_encoding
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells z.1.2.toList
  exact_mod_cast h1.trans (Nat.mul_le_mul_left _ h2)

theorem reference_pm_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * pmS s ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * pmFinal s := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact reference_cells_le adversary q pmS pmFinal _
    (fun privateTable pub => cells_pm_le adversary q (PairedReference.referenceInputs adversary)
      Finset.subset_union_left privateTable pub)

theorem pmFinal_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * pmFinal s ≤
      ((88 * q : Nat) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : PairedReference.referenceExperiment adversary q s = 0
  · simp [hs]
  · have hlen := PairedReference.reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    unfold pmFinal
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 88 hlen)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93.Z5B

namespace ClaudeWCT.W9.T3.Security.Wots.Z5
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec ENNReal
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The pre-marker prefix count of a marked source chain is at most its potential term. -/
theorem preCount_le_pmTerm (s : RefSample) (p : CanonGraph.LeafPos × Fin 58)
    (hs : WotsExtract.SourceChain7 (Enc.chainAt p)) (hm : Marked (Enc.chainAt p) s) :
    preCount (Enc.chainAt p) s ≤ CanonicalRef.Contact93.Z5B.pmTerm s.answers s.trace p := by
  have hmk : Restart.MarkerAt s.answers s.trace (Enc.chainAt p) := by
    obtain ⟨k, hk⟩ := hm
    unfold Restart.MarkerAt at hk ⊢
    obtain ⟨entry, hmem, hme⟩ := (CanonicalRef.markerAt_iff _ _ _ _).mp hk
    exact (CanonicalRef.markerAt_iff _ _ _ _).mpr ⟨entry, List.mem_of_mem_take hmem, hme⟩
  unfold CanonicalRef.Contact93.Z5B.pmTerm preCount preTrace CanonicalRef.Contact93.Z5B.rowsL
  rw [if_pos ⟨hs, hmk⟩]
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro e he
  simp only [decide_eq_true_eq] at he ⊢
  obtain ⟨step, value, -, hx⟩ := he
  exact ⟨step, value, hx⟩

/-- **L2: future markers.** -/
theorem reference_pendingMarked_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, ∑' s, PairedReference.referenceExperiment adversary q s *
        (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Marked (Enc.chainAt p) s
          then (preCount (Enc.chainAt p) s : ENNReal) else 0) ≤
      88 * ((q : ENNReal) / 2 ^ 128) *
        ∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal) := by
  calc _ = ∑' s, PairedReference.referenceExperiment adversary q s *
        ∑ p : CanonGraph.LeafPos × Fin 58, (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Marked (Enc.chainAt p) s
          then (preCount (Enc.chainAt p) s : ENNReal) else 0) := by
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine tsum_congr fun s => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑' s, PairedReference.referenceExperiment adversary q s * CanonicalRef.Contact93.Z5B.pmS s := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul' le_rfl ?_
        unfold CanonicalRef.Contact93.Z5B.pmS CanonicalRef.Contact93.Z5B.pmW
        push_cast
        refine Finset.sum_le_sum fun p _ => ?_
        split_ifs with h
        · exact_mod_cast preCount_le_pmTerm s p h.1 h.2
        · exact zero_le
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s *
          CanonicalRef.Contact93.Z5B.pmFinal s := CanonicalRef.Contact93.Z5B.reference_pm_le adversary q
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (((88 * q : Nat) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s *
          (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal)) :=
        mul_le_mul' le_rfl (CanonicalRef.Contact93.Z5B.pmFinal_le adversary q)
    _ = _ := by
        push_cast
        rw [div_eq_mul_inv]
        ring

/-- **ContactFirst, pre-marker contacts only.** -/
theorem reference_contactFirst_pre_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        ∃ k, CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          ¬CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      88 * ((q : ENNReal) / 2 ^ 128) *
        ∑' s, PairedReference.referenceExperiment adversary q s * (preContactCount s : ENNReal) :=
  CanonicalRef.Contact93.Z5B.contactFirst_pre_le adversary q

end ClaudeWCT.W9.T3.Security.Wots.Z5
