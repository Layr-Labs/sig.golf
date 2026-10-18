import SigGolfCandidate.T3.Secc.WotsEncodingContact
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingMarker
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsContacts
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportCount


namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem indicator_le_one (P : Prop) [Decidable P] : (if P then (1 : ENNReal) else 0) ≤ 1 := by
  split_ifs <;> simp

theorem contact_mono {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {trace trace' : List Entry} {a : ChainAddr}
    (h : CanonicalRef.ContactAt T messages trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    CanonicalRef.ContactAt T messages trace' a := by
  obtain ⟨hd, v, ans, hm, hv⟩ := h
  exact ⟨hd, v, ans, hsub _ hm, hv⟩
def ContactFirstAt (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T messages (trace.take k) a ∧ ¬MarkerAt T messages (trace.take k) a ∧ MarkerAt T messages trace a
def CFK (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Prop :=
  ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactFirstAt T messages trace (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)
noncomputable def contacts (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages trace (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)).card
theorem contacts_mono (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) {trace trace' : List Entry} (hsub : ∀ e ∈ trace, e ∈ trace') :
    contacts T messages trace ≤ contacts T messages trace' := by
  unfold contacts
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, contact_mono hp.2 hsub⟩
noncomputable def costL (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) : List Entry → List Entry → Nat
  | _, [] => 0
  | hist, e :: rest =>
      (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 93 * contacts T messages hist else 0) + costL T messages F (hist ++ [e]) rest
theorem costL_le (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) :
    ∀ (trace hist : List Entry), costL T messages F hist trace ≤ 93 * trace.length * contacts T messages (hist ++ trace) := by
  intro trace
  induction trace with
  | nil => intro hist; simp [costL]
  | cons e rest ih =>
      intro hist
      unfold costL
      have h1 : contacts T messages hist ≤ contacts T messages (hist ++ e :: rest) :=
        contacts_mono T messages (fun x hx => List.mem_append_left _ hx)
      have h2 := ih (hist ++ [e])
      rw [List.append_assoc, List.singleton_append] at h2
      have h3 : (if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F e.1 then 93 * contacts T messages hist else 0) ≤ 93 * contacts T messages hist := by
        split_ifs <;> omega
      rw [List.length_cons]
      nlinarith
theorem cfk_new {T : Answers} {messages : LeafAddr → WCT9.LayerMsg} {h : List Entry} {e : Entry} (hold : ¬ CFK T messages h) (hnew : CFK T messages (h ++ [e])) :
    ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧
      MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) e ∧ ¬ MarkerAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := by
  obtain ⟨p, hs, k, hc, hnm, hm⟩ := hnew
  by_cases hk : k ≤ h.length
  · rw [List.take_append_of_le_length hk] at hc hnm
    have hnot : ¬ MarkerAt T messages h (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := fun hmh => hold ⟨p, hs, k, hc, hnm, hmh⟩
    refine ⟨p, hs, contact_mono hc (fun x hx => List.mem_of_mem_take hx), ?_, hnot⟩
    obtain ⟨entry, hmem, hme⟩ := (markerAt_iff T messages _ _).mp hm
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact absurd ((markerAt_iff T messages _ _).mpr ⟨entry, hmem, hme⟩) hnot
    · exact hme
  · rw [List.take_of_length_le (by rw [List.length_append, List.length_singleton]; omega)] at hnm
    exact absurd hm hnm
noncomputable def cfCharge (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) : RefWorld.Domain → Nat
  | .inl (.inr x) => if Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x then 93 * contacts T messages h.toList else 0
  | _ => 0
theorem costL_step (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (h : FreeMonoid Entry) (input : RefWorld.Domain)
    (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    costL T messages F h.toList (Lazy.obs input answer * tail).toList =
      cfCharge T messages F h input + costL T messages F (h * Lazy.obs input answer).toList tail.toList := by
  rcases input with (n | x) | u
  · simp [Lazy.obs, cfCharge]
  · simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, costL, cfCharge]
  · simp [Lazy.obs, cfCharge]
theorem cfk_nil (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) : ¬ CFK T messages [] := by
  rintro ⟨p, -, k, -, -, hm⟩
  obtain ⟨entry, hmem, -⟩ := (markerAt_iff T messages _ _).mp hm
  simp at hmem
section Step
variable [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, Fintype k] [∀ k : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex, DecidableEq k]
theorem cf_step (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 93 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, T (.inl (.inr x)))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T input).run allowed] *
        (if CFK T messages (h * Lazy.obs input result.1).toList then (1 : ENNReal) else 0) ≤
      (if CFK T messages h.toList then (1 : ENNReal) else 0) + (2 ^ 128 : ENNReal)⁻¹ * (cfCharge T messages F h input : ENNReal) := by
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
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, cfCharge, if_pos hx]
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
          WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ ContactAt T messages h.toList (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p)
        calc _ = Pr[fun ans => CFK T messages (h.toList ++ [(x, ans)]) | cell (init e₀)] := by
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ans => ?_
              split_ifs <;> simp
          _ ≤ Pr[fun ans => ∃ p ∈ S, MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, ans) | cell (init e₀)] := by
              apply probEvent_mono
              intro ans _ hnew
              obtain ⟨p, hs, hcon, hme, -⟩ := cfk_new hold hnew
              refine ⟨p, ?_, hme⟩
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hs, hcon⟩
          _ ≤ ∑ p ∈ S, Pr[fun ans => MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, ans) | cell (init e₀)] :=
              probEvent_exists_finset_le_sum S _ _
          _ ≤ ∑ p ∈ S, 93 / (2 : ENNReal) ^ 128 := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hsrc : WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) := by
                simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
                exact hp.1
              rw [← hx₀]
              exact (probEvent_mono fun ans _ h => ⟨hsrc, h⟩).trans (hcell e₀ p)
          _ = (2 ^ 128 : ENNReal)⁻¹ * ((93 * contacts T messages h.toList : Nat) : ENNReal) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              unfold contacts
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
theorem lazy_cf_le {α : Type} (T : Answers) (messages : LeafAddr → WCT9.LayerMsg) (F : Set ClaudeWCT.W9.T3.Security.Wots.Enc.EncIndex) (init : F → Finset HashOutput)
    (hinit : ∀ e, (init e).Nonempty)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (ClaudeWCT.W9.T3.Security.Wots.Enc.encInput e.val, ans) |
        cell (init e)] ≤ 93 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain7 (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) ∧ MarkEntry T messages (ClaudeWCT.W9.T3.Security.Wots.Enc.chainAt p) (x, T (.inl (.inr x)))))
    (C : OracleComp RefWorld α) :
    ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T) (SphincsSecurity.QueryPause.traced Lazy.obs C)).run
        init] * (if CFK T messages z.1.2.toList then (1 : ENNReal) else 0) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
        (SphincsSecurity.QueryPause.traced Lazy.obs C)).run init] *
          (costL T messages F [] z.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_history_potential_le Lazy.obs (Lazy.lazyImpl ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F T)
    (fun h st => Lazy.Consistent ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init h st)
    (fun h st hc input result hr =>
      Lazy.consistent_step ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F ClaudeWCT.W9.T3.Security.Wots.Enc.encInput_injective T init h st hc input result hr)
    (fun C' h st hc => by
      rw [← Lazy.lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail (Lazy.aux T)
        (Lazy.aux_neverFail T) _ st (hc.nonempty ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F hinit)))
    (fun h _ => if CFK T messages h.toList then (1 : ENNReal) else 0) (2 ^ 128 : ENNReal)⁻¹
    (fun h tail => costL T messages F h.toList tail.toList) (cfCharge T messages F)
    (fun h => by simp [costL]) (fun h input answer tail => costL_step T messages F h input answer tail)
    (fun h st hc input => cf_step T messages F init hcell hother h st hc input)
    C 1 init (Lazy.consistent_one ClaudeWCT.W9.T3.Security.Wots.Enc.encInput F init)
  simp only [one_mul] at key
  rw [if_neg (by simpa using cfk_nil T messages), zero_add] at key
  simpa using key
end Step

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Congr
variable {T T' : Answers} {messages messages' : LeafAddr → WCT9.LayerMsg}
  (hm : ∀ leaf, WotsExtract.SourceLeaf7 leaf → messages' leaf=messages leaf)
  (hd : DecisionsAgree T T' messages)
  (hnon : ∀ query, SigGolfCandidate.T3.Security.Wots.Enc.NonEnc query → T' query=T query)
include hm hd hnon

theorem frontier_decisions (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.frontierValue T' messages' a=CanonicalRef.frontierValue T messages a := by
  have hs : WCT9.wotsSeed T' a.key.lay a.key.tree a.key.leaf a.chain =
      WCT9.wotsSeed T a.key.lay a.key.tree a.key.leaf a.chain :=
    ClaudeWCT.W9.T3.Security.Wots.Mask.wotsSeed_congr_cells _ _ _ fun p => hnon (.inr (.inl _)) trivial
  -- C3 (#866): the frontier is the chain of the current scheme.
  unfold CanonicalRef.frontierValue CanonicalRef.depth ClaudeWCT.W9.T3.Security.Wots.honestChainValueW
  rw [referenceDigits_decisions hm hd a.key ha.1,hs]
  exact (ClaudeWCT.W9.T3.Security.Wots.Enc.respects_chainW _ _ _ _ _ _ _).eval_eq hnon

theorem contact_decisions (trace : List Entry) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.ContactAt T' messages' trace a ↔ CanonicalRef.ContactAt T messages trace a := by
  unfold CanonicalRef.ContactAt
  rw [frontier_decisions hm hd hnon a ha]
  unfold CanonicalRef.depth
  rw [referenceDigits_decisions hm hd a.key ha.1]

omit hnon in
theorem marker_decisions (trace : List Entry) (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    CanonicalRef.MarkerAt T' messages' trace a ↔ CanonicalRef.MarkerAt T messages trace a := by
  rw [markerAt_iff,markerAt_iff]
  exact exists_congr fun e => and_congr_right fun _ => markEntry_decisions hm hd a ha e

theorem cfk_decisions (trace : List Entry) : CFK T' messages' trace ↔ CFK T messages trace := by
  unfold CFK ContactFirstAt
  refine exists_congr fun p => and_congr_right fun hp => exists_congr fun k => ?_
  rw [contact_decisions hm hd hnon _ _ hp,marker_decisions hm hd _ _ hp,
    marker_decisions hm hd _ _ hp]

theorem contacts_decisions (trace : List Entry) : contacts T' messages' trace=contacts T messages trace := by
  unfold contacts
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact and_congr_right fun hp => contact_decisions hm hd hnon trace _ hp
end Congr

noncomputable def cfInd (s : RefSample) : ENNReal := if CFK s.answers (sourceMessages s.answers) s.trace then 1 else 0
noncomputable def cfCost (s : RefSample) : ENNReal :=
  ((93*s.trace.length*contacts s.answers (sourceMessages s.answers) s.trace:Nat):ENNReal)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
open SigGolfCandidate.T3.Security.Wots.Enc
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cells_cf_le [∀ k : Set Enc.EncIndex, Fintype k] [∀ k : Set Enc.EncIndex, DecidableEq k]
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          cfInd (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)))))
          (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
        ∑' r, (liftM (PairedReference.offlineRun (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) adversary q) : PMF SeedResult) r *
          cfCost (mkSample (eagerAnswers U privateTable (Enc.ov (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells pub y)) r) := by
  have hleft := cell_transfer adversary q U hU privateTable pub cfInd
      (fun tr => if CFK (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr then (1:ENNReal) else 0)
      (fun y hy r => by
        unfold cfInd mkSample
        rw [propext (cfk_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)
          (overwrite_nonEnc privateTable pub _ y) _)])
  have hright := cell_transfer adversary q U hU privateTable pub cfCost
      (fun tr => ((93*tr.length*contacts (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub)) tr:Nat):ENNReal))
      (fun y hy r => by
        unfold cfCost mkSample
        rw [contacts_decisions (fun leaf _ => sourceMessages_overwrite privateTable pub _ y leaf)
          (overwrite_decisions hU privateTable pub _ (fun leaf _ => sourceMessages_fit _ leaf) y hy)
          (overwrite_nonEnc privateTable pub _ y) _])
  rw [hleft,hright]
  refine (lazy_cf_le (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells
    (cellInit (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))))
    (cellInit_nonempty _)
    (fun e p => markEntry_init_le _ _ _ e p)
    (fun x hx p => markEntry_noncell _ _ x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  have := costL_le (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))
    (cellKey (eagerAnswers U privateTable pub) (sourceMessages (eagerAnswers U privateTable pub))).cells z.1.2.toList []
  rw [List.nil_append] at this
  exact_mod_cast this

theorem reference_cfInd_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * cfInd s ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact reference_cells_le adversary q cfInd cfCost _
    (fun privateTable pub => cells_cf_le adversary q (PairedReference.referenceInputs adversary)
      Finset.subset_union_left privateTable pub)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem chainAt_injective : Function.Injective Enc.chainAt := by
  rintro ⟨⟨lay, tree, leaf⟩, i⟩ ⟨⟨lay', tree', leaf'⟩, i'⟩ h
  simp only [Enc.chainAt, Enc.leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hl⟩, hi⟩ := h
  have : tree = tree' := Fin.ext ht
  have : leaf = leaf' := Fin.ext hl
  have : i = i' := Fin.ext hi
  subst tree leaf i
  rfl
theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, Enc.chainAt p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3M.Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
theorem contacts_le_contactCount (s : RefSample) : contacts s.answers (sourceMessages s.answers) s.trace ≤ Normalized.Contacts.contactCount s := by
  unfold contacts Normalized.Contacts.contactCount
  refine Finset.card_le_card_of_injOn (fun p => Enc.chainAt p) ?_ (fun p _ p' _ h => chainAt_injective h)
  intro p hp
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
  rw [Finset.mem_coe, Finset.mem_filter, Normalized.Contacts.mem_sourceChains7]
  exact hp
theorem cfCost_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s ≤
      ((93 * q : Nat) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : PairedReference.referenceExperiment adversary q s = 0
  · simp [hs]
  · have hlen := PairedReference.reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    unfold cfCost
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left _ hlen) (contacts_le_contactCount s)
theorem reference_contactFirst_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        ∃ k, CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧ ¬CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) s.trace a | PairedReference.referenceExperiment adversary q] ≤
      93 * ((q : ENNReal) / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal) := by
  calc _ ≤ ∑' s, PairedReference.referenceExperiment adversary q s * cfInd s := by
        rw [probEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun s => ?_
        split_ifs with h
        · obtain ⟨a, ha, hcf⟩ := h
          obtain ⟨p, rfl⟩ := exists_chainAt ha
          rw [cfInd, if_pos ⟨p, ha, hcf⟩, mul_one, PMF.probOutput_eq_apply]
        · exact zero_le
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * ∑' s, PairedReference.referenceExperiment adversary q s * cfCost s := reference_cfInd_le adversary q
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (((93 * q : Nat) : ENNReal) *
          ∑' s, PairedReference.referenceExperiment adversary q s * (Normalized.Contacts.contactCount s : ENNReal)) :=
        mul_le_mul' le_rfl (cfCost_le adversary q)
    _ = _ := by
        push_cast
        rw [div_eq_mul_inv]
        ring

#print axioms reference_contactFirst_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Contact93
