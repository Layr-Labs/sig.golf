import SigGolfCandidate.Merge112S0
set_option debug.skipKernelTC true
set_option linter.all false

/-! # Z5: the pre/post-marker split of the WOTS union bound (middle window)

`combined_cases_split`: a two-edge of chain `a` is a MarkerFirst, a ContactFirst, or happens with no marker of `a`
at all (then it is a pre-marker two-edge). The split bound mixes the installed union branch (weight
`v = 407137/500000`, every prefix query pays the contact rate) with the split branch (weight `w = 92863/500000`):
MarkerFirst pays `pre·1{marked} + 2·post` (`markerFirst_split_leF`, with the pre part charged to encoding queries
by `reference_pendingMarked_le`), ContactFirst and the pre-marker two-edge pay only pre-marker prefix queries
(`reference_contactFirst_pre_le`, `preContact_cost_leF`, `preTwoEdge_cost_leF`), TwoContacts pays every prefix
query. With `post ≤ 4488 y · EE` (`reference_marker_sum_le`) the class rate is θ = 397071/200000 on
`y ≤ 2163/10^6` (`split_middle_real`). -/

namespace ClaudeWCT.W9.T3.Security.Wots.Z5
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec ENNReal
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted (Combined ReferenceFailed EncodingMatch Structural TwoEdge
  TwoContacts MarkerFirstEvent ContactFirstEvent)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- A source chain with a two-edge and no marker. -/
def PreTwoEdgeEvent (s : RefSample) : Prop := ∃ a, WotsExtract.SourceChain7 a ∧ PreTwoEdge a s

theorem twoEdge_contact {T : Answers} {m : LeafAddr → WCT9.LayerMsg} {trace : List Entry} {a : ChainAddr}
    (h : CanonicalRef.TwoEdgeAt T m trace a) : CanonicalRef.ContactAt T m trace a := by
  obtain ⟨hd, start, middle, -, h2⟩ := h
  exact ⟨by omega, middle, h2⟩

theorem preTwoEdge_twoEdge {a : ChainAddr} {s : RefSample} (h : PreTwoEdge a s) :
    CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) s.trace a := by
  obtain ⟨k, ⟨hd, start, middle, h1, h2⟩, -⟩ := h
  have hsub : ∀ e ∈ s.trace.take k, e ∈ s.trace := fun e he => List.mem_of_mem_take he
  exact ⟨hd, start, middle, seenRowW_mono h1 hsub, seenRowW_mono h2 hsub⟩

/-- **Lemma D.** -/
theorem combined_cases_split (s : RefSample) (h : Combined s) :
    ReferenceFailed s ∨ EncodingMatch s ∨ Structural s ∨
      (TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s ∨ PreTwoEdgeEvent s) := by
  rcases CanonicalWeighted.combined_cases s h with hf | hm | hs | ⟨a, ha, hte⟩ | htc | hmf | hcf
  · exact Or.inl hf
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr (Or.inl hs))
  · by_cases hmk : CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) s.trace a
    · rcases CanonicalWeighted.markerContact_split s.answers s.trace a hmk (twoEdge_contact hte) with h1 | h1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, h1⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, h1⟩)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, s.trace.length, ?_, ?_⟩)))))
      · rwa [List.take_length]
      · rwa [List.take_length]
  · exact Or.inr (Or.inr (Or.inr (Or.inl htc)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmf))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcf)))))

/-- **The mixed split** (probability form). -/
theorem combined_split_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (v w : ENNReal)
    (hvw : v + w = 1) :
    Pr[Combined | PairedReference.referenceExperiment adversary q] ≤
      Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] +
      Pr[EncodingMatch | PairedReference.referenceExperiment adversary q] +
      Pr[Structural | PairedReference.referenceExperiment adversary q] +
      (v * Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s |
          PairedReference.referenceExperiment adversary q] +
        w * (Pr[TwoContacts | PairedReference.referenceExperiment adversary q] +
          Pr[MarkerFirstEvent | PairedReference.referenceExperiment adversary q] +
          Pr[ContactFirstEvent | PairedReference.referenceExperiment adversary q] +
          Pr[PreTwoEdgeEvent | PairedReference.referenceExperiment adversary q])) := by
  set law := PairedReference.referenceExperiment adversary q
  have hX : Pr[fun s => TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s ∨ PreTwoEdgeEvent s | law] ≤
      v * Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s | law] +
        w * (Pr[TwoContacts | law] + Pr[MarkerFirstEvent | law] + Pr[ContactFirstEvent | law] +
          Pr[PreTwoEdgeEvent | law]) := by
    set X := Pr[fun s => TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s ∨ PreTwoEdgeEvent s | law]
    have hU : X ≤ Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s | law] := by
      apply probEvent_mono''
      rintro s (h | h | h | ⟨a, ha, hp⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl ⟨a, ha, preTwoEdge_twoEdge hp⟩
    have hS : X ≤ Pr[TwoContacts | law] + Pr[MarkerFirstEvent | law] + Pr[ContactFirstEvent | law] +
        Pr[PreTwoEdgeEvent | law] := by
      refine (probEvent_or_le _ _ _).trans ?_
      rw [add_assoc, add_assoc]
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      exact probEvent_or_le _ _ _
    calc X = (v + w) * X := by rw [hvw, one_mul]
      _ = v * X + w * X := add_mul _ _ _
      _ ≤ _ := add_le_add (mul_le_mul' le_rfl hU) (mul_le_mul' le_rfl hS)
  refine (probEvent_mono'' combined_cases_split).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  rw [add_assoc, add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr

/-! ### Counting lemmas -/

theorem sum_sourceChains7_le (g : ChainAddr → ENNReal) :
    ∑ a ∈ Contacts.sourceChains7, g a ≤
      ∑ p : CanonGraph.LeafPos × Fin 58, if WotsExtract.SourceChain7 (Enc.chainAt p) then g (Enc.chainAt p) else 0 := by
  calc ∑ a ∈ Contacts.sourceChains7, g a
      = ∑ a ∈ Contacts.sourceChains7, ∑ p : CanonGraph.LeafPos × Fin 58, if Enc.chainAt p = a then g a else 0 := by
        refine Finset.sum_congr rfl fun a ha => ?_
        have ha' := (Contacts.mem_sourceChains7 a).mp ha
        obtain ⟨p0, rfl⟩ := Restart.exists_chainAt ha'
        rw [Finset.sum_eq_single p0 (fun p _ hp => if_neg (fun h => hp (Restart.chainOf_injective h))) (by simp)]
        simp
    _ = ∑ p : CanonGraph.LeafPos × Fin 58, ∑ a ∈ Contacts.sourceChains7, if Enc.chainAt p = a then g a else 0 :=
        Finset.sum_comm
    _ ≤ _ := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
        · rw [if_pos hs, Finset.sum_ite_eq]
          split_ifs <;> simp
        · rw [if_neg hs]
          refine le_of_eq (Finset.sum_eq_zero fun a ha => if_neg fun h => hs ?_)
          rw [h]; exact (Contacts.mem_sourceChains7 a).mp ha

theorem prefixCount_le_q (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (a : ChainAddr)
    (s : RefSample) (hs : s ∈ (PairedReference.referenceExperiment adversary q).support) : CanonicalRef.Normalized.prefixCount a s ≤ q :=
  (LeafView.prefixCount_le_length a s).trans (Core.ref_trace_length_le adversary q s hs)

/-- F1: pre and post prefix counts together are at most the prefix class. -/
theorem pre_post_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
      ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
        ((CanonicalRef.Normalized.prefixCount a s - preCount a s : ℕ) : ENNReal) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal) := by
  rw [← Finset.sum_add_distrib]
  simp only [← ENNReal.tsum_add, ← mul_add]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun s => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  have h : ∀ a ∈ Contacts.sourceChains7, ((preCount a s : ENNReal) + ((CanonicalRef.Normalized.prefixCount a s - preCount a s : ℕ) : ENNReal)) =
      (CanonicalRef.Normalized.prefixCount a s : ENNReal) := fun a _ => by
    rw [← Nat.cast_add, Nat.add_sub_cancel' (preCount_le_prefixCount a s)]
  rw [Finset.sum_congr rfl h]
  exact_mod_cast Contacts.prefixCount_sum_le s

theorem post_le_marked (a : ChainAddr) (s : RefSample) :
    CanonicalRef.Normalized.prefixCount a s - preCount a s = (CanonicalRef.Normalized.prefixCount a s - preCount a s) * (if Marked a s then 1 else 0) := by
  by_cases h : Marked a s
  · rw [if_pos h, Nat.mul_one]
  · rw [if_neg h, Nat.mul_zero, preCount_of_not_marked a s h, Nat.sub_self]

/-- F2: post-marker queries, at most `q` per marked chain. -/
theorem post_le_q_marked (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
        ((CanonicalRef.Normalized.prefixCount a s - preCount a s : ℕ) : ENNReal) ≤
      (q : ENNReal) * ∑ a ∈ Contacts.sourceChains7, Pr[Marked a | PairedReference.referenceExperiment adversary q] := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
  · rw [post_le_marked a s, PMF.probOutput_eq_apply]
    by_cases h : Marked a s
    · rw [if_pos h, if_pos h, Nat.mul_one, mul_comm (q : ENNReal)]
      refine mul_le_mul' le_rfl ?_
      exact_mod_cast (Nat.sub_le _ _).trans (prefixCount_le_q adversary q a s hs)
    · simp [if_neg h]
  · rw [(PMF.apply_eq_zero_iff _ s).mpr hs]; simp

/-- The expected number of chains contacted before their marker. -/
theorem expected_preContactCount (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑' s, PairedReference.referenceExperiment adversary q s * (preContactCount s : ENNReal) =
      ∑ a ∈ Contacts.sourceChains7, Pr[PreContact a | PairedReference.referenceExperiment adversary q] := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  unfold preContactCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : PreContact a s
  · rw [if_pos h, if_pos h, Nat.cast_one, mul_one]
  · rw [if_neg h, if_neg h, Nat.cast_zero, mul_zero]

theorem marked_iff (a : ChainAddr) (s : RefSample) :
    Marked a s ↔ CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) s.trace a :=
  Restart.markerAt_take_exists s.answers s.trace a

/-! ### Summed bounds -/

variable (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)

noncomputable def PreS : ENNReal :=
  ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal)
noncomputable def PostS : ENNReal :=
  ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
    ((CanonicalRef.Normalized.prefixCount a s - preCount a s : ℕ) : ENNReal)
noncomputable def PreM : ENNReal :=
  ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
    ((preCount a s : ENNReal) * (if Marked a s then 1 else 0))

theorem split_charge_eq (a : ChainAddr) (s : RefSample) :
    (((preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) : ℕ) : ENNReal) *
      (if Marked a s then 1 else 0)) =
    (preCount a s : ENNReal) * (if Marked a s then 1 else 0) +
      2 * ((CanonicalRef.Normalized.prefixCount a s - preCount a s : ℕ) : ENNReal) := by
  by_cases h : Marked a s
  · simp [h]
  · simp [h, preCount_of_not_marked a s h]

theorem mf_total (S : FamScheme)
    (A1 : ∀ a, WotsExtract.SourceChain7 a →
      (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a)
          s.answers s.trace a | PairedReference.referenceExperiment adversary q]) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s *
        (((preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) : ℕ) : ENNReal) *
          (if Marked a s then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a) :
    (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[MarkerFirstEvent | PairedReference.referenceExperiment adversary q]) ≤
      PreM adversary q + 2 * PostS adversary q + ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamTot.errTotF S adversary q := by
  have hU : Pr[MarkerFirstEvent | PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Contacts.sourceChains7, Pr[fun s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a)
        s.answers s.trace a | PairedReference.referenceExperiment adversary q] := by
    refine le_trans (le_of_eq ?_) (probEvent_exists_finset_le_sum Contacts.sourceChains7
      (PairedReference.referenceExperiment adversary q)
      (fun a s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a) s.answers s.trace a))
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Contacts.mem_sourceChains7 a).mp ha, h⟩
  calc (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[MarkerFirstEvent | PairedReference.referenceExperiment adversary q])
      ≤ ∑ a ∈ Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          Pr[fun s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a)
            s.answers s.trace a | PairedReference.referenceExperiment adversary q]) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        gcongr
    _ ≤ ∑ a ∈ Contacts.sourceChains7, (∑' s, PairedReference.referenceExperiment adversary q s *
          (((preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) : ℕ) : ENNReal) *
            (if Marked a s then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a) :=
        Finset.sum_le_sum fun a ha => A1 a ((Contacts.mem_sourceChains7 a).mp ha)
    _ = PreM adversary q + 2 * PostS adversary q +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamContacts.errTot7F S adversary q := by
        rw [Finset.sum_add_distrib, FamContacts.errTot7F, ← Finset.mul_sum]
        congr 1
        unfold PreM PostS
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun s => ?_
        rw [split_charge_eq]
        ring
    _ = _ := by rw [FamContacts.errTot7F_eq]

theorem pc_total (S : FamScheme)
    (A2 : ∀ a, WotsExtract.SourceChain7 a →
      (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreContact a | PairedReference.referenceExperiment adversary q] ≤
        (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a) :
    (1 - (q : ENNReal) / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (preContactCount s : ENNReal) ≤
      (2 / 2 ^ 128) * PreS adversary q + (1 + (2 / 2 ^ 128) * q) * FamTot.errTotF S adversary q := by
  rw [expected_preContactCount, Finset.mul_sum, ← FamContacts.errTot7F_eq, FamContacts.errTot7F, PreS,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a ha => A2 a ((Contacts.mem_sourceChains7 a).mp ha)

theorem pte_total (S : FamScheme)
    (A3 : ∀ a, WotsExtract.SourceChain7 a →
      (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreTwoEdge a | PairedReference.referenceExperiment adversary q] ≤
        twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
          (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a) :
    (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreTwoEdgeEvent | PairedReference.referenceExperiment adversary q] ≤
      twoEdgeRate q * PreS adversary q + (1 + twoEdgeRate q * q) * FamTot.errTotF S adversary q := by
  have hU : Pr[PreTwoEdgeEvent | PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Contacts.sourceChains7, Pr[PreTwoEdge a | PairedReference.referenceExperiment adversary q] := by
    refine le_trans (le_of_eq ?_) (probEvent_exists_finset_le_sum Contacts.sourceChains7
      (PairedReference.referenceExperiment adversary q) (fun a s => PreTwoEdge a s))
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (Contacts.mem_sourceChains7 a).mp ha, h⟩
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreTwoEdgeEvent | PairedReference.referenceExperiment adversary q]
      ≤ ∑ a ∈ Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[PreTwoEdge a | PairedReference.referenceExperiment adversary q] := by
        rw [← Finset.mul_sum]; gcongr
    _ ≤ _ := by
        rw [← FamContacts.errTot7F_eq, FamContacts.errTot7F, PreS, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun a ha => A3 a ((Contacts.mem_sourceChains7 a).mp ha)

theorem post_total :
    PostS adversary q ≤ (q : ENNReal) * ((4488 / (2 : ENNReal) ^ 128) *
      ∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal)) := by
  refine (post_le_q_marked adversary q).trans (mul_le_mul' le_rfl ?_)
  refine (sum_sourceChains7_le _).trans (le_trans (le_of_eq ?_) (CanonicalRef.reference_marker_sum_le adversary q))
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
  · rw [if_pos hs]
    apply pmf_probEvent_congr
    intro s _
    rw [marked_iff]
    exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  · rw [if_neg hs]
    symm
    rw [probEvent_eq_tsum_ite]
    exact ENNReal.tsum_eq_zero.mpr fun s => if_neg fun h => hs h.1

theorem preM_total
    (B1 : ∑ p : CanonGraph.LeafPos × Fin 58, ∑' s, PairedReference.referenceExperiment adversary q s *
        (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Marked (Enc.chainAt p) s
          then (preCount (Enc.chainAt p) s : ENNReal) else 0) ≤
      88 * ((q : ENNReal) / 2 ^ 128) *
        ∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal)) :
    PreM adversary q ≤ 88 * ((q : ENNReal) / 2 ^ 128) *
      ∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal) := by
  refine (sum_sourceChains7_le _).trans (le_trans (le_of_eq ?_) B1)
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
  · rw [if_pos hs]
    refine tsum_congr fun s => ?_
    by_cases hm : Marked (Enc.chainAt p) s
    · simp [hs, hm]
    · simp [hm]
  · rw [if_neg hs]
    symm
    exact ENNReal.tsum_eq_zero.mpr fun s => by simp [hs]

/-- The split's middle-window closing at cap 776 / gate 929 (y_b = 2163/10^6, v = 407137/500000). -/
theorem split_middle_real (y P E O pre post preM pc err pf pm ps pu ptc pmf pcf pte pr : ℝ)
    (hy0 : 0 ≤ y) (hy : y ≤ 2163 / 1000000)
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hpre : 0 ≤ pre) (hpost : 0 ≤ post) (herr0 : 0 ≤ err) (hpc0 : 0 ≤ pc)
    (hpreM0 : 0 ≤ preM)
    (hsum : pre + post ≤ P) (hpostE : post ≤ 4488 * y * E) (hpreM : preM ≤ 88 * y * E)
    (herr : err ≤ (261 / 200) * y ^ 2)
    (hpf : pf ≤ 1 / 2 ^ 139) (hpm : pm ≤ 7 / 4 * E) (hps : ps ≤ O + 1 / 2 ^ 142)
    (hpu0 : (1 - y) * pu ≤ 2 * P + (1 + 2 * y) * err)
    (hptc : ptc ≤ 4 * y / (1 - y) ^ 2 * P + (2 * y * (1 + 2 * y) / (1 - y) ^ 2 + (1 + 2 * y) / (1 - y)) * err)
    (hpmf0 : (1 - y) * pmf ≤ preM + 2 * post + (1 + 2 * y) * err)
    (hpc0' : (1 - y) * pc ≤ 2 * pre + (1 + 2 * y) * err)
    (hpcf : pcf ≤ 88 * y * pc)
    (hpte0 : (1 - y) * pte ≤ (3 / 2 + 4 * y + 2 * y ^ 2) * pre + (1 + (3 / 2 + 4 * y + 2 * y ^ 2) * y) * err)
    (hpr : pr ≤ pf + pm + ps + 407137 / 500000 * pu + 92863 / 500000 * (ptc + pmf + pcf + pte)) :
    pr ≤ 397071 / 200000 * (P + E) + O + 37 / 20 * y ^ 2 + (1 / 2 ^ 139 + 1 / 2 ^ 142) := by
  set r := 1 / (1 - y) with hr
  have h1y : 0 < 1 - y := by linarith
  have hpu : pu ≤ (2 * P + (1 + 2 * y) * err) / (1 - y) := by rw [le_div_iff₀ h1y]; linarith
  have hpmf : pmf ≤ (preM + 2 * post) / (1 - y) + (1 + 2 * y) / (1 - y) * err := by
    rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ h1y]; linarith
  have hpc : pc ≤ (2 * pre + (1 + 2 * y) * err) / (1 - y) := by rw [le_div_iff₀ h1y]; linarith
  have hpte : pte ≤ ((3 / 2 + 4 * y + 2 * y ^ 2) * pre + (1 + (3 / 2 + 4 * y + 2 * y ^ 2) * y) * err) / (1 - y) := by
    rw [le_div_iff₀ h1y]; linarith
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ h1y]; linarith
  have hrb : r ≤ 1000000 / 997837 := by
    rw [hr, div_le_div_iff₀ h1y (by norm_num)]; linarith
  have hr0 : 0 ≤ r := by linarith
  have hry : r * (1 - y) = 1 := by rw [hr]; field_simp
  -- rewrite the divisions through r
  have e1 : ∀ x : ℝ, x / (1 - y) = x * r := fun x => by rw [hr]; field_simp
  have e2 : ∀ x : ℝ, x / (1 - y) ^ 2 = x * r ^ 2 := fun x => by rw [hr]; field_simp
  simp only [e1, e2] at hpu hpmf hpc hpte hptc
  -- monotone bounds at y_b
  have hyb : y ≤ 2163 / 1000000 := hy
  have hrr : r ^ 2 ≤ (1000000 / 997837) ^ 2 := pow_le_pow_left₀ hr0 hrb 2
  have hyr : y * r ≤ 2163 / 1000000 * (1000000 / 997837) := mul_le_mul hy hrb hr0 (by norm_num)
  have hyrr : y * r ^ 2 ≤ 2163 / 1000000 * (1000000 / 997837) ^ 2 := mul_le_mul hy hrr (by positivity) (by norm_num)
  have hyy : y ^ 2 ≤ (2163 / 1000000) ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hyyr : y ^ 2 * r ≤ (2163 / 1000000) ^ 2 * (1000000 / 997837) := mul_le_mul hyy hrb hr0 (by positivity)
  have hyyrr : y ^ 2 * r ^ 2 ≤ (2163 / 1000000) ^ 2 * (1000000 / 997837) ^ 2 :=
    mul_le_mul hyy hrr (by positivity) (by positivity)
  have hyyyr : y ^ 3 * r ≤ (2163 / 1000000) ^ 3 * (1000000 / 997837) :=
    mul_le_mul (pow_le_pow_left₀ hy0 hy 3) hrb hr0 (by positivity)
  -- prefix-class coefficients, each times its (nonnegative) mass
  have cP : (2 * r) * P ≤ (2 * (1000000 / 997837)) * P := mul_le_mul_of_nonneg_right (by linarith) hP
  have cTC : (4 * y * r ^ 2) * P ≤ (4 * (2163 / 1000000 * (1000000 / 997837) ^ 2)) * P :=
    mul_le_mul_of_nonneg_right (by linarith) hP
  have cPre : ((176 * y + 3 / 2 + 4 * y + 2 * y ^ 2) * r) * pre ≤
      ((176 * (2163 / 1000000) + 3 / 2 + 4 * (2163 / 1000000) + 2 * (2163 / 1000000) ^ 2) * (1000000 / 997837)) * pre := by
    apply mul_le_mul_of_nonneg_right _ hpre
    linarith [hyr, hrb, hyyr]
  have cPost : (2 * r) * post ≤ (2 * (1000000 / 997837)) * post := mul_le_mul_of_nonneg_right (by linarith) hpost
  have cE : (88 * y * r) * E ≤ (88 * (2163 / 1000000 * (1000000 / 997837))) * E :=
    mul_le_mul_of_nonneg_right (by linarith) hE
  -- the error coefficient (per event for the split branch, once for the union branch)
  have cErr : (407137 / 500000 * ((1 + 2 * y) * r) + 92863 / 500000 * ((2 * y * (1 + 2 * y) * r ^ 2 + (1 + 2 * y) * r) +
      (1 + 2 * y) * r + 88 * y * ((1 + 2 * y) * r) + (1 + (3 / 2 + 4 * y + 2 * y ^ 2) * y) * r)) ≤ 1417 / 1000 := by
    have : (407137 / 500000 * ((1 + 2 * y) * r) + 92863 / 500000 * ((2 * y * (1 + 2 * y) * r ^ 2 + (1 + 2 * y) * r) +
      (1 + 2 * y) * r + 88 * y * ((1 + 2 * y) * r) + (1 + (3 / 2 + 4 * y + 2 * y ^ 2) * y) * r)) =
      r + (407137 / 500000 * 2 + 92863 / 500000 * (2 + 2 + 88 + 3 / 2)) * (y * r) +
      92863 / 500000 * (2 * (y * r ^ 2) + 4 * (y ^ 2 * r ^ 2) + 176 * (y ^ 2 * r) + 4 * (y ^ 2 * r) + 2 * (y ^ 3 * r))
      + 2 * (92863 / 500000) * r := by ring
    rw [this]
    norm_num at hrb hyr hyrr hyyrr hyyr hyyyr ⊢
    linarith
  have hErr : (407137 / 500000 * ((1 + 2 * y) * r) + 92863 / 500000 * ((2 * y * (1 + 2 * y) * r ^ 2 + (1 + 2 * y) * r) +
      (1 + 2 * y) * r + 88 * y * ((1 + 2 * y) * r) + (1 + (3 / 2 + 4 * y + 2 * y ^ 2) * y) * r)) * err ≤
      37 / 20 * y ^ 2 := by
    calc _ ≤ 1417 / 1000 * err := mul_le_mul_of_nonneg_right cErr herr0
      _ ≤ 1417 / 1000 * ((261 / 200) * y ^ 2) := by linarith
      _ ≤ _ := by nlinarith [sq_nonneg y]
  -- cone: pre ≤ P - post, post ≤ min(P, 4488 y_b E)
  have hpostE' : post ≤ 4488 * (2163 / 1000000) * E := by nlinarith
  have hpcf' : pcf ≤ 88 * y * ((2 * pre + (1 + 2 * y) * err) * r) := by
    calc pcf ≤ 88 * y * pc := hpcf
      _ ≤ _ := mul_le_mul_of_nonneg_left hpc (by positivity)
  -- assemble the linear bound
  have hmain : pr ≤ 7 / 4 * E + O + (1 / 2 ^ 139 + 1 / 2 ^ 142) +
      407137 / 500000 * ((2 * r) * P) +
      92863 / 500000 * ((4 * y * r ^ 2) * P + ((176 * y + 3 / 2 + 4 * y + 2 * y ^ 2) * r) * pre +
        (2 * r) * post + (88 * y * r) * E) +
      (407137 / 500000 * ((1 + 2 * y) * r) + 92863 / 500000 * ((2 * y * (1 + 2 * y) * r ^ 2 + (1 + 2 * y) * r) +
        (1 + 2 * y) * r + 88 * y * ((1 + 2 * y) * r) + (1 + (3 / 2 + 4 * y + 2 * y ^ 2) * y) * r)) * err := by
    have hmf' : (preM + 2 * post) * r ≤ (88 * y * E + 2 * post) * r := mul_le_mul_of_nonneg_right (by linarith) hr0
    linarith
  -- constants at y_b; then the case split on P against the post budget
  have hpre' : pre ≤ P - post := by linarith
  have hpostP : post ≤ P := by linarith
  have hk := mul_le_mul_of_nonneg_left hpre' (by norm_num : (0:ℝ) ≤
    (176 * (2163 / 1000000) + 3 / 2 + 4 * (2163 / 1000000) + 2 * (2163 / 1000000) ^ 2) * (1000000 / 997837))
  linarith


end ClaudeWCT.W9.T3.Security.Wots.Z5
