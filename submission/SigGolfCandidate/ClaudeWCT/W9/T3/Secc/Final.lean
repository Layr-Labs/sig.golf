import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearFinal
import SigGolfCandidate.Research.V7Composed198Closing
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafRestart
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsClasses
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingContact
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsSmallTransport
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsSmallContract
import SigGolfCandidate.ClaudeWCT.Numerics.WCTPrice
import SigGolfCandidate.ClaudeWCT.W9.New.C2.SignerCompleteBound
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.FtsOverflow

section
namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
theorem reference_trace_length_le (adversary : AdversaryP) (q : Nat) (s : RefSample)
    (hs : s ∈ (referenceExperiment adversary q).support) : s.trace.length ≤ q := by
  rw [reference_eq_bind, PMF.mem_support_bind_iff] at hs
  obtain ⟨R, -, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨run, hrun, rfl⟩ := hs
  have h1 := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hrun
  have h2 : run ∈ support (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) := by
    revert h1
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (refImpl (restTable R))
      (SphincsSecurity.QueryCap.recorded (referenceGame (restTable R) adversary q)) run
  have hcount : (run.1, SphincsSecurity.QueryCap.calls RefCharged run.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (referenceGame (restTable R) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨run, h2, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (restTable R) adversary q) _ hcount
  refine le_trans ?_ hle
  show (traceOf (restTable R) run.2).length ≤ _
  have hf := traceOf_filter_length (restTable R) (fun _ => True) run.2
  simp only [decide_true, List.filter_true] at hf
  rw [hf]
  unfold SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨x, rfl, -⟩ := hq
  trivial
theorem prefixClassCount_le_length (s : RefSample) : prefixClassCount s ≤ s.trace.length :=
  List.length_filter_le _ _
theorem contactAt_maskAt_source (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) : ContactAt (maskAt T a) trace b ↔ ContactAt T trace b := by
  have hsize : ∀ c : ChainAddr, WotsExtract.SourceChain c → c.key.tree < 2 ^ 40 ∧ c.key.leaf < 2 ^ 24 := by
    intro c hc
    refine ⟨by have := hc.1.1; omega, ?_⟩
    have h1 := hc.1.2
    have h2 : 2 ^ height c.key.lay ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le c.key.lay; omega)
    omega
  unfold ContactAt
  rw [depth_maskAt_all T a b (Mask.maskOK_of_lt (hsize a ha).2),
    frontierValue_maskAt_bounded T a b (hsize a ha) (hsize b hb) hb.2]
def OtherContact (a : ChainAddr) (T : Answers) (trace : List Entry) : Prop :=
  ∃ b, WotsExtract.SourceChain b ∧ b ≠ a ∧ ContactAt T trace b
theorem otherContact_maskAt (a : ChainAddr) (ha : WotsExtract.SourceChain a) (T : Answers) (trace : List Entry) :
    OtherContact a (maskAt T a) trace ↔ OtherContact a T trace := by
  unfold OtherContact
  constructor
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mp h⟩
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mpr h⟩
theorem contactAt_take_length (T : Answers) (trace : List Entry) (a : ChainAddr) (h : ContactAt T trace a) :
    ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem first_contact_entry (T : Answers) (tr : List Entry) (a : ChainAddr) (k : Nat)
    (hk : ContactAt T (tr.take (k + 1)) a) (hn : ¬ContactAt T (tr.take k) a) :
    ∃ value answer, tr[k]? = some (chainRow a (depth T a - 1) value, answer) := by
  obtain ⟨hd, value, answer, hm, hl⟩ := hk
  refine ⟨value, answer, ?_⟩
  rw [List.take_add_one, List.mem_append] at hm
  rcases hm with hm | hm
  · exact absurd ⟨hd, value, answer, hm, hl⟩ hn
  · cases h : tr[k]? with
    | none => rw [h] at hm; simp at hm
    | some e => rw [h] at hm; simp only [Option.toList_some, List.mem_singleton] at hm; rw [hm]
theorem twoContacts_cases (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) (hab : a ≠ b) (hca : ContactAt T trace a) (hcb : ContactAt T trace b) :
    ContactAfterStop (OtherContact a) T trace a ∨ ContactAfterStop (OtherContact b) T trace b := by
  classical
  let ka := Nat.find (contactAt_take_length T trace a hca)
  let kb := Nat.find (contactAt_take_length T trace b hcb)
  have hka : ContactAt T (trace.take ka) a := Nat.find_spec (contactAt_take_length T trace a hca)
  have hkb : ContactAt T (trace.take kb) b := Nat.find_spec (contactAt_take_length T trace b hcb)
  have hma : ∀ j < ka, ¬ContactAt T (trace.take j) a := fun j hj => Nat.find_min _ hj
  have hmb : ∀ j < kb, ¬ContactAt T (trace.take j) b := fun j hj => Nat.find_min _ hj
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact Or.inr ⟨ka, ⟨a, ha, hab, hka⟩, hmb ka hlt, hcb⟩
  · exfalso
    have hpos : 0 < ka := by
      by_contra h0
      have : ka = 0 := by omega
      rw [this] at hka
      obtain ⟨_, _, _, hm, _⟩ := hka
      simp at hm
    obtain ⟨k, hk⟩ : ∃ k, ka = k + 1 := ⟨ka - 1, by omega⟩
    have hka' : ContactAt T (trace.take (k + 1)) a := by rw [← hk]; exact hka
    have hkb' : ContactAt T (trace.take (k + 1)) b := by rw [← hk, heq]; exact hkb
    have ea := first_contact_entry T trace a k hka' (hma k (by omega))
    have eb := first_contact_entry T trace b k hkb' (hmb k (by omega))
    obtain ⟨va, wa, hea⟩ := ea
    obtain ⟨vb, wb, heb⟩ := eb
    rw [hea] at heb
    have hrow := congrArg Prod.fst (Option.some.inj heb)
    simp only at hrow
    have hda : 1 ≤ depth T a := hca.1
    have hdb : 1 ≤ depth T b := hcb.1
    exact hab (prefixRowAt_unique (answers := T) ha hb ⟨_, va, by omega, rfl⟩ ⟨_, vb, by omega, hrow⟩)
  · exact Or.inl ⟨kb, ⟨b, hb, hab.symm, hkb⟩, hma kb hgt, hca⟩
theorem otherContact_take_count (s : RefSample) (a : ChainAddr)
    (h : ∃ k, OtherContact a s.answers (s.trace.take k)) : 1 ≤ contactCount s := by
  obtain ⟨k, b, hb, -, hc⟩ := h
  unfold contactCount
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨(mem_sourceChains b).mpr hb, ?_⟩⟩
  obtain ⟨hd, value, answer, hm, hl⟩ := hc
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
theorem otherContact_stopL (a : ChainAddr) (ha : WotsExtract.SourceChain a) :
    ∀ T T', Leaf.LeafCongr a.key T T' → ∀ trace, OtherContact a T' trace ↔ OtherContact a T trace := by
  intro T T' hC trace
  unfold OtherContact
  exact exists_congr fun b => and_congr_right fun hb => and_congr_right fun _ =>
    Leaf.contactAt_leafCongr hC (Leaf.source_bounds ha).2 (Leaf.source_bounds ha).1 trace hb
/-- `(2^128 + 2q) T / ((1 - x) 2^128) = (1 + 2x) / (1 - x) · T`. -/
theorem big_div_mul (q : Nat) (T : ENNReal) :
    ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * T / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) =
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * T := by
  have h1 : (2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
  have e : ∀ y : ENNReal, ((2 : ENNReal) ^ 128 + ((2 * q : ℕ) : ENNReal)) * T * (y * ((2 : ENNReal) ^ 128)⁻¹) =
      y * T * ((2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹) + 2 * ((q : ENNReal) * ((2 : ENNReal) ^ 128)⁻¹) * y * T := by
    intro y
    push_cast
    ring
  rw [e, h1]
  ring
theorem reference_twoContacts_le_raw (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      (((2 * q : ℕ) : ENNReal) *
          (((2 / 2 ^ 128) * (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) +
              (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q) /
            (1 - (q : ENNReal) / 2 ^ 128)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * Leaf.errTot adversary q) /
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hne : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hpos (by simp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      ∑ a ∈ sourceChains, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
        referenceExperiment adversary q] := by
    refine le_trans ?_ (probEvent_exists_finset_le_sum sourceChains (referenceExperiment adversary q)
        (fun a s => ContactAfterStop (OtherContact a) s.answers s.trace a))
    apply pmf_probEvent_mono
    rintro s - ⟨a, b, ha, hb, hab, hca, hcb⟩
    rcases twoContacts_cases s.answers s.trace a b ha hb hab hca hcb with h | h
    · exact ⟨a, (mem_sourceChains a).mpr ha, h⟩
    · exact ⟨b, (mem_sourceChains b).mpr hb, h⟩
  have hcharge := fun a (ha : a ∈ sourceChains) =>
    Leaf.source_contactAfterStop_charge (adversary := adversary) q ((mem_sourceChains a).mp ha) (OtherContact a)
      (otherContact_maskAt a ((mem_sourceChains a).mp ha)) (otherContact_stopL a ((mem_sourceChains a).mp ha)) hq
  have halloc : ∑ a ∈ sourceChains, ∑' s, referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) ≤
      ((2 * q : ℕ) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := by
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    by_cases hs : s ∈ (referenceExperiment adversary q).support
    · rw [← Finset.mul_sum]
      have hpoint : ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0) ≤
          ((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
        calc ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
              (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
            ≤ ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul' le_rfl
              by_cases h : ∃ k, OtherContact a s.answers (s.trace.take k)
              · rw [if_pos h]
                exact_mod_cast otherContact_take_count s a h
              · rw [if_neg h]
                exact bot_le
          _ = ((2 * ∑ a ∈ sourceChains, prefixCount a s : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              rw [← Finset.sum_mul, Finset.mul_sum, Nat.cast_sum]
          _ ≤ ((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal) := by
              apply mul_le_mul' _ le_rfl
              have h1 := prefixCount_sum_le s
              have h2 := prefixClassCount_le_length s
              have h3 := reference_trace_length_le adversary q s hs
              exact_mod_cast (by omega : 2 * ∑ a ∈ sourceChains, prefixCount a s ≤ 2 * q)
      calc referenceExperiment adversary q s * ∑ a ∈ sourceChains, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
          ≤ referenceExperiment adversary q s * (((2 * q : ℕ) : ENNReal) * (contactCount s : ENNReal)) :=
            mul_le_mul' le_rfl hpoint
        _ = ((2 * q : ℕ) : ENNReal) * (referenceExperiment adversary q s * (contactCount s : ENNReal)) := by ring
    · rw [(PMF.apply_eq_zero_iff _ s).mpr hs]
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  calc Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] *
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
      ≤ (∑ a ∈ sourceChains, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
          referenceExperiment adversary q]) * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ sourceChains, (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a | referenceExperiment adversary q]) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ sourceChains, (∑' s, referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * Leaf.errC adversary q a) :=
        Finset.sum_le_sum fun a ha => hcharge a ha
    _ = ∑ a ∈ sourceChains, ∑' s, referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * Leaf.errTot adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
    _ ≤ ((2 * q : ℕ) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * Leaf.errTot adversary q := add_le_add halloc le_rfl
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (reference_contacts_cost_le adversary q hq)) le_rfl
theorem reference_twoContacts_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
      (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) *
          (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * Leaf.errTot adversary q := by
  refine (reference_twoContacts_le_raw adversary q hq).trans (le_of_eq ?_)
  rw [ENNReal.add_div, big_div_mul]
  set E := ∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)
  set T := Leaf.errTot adversary q
  set y := 1 - (q : ENNReal) / 2 ^ 128
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt), pow_two, ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt)]
  push_cast
  ring
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallP
theorem mem_take_succ {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ l[n]? = some x := by
  rw [List.take_add_one, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y =>
        rw [hl] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        rw [h]
theorem probEvent_le_six {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] + Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p] := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  exact probEvent_or_le _ _ _
theorem probEvent_le_six_split {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) (a b : ENNReal) (hab : a + b = 1) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] +
      (a * (Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p]) +
        b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]) := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  calc Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]
      = (a + b) * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := by rw [hab, one_mul]
    _ = a * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] +
          b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := add_mul _ _ _
    _ ≤ _ := by
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      exact probEvent_or_le _ _ _
end SmallP
open SmallP
end SigGolfCandidate.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallR
end SmallR
open SmallR
end SigGolfCandidate.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallP
open SigGolfCandidate.T3.Security.Wots.SmallP (mem_take_succ probEvent_le_six)
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a
def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a
theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : MarkerAt T trace a) (hc : ContactAt T trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, MarkerAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, MarkerAt T (trace.take k) a ∧ ∀ j < k, ¬MarkerAt T (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, ContactAt T (trace.take k) a ∧ ∀ j < k, ¬ContactAt T (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, pad, answer, digits, -, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, pad, answer, digits, hfit, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, pad, answer, digits, hfit, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact ClaudeWCT.W9.T3.Security.Wots.SmallA.chainRow_ne_encRow _ _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩
theorem primitive_cases (T : Answers) (trace : List Entry) (h : WotsExtract.WotsPrimitiveSrc T trace) :
    (∃ L, WotsExtract.SourceLeaf7 L ∧ EncodingMatchAt T trace L) ∨ WotsExtract.StructuralHitSrc T trace ∨
      (∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt T trace a) ∨
      (∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧ ContactAt T trace a ∧
        ContactAt T trace b) ∨
      (∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst T trace a) ∨
      (∃ a, WotsExtract.SourceChain7 a ∧ ContactFirst T trace a) := by
  rcases h with h | h | h | h | ⟨a, ha, hm, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases markerContact_split T trace a hm hc with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, h'⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, h'⟩))))
def chainOf (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨⟨p.1.lay, p.1.tree.val, p.1.leaf.val⟩, p.2.val⟩
theorem exists_chainOf {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, chainOf p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
end SmallP
def TwoContactsBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
      ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | referenceExperiment adversary q] ≤
    (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
      (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
    (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * Leaf.errTot adversary q
/-- Selected-half contact rate is at most 93; the uniform marker sum is at most 54*93 = 5022. -/
def ContactFirstBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ SmallP.ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
    93 * ((q : ENNReal) / 2 ^ 128) * refExpect adversary q contactCount
def MarkerSumBound (adversary : AdversaryP) (q : Nat) : Prop :=
  ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
    (5022 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount
noncomputable def prefixCoeffW9 (q : Nat) : ENNReal :=
  (88 / 1000 : ENNReal) *
    (((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
        (1 - (q : ENNReal) / 2 ^ 128) +
      4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      2 * 93 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)) +
    (912 / 1000 : ENNReal) * 2 / (1 - (q : ENNReal) / 2 ^ 128)
noncomputable def encodingCoeffW9 (q : Nat) : ENNReal :=
  7 / 4 + (88 / 1000 : ENNReal) * 2 * 5022 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
/-- Coefficient of the total seed-test error `Leaf.errTot` in the small-route primitive bound (campaign X1 B3). -/
noncomputable def errCoeffW9 (q : Nat) : ENNReal :=
  (88 / 1000 : ENNReal) *
    ((1 + twoEdgeRate q * q) / (1 - (q : ENNReal) / 2 ^ 128) +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) +
      93 * ((q : ENNReal) / 2 ^ 128) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))) +
    (912 / 1000 : ENNReal) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))
theorem chainOf_injective : Function.Injective SmallP.chainOf := by
  rintro ⟨⟨l, t, f⟩, c⟩ ⟨⟨l', t', f'⟩, c'⟩ h
  simp only [SmallP.chainOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hf⟩, hc⟩ := h
  rw [Fin.ext ht, Fin.ext hf, Fin.ext hc]
set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_le (adversary : AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, Leaf.errC adversary q (SmallP.chainOf p) ≤ Leaf.errTot adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, Leaf.errC adversary q (SmallP.chainOf p) =
      ∑ a ∈ Finset.univ.image SmallP.chainOf, Leaf.errC adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image SmallP.chainOf, Leaf.errC adversary q a ≤
      ∑ a ∈ (Finset.univ.image SmallP.chainOf).filter WotsExtract.SourceChain, Leaf.errC adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · unfold Leaf.errC
      rw [dif_neg h]
  have h3 : (Finset.univ.image SmallP.chainOf).filter WotsExtract.SourceChain ⊆ sourceChains := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (mem_sourceChains a).mpr ha.2
  rw [h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)
theorem reference_markerFirst_sum_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hMS : MarkerSumBound adversary q) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ SmallP.MarkerFirst s.answers s.trace a | referenceExperiment adversary q] ≤
      2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
        ((5022 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * Leaf.errTot adversary q := by
  have hu0 : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hutop : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hun0 : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hu0 (by simp)
  have huntop : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ ⊤ := ENNReal.mul_ne_top hutop (by simp)
  have hper : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (SmallP.chainOf p) ∧ SmallP.MarkerFirst s.answers s.trace (SmallP.chainOf p) |
          referenceExperiment adversary q] ≤
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (SmallP.chainOf p) ∧ MarkerAt s.answers s.trace (SmallP.chainOf p) |
            referenceExperiment adversary q] +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
          Leaf.errC adversary q (SmallP.chainOf p) := by
    intro p
    by_cases hs : WotsExtract.SourceChain7 (SmallP.chainOf p)
    · simp only [hs, true_and]
      have hC := Leaf.source_markerFirst_at_le (adversary := adversary) q hq (SmallP.chainOf p) hs.source
      set PF := Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace (SmallP.chainOf p)) s.answers s.trace
        (SmallP.chainOf p) | referenceExperiment adversary q]
      set PM := Pr[fun s => MarkerAt s.answers s.trace (SmallP.chainOf p) | referenceExperiment adversary q]
      set EC := Leaf.errC adversary q (SmallP.chainOf p)
      have hrhs : 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) * PM =
          (((2 * q : ℕ) : ENNReal) * PM) / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
        generalize hu : (1 - (q : ENNReal) / 2 ^ 128) = u at hu0 hutop ⊢
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop)]
        push_cast
        ring
      rw [hrhs, ← big_div_mul, ENNReal.div_add_div_same]
      apply (ENNReal.le_div_iff_mul_le (Or.inl hun0) (Or.inl huntop)).mpr
      calc PF * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
          = (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * PF) := by ring
        _ ≤ ((2 * q : ℕ) : ENNReal) * PM + ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * EC := hC
    · simp only [hs, false_and]
      simp
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ SmallP.MarkerFirst s.answers s.trace a | referenceExperiment adversary q]
      ≤ Pr[fun s => ∃ p ∈ (Finset.univ : Finset (CanonGraph.LeafPos × Fin 58)),
          WotsExtract.SourceChain7 (SmallP.chainOf p) ∧ SmallP.MarkerFirst s.answers s.trace (SmallP.chainOf p) |
          referenceExperiment adversary q] := by
        apply probEvent_mono''
        rintro s ⟨a, ha, hmf⟩
        obtain ⟨p, rfl⟩ := SmallP.exists_chainOf ha
        exact ⟨p, by simp, ha, hmf⟩
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58,
          Pr[fun s => WotsExtract.SourceChain7 (SmallP.chainOf p) ∧ SmallP.MarkerFirst s.answers s.trace (SmallP.chainOf p) |
            referenceExperiment adversary q] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58, (2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (SmallP.chainOf p) ∧ MarkerAt s.answers s.trace (SmallP.chainOf p) |
            referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            Leaf.errC adversary q (SmallP.chainOf p)) :=
        Finset.sum_le_sum fun p _ => hper p
    _ = 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ∑ p : CanonGraph.LeafPos × Fin 58,
            Pr[fun s => WotsExtract.SourceChain7 (SmallP.chainOf p) ∧ MarkerAt s.answers s.trace (SmallP.chainOf p) |
              referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            ∑ p : CanonGraph.LeafPos × Fin 58, Leaf.errC adversary q (SmallP.chainOf p) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        · exact hMS
        · exact sum_errC_chainOf_le adversary q
theorem reference_contactFirst_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hCF : ContactFirstBound adversary q) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ SmallP.ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
      93 * ((q : ENNReal) / 2 ^ 128) *
        (((2 / 2 ^ 128) * refExpect adversary q prefixClassCount + (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q) /
          (1 - (q : ENNReal) / 2 ^ 128)) :=
  hCF.trans (by gcongr; exact reference_contacts_cost_le adversary q hq)
theorem reference_markerFirst_contact_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => (∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt s.answers s.trace a) ∨
        (∃ a b, WotsExtract.SourceChain a ∧ WotsExtract.SourceChain b ∧ a ≠ b ∧
          ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b) ∨
        (∃ a, WotsExtract.SourceChain7 a ∧ SmallP.MarkerFirst s.answers s.trace a) ∨
        (∃ a, WotsExtract.SourceChain7 a ∧ SmallP.ContactFirst s.answers s.trace a) | referenceExperiment adversary q] ≤
      ((2 / 2 ^ 128) * refExpect adversary q prefixClassCount + (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  refine le_trans ?_ (reference_contacts_cost_le adversary q hq)
  rw [expected_contactCount]
  refine le_trans ?_ (probEvent_exists_finset_le_sum sourceChains (referenceExperiment adversary q)
    (fun a s => ContactAt s.answers s.trace a))
  apply probEvent_mono''
  rintro s (⟨a, ha, hd, _, middle, _, h2⟩ | ⟨a, _, ha, _, _, hc, _⟩ | ⟨a, ha, _, _, _, hc⟩ |
    ⟨a, ha, _, ⟨hd, val, ans, hmem, hlow⟩, _, _⟩)
  · exact ⟨a, (mem_sourceChains a).mpr ha, by omega, middle, h2⟩
  · exact ⟨a, (mem_sourceChains a).mpr ha, hc⟩
  · exact ⟨a, (mem_sourceChains a).mpr ha.source, hc⟩
  · exact ⟨a, (mem_sourceChains a).mpr ha.source, hd, val, ans, List.mem_of_mem_take hmem, hlow⟩
theorem reference_primitive_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hTC : TwoContactsBound adversary q) (hCF : ContactFirstBound adversary q) (hMS : MarkerSumBound adversary q) :
    Pr[fun s => WotsExtract.WotsPrimitiveSrc s.answers s.trace | referenceExperiment adversary q] ≤
      prefixCoeffW9 q / 2 ^ 128 * refExpect adversary q prefixClassCount +
        encodingCoeffW9 q / 2 ^ 128 * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount + errCoeffW9 q * Leaf.errTot adversary q := by
  have hab : (88 / 1000 : ENNReal) + 912 / 1000 = 1 :=
    (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp (by
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
        ENNReal.toReal_one]
      norm_num)
  refine (SigGolfCandidate.T3.Security.Wots.SmallP.probEvent_le_six_split _ _ _ _ _ _ _ _ (fun s h => SmallP.primitive_cases s.answers s.trace h)
    (88 / 1000) (912 / 1000) hab).trans ?_
  have h1 := reference_encodingMatch_le adversary q
  have h2 := reference_structural_src_le adversary q
  have h3 := reference_twoEdge_le adversary q hq
  have h5a := reference_markerFirst_sum_le adversary q hq hMS
  have h5b := reference_markerFirst_contact_le adversary q hq
  have h6 := reference_contactFirst_cost_le adversary q hq hCF
  calc _ ≤ (7 / (4 * 2 ^ 128) : ENNReal) * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount +
        ((88 / 1000 : ENNReal) *
          ((twoEdgeRate q * refExpect adversary q prefixClassCount + (1 + twoEdgeRate q * q) * Leaf.errTot adversary q) /
              (1 - (q : ENNReal) / 2 ^ 128) +
            ((4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
              (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
              (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
                (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * Leaf.errTot adversary q) +
            (2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
              ((5022 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) +
              (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * Leaf.errTot adversary q) +
            93 * ((q : ENNReal) / 2 ^ 128) *
              (((2 / 2 ^ 128) * refExpect adversary q prefixClassCount + (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q) /
                (1 - (q : ENNReal) / 2 ^ 128))) +
          (912 / 1000 : ENNReal) * (((2 / 2 ^ 128) * refExpect adversary q prefixClassCount +
            (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q) / (1 - (q : ENNReal) / 2 ^ 128))) := by
        gcongr
        · exact h1
        · exact h2
        · exact h3
        · exact hTC
    _ = _ := by
        unfold prefixCoeffW9 encodingCoeffW9 errCoeffW9 twoEdgeRate
        simp only [div_eq_mul_inv,
          ENNReal.mul_inv (Or.inl (by norm_num : (4 : ENNReal) ≠ 0))
            (Or.inl (by norm_num : (4 : ENNReal) ≠ ⊤))]
        ring
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallR
/-- Together with 248/100000, this rate gives the scalar closing coefficient 196327/100000. -/
noncomputable def classRateW9 : ENNReal := 196079 / 100000
theorem inv_one_sub_leW9 (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ 4194304 / 4193304 := by
  calc (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ (4193304 / 4194304 : ENNReal)⁻¹ :=
        ENNReal.inv_le_inv.mpr (SeccClosingW9.one_sub_x_ge_of_small q hs)
    _ = 4194304 / 4193304 := ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp))
theorem prefixCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : prefixCoeffW9 q ≤ classRateW9 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  unfold prefixCoeffW9 classRateW9
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ (1 - x),
    ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (88 / 1000 : ENNReal) * (((3 / 2 : ENNReal) + 4 * x + 2 * x ^ 2) * u + 4 * x * u ^ 2 + 2 * 93 * x * u) +
        (912 / 1000 : ENNReal) * 2 * u
      ≤ (88 / 1000 : ENNReal) *
          (((3 / 2 : ENNReal) + 4 * (1000 / 4194304 : ENNReal) + 2 * ((1000 / 4194304 : ENNReal))^2) * (4194304/4193304) +
            4 * (1000 / 4194304 : ENNReal) * (4194304/4193304)^2 + 2 * 93 * (1000 / 4194304 : ENNReal) * (4194304/4193304)) +
          (912 / 1000 : ENNReal) * 2 * (4194304/4193304) := by
        gcongr
    _ ≤ 196079 / 100000 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
        norm_num
theorem encodingCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : encodingCoeffW9 q ≤ classRateW9 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  unfold encodingCoeffW9 classRateW9
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x)]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (7 / 4 : ENNReal) + (88 / 1000 : ENNReal) * 2 * 5022 * x * u
      ≤ 7 / 4 + (88 / 1000 : ENNReal) * 2 * 5022 * (1000 / 4194304 : ENNReal) * (4194304/4193304) := by gcongr
    _ ≤ 196079 / 100000 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
theorem errCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : errCoeffW9 q ≤ 2 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  have e1 : twoEdgeRate q * q = ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) +
      2 * ((q : ENNReal) / 2 ^ 128) ^ 2) * ((q : ENNReal) / 2 ^ 128) := by
    unfold twoEdgeRate
    simp only [div_eq_mul_inv]
    ring
  have e2 : (2 / 2 ^ 128 : ENNReal) * q = 2 * ((q : ENNReal) / 2 ^ 128) := by
    simp only [div_eq_mul_inv]
    ring
  unfold errCoeffW9
  rw [e1, e2]
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  simp only [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (88 / 1000 : ENNReal) * ((1 + (3 / 2 + 4 * x + 2 * x ^ 2) * x) * u +
        (2 * x * (1 + 2 * x) * u ^ 2 + (1 + 2 * x) * u) + (1 + 2 * x) * u  + 93 * x * ((1 + 2 * x) * u)) +
        912 / 1000 * ((1 + 2 * x) * u)
      ≤ (88 / 1000 : ENNReal) *
          ((1 + (3 / 2 + 4 * (1000 / 4194304 : ENNReal) + 2 * (1000 / 4194304 : ENNReal) ^ 2) * (1000 / 4194304 : ENNReal)) *
              (4194304 / 4193304) +
            (2 * (1000 / 4194304 : ENNReal) * (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304) ^ 2 +
              (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304)) +
            (1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304) +
            93 * (1000 / 4194304 : ENNReal) * ((1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304))) +
          912 / 1000 * ((1 + 2 * (1000 / 4194304 : ENNReal)) * (4194304 / 4193304)) := by
        gcongr
    _ ≤ 2 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
theorem errTerm_le (adversary : AdversaryP) (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    errCoeffW9 q * Leaf.errTot adversary q ≤ (702 / 1000 : ENNReal) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  have hs' : q ≤ 2718 * 2 ^ 106 := by
    rw [SeccClosingW9.budgetSplit_def] at hs
    exact hs.trans (by norm_num)
  calc errCoeffW9 q * Leaf.errTot adversary q
      ≤ 2 * ((351 / 1000 : ENNReal) * ((q : ENNReal) / 2 ^ 128) ^ 2) :=
        mul_le_mul' (errCoeffW9_le q hs) (Leaf.errTot_le_small q hs')
    _ = (2 * (351 / 1000 : ENNReal)) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by ring
    _ = (702 / 1000 : ENNReal) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        congr 1
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat]
        norm_num
theorem one_le_classRateW9 : (1 : ENNReal) ≤ classRateW9 := by
  unfold classRateW9
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
theorem digestRate_leW9 : 1 + SeccClosingW9.cacheRate ≤ classRateW9 := by
  unfold classRateW9
  rw [SeccClosingW9.cacheRate_def]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
theorem excess_leW9 (q : Nat) :
    (q : ENNReal) * SeccClosingW9.excessRate / 2 ^ 128 ≤ (247 / 100000) * ((q : ENNReal) / 2 ^ 128) := by
  rw [SeccClosingW9.excessRate_def]
  simp only [div_eq_mul_inv]
  exact le_of_eq (by ring)
theorem nearTerm_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    nearTerm q ≤ (1501 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 + (1 / 100000) * ((q : ENNReal) / 2 ^ 128) := by
  have hg := SeccClosingW9.div_sub_le_of_small q hs
  unfold nearTerm nearPrice SigGolfCandidate.T3.Security.Wots.signRatio
  rw [SeccClosingW9.cacheRate_def, ← div_eq_mul_inv (q : ENNReal)]
  have hinner : (150 : ENNReal) * q / 2 ^ 128 + 63 * ((201 * q : ℕ) : ENNReal) * ((2 : ENNReal) ^ 25)⁻¹ / 2 ^ 128 +
      63 * (2 : ENNReal)⁻¹ ^ 700 =
      (150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * ((q : ENNReal) / 2 ^ 128) + 63 * (2 : ENNReal)⁻¹ ^ 700 := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hinner]
  generalize (q : ENNReal) / 2 ^ 128 = x at hg ⊢
  generalize (q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal) = g at hg ⊢
  calc g * ((150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700)
      ≤ (4194304 / 4193304 * x) * ((150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (4194304 / 4193304 * (150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹)) * x ^ 2 +
          (4194304 / 4193304 * (63 * (2 : ENNReal)⁻¹ ^ 700)) * x := by ring
    _ ≤ (1501 / 10) * x ^ 2 + (1 / 100000) * x := by
        gcongr
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          norm_num
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
          norm_num
theorem pairTerm_leW9 (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    BPair.pairTerm q ≤ (6 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  have hg := SeccClosingW9.div_sub_le_of_small q hs
  have hc : (q.choose 2 : ENNReal) ≤ (1 / 2 : ENNReal) * ((q : ENNReal) * q) := by
    have hc2 : ((q.choose 2 * 2 : Nat) : ENNReal) ≤ ((q * q : Nat) : ENNReal) :=
      Nat.cast_le.mpr (by rw [Nat.choose_two_right]; exact (Nat.div_mul_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
    calc (q.choose 2 : ENNReal) = (1 / 2 : ENNReal) * ((q.choose 2 * 2 : Nat) : ENNReal) := by
          push_cast
          rw [one_div, mul_comm, mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
      _ ≤ (1 / 2 : ENNReal) * ((q * q : Nat) : ENNReal) := mul_le_mul' le_rfl hc2
      _ = (1 / 2 : ENNReal) * ((q : ENNReal) * q) := by push_cast; rfl
  unfold BPair.pairTerm
  calc (q.choose 2 : ENNReal) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2
      ≤ ((1 / 2 : ENNReal) * ((q : ENNReal) * q)) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2 := by gcongr
    _ = (1 / 2 : ENNReal) * ((q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal)) ^ 2 := by simp only [div_eq_mul_inv, mul_pow]; ring
    _ ≤ (1 / 2 : ENNReal) * (4194304 / 4193304 * ((q : ENNReal) / 2 ^ 128)) ^ 2 := by gcongr
    _ = ((1 / 2 : ENNReal) * (4194304 / 4193304 : ENNReal) ^ 2) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        rw [mul_pow]; ring
    _ ≤ (6 / 10) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        gcongr
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
end SmallR
theorem twoContactsBound (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) : TwoContactsBound adversary q :=
  reference_twoContacts_le adversary q hq
theorem markerSumBound (adversary : AdversaryP) (q : Nat) : MarkerSumBound adversary q :=
  reference_marker_sum_le adversary q
theorem contactFirstBound (adversary : AdversaryP) (q : Nat) : ContactFirstBound adversary q :=
  reference_contactFirst_le adversary q
/-- The clean win splits into cases A/B, case C without FTS overflow, signer incompleteness, and the FTS overflow
event (campaign X1 stage A; bounded by `fts_overflow_le`). -/
theorem cleanWin_le_cases (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z ∧ WPair.NoOverflow adversary z |
        SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ClaudeWCT.W9.T3.Security.FtsOverflow z.1 |
        SeccLaw.completedExperiment adversary q hq] := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) ((probEvent_or_le _ _ _).trans
    (add_le_add ((probEvent_or_le _ _ _).trans (add_le_add (probEvent_or_le _ _ _) le_rfl)) le_rfl))
  intro z hz hclean
  by_cases hov : ClaudeWCT.W9.T3.Security.FtsOverflow z.1
  · exact Or.inr ⟨hclean, hov⟩
  by_cases hcomp : BPB.SignerComplete z.2
  · rcases completed_split_src adversary q hq z hz hclean hcomp with h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hclean, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hclean, h, WPair.noOverflow_of_outIdx adversary z fun g i c hs =>
        ClaudeWCT.W9.T3.Security.logNoOverflow_of_not_ftsOverflow adversary q hq z hz hov g i c hs⟩))
    · exact absurd h (CaseC.caseCSignedPinned_impossible adversary q hq z hz hclean)
  · exact Or.inl (Or.inr hcomp)
theorem small_route (hC : CaseCSmallBound) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosingW9.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosingW9.smallBound q := by
  intro adversary q hq hq1 hs
  have hq128 : q < 2 ^ 128 := lt_of_le_of_lt hq (by norm_num)
  have hbudget := reference_class_budget adversary q hq
  have hab := (caseABSrc_le_reference adversary q hq).trans (reference_primitive_le adversary q hq128
    (twoContactsBound adversary q hq128) (contactFirstBound adversary q) (markerSumBound adversary q))
  have hc := hC adversary q hq hq1 hs
  have k1 : prefixCoeffW9 q / 2 ^ 128 ≤ SmallR.classRateW9 / 2 ^ 128 := by gcongr; exact SmallR.prefixCoeffW9_le q hs
  have k2 : encodingCoeffW9 q / 2 ^ 128 ≤ SmallR.classRateW9 / 2 ^ 128 := by gcongr; exact SmallR.encodingCoeffW9_le q hs
  have k3 : (2 ^ 128 : ENNReal)⁻¹ ≤ SmallR.classRateW9 / 2 ^ 128 := by
    rw [← one_div]; exact ENNReal.div_le_div_right SmallR.one_le_classRateW9 _
  have k4 : (1 + SeccClosingW9.cacheRate) / 2 ^ 128 ≤ SmallR.classRateW9 / 2 ^ 128 := by gcongr; exact SmallR.digestRate_leW9
  generalize refExpect adversary q prefixClassCount = EP at hbudget hab
  generalize refExpect adversary q encodingCount = EE at hbudget hab
  generalize refExpect adversary q otherCount = EO at hbudget hab
  generalize SeccLaw.expectedCharge adversary q hq digestClass = EM at hbudget hc
  have hcq : SmallR.classRateW9 / 2 ^ 128 * (EP + EE + EO + EM) ≤ SmallR.classRateW9 * ((q : ENNReal) / 2 ^ 128) := by
    calc SmallR.classRateW9 / 2 ^ 128 * (EP + EE + EO + EM) ≤ SmallR.classRateW9 / 2 ^ 128 * q := by gcongr
      _ = SmallR.classRateW9 * ((q : ENNReal) / 2 ^ 128) := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hex := SmallR.excess_leW9 q
  have hnear := SmallR.nearTerm_le q hs
  have hpair := SmallR.pairTerm_leW9 q hs
  -- signer incompleteness (2^-698, or 2^-298 after the X1 lower-target change) is charged as 2^-138
  have hinc : Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] ≤
      ((2 : ENNReal) ^ 138)⁻¹ :=
    (BPB.signerIncomplete_le adversary q hq).trans (by
      rw [one_div]
      exact ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ one_le_two (by norm_num)))
  have hov := ClaudeWCT.W9.T3.Security.fts_overflow_le adversary q hq
  have herr := SmallR.errTerm_le adversary q hs
  apply SeccClosingW9.smallBound_of_le q _ (SmallR.classRateW9 + 247 / 100000 + 1 / 100000) (75701 / 500)
    ((2 : ENNReal)⁻¹ ^ 700 + ((2 : ENNReal) ^ 138)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹)
  · rw [SeccClosingW9.smallCoefficient_def]
    unfold SmallR.classRateW9
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_one]
    norm_num
  · exact le_of_eq SeccClosingW9.smallQuadratic_def.symm
  · rw [SeccClosingW9.smallAbsolute_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  generalize errCoeffW9 q * Leaf.errTot adversary q = ER at hab herr
  generalize (q : ENNReal) / 2 ^ 128 = x at hcq hex hnear hpair herr
  calc Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq]
      ≤ Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z |
            SeccLaw.completedExperiment adversary q hq] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z ∧ WPair.NoOverflow adversary z |
            SeccLaw.completedExperiment adversary q hq] +
          Pr[fun z => ¬BPB.SignerComplete z.2 | SeccLaw.completedExperiment adversary q hq] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ClaudeWCT.W9.T3.Security.FtsOverflow z.1 |
            SeccLaw.completedExperiment adversary q hq] :=
        cleanWin_le_cases adversary q hq
    _ ≤ (prefixCoeffW9 q / 2 ^ 128 * EP + encodingCoeffW9 q / 2 ^ 128 * EE + (2 ^ 128 : ENNReal)⁻¹ * EO +
            ER) +
          ((1 + SeccClosingW9.cacheRate) / 2 ^ 128 * EM +
            (q : ENNReal) * SeccClosingW9.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
            (2 : ENNReal)⁻¹ ^ 700) + ((2 : ENNReal) ^ 138)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹ :=
        add_le_add (add_le_add (add_le_add hab hc) hinc) hov
    _ ≤ (SmallR.classRateW9 / 2 ^ 128 * EP + SmallR.classRateW9 / 2 ^ 128 * EE + SmallR.classRateW9 / 2 ^ 128 * EO +
            (702 / 1000) * x ^ 2) +
          (SmallR.classRateW9 / 2 ^ 128 * EM + 247 / 100000 * x + ((1501 / 10) * x ^ 2 + 1 / 100000 * x) + (6 / 10) * x ^ 2 +
            (2 : ENNReal)⁻¹ ^ 700) + ((2 : ENNReal) ^ 138)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹ := by gcongr
    _ = SmallR.classRateW9 / 2 ^ 128 * (EP + EE + EO + EM) +
          (247 / 100000 * x + ((1501 / 10) * x ^ 2 + 1 / 100000 * x) + (6 / 10) * x ^ 2 + (702 / 1000) * x ^ 2 +
            ((2 : ENNReal)⁻¹ ^ 700 + ((2 : ENNReal) ^ 138)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹)) := by
        ring
    _ ≤ SmallR.classRateW9 * x + (247 / 100000 * x + ((1501 / 10) * x ^ 2 + 1 / 100000 * x) + (6 / 10) * x ^ 2 +
          (702 / 1000) * x ^ 2 + ((2 : ENNReal)⁻¹ ^ 700 + ((2 : ENNReal) ^ 138)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹)) := by
        gcongr
    _ = (SmallR.classRateW9 + 247 / 100000 + 1 / 100000) * x + ((1501 / 10 : ENNReal) + 6 / 10 + 702 / 1000) * x ^ 2 +
          ((2 : ENNReal)⁻¹ ^ 700 + ((2 : ENNReal) ^ 138)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹) := by
        ring
    _ ≤ (SmallR.classRateW9 + 247 / 100000 + 1 / 100000) * x + (75701 / 500) * x ^ 2 +
          ((2 : ENNReal)⁻¹ ^ 700 + ((2 : ENNReal) ^ 138)⁻¹ + ((2 : ENNReal) ^ 137)⁻¹) := by
        gcongr
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat]
        norm_num
theorem securityP_of_small (hC : CaseCSmallBound)
    (hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosingW9.budgetSplit ≤ q →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosingW9.largeBound q) :
    SecurityP := by
  apply PaddedGame.securityP_of_clean_bound
  intro adversary q hpositive hq
  have key : Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] + SeccClosingW9.secTerms q ≤
      (q : ENNReal) / 2 ^ 127 := by
    by_cases hs : q ≤ SeccClosingW9.budgetSplit
    · exact (add_le_add (small_route hC adversary q hq hpositive hs) le_rfl).trans
        (SeccClosingW9.small_closing q hpositive hs)
    · exact (add_le_add (hlarge adversary q hq (by omega)) le_rfl).trans
        (SeccClosingW9.large_closing q (by omega) hq)
  simpa only [SeccClosingW9.secTerms, add_assoc] using key
end ClaudeWCT.W9.T3.Security.Wots
end
section
namespace ClaudeWCT.W9.T3.Secc
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security (QueryRecorded.CleanWin)
open ClaudeWCT.W9.T3.Security.SeccClosingW9 (budgetSplit largeBound)
open ClaudeWCT.W9.T3M.Final (AdversaryP SecurityP)
def LargeRouteBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | ClaudeWCT.W9.T3.Security.PaddedGame.tracedExperiment adversary q hq] ≤
      largeBound q
/-- The small case-C bound from the near and pair bounds on runs without FTS overflow (campaign X1 stage A). -/
theorem caseCSmallBound_of
    (hnear : ClaudeWCT.W9.T3.Security.CaseC.NearBoundOn ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
      ClaudeWCT.W9.T3.Security.CaseC.NearQ ClaudeWCT.W9.T3.Security.WPair.NoOverflow
      ClaudeWCT.W9.T3.Security.Wots.nearTerm)
    (hpair : ClaudeWCT.W9.T3.Security.WPair.PairGuessBoundNO SigGolfCandidate.T3.Security.BPair.pairTerm) :
    ClaudeWCT.W9.T3.Security.Wots.CaseCSmallBound :=
  ClaudeWCT.W9.T3.Security.CaseC.caseC_small_bound ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
    ClaudeWCT.W9.T3.Security.CaseC.caseCSplitInterface ClaudeWCT.W9.T3.Security.WPair.NoOverflow
    ClaudeWCT.W9.T3.Security.Wots.nearTerm SigGolfCandidate.T3.Security.BPair.pairTerm
    ClaudeWCT.Numerics.WCTPrice.wct_excessBound_2_32 hnear hpair
theorem t3_securityP
    (hnear : ClaudeWCT.W9.T3.Security.CaseC.NearBoundOn ClaudeWCT.W9.T3.Security.CaseC.caseCExtraction
      ClaudeWCT.W9.T3.Security.CaseC.NearQ ClaudeWCT.W9.T3.Security.WPair.NoOverflow
      ClaudeWCT.W9.T3.Security.Wots.nearTerm)
    (hpair : ClaudeWCT.W9.T3.Security.WPair.PairGuessBoundNO SigGolfCandidate.T3.Security.BPair.pairTerm)
    (hlarge : LargeRouteBound) : SecurityP :=
  ClaudeWCT.W9.T3.Security.Wots.securityP_of_small (caseCSmallBound_of hnear hpair) hlarge
end ClaudeWCT.W9.T3.Secc
end

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (LeafAddr entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem sourceMessages_lower (answers : Answers) (index : Nat) (hidx : index < 2^31)
    (n : Nat) (hn : 1 ≤ n) (hn4 : n < 4) :
    CanonicalRef.sourceMessages answers (routeLeaf index (Fin.ofNat 4 (n-1))) =
      WCT9.LayerMsg.pair
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).1
        (Extract.honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).2 := by
  have hl : (Fin.ofNat 4 (n-1) : Layer).val < 3 := by
    rw [Extract.ofNat_val (n-1) (by omega)]; omega
  have hm : CanonicalRef.sourceMessages answers (routeLeaf index (Fin.ofNat 4 (n-1))) =
      leafMsg answers (routeLeaf index (Fin.ofNat 4 (n-1))) := by
    unfold CanonicalRef.sourceMessages leafMsg
    simp only [routeLeaf, hl, dite_true]
  rw [hm, WotsExtract.leafMsg_route answers index _ hidx]
  exact Extract.honestMsg_lower answers index n hn (by omega)

theorem sourceMessages_bottom (answers : Answers) (index : Nat) (hidx : index < 2^31) :
    CanonicalRef.sourceMessages answers (routeLeaf index 3) =
      WCT9.LayerMsg.pair (CanonicalRef.forestCommitment answers index).1
        (CanonicalRef.forestCommitment answers index).2 := by
  have hroute : (route index 3).2 * 2 ^ height 3 + (route index 3).1 = index := by
    change index / 64 * 64 + (index / 1) % 64 = index
    rw [Nat.div_one]
    omega
  simp only [CanonicalRef.sourceMessages, routeLeaf, show ¬ (3 : Layer).val < 3 by decide,
    dite_false, hroute, Nat.mod_eq_of_lt hidx]

theorem layers_source_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2^31)
    (msg : WCT9.LayerMsg) (hfit : Extract.msgFits 3 msg)
    (h : evalWithAnswerFn answers (layersCanonicalBC w index 4 msg) = some (Extract.honestRoot answers 0 0)) :
    WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
      (entriesOf answers (queried answers (layersCanonicalBC w index 4 msg))) ∨
    ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) w index lay) ∧
      msg = WCT9.LayerMsg.pair (CanonicalRef.forestCommitment answers index).1
        (CanonicalRef.forestCommitment answers index).2) := by
  have hs := layersCanonicalBC_wots_walk answers (CanonicalRef.sourceMessages answers) w index hidx
    (fun lay => CanonicalRef.sourceMessages_fit answers (routeLeaf index lay))
    (sourceMessages_lower answers index hidx) 4 (by decide) le_rfl msg hfit h
  rcases hs with hp | ⟨hg, hm⟩
  · exact Or.inl hp
  · right
    refine ⟨fun lay => hg lay lay.isLt, ?_⟩
    change msg = CanonicalRef.sourceMessages answers (routeLeaf index 3) at hm
    exact hm.trans (sourceMessages_bottom answers index hidx)
#print axioms layers_source_walk
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (entriesOf_mono)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifyP_source_walk (answers : Answers) (message : Message) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (Paired.verifyP message pk w) = true) :
    ∃ output : HashOutput,
      (wdc w).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : Spec.Domain) ∈
        queried answers (Paired.verifyP message pk w) ∧
      output.toNat / 2^242 % 16384 < 734 ∧
      (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
      (WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
          (entriesOf answers (queried answers (Paired.verifyP message pk w))) ∨
        ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) w (WCT9.digestIndex output) lay) ∧
          evalWithAnswerFn answers (SharedV3.forest w (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) =
            CanonicalRef.forestCommitment answers (WCT9.digestIndex output) ∧
          ∀ q ∈ queried answers (SharedV3.forest w (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))),
            q ∈ queried answers (Paired.verifyP message pk w))) := by
  obtain ⟨output, top, hd, hf, hl, hqD, hqF, hqL⟩ := Paired.verifyP_split answers message pk w hv
  obtain ⟨hcounter, houtput, hquery⟩ := Paired.digestP_success answers message w output hd
  obtain ⟨hgate, hrank, hforest, hforestQ⟩ := Paired.ftsP_success answers w output top hf
  refine ⟨output, hcounter, houtput, hqD _ ?_, hgate, hrank, ?_⟩
  · rw [hquery]
    exact List.mem_singleton_self _
  · have hidx : WCT9.digestIndex output < 2^31 := Nat.mod_lt _ (by norm_num)
    rcases layers_source_walk answers w (WCT9.digestIndex output) hidx (.pair top.1 top.2) trivial
      (hpk ▸ hl) with hp | ⟨hg, hmsg⟩
    · exact Or.inl (hp.mono (entriesOf_mono hqL))
    · refine Or.inr ⟨hg, hforest.trans ?_, ?_⟩
      · exact Prod.ext (WCT9.LayerMsg.pair.inj hmsg).1 (WCT9.LayerMsg.pair.inj hmsg).2
      · intro q hq
        exact hqF q (hforestQ ▸ hq)
#print axioms verifyP_source_walk
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expanded_canonical_selections (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEnc output w)
      (WCT9.digestIndex output) lay)
    (hf : evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest) =
        forestCommitment answers (WCT9.digestIndex output)) :
    ∃ digits : List (List Nat),
      policyHintsValid w.signature.policyHints digits = true ∧
      (∀ lay, evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (hintFloor w.signature.policyHints lay) (route (WCT9.digestIndex output) lay).2
        (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        0 (WCT9.searchLimit lay)) = some (w.counters lay, digits.getD lay.val [])) ∧
      ∀ lay, w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (digits.getD lay.val [])) := by
  obtain ⟨_, counter, result, c, _, hr, hvalid, hsig, _, hcs⟩ := Paired.expandN_selections answers message pk sig output w he
  have hs := recoverHintedLayers_selections answers (fillTopSignature sig 0) (WCT9.digestIndex output)
    (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4 le_rfl _ result hr
  let input : WCT9.LayerMsg := .pair
    (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
    (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2
  have hsel : ∀ lay, evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay (hintFloor w.signature.policyHints lay)
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (recoveredMessage answers w.signature (WCT9.digestIndex output) 4 input result.digits lay)
        0 (WCT9.searchLimit lay)) = some (result.counters.getD lay.val 0, result.digits.getD lay.val []) := by
    intro lay
    have hx := hs.2.2 lay lay.isLt
    change evalWithAnswerFn answers
      (WCT9.CanonicalPolicy.layerCounterSearchAt lay (hintFloor sig.policyHints lay)
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (recoveredMessage answers (fillTopSignature sig 0) (WCT9.digestIndex output) 4 input result.digits lay)
        0 (WCT9.searchLimit lay)) = _ at hx
    rw [recoveredMessage_fill answers sig _ 4 le_rfl _ _ lay lay.isLt 0] at hx
    rw [hsig, hints_retained, recoveredMessage_fill answers sig _ 4 le_rfl _ _ lay lay.isLt c]
    exact hx
  have hshape := good_shape_witEnc answers output w hg
  have hshape' : ∀ lay, ∃ ds, WCT9.CanonicalPolicy.decode lay
      (evalWithAnswerFn answers (WCT9.encodingHash lay (WCT9.layerEncodingInput lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        (result.counters.getD lay.val 0)))) = some ds ∧
      w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1 ds) := by
    intro lay
    simpa only [hcs lay] using hshape lay
  have hi : WCT9.digestIndex output < 2^31 := Nat.mod_lt _ (by decide)
  have lower : ∀ n, n < 3 → CanonicalRef.sourceMessages answers
      (routeLeaf (WCT9.digestIndex output) (Fin.ofNat 4 n)) =
      .pair (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route (WCT9.digestIndex output) (Fin.ofNat 4 (n+1))).2).1
        (WCT9.builtPair answers (Fin.ofNat 4 (n+1)) (route (WCT9.digestIndex output) (Fin.ofNat 4 (n+1))).2).2 := by
    intro n hn
    have hm := sourceMessages_lower answers (WCT9.digestIndex output) hi (n+1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel, Extract.honestPair_eq] using hm
  have hin : input = CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) 3) := by
    dsimp only [input]
    rw [hf, sourceMessages_bottom answers _ hi]
  have hall := recoveredSelections_canonical answers w.signature (WCT9.digestIndex output)
    input result (fun lay => CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    hin lower hsel hshape'
  refine ⟨result.digits, ?_, ?_, fun lay => (hall lay).2⟩
  · rw [hsig, hints_retained]
    exact hvalid
  · intro lay
    rw [hcs lay]
    exact (hall lay).1
#print axioms expanded_canonical_selections
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifyP_canonical_or_collision (answers : Answers) (message : Message) (pk : Digest)
    (wb : ClaudeWCT.W9.T3M.WBytes) (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (Paired.verifyP message pk wb) = true) :
    ∃ output : HashOutput,
      (wdc wb).toNat < WCT9.digestVerifyWindow ∧
      evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
      (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
        queried answers (Paired.verifyP message pk wb) ∧
      output.toNat / 2^242 % 16384 < 734 ∧
      (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
      (WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
          (entriesOf answers (queried answers (Paired.verifyP message pk wb))) ∨
        Extract.Paired.FtsHitIn answers (queried answers (Paired.verifyP message pk wb)) ∨
        ((∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
          Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
            (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))) := by
  obtain ⟨output,hc,hd,hq,hgate,hrank,hcases⟩ := verifyP_source_walk answers message pk wb hpk hv
  refine ⟨output,hc,hd,hq,hgate,hrank,?_⟩
  rcases hcases with hp | ⟨hg,hforest,hsub⟩
  · exact Or.inl hp
  · rcases Extract.Paired.forest_extract answers wb (WCT9.digestIndex output)
        (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))
        (WCT9.digestIndex_lt output) (Extract.Paired.branchCompatible_output output) hforest with ho | hh
    · exact Or.inr (Or.inr ⟨hg,ho⟩)
    · exact Or.inr (Or.inl ((Extract.Paired.forest_hit_fts answers wb (WCT9.digestIndex output)
        (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))
        (WCT9.digestIndex_lt output) hh).mono hsub))
#print axioms verifyP_canonical_or_collision
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signFromOutput_canonical_selections (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (signFromOutput cache rho counter output) = some w) :
    ∃ digits : List (List Nat),
      policyHintsValid w.signature.policyHints digits = true ∧
      (∀ lay, evalWithAnswerFn answers (WCT9.CanonicalPolicy.layerCounterSearchAt lay
        (hintFloor w.signature.policyHints lay) (route (WCT9.digestIndex output) lay).2
        (route (WCT9.digestIndex output) lay).1
        (CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
        0 (WCT9.searchLimit lay)) = some (w.counters lay,digits.getD lay.val [])) ∧
      ∀ lay, w.signature.layers lay = piecesSignature lay (WCT9.wotsPieces answers lay
        (route (WCT9.digestIndex output) lay).2 (route (WCT9.digestIndex output) lay).1
        (digits.getD lay.val [])) := by
  obtain ⟨result,hs,hrho,hhints,hforest,hpieces,hdigest,hcounters⟩ :=
    signFromOutput_components answers cache rho counter output w he
  have facts := searchPreparedLayers_some answers cache (WCT9.digestIndex output) _ _ result hs
  have hi : WCT9.digestIndex output<2^31 := WCT9.digestIndex_lt output
  refine ⟨result.digits, ?_, ?_, ?_⟩
  · rw [hhints]
    exact facts.hints_valid
  · intro lay
    rw [hhints,hcounters lay]
    have hx := facts.hinted_searches lay
    rw [buildForest_commitment] at hx
    have hm : CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay) =
        (if lay=3 then .pair (forestCommitment answers (WCT9.digestIndex output)).1
          (forestCommitment answers (WCT9.digestIndex output)).2 else
          let lower : Layer := Fin.ofNat 4 (lay.val+1)
          .pair (WCT9.builtPair answers lower (route (WCT9.digestIndex output) lower).2).1
            (WCT9.builtPair answers lower (route (WCT9.digestIndex output) lower).2).2) := by
      by_cases h3 : lay = 3
      · subst lay
        exact sourceMessages_bottom answers _ hi
      · have hl : lay.val < 3 := by
          have hn : lay.val ≠ 3 := fun h => h3 (Fin.ext h)
          have := lay.isLt
          omega
        have he : (Fin.ofNat 4 lay.val : Layer) = lay := Fin.ext (Nat.mod_eq_of_lt lay.isLt)
        have hx := sourceMessages_lower answers _ hi (lay.val+1) (by omega) (by omega)
        simpa only [if_neg h3,Nat.add_sub_cancel,he,Extract.honestPair_eq] using hx
    rw [hm]
    exact hx
  · intro lay
    rw [hpieces lay,facts.honest_pieces hcache hi lay]
#print axioms signFromOutput_canonical_selections
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security.WotsExtract (routeLeaf)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expanded_eq_signer_signature (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w signed : SigGolfCandidate.Research.SharedForest.Witness) (counter : BitVec 32)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEnc output w)
      (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (Paired.witEnc output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val)))
    (hs : evalWithAnswerFn answers (signFromOutput cache sig.rho counter output) = some signed) :
    w.signature = signed.signature := by
  have hforest := Extract.Paired.forest_openings_shape answers output w ho
  obtain ⟨_, _, _, c, _, _, _, hsig, _, _⟩ := Paired.expandN_selections answers message pk sig output w he
  have hforestSig : sig.forest = w.signature.forest := by rw [hsig];rfl
  have hf : evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest) =
      forestCommitment answers (WCT9.digestIndex output) := by
    rw [hforestSig,hforest]
    exact recoverForest_commitment answers _ _ _
  obtain ⟨da,hva,hsa,hpa⟩ := expanded_canonical_selections answers message pk sig output w he hg hf
  obtain ⟨db,hvb,hsb,hpb⟩ := signFromOutput_canonical_selections answers cache hcache sig.rho counter output signed hs
  obtain ⟨_,_,hrho,_,hfs,_,_,_⟩ := signFromOutput_components answers cache sig.rho counter output signed hs
  apply signature_unique_of_selections answers (WCT9.digestIndex output)
    (fun lay => CanonicalRef.sourceMessages answers (routeLeaf (WCT9.digestIndex output) lay))
    w.signature signed.signature w.counters signed.counters da db _ (hforest.trans hfs.symm)
    hva hvb hsa hsb hpa hpb
  rw [hsig,nonce_retained,hrho]

 theorem same_nonce_signed_wire (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (message : Message) (pk : Digest)
    (sig signedSig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, Good answers (CanonicalRef.sourceMessages answers) (Paired.witEnc output w)
      (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (Paired.witEnc output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val)))
    (hs : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload cache message) = some signedSig)
    (hrho : sig.rho = signedSig.rho) :
    SharedCodec.sigBC sig = SharedCodec.sigBC signedSig := by
  obtain ⟨counter,N,signed,hd,hsigned,hsig⟩ := signPayload_components answers cache message signedSig hs
  obtain ⟨_,_,hnonce,_,_,_,_,_⟩ := signFromOutput_components answers cache
    (evalWithAnswerFn answers (SigGolfCandidate.T3.privateNonce message)) counter N signed hsigned
  have hr : sig.rho = evalWithAnswerFn answers (SigGolfCandidate.T3.privateNonce message) :=
    hrho.trans ((congrArg (fun s : SigGolfCandidate.Research.SharedForest.Signature => s.rho) hsig).symm.trans hnonce)
  obtain ⟨_,ec,_,c,hed,_,_,hw,_,_⟩ := Paired.expandN_selections answers message pk sig output w he
  rw [hr,hd] at hed
  have hout : N=output := congrArg Prod.snd (Option.some.inj hed)
  subst N
  have heq := expanded_eq_signer_signature answers cache hcache message pk sig output w signed counter he hg ho
    (by rw [hr];exact hsigned)
  calc
    SharedCodec.sigBC sig = SharedCodec.sigBC (fillTopSignature sig c) := (SharedCodec.sigBC_fillTopSignature sig c).symm
    _ = SharedCodec.sigBC w.signature := by rw [hw]
    _ = SharedCodec.sigBC signedSig := by rw [heq,hsig]
#print axioms expanded_eq_signer_signature
#print axioms same_nonce_signed_wire
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.WPair.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

theorem fresh_witness_not_signed_digest (log : QueryLog Requests) (message : Message)
    (wb : WBytes) (rho : Digest) (hfresh : Final.Paired.Fresh log (.witness message wb)) :
    ¬ SignedDigest log message rho := by
  rintro ⟨entry,hin,hm,sig,he,_⟩
  exact hfresh ⟨entry,hin,hm,by rw [he];rfl⟩

theorem fresh_signature_not_signed_digest (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = cacheRegion (maskedTop answers)) (log : QueryLog Requests)
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (authenticatedSign published entry.1))
    (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hfresh : Final.Paired.Fresh log (.signature message sig))
    (he : evalWithAnswerFn answers (T3M.Paired.expandN message pk sig) = some (output,w))
    (hg : ∀ lay, CanonicalExtract.Good answers (CanonicalRef.sourceMessages answers)
      (T3M.Paired.witEnc output w) (WCT9.digestIndex output) lay)
    (ho : Extract.Paired.ForestOpenings answers (T3M.Paired.witEnc output w) (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun coord => WCT9.embed (forestRank output coord.val))) :
    ¬ SignedDigest log message sig.rho := by
  rintro ⟨entry,hin,hm,signed,hsigned,hrho⟩
  have hreply := hlog entry hin
  rw [hsigned,eval_authenticatedSign] at hreply
  have hsource : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signPayload published message) = some signed := by
    by_cases hc : entry.1.cache = published
    · rw [if_pos hc,hc,hm] at hreply
      exact hreply.symm
    · rw [if_neg hc] at hreply
      cases hreply
  have hwire := CanonicalExtract.same_nonce_signed_wire answers published hcache message pk sig signed output w
    he hg ho hsource hrho.symm
  apply hfresh
  refine ⟨entry,hin,hm,?_⟩
  rw [hsigned,Option.map_some,hwire]
#print axioms fresh_witness_not_signed_digest
#print axioms fresh_signature_not_signed_digest
end ClaudeWCT.W9.T3.Security.WPair.Paired

namespace ClaudeWCT.W9.T3.Security.CanonicalExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (entriesOf_mono)
open SigGolfCandidate.Research.SharedForest W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem checkForgery_canonical_or_collision (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (hcache : published.region = cacheRegion (maskedTop answers)) (pk : Digest)
    (hpk : pk = Extract.honestRoot answers 0 0) (log : QueryLog Final.Paired.Requests)
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn answers (WPair.Paired.authenticatedSign published entry.1))
    (forgery : Final.Paired.ForgeryP)
    (haccept : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true) :
    WotsPrimitiveSrc answers (CanonicalRef.sourceMessages answers)
        (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) ∨
      Extract.Paired.FtsHitIn answers (queried answers (Final.Paired.checkForgeryP pk log forgery)) ∨
      ∃ (message : Message) (wb : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
        Final.Paired.WitnessOf answers pk forgery message wb ∧
        (wdc wb).toNat < WCT9.digestVerifyWindow ∧
        evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
        (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
          queried answers (Final.Paired.checkForgeryP pk log forgery) ∧
        output.toNat / 2^242 % 16384 < 734 ∧
        (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
        (∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
        Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
          (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) ∧
        ¬ WPair.Paired.SignedDigest log message (wrho wb) := by
  obtain ⟨hfresh,message,wb,hw,hv,hsub⟩ := Final.Paired.check_accepting answers pk log forgery haccept
  obtain ⟨output,hc,hd,hq,hgate,hrank,hcases⟩ :=
    verifyP_canonical_or_collision answers message pk wb hpk hv
  rcases hcases with hp | hh | ⟨hg,ho⟩
  · exact Or.inl (hp.mono (entriesOf_mono hsub))
  · exact Or.inr (Or.inl (hh.mono hsub))
  · refine Or.inr (Or.inr ⟨message,wb,output,hw,hc,hd,hsub _ hq,hgate,hrank,hg,ho,?_⟩)
    cases forgery with
    | witness sourceMessage sourceWitness =>
        obtain ⟨hm,hb⟩ := hw
        subst sourceMessage sourceWitness
        exact WPair.Paired.fresh_witness_not_signed_digest log message wb (wrho wb) hfresh
    | signature sourceMessage sig =>
        obtain ⟨hm,he⟩ := hw
        subst sourceMessage
        obtain ⟨N,w,hn,rfl⟩ := Paired.expandB_some answers message pk sig wb he
        have hout : N = output := (Paired.expandN_digest answers message pk sig N w hn).symm.trans hd
        subst N
        rw [Paired.expandN_nonce answers message pk sig output w hn]
        exact WPair.Paired.fresh_signature_not_signed_digest answers published hcache log hlog
          message pk sig output w hfresh hn hg ho
#print axioms checkForgery_canonical_or_collision
end ClaudeWCT.W9.T3.Security.CanonicalExtract

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.CanonicalExtract
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def FreshForestAt (answers : Answers) (pk : Digest) (log : QueryLog Final.Paired.Requests)
    (forgery : Final.Paired.ForgeryP) : Prop :=
  ∃ (message : Message) (wb : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
        Final.Paired.WitnessOf answers pk forgery message wb ∧
        (wdc wb).toNat < WCT9.digestVerifyWindow ∧
        evalWithAnswerFn answers (digest (wrho wb) message (wdc wb)) = output ∧
        (.inl (.inr (pad64 (digestInput (wrho wb) message (wdc wb)))) : Spec.Domain) ∈
          queried answers (Final.Paired.checkForgeryP pk log forgery) ∧
        output.toNat / 2^242 % 16384 < 734 ∧
        (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
        (∀ lay : Layer, Good answers (CanonicalRef.sourceMessages answers) wb (WCT9.digestIndex output) lay) ∧
        Extract.Paired.ForestOpenings answers wb (WCT9.digestIndex output)
          (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) ∧
        ¬ WPair.Paired.SignedDigest log message (wrho wb)

def FreshForestCase (adversary : Final.Paired.AdversaryP)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked ∧
    generated.value.1 = Extract.honestRoot z.2 0 0 ∧
    generated.value.2.region = Correctness.cacheRegion (Correctness.maskedTop z.2) ∧
    (∀ entry ∈ interaction.value.2,
      entry.2 = evalWithAnswerFn z.2 (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    ∃ forgery, interaction.value.1 = some forgery ∧
      evalWithAnswerFn z.2 (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) = true ∧
      FreshForestAt z.2 generated.value.1 interaction.value.2 forgery

theorem completed_split_canonical (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z ∈ (PairedSeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) :
    CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z := by
  by_cases hab : CaseABEv combinedEvent adversary z
  · exact Or.inl hab
  right
  unfold CaseABEv CaseABEvAt at hab
  push Not at hab
  obtain ⟨generated,interaction,checked,hsplit,forgery,hf,hnot⟩ := hab
  obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  obtain ⟨_,hpk,hcache,hlog,hverdict⟩ := hsplit.facts z.2 ha hclean.1
  obtain ⟨forgery',hf',hcheck,_⟩ := PairedReference.Ref.verdict_accepts z.2 _ _ hverdict
  have heq : forgery' = forgery := Option.some.inj (hf'.symm.trans hf)
  subst forgery'
  rcases CanonicalExtract.checkForgery_canonical_or_collision z.2 generated.value.2 hcache
      generated.value.1 hpk interaction.value.2 hlog forgery hcheck with hp | hh | hgood
  · exact (hnot ⟨hcheck,Or.inl hp⟩).elim
  · exact (hnot ⟨hcheck,Or.inr (PairedReference.ftsHitIn_structuralHitTrace hh)⟩).elim
  · exact ⟨generated,interaction,checked,hsplit,hpk,hcache,hlog,forgery,hf,hcheck,hgood⟩
#print axioms completed_split_canonical
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem cleanWin_le_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2^127) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv combinedEvent adversary z |
        PairedSeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z |
        PairedSeccLaw.completedExperiment adversary q hq] := by
  rw [← PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) (probEvent_or_le _ _ _)
  intro z hz hclean
  rcases completed_split_canonical adversary q hq z hz hclean with hab | hf
  · exact Or.inl ⟨hclean,hab⟩
  · exact Or.inr ⟨hclean,hf⟩
#print axioms cleanWin_le_cases
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem checker_forest_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true) :
    ∀ query ∈ queried answers (SharedV3.forest w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))),
      query ∈ queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  obtain ⟨_,m',w',hw',hv,hq⟩ := Final.Paired.check_accepting answers pk log forgery hcheck
  obtain ⟨rfl,rfl⟩ := PairedReference.Ref.witnessOf_unique hw hw'
  obtain ⟨out,top,hd',hf,_,_,hqF,_⟩ := Paired.verifyP_split answers message pk w hv
  obtain ⟨_,hout,_⟩ := Paired.digestP_success answers message w out hd'
  have he : out = output := hout.symm.trans hd
  rw [he] at hf hqF
  obtain ⟨_,_,_,hforestQ⟩ := Paired.ftsP_success answers w output top hf
  intro query hquery
  exact hq query (hqF query (hforestQ ▸ hquery))

theorem checker_slot_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))
    (k : Fin 9) (t : Fin 6) (p : Fin 4) (hp : p.val = 4-WPair.Paired.deficit output k t) :
    (.inl (.inr (Guess.honestProbe answers (WPair.Paired.chainOf output k t,p))) : Spec.Domain) ∈
      queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  apply checker_forest_queries answers pk log forgery message w output hw hd hcheck
  rw [WPair.Paired.honestProbe_slot]
  have hp' : p.val = 4-WCT9.digit (WCT9.embed (forestRank output k.val)) t := hp
  rw [hp']
  apply Extract.Paired.active_slot_queried answers w (WCT9.digestIndex output)
    (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)) (WCT9.digestIndex_lt output) ho
  have hplt := p.isLt
  omega

#print axioms checker_forest_queries
#print axioms checker_slot_queries
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def FullCovered (answers : Answers) (log : QueryLog Final.Paired.Requests) (output : HashOutput) : Prop :=
  ∀ k t, WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs answers log) output k t

def NearGuess (answers : Answers) (log : QueryLog Final.Paired.Requests)
    (output : HashOutput) (trace : List SigGolfCandidate.T3.Security.Wots.Entry) : Prop :=
  ∃ (k : Fin 9) (t : Fin 6) (cell : Guess.GCoord),
    cell.1 = WPair.Paired.chainOf output k t ∧
    cell.2.val = 4-WPair.Paired.deficit output k t ∧
    WPair.Paired.GuessedIn answers log trace cell ∧
    ∀ k' t', (k',t') ≠ (k,t) →
      WPair.Paired.SlotCovered (WPair.Paired.loggedOutputs answers log) output k' t'

def PairGuessIn (answers : Answers) (log : QueryLog Final.Paired.Requests)
    (trace : List SigGolfCandidate.T3.Security.Wots.Entry) : Prop :=
  ∃ cell cell' : Guess.GCoord, cell.1 ≠ cell'.1 ∧
    WPair.Paired.GuessedIn answers log trace cell ∧ WPair.Paired.GuessedIn answers log trace cell'

theorem checker_coverage_cases (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) :
    FullCovered answers log output ∨
      NearGuess answers log output (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) ∨
      PairGuessIn answers log (entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))) := by
  let trace := entriesOf answers (queried answers (Final.Paired.checkForgeryP pk log forgery))
  let slot (k : Fin 9) (t : Fin 6) (ha : 1 ≤ WPair.Paired.deficit output k t) : Guess.GCoord :=
    (WPair.Paired.chainOf output k t,⟨4-WPair.Paired.deficit output k t,by omega⟩)
  have make (k : Fin 9) (t : Fin 6) (ha : 1 ≤ WPair.Paired.deficit output k t)
      (hu : ¬WPair.Paired.ChainCovered (WPair.Paired.loggedOutputs answers log)
        (WPair.Paired.chainOf output k t) (4-WPair.Paired.deficit output k t)) :
      WPair.Paired.GuessedIn answers log trace (slot k t ha) := by
    refine ⟨hu,answers (.inl (.inr (Guess.honestProbe answers (slot k t ha)))),?_⟩
    exact WotsExtract.mem_entriesOf (checker_slot_queries answers pk log forgery message w output
      hw hd hcheck ho k t (slot k t ha).2 rfl)
  rcases WPair.Paired.caseC_slots (WPair.Paired.loggedOutputs answers log) output with
    hall | ⟨k,t,ha,hu,hrest⟩ | ⟨k,t,k',t',hne,ha,hu,ha',hu'⟩
  · exact Or.inl hall
  · exact Or.inr (Or.inl ⟨k,t,slot k t ha,rfl,rfl,make k t ha hu,hrest⟩)
  · exact Or.inr (Or.inr ⟨slot k t ha,slot k' t' ha',WPair.Paired.chainOf_ne hne,
      make k t ha hu,make k' t' ha' hu'⟩)
#print axioms checker_coverage_cases
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT


namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The fully covered fresh-forest case, restricted to complete source tables. -/
def FullForestEvent (adversary : Final.Paired.AdversaryP) (q : Nat)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  y.1=true ∧ countOf y.2≤q ∧
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    interaction.value.2.length≤2^32 ∧
    (∀ entry∈interaction.value.2,entry.2=evalWithAnswerFn A
      (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    (∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature) ∧
    ∃ (forgery : Final.Paired.ForgeryP) (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
      interaction.value.1=some forgery ∧
      evalWithAnswerFn A (digest (wrho w) message (wdc w))=output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) ∧
      output.toNat/2^242%16384<734 ∧
      (∀ k : Fin 9,rawForestRank output k.val<563) ∧
      ¬WPair.Paired.SignedDigest interaction.value.2 message (wrho w) ∧
      FullCovered A interaction.value.2 output

theorem paired_recordMatches (published : SigGolfCandidate.T3.Cache) (request : Request) :
    Prod.fst <$> ClaudeWCT.Bank.Paired.bankSpec.authenticatedRecord
      ClaudeWCT.Bank.Paired.payAfterDigest published request =
        PairedOuter.FullGame.authenticatedSign published request :=
  ClaudeWCT.Bank.Paired.record_erasure published request

theorem paired_bank_search (rho : Digest) (message : Message) :
    ClaudeWCT.Bank.Paired.bankSpec.search rho message 0 ClaudeWCT.Bank.Paired.bankSpec.limit =
      sharedDigestSearch rho message 0 WCT9.digestAttemptLimit :=
  (ClaudeWCT.Bank.Paired.digestSearch_public rho message WCT9.digestAttemptLimit 0).symm

theorem paired_bank_covered (X : List HashOutput) (N : HashOutput)
    (h : ∀ k t, WPair.Paired.SlotCovered X N k t) :
    ClaudeWCT.Bank.Paired.bankSpec.covered X N := by
  apply (ClaudeWCT.Bank.Paired.covered_source X N).mpr
  exact h

theorem full_event_potential (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    1≤ClaudeWCT.Bank.Paired.bankSpec.potential q b.2 := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hcover⟩ := hfull
  obtain ⟨prior,hprior⟩ := hsplit.checker_event A hA forgery hforgery _ hquery
  have hevent := hsplit.checked_mem hprior
  change evalWithAnswerFn A (digest (wrho w) message (wdc w))=N at hN
  have hevent' : (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),N⟩ :
      FirstHit.QueryEvent)∈b.2.2.events := by
    change (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),
      evalWithAnswerFn A (digest (wrho w) message (wdc w))⟩ : FirstHit.QueryEvent)∈_ at hevent
    rwa [hN] at hevent
  apply PairedBankLink.full_potential ClaudeWCT.Bank.Paired.bankSpec
    ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches
    ClaudeWCT.Bank.Paired.payHashOnly ClaudeWCT.Bank.Paired.payRho ClaudeWCT.Bank.Paired.payAvoids
    paired_bank_search paired_bank_covered adversary q hq b hb A hA hcount
    generated interaction checked hsplit hlen
    (pad64 (digestInput (wrho w) message (wdc w))) N ⟨wrho w,message,wdc w,rfl⟩ prior hevent'
  · exact WPair.Paired.fresh_digest_not_signer_eval A generated.value.2 interaction.value.2 hsig
      message (wrho w) (wdc w) hcomp hfresh
  · change ClaudeWCT.Bank.Paired.admissible N=true
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
  · exact hcover

theorem completed_full_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (rate : ENNReal)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W => ClaudeWCT.Bank.Paired.price W-(1023/1024 : ENNReal))≤rate) :
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      (CaseC.theta+1/64)/2^128 * PairedSeccLaw.expectedCharge adversary q hq
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) +
      (q : ENNReal)*rate/2^128 := by
  apply PairedBankLink.completed_event_le_shared ClaudeWCT.Bank.Paired.bankSpec
    ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches ClaudeWCT.Bank.Paired.payNotDigest
    ClaudeWCT.Bank.Paired.payAvoids (FullForestEvent adversary q) adversary q hq rate hrate
  intro b hb tables hfull
  exact full_event_potential adversary q hq b hb _
    (fun input answer hk => SigGolfCandidate.T3.Security.SeccLaw.completeWith_agrees _ tables input answer hk) hfull
#print axioms full_event_potential
#print axioms completed_full_bound
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem full_event_target_covered (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    b.2.1.dead=false ∧ ∃ N∈b.2.1.targets, ClaudeWCT.Bank.Paired.admissible N=true ∧
      ClaudeWCT.Bank.Paired.Covered b.2.1.exposures N := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hcover⟩ := hfull
  obtain ⟨prior,hprior⟩ := hsplit.checker_event A hA forgery hforgery _ hquery
  have hevent := hsplit.checked_mem hprior
  change evalWithAnswerFn A (digest (wrho w) message (wdc w))=N at hN
  have hevent' : (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),N⟩ :
      FirstHit.QueryEvent)∈b.2.2.events := by
    change (⟨prior,.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))),
      evalWithAnswerFn A (digest (wrho w) message (wdc w))⟩ : FirstHit.QueryEvent)∈_ at hevent
    rwa [hN] at hevent
  have hadm : ClaudeWCT.Bank.Paired.admissible N=true := by
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
  have hc : b.2.1.dead=false ∧ N∈b.2.1.targets ∧
      ClaudeWCT.Bank.Paired.bankSpec.covered b.2.1.exposures N := by
    apply PairedBankLink.full_target_covered ClaudeWCT.Bank.Paired.bankSpec
      ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches
      ClaudeWCT.Bank.Paired.payHashOnly ClaudeWCT.Bank.Paired.payRho ClaudeWCT.Bank.Paired.payAvoids
      paired_bank_search paired_bank_covered adversary q hq b hb A hA hcount
      generated interaction checked hsplit hlen
      (pad64 (digestInput (wrho w) message (wdc w))) N ⟨wrho w,message,wdc w,rfl⟩ prior hevent'
    · exact WPair.Paired.fresh_digest_not_signer_eval A generated.value.2 interaction.value.2 hsig
        message (wrho w) (wdc w) hcomp hfresh
    · change ClaudeWCT.Bank.Paired.admissible N=true
      rw [ClaudeWCT.Bank.Paired.admissible_source]
      simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks
    · exact hcover
  
  exact ⟨hc.1,N,hc.2.1,hadm,hc.2.2⟩

theorem full_event_flexible_potential (theta : ENNReal)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (b : Bool × PairedBankLink.PairedBankState)
    (hb : b∈(ClaudeWCT.Bank.Paired.bankSpec.bankExperiment ClaudeWCT.Bank.Paired.payAfterDigest
      (PairedBankLink.rest adversary) q).support)
    (A : Answers) (hA : Agrees A (lazyOf b.2.2))
    (hfull : FullForestEvent adversary q (b.1,b.2.2) A) :
    1≤ClaudeWCT.Bank.Paired.flexiblePotential theta q b.2 := by
  obtain ⟨halive,N,hN,hadm,hcov⟩ := full_event_target_covered adversary q hq b hb A hA hfull
  exact ClaudeWCT.Bank.Paired.flexible_potential_win theta q b.2 halive hfull.2.1
    (Or.inr ⟨N,hN,hadm,hcov⟩)

theorem completed_flexible_full_bound (theta rate : ENNReal)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W => ClaudeWCT.Bank.Paired.price W-theta)≤rate) :
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      (theta+1/1024)/2^128 * PairedSeccLaw.expectedCharge adversary q hq
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) +
      (q : ENNReal)*rate/2^128 := by
  rw [PairedBankLink.completed_event_eq]
  have he := congrArg (fun law : PMF (Bool × QueryRecorded.State) =>
    expectedValue law (PairedBankLink.completedWeight (FullForestEvent adversary q)))
      (PairedBankLink.recordedExperiment_eq ClaudeWCT.Bank.Paired.bankSpec
        ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches adversary q hq)
  rw [PMF.monad_map_eq_map,CaseC.expectedValue_pmf_map] at he
  rw [he]
  refine (ClaudeWCT.Bank.Paired.flexible_event_le theta rate hrate (PairedBankLink.rest adversary) q
    (PairedBankLink.completedWeight (FullForestEvent adversary q)) (fun _ => probEvent_le_one) ?_).trans ?_
  · intro b hb hnonzero
    by_cases hex : ∃ tables, FullForestEvent adversary q (b.1,b.2.2)
        (SigGolfCandidate.T3.Security.SeccLaw.completeWith (lazyOf b.2.2) tables)
    · obtain ⟨tables,ht⟩ := hex
      exact full_event_flexible_potential theta adversary q hq b hb _
        (fun input answer hk => SigGolfCandidate.T3.Security.SeccLaw.completeWith_agrees _ tables input answer hk) ht
    · exfalso
      apply hnonzero
      unfold PairedBankLink.completedWeight
      simp only [probEvent_eq_tsum_ite]
      have hfalse : ∀ tables, ¬FullForestEvent adversary q (b.1,b.2.2)
          (SigGolfCandidate.T3.Security.SeccLaw.completeWith (lazyOf b.2.2) tables) :=
        fun tables ht => hex ⟨tables,ht⟩
      simp [hfalse]
  · exact add_le_add (mul_le_mul' le_rfl
      (PairedBankLink.expectedBirths_le_shared ClaudeWCT.Bank.Paired.bankSpec
        ClaudeWCT.Bank.Paired.payAfterDigest paired_recordMatches adversary q hq)) le_rfl
#print axioms completed_flexible_full_bound
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf Agrees)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The remaining fresh-forest cases, with a predicate on the actual checker trace. -/
def PartialForestEvent
    (Q : Answers → QueryLog Final.Paired.Requests → HashOutput → List Entry → Prop)
    (adversary : Final.Paired.AdversaryP) (q : Nat)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  y.1=true ∧ countOf y.2≤q ∧
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    interaction.value.2.length≤2^32 ∧
    (∀ entry∈interaction.value.2,entry.2=evalWithAnswerFn A
      (PairedOuter.FullGame.authenticatedSign generated.value.2 entry.1)) ∧
    (∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature) ∧
    ∃ (forgery : Final.Paired.ForgeryP) (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput),
      interaction.value.1=some forgery ∧
      evalWithAnswerFn A (digest (wrho w) message (wdc w))=output ∧
      (.inl (.inr (pad64 (digestInput (wrho w) message (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∈
        queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery) ∧
      output.toNat/2^242%16384<734 ∧
      (∀ k : Fin 9,rawForestRank output k.val<563) ∧
      ¬WPair.Paired.SignedDigest interaction.value.2 message (wrho w) ∧
      Q A interaction.value.2 output
        (entriesOf A (queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery)))

abbrev NearForestEvent := PartialForestEvent NearGuess
abbrev PairForestEvent := PartialForestEvent (fun A log _ => PairGuessIn A log)

def IncompleteForestEvent (adversary : Final.Paired.AdversaryP)
    (y : Bool × QueryRecorded.State) (A : Answers) : Prop :=
  ∃ generated interaction checked,
    PairedReference.GameSplit adversary ⟨y.1,y.2.events,lazyOf y.2⟩ generated interaction checked ∧
    ¬∀ message, ∃ signature, evalWithAnswerFn A
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature

theorem completed_forest_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1)
    (hfresh : FreshForestCase adversary z) :
    FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
    IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 := by
  obtain ⟨generated,interaction,checked,hsplit,hpk,hcache,hsig,forgery,hforgery,hcheck,
    message,w,N,hw,hctr,hN,hquery,hgate,hranks,hgood,hopen,hfresh⟩ := hfresh
  by_cases hcomp : ∀ message, ∃ signature, evalWithAnswerFn z.2
      (SigGolfCandidate.Research.SharedForest.signPayload generated.value.2 message)=some signature
  · obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
    obtain ⟨_,_,_,_,hverdict⟩ := hsplit.facts z.2 ha hclean.1
    have hlen : interaction.value.2.length≤2^32 := by
      simp only [PairedOuter.GameWith.verdict,hforgery,PairedOuter.PaddedGame.checker,
        evalWithAnswerFn_bind,evalWithAnswerFn_pure,Bool.and_eq_true,decide_eq_true_eq] at hverdict
      exact hverdict.1
    rcases checker_coverage_cases z.2 generated.value.1 interaction.value.2 forgery
      message w N hw hN hcheck hopen with hc | hc | hc
    · exact Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩
    · exact Or.inr (Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hclean.1,hclean.2.1,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
        forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨generated,interaction,checked,hsplit,hcomp⟩))

#print axioms completed_forest_cases
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem completed_forest_le_cases (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
    Pr[fun z => FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z => IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq] := by
  have h := Ref.pmf_probEvent_mono (PairedSeccLaw.completedExperiment adversary q hq)
    (fun z hz (h : QueryRecorded.CleanWin q z.1 ∧ FreshForestCase adversary z) =>
      completed_forest_cases adversary q hq z hz h.1 h.2)
  refine h.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ = _ := by ac_rfl
#print axioms completed_forest_le_cases
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem GameSplit.unique_log_events {adversary : Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool}
    {generated generated' : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction interaction' : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests)}
    {checked checked' : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked)
    (h' : GameSplit adversary result generated' interaction' checked') :
    generated=generated' ∧ interaction=interaction' ∧ checked.events=checked'.events := by
  have hev : result.events=generated'.events++(interaction'.events++checked'.events) := by rw [h'.2.2.2]
  obtain ⟨hg,hi⟩ := PairedBankLink.split_unique adversary result generated' h'.1 interaction' h'.2.1
    checked'.events hev generated interaction checked h
  refine ⟨hg,hi,?_⟩
  have hev' : result.events=generated.events++(interaction.events++checked.events) := by rw [h.2.2.2]
  rw [hg,hi] at hev'
  exact List.append_cancel_left (List.append_cancel_left (hev'.symm.trans hev))

theorem GameSplit.checker_entries {adversary : Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option Final.Paired.ForgeryP × QueryLog Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    (A : Answers) (hA : CaseC.Agrees A result.state)
    (forgery : Final.Paired.ForgeryP) (hf : interaction.value.1=some forgery) :
    ∀ entry∈SigGolfCandidate.T3.Security.Wots.entriesOf A
      (queried A (Final.Paired.checkForgeryP generated.value.1 interaction.value.2 forgery)),
      entry∈BPair.publicEntries checked.events := by
  rintro ⟨input,answer⟩ he
  obtain ⟨hq,ha⟩ := SigGolfCandidate.T3.Security.WotsExtract.mem_entriesOf_iff.mp he
  obtain ⟨prior,hprior⟩ := h.checker_event A hA forgery hf _ hq
  have hm := SigGolfCandidate.T3.Security.CaseC.mem_publicEntries hprior
  rwa [ha] at hm
#print axioms GameSplit.unique_log_events
#print axioms GameSplit.checker_entries
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_pair_implies (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hpair : PairForestEvent adversary q (z.1.1,z.1.2.2) z.2) :
    WPair.Paired.PairGuess adversary z := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hpair⟩ := hpair
  intro generated' interaction' checked' hsplit'
  obtain ⟨_,hi,hc⟩ := hsplit.unique_log_events hsplit'
  rw [←hi,←hc]
  obtain ⟨_,ha⟩ := PairedSeccLaw.completed_agrees adversary q hq z hz
  have hsub := hsplit.checker_entries z.2 ha forgery hforgery
  obtain ⟨cell,cell',hne,hg,hg'⟩ := hpair
  exact ⟨cell,cell',hne,WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell hg,
    WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell' hg'⟩

theorem completed_pair_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => PairForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤ BPair.pairTerm q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans (WPair.Paired.pair_guess_bound_budget adversary q hq)
  intro z hz h
  exact ⟨h.1.2.1,completed_pair_implies adversary q hq z hz h.1,h.2⟩
#print axioms completed_pair_implies
#print axioms completed_pair_bound
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_near_implies (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hnear : NearForestEvent adversary q (z.1.1,z.1.2.2) z.2)
    (generated' interaction' checked')
    (hsplit' : PairedReference.GameSplit adversary (QueryRecorded.recordedTrace z.1)
      generated' interaction' checked') :
    WPair.Paired.NearIn z.2 interaction'.value.2 (BPair.publicEntries checked'.events) := by
  obtain ⟨hwin,hcount,generated,interaction,checked,hsplit,hlen,hsig,hcomp,
    forgery,message,w,N,hforgery,hN,hquery,hgate,hranks,hfresh,hnear⟩:=hnear
  obtain ⟨_,hi,hc⟩:=hsplit.unique_log_events hsplit'
  rw [←hi,←hc]
  obtain ⟨_,ha⟩:=PairedSeccLaw.completed_agrees adversary q hq z hz
  have hsub:=hsplit.checker_entries z.2 ha forgery hforgery
  obtain ⟨k,t,cell,hcell,hdepth,hguess,hcover⟩:=hnear
  refine ⟨hlen,WPair.Paired.cacheCompleteLog_of_complete z.2 generated.value.2
    interaction.value.2 hsig hcomp,message,wrho w,wdc w,N,cell,?_,?_,hfresh,
    WPair.Paired.guessedIn_mono z.2 interaction.value.2 _ _ hsub cell hguess,k,t,hcover⟩
  · apply hsub
    rw [←hN]
    exact SigGolfCandidate.T3.Security.WotsExtract.mem_entriesOf hquery
  · rw [ClaudeWCT.Bank.Paired.admissible_source]
    simpa only [Bool.and_eq_true,decide_eq_true_eq,ranksAccepted_iff] using And.intro hgate hranks

variable {P : Type} [Fintype P] [SampleableType P]

theorem completed_near_bound (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,WPair.Paired.NearCovers X N → S.covered X N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128) := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.near_bound_budget S hproducer hadmissible hmono hcovered rate hrate adversary q hq)
  intro z hz h
  exact ⟨h.1.2.1,fun generated interaction checked hs=>
    ⟨completed_near_implies adversary q hq z hz h.1 generated interaction checked hs,
      h.2 generated interaction checked hs⟩⟩

#print axioms completed_near_implies
#print axioms completed_near_bound
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
theorem prefixClassCount_le_length (s : RefSample) : Contacts.prefixClassCount s ≤ s.trace.length :=
  List.length_filter_le _ _
theorem contactAt_maskAt_source (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain7 a)
    (hb : WotsExtract.SourceChain7 b) : ContactAt (maskAt T a) trace b ↔ ContactAt T trace b := by
  unfold ContactAt maskAt CanonicalRef.ContactAt
  rw [CanonicalRef.depth_source_maskAt T a b (Or.inr (source_bounds ha).2),
    CanonicalRef.frontierValue_source_maskAt T a b (source_bounds ha) (source_bounds hb) hb.2]
def OtherContact (a : ChainAddr) (T : Answers) (trace : List Entry) : Prop :=
  ∃ b, WotsExtract.SourceChain7 b ∧ b ≠ a ∧ ContactAt T trace b
theorem otherContact_maskAt (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) (T : Answers) (trace : List Entry) :
    OtherContact a (maskAt T a) trace ↔ OtherContact a T trace := by
  unfold OtherContact
  constructor
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mp h⟩
  · rintro ⟨b, hb, hne, h⟩
    exact ⟨b, hb, hne, (contactAt_maskAt_source T trace a b ha hb).mpr h⟩
theorem contactAt_take_length (T : Answers) (trace : List Entry) (a : ChainAddr) (h : ContactAt T trace a) :
    ∃ k, ContactAt T (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact h⟩
theorem first_contact_entry (T : Answers) (tr : List Entry) (a : ChainAddr) (k : Nat)
    (hk : ContactAt T (tr.take (k + 1)) a) (hn : ¬ContactAt T (tr.take k) a) :
    ∃ value answer, tr[k]? = some (chainRow a (depth T a - 1) value, answer) := by
  obtain ⟨hd, value, answer, hm, hl⟩ := hk
  refine ⟨value, answer, ?_⟩
  rw [List.take_add_one, List.mem_append] at hm
  rcases hm with hm | hm
  · exact absurd ⟨hd, value, answer, hm, hl⟩ hn
  · cases h : tr[k]? with
    | none => rw [h] at hm; simp at hm
    | some e => rw [h] at hm; simp only [Option.toList_some, List.mem_singleton] at hm; exact congrArg some hm.symm
theorem twoContacts_cases (T : Answers) (trace : List Entry) (a b : ChainAddr) (ha : WotsExtract.SourceChain7 a)
    (hb : WotsExtract.SourceChain7 b) (hab : a ≠ b) (hca : ContactAt T trace a) (hcb : ContactAt T trace b) :
    ContactAfterStop (OtherContact a) T trace a ∨ ContactAfterStop (OtherContact b) T trace b := by
  classical
  let ka := Nat.find (contactAt_take_length T trace a hca)
  let kb := Nat.find (contactAt_take_length T trace b hcb)
  have hka : ContactAt T (trace.take ka) a := Nat.find_spec (contactAt_take_length T trace a hca)
  have hkb : ContactAt T (trace.take kb) b := Nat.find_spec (contactAt_take_length T trace b hcb)
  have hma : ∀ j < ka, ¬ContactAt T (trace.take j) a := fun j hj => Nat.find_min _ hj
  have hmb : ∀ j < kb, ¬ContactAt T (trace.take j) b := fun j hj => Nat.find_min _ hj
  rcases lt_trichotomy ka kb with hlt | heq | hgt
  · exact Or.inr ⟨ka, ⟨a, ha, hab, hka⟩, hmb ka hlt, hcb⟩
  · exfalso
    have hpos : 0 < ka := by
      by_contra h0
      have : ka = 0 := by omega
      rw [this] at hka
      obtain ⟨_, _, _, hm, _⟩ := hka
      simp at hm
    obtain ⟨k, hk⟩ : ∃ k, ka = k + 1 := ⟨ka - 1, by omega⟩
    have hka' : ContactAt T (trace.take (k + 1)) a := by rw [← hk]; exact hka
    have hkb' : ContactAt T (trace.take (k + 1)) b := by rw [← hk, heq]; exact hkb
    have ea := first_contact_entry T trace a k hka' (hma k (by omega))
    have eb := first_contact_entry T trace b k hkb' (hmb k (by omega))
    obtain ⟨va, wa, hea⟩ := ea
    obtain ⟨vb, wb, heb⟩ := eb
    rw [hea] at heb
    have hrow := congrArg Prod.fst (Option.some.inj heb)
    simp only at hrow
    have hda : 1 ≤ depth T a := hca.1
    have hdb : 1 ≤ depth T b := hcb.1
    exact hab (Contacts.prefixRowAt_unique (answers := T) ha hb ⟨_, va, by change depth T a - 1 < depth T a; omega, rfl⟩ ⟨_, vb, by change depth T b - 1 < depth T b; omega, hrow⟩)
  · exact Or.inl ⟨kb, ⟨b, hb, hab.symm, hkb⟩, hma kb hgt, hca⟩
theorem otherContact_take_count (s : RefSample) (a : ChainAddr)
    (h : ∃ k, OtherContact a s.answers (s.trace.take k)) : 1 ≤ Contacts.contactCount s := by
  obtain ⟨k, b, hb, -, hc⟩ := h
  unfold Contacts.contactCount
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨(Contacts.mem_sourceChains7 b).mpr hb, ?_⟩⟩
  obtain ⟨hd, value, answer, hm, hl⟩ := hc
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩
theorem otherContact_stopL (a : ChainAddr) (ha : WotsExtract.SourceChain7 a) :
    ∀ T T', CanonicalRef.Leaf.Congr (sourceMessages T) a.key T T' → ∀ trace, OtherContact a T' trace ↔ OtherContact a T trace := by
  intro T T' hC trace
  unfold OtherContact
  exact exists_congr fun b => and_congr_right fun hb => and_congr_right fun _ =>
    contactAt_leafCongr hC (source_bounds ha).2 (source_bounds ha).1 trace hb
/-- `(2^128 + 2q) T / ((1 - x) 2^128) = (1 + 2x) / (1 - x) · T`. -/
theorem big_div_mul (q : Nat) (T : ENNReal) :
    ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * T / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) =
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * T := by
  have h1 : (2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]
  have e : ∀ y : ENNReal, ((2 : ENNReal) ^ 128 + ((2 * q : ℕ) : ENNReal)) * T * (y * ((2 : ENNReal) ^ 128)⁻¹) =
      y * T * ((2 : ENNReal) ^ 128 * ((2 : ENNReal) ^ 128)⁻¹) + 2 * ((q : ENNReal) * ((2 : ENNReal) ^ 128)⁻¹) * y * T := by
    intro y
    push_cast
    ring
  rw [e, h1]
  ring
theorem reference_twoContacts_le_raw (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      (((2 * q : ℕ) : ENNReal) *
          (((2 / 2 ^ 128) * (∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)) +
              (1 + (2 / 2 ^ 128) * q) * Contacts.errTot adversary q) /
            (1 - (q : ENNReal) / 2 ^ 128)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * Contacts.errTot adversary q) /
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hne : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hpos (by simp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      ∑ a ∈ Contacts.sourceChains7, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
        PairedReference.referenceExperiment adversary q] := by
    refine le_trans ?_ (probEvent_exists_finset_le_sum Contacts.sourceChains7 (PairedReference.referenceExperiment adversary q)
        (fun a s => ContactAfterStop (OtherContact a) s.answers s.trace a))
    apply pmf_probEvent_mono
    rintro s - ⟨a, b, ha, hb, hab, hca, hcb⟩
    rcases twoContacts_cases s.answers s.trace a b ha hb hab hca hcb with h | h
    · exact ⟨a, (Contacts.mem_sourceChains7 a).mpr ha, h⟩
    · exact ⟨b, (Contacts.mem_sourceChains7 b).mpr hb, h⟩
  have hcharge := fun a (ha : a ∈ Contacts.sourceChains7) =>
    source_contactAfterStop_charge (adversary := adversary) q ((Contacts.mem_sourceChains7 a).mp ha) (OtherContact a)
      (otherContact_maskAt a ((Contacts.mem_sourceChains7 a).mp ha)) (otherContact_stopL a ((Contacts.mem_sourceChains7 a).mp ha)) hq
  have halloc : ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
        (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) ≤
      ((2 * q : ℕ) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal) := by
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro s
    by_cases hs : s ∈ (PairedReference.referenceExperiment adversary q).support
    · rw [← Finset.mul_sum]
      have hpoint : ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0) ≤
          ((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
        calc ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
              (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
            ≤ ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul' le_rfl
              by_cases h : ∃ k, OtherContact a s.answers (s.trace.take k)
              · rw [if_pos h]
                exact_mod_cast otherContact_take_count s a h
              · rw [if_neg h]
                exact bot_le
          _ = ((2 * ∑ a ∈ Contacts.sourceChains7, prefixCount a s : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              rw [← Finset.sum_mul, Finset.mul_sum, Nat.cast_sum]
          _ ≤ ((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal) := by
              apply mul_le_mul' _ le_rfl
              have h1 := Contacts.prefixCount_sum_le s
              have h2 := prefixClassCount_le_length s
              have h3 := Core.ref_trace_length_le adversary q s hs
              exact_mod_cast (by omega : 2 * ∑ a ∈ Contacts.sourceChains7, prefixCount a s ≤ 2 * q)
      calc PairedReference.referenceExperiment adversary q s * ∑ a ∈ Contacts.sourceChains7, ((2 * prefixCount a s : ℕ) : ENNReal) *
            (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)
          ≤ PairedReference.referenceExperiment adversary q s * (((2 * q : ℕ) : ENNReal) * (Contacts.contactCount s : ENNReal)) :=
            mul_le_mul' le_rfl hpoint
        _ = ((2 * q : ℕ) : ENNReal) * (PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal)) := by ring
    · rw [(PMF.apply_eq_zero_iff _ s).mpr hs]
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  calc Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] *
        ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
      ≤ (∑ a ∈ Contacts.sourceChains7, Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a |
          PairedReference.referenceExperiment adversary q]) * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ Contacts.sourceChains7, (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) *
          Pr[fun s => ContactAfterStop (OtherContact a) s.answers s.trace a | PairedReference.referenceExperiment adversary q]) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ Contacts.sourceChains7, (∑' s, PairedReference.referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * Core.errC adversary q a) :=
        Finset.sum_le_sum fun a ha => hcharge a ha
    _ = ∑ a ∈ Contacts.sourceChains7, ∑' s, PairedReference.referenceExperiment adversary q s *
          (((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, OtherContact a s.answers (s.trace.take k) then 1 else 0)) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * Contacts.errTot adversary q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
    _ ≤ ((2 * q : ℕ) : ENNReal) * ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.contactCount s : ENNReal) +
          ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * Contacts.errTot adversary q := add_le_add halloc le_rfl
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (Contacts.reference_contacts_cost_le adversary q hq)) le_rfl
theorem reference_twoContacts_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
        ContactAt s.answers s.trace a ∧ ContactAt s.answers s.trace b | PairedReference.referenceExperiment adversary q] ≤
      (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) *
          (∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * Contacts.errTot adversary q := by
  refine (reference_twoContacts_le_raw adversary q hq).trans (le_of_eq ?_)
  rw [ENNReal.add_div, big_div_mul]
  set E := ∑' s, PairedReference.referenceExperiment adversary q s * (Contacts.prefixClassCount s : ENNReal)
  set T := Contacts.errTot adversary q
  set y := 1 - (q : ENNReal) / 2 ^ 128
  have hy0 : y ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt), pow_two, ENNReal.mul_inv (Or.inl hy0) (Or.inl hyt)]
  push_cast
  ring

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem probEvent_le_six_split {α : Type} (p : PMF α) (E A₁ A₂ A₃ A₄ A₅ A₆ : α → Prop)
    (h : ∀ x, E x → A₁ x ∨ A₂ x ∨ A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x) (a b : ENNReal) (hab : a + b = 1) :
    Pr[E | p] ≤ Pr[A₁ | p] + Pr[A₂ | p] +
      (a * (Pr[A₃ | p] + Pr[A₄ | p] + Pr[A₅ | p] + Pr[A₆ | p]) +
        b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]) := by
  refine (probEvent_mono'' h).trans ?_
  refine (probEvent_or_le _ _ _).trans ?_
  simp only [add_assoc]
  gcongr
  refine (probEvent_or_le _ _ _).trans ?_
  gcongr
  calc Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p]
      = (a + b) * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := by rw [hab, one_mul]
    _ = a * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] +
          b * Pr[fun x => A₃ x ∨ A₄ x ∨ A₅ x ∨ A₆ x | p] := add_mul _ _ _
    _ ≤ _ := by
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      refine (probEvent_or_le _ _ _).trans ?_
      gcongr
      exact probEvent_or_le _ _ _

noncomputable def prefixCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  w *
    (((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
        (1 - (q : ENNReal) / 2 ^ 128) +
      4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      2 * 93 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)) +
    v * 2 / (1 - (q : ENNReal) / 2 ^ 128)
noncomputable def encodingCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  7 / 4 + w * 2 * 5022 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
/-- Coefficient of the total seed-test error `Leaf.errTot` in the small-route primitive bound (campaign X1 B3). -/
noncomputable def errCoeff (q : Nat) (w v : ENNReal) : ENNReal :=
  w *
    ((1 + twoEdgeRate q * q) / (1 - (q : ENNReal) / 2 ^ 128) +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) +
      93 * ((q : ENNReal) / 2 ^ 128) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))) +
    v * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))

theorem weighted_union_le {α : Type} (law : PMF α)
    (E Failed Match Structural TwoEdge TwoContacts MarkerFirst ContactFirst : α → Prop)
    (q : Nat) (w v EP EE EO error : ENNReal) (hwv : w+v=1)
    (hsplit : ∀ s, E s → Failed s ∨ Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s)
    (hmatch : Pr[Match | law] ≤ 7/(4*2^128) * EE)
    (hstruct : Pr[Structural | law] ≤ (2^128:ENNReal)⁻¹ * EO)
    (hedge : Pr[TwoEdge | law] ≤ (twoEdgeRate q * EP + (1+twoEdgeRate q*q)*error)/(1-(q:ENNReal)/2^128))
    (htwo : Pr[TwoContacts | law] ≤
      (4*((q:ENNReal)/2^128)/2^128)*EP/(1-(q:ENNReal)/2^128)^2 +
      (2*((q:ENNReal)/2^128)*(1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)^2 +
        (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128))*error)
    (hmarker : Pr[MarkerFirst | law] ≤
      2*((q:ENNReal)/2^128)/(1-(q:ENNReal)/2^128)*((5022/2^128)*EE) +
      (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)*error)
    (hcontact : Pr[ContactFirst | law] ≤
      93*((q:ENNReal)/2^128)*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)))
    (hany : Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s | law] ≤
      ((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)) :
    Pr[E | law] ≤ Pr[Failed | law] + prefixCoeff q w v/2^128*EP +
      encodingCoeff q w v/2^128*EE + (2^128:ENNReal)⁻¹*EO + errCoeff q w v*error := by
  have h0 : Pr[E | law] ≤ Pr[Failed | law] +
      Pr[fun s => Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s | law] :=
    (probEvent_mono'' hsplit).trans (probEvent_or_le _ _ _)
  have h1 := probEvent_le_six_split law
    (fun s => Match s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirst s ∨ ContactFirst s)
    Match Structural TwoEdge TwoContacts MarkerFirst ContactFirst (fun _ h => h) w v hwv
  refine (h0.trans (add_le_add le_rfl h1)).trans ?_
  calc _ ≤ Pr[Failed | law] +
      ((7/(4*2^128):ENNReal)*EE + (2^128:ENNReal)⁻¹*EO +
      (w*((twoEdgeRate q*EP+(1+twoEdgeRate q*q)*error)/(1-(q:ENNReal)/2^128) +
      ((4*((q:ENNReal)/2^128)/2^128)*EP/(1-(q:ENNReal)/2^128)^2 +
      (2*((q:ENNReal)/2^128)*(1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)^2 +
        (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128))*error) +
      (2*((q:ENNReal)/2^128)/(1-(q:ENNReal)/2^128)*((5022/2^128)*EE) +
      (1+2*((q:ENNReal)/2^128))/(1-(q:ENNReal)/2^128)*error) +
      93*((q:ENNReal)/2^128)*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128))) +
      v*(((2/2^128)*EP+(1+(2/2^128)*q)*error)/(1-(q:ENNReal)/2^128)))) := by
        gcongr
    _ = _ := by
      unfold prefixCoeff encodingCoeff errCoeff twoEdgeRate
      simp only [div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (by norm_num : (4:ENNReal)≠0)) (Or.inl (by norm_num : (4:ENNReal)≠⊤))]
      ring
#print axioms weighted_union_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel (TSpec Free evalT seedsY seedsR seedsH amLen)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate observedRun realRun Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] raw normalize answers RawPrefix.fill RawLeaf.ovL
variable {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
abbrev MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ContactAfterStop (fun T trace => MarkerAt T trace a) T trace a
theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain7 a) : ∃ p, Enc.chainAt p = a := by
  have ht := ha.1.tree_lt
  obtain ⟨⟨-, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (SigGolfCandidate.T3M.Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩

theorem chainOf_injective : Function.Injective Enc.chainAt := by
  rintro ⟨⟨l, t, f⟩, c⟩ ⟨⟨l', t', f'⟩, c'⟩ h
  simp only [Enc.chainAt, Enc.leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hf⟩, hc⟩ := h
  rw [Fin.ext ht, Fin.ext hf, Fin.ext hc]
set_option linter.constructorNameAsVariable false in
theorem sum_errC_chainOf_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    ∑ p : CanonGraph.LeafPos × Fin 58, Core.errC adversary q (Enc.chainAt p) ≤ Contacts.errTot adversary q := by
  have h1 : ∑ p : CanonGraph.LeafPos × Fin 58, Core.errC adversary q (Enc.chainAt p) =
      ∑ a ∈ Finset.univ.image Enc.chainAt, Core.errC adversary q a :=
    (Finset.sum_image (fun p _ p' _ h => chainOf_injective h)).symm
  have h2 : ∑ a ∈ Finset.univ.image Enc.chainAt, Core.errC adversary q a ≤
      ∑ a ∈ (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7, Core.errC adversary q a := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun a _ => ?_
    split_ifs with h
    · exact le_rfl
    · unfold Core.errC
      rw [dif_neg h]
  have h3 : (Finset.univ.image Enc.chainAt).filter WotsExtract.SourceChain7 ⊆ Contacts.sourceChains7 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact (Contacts.mem_sourceChains7 a).mpr ha.2
  rw [h1]
  exact h2.trans (Finset.sum_le_sum_of_subset h3)
theorem reference_markerFirst_sum_le_of (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hMS : ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧
        MarkerAt s.answers s.trace (Enc.chainAt p) | PairedReference.referenceExperiment adversary q] ≤
      (5022/(2:ENNReal)^128) * ∑' s, PairedReference.referenceExperiment adversary q s *
        (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal)) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a | PairedReference.referenceExperiment adversary q] ≤
      2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
        ((5022 / 2 ^ 128 : ENNReal) * (∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal))) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * Contacts.errTot adversary q := by
  have hu0 : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hutop : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hun0 : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ 0 := mul_ne_zero hu0 (by simp)
  have huntop : (1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128 ≠ ⊤ := ENNReal.mul_ne_top hutop (by simp)
  have hper : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] ≤
        2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
          Core.errC adversary q (Enc.chainAt p) := by
    intro p
    by_cases hs : WotsExtract.SourceChain7 (Enc.chainAt p)
    · simp only [hs, true_and]
      have hC := source_markerFirst_at_le (adversary := adversary) q hq (Enc.chainAt p) hs
      set PF := Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace (Enc.chainAt p)) s.answers s.trace
        (Enc.chainAt p) | PairedReference.referenceExperiment adversary q]
      set PM := Pr[fun s => MarkerAt s.answers s.trace (Enc.chainAt p) | PairedReference.referenceExperiment adversary q]
      set EC := Core.errC adversary q (Enc.chainAt p)
      have hrhs : 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) * PM =
          (((2 * q : ℕ) : ENNReal) * PM) / ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128) := by
        generalize hu : (1 - (q : ENNReal) / 2 ^ 128) = u at hu0 hutop ⊢
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hu0) (Or.inl hutop)]
        push_cast
        ring
      rw [hrhs, ← big_div_mul, ENNReal.div_add_div_same]
      apply (ENNReal.le_div_iff_mul_le (Or.inl hun0) (Or.inl huntop)).mpr
      calc PF * ((1 - (q : ENNReal) / 2 ^ 128) * 2 ^ 128)
          = (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * PF) := by ring
        _ ≤ ((2 * q : ℕ) : ENNReal) * PM + ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * EC := hC
    · simp only [hs, false_and]
      simp
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a | PairedReference.referenceExperiment adversary q]
      ≤ Pr[fun s => ∃ p ∈ (Finset.univ : Finset (CanonGraph.LeafPos × Fin 58)),
          WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
          PairedReference.referenceExperiment adversary q] := by
        apply probEvent_mono''
        rintro s ⟨a, ha, hmf⟩
        obtain ⟨p, rfl⟩ := exists_chainAt ha
        exact ⟨p, by simp, ha, hmf⟩
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58,
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerFirst s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ p : CanonGraph.LeafPos × Fin 58, (2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
            PairedReference.referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            Core.errC adversary q (Enc.chainAt p)) :=
        Finset.sum_le_sum fun p _ => hper p
    _ = 2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
          ∑ p : CanonGraph.LeafPos × Fin 58,
            Pr[fun s => WotsExtract.SourceChain7 (Enc.chainAt p) ∧ MarkerAt s.answers s.trace (Enc.chainAt p) |
              PairedReference.referenceExperiment adversary q] +
          (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) *
            ∑ p : CanonGraph.LeafPos × Fin 58, Core.errC adversary q (Enc.chainAt p) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl hMS) (mul_le_mul' le_rfl (sum_errC_chainOf_le adversary q))

#print axioms reference_markerFirst_sum_le_of
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.Restart

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem mem_take_succ {α : Type} {l : List α} {n : Nat} {x : α} (h : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ l[n]? = some x := by
  rw [List.take_add_one, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y =>
        rw [hl] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        rw [h]

def MarkerFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
 ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   ¬CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) trace a

def ContactFirst (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
 ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   ¬CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧
   CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) trace a

def ReferenceFailed (s : RefSample) : Prop :=
 ∃ L, WotsExtract.SourceLeaf7 L ∧
   CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L = none

def EncodingMatch (s : RefSample) : Prop :=
 ∃ L, WotsExtract.SourceLeaf7 L ∧
   CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L ≠ none ∧
   CanonicalRef.EncodingMatchAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace L

def Structural (s : RefSample) : Prop :=
 CanonicalExtract.StructuralHitSrc s.answers (CanonicalRef.sourceMessages s.answers) s.trace ∨
   PairedReference.StructuralHitTrace s.answers s.trace

def TwoEdge (s : RefSample) : Prop :=
 ∃ a, WotsExtract.SourceChain7 a ∧ CanonicalRef.TwoEdgeAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a

def TwoContacts (s : RefSample) : Prop :=
 ∃ a b, WotsExtract.SourceChain7 a ∧ WotsExtract.SourceChain7 b ∧ a ≠ b ∧
   CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a ∧
   CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace b

def MarkerFirstEvent (s : RefSample) : Prop := ∃ a, WotsExtract.SourceChain7 a ∧ MarkerFirst s.answers s.trace a
def ContactFirstEvent (s : RefSample) : Prop := ∃ a, WotsExtract.SourceChain7 a ∧ ContactFirst s.answers s.trace a

def Combined (s : RefSample) : Prop :=
 CanonicalExtract.WotsPrimitiveSrc s.answers (CanonicalRef.sourceMessages s.answers) s.trace ∨
   PairedReference.StructuralHitTrace s.answers s.trace
theorem chainRow_ne_encRow (a : ChainAddr) (s : Nat) (v : Digest) (L : LeafAddr) (m : WCT9.LayerMsg)
    (c : BitVec 32) (pad : RowPad) : chainRow a s v ≠ encRow L m c pad := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h1 : ClaudeWCT.W9.T3M.Extract.hdrBlock (chainRow a s v) =
      SphincsSecurity.bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
    SigGolfCandidate.T3.chainInput_header _ _ _ _ _ _
  rw [h1, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  exact chainHeader_ne_rowTweak _ _ _ _ _ _ _ _ (SphincsSecurity.bytesLE_injective hb)

theorem markerContact_split (T : Answers) (trace : List Entry) (a : ChainAddr)
    (hm : CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) trace a) (hc : CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) trace a) : MarkerFirst T trace a ∨ ContactFirst T trace a := by
  have hPex : ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hm⟩
  have hQex : ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a := ⟨trace.length, by rw [List.take_length]; exact hc⟩
  obtain ⟨km, hPkm, hPmin⟩ : ∃ k, CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧ ∀ j < k, ¬CanonicalRef.MarkerAt T (CanonicalRef.sourceMessages T) (trace.take j) a :=
    ⟨Nat.find hPex, Nat.find_spec hPex, fun j hj => Nat.find_min hPex hj⟩
  obtain ⟨kc, hQkc, hQmin⟩ : ∃ k, CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take k) a ∧ ∀ j < k, ¬CanonicalRef.ContactAt T (CanonicalRef.sourceMessages T) (trace.take j) a :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun j hj => Nat.find_min hQex hj⟩
  rcases lt_trichotomy km kc with hlt | heq | hgt
  · exact Or.inl ⟨km, hPkm, hQmin km hlt, hc⟩
  · exfalso
    subst heq
    cases km with
    | zero =>
        obtain ⟨message, counter, pad, answer, digits, -, hmem, -⟩ := hPkm
        simp at hmem
    | succ j =>
        have hPj := hPmin j (by omega)
        have hQj := hQmin j (by omega)
        obtain ⟨message, counter, pad, answer, digits, hfit, hmem, hrest⟩ := hPkm
        obtain ⟨hd, value, answer', hmem', hlow⟩ := hQkc
        rcases mem_take_succ hmem with h1 | h1
        · exact hPj ⟨message, counter, pad, answer, digits, hfit, h1, hrest⟩
        rcases mem_take_succ hmem' with h2 | h2
        · exact hQj ⟨hd, value, answer', h2, hlow⟩
        rw [h1] at h2
        have he := congrArg Prod.fst (Option.some.inj h2)
        exact chainRow_ne_encRow _ _ _ _ _ _ _ he.symm
  · exact Or.inr ⟨kc, hQkc, hPmin kc hgt, hm⟩

theorem combined_cases (s : RefSample) (h : Combined s) :
 ReferenceFailed s ∨ EncodingMatch s ∨ Structural s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s := by
 rcases h with hp | hs
 · rcases hp with hm | hs | he | ht | ⟨a,ha,hm,hc⟩
   · obtain ⟨L,hL,hm⟩ := hm
     by_cases hf : CanonicalRef.referenceSearch s.answers (CanonicalRef.sourceMessages s.answers) L = none
     · exact Or.inl ⟨L,hL,hf⟩
     · exact Or.inr (Or.inl ⟨L,hL,hf,hm⟩)
   · exact Or.inr (Or.inr (Or.inl (Or.inl hs)))
   · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
   · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
   · rcases markerContact_split s.answers s.trace a hm hc with hm | hc
     · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a,ha,hm⟩)))))
     · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a,ha,hc⟩)))))
 · exact Or.inr (Or.inr (Or.inl (Or.inr hs)))

theorem structural_reference_le (adversary : Final.Paired.AdversaryP) (q : Nat)
 (hstruct : Pr[fun s => PairedReference.StructuralHitIn (PairedReference.referenceInputs adversary) s.answers s.trace |
   PairedReference.referenceExperiment adversary q] ≤
   (2^128:ENNReal)⁻¹*∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) :
 Pr[Structural | PairedReference.referenceExperiment adversary q] ≤
   (2^128:ENNReal)⁻¹*∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal) := by
 refine le_trans (SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono _ fun s hs h => ?_) hstruct
 have hin := PairedReference.reference_trace_mem adversary q s hs
 exact h.elim (fun h => CanonicalExtract.structuralHitSrc_paired h hin)
   (fun h => PairedReference.StructuralHitTrace.toHitIn h hin)
#print axioms combined_cases
#print axioms structural_reference_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nonstructural_contact (s : RefSample)
 (h : TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s) :
 ∃a∈Contacts.sourceChains7,CanonicalRef.ContactAt s.answers (CanonicalRef.sourceMessages s.answers) s.trace a := by
 rcases h with ⟨a,ha,hd,_,middle,_,h2⟩ | ⟨a,_,ha,_,_,hc,_⟩ | ⟨a,ha,_,_,_,hc⟩ | ⟨a,ha,_,⟨hd,value,answer,hm,hl⟩,_,_⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,by omega,middle,h2⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hc⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hc⟩
 · exact ⟨a,(Contacts.mem_sourceChains7 a).mpr ha,hd,value,answer,List.mem_of_mem_take hm,hl⟩

theorem nonstructural_reference_le (adversary : Final.Paired.AdversaryP) (q : Nat) :
 Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s |
   PairedReference.referenceExperiment adversary q] ≤
 ∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.contactCount s:ENNReal) := by
 rw [probEvent_eq_tsum_ite]
 apply ENNReal.tsum_le_tsum
 intro s
 split_ifs with h
 · obtain ⟨a,ha,hc⟩ := nonstructural_contact s h
   rw [PMF.probOutput_eq_apply]
   apply le_mul_of_one_le_right'
   have hp : 0 < Contacts.contactCount s := Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hc⟩⟩
   exact_mod_cast hp
 · exact zero_le
#print axioms nonstructural_reference_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem reference_primitive_le (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128)
 (w v : ENNReal) (hwv : w+v=1) :
 Pr[Combined | PairedReference.referenceExperiment adversary q] ≤
 Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] +
 prefixCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)) +
 encodingCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)) +
 (2^128:ENNReal)⁻¹*(∑'s,PairedReference.referenceExperiment adversary q s*(PairedReference.otherCount s:ENNReal)) +
 errCoeff q w v*Contacts.errTot adversary q := by
 refine weighted_union_le (PairedReference.referenceExperiment adversary q)
   Combined ReferenceFailed EncodingMatch Structural TwoEdge TwoContacts MarkerFirstEvent ContactFirstEvent
   q w v _ _ _ _ hwv combined_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_
 · exact CanonicalRef.reference_encodingMatch_le adversary q
 · exact structural_reference_le adversary q (PairedReference.reference_structural_in_le adversary q)
 · exact Contacts.reference_twoEdge_le adversary q hq
 · exact Restart.reference_twoContacts_le adversary q hq
 · exact Restart.reference_markerFirst_sum_le_of adversary q hq (CanonicalRef.reference_marker_sum_le adversary q)
 · exact (CanonicalRef.Contact93.reference_contactFirst_le adversary q).trans
     (mul_le_mul' le_rfl (Contacts.reference_contacts_cost_le adversary q hq))
 · exact (nonstructural_reference_le adversary q).trans (Contacts.reference_contacts_cost_le adversary q hq)
#print axioms reference_primitive_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference
open OracleComp OracleSpec OracleComp.EvalDist
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem GameSplit.keygen_value {adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP}
    {result : FirstHit.Recorded Bool} {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option ClaudeWCT.W9.T3M.Final.Paired.ForgeryP × QueryLog ClaudeWCT.W9.T3M.Final.Paired.Requests)}
    {checked : FirstHit.Recorded Bool} (h : GameSplit adversary result generated interaction checked)
    (A : Answers) (ha:∀input answer,SourceReplay.known result.state input=some answer → A input=answer) :
    evalWithAnswerFn A keygen=generated.value := by
  obtain ⟨hg,hi,hc,heq⟩:=h
  have hs:result.state=checked.state:=by rw[heq]
  have hiext:SourceReplay.Extends interaction.state result.state:=by
    rw[hs]
    exact SourceReplay.run_extends _ interaction.state (checked.value,checked.state)
      (FirstHit.recorded_support _ _ _ hc)
  have hgext:SourceReplay.Extends generated.state result.state:=
    (SourceReplay.run_extends _ generated.state (interaction.value,interaction.state)
      (FirstHit.recorded_support _ _ _ hi)).trans hiext
  exact (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅,∅)
    (generated.value,generated.state) (FirstHit.recorded_support _ _ _ hg)).eval A
    (fun input answer hk=>ha input answer (SourceReplay.known_mono _ _ hgext hk))
#print axioms GameSplit.keygen_value
end ClaudeWCT.W9.T3.Security.Wots.PairedReference

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Security.CaseC (lazyOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_incomplete_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138 := by
  refine (Ref.pmf_probEvent_mono (PairedSeccLaw.completedExperiment adversary q hq) ?_).trans
    (PairedSearchTable.completed_signer_failure adversary q hq)
  intro z hz hevent hcomplete
  obtain ⟨generated,interaction,checked,hsplit,hbad⟩:=hevent
  obtain ⟨_,ha⟩:=PairedSeccLaw.completed_agrees adversary q hq z hz
  have hk:=hsplit.keygen_value z.2 ha
  apply hbad
  intro message
  obtain ⟨sig,hsig⟩:=hcomplete message
  rw[hk] at hsig
  refine ⟨sig,?_⟩
  unfold SigGolfCandidate.Research.SharedForest.sign at hsig
  rw[evalWithAnswerFn_bind] at hsig
  split_ifs at hsig with hm
  · simp only[evalWithAnswerFn_pure,reduceCtorEq] at hsig
  · exact hsig

#print axioms completed_incomplete_bound
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_near_le_other (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧ WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*WPair.Paired.Counted.referenceOther adversary q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.Counted.completed_event_le_other adversary q hq
      (fun A log entries=>WPair.Paired.NearIn A log entries ∧ ¬WPair.Paired.OverflowIn A log)
      (fun A T log entries h hp=>⟨WPair.Paired.nearIn_short h log entries hp.1,
        fun ho=>hp.2 (WPair.Paired.overflowIn_short h.symm log ho)⟩)
      (fun A log entries entries' hsub hp=>⟨WPair.Paired.nearIn_mono A log entries entries' hsub hp.1,hp.2⟩)
      (fun _ _ _ hp=>hp.2) ?_)
  · intro z hz h
    exact ⟨h.1.2.1,fun generated interaction checked hs=>
      ⟨completed_near_implies adversary q hq z hz h.1 generated interaction checked hs,
        h.2 generated interaction checked hs⟩⟩
  · intro A log entries hp
    obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=hp.1
    exact ⟨cell,hguess⟩

theorem completed_near_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    (1-(q:ℝ)/2^128)*(Pr[fun z => NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∧
      WPair.Paired.NoOverflow adversary z | PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      (WPair.Paired.Counted.referenceOther adversary q).toReal/2^128 := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using WPair.Paired.Counted.hazard_normalized
    (n:=2^128) (q:=q) (by omega) (WPair.Paired.Counted.referenceOther_ne_top adversary q)
    (completed_near_le_other adversary q hq)
#print axioms completed_near_le_other
#print axioms completed_near_normalized
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem referenceSearch_complete (answers : Answers) (hgood : ContextGood answers)
    (L : LeafAddr) (hL : WotsExtract.SourceLeaf7 L) :
    referenceSearch answers (sourceMessages answers) L ≠ none := by
  let cache : SigGolfCandidate.T3.Cache := ⟨0,fun _=>0⟩
  exact referenceSearch_complete_of_routes answers cache
    (fun index hi => searchPreparedLayers_complete answers hgood cache index hi _ _) L hL
#print axioms referenceSearch_complete
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef
namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.CanonicalSearch
attribute [local instance] Classical.propDecidable

theorem reference_failed_le (adversary : Final.Paired.AdversaryP) (q : Nat) :
    Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139 := by
  refine (SigGolfCandidate.T3.Security.Wots.Ref.pmf_probEvent_mono _ ?_).trans
    (PairedSearchTable.context_failure adversary q)
  rintro s _ ⟨L,hL,hs⟩ hgood
  exact CanonicalRef.referenceSearch_complete s.answers hgood L hL hs
#print axioms reference_failed_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable

def PartialForestNoOverflow (adversary : Final.Paired.AdversaryP) (q : Nat)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) : Prop :=
  (NearForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨ PairForestEvent adversary q (z.1.1,z.1.2.2) z.2) ∧
    WPair.Paired.NoOverflow adversary z

theorem completed_partial_le_other (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*WPair.Paired.Counted.referenceOther adversary q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans
    (WPair.Paired.Counted.completed_event_le_other adversary q hq
      (fun A log entries=>(∃cell,WPair.Paired.GuessedIn A log entries cell) ∧ ¬WPair.Paired.OverflowIn A log)
      (fun A T log entries h hp=>⟨by
        obtain ⟨cell,hcell⟩:=hp.1
        exact ⟨cell,WPair.Paired.guessedIn_short h log entries cell hcell⟩,
        fun ho=>hp.2 (WPair.Paired.overflowIn_short h.symm log ho)⟩)
      (fun A log entries entries' hsub hp=>⟨by
        obtain ⟨cell,hcell⟩:=hp.1
        exact ⟨cell,WPair.Paired.guessedIn_mono A log entries entries' hsub cell hcell⟩,hp.2⟩)
      (fun _ _ _ hp=>hp.2) (fun _ _ _ hp=>hp.1))
  intro z hz h
  refine ⟨h.1.elim (fun hn=>hn.2.1) (fun hp=>hp.2.1),?_⟩
  intro generated interaction checked hs
  refine ⟨?_,h.2 generated interaction checked hs⟩
  rcases h.1 with hn | hp
  · obtain ⟨hlen,hclosed,message,rho,counter,N,cell,he,ha,hfresh,hguess,hcover⟩:=
      completed_near_implies adversary q hq z hz hn generated interaction checked hs
    exact ⟨cell,hguess⟩
  · obtain ⟨cell,cell',hne,hg,hg'⟩:=completed_pair_implies adversary q hq z hz hp generated interaction checked hs
    exact ⟨cell,hg⟩

theorem completed_partial_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    (1-(q:ℝ)/2^128)*(Pr[PartialForestNoOverflow adversary q |
      PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      (WPair.Paired.Counted.referenceOther adversary q).toReal/2^128 := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using WPair.Paired.Counted.hazard_normalized
    (n:=2^128) (q:=q) (by omega) (WPair.Paired.Counted.referenceOther_ne_top adversary q)
    (completed_partial_le_other adversary q hq)

variable {P : Type} [Fintype P] [SampleableType P]
theorem completed_partial_bound (S : ClaudeWCT.Bank.FtsBankSpec P)
    (hproducer : S.producer=SigGolfCandidate.Research.SharedForest.digestAccepted)
    (hadmissible : S.admissible=ClaudeWCT.Bank.Paired.admissible)
    (hmono : ∀ X Y N,(∀ value∈X,value∈Y) → S.covered X N → S.covered Y N)
    (hcovered : ∀ X N,WPair.Paired.NearCovers X N → S.covered X N)
    (rate : ENNReal) (hrate : ClaudeWCT.Numerics.Law.lawAvg S.law (2^32) S.price≤rate)
    (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(rate+S.admBound)/(2*2^128)+BPair.pairTerm q := by
  refine (Ref.pmf_probEvent_mono _ ?_).trans ((probEvent_or_le _ _ _).trans (add_le_add
    (completed_near_bound S hproducer hadmissible hmono hcovered rate hrate adversary q hq)
    (completed_pair_bound adversary q hq)))
  intro z hz h
  exact h.1.elim (fun hn=>Or.inl ⟨hn,h.2⟩) (fun hp=>Or.inr ⟨hp,h.2⟩)
#print axioms completed_partial_le_other
#print axioms completed_partial_normalized
#print axioms completed_partial_bound
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def Nonstructural (s : RefSample) : Prop := EncodingMatch s ∨ TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s

theorem reference_nonstructural_le (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128)
    (w v : ENNReal) (hwv : w+v=1) :
 Pr[Nonstructural | PairedReference.referenceExperiment adversary q] ≤
 prefixCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)) +
 encodingCoeff q w v/2^128*(∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)) +
 errCoeff q w v*Contacts.errTot adversary q := by
 have hh := weighted_union_le (PairedReference.referenceExperiment adversary q)
   Nonstructural (fun _=>False) EncodingMatch (fun _=>False) TwoEdge TwoContacts MarkerFirstEvent ContactFirstEvent
   q w v
   (∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal))
   (∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal))
   0 (Contacts.errTot adversary q) hwv
   (fun s h => by rcases h with h|h;exact Or.inr (Or.inl h);exact Or.inr (Or.inr (Or.inr h)))
   (CanonicalRef.reference_encodingMatch_le adversary q)
   (by simp)
   (Contacts.reference_twoEdge_le adversary q hq)
   (Restart.reference_twoContacts_le adversary q hq)
   (Restart.reference_markerFirst_sum_le_of adversary q hq (CanonicalRef.reference_marker_sum_le adversary q))
   ((CanonicalRef.Contact93.reference_contactFirst_le adversary q).trans
     (mul_le_mul' le_rfl (Contacts.reference_contacts_cost_le adversary q hq)))
   ((nonstructural_reference_le adversary q).trans (Contacts.reference_contacts_cost_le adversary q hq))
 have hz : Pr[fun _ : RefSample => False | PairedReference.referenceExperiment adversary q]=0 := by
   simp
 simpa only [hz,zero_add,mul_zero,add_zero] using hh
#print axioms reference_nonstructural_le
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem cleanWin_le_union_cases_of_split (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q≤2^127)
    (hsplit : ∀ z, z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
    Pr[fun s=>combinedEvent.holds s.answers s.trace | PairedReference.referenceExperiment adversary q] +
    Pr[fun z=>FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
    Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq] := by
  rw [←PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  have hs : Pr[fun z=>QueryRecorded.CleanWin q z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
    Pr[fun z=>
      (QueryRecorded.CleanWin q z.1 ∧ CaseABEv combinedEvent adversary z) ∨
      FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 ∨
      PartialForestNoOverflow adversary q z ∨
      IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 ∨
      (QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z) |
        PairedSeccLaw.completedExperiment adversary q hq] := by
    apply Ref.pmf_probEvent_mono
    intro z hz hclean
    rcases Classical.em (WPair.Paired.NoOverflow adversary z) with hno | hno
    · rcases hsplit z hz hclean with hab | hf
      · exact Or.inl ⟨hclean,hab⟩
      · rcases completed_forest_cases adversary q hq z hz hclean hf with hfull | hnear | hpair | hinc
        · exact Or.inr (Or.inl hfull)
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inl hnear,hno⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨Or.inr hpair,hno⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hinc)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hclean,hno⟩)))
  refine hs.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add (caseABEv_le_reference combinedEvent adversary q hq) (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _)))
    _ = _ := by ac_rfl
#print axioms cleanWin_le_union_cases_of_split
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem queryRatio_lt_one (q : Nat) (hq : q<2^128) : (q:ENNReal)/2^128<1 := by
  rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)),one_mul]
  exact_mod_cast hq

theorem denominator_ne_zero (q : Nat) (hq : q<2^128) : 1-(q:ENNReal)/2^128≠0 :=
  ne_of_gt (tsub_pos_iff_lt.mpr (queryRatio_lt_one q hq))

theorem prefixCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) :
    prefixCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold prefixCoeff
  finiteness

theorem encodingCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) :
    encodingCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold encodingCoeff
  finiteness

theorem errCoeff_ne_top (q : Nat) (hq : q<2^128) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) :
    errCoeff q w v≠⊤ := by
  have hd:=denominator_ne_zero q hq
  unfold errCoeff twoEdgeRate
  finiteness

theorem denominator_toReal (q : Nat) (hq : q<2^128) :
    (1-(q:ENNReal)/2^128).toReal=1-(q:ℝ)/2^128 := by
  rw [ENNReal.toReal_sub_of_le (le_of_lt (queryRatio_lt_one q hq)) (by simp)]
  simp

theorem prefixCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1) :
    (prefixCoeff q w v).toReal=canonicalPrefix ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  have hvw : v.toReal=1-w.toReal := by
    have h:=congrArg ENNReal.toReal hwv
    rw [ENNReal.toReal_add hw hv] at h
    simp only [ENNReal.toReal_one] at h
    linarith
  unfold prefixCoeff canonicalPrefix
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,denominator_toReal q hq,hvw]
  ring

theorem encodingCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) :
    (encodingCoeff q w v).toReal=canonicalEncoding ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  unfold encodingCoeff canonicalEncoding
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,denominator_toReal q hq]
  ring

theorem errCoeff_toReal (q : Nat) (hq : q<2^128) (w v : ENNReal)
    (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1) :
    (errCoeff q w v).toReal=canonicalError ((q:ℝ)/2^128) w.toReal := by
  have hd:=denominator_ne_zero q hq
  have hvw : v.toReal=1-w.toReal := by
    have h:=congrArg ENNReal.toReal hwv
    rw [ENNReal.toReal_add hw hv] at h
    simp only [ENNReal.toReal_one] at h
    linarith
  unfold errCoeff twoEdgeRate canonicalError
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one,denominator_toReal q hq,hvw]
  ring

#print axioms prefixCoeff_toReal
#print axioms encodingCoeff_toReal
#print axioms errCoeff_toReal
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceExperiment

theorem query_card_lt_one (q : Nat) (hq : q<2^128) : (Fintype.card Digest:ℝ)⁻¹*q<1 := by
  have hcard : (Fintype.card Digest:ℝ)=2^128 := by rw [Fintype.card_bitVec];norm_num
  rw [hcard]
  have hq' : (q:ℝ)<2^128 := by exact_mod_cast hq
  rw [mul_comm,←div_eq_mul_inv]
  exact (div_lt_one (by positivity)).2 hq'

theorem kconst_le (q : Nat) : (ClaudeWCT.Arith.SideChannel.kconst q:ℝ)≤5*(q:ℝ)^2 := by
  have hc (n : Nat) : n.choose 2*2≤n*n := by
    rw [Nat.choose_two_right]
    exact (Nat.div_mul_le_self _ 2).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
  have h1 : ((3*q).choose 2:ℝ)*2≤(3*(q:ℝ))*(3*q) := by exact_mod_cast hc (3*q)
  have h2 : (q.choose 2:ℝ)*2≤(q:ℝ)*q := by exact_mod_cast hc q
  unfold ClaudeWCT.Arith.SideChannel.kconst
  push_cast
  nlinarith

theorem errConst_nonneg (q : Nat) (hq : q<2^128) : 0≤Core.errConst q := by
  have hd : 0<1-(Fintype.card Digest:ℝ)⁻¹*q := sub_pos.mpr (query_card_lt_one q hq)
  unfold Core.errConst
  positivity

theorem errTot_ne_top (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128) :
    Contacts.errTot adversary q≠⊤ :=
  ne_top_of_le_ne_top (by finiteness) (Contacts.errTot_le adversary q (query_card_lt_one q hq))

theorem errTot_toReal (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128) :
    (Contacts.errTot adversary q).toReal ≤
      540*((q:ℝ)/2^128)^3/(1-(q:ℝ)/2^128) := by
  have h0:=errConst_nonneg q hq
  have h:=ENNReal.toReal_mono (by finiteness)
    (Contacts.errTot_le adversary q (query_card_lt_one q hq))
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal h0,ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat] at h
  have hd : 0<1-(q:ℝ)/2^128 := by
    have hq' : (q:ℝ)<2^128 := by exact_mod_cast hq
    exact sub_pos.mpr ((div_lt_one (by positivity)).2 hq')
  have hn : 0≤(q:ℝ) := Nat.cast_nonneg q
  have hk:=kconst_le q
  have hm : 0≤(54:ℝ)*(q:ℝ) := mul_nonneg (by norm_num) hn
  have hc : 0≤2*((2:ℝ)^128)⁻¹^3 := mul_nonneg (by norm_num) (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) 128)) 3)
  unfold Core.errConst at h
  have hcard : (Fintype.card Digest:ℝ)=2^128 := by rw [Fintype.card_bitVec];norm_num
  rw [hcard] at h
  have hrat : ((2:ℝ)^128)⁻¹*(q:ℝ)=(q:ℝ)/2^128 := by ring
  rw [hrat] at h
  calc (Contacts.errTot adversary q).toReal
      ≤ (2*((2:ℝ)^128)⁻¹^3*(ClaudeWCT.Arith.SideChannel.kconst q:ℝ)/(1-(q:ℝ)/2^128))*(54*q) := h
    _ ≤ (2*((2:ℝ)^128)⁻¹^3*(5*(q:ℝ)^2)/(1-(q:ℝ)/2^128))*(54*q) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hc) hd.le)
        hm
    _ = _ := by ring

#print axioms errTot_toReal
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] PairedReference.referenceExperiment

noncomputable def prefixMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  ∑'s,PairedReference.referenceExperiment adversary q s*(Contacts.prefixClassCount s:ENNReal)
noncomputable def encodingMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  ∑'s,PairedReference.referenceExperiment adversary q s*(encodingCount s:ENNReal)

theorem nonstructural_real (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128)
    (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hp:prefixMass adversary q≠⊤) (he:encodingMass adversary q≠⊤) :
    (Pr[Nonstructural | PairedReference.referenceExperiment adversary q]).toReal ≤
      canonicalPrefix ((q:ℝ)/2^128) w.toReal*((prefixMass adversary q).toReal/2^128)+
      canonicalEncoding ((q:ℝ)/2^128) w.toReal*((encodingMass adversary q).toReal/2^128)+
      canonicalError ((q:ℝ)/2^128) w.toReal*(Contacts.errTot adversary q).toReal := by
  have hc1:=prefixCoeff_ne_top q hq w v hw hv
  have hc2:=encodingCoeff_ne_top q hq w v hw
  have hc3:=errCoeff_ne_top q hq w v hw hv
  have hf:=errTot_ne_top adversary q hq
  have hbound : Pr[Nonstructural | PairedReference.referenceExperiment adversary q] ≤
      prefixCoeff q w v/2^128*prefixMass adversary q+
      encodingCoeff q w v/2^128*encodingMass adversary q+errCoeff q w v*Contacts.errTot adversary q :=
    reference_nonstructural_le adversary q hq w v hwv
  have h:=ENNReal.toReal_mono (by finiteness) hbound
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,prefixCoeff_toReal q hq w v hw hv hwv,
    encodingCoeff_toReal q hq w v hw,errCoeff_toReal q hq w v hw hv hwv] at h
  convert h using 1 <;> ring

theorem nonstructural_small_real (adversary : Final.Paired.AdversaryP) (q : Nat) (hq : q<2^128)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hp:prefixMass adversary q≠⊤) (he:encodingMass adversary q≠⊤)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤109/100) :
    (Pr[Nonstructural | PairedReference.referenceExperiment adversary q]).toReal ≤
      theta*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
      (710/1000)*((q:ℝ)/2^128)^2 := by
  have he0 : 0≤canonicalError ((q:ℝ)/2^128) w.toReal := by
    rw [←errCoeff_toReal q hq w v hw hv hwv]
    exact ENNReal.toReal_nonneg
  have hseed := (errTot_toReal adversary q hq).trans (canonical_seed_error _ hy)
  have hweighted:=canonical_weighted_error ((q:ℝ)/2^128) (Contacts.errTot adversary q).toReal
    (canonicalError ((q:ℝ)/2^128) w.toReal) he0 herror hseed
  refine (nonstructural_real adversary q hq w v hw hv hwv hp he).trans ?_
  calc _ ≤ theta*((prefixMass adversary q).toReal/2^128)+
        theta*((encodingMass adversary q).toReal/2^128)+(710/1000)*((q:ℝ)/2^128)^2 := by
          exact add_le_add (add_le_add
            (mul_le_mul_of_nonneg_right hprefix (by positivity))
            (mul_le_mul_of_nonneg_right hencoding (by positivity))) hweighted
    _ = _ := by ring

#print axioms nonstructural_small_real
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open PairedReference.Classes
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def prefixMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount
noncomputable def encodingMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q encodingCount
noncomputable def otherMass (adversary : Final.Paired.AdversaryP) (q : Nat) : ENNReal :=
  PairedReference.Classes.refExpect adversary q PairedReference.otherCount
noncomputable def digestMass (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) : ENNReal :=
  PairedSeccLaw.expectedCharge adversary q hq PairedReference.Classes.digestClass

theorem masses_finite (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    prefixMass adversary q≠⊤ ∧ encodingMass adversary q≠⊤ ∧ otherMass adversary q≠⊤ ∧
      digestMass adversary q hq≠⊤ := by
  have hf := ne_top_of_le_ne_top (ENNReal.natCast_ne_top q) (PairedReference.Classes.reference_class_budget adversary q hq)
  change prefixMass adversary q+encodingMass adversary q+otherMass adversary q+digestMass adversary q hq≠⊤ at hf
  rcases ENNReal.add_ne_top.mp hf with ⟨hpeo,hm⟩
  rcases ENNReal.add_ne_top.mp hpeo with ⟨hpe,ho⟩
  exact ⟨(ENNReal.add_ne_top.mp hpe).1,(ENNReal.add_ne_top.mp hpe).2,ho,hm⟩

theorem masses_normalized (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    (prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
      (otherMass adversary q).toReal/2^128+(digestMass adversary q hq).toReal/2^128≤(q:ℝ)/2^128 := by
  have hf:=masses_finite adversary q hq
  have h:=ENNReal.toReal_mono (ENNReal.natCast_ne_top q) (PairedReference.Classes.reference_class_budget adversary q hq)
  change (prefixMass adversary q+encodingMass adversary q+otherMass adversary q+digestMass adversary q hq).toReal≤(q:ENNReal).toReal at h
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hf.1,hf.2.1⟩,hf.2.2.1⟩) hf.2.2.2,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hf.1,hf.2.1⟩) hf.2.2.1,ENNReal.toReal_add hf.1 hf.2.1,ENNReal.toReal_natCast] at h
  simpa only [add_div] using div_le_div_of_nonneg_right h (show (0:ℝ)≤2^128 by positivity)

theorem full_probability_real (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤)
    (hmin:1/1024≤theta) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate) :
    (Pr[fun z=>FullForestEvent adversary q (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
        theta.toReal*((digestMass adversary q hq).toReal/2^128)+(q:ℝ)/2^128*rate.toReal := by
  have h := completed_flexible_full_bound (theta-1/1024) rate adversary q hq hrate
  rw [tsub_add_cancel_of_le hmin] at h
  have hcls : (fun (_ : PairedOuter.PaddedGame.TraceResult × SigGolfCandidate.T3.Correctness.Answers) =>
      CreationGame.publicClass CaseC.IsDigestInput)=PairedReference.Classes.digestClass := by
    funext z input
    apply propext
    rcases input with (coin | x) | priv
    · exact ⟨fun h => h.elim, fun ⟨_,_,_,h⟩ => by cases h⟩
    · constructor
      · rintro ⟨rho,m,ctr,rfl⟩;exact ⟨rho,m,ctr,rfl⟩
      · rintro ⟨rho,m,ctr,h⟩;cases h;exact ⟨rho,m,ctr,rfl⟩
    · exact ⟨fun h => h.elim, fun ⟨_,_,_,h⟩ => by cases h⟩
  rw [hcls] at h
  change _≤theta/2^128*digestMass adversary q hq+(q:ENNReal)*rate/2^128 at h
  have hm: digestMass adversary q hq≠⊤ := (masses_finite adversary q hq).2.2.2
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast] at hreal
  convert hreal using 1 <;> ring

theorem partial_probability_real (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(350+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal ≤
      ((350+1/1024)/(2*(1-(q:ℝ)/2^128))+1/(2*(1-(q:ℝ)/2^128)^2))*((q:ℝ)/2^128)^2 := by
  have hqN : q<2^128 := by omega
  have hN : (0:ℝ)<2^128 := by positivity
  have hqr : (q:ℝ)<2^128 := by exact_mod_cast hqN
  have hd : 0<(2:ℝ)^128-q := sub_pos.mpr hqr
  have hsub : ((2^128-q:Nat):ℝ)=(2:ℝ)^128-q := by rw [Nat.cast_sub (by omega),Nat.cast_pow,Nat.cast_ofNat]
  have hsub0 : ((2^128-q:Nat):ENNReal)≠0 := by exact_mod_cast (by omega : 2^128-q≠0)
  have hchoose : (q.choose 2:ℝ)≤(q:ℝ)^2/2 := by
    have hc : q.choose 2*2≤q*q := by
      rw [Nat.choose_two_right]
      exact (Nat.div_mul_le_self _ 2).trans (Nat.mul_le_mul_left q (Nat.sub_le q 1))
    have hc' : (q.choose 2:ℝ)*2≤(q:ℝ)*q := by exact_mod_cast hc
    nlinarith
  have hprod : ((q*(q-1):Nat):ℝ)≤(q:ℝ)^2 := by
    have hp : q*(q-1)≤q*q := Nat.mul_le_mul_left q (Nat.sub_le q 1)
    simpa only [pow_two] using (show ((q*(q-1):Nat):ℝ)≤(q:ℝ)*q by exact_mod_cast hp)
  have hr := ENNReal.toReal_mono (by unfold BPair.pairTerm;finiteness) h
  simp (disch:=finiteness) only [BPair.pairTerm,ENNReal.toReal_add,ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast,ENNReal.toReal_one] at hr
  rw [hsub] at hr
  refine hr.trans ?_
  calc
    _ ≤ ((2:ℝ)^128-q)⁻¹*(q:ℝ)^2*(350+1/1024)/(2*2^128)+
      ((q:ℝ)^2/2)*(((2:ℝ)^128-q)⁻¹)^2 := by
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hd.le)) (by norm_num)
      · exact mul_le_mul_of_nonneg_right hchoose (sq_nonneg _)
    _ = _ := by
      have hdy : 1-(q:ℝ)/2^128≠0 := ne_of_gt (sub_pos.mpr ((div_lt_one hN).2 hqr))
      field_simp [ne_of_gt hd,hdy]
      <;> ring

#print axioms masses_normalized
#print axioms full_probability_real
#print axioms partial_probability_real
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_probability_real_of (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hsplit : ∀ z,z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z)
    (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤) (hmin:1/1024≤theta)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-1/1024))≤rate)
    (hprimitive : (Pr[fun s=>combinedEvent.holds s.answers s.trace |
      PairedReference.referenceExperiment adversary q]).toReal ≤
        theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
        (otherMass adversary q).toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139)
    (hincomplete : Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138)
    (hoverflow : Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate.toReal+(710/1000)*((q:ℝ)/2^128)^2+1/2^136 := by
  have hf := full_probability_real theta rate htheta hratefin hmin adversary q hq hrate
  have hinc := ENNReal.toReal_mono (by finiteness) hincomplete
  have hov := ENNReal.toReal_mono (by finiteness) hoverflow
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hinc hov
  have hevent {α:Type} (law:PMF α) (P:α→Prop) : Pr[P|law]≠⊤ := ne_top_of_le_ne_top (by simp) probEvent_le_one
  have h:=ENNReal.toReal_mono (by exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩)
    (cleanWin_le_union_cases_of_split adversary q hq hsplit)
  simp only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hevent _ _,hevent _ _⟩) (hevent _ _),
    ENNReal.toReal_add (hevent _ _) (hevent _ _)] at h
  have habs : (1:ℝ)/2^139+1/2^138+1/2^137≤1/2^136 := by norm_num
  nlinarith

#print axioms clean_probability_real_of
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem middle_clean_closing (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : 1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh : (q:ℝ)/2^128≤3/2500)
    (rate : ℝ) (hrate : rate≤147/125000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (99847/50000)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(710/1000)*((q:ℝ)/2^128)^2+1/2^136)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(350+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hquad := paired_partial_denominator _ _ hhigh (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := class_budget _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := middle_closing_rows18 ((q:ℝ)/2^128) rate hlow hhigh hrate
  linarith

theorem tiny_clean_closing (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive : 1≤q) (hhigh : (q:ℝ)/2^128≤1/2^28)
    (rate : ℝ) (hrate : rate≤18/5000)
    (hclean : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      (249/125)*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate+(710/1000)*((q:ℝ)/2^128)^2+1/2^136)
    (hpartial : Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(350+1/1024)/(2*2^128)+BPair.pairTerm q) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128) := by
  have hsmall : (q:ℝ)/2^128≤3/2500 := hhigh.trans (by norm_num)
  have hlow : 1/(2:ℝ)^128≤(q:ℝ)/2^128 := div_le_div_of_nonneg_right (by exact_mod_cast hpositive) (by positivity)
  have hquad := paired_partial_denominator _ _ hsmall (partial_probability_real adversary q hq hpartial)
  have hcost := completed_partial_normalized adversary q hq
  change (1-(q:ℝ)/2^128)*_≤(otherMass adversary q).toReal/2^128 at hcost
  rw [mul_comm] at hcost
  have hbudget := tiny_class_budget _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (masses_normalized adversary q hq) hhigh ENNReal.toReal_nonneg hcost hquad
  have hbound := tiny_closing_rows18 ((q:ℝ)/2^128) rate hlow hhigh hrate
  nlinarith [sq_nonneg ((q:ℝ)/2^128)]

theorem clean_outer_ennreal (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (h : (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal+
      ((q:ℝ)/2^128/2^18+1/2^700+1/2^152+((q:ℝ)/2^128)/2^128)≤2*((q:ℝ)/2^128)) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hevent : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]≠⊤ :=
    ne_top_of_le_ne_top (by simp) probEvent_le_one
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,Nat.cast_pow,Nat.cast_ofNat]
  convert h using 1 <;> norm_num <;> ring

#print axioms middle_clean_closing
#print axioms tiny_clean_closing
#print axioms clean_outer_ennreal
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem primitive_real_of_raw (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q<2^128)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hp:prefixMass adversary q≠⊤) (he:encodingMass adversary q≠⊤)
    (eventProbability otherMass : ENNReal) (ho:otherMass≠⊤)
    (hraw : eventProbability ≤ 1/(2:ENNReal)^139+
      prefixCoeff q w v/2^128*prefixMass adversary q+
      encodingCoeff q w v/2^128*encodingMass adversary q+
      (2^128:ENNReal)⁻¹*otherMass+errCoeff q w v*Contacts.errTot adversary q)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤109/100) :
    eventProbability.toReal ≤
      theta*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
      otherMass.toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139 := by
  have hc1:=prefixCoeff_ne_top q hq w v hw hv
  have hc2:=encodingCoeff_ne_top q hq w v hw
  have hc3:=errCoeff_ne_top q hq w v hw hv
  have hfin:=errTot_ne_top adversary q hq
  have h:=ENNReal.toReal_mono (by finiteness) hraw
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_inv,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    prefixCoeff_toReal q hq w v hw hv hwv,encodingCoeff_toReal q hq w v hw,
    errCoeff_toReal q hq w v hw hv hwv] at h
  have he0 : 0≤canonicalError ((q:ℝ)/2^128) w.toReal := by
    rw [←errCoeff_toReal q hq w v hw hv hwv]
    exact ENNReal.toReal_nonneg
  have hseed := (errTot_toReal adversary q hq).trans (canonical_seed_error _ hy)
  have herr:=canonical_weighted_error ((q:ℝ)/2^128) (Contacts.errTot adversary q).toReal
    (canonicalError ((q:ℝ)/2^128) w.toReal) he0 herror hseed
  have hp' := mul_le_mul_of_nonneg_right hprefix (show 0≤(prefixMass adversary q).toReal/2^128 by positivity)
  have he' := mul_le_mul_of_nonneg_right hencoding (show 0≤(encodingMass adversary q).toReal/2^128 by positivity)
  simp only [div_eq_mul_inv] at h hp' he' herr ⊢
  nlinarith
#print axioms primitive_real_of_raw
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M CanonicalRef.Normalized
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem primitive_real_of_failure (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500) (w v : ENNReal) (hw:w≠⊤) (hv:v≠⊤) (hwv:w+v=1)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139)
    (theta : ℝ) (hprefix:canonicalPrefix ((q:ℝ)/2^128) w.toReal≤theta)
    (hencoding:canonicalEncoding ((q:ℝ)/2^128) w.toReal≤theta)
    (herror:canonicalError ((q:ℝ)/2^128) w.toReal≤109/100) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      theta*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139 := by
  have hqN : q<2^128 := by omega
  have hf := PairedSmallT.masses_finite adversary q hq
  have hraw := (reference_primitive_le adversary q hqN w v hwv).trans
    (add_le_add (add_le_add (add_le_add (add_le_add hfailed le_rfl) le_rfl) le_rfl) le_rfl)
  exact primitive_real_of_raw adversary q hqN hy w v hw hv hwv hf.1 hf.2.1
    _ (PairedSmallT.otherMass adversary q) hf.2.2.1 hraw theta hprefix hencoding herror

theorem primitive_middle_real_of_failure (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (99847/50000)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139 := by
  have hc := middle_coefficients ((q:ℝ)/2^128) (by positivity) hy
  apply primitive_real_of_failure adversary q hq hy (1023/50000) (48977/50000)
    (by finiteness) (by finiteness) (by norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)) hfailed
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.2

theorem primitive_tiny_real_of_failure (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤1/2^28)
    (hfailed : Pr[ReferenceFailed | PairedReference.referenceExperiment adversary q] ≤ 1/(2:ENNReal)^139) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (249/125)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139 := by
  have hc := tiny_coefficients ((q:ℝ)/2^128) (by positivity) hy
  apply primitive_real_of_failure adversary q hq (hy.trans (by norm_num)) (3/100) (97/100)
    (by finiteness) (by finiteness) (by norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)) hfailed
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.1
  · simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using hc.2.2

#print axioms primitive_real_of_failure
#print axioms primitive_middle_real_of_failure
#print axioms primitive_tiny_real_of_failure
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false

theorem primitive_middle_real (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤3/2500) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (99847/50000)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139 :=
  primitive_middle_real_of_failure adversary q hq hy (reference_failed_le adversary q)

theorem primitive_tiny_real (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hy : (q:ℝ)/2^128≤1/2^28) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (249/125)*((PairedSmallT.prefixMass adversary q).toReal/2^128+
        (PairedSmallT.encodingMass adversary q).toReal/2^128)+
      (PairedSmallT.otherMass adversary q).toReal/2^128+(710/1000)*((q:ℝ)/2^128)^2+1/2^139 :=
  primitive_tiny_real_of_failure adversary q hq hy (reference_failed_le adversary q)
end ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem completed_partial_certified (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq] ≤
      ((2^128-q:Nat):ENNReal)⁻¹*((q*(q-1):Nat):ENNReal)*(350+1/1024)/(2*2^128)+BPair.pairTerm q := by
  apply completed_partial_bound ClaudeWCT.Bank.Paired.nearLawSpec
    ClaudeWCT.Bank.Paired.nearLawSpec_producer rfl ClaudeWCT.Bank.Paired.nearCovered_mono
    (fun X N h => by
      obtain ⟨k,t,h⟩:=h
      exact WPair.Paired.nearCovered_bank X N k t h)
    350 ClaudeWCT.Bank.Paired.nearLawSpec_mean adversary q hq

theorem excess_middle_actual :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-((99847:ENNReal)/50000-1/1024))≤147/125000 := by
  have h:=ClaudeWCT.Bank.Paired.excess_middle_certified ClaudeWCT.Bank.Paired.finiteFees_checked
  simpa (disch:=positivity) only [ENNReal.ofReal_sub,ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using h

theorem excess_tiny_actual :
    ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-((249:ENNReal)/125-1/1024))≤18/5000 := by
  have h:=ClaudeWCT.Bank.Paired.excess_tiny_certified ClaudeWCT.Bank.Paired.finiteFees_checked
  simpa (disch:=positivity) only [ENNReal.ofReal_sub,ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using h

theorem middle_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow:1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh:(q:ℝ)/2^128≤3/2500) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennreal adversary q hq
  apply middle_clean_closing adversary q hq hlow hhigh (147/125000) le_rfl ?_
    (completed_partial_certified adversary q hq)
  have hp:=CanonicalWeighted.primitive_middle_real adversary q hq hhigh
  have h:=clean_probability_real_of adversary q hq (completed_split_canonical adversary q hq)
    (99847/50000) (147/125000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/1024≤99847/50000))
    excess_middle_actual (by simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using! hp)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem tiny_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤1/2^28) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennreal adversary q hq
  apply tiny_clean_closing adversary q hq hpositive hhigh (18/5000) le_rfl ?_
    (completed_partial_certified adversary q hq)
  have hp:=CanonicalWeighted.primitive_tiny_real adversary q hq hhigh
  have h:=clean_probability_real_of adversary q hq (completed_split_canonical adversary q hq)
    (249/125) (18/5000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/1024≤249/125))
    excess_tiny_actual (by simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using! hp)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem small_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤3/2500) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  by_cases ht:(q:ℝ)/2^128≤1/2^28
  · exact tiny_bound adversary q hq hpositive ht
  · exact middle_bound adversary q hq (le_of_lt (lt_of_not_ge ht)) hhigh

#print axioms completed_partial_certified
#print axioms small_bound
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem checker_active_queries (answers : Answers) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (message : Message) (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (hw : Final.Paired.WitnessOf answers pk forgery message w)
    (hd : evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output)
    (hcheck : evalWithAnswerFn answers (Final.Paired.checkForgeryP pk log forgery) = true)
    (ho : Extract.Paired.ForestOpenings answers w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val)))
    (k : Fin 9) (t : Fin 6) (p : Fin 4) (hp : p.val = 4-WCT9.wordDigit (forestRank output k.val) t) :
    (.inl (.inr (Extract.Paired.honestInput answers (.wctChain (WCT9.digestIndex output) k.val
      (rawChildFromOutput output k).val t.val p.val))) : Spec.Domain) ∈
      queried answers (Final.Paired.checkForgeryP pk log forgery) := by
  have h := checker_slot_queries answers pk log forgery message w output hw hd hcheck ho k t p hp
  rw [WPair.Paired.honestProbe_slot] at h
  exact h
#print axioms checker_active_queries
end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem ftsHitIn_false (A : Answers) (K : LargeResidual.Coord → Prop) (qs : List Spec.Domain)
    (h : Extract.Paired.FtsHitIn A qs) (hclear : AllClear A K qs) : False := by
  obtain ⟨p,x,hfts,hb,hq,hh,hs⟩ := h
  have hp : Extract.posOf x = some p := by
    apply Extract.posOf_key_eq hb.legacy
    rw [hs,Extract.Paired.hdrBlock_honestInput,Extract.Pos.canonicalHeader_eq hb.legacy]
  apply paired_hit_false A K qs p x hq hp hb _ hh hclear
  cases p with
  | chain | leaf | node | forest => exact hfts.elim
  | wctChain | wctLeaf | wctNode => exact hb.legacy

theorem checker_bankFresh (A : Answers) (published : SigGolfCandidate.T3.Cache) (pk : Digest)
    (log : QueryLog Final.Paired.Requests) (forgery : Final.Paired.ForgeryP)
    (hgen : evalWithAnswerFn A keygen = (pk,published))
    (hlog : ∀ entry ∈ log, entry.2 = evalWithAnswerFn A (PairedOuter.FullGame.authenticatedSign published entry.1))
    (hcheck : evalWithAnswerFn A (Final.Paired.checkForgeryP pk log forgery) = true)
    (hcomplete : ∀ m, ∃ sig, evalWithAnswerFn A (SigGolfCandidate.Research.SharedForest.signPayload published m) = some sig)
    (hsource : ∀ L, WotsExtract.SourceLeaf7 L →
      Wots.CanonicalRef.referenceSearch A (Wots.CanonicalRef.sourceMessages A) L ≠ none)
    (hclear : AllClear A (LargeResidual.Paired.Known (Disclosed A published))
      (queried A (Final.Paired.checkForgeryP pk log forgery))) :
    BankFresh A published log (queried A (Final.Paired.checkForgeryP pk log forgery)) := by
  have hpk : pk = Extract.honestRoot A 0 0 := by
    have h := Extract.keygen_pk A
    change (evalWithAnswerFn A keygen).1 = Extract.honestRoot A 0 0 at h
    rw [hgen] at h
    exact h
  have hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop A) := by
    have h := (Correctness.keygen_correct A).2.1
    rw [hgen] at h
    exact h
  rcases CanonicalExtract.checkForgery_canonical_or_collision A published hcache pk hpk log hlog forgery hcheck
    with hprim | hhit | ⟨m,w,N,hw,hdc,hd,hdq,hgate,hrank,hgood,hopen,hfresh⟩
  · exact (wotsPrimitive_false A published _ hsource hprim hclear).elim
  · exact (ftsHitIn_false A _ _ hhit hclear).elim
  refine ⟨m,wrho w,wdc w,N,?_,hdq,?_,?_,?_⟩
  · exact hd
  · change ClaudeWCT.Bank.Paired.admissible N = true
    rw [ClaudeWCT.Bank.Paired.admissible_source]
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨hgate,?_⟩
    simpa only [ranksAccepted,List.all_eq_true,List.mem_finRange,forall_true_left,decide_eq_true_eq] using hrank
  · intro k t s hs
    exact Wots.PairedSmallT.checker_active_queries A pk log forgery m w N hw hd hcheck hopen k t s hs
  · exact WPair.Paired.fresh_digest_not_signer_eval A published log hlog m (wrho w) (wdc w) hcomplete hfresh
#print axioms ftsHitIn_false
#print axioms checker_bankFresh
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem cert_of_clean (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (z : PairedOuter.PaddedGame.TraceResult × Answers)
    (hz : z∈(PairedSeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z)
    (hcomp : SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2)
    (hcontext : ContextGood z.2) : CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 := by
  apply cert_of_clean_of_checker adversary q hq z hz hwin hno
  intro published pk log forgery hgen hlog hcheck hclear
  apply checker_bankFresh z.2 published pk log forgery hgen hlog hcheck _ _ hclear
  · intro message
    obtain ⟨sig,hsig⟩ := hcomp message
    rw [hgen] at hsig
    refine ⟨sig,?_⟩
    unfold SigGolfCandidate.Research.SharedForest.sign at hsig
    rw [evalWithAnswerFn_bind] at hsig
    split_ifs at hsig with hm
    · simp only [evalWithAnswerFn_pure,reduceCtorEq] at hsig
    · exact hsig
  · exact Wots.CanonicalRef.referenceSearch_complete z.2 hcontext
#print axioms cert_of_clean
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3.CanonicalSearch
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem clean_noOvR_failure (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137 := by
  simpa only [one_div] using! FtsOverflow.Paired.cleanWin_logOverflow_le adversary q hq

theorem clean_le_contact_cert (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[ContactNO adversary q | PairedSeccLaw.completedExperiment adversary q hq] +
      Pr[fun z=>CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧
        NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2 | PairedSeccLaw.completedExperiment adversary q hq] +
      1/(2:ENNReal)^139+1/(2:ENNReal)^138+1/(2:ENNReal)^137 := by
  rw [←PairedSeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  have hs : Pr[fun z=>QueryRecorded.CleanWin q z.1 | PairedSeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun z=> ContactNO adversary q z ∨
        (CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 ∧ NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) ∨
        ¬ContextGood z.2 ∨ ¬SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2 ∨
        (QueryRecorded.CleanWin q z.1 ∧ ¬NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2) |
        PairedSeccLaw.completedExperiment adversary q hq] := by
    apply Wots.Ref.pmf_probEvent_mono
    intro z hz hclean
    by_cases hno : NoOvR adversary (QueryRecorded.recordedTrace z.1) z.2
    swap
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hclean,hno⟩)))
    by_cases hcontext : ContextGood z.2
    swap
    · exact Or.inr (Or.inr (Or.inl hcontext))
    by_cases hcomp : SigningComplete z.2 (evalWithAnswerFn z.2 keygen).2
    swap
    · exact Or.inr (Or.inr (Or.inr (Or.inl hcomp)))
    by_cases hcontact : Contact adversary q z
    · exact Or.inl ⟨hcontact,hno⟩
    · exact Or.inr (Or.inl ⟨cert_of_clean adversary q hq z hz hclean hcontact hcomp hcontext,hno⟩)
  refine hs.trans ?_
  calc
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ _ := add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (probEvent_or_le _ _ _)))
    _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl
      (add_le_add (Wots.PairedSearchTable.completed_context_failure adversary q hq)
        (add_le_add (Wots.PairedSearchTable.completed_signer_failure adversary q hq)
          (clean_noOvR_failure adversary q hq))))
    _ = _ := by ac_rfl
#print axioms clean_noOvR_failure
#print axioms clean_le_contact_cert
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem large_clean_closing (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : (3:ℝ)/2500≤(q:ℝ)/2^128)
    (hclean : Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq] ≤
      ENNReal.ofReal (2*((q:ℝ)/2^128)-((q:ℝ)/2^128)^2)+
      (q:ENNReal)*ENNReal.ofReal ((49/50)*((q:ℝ)/2^128))/2^128+
      1/(2:ENNReal)^139+1/(2:ENNReal)^138+1/(2:ENNReal)^137) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply Wots.PairedSmallT.clean_outer_ennreal adversary q hq
  let y : ℝ := (q:ℝ)/2^128
  have hy : 0≤y := by dsimp [y];positivity
  have hhalf : y≤1/2 := by
    have hqr : (q:ℝ)≤2^127 := by exact_mod_cast hq
    dsimp [y]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^128)).2
    calc
      (q:ℝ) ≤ 2^127 := hqr
      _ = (1/2:ℝ)*2^128 := by norm_num
  have hpoly : 0≤2*y-y^2 := by nlinarith
  have hrate : 0≤(49/50:ℝ)*y := mul_nonneg (by norm_num) hy
  have hr := ENNReal.toReal_mono (by finiteness) hclean
  simp (disch:=finiteness) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast,ENNReal.toReal_one] at hr
  change _ ≤ ENNReal.toReal (ENNReal.ofReal (2*y-y^2))+
    (q:ℝ)*ENNReal.toReal (ENNReal.ofReal ((49/50)*y))/2^128+1/2^139+1/2^138+1/2^137 at hr
  rw [ENNReal.toReal_ofReal hpoly,ENNReal.toReal_ofReal hrate] at hr
  have hmul : (q:ℝ)*((49/50)*y)/2^128=y*((49/50)*y) := by dsimp [y];ring
  rw [hmul] at hr
  have hlow' : 1000/4194304≤y := (by norm_num : (1000:ℝ)/4194304≤3/2500).trans hlow
  have hc := ContinuousPricing.large_closing_real y ((49/50)*y) hlow' le_rfl
  have he : (1:ℝ)/2^139+1/2^138+1/2^137≤1/2^131 := by norm_num
  have hp1 : 0≤y*((1:ℝ)/2^25) := mul_nonneg hy (by positivity)
  have hp2 : 0≤y*((1:ℝ)/2^50) := mul_nonneg hy (by positivity)
  change _+ (y/2^18+1/2^700+1/2^152+y/2^128)≤2*y
  linarith

#print axioms large_clean_closing
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Security.LargeCoupling.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem large_bound (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow : (3:ℝ)/2500≤(q:ℝ)/2^128) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  have hhalf : (q:ℝ)/2^128≤1/2 := by
    have hqr : (q:ℝ)≤2^127 := by exact_mod_cast hq
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^128)).2
    calc
      (q:ℝ) ≤ 2^127 := hqr
      _ = (1/2:ℝ)*2^128 := by norm_num
  have hexc := ClaudeWCT.Bank.Paired.excess_large_certified
    ClaudeWCT.Bank.Paired.finiteFees_checked ((q:ℝ)/2^128) hlow hhalf
  have hexc' : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-ENNReal.ofReal (Flexible.budgetRate q-1/1024))≤
      ENNReal.ofReal ((49/50)*((q:ℝ)/2^128)) := by
    simpa only [Flexible.budgetRate,mul_div_assoc] using hexc
  apply large_clean_closing adversary q hq hlow
  exact (clean_le_contact_cert adversary q hq).trans
    (add_le_add (add_le_add (add_le_add
      (contact_cert_bound_of_excess adversary q hq _ hexc') le_rfl) le_rfl) le_rfl)
#print axioms large_bound
end ClaudeWCT.W9.T3.Security.LargeCoupling.Paired

namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem t3_securityP : SecurityP := by
  apply PairedOuter.PaddedGame.securityP_of_clean_bound
  intro adversary q hpositive hq
  by_cases hsmall : (q:ℝ)/2^128 ≤ 3/2500
  · exact Wots.PairedSmallT.small_bound adversary q hq hpositive hsmall
  · exact LargeCoupling.Paired.large_bound adversary q hq (le_of_not_ge hsmall)
end ClaudeWCT.W9.T3.Secc.Paired
