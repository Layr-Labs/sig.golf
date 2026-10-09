import SigGolfCandidate.T3.Secc.WotsTwoContacts
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
def ContactFirstBound (adversary : AdversaryP) (q : Nat) : Prop :=
  Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧ SmallP.ContactFirst s.answers s.trace a | referenceExperiment adversary q] ≤
    57 * ((q : ENNReal) / 2 ^ 128) * refExpect adversary q contactCount
def MarkerSumBound (adversary : AdversaryP) (q : Nat) : Prop :=
  ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain7 ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
    (2865 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount
noncomputable def prefixCoeffW9 (q : Nat) : ENNReal :=
  (242 / 1000 : ENNReal) *
    (((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) /
        (1 - (q : ENNReal) / 2 ^ 128) +
      4 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
      2 * 57 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)) +
    (758 / 1000 : ENNReal) * 2 / (1 - (q : ENNReal) / 2 ^ 128)
noncomputable def encodingCoeffW9 (q : Nat) : ENNReal :=
  1 + (242 / 1000 : ENNReal) * 2 * 2865 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128)
/-- Coefficient of the total seed-test error `Leaf.errTot` in the small-route primitive bound (campaign X1 B3). -/
noncomputable def errCoeffW9 (q : Nat) : ENNReal :=
  (242 / 1000 : ENNReal) *
    ((1 + twoEdgeRate q * q) / (1 - (q : ENNReal) / 2 ^ 128) +
      (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
        (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) +
      (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) +
      57 * ((q : ENNReal) / 2 ^ 128) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))) +
    (758 / 1000 : ENNReal) * ((1 + (2 / 2 ^ 128) * q) / (1 - (q : ENNReal) / 2 ^ 128))
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
        ((2865 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) +
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
      57 * ((q : ENNReal) / 2 ^ 128) *
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
  have hab : (242 / 1000 : ENNReal) + 758 / 1000 = 1 :=
    (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp (by
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
        ENNReal.toReal_one]
      norm_num)
  refine (SigGolfCandidate.T3.Security.Wots.SmallP.probEvent_le_six_split _ _ _ _ _ _ _ _ (fun s h => SmallP.primitive_cases s.answers s.trace h)
    (242 / 1000) (758 / 1000) hab).trans ?_
  have h1 := reference_encodingMatch_le adversary q
  have h2 := reference_structural_src_le adversary q
  have h3 := reference_twoEdge_le adversary q hq
  have h5a := reference_markerFirst_sum_le adversary q hq hMS
  have h5b := reference_markerFirst_contact_le adversary q hq
  have h6 := reference_contactFirst_cost_le adversary q hq hCF
  calc _ ≤ (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q encodingCount +
        (2 ^ 128 : ENNReal)⁻¹ * refExpect adversary q otherCount +
        ((242 / 1000 : ENNReal) *
          ((twoEdgeRate q * refExpect adversary q prefixClassCount + (1 + twoEdgeRate q * q) * Leaf.errTot adversary q) /
              (1 - (q : ENNReal) / 2 ^ 128) +
            ((4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * refExpect adversary q prefixClassCount /
              (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
              (2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 +
                (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128)) * Leaf.errTot adversary q) +
            (2 * ((q : ENNReal) / 2 ^ 128) / (1 - (q : ENNReal) / 2 ^ 128) *
              ((2865 / 2 ^ 128 : ENNReal) * refExpect adversary q encodingCount) +
              (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) * Leaf.errTot adversary q) +
            57 * ((q : ENNReal) / 2 ^ 128) *
              (((2 / 2 ^ 128) * refExpect adversary q prefixClassCount + (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q) /
                (1 - (q : ENNReal) / 2 ^ 128))) +
          (758 / 1000 : ENNReal) * (((2 / 2 ^ 128) * refExpect adversary q prefixClassCount +
            (1 + (2 / 2 ^ 128) * q) * Leaf.errTot adversary q) / (1 - (q : ENNReal) / 2 ^ 128))) := by
        gcongr
        · exact h1
        · exact h2
        · exact h3
        · exact hTC
    _ = _ := by
        unfold prefixCoeffW9 encodingCoeffW9 errCoeffW9 twoEdgeRate
        simp only [div_eq_mul_inv]
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
noncomputable def classRateW9 : ENNReal := 189937 / 100000
theorem inv_one_sub_leW9 (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ 4194304 / 4191586 := by
  calc (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ (4191586 / 4194304 : ENNReal)⁻¹ :=
        ENNReal.inv_le_inv.mpr (SeccClosingW9.one_sub_x_ge_of_small q hs)
    _ = 4194304 / 4191586 := ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp))
theorem prefixCoeffW9_le (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) : prefixCoeffW9 q ≤ classRateW9 := by
  have hx := SeccClosingW9.x_le_of_small q hs
  have hu := inv_one_sub_leW9 q hs
  unfold prefixCoeffW9 classRateW9
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ (1 - x),
    ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (242 / 1000 : ENNReal) * (((3 / 2 : ENNReal) + 4 * x + 2 * x ^ 2) * u + 4 * x * u ^ 2 + 2 * 57 * x * u) +
        (758 / 1000 : ENNReal) * 2 * u
      ≤ (242 / 1000 : ENNReal) *
          (((3 / 2 : ENNReal) + 4 * (2718 / 4194304 : ENNReal) + 2 * ((2718 / 4194304 : ENNReal))^2) * (4194304/4191586) +
            4 * (2718 / 4194304 : ENNReal) * (4194304/4191586)^2 + 2 * 57 * (2718 / 4194304 : ENNReal) * (4194304/4191586)) +
          (758 / 1000 : ENNReal) * 2 * (4194304/4191586) := by
        gcongr
    _ ≤ 189937 / 100000 := by
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
  calc (1 : ENNReal) + (242 / 1000 : ENNReal) * 2 * 2865 * x * u
      ≤ 1 + (242 / 1000 : ENNReal) * 2 * 2865 * (2718 / 4194304 : ENNReal) * (4194304/4191586) := by gcongr
    _ ≤ 189937 / 100000 := by
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
  calc (242 / 1000 : ENNReal) * ((1 + (3 / 2 + 4 * x + 2 * x ^ 2) * x) * u +
        (2 * x * (1 + 2 * x) * u ^ 2 + (1 + 2 * x) * u) + (1 + 2 * x) * u + 57 * x * ((1 + 2 * x) * u)) +
        758 / 1000 * ((1 + 2 * x) * u)
      ≤ (242 / 1000 : ENNReal) *
          ((1 + (3 / 2 + 4 * (2718 / 4194304 : ENNReal) + 2 * (2718 / 4194304 : ENNReal) ^ 2) * (2718 / 4194304 : ENNReal)) *
              (4194304 / 4191586) +
            (2 * (2718 / 4194304 : ENNReal) * (1 + 2 * (2718 / 4194304 : ENNReal)) * (4194304 / 4191586) ^ 2 +
              (1 + 2 * (2718 / 4194304 : ENNReal)) * (4194304 / 4191586)) +
            (1 + 2 * (2718 / 4194304 : ENNReal)) * (4194304 / 4191586) +
            57 * (2718 / 4194304 : ENNReal) * ((1 + 2 * (2718 / 4194304 : ENNReal)) * (4194304 / 4191586))) +
          758 / 1000 * ((1 + 2 * (2718 / 4194304 : ENNReal)) * (4194304 / 4191586)) := by
        gcongr
    _ ≤ 2 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
theorem errTerm_le (adversary : AdversaryP) (q : Nat) (hs : q ≤ SeccClosingW9.budgetSplit) :
    errCoeffW9 q * Leaf.errTot adversary q ≤ (702 / 1000 : ENNReal) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  have hs' : q ≤ 2718 * 2 ^ 106 := by rw [SeccClosingW9.budgetSplit_def] at hs; exact hs
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
      ≤ (4194304 / 4191586 * x) * ((150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 63 * (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (4194304 / 4191586 * (150 + 63 * 201 * ((2 : ENNReal) ^ 25)⁻¹)) * x ^ 2 +
          (4194304 / 4191586 * (63 * (2 : ENNReal)⁻¹ ^ 700)) * x := by ring
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
    _ ≤ (1 / 2 : ENNReal) * (4194304 / 4191586 * ((q : ENNReal) / 2 ^ 128)) ^ 2 := by gcongr
    _ = ((1 / 2 : ENNReal) * (4194304 / 4191586 : ENNReal) ^ 2) * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
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
