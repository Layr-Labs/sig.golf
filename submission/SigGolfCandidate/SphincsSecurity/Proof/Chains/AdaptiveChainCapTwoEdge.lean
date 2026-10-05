import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCountedRows
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapObservation

section


namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
noncomputable def contactCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Nat :=
  ∑ query : Fin n × State, if query.1.val + 1 = n ∧ observed query.1 query.2 = some endpoint then 1 else 0
theorem contactCount_empty {n : Nat} (endpoint : State) : contactCount (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [contactCount]
theorem contactCount_succ {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State) :
    contactCount observed endpoint = ∑ input : State, if observed (Fin.last n) input = some endpoint then 1 else 0 := by
  rw [contactCount, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp only [Fin.val_last, true_and]
  · intro step _ hstep
    have hn : step.val + 1 ≠ n + 1 := by
      intro hn
      apply hstep
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    simp only [hn, false_and, if_false, Finset.sum_const_zero]
  · simp
theorem contactCount_tail {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) :
    contactCount (Fin.tail observed) endpoint = contactCount observed endpoint := by
  simp only [contactCount_succ, Fin.tail, Fin.succ_last]
theorem contactCount_single (observed : Fin 1 → State → Option State) (endpoint : State) :
    contactCount observed endpoint = knownCount observed endpoint := by
  rw [contactCount_succ, knownCount]
  apply Finset.sum_congr rfl
  intro input _
  cases hrow : observed 0 input <;> simp [knownRun, hrow]
omit [Fintype State] in
theorem record_at_other {n : Nat} (observed : Fin n → State → Option State) (query other : Fin n × State)
    (answer : State) (h : other ≠ query) : record observed query answer other.1 other.2 = observed other.1 other.2 := by
  by_cases hs : other.1 = query.1
  · have hi : other.2 ≠ query.2 := fun heq => h (Prod.ext hs heq)
    simp only [record, hs, Function.update_self, Function.update_of_ne hi]
  · simp only [record, Function.update_of_ne hs]
theorem contactCount_record_fresh {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer endpoint : State) (hfresh : observed query.1 query.2 = none) :
    contactCount (record observed query answer) endpoint =
      contactCount observed endpoint + if query.1.val + 1 = n ∧ answer = endpoint then 1 else 0 := by
  have hfun : (fun other : Fin n × State =>
      if other.1.val + 1 = n ∧ record observed query answer other.1 other.2 = some endpoint then 1 else 0) =
      Function.update (fun other : Fin n × State => if other.1.val + 1 = n ∧ observed other.1 other.2 = some endpoint then 1 else 0)
        query (if query.1.val + 1 = n ∧ answer = endpoint then 1 else 0) := by
    funext other
    by_cases ho : other = query
    · subst other
      simp only [record, Function.update_self, Option.some.injEq]
    · simp only [record_at_other observed query other answer ho, Function.update_of_ne ho]
  rw [contactCount, hfun, Finset.sum_update_of_mem (Finset.mem_univ query), Finset.sdiff_singleton_eq_erase,
    contactCount, ← Finset.add_sum_erase Finset.univ
      (fun other : Fin n × State => if other.1.val + 1 = n ∧ observed other.1 other.2 = some endpoint then 1 else 0)
      (Finset.mem_univ query)]
  simp only [hfresh, reduceCtorEq, and_false, if_false, Nat.zero_add, Nat.add_comm]
theorem contactCount_observe_increment_le [Nonempty State] {n : Nat}
    (value increment : Nat → ENNReal) (hincrement : ∀ k, value (k + 1) = value k + increment k)
    (observed : Fin n → State → Option State) (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * value (contactCount (record observed query answer) endpoint)) ≤
      value (contactCount observed endpoint) + increment (contactCount observed endpoint) / Fintype.card State := by
  cases hrow : observed query.1 query.2 with
  | some answer =>
      simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
      exact _root_.le_add_of_nonneg_right bot_le
  | none =>
      simp only [rowLaw, contactCount_record_fresh observed query _ endpoint hrow]
      by_cases hlast : query.1.val + 1 = n
      · simp only [hlast, true_and]
        have hvalue (answer : State) : value (contactCount observed endpoint + if answer = endpoint then 1 else 0) =
            value (contactCount observed endpoint) + if answer = endpoint then increment (contactCount observed endpoint) else 0 := by
          by_cases heq : answer = endpoint <;> simp only [heq, if_true, if_false, hincrement, add_zero]
        simp only [hvalue, expectation_add, expectation_const]
        simp only [mul_ite, mul_zero, tsum_ite_eq, PMF.uniformOfFintype_apply]
        exact le_of_eq (by rw [div_eq_mul_inv, mul_comm])
      · simp only [hlast, false_and, if_false, Nat.add_zero, expectation_const]
        exact _root_.le_add_of_nonneg_right bot_le
theorem contactCount_observe_le [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * (contactCount (record observed query answer) endpoint : ENNReal)) ≤
      (contactCount observed endpoint : ENNReal) + 1 / Fintype.card State :=
  contactCount_observe_increment_le (fun k => k) (fun _ => 1) (fun k => by simp only [Nat.cast_add, Nat.cast_one]) observed query endpoint
def contactFactorial (k : Nat) : Nat := k * (k - 1)
theorem contactFactorial_succ (k : Nat) : contactFactorial (k + 1) = contactFactorial k + 2 * k := by
  cases k with
  | zero => rfl
  | succ k => simp only [contactFactorial, Nat.add_sub_cancel]; ring
theorem contactFactorial_observe_le [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * (contactFactorial (contactCount (record observed query answer) endpoint) : ENNReal)) ≤
      (contactFactorial (contactCount observed endpoint) : ENNReal) + (2 * contactCount observed endpoint : Nat) / (Fintype.card State : ENNReal) :=
  contactCount_observe_increment_le (fun k => contactFactorial k) (fun k => (2 * k : Nat))
    (fun k => by rw [contactFactorial_succ, Nat.cast_add]) observed query endpoint
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
def TwoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) : Prop :=
  ∃ start middle, observed (Fin.last n).castSucc start = some middle ∧ observed (Fin.last (n + 1)) middle = some endpoint
omit [Fintype State] [DecidableEq State] in
theorem twoEdge_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (hextends : Extends before after)
    (endpoint : State) (h : TwoEdge before endpoint) : TwoEdge after endpoint := by
  obtain ⟨start, middle, hfirst, hlast⟩ := h
  exact ⟨start, middle, hextends _ _ _ hfirst, hextends _ _ _ hlast⟩
omit [Fintype State] [DecidableEq State] in
theorem twoEdge_tail {n : Nat} (observed : Fin (n + 3) → State → Option State) (endpoint : State)
    (h : TwoEdge (Fin.tail observed) endpoint) : TwoEdge observed endpoint := by
  obtain ⟨start, middle, hfirst, hlast⟩ := h
  have hindex : (Fin.last n).castSucc.succ = (Fin.last (n + 1)).castSucc := by apply Fin.ext; rfl
  exact ⟨start, middle, by simpa only [Fin.tail, hindex] using hfirst, by simpa only [Fin.tail, Fin.succ_last] using hlast⟩
omit [Fintype State] [DecidableEq State] in
theorem knownRun_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (start endpoint : State)
    (h : knownRun observed start = some endpoint) : TwoEdge observed endpoint := by
  induction n generalizing start with
  | zero =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hfirst, hlast⟩ := h
      change (observed 1 middle).bind (fun value => some value) = some endpoint at hlast
      have hrow : observed 1 middle = some endpoint := by
        cases hrow : observed 1 middle <;> simpa only [hrow, Option.bind_none, Option.bind_some] using hlast
      exact ⟨start, middle, hfirst, hrow⟩
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨middle, _, htail⟩ := h
      exact twoEdge_tail observed endpoint (ih (Fin.tail observed) middle htail)
theorem knownCount_eq_zero_of_no_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State)
    (h : ¬TwoEdge observed endpoint) : knownCount observed endpoint = 0 := by
  unfold knownCount
  apply Finset.sum_eq_zero
  intro start _
  exact if_neg (fun hrun => h (knownRun_twoEdge observed start endpoint hrun))
theorem targetCount_eq_contactCount_of_no_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State)
    (h : ¬TwoEdge observed endpoint) : targetCount observed endpoint = contactCount observed endpoint := by
  induction n with
  | zero =>
      rw [targetCount, knownCount_eq_zero_of_no_twoEdge observed endpoint h, Nat.zero_add, targetCount, targetCount, Nat.add_zero,
        ← contactCount_single, contactCount_tail]
  | succ n ih =>
      rw [targetCount, knownCount_eq_zero_of_no_twoEdge observed endpoint h, Nat.zero_add,
        ih (Fin.tail observed) (fun htail => h (twoEdge_tail observed endpoint htail)), contactCount_tail]
theorem meanPreimages_le_contactCount_of_no_twoEdge [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages observed endpoint ≤ (1 + contactCount observed endpoint : Nat) := by
  have hbound := meanPreimages_le_suffixCount observed endpoint
  rwa [suffixCount_eq_targetCount, targetCount_eq_contactCount_of_no_twoEdge observed endpoint h] at hbound
omit [Fintype State] in
theorem twoEdge_record_earlier {n : Nat} (observed : Fin (n + 2) → State → Option State) (query : Fin (n + 2) × State)
    (answer endpoint : State) (hfirst : (Fin.last n).castSucc ≠ query.1) (hlast : Fin.last (n + 1) ≠ query.1) :
    TwoEdge (record observed query answer) endpoint ↔ TwoEdge observed endpoint := by
  simp only [TwoEdge, record, Function.update_of_ne hfirst, Function.update_of_ne hlast]
omit [Fintype State] in
theorem twoEdge_record_last {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer endpoint : State)
    (h : ¬TwoEdge observed endpoint) :
    TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint ↔
      answer = endpoint ∧ ∃ start, observed (Fin.last n).castSucc start = some input := by
  have hindex : (Fin.last n).castSucc ≠ Fin.last (n + 1) := by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
  constructor
  · rintro ⟨start, middle, hfirst, hlast⟩
    have hfirst' : observed (Fin.last n).castSucc start = some middle := by
      simpa only [record, Function.update_of_ne hindex] using hfirst
    by_cases hm : middle = input
    · subst middle
      exact ⟨by simpa only [record, Function.update_self, Option.some.injEq] using hlast, start, hfirst'⟩
    · exact False.elim (h ⟨start, middle, hfirst', by simpa only [record, Function.update_self, Function.update_of_ne hm] using hlast⟩)
  · rintro ⟨rfl, start, hfirst⟩
    exact ⟨start, input, by simpa only [record, Function.update_of_ne hindex] using hfirst,
      by simp only [record, Function.update_self]⟩
omit [Fintype State] in
theorem twoEdge_record_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer endpoint : State)
    (h : ¬TwoEdge observed endpoint) :
    TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint ↔ observed (Fin.last (n + 1)) answer = some endpoint := by
  have hindex : Fin.last (n + 1) ≠ (Fin.last n).castSucc := by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
  constructor
  · rintro ⟨start, middle, hfirst, hlast⟩
    have hlast' : observed (Fin.last (n + 1)) middle = some endpoint := by
      simpa only [record, Function.update_of_ne hindex] using hlast
    by_cases hs : start = input
    · subst start
      have hm : answer = middle := by simpa only [record, Function.update_self, Option.some.injEq] using hfirst
      simpa only [hm] using hlast'
    · exact False.elim (h ⟨start, middle, by simpa only [record, Function.update_self, Function.update_of_ne hs] using hfirst, hlast'⟩)
  · intro hlast
    exact ⟨input, answer, by simp only [record, Function.update_self], by simpa only [record, Function.update_of_ne hindex] using hlast⟩
theorem twoEdge_last_probability [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (input endpoint : State)
    (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last (n + 1)) input = none) :
    Pr[fun answer => TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint |
      rowLaw (observed (Fin.last (n + 1)) input)] =
        if ∃ start, observed (Fin.last n).castSucc start = some input then 1 / (Fintype.card State : ENNReal) else 0 := by
  classical
  simp only [hfresh, rowLaw, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    twoEdge_record_last observed input _ endpoint h]
  by_cases hp : ∃ start, observed (Fin.last n).castSucc start = some input
  · simp only [hp, and_true, if_true, tsum_ite_eq, PMF.uniformOfFintype_apply, one_div]
  · simp only [hp, and_false, if_false, tsum_zero]
theorem twoEdge_penultimate_probability [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (input endpoint : State)
    (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last n).castSucc input = none) :
    Pr[fun answer => TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint |
      rowLaw (observed (Fin.last n).castSucc input)] = (contactCount observed endpoint : ENNReal) / Fintype.card State := by
  classical
  simp only [hfresh, rowLaw, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    twoEdge_record_penultimate observed input _ endpoint h, PMF.uniformOfFintype_apply, tsum_fintype,
    contactCount_succ, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_mul_inv,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
private theorem weighted_event_le_bound {Result : Type} (law : PMF Result) (weight : Result → ENNReal)
    (event : Result → Prop) [DecidablePred event] (bound : ENNReal) (hbound : ∀ result, weight result ≤ bound) :
    (∑' result, law result * (weight result * if event result then 1 else 0)) ≤ bound * Pr[event | law] := by
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : event result
  · simpa only [hevent, if_true, mul_one, PMF.probOutput_eq_apply, mul_comm] using mul_le_mul' (hbound result) (le_refl (law result))
  · simp only [hevent, if_false, mul_zero, le_refl]
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
omit [DecidableEq State] in
theorem kernel_snoc {n : Nat} (before : Fin n → State → Option State) (last : State → Option State) :
    kernel (Fin.snoc before last) = fun start => (kernel before start).bind (fun input => rowLaw (last input)) := by
  induction n with
  | zero => funext start; simp [kernel, Fin.snoc_zero]
  | succ n ih =>
      funext start
      have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
      rw [hs, kernel, Fin.cons_zero, Fin.tail_cons]
      rw [ih]
      simp only [kernel, PMF.bind_bind]
theorem row_update_charge (prior : PMF State) (observed : State → Option State) (next : State → PMF State)
    (input answer endpoint : State) :
    prior.bind (fun start => (rowLaw (Function.update observed input (some answer) start)).bind next) endpoint ≤
      prior.bind (fun start => (rowLaw (observed start)).bind next) endpoint + prior input := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' start, prior start * (((rowLaw (observed start)).bind next) endpoint + if start = input then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro start
      apply mul_le_mul' le_rfl
      by_cases hs : start = input
      · rw [if_pos hs]
        exact (PMF.coe_le_one _ endpoint).trans (_root_.le_add_of_nonneg_left bot_le)
      · simp only [Function.update_of_ne hs, if_neg hs, add_zero, le_refl]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, tsum_ite_eq, PMF.bind_apply]
theorem meanPreimages_last_update_le {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer endpoint : State) :
    meanPreimages (Fin.snoc before (Function.update last input (some answer))) endpoint ≤
      meanPreimages (Fin.snoc before last) endpoint + meanPreimages before input := by
  have h := row_update_charge ((PMF.uniformOfFintype State).bind (kernel before)) last PMF.pure input answer endpoint
  simp only [PMF.bind_pure] at h
  have hscaled := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) h
  simpa only [meanPreimages_eq, kernel_snoc, PMF.bind_bind, mul_add] using hscaled
theorem meanPreimages_penultimate_update_le {n : Nat} (before : Fin n → State → Option State)
    (penultimate last : State → Option State) (input answer endpoint : State) :
    meanPreimages (Fin.snoc (Fin.snoc before (Function.update penultimate input (some answer))) last) endpoint ≤
      meanPreimages (Fin.snoc (Fin.snoc before penultimate) last) endpoint + meanPreimages before input := by
  have h := row_update_charge ((PMF.uniformOfFintype State).bind (kernel before)) penultimate
    (fun middle => rowLaw (last middle)) input answer endpoint
  have hscaled := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) h
  simpa only [meanPreimages_eq, kernel_snoc, PMF.bind_bind, mul_add] using hscaled
theorem meanPreimages_record_last_le {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (input answer endpoint : State) :
    meanPreimages (record observed (Fin.last n, input) answer) endpoint ≤
      meanPreimages observed endpoint + meanPreimages (Fin.init observed) input := by
  have h := meanPreimages_last_update_le (Fin.init observed) (observed (Fin.last n)) input answer endpoint
  rw [Fin.snoc_init_self] at h
  have hrecord : record observed (Fin.last n, input) answer =
      Fin.snoc (Fin.init observed) (Function.update (observed (Fin.last n)) input (some answer)) := by
    conv_lhs => rw [← Fin.snoc_init_self observed]
    simp only [record, Fin.snoc_last, Fin.update_snoc_last]
  simpa only [hrecord] using h
theorem meanPreimages_record_penultimate_le {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) :
    meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint ≤
      meanPreimages observed endpoint + meanPreimages (Fin.init (Fin.init observed)) input := by
  have h := meanPreimages_penultimate_update_le (Fin.init (Fin.init observed)) ((Fin.init observed) (Fin.last n))
    (observed (Fin.last (n + 1))) input answer endpoint
  rw [Fin.snoc_init_self, Fin.snoc_init_self] at h
  have hrecord : record observed ((Fin.last n).castSucc, input) answer =
      Fin.snoc (Fin.snoc (Fin.init (Fin.init observed))
        (Function.update ((Fin.init observed) (Fin.last n)) input (some answer))) (observed (Fin.last (n + 1))) := by
    conv_lhs => rw [← Fin.snoc_init_self observed, ← Fin.snoc_init_self (Fin.init observed)]
    simp only [record, Fin.snoc_castSucc, Fin.snoc_last, ← Fin.snoc_update, Fin.update_snoc_last]
  simpa only [hrecord] using h
theorem twoEdge_last_density_charge {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint ≤
      (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat) := by
  have hprefix := meanPreimages_le_suffixCount (Fin.init observed) input
  rw [suffixCount_eq_targetCount] at hprefix
  apply (meanPreimages_record_last_le observed input answer endpoint).trans
  have hsum := _root_.add_le_add (meanPreimages_le_contactCount_of_no_twoEdge observed endpoint h) hprefix
  convert hsum using 1
  push_cast
  ring
theorem twoEdge_penultimate_density_charge {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint ≤
      (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input : Nat) := by
  have hprefix := meanPreimages_le_suffixCount (Fin.init (Fin.init observed)) input
  rw [suffixCount_eq_targetCount] at hprefix
  apply (meanPreimages_record_penultimate_le observed input answer endpoint).trans
  have hsum := _root_.add_le_add (meanPreimages_le_contactCount_of_no_twoEdge observed endpoint h) hprefix
  convert hsum using 1
  push_cast
  ring
theorem twoEdge_last_weighted_risk {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input endpoint : State) (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last (n + 1)) input = none) :
    (∑' answer, rowLaw (observed (Fin.last (n + 1)) input) answer *
      (meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint *
        if TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint then 1 else 0)) ≤
      if ∃ start, observed (Fin.last n).castSucc start = some input then
        (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat) / (Fintype.card State : ENNReal) else 0 := by
  classical
  apply (weighted_event_le_bound (rowLaw (observed (Fin.last (n + 1)) input))
    (fun answer => meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint)
    (fun answer => TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint)
    (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat)
    (fun answer => twoEdge_last_density_charge observed input answer endpoint h)).trans_eq
  rw [twoEdge_last_probability observed input endpoint h hfresh]
  split <;> simp only [mul_zero, div_eq_mul_inv, one_mul]
theorem twoEdge_penultimate_weighted_risk {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input endpoint : State) (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last n).castSucc input = none) :
    (∑' answer, rowLaw (observed (Fin.last n).castSucc input) answer *
      (meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint *
        if TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint then 1 else 0)) ≤
      (contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input) : Nat) /
        (Fintype.card State : ENNReal) := by
  classical
  apply (weighted_event_le_bound (rowLaw (observed (Fin.last n).castSucc input))
    (fun answer => meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint)
    (fun answer => TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint)
    (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input : Nat)
    (fun answer => twoEdge_penultimate_density_charge observed input answer endpoint h)).trans_eq
  rw [twoEdge_penultimate_probability observed input endpoint h hfresh]
  simp only [Nat.cast_mul, div_eq_mul_inv]
  ring
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
noncomputable def longCompleted : {n : Nat} → (Fin n → State → Option State) → Nat
  | 0, _ => 0
  | 1, _ => 0
  | _ + 2, observed => (∑ endpoint : State, knownCount observed endpoint) + longCompleted (Fin.tail observed)
omit [Fintype State] [DecidableEq State] in
theorem Extends.init {n : Nat} {before after : Fin (n + 1) → State → Option State} (h : Extends before after) :
    Extends (Fin.init before) (Fin.init after) := fun step input answer => h step.castSucc input answer
theorem longCompleted_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) :
    longCompleted before ≤ longCompleted after := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      cases n with
      | zero => exact le_rfl
      | succ n =>
          exact Nat.add_le_add (Finset.sum_le_sum fun endpoint _ => knownCount_mono h endpoint) (ih h.tail)
theorem knownCount_sum_single (observed : Fin 1 → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) = queriedCount (observed 0) := by
  rw [knownCount_sum, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases hrow : observed 0 input <;> simp [knownRun, hrow]
theorem completedCount_eq_longCompleted {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    completedCount observed = longCompleted observed + queriedCount (observed (Fin.last n)) := by
  induction n with
  | zero =>
      simp only [completedCount, targetCount, Nat.add_zero, longCompleted, Nat.zero_add]
      exact knownCount_sum_single observed
  | succ n ih =>
      change (∑ endpoint : State, (knownCount observed endpoint + targetCount (Fin.tail observed) endpoint)) = _
      rw [Finset.sum_add_distrib]
      change (∑ endpoint : State, knownCount observed endpoint) + completedCount (Fin.tail observed) = _
      rw [ih (Fin.tail observed)]
      simp only [longCompleted, Fin.tail, Fin.succ_last, Nat.add_assoc]
omit [DecidableEq State] in
theorem queryCount_split_last {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    queryCount observed = queryCount (Fin.init observed) + queriedCount (observed (Fin.last n)) := by
  simp only [queryCount, Fin.sum_univ_castSucc, Fin.init]
theorem longCompleted_le_prefix_queries {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    longCompleted observed ≤ queryCount (Fin.init observed) := by
  have h := completedCount_le_queryCount observed
  rw [completedCount_eq_longCompleted, queryCount_split_last] at h
  omega
theorem longCompleted_le_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    longCompleted observed ≤ queryCount observed := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
      have h := longCompleted_le_prefix_queries observed
      rw [queryCount_split_last]
      omega
theorem longCompleted_empty {n : Nat} : longCompleted (fun (_ : Fin n) (_ : State) => none) = 0 := by
  have h := longCompleted_le_queryCount (fun (_ : Fin n) (_ : State) => none)
  rw [queryCount_empty] at h
  omega
omit [Fintype State] [DecidableEq State] in
theorem tail_snoc {n : Nat} (before : Fin (n + 1) → State → Option State) (last : State → Option State) :
    @Fin.tail (n + 1) (fun _ => State → Option State) (Fin.snoc before last) =
      (Fin.snoc (Fin.tail before) last : Fin (n + 1) → State → Option State) := by
  have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
    rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
  rw [hs, Fin.tail_cons]
omit [Fintype State] [DecidableEq State] in
theorem knownRun_snoc {n : Nat} (before : Fin n → State → Option State) (last : State → Option State) :
    knownRun (Fin.snoc before last) = fun start => (knownRun before start).bind last := by
  induction n with
  | zero => funext start; simp [knownRun, Fin.snoc_zero]
  | succ n ih =>
      funext start
      have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
      rw [hs, knownRun, Fin.cons_zero, Fin.tail_cons, ih]
      simp only [knownRun, Option.bind_assoc]
theorem knownCount_sum_last_fresh {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer : State) (hfresh : last input = none) :
    (∑ endpoint : State, knownCount (Fin.snoc before (Function.update last input (some answer))) endpoint) =
      (∑ endpoint : State, knownCount (Fin.snoc before last) endpoint) + knownCount before input := by
  rw [knownCount_sum, knownCount_sum]
  simp only [knownCount, ← Finset.sum_add_distrib, knownRun_snoc]
  apply Finset.sum_congr rfl
  intro start _
  cases hrun : knownRun before start with
  | none => simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, if_false, reduceCtorEq, Nat.add_zero]
  | some value =>
      by_cases hv : value = input
      · subst value
        simp only [Option.bind_some, Function.update_self, hfresh, Option.isSome_some, Option.isSome_none,
          Bool.false_eq_true, if_true, if_false, Nat.zero_add]
      · simp only [Option.bind_some, Function.update_of_ne hv, Option.some.injEq, if_neg hv, Nat.add_zero]
theorem longCompleted_last_fresh {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer : State) (hfresh : last input = none) :
    longCompleted (Fin.snoc before (Function.update last input (some answer))) =
      longCompleted (Fin.snoc before last) + targetCount before input := by
  induction n with
  | zero => simp only [longCompleted, targetCount, Nat.add_zero]
  | succ n ih =>
      rw [longCompleted, longCompleted, tail_snoc, tail_snoc, knownCount_sum_last_fresh before last input answer hfresh,
        ih (Fin.tail before), targetCount]
      omega
theorem longCompleted_record_last {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (input answer : State) (hfresh : observed (Fin.last n) input = none) :
    longCompleted (record observed (Fin.last n, input) answer) =
      longCompleted observed + targetCount (Fin.init observed) input := by
  have h := longCompleted_last_fresh (Fin.init observed) (observed (Fin.last n)) input answer hfresh
  rw [Fin.snoc_init_self] at h
  have hrecord : record observed (Fin.last n, input) answer =
      Fin.snoc (Fin.init observed) (Function.update (observed (Fin.last n)) input (some answer)) := by
    conv_lhs => rw [← Fin.snoc_init_self observed]
    simp only [record, Fin.snoc_last, Fin.update_snoc_last]
  simpa only [hrecord] using h
omit [Fintype State] in
theorem init_record {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (step : Fin n) (input answer : State) :
    Fin.init (record observed (step.castSucc, input) answer) = record (Fin.init observed) (step, input) answer := by
  simp only [record, Fin.init_update_castSucc, Fin.init]
theorem longCompleted_prefix_record_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer : State) (hfresh : observed (Fin.last n).castSucc input = none) :
    longCompleted (Fin.init (record observed ((Fin.last n).castSucc, input) answer)) =
      longCompleted (Fin.init observed) + targetCount (Fin.init (Fin.init observed)) input := by
  rw [init_record]
  exact longCompleted_record_last (Fin.init observed) input answer hfresh
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
noncomputable def queriedInputs (row : State → Option State) : Finset State :=
  Finset.univ.filter fun input => row input ≠ none
noncomputable def rowImage (row : State → Option State) : Finset State :=
  Finset.univ.biUnion fun input => (row input).toFinset
omit [DecidableEq State] in
theorem mem_queriedInputs (row : State → Option State) (input : State) :
    input ∈ queriedInputs row ↔ row input ≠ none := by simp [queriedInputs]
omit [DecidableEq State] in
theorem queriedInputs_card (row : State → Option State) : (queriedInputs row).card = queriedCount row := by
  rw [queriedInputs, Finset.card_filter, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases row input <;> simp
theorem mem_rowImage (row : State → Option State) (output : State) :
    output ∈ rowImage row ↔ ∃ input, row input = some output := by
  simp only [rowImage, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset, Option.mem_def]
theorem rowImage_card_le (row : State → Option State) : (rowImage row).card ≤ queriedCount row := by
  apply Finset.card_biUnion_le.trans
  rw [queriedCount_eq_sum]
  apply Finset.sum_le_sum
  intro input _
  cases row input <;> simp
noncomputable def productiveInputs {n : Nat} (observed : Fin (n + 2) → State → Option State) : Finset State :=
  queriedInputs (observed (Fin.last (n + 1))) ∩ rowImage (observed (Fin.last n).castSucc)
noncomputable def preparationCount {n : Nat} (observed : Fin (n + 2) → State → Option State) : Nat :=
  (productiveInputs observed).card
theorem mem_productiveInputs {n : Nat} (observed : Fin (n + 2) → State → Option State) (input : State) :
    input ∈ productiveInputs observed ↔
      observed (Fin.last (n + 1)) input ≠ none ∧ ∃ start, observed (Fin.last n).castSucc start = some input := by
  simp only [productiveInputs, Finset.mem_inter, mem_queriedInputs, mem_rowImage]
theorem productiveInputs_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (h : Extends before after) :
    productiveInputs before ⊆ productiveInputs after := by
  intro input hi
  rw [mem_productiveInputs] at hi ⊢
  constructor
  · cases hr : before (Fin.last (n + 1)) input with
    | none => exact False.elim (hi.1 hr)
    | some answer => rw [h _ _ _ hr]; exact Option.some_ne_none answer
  · obtain ⟨start, hs⟩ := hi.2
    exact ⟨start, h _ _ _ hs⟩
theorem preparationCount_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (h : Extends before after) :
    preparationCount before ≤ preparationCount after := Finset.card_le_card (productiveInputs_mono h)
theorem preparationCount_le_last {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queriedCount (observed (Fin.last (n + 1))) := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (queriedInputs_card _)
theorem preparationCount_le_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queriedCount (observed (Fin.last n).castSucc) := by
  exact (Finset.card_le_card Finset.inter_subset_right).trans (rowImage_card_le _)
theorem preparationCount_le_prefix {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queryCount (Fin.init observed) := by
  apply (preparationCount_le_penultimate observed).trans
  change queriedCount ((Fin.init observed) (Fin.last n)) ≤ ∑ step, queriedCount ((Fin.init observed) step)
  exact Finset.single_le_sum (f := fun step => queriedCount ((Fin.init observed) step))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.last n))
theorem preparationCount_empty {n : Nat} : preparationCount (n := n) (fun (_ : Fin (n + 2)) (_ : State) => none) = 0 := by
  simp [preparationCount, productiveInputs, queriedInputs]
theorem preparationCount_last_fresh {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer : State)
    (hfresh : observed (Fin.last (n + 1)) input = none)
    (hprepared : ∃ start, observed (Fin.last n).castSucc start = some input) :
    preparationCount observed + 1 ≤ preparationCount (record observed (Fin.last (n + 1), input) answer) := by
  have hnot : input ∉ productiveInputs observed := by simp only [mem_productiveInputs, hfresh, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  have hmem : input ∈ productiveInputs (record observed (Fin.last (n + 1), input) answer) := by
    rw [mem_productiveInputs]
    constructor
    · simp only [record, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
    · obtain ⟨start, hs⟩ := hprepared
      refine ⟨start, ?_⟩
      rw [record_at_other observed (Fin.last (n + 1), input) ((Fin.last n).castSucc, start) answer]
      · exact hs
      · intro heq
        have hv := congrArg (fun query => query.1.val) heq
        simp only [Fin.val_castSucc, Fin.val_last] at hv
        omega
  have hsub := productiveInputs_mono (record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh))
  have hcard := Finset.card_le_card (Finset.insert_subset hmem hsub)
  rw [Finset.card_insert_of_notMem hnot] at hcard
  exact hcard
theorem preparation_charge_le_three_halves {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    2 * (longCompleted observed + 2 * preparationCount observed) ≤ 3 * queryCount observed := by
  have hd := longCompleted_le_prefix_queries observed
  have hp := preparationCount_le_prefix observed
  have hl := preparationCount_le_last observed
  rw [queryCount_split_last]
  omega
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
theorem contactCount_mono {n : Nat} {before after : Fin n → State → Option State}
    (h : Extends before after) (endpoint : State) : contactCount before endpoint ≤ contactCount after endpoint := by
  unfold contactCount
  apply Finset.sum_le_sum
  intro query _
  by_cases hk : query.1.val + 1 = n ∧ before query.1 query.2 = some endpoint
  · have hk' : query.1.val + 1 = n ∧ after query.1 query.2 = some endpoint := ⟨hk.1, h _ _ _ hk.2⟩
    simp only [if_pos hk, if_pos hk', le_refl]
  · simp only [if_neg hk, Nat.zero_le]
noncomputable def twoEdgeCharge {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State) (endpoint : State) : Nat :=
  longCompleted observed + 2 * preparationCount observed +
    spent * (contactCount observed endpoint * (contactCount observed endpoint + 2)) +
    contactCount observed endpoint * longCompleted (Fin.init observed)
theorem twoEdgeCharge_empty {n : Nat} (endpoint : State) :
    twoEdgeCharge 0 (n := n) (fun _ _ => none) endpoint = 0 := by
  simp only [twoEdgeCharge, longCompleted_empty, preparationCount_empty, contactCount_empty,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
theorem twoEdgeCharge_mono {n : Nat} {before after : Fin (n + 2) → State → Option State}
    {spent next : Nat} (hs : spent ≤ next) (h : Extends before after) (endpoint : State) :
    twoEdgeCharge spent before endpoint ≤ twoEdgeCharge next after endpoint := by
  unfold twoEdgeCharge
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (longCompleted_mono h) (Nat.mul_le_mul_left 2 (preparationCount_mono h)))
      (Nat.mul_le_mul hs (Nat.mul_le_mul (contactCount_mono h endpoint) (Nat.add_le_add_right (contactCount_mono h endpoint) 2))))
    (Nat.mul_le_mul (contactCount_mono h endpoint) (longCompleted_mono h.init))
private theorem charge_increment (d p r k d' p' r' k' spent dd dp dr : Nat)
    (hd : d + dd ≤ d') (hp : p + dp ≤ p') (hr : r + dr ≤ r') (hk : k ≤ k') :
    (d + 2 * p + spent * (k * (k + 2)) + k * r) + dd + 2 * dp + k * (k + 2) + k * dr ≤
      d' + 2 * p' + (spent + 1) * (k' * (k' + 2)) + k' * r' := by
  have hpoly := Nat.mul_le_mul (Nat.le_refl (spent + 1)) (Nat.mul_le_mul hk (Nat.add_le_add_right hk 2))
  have hprod := Nat.mul_le_mul hk hr
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hd (Nat.mul_le_mul_left 2 hp)) hpoly) hprod
  convert hsum using 1
  ring
theorem twoEdgeCharge_record_last {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (hfresh : observed (Fin.last (n + 1)) input = none)
    (hprepared : ∃ start, observed (Fin.last n).castSucc start = some input) :
    twoEdgeCharge spent observed endpoint + (2 + contactCount observed endpoint + targetCount (Fin.init observed) input) ≤
      twoEdgeCharge (spent + 1) (record observed (Fin.last (n + 1), input) answer) endpoint := by
  have hext := record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh)
  have h := charge_increment _ _ _ _ _ _ _ _ spent (targetCount (Fin.init observed) input) 1 0
    (le_of_eq (longCompleted_record_last observed input answer hfresh).symm)
    (preparationCount_last_fresh observed input answer hfresh hprepared)
    (by simpa only [Nat.add_zero] using longCompleted_mono hext.init) (contactCount_mono hext endpoint)
  change twoEdgeCharge spent observed endpoint + _ + _ + _ + _ ≤ twoEdgeCharge (spent + 1) _ endpoint at h
  have hk : contactCount observed endpoint ≤ contactCount observed endpoint * (contactCount observed endpoint + 2) := by nlinarith
  omega
theorem twoEdgeCharge_record_penultimate {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (hfresh : observed (Fin.last n).castSucc input = none) :
    twoEdgeCharge spent observed endpoint +
      contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input) ≤
      twoEdgeCharge (spent + 1) (record observed ((Fin.last n).castSucc, input) answer) endpoint := by
  have hext := record_extends observed ((Fin.last n).castSucc, input) answer (Or.inl hfresh)
  have h := charge_increment _ _ _ _ _ _ _ _ spent 0 0 (targetCount (Fin.init (Fin.init observed)) input)
    (by simpa only [Nat.add_zero] using longCompleted_mono hext)
    (by simpa only [Nat.add_zero] using preparationCount_mono hext)
    (le_of_eq (longCompleted_prefix_record_penultimate observed input answer hfresh).symm) (contactCount_mono hext endpoint)
  change twoEdgeCharge spent observed endpoint + _ + _ + _ + _ ≤ twoEdgeCharge (spent + 1) _ endpoint at h
  convert h using 1
  ring
theorem contact_correction_identity (k : Nat) : k * (k + 2) + k = contactFactorial k + 4 * k := by
  cases k with
  | zero => rfl
  | succ k => simp only [contactFactorial, Nat.add_sub_cancel]; ring
theorem twoEdgeCharge_le {n : Nat} (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ budget) :
    twoEdgeCharge spent observed endpoint ≤ longCompleted observed + 2 * preparationCount observed +
      budget * (contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint) := by
  have hr := longCompleted_le_queryCount (Fin.init observed)
  have hsplit := queryCount_split_last observed
  have hrq : longCompleted (Fin.init observed) ≤ budget := by omega
  have hprod := Nat.mul_le_mul_left (contactCount observed endpoint) hrq
  have hspent := Nat.mul_le_mul_right (contactCount observed endpoint * (contactCount observed endpoint + 2)) hs
  have hsum := Nat.add_le_add hspent hprod
  rw [Nat.mul_comm (contactCount observed endpoint) budget, ← Nat.mul_add, contact_correction_identity] at hsum
  unfold twoEdgeCharge
  omega
theorem twoEdgeCharge_twice_le {n : Nat} (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ budget) :
    2 * twoEdgeCharge spent observed endpoint ≤ 3 * queryCount observed +
      2 * budget * (contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint) := by
  have h := twoEdgeCharge_le spent budget observed endpoint hs hq
  have hbase := preparation_charge_le_three_halves observed
  nlinarith
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
noncomputable def twoEdgeWeight {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) : ENNReal :=
  meanPreimages observed endpoint * if TwoEdge observed endpoint then 1 else 0
theorem twoEdgeWeight_empty {n : Nat} (endpoint : State) :
    twoEdgeWeight (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [twoEdgeWeight, TwoEdge]
omit [DecidableEq State] [Nonempty State] in
private theorem expected_charge_cover (law : PMF State) (before increment : Nat) (after : State → Nat)
    (weight : State → ENNReal)
    (hrisk : (∑' answer, law answer * weight answer) ≤ (increment : ENNReal) / Fintype.card State)
    (hcharge : ∀ answer, before + increment ≤ after answer) :
    (before : ENNReal) / Fintype.card State + (∑' answer, law answer * weight answer) ≤
      ∑' answer, law answer * ((after answer : ENNReal) / Fintype.card State) := by
  calc
    _ ≤ (before : ENNReal) / Fintype.card State + (increment : ENNReal) / Fintype.card State := _root_.add_le_add le_rfl hrisk
    _ = ((before + increment : Nat) : ENNReal) / Fintype.card State := by simp only [Nat.cast_add, div_eq_mul_inv, add_mul]
    _ = ∑' answer, law answer * (((before + increment : Nat) : ENNReal) / Fintype.card State) := (expectation_const _ _).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (by gcongr; exact_mod_cast hcharge answer)
theorem twoEdgeCharge_observe_mono {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State ≤
      ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  cases hrow : observed query.1 query.2 with
  | some answer =>
      simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
      gcongr
      exact twoEdgeCharge_mono (Nat.le_succ spent) (fun _ _ _ h => h) endpoint
  | none =>
      rw [← expectation_const (rowLaw (none : Option State)) ((twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State)]
      apply ENNReal.tsum_le_tsum
      intro answer
      apply mul_le_mul' le_rfl
      gcongr
      exact twoEdgeCharge_mono (Nat.le_succ spent) (record_extends observed query answer (Or.inl hrow)) endpoint
theorem twoEdgeWeight_observe_of_bad {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) (hbad : TwoEdge observed endpoint) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) =
      twoEdgeWeight observed endpoint := by
  cases hrow : observed query.1 query.2 with
  | some answer => simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
  | none =>
      have hafter (answer : State) : TwoEdge (record observed query answer) endpoint :=
        twoEdge_mono (record_extends observed query answer (Or.inl hrow)) endpoint hbad
      simp only [twoEdgeWeight, if_pos hbad, if_pos (hafter _), mul_one]
      simpa only [hrow] using meanPreimages_observe observed query endpoint
theorem twoEdge_first_compensation {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) (hbad : ¬TwoEdge observed endpoint)
    (hfresh : observed query.1 query.2 = none) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) ≤
      ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  rcases query with ⟨step, input⟩
  by_cases hlast : step = Fin.last (n + 1)
  · subst step
    by_cases hprepared : ∃ start, observed (Fin.last n).castSucc start = some input
    · apply expected_charge_cover _ _ (2 + contactCount observed endpoint + targetCount (Fin.init observed) input)
      · simpa only [twoEdgeWeight, if_pos hprepared] using twoEdge_last_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        exact twoEdgeCharge_record_last spent observed input answer endpoint hfresh hprepared
    · apply expected_charge_cover _ _ 0
      · simpa only [twoEdgeWeight, if_neg hprepared, Nat.cast_zero, div_eq_mul_inv, zero_mul] using twoEdge_last_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        simpa only [Nat.add_zero] using twoEdgeCharge_mono (Nat.le_succ spent)
          (record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh)) endpoint
  · by_cases hpen : step = (Fin.last n).castSucc
    · subst step
      apply expected_charge_cover _ _ (contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input))
      · exact twoEdge_penultimate_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        exact twoEdgeCharge_record_penultimate spent observed input answer endpoint hfresh
    · have hafter (answer : State) : ¬TwoEdge (record observed (step, input) answer) endpoint := by
        rw [twoEdge_record_earlier observed (step, input) answer endpoint (Ne.symm hpen) (Ne.symm hlast)]
        exact hbad
      simp only [twoEdgeWeight, if_neg (hafter _), mul_zero, tsum_zero, add_zero]
      exact twoEdgeCharge_observe_mono spent observed (step, input) endpoint
theorem twoEdge_observe_compensation {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) ≤
      twoEdgeWeight observed endpoint + ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  by_cases hbad : TwoEdge observed endpoint
  · rw [twoEdgeWeight_observe_of_bad observed query endpoint hbad, add_comm]
    exact _root_.add_le_add le_rfl (twoEdgeCharge_observe_mono spent observed query endpoint)
  · have hzero : twoEdgeWeight observed endpoint = 0 := by simp only [twoEdgeWeight, if_neg hbad, mul_zero]
    rw [hzero, zero_add]
    cases hrow : observed query.1 query.2 with
    | none => simpa only [hrow] using twoEdge_first_compensation spent observed query endpoint hbad hrow
    | some answer =>
        simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow, hzero, add_zero]
        gcongr
        exact twoEdgeCharge_mono (Nat.le_succ spent) (fun _ _ _ h => h) endpoint
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end

section





section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_budget_potential_le (auxiliary : QueryImpl auxSpec PMF)
    (potential : Nat → (Fin n → State → Option State) → ENNReal)
    (terminal : (Fin n → State → Option State) → ENNReal) (rate : ENNReal) (limit : Nat)
    (hterminal : ∀ budget observed, terminal observed ≤ potential budget observed)
    (hstep : ∀ input observed budget, budget ≤ limit → (¬IsPrefixQuery input ∨ 0 < budget) →
      (∑' result, (lazyImpl auxiliary input).run observed result *
        potential (if IsPrefixQuery input then budget - 1 else budget) result.2) ≤
          potential budget observed + rate * ((if IsPrefixQuery input then 1 else 0 : Nat) : ENNReal))
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (budget : Nat) (hbudget : budget ≤ limit) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * terminal result.2) ≤
      potential budget observed + rate *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure result =>
      simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.cast_zero, mul_zero, add_zero]
      exact hterminal budget observed
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hremaining : (if IsPrefixQuery input then budget - 1 else budget) ≤ limit := by split <;> omega
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, Nat.cast_add, expectation_add, expectation_const]
      calc
        _ ≤ ∑' output, (lazyImpl auxiliary input).run observed output *
            (potential (if IsPrefixQuery input then budget - 1 else budget) output.2 + rate *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal)) :=
          ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl
            (ih output.1 output.2 _ hremaining (hbound.2 output.1))
        _ = (∑' output, (lazyImpl auxiliary input).run observed output *
              potential (if IsPrefixQuery input then budget - 1 else budget) output.2) +
            rate * ∑' output, (lazyImpl auxiliary input).run observed output *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal) := by
          rw [expectation_add, expectation_scale]
        _ ≤ _ := by
          rw [mul_add, ← add_assoc]
          exact _root_.add_le_add (hstep input observed budget hbudget hbound.1) le_rfl
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
noncomputable def contactMomentPotential (remaining : Nat) (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  (contactFactorial (contactCount observed endpoint) : ENNReal) +
    (2 * remaining : Nat) / (Fintype.card State : ENNReal) * (contactCount observed endpoint : ENNReal)
theorem contactMomentPotential_observe_le (observed : Fin n → State → Option State) (query : Fin n × State)
    (endpoint : State) (remaining limit : Nat) (hremaining : remaining ≤ limit) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * contactMomentPotential remaining (record observed query answer) endpoint) ≤
      contactMomentPotential (remaining + 1) observed endpoint + (2 * limit : Nat) / (Fintype.card State : ENNReal)^2 := by
  simp only [contactMomentPotential, expectation_add, expectation_scale]
  calc
    _ ≤ ((contactFactorial (contactCount observed endpoint) : ENNReal) +
          (2 * contactCount observed endpoint : Nat) / (Fintype.card State : ENNReal)) +
        ((2 * remaining : Nat) / (Fintype.card State : ENNReal)) *
          ((contactCount observed endpoint : ENNReal) + 1 / Fintype.card State) :=
      _root_.add_le_add (contactFactorial_observe_le observed query endpoint)
        (mul_le_mul' le_rfl (contactCount_observe_le observed query endpoint))
    _ = (contactFactorial (contactCount observed endpoint) : ENNReal) +
          (2 * (remaining + 1) : Nat) / (Fintype.card State : ENNReal) * (contactCount observed endpoint : ENNReal) +
          (2 * remaining : Nat) / (Fintype.card State : ENNReal)^2 := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv, ENNReal.inv_pow]
      ring
    _ ≤ _ := by
      apply _root_.add_le_add le_rfl
      have h : (2 * remaining : Nat) ≤ 2 * limit := Nat.mul_le_mul_left 2 hremaining
      simpa only [div_eq_mul_inv] using mul_le_mul'
        (show ((2 * remaining : Nat) : ENNReal) ≤ (2 * limit : Nat) by exact_mod_cast h)
        (le_refl ((Fintype.card State : ENNReal)^2)⁻¹)
theorem lazyRun_contactCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (endpoint : State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (contactCount result.2 endpoint : ENNReal)) ≤
      (contactCount observed endpoint : ENNReal) + (1 / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  apply lazyRun_potential_le auxiliary (fun current => (contactCount current endpoint : ENNReal)) (1 / Fintype.card State)
  intro input current
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one]
      exact contactCount_observe_le current query endpoint
theorem lazyRun_contactFactorial_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      (contactFactorial (contactCount result.2 endpoint) : ENNReal)) ≤
      contactMomentPotential budget observed endpoint + ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  apply lazyRun_budget_potential_le auxiliary (fun remaining current => contactMomentPotential remaining current endpoint)
    (fun current => (contactFactorial (contactCount current endpoint) : ENNReal))
    ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) budget
    (fun _ _ => _root_.le_add_of_nonneg_right bot_le) ?_ computation observed budget le_rfl hbound
  intro input current remaining hremaining hpositive
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      have hpos : 0 < remaining := by simpa only [IsPrefixQuery, not_true_eq_false, false_or] using hpositive
      cases remaining with
      | zero => omega
      | succ remaining =>
          simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one, Nat.add_sub_cancel]
          exact contactMomentPotential_observe_le current query endpoint remaining budget (by omega)
theorem lazyRun_empty_contactCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
      (contactCount result.2 endpoint : ENNReal)) ≤
      (1 / Fintype.card State) * ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        (result.1.2 : ENNReal) := by
  simpa only [contactCount_empty, Nat.cast_zero, zero_add] using lazyRun_contactCount_le auxiliary computation (fun _ _ => none) endpoint
theorem lazyRun_empty_contactFactorial_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
      (contactFactorial (contactCount result.2 endpoint) : ENNReal)) ≤
      ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  simpa only [contactMomentPotential, contactCount_empty, contactFactorial, Nat.zero_mul, Nat.cast_zero, mul_zero, zero_add] using
    lazyRun_contactFactorial_le auxiliary computation (fun _ _ => none) endpoint budget hbound
theorem lazyRun_empty_contact_correction (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    ((budget : ENNReal) / Fintype.card State) *
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        ((contactFactorial (contactCount result.2 endpoint) + 4 * contactCount result.2 endpoint : Nat) : ENNReal)) ≤
      ((4 * ((budget : ENNReal) / Fintype.card State) + 2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, expectation_add, expectation_scale]
  have h := mul_le_mul' (le_refl ((budget : ENNReal) / Fintype.card State))
    (_root_.add_le_add (lazyRun_empty_contactFactorial_le auxiliary computation endpoint budget hbound)
      (mul_le_mul' (le_refl (4 : ENNReal)) (lazyRun_empty_contactCount_le auxiliary computation endpoint)))
  apply h.trans_eq
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
  ring
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
private theorem compensation_compose {a b c d e f : ENNReal} (hc : c ≠ ⊤)
    (hstep : a + d ≤ b + c) (htail : c + e ≤ d + f) : a + e ≤ b + f := by
  apply (ENNReal.add_le_add_iff_left hc).mp
  calc
    c + (a + e) = a + (c + e) := by ac_rfl
    _ ≤ a + (d + f) := _root_.add_le_add le_rfl htail
    _ = (a + d) + f := by rw [add_assoc]
    _ ≤ (b + c) + f := _root_.add_le_add hstep le_rfl
    _ = c + (b + f) := by ac_rfl
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_compensation (auxiliary : QueryImpl auxSpec PMF)
    (charge weight : Nat → (Fin n → State → Option State) → ENNReal)
    (hfinite : ∀ input observed spent,
      (∑' output, (lazyImpl auxiliary input).run observed output *
        charge (spent + if IsPrefixQuery input then 1 else 0) output.2) ≠ ⊤)
    (hstep : ∀ input observed spent,
      charge spent observed + (∑' output, (lazyImpl auxiliary input).run observed output *
        weight (spent + if IsPrefixQuery input then 1 else 0) output.2) ≤
      weight spent observed + ∑' output, (lazyImpl auxiliary input).run observed output *
        charge (spent + if IsPrefixQuery input then 1 else 0) output.2)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (spent : Nat) :
    charge spent observed + (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      weight (spent + result.1.2) result.2) ≤
    weight spent observed + ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      charge (spent + result.1.2) result.2 := by
  induction computation using OracleComp.inductionOn generalizing observed spent with
  | pure result =>
      simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.add_zero]
      exact le_of_eq (add_comm _ _)
  | query_bind input next ih =>
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, ← Nat.add_assoc]
      apply compensation_compose (hfinite input observed spent) (hstep input observed spent)
      have h := ENNReal.tsum_le_tsum fun output => mul_le_mul' (le_refl ((lazyImpl auxiliary input).run observed output))
        (ih output.1 output.2 (spent + if IsPrefixQuery input then 1 else 0))
      simpa only [expectation_add] using h
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_twoEdge_compensation (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (observed : Fin (n + 2) → State → Option State) (spent : Nat) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * twoEdgeWeight result.2 endpoint) ≤
      twoEdgeWeight observed endpoint + ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
        ((twoEdgeCharge (spent + result.1.2) result.2 endpoint : ENNReal) / Fintype.card State) := by
  apply lazyRun_compensation auxiliary (fun used current => (twoEdgeCharge used current endpoint : ENNReal) / Fintype.card State)
    (fun _ current => twoEdgeWeight current endpoint) ?_ ?_ computation observed spent
  · intro input current used
    have hn : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    cases input with
    | inl input =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.add_zero]
        exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn
    | inr query =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true]
        change (∑' answer : State, rowLaw (current query.1 query.2) answer *
          ((twoEdgeCharge (used + 1) (record current query answer) endpoint : ENNReal) / Fintype.card State)) ≠ ⊤
        rw [tsum_fintype]
        apply ENNReal.sum_ne_top.mpr
        intro answer _
        exact ENNReal.mul_ne_top (ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤) (PMF.coe_le_one _ _))
          (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn)
  · intro input current used
    cases input with
    | inl input =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.add_zero]
        exact le_of_eq (add_comm _ _)
    | inr query =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true]
        exact twoEdge_observe_compensation used current query endpoint
omit [Nonempty State] in
theorem twoEdgeCharge_div_le (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ spent) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State ≤
      ((3 / 2 : ENNReal) / Fintype.card State) * (spent : ENNReal) +
        ((budget : ENNReal) / Fintype.card State) *
          ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
  have hdouble : 2 * (twoEdgeCharge spent observed endpoint : ENNReal) ≤ 3 * (spent : ENNReal) +
      2 * (budget : ENNReal) * ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
    exact_mod_cast (twoEdgeCharge_twice_le spent budget observed endpoint hs (hq.trans hs)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hq) _)
  have hcast : (twoEdgeCharge spent observed endpoint : ENNReal) ≤ (3 / 2 : ENNReal) * (spent : ENNReal) +
      (budget : ENNReal) * ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
    apply (ENNReal.mul_le_mul_iff_left (c := 2) (by norm_num) (by norm_num)).mp
    have ht : (3 / 2 : ENNReal) * 2 = 3 := by
      rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
    calc
      _ = 2 * (twoEdgeCharge spent observed endpoint : ENNReal) := mul_comm _ _
      _ ≤ _ := hdouble
      _ = (3 / 2 * 2) * (spent : ENNReal) + 2 * (budget : ENNReal) *
          ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by rw [ht]
      _ = _ := by ring
  have h := mul_le_mul' hcast (le_refl (Fintype.card State : ENNReal)⁻¹)
  simpa only [div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using h
theorem lazyRun_empty_twoEdge_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec (n + 2) State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary computation (fun _ _ => none) result * twoEdgeWeight result.2 endpoint) ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  rw [lazyRun_counted_expectation]
  have hc := lazyRun_twoEdge_compensation auxiliary computation (fun _ _ => none) 0 endpoint
  simp only [twoEdgeCharge_empty, Nat.cast_zero, div_eq_mul_inv, zero_mul, twoEdgeWeight_empty, zero_add] at hc
  apply hc.trans
  calc
    _ ≤ ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        (((3 / 2 : ENNReal) / Fintype.card State) * (result.1.2 : ENNReal) +
          ((budget : ENNReal) / Fintype.card State) *
            ((contactFactorial (contactCount result.2 endpoint) + 4 * contactCount result.2 endpoint : Nat) : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none)).support
      · apply mul_le_mul' le_rfl
        have hq := lazyRun_counted_queryCount_le auxiliary computation (fun _ _ => none) result hr
        simp only [queryCount_empty, Nat.zero_add] at hq
        exact twoEdgeCharge_div_le result.1.2 budget result.2 endpoint (lazyRun_counted_budget_le auxiliary computation _ budget hbound result hr) hq
      · have hz : lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result = 0 := not_not.mp hr
        simp only [hz, zero_mul, le_refl]
    _ = _ := by rw [expectation_add, expectation_scale, expectation_scale]
    _ ≤ _ := by
      have h := _root_.add_le_add
        (le_refl (((3 / 2 : ENNReal) / Fintype.card State) *
          ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal)))
        (lazyRun_empty_contact_correction auxiliary computation endpoint budget hbound)
      apply h.trans_eq
      simp only [div_eq_mul_inv]
      ring
theorem realRun_twoEdge_le (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (budget : Nat) (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
            (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  rw [show Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] =
      (∑' result, realRun auxiliary computation (fun _ _ => none) result * (if TwoEdge result.2.2 result.1 then 1 else 0)) by
        simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realRun_expectation]
  simp only [idealRun, expectation_bind, expectation_map]
  rw [← expectation_scale]
  apply ENNReal.tsum_le_tsum
  intro endpoint
  apply mul_le_mul' le_rfl
  exact lazyRun_empty_twoEdge_le (auxiliary endpoint) (computation endpoint) endpoint budget (hbound endpoint)
end SphincsSecurity.Concrete.PartialChainEndpoint
end
section
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
include hcharge hreal
theorem realRun_cap_twoEdge_eq :
    Pr[fun result => TwoEdge result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin (n + 2) → State → Option State))) =>
    Pr[fun result => TwoEdge result.2.2 result.1 | law])
    (realRun_cap_erased_observed auxiliary computation cost budget hcharge hreal)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h
theorem realRun_twoEdge_le_cap_cost (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_twoEdge_eq auxiliary computation cost budget hcharge hreal]
  have h := realRun_twoEdge_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
  rw [idealRun_cap_count_expectation auxiliary computation cost budget hcharge hreal hsmall] at h
  exact h
omit hcharge hreal in
def TwoEdgeEvent : {depth : Nat} → (Fin depth → State → Option State) → State → Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | _ + 2, observed, endpoint => TwoEdge observed endpoint
omit hcharge hreal in
theorem realRun_twoEdgeEvent_le_cap_cost {depth : Nat} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec depth State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
      result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
    (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  cases depth with
  | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
  | succ depth =>
      cases depth with
      | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
      | succ depth => exact realRun_twoEdge_le_cap_cost auxiliary computation cost budget hcharge hreal hsmall
end SphincsSecurity.Concrete.PartialChainEndpoint
end
end
