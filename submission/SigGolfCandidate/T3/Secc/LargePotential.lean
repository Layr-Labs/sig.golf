import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude

section
namespace SphincsSecurity.Concrete.PrimitiveMessagePotential
noncomputable def value (space probes remaining : ℝ) : ℝ :=
  1 - ((space - probes - remaining) / (space - probes)) ^ 2
theorem initial (space budget : ℝ) (hspace : space ≠ 0) :
    value space 0 budget = 2 * (budget / space) - (budget / space) ^ 2 := by
  unfold value
  simp only [sub_zero]
  field_simp
  ring
theorem probe_balance (space probes remaining : ℝ)
    (hspace : space - probes ≠ 0) (hnext : space - (probes + 1) ≠ 0) :
    value space probes 1 + (1 - value space probes 1) * value space (probes + 1) remaining =
      value space probes (remaining + 1) := by
  unfold value
  field_simp
  ring
theorem hazard (space probes : ℝ) (hspace : space - probes ≠ 0) :
    value space probes 1 = 1 - (1 - (space - probes)⁻¹) ^ 2 := by
  unfold value
  field_simp
theorem toReal_hazard (space probes : Nat) (hprobes : probes < space) :
    (1 - (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2 : ENNReal).toReal = value space probes 1 := by
  have hminimum : 1 ≤ space - probes := Nat.sub_pos_of_lt hprobes
  have hinverse : ((space - probes : Nat) : ENNReal)⁻¹ ≤ 1 := by
    apply ENNReal.inv_le_one.mpr
    exact_mod_cast hminimum
  have hsub : (1 - ((space - probes : Nat) : ENNReal)⁻¹ : ENNReal) ≤ 1 := tsub_le_self
  have hsquare : (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2 ≤ (1 : ENNReal) := by
    simpa only [pow_two, mul_one] using mul_le_mul' hsub hsub
  have hden : (space : ℝ) - probes ≠ 0 := ne_of_gt (sub_pos.mpr (Nat.cast_lt.mpr hprobes))
  rw [ENNReal.toReal_sub_of_le hsquare (by simp), ENNReal.toReal_one, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le hinverse (by simp), ENNReal.toReal_one, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Nat.cast_sub hprobes.le, hazard _ _ hden]
theorem bounds (space probes remaining : ℝ) (hremaining : 0 ≤ remaining)
    (hbudget : probes + remaining < space) :
    0 ≤ value space probes remaining ∧ value space probes remaining < 1 := by
  have hden : 0 < space - probes := by linarith
  have hnum : 0 < space - probes - remaining := by linarith
  have hratio : 0 < (space - probes - remaining) / (space - probes) := div_pos hnum hden
  have hone : (space - probes - remaining) / (space - probes) ≤ 1 := by
    apply (div_le_one₀ hden).mpr
    linarith
  unfold value
  constructor
  · nlinarith [sq_nonneg ((space - probes - remaining) / (space - probes)),
      mul_self_le_mul_self hratio.le hone]
  · nlinarith [sq_pos_of_pos hratio]
theorem message_increment (space probes remaining : ℝ) (hspace : space - probes ≠ 0) :
    value space probes (remaining + 1) - value space probes remaining =
      (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
  unfold value
  field_simp
  ring
theorem message_payment (space probes remaining : ℝ) (hspace : 0 < space)
    (hprobes : 0 ≤ probes) (hremaining : 0 ≤ remaining)
    (hbudget : 2 * (probes + remaining + 1) ≤ space) :
    1 / space + value space probes remaining ≤ value space probes (remaining + 1) := by
  have hden : 0 < space - probes := by linarith
  have hnum : space ≤ 2 * (space - probes - remaining) - 1 := by linarith
  have hsq : (space - probes) ^ 2 ≤ space ^ 2 := by nlinarith
  have hpay : 1 / space ≤ (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
    calc
      1 / space = space / space ^ 2 := by field_simp
      _ ≤ space / (space - probes) ^ 2 := div_le_div_of_nonneg_left hspace.le (sq_pos_of_pos hden) hsq
      _ ≤ _ := (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr hnum
  rw [← message_increment space probes remaining (ne_of_gt hden)] at hpay
  linarith
theorem mono_remaining (space probes before after : ℝ) (hbefore : 0 ≤ before)
    (horder : before ≤ after) (hbudget : probes + after < space) :
    value space probes before ≤ value space probes after := by
  have hden : 0 < space - probes := by linarith
  have hsmall : 0 ≤ (space - probes - after) / (space - probes) := div_nonneg (by linarith) hden.le
  have hratio : (space - probes - after) / (space - probes) ≤ (space - probes - before) / (space - probes) :=
    (div_le_div_iff_of_pos_right hden).mpr (by linarith)
  unfold value
  nlinarith [mul_self_le_mul_self hsmall hratio]
theorem mono_probes (space before after remaining : ℝ) (hremaining : 0 ≤ remaining)
    (horder : before ≤ after) (hbudget : after + remaining < space) :
    value space before remaining ≤ value space after remaining := by
  have hafter : 0 < space - after := by linarith
  have hbefore : 0 < space - before := by linarith
  have hquot : remaining / (space - before) ≤ remaining / (space - after) :=
    div_le_div_of_nonneg_left hremaining hafter (by linarith)
  have hratio (probes : ℝ) (hden : space - probes ≠ 0) :
      (space - probes - remaining) / (space - probes) = 1 - remaining / (space - probes) := by
    field_simp
  have hnonnegative : 0 ≤ 1 - remaining / (space - after) := by
    have hle := (div_le_one₀ hafter).mpr (show remaining ≤ space - after by linarith)
    linarith
  unfold value
  rw [hratio before hbefore.ne', hratio after hafter.ne']
  nlinarith [mul_self_le_mul_self hnonnegative (show 1 - remaining / (space - after) ≤
    1 - remaining / (space - before) by linarith)]
theorem nonmessage_step (space probes after remaining probability : ℝ)
    (hremaining : 0 ≤ remaining) (hafter : after ≤ probes + 1) (hbudget : probes + remaining + 1 < space)
    (hhazard : probability ≤ value space probes 1) :
    probability + (1 - probability) * value space after remaining ≤ value space probes (remaining + 1) := by
  have hnext := bounds space (probes + 1) remaining hremaining (by linarith)
  have hfirst := bounds space probes 1 (by norm_num) (by linarith)
  have hcontinuation := mono_probes space after (probes + 1) remaining hremaining hafter (by linarith)
  have hsurvive : 0 ≤ 1 - probability := by linarith
  calc
    _ ≤ probability + (1 - probability) * value space (probes + 1) remaining :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcontinuation hsurvive)
    _ ≤ value space probes 1 + (1 - value space probes 1) * value space (probes + 1) remaining := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hhazard) (sub_nonneg.mpr hnext.2.le)]
    _ = _ := probe_balance space probes remaining (by linarith) (by linarith)
end SphincsSecurity.Concrete.PrimitiveMessagePotential
end
section
namespace SigGolfCandidate.T3.Security.LargePotential
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
noncomputable def hazard (space probes : Nat) : ENNReal :=
  1 - (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2
noncomputable def continuation (space q calls probes : Nat) : ENNReal :=
  if calls ≤ q then ENNReal.ofReal (PrimitiveMessagePotential.value space probes ((q : ℝ) - calls)) else 0
theorem hazard_le_one (space probes : Nat) : hazard space probes ≤ 1 := tsub_le_self
private theorem real_facts (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) :
    (0 : ℝ) < space ∧ 2 * (q : ℝ) ≤ space ∧ (probes : ℝ) ≤ calls ∧ (q : ℝ) < space := by
  have h1 : (0 : ℝ) < space := by exact_mod_cast hspace
  have h2 : 2 * (q : ℝ) ≤ space := by exact_mod_cast hq
  have h3 : (probes : ℝ) ≤ calls := by exact_mod_cast hprobes
  refine ⟨h1, h2, h3, by linarith⟩
theorem continuation_anti (space q calls probes calls' probes' : Nat) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (hprobes : probes ≤ calls) (hcalls : calls ≤ calls') (hprobes' : probes' ≤ probes) :
    continuation space q calls' probes' ≤ continuation space q calls probes := by
  unfold continuation
  by_cases h' : calls' ≤ q
  · rw [if_pos h', if_pos (le_trans hcalls h')]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
    have hc : (calls : ℝ) ≤ calls' := by exact_mod_cast hcalls
    have hc' : (calls' : ℝ) ≤ q := by exact_mod_cast h'
    have hp' : (probes' : ℝ) ≤ probes := by exact_mod_cast hprobes'
    have hm1 := PrimitiveMessagePotential.mono_probes space probes' probes ((q : ℝ) - calls')
      (by linarith) hp' (by linarith)
    have hm2 := PrimitiveMessagePotential.mono_remaining space probes ((q : ℝ) - calls') ((q : ℝ) - calls)
      (by linarith) (by linarith) (by linarith)
    exact hm1.trans hm2
  · rw [if_neg h']
    exact zero_le
theorem continuation_pay (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) :
    continuation space q (calls + 1) probes + (space : ENNReal)⁻¹ ≤ continuation space q calls probes := by
  obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hpay := PrimitiveMessagePotential.message_payment space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) hs
    (by positivity) (by push_cast; linarith) (by push_cast; linarith)
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hpay
  have hv := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - ((calls + 1 : Nat) : ℝ))
    (by push_cast; linarith) (by push_cast; linarith)).1
  have hfinal := ENNReal.ofReal_le_ofReal hpay
  rw [ENNReal.ofReal_add (by positivity) hv, one_div, ENNReal.ofReal_inv_of_pos hs, ENNReal.ofReal_natCast] at hfinal
  rw [add_comm]
  exact hfinal
theorem ennreal_mixture_le (probability : ENNReal) (hprobability : probability ≤ 1)
    (value bound : ℝ) (hvalue : 0 ≤ value) (hbound : 0 ≤ bound)
    (h : probability.toReal + (1 - probability.toReal) * value ≤ bound) :
    probability + (1 - probability) * ENNReal.ofReal value ≤ ENNReal.ofReal bound := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) hprobability
  have hs : 1 - probability ≠ ⊤ := ne_top_of_le_ne_top (by simp) tsub_le_self
  apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hp, ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top⟩)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add hp (ENNReal.mul_ne_top hs ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le hprobability (by simp), ENNReal.toReal_one,
    ENNReal.toReal_ofReal hvalue, ENNReal.toReal_ofReal hbound]
  exact h
theorem continuation_probe (space q calls probes : Nat) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : probes ≤ calls) (hcall : calls + 1 ≤ q) (probability : ENNReal)
    (hhazard : probability ≤ hazard space probes) :
    probability + (1 - probability) * continuation space q (calls + 1) (probes + 1) ≤
      continuation space q calls probes := by
  obtain ⟨hs, hb, hp, hlt⟩ := real_facts space q calls probes hspace hq hprobes
  have hc : (calls : ℝ) + 1 ≤ q := by exact_mod_cast hcall
  have hpl : probes < space := by omega
  unfold continuation
  rw [if_pos hcall, if_pos (by omega)]
  have hone : probability ≤ 1 := hhazard.trans (hazard_le_one space probes)
  have hreal : probability.toReal ≤ PrimitiveMessagePotential.value space probes 1 := by
    have h := ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp) (hazard_le_one space probes)) hhazard
    rwa [hazard, PrimitiveMessagePotential.toReal_hazard space probes hpl] at h
  have hstep := PrimitiveMessagePotential.nonmessage_step space probes ((probes + 1 : Nat) : ℝ)
    ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) probability.toReal (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) hreal
  have heq : (q : ℝ) - ((calls + 1 : Nat) : ℝ) + 1 = (q : ℝ) - calls := by push_cast; ring
  rw [heq] at hstep
  have hnext := (PrimitiveMessagePotential.bounds space ((probes + 1 : Nat) : ℝ)
    ((q : ℝ) - ((calls + 1 : Nat) : ℝ)) (by push_cast; linarith) (by push_cast; linarith)).1
  have hbefore := (PrimitiveMessagePotential.bounds space probes ((q : ℝ) - calls)
    (by linarith) (by linarith)).1
  exact ennreal_mixture_le probability hone _ _ hnext hbefore hstep
theorem initial_potential (q : Nat) :
    ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ 128) 0 ((q : ℝ) - 0)) =
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  rw [sub_zero, PrimitiveMessagePotential.initial _ _ (by positivity)]
variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
abbrev Step (m : Type → Type) (spec : OracleSpec ι) (σ : Type) :=
  (input : spec.Domain) → σ → m (Option (spec.Range input) × σ)
noncomputable def run {α σ : Type} (step : Step m spec σ) (program : OracleComp spec α) :
    σ → m (Option α × σ) :=
  OracleComp.construct
    (fun value state => pure (some value, state))
    (fun input _ next state => do
      let middle ← step input state
      match middle.1 with
      | none => pure (none, middle.2)
      | some answer => next answer middle.2) program
theorem run_pure {α σ : Type} (step : Step m spec σ) (value : α) (state : σ) :
    run step (pure value : OracleComp spec α) state = pure (some value, state) := rfl
theorem run_query_bind {α σ : Type} (step : Step m spec σ) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) (state : σ) :
    run step (liftM (spec.query input) >>= next) state = (do
      let middle ← step input state
      match middle.1 with
      | none => pure (none, middle.2)
      | some answer => run step (next answer) middle.2) := rfl
variable [LawfulMonad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  [EvalDistCompatible m]
def terminal {β σ : Type} (stopValue doneValue : σ → ENNReal) (result : Option β × σ) : ENNReal :=
  result.1.elim (stopValue result.2) (fun _ => doneValue result.2)
theorem run_expected_le {α σ : Type} (step : Step m spec σ) (inv : σ → Prop)
    (potential stopValue doneValue : σ → ENNReal)
    (hdone : ∀ state, inv state → doneValue state ≤ potential state)
    (hpreserve : ∀ input state, inv state → ∀ answer after,
      (some answer, after) ∈ support (step input state) → inv after)
    (hstep : ∀ input state, inv state →
      expectedValue (step input state) (terminal stopValue potential) ≤ potential state)
    (program : OracleComp spec α) (state : σ) (hstate : inv state) :
    expectedValue (run step program state) (terminal stopValue doneValue) ≤ potential state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [run_pure, expectedValue_pure]
      exact hdone state hstate
  | query_bind input next ih =>
      rw [run_query_bind, expectedValue_bind]
      refine le_trans ?_ (hstep input state hstate)
      apply expectedValue_mono_of_support
      rintro ⟨answer, after⟩ hmiddle
      cases answer with
      | none => simp [terminal]
      | some answer => exact ih answer after (hpreserve input state hstate answer after hmiddle)
structure Charges (σ : Type) where
  calls : σ → Nat
  probes : σ → Nat
  mass : σ → Nat
noncomputable def potential {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  continuation space q (ch.calls state) (ch.probes state) + (ch.mass state : ENNReal) / space
noncomputable def stopValue {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) : ENNReal :=
  (if ch.calls state ≤ q then 1 else 0) + (ch.mass state : ENNReal) / space
noncomputable def doneValue {σ : Type} (ch : Charges σ) (space : Nat) (state : σ) : ENNReal :=
  (ch.mass state : ENNReal) / space
def FreeStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (input : spec.Domain) (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] = 0
def MassStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat) (input : spec.Domain) (state : σ) :
    Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧
    ch.mass result.2 ≤ ch.mass state + (if ch.calls state + 1 ≤ q then 1 else 0)) ∧
  Pr[fun result => result.1 = none | step input state] = 0
def TestStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] ≤ (space : ENNReal)⁻¹
def ProbeStep {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  (∀ result ∈ support (step input state), ch.calls state + 1 ≤ ch.calls result.2 ∧
    ch.probes result.2 ≤ ch.probes state + 1 ∧ ch.mass result.2 ≤ ch.mass state) ∧
  Pr[fun result => result.1 = none | step input state] ≤ hazard space (ch.probes state)
def StepBound {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat) (input : spec.Domain)
    (state : σ) : Prop :=
  FreeStep step ch input state ∨ MassStep step ch q input state ∨ TestStep step ch space input state ∨
    ProbeStep step ch space input state
theorem StepBound.probes_le {σ : Type} {step : Step m spec σ} {ch : Charges σ} {space q : Nat}
    {input : spec.Domain} {state : σ} (h : StepBound step ch space q input state)
    (hprobes : ch.probes state ≤ ch.calls state) :
    ∀ result ∈ support (step input state), ch.probes result.2 ≤ ch.calls result.2 := by
  intro result hresult
  rcases h with h | h | h | h
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega
  · have := h.1 result hresult; omega
theorem terminal_le_of_over {σ : Type} (ch : Charges σ) (space q : Nat) (state : σ) {β : Type}
    (result : Option β × σ) (hover : q < ch.calls state + 1)
    (hcalls : ch.calls state + 1 ≤ ch.calls result.2) (hmass : ch.mass result.2 ≤ ch.mass state) :
    terminal (stopValue ch space q) (potential ch space q) result ≤ (ch.mass state : ENNReal) / space := by
  have hnot : ¬ch.calls result.2 ≤ q := by omega
  have hm : (ch.mass result.2 : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
    ENNReal.div_le_div_right (by exact_mod_cast hmass) _
  rcases result with ⟨_ | answer, after⟩
  · simpa [terminal, stopValue, hnot] using hm
  · simpa [terminal, potential, continuation, hnot] using hm
theorem expected_stop_le {β σ : Type} (law : m (Option β × σ)) (value rest : ENNReal) :
    expectedValue law (fun result => (if result.1 = none then 1 else value) + rest) ≤
      Pr[fun result => result.1 = none | law] +
        (1 - Pr[fun result => result.1 = none | law]) * value + rest := by
  have hcompl : Pr[fun result => ¬result.1 = none | law] ≤ 1 - Pr[fun result => result.1 = none | law] := by
    apply ENNReal.le_sub_of_add_le_left probEvent_ne_top
    rw [probEvent_compl]
    exact tsub_le_self
  rw [expectedValue_add]
  have hsplit : expectedValue law (fun result => if result.1 = none then 1 else value) =
      Pr[fun result => result.1 = none | law] + Pr[fun result => ¬result.1 = none | law] * value := by
    rw [expectedValue_def, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right,
      ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    by_cases h : result.1 = none <;> simp [h]
  rw [hsplit]
  refine add_le_add (add_le_add le_rfl (mul_le_mul' hcompl le_rfl)) ?_
  exact expectedValue_le_of_le law (fun _ => le_rfl)
section payments
variable {σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat) (input : spec.Domain) (state : σ)
theorem FreeStep.payment (h : FreeStep step ch input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  apply expectedValue_le_of_support
  rintro ⟨answer, after⟩ hresult
  obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
  have hsome : answer ≠ none := by
    have := (probEvent_eq_zero_iff.mp h.2) _ hresult
    simpa using this
  obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
  simp only [terminal, Option.elim_some, potential]
  exact add_le_add (continuation_anti space q _ _ _ _ hspace hq hprobes hcalls hp)
    (ENNReal.div_le_div_right (by exact_mod_cast hmass) _)
theorem MassStep.payment (h : MassStep step ch q input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  apply expectedValue_le_of_support
  rintro ⟨answer, after⟩ hresult
  obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
  by_cases hc : ch.calls state + 1 ≤ q
  · rw [if_pos hc] at hmass
    have hsome : answer ≠ none := by
      have := (probEvent_eq_zero_iff.mp h.2) _ hresult
      simpa using this
    obtain ⟨answer, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp only [terminal, Option.elim_some, potential]
    have hcont := continuation_anti space q (ch.calls state + 1) (ch.probes state) (ch.calls after)
      (ch.probes after) hspace hq (by omega) hcalls hp
    have hpay := continuation_pay space q (ch.calls state) (ch.probes state) hspace hq hprobes hc
    have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space + (space : ENNReal)⁻¹ := by
      rw [← one_div, ← ENNReal.add_div]
      exact ENNReal.div_le_div_right (by exact_mod_cast hmass) _
    calc
      _ ≤ continuation space q (ch.calls state + 1) (ch.probes state) +
          ((ch.mass state : ENNReal) / space + (space : ENNReal)⁻¹) := add_le_add hcont hm
      _ = (continuation space q (ch.calls state + 1) (ch.probes state) + (space : ENNReal)⁻¹) +
          (ch.mass state : ENNReal) / space := by ring
      _ ≤ _ := add_le_add hpay le_rfl
  · rw [if_neg hc, add_zero] at hmass
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
theorem TestStep.payment (h : TestStep step ch space input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  by_cases hc : ch.calls state + 1 ≤ q
  · have hpoint : ∀ result ∈ support (step input state),
        terminal (stopValue ch space q) (potential ch space q) result ≤
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
            (ch.mass state : ENNReal) / space := by
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
        ENNReal.div_le_div_right (by exact_mod_cast hmass) _
      rcases answer with _ | answer
      · simp only [terminal, Option.elim_none, stopValue, if_true]
        exact add_le_add (by split <;> simp) hm
      · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
        exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
    calc
      _ ≤ expectedValue (step input state) (fun result =>
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state)) +
            (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
      _ ≤ Pr[fun result => result.1 = none | step input state] +
          (1 - Pr[fun result => result.1 = none | step input state]) *
            continuation space q (ch.calls state + 1) (ch.probes state) + (ch.mass state : ENNReal) / space :=
        expected_stop_le _ _ _
      _ ≤ ((space : ENNReal)⁻¹ + continuation space q (ch.calls state + 1) (ch.probes state)) +
          (ch.mass state : ENNReal) / space := by
        refine add_le_add (add_le_add h.2 ?_) le_rfl
        exact mul_le_of_le_one_left' tsub_le_self
      _ ≤ _ := by
        rw [add_comm ((space : ENNReal)⁻¹)]
        exact add_le_add (continuation_pay space q _ _ hspace hq hprobes hc) le_rfl
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
theorem ProbeStep.payment (h : ProbeStep step ch space input state) (hspace : 0 < space) (hq : 2 * q ≤ space)
    (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  by_cases hc : ch.calls state + 1 ≤ q
  · have hpoint : ∀ result ∈ support (step input state),
        terminal (stopValue ch space q) (potential ch space q) result ≤
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
            (ch.mass state : ENNReal) / space := by
      rintro ⟨answer, after⟩ hresult
      obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
      have hm : (ch.mass after : ENNReal) / space ≤ (ch.mass state : ENNReal) / space :=
        ENNReal.div_le_div_right (by exact_mod_cast hmass) _
      rcases answer with _ | answer
      · simp only [terminal, Option.elim_none, stopValue, if_true]
        exact add_le_add (by split <;> simp) hm
      · simp only [terminal, Option.elim_some, potential, reduceCtorEq, if_false]
        exact add_le_add (continuation_anti space q _ _ _ _ hspace hq (by omega) hcalls hp) hm
    calc
      _ ≤ expectedValue (step input state) (fun result =>
          (if result.1 = none then 1 else continuation space q (ch.calls state + 1) (ch.probes state + 1)) +
            (ch.mass state : ENNReal) / space) := expectedValue_mono_of_support hpoint
      _ ≤ Pr[fun result => result.1 = none | step input state] +
          (1 - Pr[fun result => result.1 = none | step input state]) *
            continuation space q (ch.calls state + 1) (ch.probes state + 1) + (ch.mass state : ENNReal) / space :=
        expected_stop_le _ _ _
      _ ≤ _ := add_le_add (continuation_probe space q _ _ hspace hq hprobes hc _ h.2) le_rfl
  · apply expectedValue_le_of_support
    rintro ⟨answer, after⟩ hresult
    obtain ⟨hcalls, hp, hmass⟩ := h.1 _ hresult
    exact (terminal_le_of_over ch space q state (answer, after) (by omega) hcalls hmass).trans le_add_self
theorem StepBound.payment (h : StepBound step ch space q input state) (hspace : 0 < space)
    (hq : 2 * q ≤ space) (hprobes : ch.probes state ≤ ch.calls state) :
    expectedValue (step input state) (terminal (stopValue ch space q) (potential ch space q)) ≤
      potential ch space q state := by
  rcases h with h | h | h | h
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes
  · exact h.payment step ch space q input state hspace hq hprobes
end payments
theorem stop_add_mass_eq {β σ : Type} (ch : Charges σ) (space q : Nat) (law : m (Option β × σ)) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | law] +
      (∑' result, Pr[= result | law] * (ch.mass result.2 : ENNReal)) / space =
      expectedValue law (terminal (stopValue ch space q) (doneValue ch space)) := by
  have hfun : terminal (stopValue ch space q) (doneValue ch space) = fun result : Option β × σ =>
      (if result.1 = none ∧ ch.calls result.2 ≤ q then 1 else 0) + (ch.mass result.2 : ENNReal) / space := by
    funext result
    rcases result with ⟨_ | answer, after⟩
    · simp [terminal, stopValue]
    · simp [terminal, doneValue]
  rw [hfun, expectedValue_add, expectedValue_ite_one, expectedValue_def]
  congr 1
  simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
theorem run_potential_of_bound {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (space q : Nat)
    (hspace : 0 < space) (hq : 2 * q ≤ space) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch space q input state)
    (program : OracleComp spec α) (state : σ) (hstate : inv state)
    (hprobes : ch.probes state ≤ ch.calls state) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | run step program state] +
      (∑' result, Pr[= result | run step program state] * (ch.mass result.2 : ENNReal)) / space ≤
      potential ch space q state := by
  rw [stop_add_mass_eq]
  refine run_expected_le step (fun state => inv state ∧ ch.probes state ≤ ch.calls state)
    (potential ch space q) (stopValue ch space q) (doneValue ch space) ?_ ?_ ?_ program state ⟨hstate, hprobes⟩
  · intro state _
    exact le_add_self
  · rintro input state ⟨hi, hp⟩ answer after hmem
    exact ⟨hpreserve input state hi hp answer after hmem,
      (hbound input state hi hp).probes_le hp _ hmem⟩
  · rintro input state ⟨hi, hp⟩
    exact (hbound input state hi hp).payment step ch space q input state hspace hq hp
theorem potential_initial_le {σ : Type} (ch : Charges σ) (q : Nat) (hq : q ≤ 2 ^ 127) (state : σ)
    (hprobes : ch.probes state = 0) (hmass : ch.mass state = 0) :
    potential ch (2 ^ 128) q state ≤ ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have hmono := continuation_anti (2 ^ 128) q 0 0 (ch.calls state) (ch.probes state) (by positivity)
    (by omega) le_rfl (Nat.zero_le _) (by omega)
  unfold potential
  rw [hmass, Nat.cast_zero, ENNReal.zero_div, add_zero]
  refine hmono.trans (le_of_eq ?_)
  unfold continuation
  rw [if_pos (Nat.zero_le q), Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat]
  exact initial_potential q
theorem run_potential_initial {α σ : Type} (step : Step m spec σ) (ch : Charges σ) (q : Nat)
    (hq : q ≤ 2 ^ 127) (inv : σ → Prop)
    (hpreserve : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      ∀ answer after, (some answer, after) ∈ support (step input state) → inv after)
    (hbound : ∀ input state, inv state → ch.probes state ≤ ch.calls state →
      StepBound step ch (2 ^ 128) q input state)
    (program : OracleComp spec α) (init : σ) (hinit : inv init) (hprobes : ch.probes init = 0)
    (hmass : ch.mass init = 0) :
    Pr[fun result => result.1 = none ∧ ch.calls result.2 ≤ q | run step program init] +
      (∑' result, Pr[= result | run step program init] * (ch.mass result.2 : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) := by
  have h := run_potential_of_bound step ch (2 ^ 128) q (by positivity) (by omega) inv hpreserve hbound program init
    hinit (by omega)
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.trans (potential_initial_le ch q hq init hprobes hmass)
section observe
variable {α σ : Type} (impl : QueryImpl spec (StateT σ m))
  (test : σ → (input : spec.Domain) → spec.Range input → σ → Prop)
def cut : Option σ × α × σ → Option α × σ
  | (some hit, _, _) => (none, hit)
  | (none, value, final) => (some value, final)
end observe
end SigGolfCandidate.T3.Security.LargePotential
end
