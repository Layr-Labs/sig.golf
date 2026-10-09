import SigGolfCandidate.ClaudeWCT.Arith.SideChannelComp
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Probabilistic semantics of test programs (campaign X1, stage B, item B3)

`evalT y p` runs a test program with uniform coins and tests answered against `y`; `exT y f p` is the expectation
of `f` defined by structural recursion (`prT` is the case of an indicator). This file links the recursive
quantities of `SideChannelComp` to the `PMF` semantics, and gives the generic lemma that `simulateQ` into `PMF`
commutes with a state-passing simulation (`simulateQ_run_stateT`), used to identify a stateful test program with
the oracle world it simulates.
-/

namespace ClaudeWCT.Arith.SideChannel

open OracleComp OracleSpec Finset ENNReal

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] {α β : Type}

/-- Uniform coins. -/
noncomputable def coinImpl : QueryImpl unifSpec PMF := fun n => PMF.uniformOfFintype (Fin (n + 1))
/-- Tests answered against `y`. -/
noncomputable def testAns (y : ι → V) : QueryImpl ((ι × V) →ₒ Bool) PMF :=
  fun p : ι × V => PMF.pure (decide (y p.1 = p.2))
/-- Coins uniform, tests answered against `y`. -/
noncomputable def answerImpl (y : ι → V) : QueryImpl (TSpec ι V) PMF := coinImpl + testAns y

/-- The run of a test program against `y`. -/
noncomputable def evalT (y : ι → V) (oa : OracleComp (TSpec ι V) α) : PMF α := simulateQ (answerImpl y) oa

theorem evalT_pure (y : ι → V) (a : α) : evalT y (pure a : OracleComp (TSpec ι V) α) = PMF.pure a := rfl
theorem evalT_bind (y : ι → V) (oa : OracleComp (TSpec ι V) α) (f : α → OracleComp (TSpec ι V) β) :
    evalT y (oa >>= f) = (evalT y oa).bind (fun x => evalT y (f x)) := by
  unfold evalT
  rw [simulateQ_bind]
  rfl
theorem evalT_coinQ (y : ι → V) (n : ℕ) :
    evalT y (coinQ n : OracleComp (TSpec ι V) _) = PMF.uniformOfFintype (Fin (n + 1)) := by
  unfold evalT coinQ
  rw [simulateQ_spec_query]
  rfl
theorem evalT_testQ (y : ι → V) (p : ι × V) :
    evalT y (testQ p : OracleComp (TSpec ι V) Bool) = PMF.pure (decide (y p.1 = p.2)) := by
  unfold evalT testQ
  rw [simulateQ_spec_query]
  rfl
theorem evalT_coin (y : ι → V) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    evalT y (coinQ n >>= k) = (PMF.uniformOfFintype (Fin (n + 1))).bind (fun u => evalT y (k u)) := by
  rw [evalT_bind, evalT_coinQ]
theorem evalT_test (y : ι → V) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    evalT y (testQ p >>= k) = evalT y (k (decide (y p.1 = p.2))) := by
  rw [evalT_bind, evalT_testQ, PMF.pure_bind]

/-- Expectation of `f` over the run against `y`, by structural recursion. -/
noncomputable def exT (y : ι → V) (f : α → ℝ) : OracleComp (TSpec ι V) α → ℝ :=
  OracleComp.construct (C := fun _ => ℝ) f
    (fun t _ r => match t, r with
      | .inl n, r => (∑ u : Fin (n + 1), r u) / (n + 1)
      | .inr p, r => by classical exact r (decide (y p.1 = p.2)))

theorem exT_pure (y : ι → V) (f : α → ℝ) (a : α) : exT y f (pure a : OracleComp (TSpec ι V) α) = f a := rfl
theorem exT_coin (y : ι → V) (f : α → ℝ) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    exT y f (coinQ n >>= k) = (∑ u : Fin (n + 1), exT y f (k u)) / (n + 1) := rfl
theorem exT_test (y : ι → V) (f : α → ℝ) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    exT y f (testQ p >>= k) = exT y f (k (decide (y p.1 = p.2))) := rfl

theorem prT_eq_exT (y : ι → V) (A : α → Prop) (oa : OracleComp (TSpec ι V) α) :
    prT y A oa = exT y (fun a => by classical exact if A a then 1 else 0) oa := by
  induction oa using tinduction with
  | pure a => rfl
  | coin n k ih => rw [prT_coin, exT_coin]; simp only [ih]
  | test p k ih => rw [prT_test, exT_test]; exact ih _

theorem exT_bind (y : ι → V) (f : β → ℝ) (oa : OracleComp (TSpec ι V) α) (g : α → OracleComp (TSpec ι V) β) :
    exT y f (oa >>= g) = exT y (fun x => exT y f (g x)) oa := by
  induction oa using tinduction with
  | pure a => rw [pure_bind]; rfl
  | coin n k ih => rw [bind_assoc, exT_coin, exT_coin]; simp only [ih]
  | test p k ih => rw [bind_assoc, exT_test, exT_test]; exact ih _

theorem enT_bind (y : ι → V) (oa : OracleComp (TSpec ι V) α) (g : α → OracleComp (TSpec ι V) β) :
    enT y (oa >>= g) = enT y oa + exT y (fun x => enT y (g x)) oa := by
  induction oa using tinduction with
  | pure a => rw [pure_bind, enT_pure, exT_pure, zero_add]
  | coin n k ih =>
      rw [bind_assoc, enT_coin, enT_coin, exT_coin]
      simp only [ih, Finset.sum_add_distrib, add_div]
  | test p k ih =>
      rw [bind_assoc, enT_test, enT_test, exT_test, ih]
      ring

theorem exT_congr (y : ι → V) {f f' : α → ℝ} (h : ∀ x, f x = f' x) (oa : OracleComp (TSpec ι V) α) :
    exT y f oa = exT y f' oa := by
  rw [show f = f' from funext h]

theorem exT_nonneg (y : ι → V) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (oa : OracleComp (TSpec ι V) α) :
    0 ≤ exT y f oa := by
  induction oa using tinduction with
  | pure a => exact hf a
  | coin n k ih => rw [exT_coin]; exact div_nonneg (sum_nonneg fun u _ => ih u) (by positivity)
  | test p k ih => rw [exT_test]; exact ih _

/-- The recursive expectation is the `PMF` expectation (nonnegative payoffs). -/
theorem ofReal_exT (y : ι → V) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (oa : OracleComp (TSpec ι V) α) :
    ENNReal.ofReal (exT y f oa) = ∑' x, evalT y oa x * ENNReal.ofReal (f x) := by
  induction oa using tinduction with
  | pure a =>
      rw [exT_pure, evalT_pure, tsum_eq_single a (fun b hb => by rw [PMF.pure_apply, if_neg hb, zero_mul]),
        PMF.pure_apply, if_pos rfl, one_mul]
  | coin n k ih =>
      rw [exT_coin, evalT_coin]
      simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_fin]
      simp_rw [← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      simp_rw [mul_assoc, ENNReal.tsum_mul_left, ← ih]
      rw [tsum_fintype, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_sum_of_nonneg
        (fun u _ => exT_nonneg y hf (k u)), div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [mul_comm]
      congr 2
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  | test p k ih => rw [exT_test, evalT_test]; exact ih _

theorem ofReal_prT (y : ι → V) (A : α → Prop) (oa : OracleComp (TSpec ι V) α) :
    ENNReal.ofReal (prT y A oa) = by classical exact ∑' x, evalT y oa x * (if A x then 1 else 0) := by
  classical
  rw [prT_eq_exT, ofReal_exT y (fun x => by split <;> norm_num)]
  refine tsum_congr fun x => ?_
  split <;> simp

/-! ### State-passing simulations -/

/-- `simulateQ` into `PMF` commutes with a state-passing simulation into `OracleComp`. -/
theorem simulateQ_run_stateT {ιs ιt σ : Type} {spec : OracleSpec ιs} {τ : OracleSpec ιt}
    (h : QueryImpl τ PMF) (impl : QueryImpl spec (StateT σ (OracleComp τ))) (G : OracleComp spec α) (s : σ) :
    simulateQ h ((simulateQ impl G).run s) =
      (simulateQ (fun q => (StateT.mk fun s => simulateQ h ((impl q).run s) : StateT σ PMF _)) G).run s := by
  induction G using OracleComp.inductionOn generalizing s with
  | pure x => rfl
  | query_bind q k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk]
      congr 1
      funext p
      exact ih p.1 p.2

/-! ### Depth and expectation under binds and simulations -/

theorem tdepth_bind_le (oa : OracleComp (TSpec ι V) α) (f : α → OracleComp (TSpec ι V) β) (D : ℕ)
    (h : ∀ x, tdepth (f x) ≤ D) : tdepth (oa >>= f) ≤ tdepth oa + D := by
  induction oa using tinduction with
  | pure a => rw [pure_bind]; exact (h a).trans (by rw [tdepth_pure, zero_add])
  | coin n k ih =>
      rw [bind_assoc, tdepth_coin, tdepth_coin]
      refine Finset.sup_le fun u _ => (ih u).trans ?_
      exact Nat.add_le_add_right (Finset.le_sup (f := fun u => tdepth (k u)) (Finset.mem_univ u)) D
  | test p k ih =>
      rw [bind_assoc, tdepth_test, tdepth_test]
      have h1 := ih true
      have h2 := ih false
      omega

theorem exT_const (y : ι → V) (c : ℝ) (oa : OracleComp (TSpec ι V) α) : exT y (fun _ => c) oa = c := by
  induction oa using tinduction with
  | pure a => rfl
  | coin n k ih =>
      rw [exT_coin]
      simp only [ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
  | test p k ih => rw [exT_test]; exact ih _

theorem exT_add_const (y : ι → V) (c : ℝ) (f : α → ℝ) (oa : OracleComp (TSpec ι V) α) :
    exT y (fun x => c + f x) oa = c + exT y f oa := by
  induction oa using tinduction with
  | pure a => rfl
  | coin n k ih =>
      rw [exT_coin, exT_coin]
      simp only [ih, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
  | test p k ih => rw [exT_test, exT_test]; exact ih _

/-- A state-passing simulation that tests at most once per `C`-query has test depth at most the `C`-query bound. -/
theorem tdepth_simulate_le {ιs σ : Type} {spec : OracleSpec ιs} (impl : QueryImpl spec (StateT σ (OracleComp (TSpec ι V))))
    (C : ιs → Prop) [DecidablePred C] (himpl : ∀ q s, tdepth ((impl q).run s) ≤ if C q then 1 else 0) :
    ∀ (G : OracleComp spec α) (n : ℕ) (s : σ), OracleComp.IsQueryBoundP G C n → tdepth ((simulateQ impl G).run s) ≤ n := by
  intro G
  induction G using OracleComp.inductionOn with
  | pure x => intro n s _; exact Nat.zero_le _
  | query_bind q k ih =>
      intro n s h
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine (tdepth_bind_le _ _ _ fun (p : spec.Range q × σ) => ih p.1 _ p.2 (h.2 p.1)).trans ?_
      have h1 := himpl q s
      split_ifs at h1 ⊢ with hc
      · rcases h.1 with h0 | h0
        · exact absurd hc h0
        · omega
      · omega

end ClaudeWCT.Arith.SideChannel
