import SigGolfCandidate.ClaudeR3.P1
import Mathlib.Algebra.Polynomial.Basic
import SigGolfCandidate.ClaudeR3.C2
import SigGolfCandidate.ClaudeR3.C3

namespace ClaudeR3.Tab
open ClaudeWCT.Numerics.N600

set_option maxRecDepth 100000 in
theorem tabM_length : tabM.length = 1 * 1101 := by decide +kernel
set_option maxRecDepth 100000 in
theorem tabN_length : tabN.length = 1 * 1101 := by decide +kernel
set_option maxRecDepth 100000 in
theorem tabS_length : tabS.length = 1 * 8219 := by decide +kernel

theorem key_mean {M : Type*} [AddCommGroup M] (Ψ : ℕ → M) :
    ∑ u : Fin 6 → Fin 6, (if parU u then (-1 : ℤ) else 1) • (lookup g1T (digitsOf u) • Ψ (lookup keyT (digitsOf u))) =
      (tabM.map (fun e => e.2 • Ψ e.1)).sum :=
  tab_key tabM g1T full_g1T' 17 1101 1 (fun _ => 0) (by norm_num) tabM_length mean_miss mean_bound
    (fun c hc => by interval_cases c; exact mean_chunk) Ψ

theorem key_near {M : Type*} [AddCommGroup M] (Ψ : ℕ → M) :
    ∑ u : Fin 6 → Fin 6, (if parU u then (-1 : ℤ) else 1) • (lookup gNearT (digitsOf u) • Ψ (lookup keyT (digitsOf u))) =
      (tabN.map (fun e => e.2 • Ψ e.1)).sum :=
  tab_key tabN gNearT full_gNearT 18 1101 1 (fun _ => 0) (by norm_num) tabN_length near_miss near_bound
    (fun c hc => by interval_cases c; exact near_chunk) Ψ

theorem key_same {M : Type*} [AddCommGroup M] (Ψ : ℕ → M) :
    ∑ u : Fin 6 → Fin 6, (if parU u then (-1 : ℤ) else 1) • (lookup g2T (digitsOf u) • Ψ (lookup keyT (digitsOf u))) =
      (tabS.map (fun e => e.2 • Ψ e.1)).sum :=
  tab_key tabS g2T full_g2T' 25 8219 1 (fun _ => 0) (by norm_num) tabS_length same_miss same_bound
    (fun c hc => by interval_cases c; exact same_chunk) Ψ

open Polynomial in
theorem key_mean_poly (Ψ : ℕ → ℤ[X]) :
    ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : ℤ[X]) *
        (((lookup g1T (digitsOf u) : ℕ) : ℤ[X]) * Ψ (lookup keyT (digitsOf u))) =
      (tabM.map (fun e => ((e.2 : ℤ) : ℤ[X]) * Ψ e.1)).sum := by
  simpa only [zsmul_eq_mul, nsmul_eq_mul] using key_mean (M := ℤ[X]) Ψ

open Polynomial in
theorem key_near_poly (Ψ : ℕ → ℤ[X]) :
    ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : ℤ[X]) *
        (((lookup gNearT (digitsOf u) : ℕ) : ℤ[X]) * Ψ (lookup keyT (digitsOf u))) =
      (tabN.map (fun e => ((e.2 : ℤ) : ℤ[X]) * Ψ e.1)).sum := by
  simpa only [zsmul_eq_mul, nsmul_eq_mul] using key_near (M := ℤ[X]) Ψ

open Polynomial in
theorem key_same_poly (Ψ : ℕ → ℤ[X]) :
    ∑ u : Fin 6 → Fin 6, (((if parU u then (-1 : ℤ) else 1 : ℤ)) : ℤ[X]) *
        (((lookup g2T (digitsOf u) : ℕ) : ℤ[X]) * Ψ (lookup keyT (digitsOf u))) =
      (tabS.map (fun e => ((e.2 : ℤ) : ℤ[X]) * Ψ e.1)).sum := by
  simpa only [zsmul_eq_mul, nsmul_eq_mul] using key_same (M := ℤ[X]) Ψ

end ClaudeR3.Tab
