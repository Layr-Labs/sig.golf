import SigGolfCandidate.T3.Secc.WotsEncodingCongr

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace Enc
theorem uniform_resample {Ω K : Type} [Fintype Ω] [Nonempty Ω] {X : K → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → K) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) :
    (PMF.uniformOfFintype Ω).bind (fun ω => (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω)) =
      PMF.uniformOfFintype Ω := by
  classical
  let _ : DecidableEq Ω := Classical.decEq Ω
  let _ : DecidableEq K := Classical.decEq K
  apply PMF.ext
  intro ω₀
  obtain ⟨k₀, hk₀⟩ : ∃ k, k = d ω₀ := ⟨_, rfl⟩
  let σ : Ω × X k₀ → Ω × X k₀ := fun p =>
    if h : d p.1 = k₀ then (ov k₀ p.1 p.2, rd k₀ p.1) else p
  have hov : ∀ ω (h : d ω = k₀) (x : X k₀), d (ov k₀ ω x) = k₀ := by
    intro ω h x
    subst h
    exact h3 ω x
  have hσ : Function.Involutive σ := by
    rintro ⟨ω, x⟩
    by_cases h : d ω = k₀
    · have h' := hov ω h x
      simp only [σ, dif_pos h, dif_pos h']
      subst h
      rw [h2 ω x, h1 ω x]
    · simp only [σ, dif_neg h]
  have hinner : ∀ ω, (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω) ω₀ =
      if d ω = k₀ then ∑' x : X k₀, PMF.uniformOfFintype (X k₀) x * (if (σ (ω, x)).1 = ω₀ then 1 else 0)
      else 0 := by
    intro ω
    by_cases h : d ω = k₀
    · rw [if_pos h]
      have hgen : ∀ k (hk : d ω = k), (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω) ω₀ =
          (PMF.uniformOfFintype (X k)).map (ov k ω) ω₀ := by
        rintro k rfl; rfl
      rw [hgen k₀ h, PMF.map_apply]
      apply tsum_congr
      intro x
      simp only [σ, dif_pos h]
      by_cases he : ω₀ = ov k₀ ω x
      · rw [if_pos he, if_pos he.symm, mul_one]
      · rw [if_neg he, if_neg (fun h' => he h'.symm), mul_zero]
    · rw [if_neg h, PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      rw [if_neg]
      intro he
      apply h
      rw [hk₀, he, h3 ω x]
  rw [PMF.bind_apply]
  simp only [hinner]
  have hconst : ∀ (ω : Ω) (x : X k₀), PMF.uniformOfFintype Ω ω * PMF.uniformOfFintype (X k₀) x =
      PMF.uniformOfFintype (Ω × X k₀) (ω, x) := by
    intro ω x
    simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
    rw [ENNReal.mul_inv (by simp) (by simp)]
  have hfiber : ∀ ω, PMF.uniformOfFintype Ω ω *
      (if d ω = k₀ then ∑' x : X k₀, PMF.uniformOfFintype (X k₀) x * (if (σ (ω, x)).1 = ω₀ then 1 else 0)
        else 0) =
      ∑' x : X k₀, PMF.uniformOfFintype (Ω × X k₀) (ω, x) * (if (σ (ω, x)).1 = ω₀ then 1 else 0) := by
    intro ω
    by_cases h : d ω = k₀
    · rw [if_pos h, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      rw [← mul_assoc, hconst]
    · rw [if_neg h, mul_zero]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      have : (σ (ω, x)).1 = ω := by simp only [σ, dif_neg h]
      rw [this, if_neg (fun he => h (by rw [he, hk₀])), mul_zero]
  simp only [hfiber]
  rw [← ENNReal.tsum_prod (f := fun ω x => PMF.uniformOfFintype (Ω × X k₀) (ω, x) *
    (if (σ (ω, x)).1 = ω₀ then 1 else 0))]
  have hc : ∀ p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) p = PMF.uniformOfFintype (Ω × X k₀) (σ p) := by
    intro p
    simp only [PMF.uniformOfFintype_apply]
  calc (∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) (p.1, p.2) * (if (σ (p.1, p.2)).1 = ω₀ then 1 else 0))
      = ∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) (σ p) * (if (σ p).1 = ω₀ then 1 else 0) := by
        apply tsum_congr
        intro p
        rw [← hc p]
    _ = ∑' p : Ω × X k₀, PMF.uniformOfFintype (Ω × X k₀) p * (if p.1 = ω₀ then 1 else 0) :=
        (hσ.toPerm σ).tsum_eq (fun p => PMF.uniformOfFintype (Ω × X k₀) p * (if p.1 = ω₀ then 1 else 0))
    _ = ∑' x : X k₀, PMF.uniformOfFintype (Ω × X k₀) (ω₀, x) := by
        rw [ENNReal.tsum_prod']
        rw [tsum_eq_single ω₀]
        · simp only [if_true, mul_one]
        · intro ω hω
          apply ENNReal.tsum_eq_zero.mpr
          intro x
          rw [if_neg hω, mul_zero]
    _ = PMF.uniformOfFintype Ω ω₀ := by
        simp only [← hconst, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
theorem tsum_bind_mul {α β : Type} (μ : PMF α) (g : α → PMF β) (F : β → ENNReal) :
    ∑' b, (μ.bind g) b * F b = ∑' a, μ a * ∑' b, g a b * F b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  rw [mul_assoc]
theorem tsum_map_mul {α β : Type} (μ : PMF α) (f : α → β) (F : β → ENNReal) :
    ∑' b, (μ.map f) b * F b = ∑' a, μ a * F (f a) := by
  classical
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (f a)]
  · rw [if_pos rfl]
  · intro b hb
    rw [if_neg hb, zero_mul]
theorem uniform_resample_tsum {Ω K : Type} [Fintype Ω] [Nonempty Ω] {X : K → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → K) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) (F : Ω → ENNReal) :
    ∑' ω, PMF.uniformOfFintype Ω ω * F ω =
      ∑' ω, PMF.uniformOfFintype Ω ω * ∑' x, PMF.uniformOfFintype (X (d ω)) x * F (ov (d ω) ω x) := by
  conv_lhs => rw [← uniform_resample d ov rd h1 h2 h3]
  rw [tsum_bind_mul]
  refine tsum_congr fun ω => ?_
  rw [tsum_map_mul]
theorem encInput_short (e : EncIndex) : encInput e ∈ SeccLaw.publicUniverse :=
  SeccLaw.mem_publicUniverse _ (by rw [encInput_length]; unfold SeccLaw.maxInputLength; omega)
section Overwrite
variable {U : Finset HashInput}
noncomputable def ov (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) : U → HashOutput :=
  fun u => if h : ∃ e, e ∈ k ∧ encInput e = u.val then y ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else pub u
noncomputable def rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) :
    k → HashOutput :=
  fun e => pub ⟨encInput e.val, hU (encInput_short e.val)⟩
end Overwrite
section Tables
variable (U : Finset HashInput)
theorem eagerAnswers_public_mem (privateTable : FullGame.FullTable) (pub : U → HashOutput) (u : U) :
    eagerAnswers U privateTable pub (.inl (.inr u.val)) = pub u := by
  change SphincsSecurity.Concrete.finiteHashAnswer ∅ U pub u.val = pub u
  rw [SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U pub u.val u.property (by simp)]
theorem eagerAnswers_public_not_mem (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (input : HashInput) (h : input ∉ U) : eagerAnswers U privateTable pub (.inl (.inr input)) = (0 : HashOutput) := by
  change SphincsSecurity.Concrete.finiteHashAnswer ∅ U pub input = 0
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  simp [h]
  rfl
theorem tsum_uniform_coe {α : Type} (A : Finset α) (hA : A.Nonempty) (iN : Nonempty ↥A) (G : α → ENNReal) :
    ∑' x : ↥A, @PMF.uniformOfFintype ↥A _ iN x * G x.val = ∑' y, PMF.uniformOfFinset A hA y * G y := by
  classical
  have hr : ∀ y, PMF.uniformOfFinset A hA y * G y =
      (↑A : Set α).indicator (fun y => ((A.card : ENNReal))⁻¹ * G y) y := by
    intro y
    by_cases h : y ∈ A
    · rw [PMF.uniformOfFinset_apply, if_pos h, Set.indicator_apply, if_pos (Finset.mem_coe.mpr h)]
    · rw [PMF.uniformOfFinset_apply, if_neg h, zero_mul, Set.indicator_apply,
        if_neg (fun hm => h (Finset.mem_coe.mp hm))]
  simp only [hr]
  rw [← tsum_subtype (↑A : Set α) (fun y => ((A.card : ENNReal))⁻¹ * G y)]
  refine tsum_congr fun x => ?_
  rw [PMF.uniformOfFintype_apply, Fintype.card_coe]
end Tables
end Enc
end SigGolfCandidate.T3.Security.Wots
