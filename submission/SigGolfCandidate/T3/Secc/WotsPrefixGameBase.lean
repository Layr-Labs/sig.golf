import SigGolfCandidate.T3.Secc.WotsMaskRef
import SigGolfCandidate.T3.Secc.WotsMaskRest
import SigGolfCandidate.T3.Secc.WotsExtractChain
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsPrefixGameBase : Fintype Coordinate := coordinateFintype
open Mask
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
namespace PrefixGame
theorem uniform_resample {Ω : Type} [Fintype Ω] [Nonempty Ω] {X : ℕ → Type} [∀ k, Fintype (X k)]
    [∀ k, Nonempty (X k)] (d : Ω → ℕ) (ov : ∀ k, Ω → X k → Ω) (rd : ∀ k, Ω → X k)
    (h1 : ∀ ω x, rd (d ω) (ov (d ω) ω x) = x) (h2 : ∀ ω x, ov (d ω) (ov (d ω) ω x) (rd (d ω) ω) = ω)
    (h3 : ∀ ω x, d (ov (d ω) ω x) = d ω) :
    (PMF.uniformOfFintype Ω).bind (fun ω => (PMF.uniformOfFintype (X (d ω))).map (ov (d ω) ω)) =
      PMF.uniformOfFintype Ω := by
  classical
  let _ : DecidableEq Ω := Classical.decEq Ω
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
end PrefixGame
abbrev RefTables (adversary : AdversaryP) := FullGame.FullTable × (referenceInputs adversary → HashOutput)
noncomputable instance instFintypeRefTables (adversary : AdversaryP) : Fintype (RefTables adversary) := by
  unfold RefTables FullGame.FullTable
  infer_instance
instance instNonemptyRefTables (adversary : AdversaryP) : Nonempty (RefTables adversary) := ⟨(fun _ => 0, fun _ => 0)⟩
noncomputable def restTable {adversary : AdversaryP} (R : RefTables adversary) : Answers :=
  eagerAnswers (referenceInputs adversary) R.1 R.2
@[irreducible] noncomputable def restDepth {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) : Nat :=
  depth (restTable R) a
namespace PrefixGame
variable {adversary : AdversaryP}
def high (output : HashOutput) : Digest := output.extractLsb' 128 128
def seedHalf (a : ChainAddr) (output : HashOutput) : Digest :=
  if a.chain % 2 = 0 then output.extractLsb' 0 128 else output.extractLsb' 128 128
noncomputable def setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) : HashOutput :=
  if a.chain % 2 = 0 then ChainGraph.joinOutput seed (output.extractLsb' 128 128)
  else ChainGraph.joinOutput (output.extractLsb' 0 128) seed
theorem seedHalf_setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) :
    seedHalf a (setSeed a output seed) = seed := by
  unfold seedHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, ChainGraph.joinOutput_low]
  · rw [if_neg h, if_neg h, ChainGraph.joinOutput_high]
theorem setSeed_seedHalf (a : ChainAddr) (output : HashOutput) : setSeed a output (seedHalf a output) = output := by
  unfold seedHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, ChainGraph.joinOutput_parts]
  · rw [if_neg h, if_neg h, ChainGraph.joinOutput_parts]
theorem setSeed_setSeed (a : ChainAddr) (output : HashOutput) (seed seed' : Digest) :
    setSeed a (setSeed a output seed) seed' = setSeed a output seed' := by
  unfold setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, if_pos h, ChainGraph.joinOutput_high]
  · rw [if_neg h, if_neg h, if_neg h, ChainGraph.joinOutput_low]
theorem siblingHalf_setSeed (a : ChainAddr) (output : HashOutput) (seed : Digest) :
    siblingHalf a (setSeed a output seed) = siblingHalf a output := by
  unfold siblingHalf setSeed
  by_cases h : a.chain % 2 = 0
  · rw [if_pos h, if_pos h, if_pos h, ChainGraph.joinOutput_high]
  · rw [if_neg h, if_neg h, if_neg h, ChainGraph.joinOutput_low]
noncomputable def rowOf (a : ChainAddr) (d : Nat) (input : HashInput) : Option (Fin d × Digest) :=
  if h : ∃ p : Fin d × Digest, input = chainRow a p.1 p.2 then some (Classical.choose h) else none
theorem rowOf_some {a : ChainAddr} {d : Nat} {input : HashInput} {p : Fin d × Digest}
    (h : rowOf a d input = some p) : input = chainRow a p.1 p.2 := by
  unfold rowOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem rowOf_none {a : ChainAddr} {d : Nat} {input : HashInput} (h : rowOf a d input = none) (p : Fin d × Digest) :
    input ≠ chainRow a p.1 p.2 := by
  intro he
  unfold rowOf at h
  rw [dif_pos ⟨p, he⟩] at h
  cases h
theorem rowOf_chainRow (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (i : Fin d) (v : Digest) :
    rowOf a d (chainRow a i v) = some (i, v) := by
  cases h : rowOf a d (chainRow a i v) with
  | none => exact absurd rfl (rowOf_none h (i, v))
  | some p =>
      have he := rowOf_some h
      obtain ⟨hs, hv⟩ := chainRow_inj (by omega) (by have := p.1.isLt; omega) he
      rw [show p = (i, v) from Prod.ext (Fin.ext hs.symm) hv.symm]
theorem rowOf_none_iff (a : ChainAddr) {d : Nat} (input : HashInput) :
    rowOf a d input = none ↔ ¬∃ step value, step < d ∧ input = chainRow a step value := by
  constructor
  · rintro h ⟨step, value, hs, rfl⟩
    exact rowOf_none h (⟨step, hs⟩, value) rfl
  · intro h
    cases hp : rowOf a d input with
    | none => rfl
    | some p => exact absurd ⟨p.1.val, p.2, p.1.isLt, rowOf_some hp⟩ h
theorem chainRow_mem (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRow a step value ∈ referenceInputs adversary := by
  unfold referenceInputs
  apply Finset.mem_union_left
  apply SeccLaw.mem_publicUniverse
  rw [chainRow_eq]
  have h : (chainInput a.key.lay a.key.tree a.key.leaf a.chain step value).length = 64 := by
    simp [chainInput, zero16, SphincsSecurity.bytesLE_length]
  rw [h]
  unfold SeccLaw.maxInputLength
  omega
abbrev Hidden (d : Nat) := (Fin d → Digest → Digest) × Digest
noncomputable def ovPub (a : ChainAddr) (d : Nat) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match rowOf a d x.val with
  | some p => ChainGraph.joinOutput (tables p.1 p.2) (high (pub x))
  | none => pub x
noncomputable def ovPriv (a : ChainAddr) (priv : FullGame.FullTable) (seed : Digest) : FullGame.FullTable :=
  Function.update priv (.inl (seedTweak a)) (setSeed a (priv (.inl (seedTweak a))) seed)
noncomputable def ov (a : ChainAddr) (d : Nat) (R : RefTables adversary) (x : Hidden d) : RefTables adversary :=
  (ovPriv a R.1 x.2, ovPub a d R.2 x.1)
noncomputable def rd (a : ChainAddr) (d : Nat) (R : RefTables adversary) : Hidden d :=
  (fun i v => low (R.2 ⟨chainRow a i v, chainRow_mem a i v⟩), seedHalf a (R.1 (.inl (seedTweak a))))
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
