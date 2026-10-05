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
theorem reached_encInput {T : Answers} {L : CanonGraph.LeafPos} {input : HashInput}
    (h : Reached T (leafOf L) input) : ∃ c : BitVec 32, input = encInput (L, leafMsg T (leafOf L), c) := by
  obtain ⟨c, -, rfl, -⟩ := h
  exact ⟨_, rfl⟩
def Free (T : Answers) (e : EncIndex) : Prop := ¬ Reached T (leafOf e.1) (encInput e)
def freeSet (T : Answers) : Set EncIndex := {e | Free T e}
noncomputable def rowDec (T A : Answers) (L : CanonGraph.LeafPos) (c : Nat) : Option (List Nat) :=
  searchDecode (leafOf L).lay (low (A (.inl (.inr (encodingRow (leafOf L) (leafMsg T (leafOf L))
    (BitVec.ofNat 32 c))))))
theorem rowDec_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (L : CanonGraph.LeafPos) (c : Nat)
    (hc : c < counterLimit) (hprev : ∀ c' < c, rowDec T T L c' = none) :
    rowDec T T' L c = none ↔ rowDec T T L c = none := by
  rcases h (.inl (.inr (encodingRow (leafOf L) (leafMsg T (leafOf L)) (BitVec.ofNat 32 c))))
      (Or.inr ⟨L, c, hc, rfl, hprev⟩) with he | hrej
  · unfold rowDec
    rw [he]
  · obtain ⟨hT, hT'⟩ := hrej.layer (encInput_hdr (L, leafMsg T (leafOf L), BitVec.ofNat 32 c))
    exact ⟨fun _ => hT, fun _ => hT'⟩
theorem rowDec_prefix_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (L : CanonGraph.LeafPos) :
    ∀ c, c ≤ counterLimit → ((∀ c' < c, rowDec T T' L c' = none) ↔ ∀ c' < c, rowDec T T L c' = none) := by
  intro c
  induction c with
  | zero =>
      intro _
      exact ⟨fun _ c' hc' => absurd hc' (Nat.not_lt_zero _), fun _ c' hc' => absurd hc' (Nat.not_lt_zero _)⟩
  | succ c ih =>
      intro hc
      have ih' := ih (by omega)
      constructor
      · intro hT' c' hc'
        have hprev := ih'.mp (fun c'' hc'' => hT' c'' (by omega))
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
        · exact hprev c' hlt
        · exact (rowDec_congr h L c' (by omega) hprev).mp (hT' c' (by omega))
      · intro hT c' hc'
        have hprev : ∀ c'' < c, rowDec T T L c'' = none := fun c'' hc'' => hT c'' (by omega)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc' with hlt | rfl
        · exact ih'.mpr hprev c' hlt
        · exact (rowDec_congr h L c' (by omega) hprev).mpr (hT c' (by omega))
theorem reached_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (L : CanonGraph.LeafPos)
    (input : HashInput) : Reached T' (leafOf L) input ↔ Reached T (leafOf L) input := by
  have hm : leafMsg T' (leafOf L) = leafMsg T (leafOf L) := leafMsg_congr_nonEnc (nonEnc_of_honest h) _
  unfold Reached
  rw [hm]
  constructor
  · rintro ⟨c, hc, rfl, hprev⟩
    exact ⟨c, hc, rfl, (rowDec_prefix_congr h L c (le_of_lt hc)).mp hprev⟩
  · rintro ⟨c, hc, rfl, hprev⟩
    exact ⟨c, hc, rfl, (rowDec_prefix_congr h L c (le_of_lt hc)).mpr hprev⟩
theorem free_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') : freeSet T' = freeSet T := by
  ext e
  simp only [freeSet, Set.mem_ofPred_eq, Free]
  rw [reached_congr h]
section Overwrite
variable {U : Finset HashInput}
noncomputable def ov (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) : U → HashOutput :=
  fun u => if h : ∃ e, e ∈ k ∧ encInput e = u.val then y ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else pub u
noncomputable def rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) :
    k → HashOutput :=
  fun e => pub ⟨encInput e.val, hU (encInput_short e.val)⟩
theorem ov_at (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput)
    (e : k) : ov k pub y ⟨encInput e.val, hU (encInput_short e.val)⟩ = y e := by
  unfold ov
  have h : ∃ e', e' ∈ k ∧ encInput e' = encInput e.val := ⟨e.val, e.property, rfl⟩
  rw [dif_pos h]
  have he : Classical.choose h = e.val := encInput_injective (Classical.choose_spec h).2
  congr 1
  exact Subtype.ext he
theorem ov_other (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) (u : U)
    (hu : ∀ e, e ∈ k → encInput e ≠ u.val) : ov k pub y u = pub u := by
  unfold ov
  rw [dif_neg]
  rintro ⟨e, he, heq⟩
  exact hu e he heq
theorem rd_ov (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput) (y : k → HashOutput) :
    rd hU k (ov k pub y) = y := by
  funext e
  exact ov_at hU k pub y e
theorem ov_ov_rd (hU : SeccLaw.publicUniverse ⊆ U) (k : Set EncIndex) (pub : U → HashOutput)
    (y : k → HashOutput) : ov k (ov k pub y) (rd hU k pub) = pub := by
  funext u
  unfold ov
  split_ifs with h
  · unfold rd
    congr 1
    exact Subtype.ext ((Classical.choose_spec h).2)
  · rfl
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
theorem honest_ov (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    ∀ q, HonestQ (eagerAnswers U privateTable pub) q →
      eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y) q =
        eagerAnswers U privateTable pub q := by
  intro q hq
  rcases q with (coin | input) | coordinate
  · simp only [eagerAnswers]
  · by_cases hin : input ∈ U
    · rw [eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩,
        eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩]
      apply ov_other
      intro e he heq
      rcases hq with hnon | ⟨L, hr⟩
      · have h' : encInput e = input := heq
        exact hnon (h' ▸ encInput_encHeader e)
      · obtain ⟨c, hc⟩ := reached_encInput hr
        have hee := encInput_injective ((show encInput e = input from heq).trans hc)
        apply he
        rw [hee, ← hc]
        exact hr
    · rw [eagerAnswers_public_not_mem U _ _ input hin, eagerAnswers_public_not_mem U _ _ input hin]
  · simp only [eagerAnswers]
theorem free_ov (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    freeSet (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) =
      freeSet (eagerAnswers U privateTable pub) :=
  free_congr (AgreeOn.of_eq (honest_ov U privateTable pub y))
theorem public_resample (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput))
    [Fintype (U → HashOutput)] (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (F : (U → HashOutput) → ENNReal) :
    ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub * F pub =
      ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub *
        ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
          F (ov (freeSet (eagerAnswers U privateTable pub)) pub y) :=
  @uniform_resample_tsum (U → HashOutput) (Set EncIndex) _ _ (fun k : Set EncIndex => k → HashOutput) iX _
    (fun pub => freeSet (eagerAnswers U privateTable pub)) (fun k pub y => ov k pub y) (fun k pub => rd hU k pub)
    (fun pub y => rd_ov hU _ pub y) (fun pub y => ov_ov_rd hU _ pub y) (fun pub y => free_ov U privateTable pub y) F
def Rej (T : Answers) (e : EncIndex) : Prop :=
  Reached T (leafOf e.1) (encInput e) ∧ searchDecode e.1.lay (low (T (.inl (.inr (encInput e))))) = none
def cellSet (T : Answers) : Set EncIndex := {e | Free T e ∨ Rej T e}
abbrev CellKey := Set EncIndex × Set EncIndex
def cellKey (T : Answers) : CellKey := (cellSet T, freeSet T)
noncomputable def rejAnswers (lay : Layer) : Finset HashOutput :=
  Finset.univ.filter fun a => searchDecode lay (low a) = none
theorem mem_rejAnswers (lay : Layer) (a : HashOutput) : a ∈ rejAnswers lay ↔ searchDecode lay (low a) = none := by
  simp only [rejAnswers, Finset.mem_filter, Finset.mem_univ, true_and]
theorem searchDecode_allOnes (lay : Layer) : searchDecode lay (low (BitVec.allOnes 256)) = none := by
  fin_cases lay <;> decide +kernel
theorem rejAnswers_nonempty (lay : Layer) : (rejAnswers lay).Nonempty :=
  ⟨BitVec.allOnes 256, (mem_rejAnswers lay _).mpr (searchDecode_allOnes lay)⟩
noncomputable def cellInit (k : CellKey) (e : k.1) : Finset HashOutput :=
  if e.val ∈ k.2 then Finset.univ else rejAnswers e.val.1.lay
theorem cellInit_nonempty (k : CellKey) (e : k.1) : (cellInit k e).Nonempty := by
  unfold cellInit
  split_ifs
  · exact Finset.univ_nonempty
  · exact rejAnswers_nonempty _
theorem rej_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') (e : EncIndex) : Rej T' e ↔ Rej T e := by
  constructor
  · rintro ⟨hr', hv'⟩
    have hr := (reached_congr h e.1 _).mp hr'
    refine ⟨hr, ?_⟩
    obtain ⟨c, hc, hin, hprev⟩ := hr
    rw [hin] at hv' ⊢
    exact (rowDec_congr h e.1 c hc hprev).mp hv'
  · rintro ⟨hr, hv⟩
    refine ⟨(reached_congr h e.1 _).mpr hr, ?_⟩
    obtain ⟨c, hc, hin, hprev⟩ := hr
    rw [hin] at hv ⊢
    exact (rowDec_congr h e.1 c hc hprev).mpr hv
theorem cellKey_congr {T T' : Answers} (h : AgreeOn (HonestQ T) T T') : cellKey T' = cellKey T := by
  have hf := free_congr h
  refine Prod.ext ?_ hf
  ext e
  have hfe : Free T' e ↔ Free T e := by
    have := congrArg (fun s : Set EncIndex => e ∈ s) hf
    simpa only [freeSet, Set.mem_setOf_eq, eq_iff_iff] using this
  show (Free T' e ∨ Rej T' e) ↔ (Free T e ∨ Rej T e)
  rw [hfe, rej_congr h]
theorem rej_of_cell {T : Answers} {e : EncIndex} (he : e ∈ (cellKey T).1) (hf : e ∉ (cellKey T).2) : Rej T e := by
  rcases he with h | h
  · exact absurd h hf
  · exact h
theorem agree_ovc (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : (cellKey (eagerAnswers U privateTable pub)).1 → HashOutput)
    (hy : ∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e) :
    AgreeOn (HonestQ (eagerAnswers U privateTable pub)) (eagerAnswers U privateTable pub)
      (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) := by
  intro q hq
  rcases q with (coin | input) | coordinate
  · left; simp only [eagerAnswers]
  · by_cases hin : input ∈ U
    · by_cases hcell : ∃ e, e ∈ (cellKey (eagerAnswers U privateTable pub)).1 ∧ encInput e = input
      · obtain ⟨e, he, rfl⟩ := hcell
        right
        rcases hq with hnon | ⟨L, hr⟩
        · exact absurd (encInput_encHeader e) hnon
        · obtain ⟨c, hc⟩ := reached_encInput hr
          have hee : e = (L, leafMsg (eagerAnswers U privateTable pub) (leafOf L), c) := encInput_injective hc
          have hr' : Reached (eagerAnswers U privateTable pub) (leafOf e.1) (encInput e) := by
            rw [hee]
            rw [hee] at hr
            exact hr
          have hnf : e ∉ (cellKey (eagerAnswers U privateTable pub)).2 := fun hfree => hfree hr'
          have hrej := rej_of_cell he hnf
          refine RejPair.mk (encInput_hdr e) hrej.2 ?_
          rw [eagerAnswers_public_mem U privateTable _ ⟨encInput e, hin⟩]
          have hat := ov_at hU (cellKey (eagerAnswers U privateTable pub)).1 pub y ⟨e, he⟩
          rw [hat]
          have hmem := hy ⟨e, he⟩
          unfold cellInit at hmem
          rw [if_neg hnf] at hmem
          exact (mem_rejAnswers _ _).mp hmem
      · left
        rw [eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩,
          eagerAnswers_public_mem U privateTable _ ⟨input, hin⟩]
        exact ov_other _ _ _ _ (fun e he heq => hcell ⟨e, he, heq⟩)
    · left
      rw [eagerAnswers_public_not_mem U _ _ input hin, eagerAnswers_public_not_mem U _ _ input hin]
  · left; simp only [eagerAnswers]
theorem cellKey_ovc (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (y : (cellKey (eagerAnswers U privateTable pub)).1 → HashOutput)
    (hy : ∀ e, y e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e) :
    cellKey (eagerAnswers U privateTable (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y)) =
      cellKey (eagerAnswers U privateTable pub) :=
  cellKey_congr (agree_ovc U hU privateTable pub y hy)
theorem rd_cellInit (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (e : (cellKey (eagerAnswers U privateTable pub)).1) :
    rd hU (cellKey (eagerAnswers U privateTable pub)).1 pub e ∈ cellInit (cellKey (eagerAnswers U privateTable pub)) e := by
  unfold cellInit
  split_ifs with hf
  · exact Finset.mem_univ _
  · have hrej := rej_of_cell e.property hf
    rw [mem_rejAnswers]
    have h2 := hrej.2
    rw [eagerAnswers_public_mem U privateTable _ ⟨encInput e.val, hU (encInput_short e.val)⟩] at h2
    exact h2
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
set_option maxRecDepth 100000 in
theorem public_resample_cells [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    [Fintype (U → HashOutput)] (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (F : (U → HashOutput) → ENNReal) :
    ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub * F pub =
      ∑' pub, PMF.uniformOfFintype (U → HashOutput) pub *
        ∑' y, PMF.uniformOfFinset (Fintype.piFinset (cellInit (cellKey (eagerAnswers U privateTable pub))))
            (Fintype.piFinset_nonempty.mpr (cellInit_nonempty _)) y *
          F (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y) := by
  let A : ∀ k : CellKey, Finset (k.1 → HashOutput) := fun k => Fintype.piFinset (cellInit k)
  have hA : ∀ k, (A k).Nonempty := fun k => Fintype.piFinset_nonempty.mpr (cellInit_nonempty k)
  have iN : ∀ k, Nonempty ↥(A k) := fun k => (hA k).to_subtype
  let rd' : ∀ k : CellKey, (U → HashOutput) → ↥(A k) := fun k pub =>
    if h : rd hU k.1 pub ∈ A k then ⟨rd hU k.1 pub, h⟩ else Classical.choice (iN k)
  have hmem : ∀ pub, rd hU (cellKey (eagerAnswers U privateTable pub)).1 pub ∈
      A (cellKey (eagerAnswers U privateTable pub)) :=
    fun pub => Fintype.mem_piFinset.mpr (rd_cellInit U hU privateTable pub)
  have hrdv : ∀ (k : CellKey) (pub' : U → HashOutput) (h : rd hU k.1 pub' ∈ A k),
      rd' k pub' = ⟨rd hU k.1 pub', h⟩ := by
    intro k pub' h
    show (if h : rd hU k.1 pub' ∈ A k then (⟨rd hU k.1 pub', h⟩ : ↥(A k)) else Classical.choice (iN k)) = _
    rw [dif_pos h]
  have key := @uniform_resample_tsum (U → HashOutput) CellKey _ _ (fun k => ↥(A k)) (fun k => inferInstance) iN
    (fun pub => cellKey (eagerAnswers U privateTable pub)) (fun k pub x => ov k.1 pub x.val) rd'
    (fun pub x => by
      obtain ⟨xv, xp⟩ := x
      have he : rd hU (cellKey (eagerAnswers U privateTable pub)).1
          (ov (cellKey (eagerAnswers U privateTable pub)).1 pub xv) = xv := rd_ov hU _ pub xv
      have hm : rd hU (cellKey (eagerAnswers U privateTable pub)).1
          (ov (cellKey (eagerAnswers U privateTable pub)).1 pub xv) ∈
          A (cellKey (eagerAnswers U privateTable pub)) := by rw [he]; exact xp
      refine (hrdv _ _ hm).trans ?_
      exact Subtype.mk_eq_mk.mpr he)
    (fun pub x => by
      have h2 := hrdv _ pub (hmem pub)
      show ov (cellKey (eagerAnswers U privateTable pub)).1 (ov (cellKey (eagerAnswers U privateTable pub)).1 pub x.val)
        (rd' (cellKey (eagerAnswers U privateTable pub)) pub).val = pub
      rw [h2]
      exact ov_ov_rd hU _ pub x.val)
    (fun pub x => cellKey_ovc U hU privateTable pub x.val (Fintype.mem_piFinset.mp x.property)) F
  rw [key]
  refine tsum_congr fun pub => ?_
  congr 1
  exact tsum_uniform_coe (A (cellKey (eagerAnswers U privateTable pub))) (hA _) (iN _)
    (fun y => F (ov (cellKey (eagerAnswers U privateTable pub)).1 pub y))
end Tables
end Enc
end SigGolfCandidate.T3.Security.Wots
