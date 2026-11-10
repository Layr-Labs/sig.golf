import SigGolfCandidate.Merge112S
import SigGolfCandidate.Merge112SA
import SigGolfCandidate.Merge112SB
set_option debug.skipKernelTC true
set_option linter.all false

namespace ClaudeWCT.W9.T3.Security.Wots.Z5
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open OracleComp OracleSpec ENNReal
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted (Combined ReferenceFailed EncodingMatch Structural TwoEdge
  TwoContacts MarkerFirstEvent ContactFirstEvent)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme FamCaps)
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem seed_error_split {S : FamScheme} {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 301)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q < 2 ^ 128)
    (hy : (q : ℝ) / 2 ^ 128 ≤ 2163 / 1000000) :
    (FamTot.errTotF S adversary q).toReal ≤ (261 / 200) * ((q : ℝ) / 2 ^ 128) ^ 2 := by
  refine (FamTot.errTotF_toReal H adversary q hq).trans ?_
  set y := (q : ℝ) / 2 ^ 128
  have hy0 : 0 ≤ y := by positivity
  have hd : 0 < 1 - y := by linarith
  have hC' : (Cmax : ℝ) ≤ 301 := by exact_mod_cast hC
  rw [div_le_iff₀ hd]
  have h1 : 2 * (Cmax : ℝ) * y ≤ 261 / 200 * (1 - y) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg y)]

theorem toReal_one_sub (q : Nat) (hq : q < 2 ^ 128) :
    (1 - (q : ENNReal) / 2 ^ 128).toReal = 1 - (q : ℝ) / 2 ^ 128 := by
  have hle : (q : ENNReal) / 2 ^ 128 ≤ 1 := by
    rw [ENNReal.div_le_iff (by simp) (by simp), one_mul]; exact_mod_cast hq.le
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top]
  simp [ENNReal.toReal_div]

/-- **The split primitive bound, middle window** (θ = 397071/200000, error quadratic 37/20). No `set` on the
reference law: abbreviating it made the kernel check of `masses_finite` recurse without bound. -/
theorem primitive_middle_split (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 301)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hy : (q : ℝ) / 2 ^ 128 ≤ 2163 / 1000000)
    (A1 : ∀ a, WotsExtract.SourceChain7 a →
      (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => Restart.ContactAfterStop (fun T trace => Restart.MarkerAt T trace a)
          s.answers s.trace a | PairedReference.referenceExperiment adversary q]) ≤
      ∑' s, PairedReference.referenceExperiment adversary q s *
        (((preCount a s + 2 * (CanonicalRef.Normalized.prefixCount a s - preCount a s) : ℕ) : ENNReal) *
          (if Marked a s then 1 else 0)) +
        ((2 ^ 128 : ENNReal) + ((2 * q : ℕ) : ENNReal)) * FamLift.errCF S adversary q a)
    (A2 : ∀ a, WotsExtract.SourceChain7 a →
      (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreContact a | PairedReference.referenceExperiment adversary q] ≤
        (2 / 2 ^ 128) * ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
          (1 + (2 / 2 ^ 128) * q) * FamLift.errCF S adversary q a)
    (A3 : ∀ a, WotsExtract.SourceChain7 a →
      (1 - (q : ENNReal) / 2 ^ 128) * Pr[PreTwoEdge a | PairedReference.referenceExperiment adversary q] ≤
        twoEdgeRate q * ∑' s, PairedReference.referenceExperiment adversary q s * (preCount a s : ENNReal) +
          (1 + twoEdgeRate q * q) * FamLift.errCF S adversary q a)
    (B1 : ∑ p : CanonGraph.LeafPos × Fin 58, ∑' s, PairedReference.referenceExperiment adversary q s *
        (if WotsExtract.SourceChain7 (Enc.chainAt p) ∧ Marked (Enc.chainAt p) s
          then (preCount (Enc.chainAt p) s : ENNReal) else 0) ≤
      88 * ((q : ENNReal) / 2 ^ 128) *
        ∑' s, PairedReference.referenceExperiment adversary q s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal))
    (B2 : Pr[fun s => ∃ a, WotsExtract.SourceChain7 a ∧
        ∃ k, CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          ¬CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
          CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) s.trace a |
        PairedReference.referenceExperiment adversary q] ≤
      88 * ((q : ENNReal) / 2 ^ 128) *
        ∑' s, PairedReference.referenceExperiment adversary q s * (preContactCount s : ENNReal)) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (397071 / 200000) * ((PairedSmallT.prefixMass adversary q).toReal / 2 ^ 128 +
        (PairedSmallT.encodingMass adversary q).toReal / 2 ^ 128) +
      (PairedSmallT.otherMass adversary q).toReal / 2 ^ 128 + (37 / 20) * ((q : ℝ) / 2 ^ 128) ^ 2 +
        (1 / 2 ^ 139 + 1 / 2 ^ 142) := by
  have hqN : q < 2 ^ 128 := by omega
  set EP := ∑' s, (PairedReference.referenceExperiment adversary q) s * (Contacts.prefixClassCount s : ENNReal) with hEP
  set EE := ∑' s, (PairedReference.referenceExperiment adversary q) s * (ClaudeWCT.W9.T3.Security.Wots.encodingCount s : ENNReal) with hEE
  set EO := ∑' s, (PairedReference.referenceExperiment adversary q) s * (PairedReference.otherCount s : ENNReal) with hEO
  set ERR := FamTot.errTotF S adversary q with hERR
  set PC := ∑' s, (PairedReference.referenceExperiment adversary q) s * (preContactCount s : ENNReal) with hPC
  have hf := PairedSmallT.masses_finite adversary q hq
  have hEPf : EP ≠ ⊤ := hf.1
  have hEEf : EE ≠ ⊤ := hf.2.1
  have hEOf : EO ≠ ⊤ := hf.2.2.1
  have hERRf : ERR ≠ ⊤ := CanonicalWeighted.errTotF_ne_topFam S H adversary q hqN
  have hsum := pre_post_le adversary q
  have hPreSf : PreS adversary q ≠ ⊤ := ne_top_of_le_ne_top hEPf (le_trans le_self_add hsum)
  have hPostSf : PostS adversary q ≠ ⊤ := ne_top_of_le_ne_top hEPf (le_trans le_add_self hsum)
  have hPreMle : PreM adversary q ≤ PreS adversary q := by
    unfold PreM PreS
    refine Finset.sum_le_sum fun a _ => ENNReal.tsum_le_tsum fun s => mul_le_mul' le_rfl ?_
    split_ifs <;> simp
  have hPreMf : PreM adversary q ≠ ⊤ := ne_top_of_le_ne_top hPreSf hPreMle
  have hPCle : PC ≤ (Contacts.sourceChains7.card : ENNReal) := by
    calc PC ≤ ∑' s, (PairedReference.referenceExperiment adversary q) s * (Contacts.sourceChains7.card : ENNReal) :=
          ENNReal.tsum_le_tsum fun s => mul_le_mul' le_rfl (by exact_mod_cast Finset.card_filter_le _ _)
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hPCf : PC ≠ ⊤ := ne_top_of_le_ne_top (by simp) hPCle
  have h1y := toReal_one_sub q hqN
  set y := (q : ℝ) / 2 ^ 128 with hydef
  have hy0 : 0 ≤ y := by positivity
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  -- the mixed split
  have hvw : (407137 / 500000 : ENNReal) + 92863 / 500000 = 1 := by
    norm_num [ENNReal.div_add_div_same]; exact ENNReal.div_self (by norm_num) (by finiteness)
  have hsplit := combined_split_le adversary q (407137 / 500000) (92863 / 500000) hvw
  -- the pieces
  have hF := CanonicalWeighted.reference_failed_le adversary q
  have hM := CanonicalRef.reference_encodingMatch_le adversary q
  have hS := CanonicalWeighted.structural_reference_le adversary q (PairedReference.reference_structural_in_le adversary q)
  have hU : Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s | (PairedReference.referenceExperiment adversary q)] ≤
      ((2 / 2 ^ 128) * EP + (1 + (2 / 2 ^ 128) * q) * ERR) / (1 - (q : ENNReal) / 2 ^ 128) :=
    (CanonicalWeighted.nonstructural_reference_le adversary q).trans (FamContacts.reference_contacts_cost_leF H adversary q hqN)
  have hTC := Restart.reference_twoContacts_leFam S H adversary q hqN
  have hMF := mf_total adversary q S A1
  have hCF : Pr[ContactFirstEvent | (PairedReference.referenceExperiment adversary q)] ≤ 88 * ((q : ENNReal) / 2 ^ 128) * PC := B2
  have hPC := pc_total adversary q S A2
  have hPTE := pte_total adversary q S A3
  have hPost := post_total adversary q
  have hPreM := preM_total adversary q B1
  have hErr := seed_error_split H hC adversary q hqN hy

  -- finiteness of the probabilities
  have hpf : ∀ (P : RefSample → Prop), Pr[P | (PairedReference.referenceExperiment adversary q)] ≠ ⊤ := fun P => ne_top_of_le_ne_top (by simp) probEvent_le_one
  have hqf : (q : ENNReal) / 2 ^ 128 ≠ ⊤ := by finiteness
  have h1 : (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  -- real forms
  have rsplit := ENNReal.toReal_mono (by
    have := hpf ReferenceFailed; have := hpf EncodingMatch; have := hpf Structural
    have := hpf (fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s)
    have := hpf TwoContacts; have := hpf MarkerFirstEvent; have := hpf ContactFirstEvent; have := hpf PreTwoEdgeEvent
    finiteness) hsplit
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat] at rsplit
  have rF := ENNReal.toReal_mono (by finiteness) hF
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at rF
  have rM := ENNReal.toReal_mono (by finiteness) hM
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_pow] at rM
  have rS := ENNReal.toReal_mono (by finiteness) hS
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] at rS
  have rU := ENNReal.toReal_mono (by
    have hd : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
      apply ne_of_gt; apply tsub_pos_iff_lt.mpr
      rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]; exact_mod_cast hqN
    exact ENNReal.div_ne_top (by finiteness) hd) hU
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_one, ENNReal.toReal_natCast, ENNReal.toReal_pow, h1y] at rU

  have hd : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt; apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]; exact_mod_cast hqN
  have hd2 : (1 - (q : ENNReal) / 2 ^ 128) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hT1 : (4 * ((q : ENNReal) / 2 ^ 128) / 2 ^ 128) * EP / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 ≠ ⊤ :=
    ENNReal.div_ne_top (by finiteness) hd2
  have hT2 : 2 * ((q : ENNReal) / 2 ^ 128) * (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ^ 2 ≠ ⊤ :=
    ENNReal.div_ne_top (by finiteness) hd2
  have hT3 : (1 + 2 * ((q : ENNReal) / 2 ^ 128)) / (1 - (q : ENNReal) / 2 ^ 128) ≠ ⊤ := ENNReal.div_ne_top (by finiteness) hd
  have rTC := ENNReal.toReal_mono (by finiteness) hTC
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_one, ENNReal.toReal_natCast, ENNReal.toReal_pow, h1y] at rTC
  have rMF := ENNReal.toReal_mono (by finiteness) hMF
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.toReal_pow, h1y] at rMF
  have rCF := ENNReal.toReal_mono (by finiteness) hCF
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.toReal_pow] at rCF
  have rPC := ENNReal.toReal_mono (by finiteness) hPC
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_one, ENNReal.toReal_natCast, ENNReal.toReal_pow, h1y] at rPC
  have hTEf : twoEdgeRate q ≠ ⊤ := by unfold twoEdgeRate; finiteness
  have rPTE := ENNReal.toReal_mono (by finiteness) hPTE
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_one, ENNReal.toReal_natCast, ENNReal.toReal_pow, h1y] at rPTE
  have hTEr : (twoEdgeRate q).toReal = (3 / 2 + 4 * y + 2 * y ^ 2) / 2 ^ 128 := by
    unfold twoEdgeRate
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_natCast, ENNReal.toReal_pow]
    norm_num [hydef]
  rw [hTEr] at rPTE
  have rPost := ENNReal.toReal_mono (by finiteness) hPost
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.toReal_pow] at rPost
  have rPreM := ENNReal.toReal_mono (by finiteness) hPreM
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast, ENNReal.toReal_pow] at rPreM
  have hsum' : PreS adversary q + PostS adversary q ≤ EP := hsum
  have rSum := ENNReal.toReal_mono hEPf hsum'
  rw [ENNReal.toReal_add hPreSf hPostSf] at rSum
  have h1y' : 0 < 1 - y := by
    have : y ≤ 2163 / 1000000 := hy
    linarith
  set pr := (Pr[Combined | (PairedReference.referenceExperiment adversary q)]).toReal
  set pf := (Pr[ReferenceFailed | (PairedReference.referenceExperiment adversary q)]).toReal
  set pm := (Pr[EncodingMatch | (PairedReference.referenceExperiment adversary q)]).toReal
  set ps := (Pr[Structural | (PairedReference.referenceExperiment adversary q)]).toReal
  set pu := (Pr[fun s => TwoEdge s ∨ TwoContacts s ∨ MarkerFirstEvent s ∨ ContactFirstEvent s | (PairedReference.referenceExperiment adversary q)]).toReal
  set ptc := (Pr[TwoContacts | (PairedReference.referenceExperiment adversary q)]).toReal
  set pmf := (Pr[MarkerFirstEvent | (PairedReference.referenceExperiment adversary q)]).toReal
  set pcf := (Pr[ContactFirstEvent | (PairedReference.referenceExperiment adversary q)]).toReal
  set pte := (Pr[PreTwoEdgeEvent | (PairedReference.referenceExperiment adversary q)]).toReal
  have xsum : (PreS adversary q).toReal / 2 ^ 128 + (PostS adversary q).toReal / 2 ^ 128 ≤ EP.toReal / 2 ^ 128 := by
    rw [← add_div]; exact div_le_div_of_nonneg_right rSum hN.le
  have xpost : (PostS adversary q).toReal / 2 ^ 128 ≤ 4488 * y * (EE.toReal / 2 ^ 128) := by
    have h : (PostS adversary q).toReal / 2 ^ 128 ≤ ((q : ℝ) * (4488 / 2 ^ 128 * EE.toReal)) / 2 ^ 128 :=
      div_le_div_of_nonneg_right rPost hN.le
    refine h.trans (le_of_eq ?_); rw [hydef]; ring
  have xpreM : (PreM adversary q).toReal / 2 ^ 128 ≤ 88 * y * (EE.toReal / 2 ^ 128) := by
    have h : (PreM adversary q).toReal / 2 ^ 128 ≤ (88 * ((q : ℝ) / 2 ^ 128) * EE.toReal) / 2 ^ 128 :=
      div_le_div_of_nonneg_right rPreM hN.le
    refine h.trans (le_of_eq ?_); rw [hydef]; ring
  have xerr : ERR.toReal ≤ (261 / 200) * y ^ 2 := hErr
  have xpf : pf ≤ 1 / 2 ^ 139 := rF
  have xpm : pm ≤ 7 / 4 * (EE.toReal / 2 ^ 128) := by
    have h : pm ≤ 7 / (4 * 2 ^ 128) * EE.toReal := rM
    refine h.trans (le_of_eq ?_); ring
  have xps : ps ≤ EO.toReal / 2 ^ 128 + 1 / 2 ^ 142 := by
    have h : ps ≤ (2 ^ 128 : ℝ)⁻¹ * EO.toReal + (2 ^ 142 : ℝ)⁻¹ := rS
    refine h.trans (le_of_eq ?_); ring
  have xpu : (1 - y) * pu ≤ 2 * (EP.toReal / 2 ^ 128) + (1 + 2 * y) * ERR.toReal := by
    have h : pu ≤ (2 / 2 ^ 128 * EP.toReal + (1 + 2 / 2 ^ 128 * (q : ℝ)) * ERR.toReal) / (1 - y) := rU
    rw [le_div_iff₀ h1y'] at h
    calc (1 - y) * pu = pu * (1 - y) := by ring
      _ ≤ _ := h
      _ = _ := by rw [hydef]; ring
  have xtc : ptc ≤ 4 * y / (1 - y) ^ 2 * (EP.toReal / 2 ^ 128) +
      (2 * y * (1 + 2 * y) / (1 - y) ^ 2 + (1 + 2 * y) / (1 - y)) * ERR.toReal := by
    have h : ptc ≤ 4 * ((q : ℝ) / 2 ^ 128) / 2 ^ 128 * EP.toReal / (1 - y) ^ 2 +
      (2 * ((q : ℝ) / 2 ^ 128) * (1 + 2 * ((q : ℝ) / 2 ^ 128)) / (1 - y) ^ 2 +
        (1 + 2 * ((q : ℝ) / 2 ^ 128)) / (1 - y)) * ERR.toReal := rTC
    refine h.trans (le_of_eq ?_); rw [hydef]; ring
  have xmf : (1 - y) * pmf ≤ (PreM adversary q).toReal / 2 ^ 128 + 2 * ((PostS adversary q).toReal / 2 ^ 128) +
      (1 + 2 * y) * ERR.toReal := by
    have h : (1 - y) * (2 ^ 128 * pmf) ≤ (PreM adversary q).toReal + 2 * (PostS adversary q).toReal +
      (2 ^ 128 + ((2 * q : ℕ) : ℝ)) * ERR.toReal := rMF
    push_cast at h
    have h2 := div_le_div_of_nonneg_right h hN.le
    calc (1 - y) * pmf = (1 - y) * (2 ^ 128 * pmf) / 2 ^ 128 := by ring
      _ ≤ _ := h2
      _ = _ := by rw [hydef]; ring
  have xpc : (1 - y) * PC.toReal ≤ 2 * ((PreS adversary q).toReal / 2 ^ 128) + (1 + 2 * y) * ERR.toReal := by
    have h : (1 - y) * PC.toReal ≤ 2 / 2 ^ 128 * (PreS adversary q).toReal +
      (1 + 2 / 2 ^ 128 * (q : ℝ)) * ERR.toReal := rPC
    refine h.trans (le_of_eq ?_); rw [hydef]; ring
  have xcf : pcf ≤ 88 * y * PC.toReal := rCF
  have xte : (1 - y) * pte ≤ (3 / 2 + 4 * y + 2 * y ^ 2) * ((PreS adversary q).toReal / 2 ^ 128) +
      (1 + (3 / 2 + 4 * y + 2 * y ^ 2) * y) * ERR.toReal := by
    have h : (1 - y) * pte ≤ (3 / 2 + 4 * y + 2 * y ^ 2) / 2 ^ 128 * (PreS adversary q).toReal +
      (1 + (3 / 2 + 4 * y + 2 * y ^ 2) / 2 ^ 128 * (q : ℝ)) * ERR.toReal := rPTE
    refine h.trans (le_of_eq ?_); rw [hydef]; ring
  have xpr : pr ≤ pf + pm + ps + 407137 / 500000 * pu + 92863 / 500000 * (ptc + pmf + pcf + pte) := by
    refine rsplit.trans (le_of_eq ?_); ring
  have key := split_middle_real y (EP.toReal / 2 ^ 128) (EE.toReal / 2 ^ 128) (EO.toReal / 2 ^ 128)
    ((PreS adversary q).toReal / 2 ^ 128) ((PostS adversary q).toReal / 2 ^ 128)
    ((PreM adversary q).toReal / 2 ^ 128) PC.toReal ERR.toReal pf pm ps pu ptc pmf pcf pte pr
    hy0 hy (by positivity) (by positivity) (by positivity) (by positivity) ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg (by positivity) xsum xpost xpreM xerr xpf xpm xps xpu xtc xmf xpc xcf xte xpr
  exact key

end ClaudeWCT.W9.T3.Security.Wots.Z5

namespace ClaudeWCT.W9.T3.Security.Wots.Z5
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open OracleComp OracleSpec ENNReal
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open ClaudeWCT.W9.T3.Security.Wots.CanonicalWeighted (Combined)
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)

/-- The split primitive bound of the middle window, with the per-chain kernels (A) and the lazy-cell potentials (B). -/
theorem primitive_middle_splitFam (S : FamScheme) {Cmax : Nat} (H : FamTot.FamHyps S Cmax) (hC : Cmax ≤ 301)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hy : (q : ℝ) / 2 ^ 128 ≤ 2163 / 1000000) :
    (Pr[Combined | PairedReference.referenceExperiment adversary q]).toReal ≤
      (397071 / 200000) * ((PairedSmallT.prefixMass adversary q).toReal / 2 ^ 128 +
        (PairedSmallT.encodingMass adversary q).toReal / 2 ^ 128) +
      (PairedSmallT.otherMass adversary q).toReal / 2 ^ 128 + (37 / 20) * ((q : ℝ) / 2 ^ 128) ^ 2 +
        (1 / 2 ^ 139 + 1 / 2 ^ 142) := by
  have hqN : q < 2 ^ 128 := by omega
  exact primitive_middle_split S H hC adversary q hq hy
    (fun a ha => markerFirst_split_leF (adversary := adversary) S H q hqN a ha)
    (fun a ha => preContact_cost_leF (adversary := adversary) S H q hqN a ha)
    (fun a ha => preTwoEdge_cost_leF (adversary := adversary) S H q hqN a ha)
    (reference_pendingMarked_le adversary q) (reference_contactFirst_pre_le adversary q)

end ClaudeWCT.W9.T3.Security.Wots.Z5

namespace ClaudeWCT.W9.T3.Security.Wots.PairedSmallT
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- `clean_probability_real_ofG` with the error quadratic `errq` as a parameter (the split's middle window uses 1850/1000). -/
theorem clean_probability_real_ofGq (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hsplit : ∀ z,z∈(PairedSeccLaw.completedExperiment adversary q hq).support →
      QueryRecorded.CleanWin q z.1 → CaseABEv combinedEvent adversary z ∨ FreshForestCase adversary z)
    (theta rate : ENNReal) (htheta:theta≠⊤) (hratefin:rate≠⊤) (hmin:28883/2500000≤theta)
    (hrate : ClaudeWCT.Numerics.Law.lawAvg ClaudeWCT.Bank.Paired.honestLaw (2^32)
      (fun W=>ClaudeWCT.Bank.Paired.price W-(theta-28883/2500000))≤rate)
    (errq : ℝ)
    (hprimitive : (Pr[fun s=>combinedEvent.holds s.answers s.trace |
      PairedReference.referenceExperiment adversary q]).toReal ≤
        theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128)+
        (otherMass adversary q).toReal/2^128+errq*((q:ℝ)/2^128)^2+(1/2^139+1/2^142))
    (hincomplete : Pr[fun z=>IncompleteForestEvent adversary (z.1.1,z.1.2.2) z.2 |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^138)
    (hoverflow : Pr[fun z=>QueryRecorded.CleanWin q z.1 ∧ ¬WPair.Paired.NoOverflow adversary z |
      PairedSeccLaw.completedExperiment adversary q hq]≤1/(2:ENNReal)^137) :
    (Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]).toReal ≤
      theta.toReal*((prefixMass adversary q).toReal/2^128+(encodingMass adversary q).toReal/2^128+
        (digestMass adversary q hq).toReal/2^128)+(otherMass adversary q).toReal/2^128+
      (Pr[PartialForestNoOverflow adversary q | PairedSeccLaw.completedExperiment adversary q hq]).toReal+
      (q:ℝ)/2^128*rate.toReal+errq*((q:ℝ)/2^128)^2+1/2^136 := by
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
  have habs : (1:ℝ)/2^139+1/2^142+1/2^138+1/2^137≤1/2^136 := by norm_num
  nlinarith

/-- **The middle window through the split** (`2^-28 ≤ y ≤ 2163/10^6`, θ = 397071/200000, excess ≤ 2143/10^6). -/
theorem middle_boundSplit (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 301) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hlow:1/(2:ℝ)^28≤(q:ℝ)/2^128) (hhigh:(q:ℝ)/2^128≤2163/1000000) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  apply clean_outer_ennrealG adversary q hq
  apply middle_clean_closingG adversary q hq hlow hhigh (2143/1000000) le_rfl ?_
    (completed_partial_certifiedG adversary q hq)
  have hp:=Z5.primitive_middle_splitFam S H hC adversary q hq hhigh
  have h:=clean_probability_real_ofGq adversary q hq (completed_split_canonical adversary q hq)
    (397071/200000) (2143/1000000) (by finiteness) (by finiteness) (by
      simpa (disch:=positivity) only [ENNReal.ofReal_div_of_pos,ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (by norm_num : (28883:ℝ)/2500000≤397071/200000))
    excess_middle_actualG (1850/1000)
    (by
      simp only [ENNReal.toReal_div,ENNReal.toReal_ofNat]
      refine hp.trans (le_of_eq ?_)
      ring)
    (completed_incomplete_bound adversary q hq)
    (by simpa only [one_div] using FtsOverflow.Paired.cleanWin_noOverflow_le adversary q hq)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h

theorem small_boundSplit (S : FamScheme) {Cmax : Nat} (H : CanonicalRef.Normalized.FamTot.FamHyps S Cmax)
    (hC : Cmax ≤ 301) (adversary : Final.Paired.AdversaryP) (q : Nat) (hq:q≤2^127)
    (hpositive:1≤q) (hhigh:(q:ℝ)/2^128≤2163/1000000) :
    Pr[QueryRecorded.CleanWin q | PairedOuter.PaddedGame.tracedExperiment adversary q hq]+
      q/(2:ENNReal)^146+(2:ENNReal)⁻¹^700+((2:ENNReal)^152)⁻¹+
      q/((2^256:Nat):ENNReal)≤(q:ENNReal)/2^127 := by
  by_cases ht:(q:ℝ)/2^128≤1/2^28
  · exact tiny_boundFam S H hC adversary q hq hpositive ht
  · exact middle_boundSplit S H hC adversary q hq (le_of_lt (lt_of_not_ge ht)) hhigh

end ClaudeWCT.W9.T3.Security.Wots.PairedSmallT

namespace ClaudeWCT.W9.T3.Secc.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security
open ClaudeWCT.W9.T3M.Final.Paired
open ClaudeWCT.W9.T3.Security.Wots.FamRestart (FamScheme layoutScheme)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- **The live security theorem through the pre/post-marker split** (Z5): small route up to `y = 2163/10^6`
(tiny window, then the split's middle window), large route above. -/
theorem t3_securityP_split (S : FamScheme) (Cmax : Nat)
    (H : ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot.FamHyps S Cmax) (hC : Cmax ≤ 301) :
    ClaudeWCT.W9.T3M.Final.Paired.SecurityP := by
  apply PairedOuter.PaddedGame.securityP_of_clean_bound
  intro adversary q hpositive hq
  by_cases hsmall : (q:ℝ)/2^128 ≤ 2163/1000000
  · exact Wots.PairedSmallT.small_boundSplit S H hC adversary q hq hpositive hsmall
  · exact LargeCoupling.Paired.large_bound adversary q hq (le_of_not_ge hsmall)

/-- **The live security theorem of the v6 scheme** (the `Correctness` layout: lower 7-leaf families, charge 301). -/
theorem t3_securityP_layout_split : ClaudeWCT.W9.T3M.Final.Paired.SecurityP :=
  t3_securityP_split layoutScheme 301 ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.FamTot.layoutHyps
    (by norm_num)

end ClaudeWCT.W9.T3.Secc.Paired
