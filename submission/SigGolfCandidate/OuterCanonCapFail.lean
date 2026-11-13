import SigGolfCandidate.OuterCanonCapFailOuter
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option maxErrors 30
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterCanonBase.Paired
open ClaudeWCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance low] Classical.propDecidable
attribute [local instance] OuterCanonBase.Paired.instSampleableTypeLabels_capFail
namespace CapFailBound
theorem allFail_trials (m : WctNodePos) (test : Digest→Bool)
    (hw : ∀ (labels : Labels) j, wTrialFails labels m j ↔ test ((wHalfPos m).proj (labels (.wctNode (wWithNonce m j))))=false) :
    (fun labels : Labels => ∀ j<wTrialCap m.1.coord.val m.1.level.val,wTrialFails labels m j)=
    (fun labels : Labels => ∀ a∈wTrialSet m,test ((wHalfPos m).proj (labels a))=false) := by
  funext labels
  apply propext
  unfold wTrialSet
  constructor
  · intro h a ha
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp ha
    exact (hw labels j).mp (h j (Finset.mem_range.mp hj))
  · intro h j hj
    exact (hw labels j).mpr (h _ (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩))
theorem prob_wAllFail_le (m : WctNodePos) (h3 : OuterExtractGround.ftsNonceLevel m.1.coord.val m.1.level.val) :
    Pr[fun labels : Labels => ∀ j < wTrialCap m.1.coord.val m.1.level.val, wTrialFails labels m j |
      ($ᵗ Labels : ProbComp Labels)] ≤ ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
  classical
  by_cases h5 : m.1.level.val=5
  · have hf : Extract.Paired.first m.1.coord.val=false := by
      rcases h3 with hi|ho
      · unfold Extract.Paired.ftsNonceLevel at hi;omega
      · exact ho.2
    rw [allFail_trials m (OuterGroundCore.zeroOk m.1.coord.val) (by
      intro labels j;unfold wTrialFails;rw [if_pos h5,pairedProj_wHalfPos])]
    apply prob_outerFail_le (wHalfPos m) m.1.coord.val 0
    rw [wTrialSet_card,wTrialCap,if_pos ⟨h5,hf⟩]
  · have hi : Extract.Paired.ftsNonceLevel m.1.coord.val m.1.level.val := by
      rcases h3 with hi|ho;exact hi;exact (h5 ho.1).elim
    rw [allFail_trials m (WCT9.ftsZeroOk m.1.coord.val (2^(6-m.1.level.val))) (by
      intro labels j;unfold wTrialFails;rw [if_neg h5,pairedProj_wHalfPos])]
    apply prob_ftsFail_le
    rw [wTrialSet_card,wTrialCap,if_neg (by tauto : ¬(m.1.level.val=5 ∧ Extract.Paired.first m.1.coord.val=false))]
    unfold OuterCanonBase.wTrialCap WCT9.ftsNonceCap
    rw [if_pos hi]

/-- E8: the nonce-0 representatives of the FTS ground positions (Y7: the 72 level-3 positions and the 64 level-2
positions of coordinates `0..3` of each index). -/
def wctReps : Finset WctNodePos :=
  Finset.univ.filter (fun m : WctNodePos => OuterExtractGround.ftsNonceLevel m.1.coord.val m.1.level.val ∧
    m.1.nonce.val = 0)

/-- Y7: the slot of a ground representative among the `136` ground positions of its index. -/
def wRepCode (m : WctNodePos) : Fin 154 :=
  ⟨(if m.1.level.val=5 then 136+m.1.coord.val*2+m.1.idx.val%2 else if m.1.level.val = 3 then m.1.coord.val * 8 + m.1.idx.val % 8 else 72 + m.1.coord.val % 4 * 16 + m.1.idx.val % 16)
    % 154, Nat.mod_lt _ (by norm_num)⟩

theorem card_wctReps_le : wctReps.card ≤ 154 * 2 ^ 31 := by
  have hU : (Finset.univ : Finset (Fin (2 ^ 31) × Fin 154)).card = 154 * 2 ^ 31 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]
  rw [← hU]
  apply Finset.card_le_card_of_injOn (fun m : WctNodePos => (m.1.index, wRepCode m))
  · intro m _; simp
  · intro n hn m hm heq
    simp only [wctReps, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hn hm
    have hvn : n.1.idx.val < 2 ^ (7 - n.1.level.val - 1) := n.2
    have hvm : m.1.idx.val < 2 ^ (7 - m.1.level.val - 1) := m.2
    have hcn := n.1.coord.isLt
    have hcm := m.1.coord.isLt
    have bn : (n.1.level.val=5 ∧ n.1.idx.val<2) ∨ (n.1.level.val = 3 ∧ n.1.idx.val < 8) ∨ (n.1.level.val = 2 ∧ n.1.coord.val < 4 ∧ n.1.idx.val < 16) := by
      rcases hn.1 with hi|ho
      · rcases hi with hi|⟨hl,hc⟩
        · right;left;rw [hi] at hvn;exact ⟨hi,by simpa using hvn⟩
        · right;right;rw [hl] at hvn;exact ⟨hl,hc,by simpa using hvn⟩
      · left;rw [ho.1] at hvn;exact ⟨ho.1,by simpa using hvn⟩
    have bm : (m.1.level.val=5 ∧ m.1.idx.val<2) ∨ (m.1.level.val = 3 ∧ m.1.idx.val < 8) ∨ (m.1.level.val = 2 ∧ m.1.coord.val < 4 ∧ m.1.idx.val < 16) := by
      rcases hm.1 with hi|ho
      · rcases hi with hi|⟨hl,hc⟩
        · right;left;rw [hi] at hvm;exact ⟨hi,by simpa using hvm⟩
        · right;right;rw [hl] at hvm;exact ⟨hl,hc,by simpa using hvm⟩
      · left;rw [ho.1] at hvm;exact ⟨ho.1,by simpa using hvm⟩
    simp only [Prod.mk.injEq, wRepCode, Fin.mk.injEq] at heq
    obtain ⟨h1, h4⟩ := heq
    have key : n.1.coord.val = m.1.coord.val ∧ n.1.level.val = m.1.level.val ∧ n.1.idx.val = m.1.idx.val := by
      rcases bn with ⟨hl, hi⟩ | ⟨hl, hi⟩ | ⟨hl, hc, hi⟩ <;> rcases bm with ⟨hl', hi'⟩ | ⟨hl', hi'⟩ | ⟨hl', hc', hi''⟩ <;>
        simp only [hl, hl', show (2:Nat) ≠ 3 by decide,show (2:Nat)≠5 by decide,show (3:Nat)≠5 by decide, ↓reduceIte] at h4 <;>
        (rw [Nat.mod_eq_of_lt (show _ < 154 by omega), Nat.mod_eq_of_lt (show _ < 154 by omega)] at h4) <;> omega
    obtain ⟨hc', hl', hi'⟩ := key
    have hn0 := hn.2
    have hm0 := hm.2
    obtain ⟨⟨index, coord, level, idx, nonce⟩, hv⟩ := n
    obtain ⟨⟨index', coord', level', idx', nonce'⟩, hv'⟩ := m
    simp only at h1 hc' hl' hi' hn0 hm0
    have e1 : coord = coord' := Fin.ext hc'
    have e2 : level = level' := Fin.ext hl'
    have e3 : idx = idx' := Fin.ext hi'
    have e4 : nonce = nonce' := Fin.ext (by omega)
    subst h1 e1 e2 e3 e4
    rfl

theorem sum_wct_arith : ((154 * 2 ^ 31 : Nat) : ℝ) * (36788 / 100000 : ℝ) ^ 128 ≤ 1 / 2 ^ 145 := by
  norm_num

theorem sum_wctReps_le (f : WctNodePos → ℝ≥0∞)
    (hf : ∀ m ∈ wctReps, f m ≤ ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128)) :
    ∑ m ∈ wctReps, f m ≤ (2 ^ 145 : ℝ≥0∞)⁻¹ := by
  calc ∑ m ∈ wctReps, f m ≤ ∑ m ∈ wctReps, ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := Finset.sum_le_sum hf
    _ = (wctReps.card : ℝ≥0∞) * ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((154 * 2 ^ 31 : Nat) : ℝ≥0∞) * ENNReal.ofReal ((36788 / 100000 : ℝ) ^ 128) := by
        gcongr; exact_mod_cast card_wctReps_le
    _ = ENNReal.ofReal (((154 * 2 ^ 31 : Nat) : ℝ) * (36788 / 100000 : ℝ) ^ 128) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 145) := ENNReal.ofReal_le_ofReal sum_wct_arith
    _ = (2 ^ 145 : ℝ≥0∞)⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]

theorem capFailW_eq :
    CapFailW = fun labels : Labels =>
      ∃ m ∈ wctReps, ∀ j < wTrialCap m.1.coord.val m.1.level.val, wTrialFails labels m j := by
  funext labels
  apply propext
  unfold CapFailW
  simp only [wctReps, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨m, h3, h0, h⟩ => ⟨m, ⟨h3, h0⟩, h⟩, fun ⟨m, ⟨h3, h0⟩, h⟩ => ⟨m, h3, h0, h⟩⟩

theorem three_quarters : (2 ^ 145 : ℝ≥0∞)⁻¹ + ((2 ^ 144 : ℝ≥0∞)⁻¹ + (2 ^ 144 : ℝ≥0∞)⁻¹) ≤ (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have e : ∀ k : ℕ, (2 ^ k : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ k) := fun k => by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rw [e, e, e, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end CapFailBound

open CapFailBound in
/-- E8: an FTS ground position exhausts its cap with probability at most `2^-145`. -/
theorem prob_capFailW_le :
    Pr[CapFailW | ($ᵗ Labels : ProbComp Labels)] ≤ (2 ^ 145 : ℝ≥0∞)⁻¹ := by
  rw [capFailW_eq]
  refine (probEvent_exists_finset_le_sum wctReps _ _).trans ?_
  exact sum_wctReps_le _ fun m hm => by
    simp only [wctReps, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact prob_wAllFail_le m hm.1

open CapFailBound in
theorem prob_capFailT_le :
    Pr[CapFailT | ($ᵗ Labels : ProbComp Labels)] ≤ (2 ^ 144 : ℝ≥0∞)⁻¹ + (2 ^ 144 : ℝ≥0∞)⁻¹ := by
  rw [capFail_eq]
  refine (probEvent_exists_finset_le_sum (topReps ∪ lowReps) _ _).trans ?_
  rw [Finset.sum_union disjoint_reps]
  refine add_le_add ?_ (sum_lowReps_le _ fun n hn => by
    simp only [lowReps, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    exact prob_allFail_le_low n hn.1 hn.2.1)
  calc ∑ n ∈ topReps, Pr[fun labels : Labels =>
          ∀ j < trialCap n.1.lay n.1.level.val, trialFails labels n j | ($ᵗ Labels : ProbComp Labels)]
      ≤ ∑ n ∈ topReps, ENNReal.ofReal (failR n.1.level.val) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [topReps, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        exact prob_allFail_le n hn.1 hn.2.1
    _ = ∑ l ∈ Finset.range 11, ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l),
          ENNReal.ofReal (failR n.1.level.val) := by
        rw [Finset.sum_fiberwise_of_maps_to]
        intro n hn
        simp only [topReps, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        exact Finset.mem_range.mpr hn.2.1
    _ ≤ ∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ≥0∞) * ENNReal.ofReal (failR l) := by
        apply Finset.sum_le_sum
        intro l _
        have hfib := card_fiber_le l
        calc ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l), ENNReal.ofReal (failR n.1.level.val)
            = ∑ n ∈ topReps.filter (fun n : TreeNode => n.1.level.val = l), ENNReal.ofReal (failR l) :=
              Finset.sum_congr rfl (fun n hn => by simp only [Finset.mem_filter] at hn; rw [hn.2])
          _ = ((topReps.filter (fun n : TreeNode => n.1.level.val = l)).card : ℝ≥0∞) *
                ENNReal.ofReal (failR l) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := by gcongr
    _ = ENNReal.ofReal (∑ l ∈ Finset.range 11, ((2 ^ (11 - l) : Nat) : ℝ) * failR l) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (by positivity) (failR_nonneg l))]
        apply Finset.sum_congr rfl
        intro l _
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 144) := ENNReal.ofReal_le_ofReal sum_failR
    _ = (2 ^ 144 : ℝ≥0∞)⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]


open CapFailBound in
/-- **Cap failure is negligible**: under uniformly random labels, some multi-trial position exhausts its nonce cap
with probability at most `2^-142` (top and lower ground positions `≤ 2 · 2^-144`, E8: FTS ground positions
`≤ 2^-145`). -/
theorem prob_capFail_le :
    Pr[CapFail | ($ᵗ Labels : ProbComp Labels)] ≤ (2 ^ 142 : ℝ≥0∞)⁻¹ := by
  have hsplit : CapFail = fun labels : Labels =>
      ∃ b ∈ (Finset.univ : Finset Bool), (if b then CapFailW labels else CapFailT labels) := by
    funext labels
    apply propext
    unfold CapFail
    constructor
    · rintro (h | h)
      · exact ⟨false, Finset.mem_univ _, by simpa using h⟩
      · exact ⟨true, Finset.mem_univ _, by simpa using h⟩
    · rintro ⟨b, -, h⟩
      cases b
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
  rw [hsplit]
  refine (probEvent_exists_finset_le_sum (Finset.univ : Finset Bool) _ _).trans ?_
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]
  exact le_trans (add_le_add prob_capFailW_le prob_capFailT_le) three_quarters

#print axioms prob_capFail_le
end OuterCanonBase.Paired
