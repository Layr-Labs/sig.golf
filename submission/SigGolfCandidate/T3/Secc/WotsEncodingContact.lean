import SigGolfCandidate.T3.Secc.WotsEncodingMarker
import SigGolfCandidate.T3.Secc.WotsContacts
import SigGolfCandidate.T3.Secc.WotsTransportCount

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
def ContactFirstAt (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, ContactAt T (trace.take k) a ∧ ¬MarkerAt T (trace.take k) a ∧ MarkerAt T trace a
def CFK (T : Answers) (trace : List Entry) : Prop :=
  ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain (chainAt p) ∧ ContactFirstAt T trace (chainAt p)
noncomputable def contacts (T : Answers) (trace : List Entry) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ ContactAt T trace (chainAt p)).card
theorem contacts_mono (T : Answers) {trace trace' : List Entry} (hsub : ∀ e ∈ trace, e ∈ trace') :
    contacts T trace ≤ contacts T trace' := by
  unfold contacts
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, WotsExtract.contactAt_mono hp.2 hsub⟩
noncomputable def costL (T : Answers) (F : Set EncIndex) : List Entry → List Entry → Nat
  | _, [] => 0
  | hist, e :: rest =>
      (if Lazy.IsCell encInput F e.1 then 57 * contacts T hist else 0) + costL T F (hist ++ [e]) rest
theorem costL_le (T : Answers) (F : Set EncIndex) :
    ∀ (trace hist : List Entry), costL T F hist trace ≤ 57 * trace.length * contacts T (hist ++ trace) := by
  intro trace
  induction trace with
  | nil => intro hist; simp [costL]
  | cons e rest ih =>
      intro hist
      unfold costL
      have h1 : contacts T hist ≤ contacts T (hist ++ e :: rest) :=
        contacts_mono T (fun x hx => List.mem_append_left _ hx)
      have h2 := ih (hist ++ [e])
      rw [List.append_assoc, List.singleton_append] at h2
      have h3 : (if Lazy.IsCell encInput F e.1 then 57 * contacts T hist else 0) ≤ 57 * contacts T hist := by
        split_ifs <;> omega
      rw [List.length_cons]
      nlinarith
theorem cfk_new {T : Answers} {h : List Entry} {e : Entry} (hold : ¬ CFK T h) (hnew : CFK T (h ++ [e])) :
    ∃ p : CanonGraph.LeafPos × Fin 58, WotsExtract.SourceChain (chainAt p) ∧ ContactAt T h (chainAt p) ∧
      MarkEntry T (chainAt p) e ∧ ¬ MarkerAt T h (chainAt p) := by
  obtain ⟨p, hs, k, hc, hnm, hm⟩ := hnew
  by_cases hk : k ≤ h.length
  · rw [List.take_append_of_le_length hk] at hc hnm
    have hnot : ¬ MarkerAt T h (chainAt p) := fun hmh => hold ⟨p, hs, k, hc, hnm, hmh⟩
    refine ⟨p, hs, WotsExtract.contactAt_mono hc (fun x hx => List.mem_of_mem_take hx), ?_, hnot⟩
    obtain ⟨entry, hmem, hme⟩ := (markerAt_iff T _ _).mp hm
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact absurd ((markerAt_iff T _ _).mpr ⟨entry, hmem, hme⟩) hnot
    · exact hme
  · rw [List.take_of_length_le (by rw [List.length_append, List.length_singleton]; omega)] at hnm
    exact absurd hm hnm
noncomputable def cfCharge (T : Answers) (F : Set EncIndex) (h : FreeMonoid Entry) : RefWorld.Domain → Nat
  | .inl (.inr x) => if Lazy.IsCell encInput F x then 57 * contacts T h.toList else 0
  | _ => 0
theorem costL_step (T : Answers) (F : Set EncIndex) (h : FreeMonoid Entry) (input : RefWorld.Domain)
    (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    costL T F h.toList (Lazy.obs input answer * tail).toList =
      cfCharge T F h input + costL T F (h * Lazy.obs input answer).toList tail.toList := by
  rcases input with (n | x) | u
  · simp [Lazy.obs, cfCharge]
  · simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, costL, cfCharge]
  · simp [Lazy.obs, cfCharge]
theorem cfk_nil (T : Answers) : ¬ CFK T [] := by
  rintro ⟨p, -, k, -, -, hm⟩
  obtain ⟨entry, hmem, -⟩ := (markerAt_iff T _ _).mp hm
  simp at hmem
theorem indicator_le_one (P : Prop) [Decidable P] : (if P then (1 : ENNReal) else 0) ≤ 1 := by
  split_ifs <;> simp
section Step
variable [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
theorem cf_step (T : Answers) (F : Set EncIndex) (init : F → Finset HashOutput)
    (hcell : ∀ (e : F) (p : CanonGraph.LeafPos × Fin 58),
      Pr[fun ans => MarkEntry T (chainAt p) (encInput e.val, ans) | cell (init e)] ≤ 57 / (2 : ENNReal) ^ 128)
    (hother : ∀ x, ¬ Lazy.IsCell encInput F x → ∀ p,
      ¬ (WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (x, T (.inl (.inr x)))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Lazy.Consistent encInput F init h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (Lazy.lazyImpl encInput F T input).run allowed] *
        (if CFK T (h * Lazy.obs input result.1).toList then (1 : ENNReal) else 0) ≤
      (if CFK T h.toList then (1 : ENNReal) else 0) + (2 ^ 128 : ENNReal)⁻¹ * (cfCharge T F h input : ENNReal) := by
  classical
  by_cases hold : CFK T h.toList
  · rw [if_pos hold]
    refine le_trans ?_ le_self_add
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl (indicator_le_one _)).trans ?_
    exact Lazy.tsum_probOutput_mul_le_self _ _
  rw [if_neg hold, zero_add]
  rcases input with (n | x) | u
  · rw [Lazy.lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
  · by_cases hx : Lazy.IsCell encInput F x
    · rw [Lazy.lazyImpl_cell encInput F T x hx, tsum_probOutput_map_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, cfCharge, if_pos hx]
      set e₀ := Lazy.cellOf encInput F x hx with he₀
      have hx₀ : encInput e₀.val = x := Lazy.cellOf_input encInput F x hx
      by_cases hq : ∃ ans₀, (encInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        refine le_trans (le_of_eq ?_) zero_le
        apply ENNReal.tsum_eq_zero.mpr
        intro ans
        by_cases hne : ans = ans₀
        · subst hne
          rw [if_neg, mul_zero]
          intro hnew
          obtain ⟨p, -, -, hme, hnm⟩ := cfk_new hold hnew
          rw [← hx₀] at hme
          exact hnm ((markerAt_iff T _ _).mpr ⟨_, hans₀, hme⟩)
        · rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne), zero_mul]
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        let S := Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
          WotsExtract.SourceChain (chainAt p) ∧ ContactAt T h.toList (chainAt p)
        calc _ = Pr[fun ans => CFK T (h.toList ++ [(x, ans)]) | cell (init e₀)] := by
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun ans => ?_
              split_ifs <;> simp
          _ ≤ Pr[fun ans => ∃ p ∈ S, MarkEntry T (chainAt p) (x, ans) | cell (init e₀)] := by
              apply probEvent_mono
              intro ans _ hnew
              obtain ⟨p, hs, hcon, hme, -⟩ := cfk_new hold hnew
              refine ⟨p, ?_, hme⟩
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hs, hcon⟩
          _ ≤ ∑ p ∈ S, Pr[fun ans => MarkEntry T (chainAt p) (x, ans) | cell (init e₀)] :=
              probEvent_exists_finset_le_sum S _ _
          _ ≤ ∑ p ∈ S, 57 / (2 : ENNReal) ^ 128 := by
              refine Finset.sum_le_sum fun p _ => ?_
              rw [← hx₀]
              exact hcell e₀ p
          _ = (2 ^ 128 : ENNReal)⁻¹ * ((57 * contacts T h.toList : Nat) : ENNReal) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              unfold contacts
              push_cast
              rw [div_eq_mul_inv]
              ring
    · rw [Lazy.lazyImpl_other encInput F T x hx, tsum_probOutput_pure_mul]
      simp only [Lazy.obs, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      rw [if_neg]
      · exact zero_le
      · intro hnew
        obtain ⟨p, hs, -, hme, -⟩ := cfk_new hold hnew
        exact hother x hx p ⟨hs, hme⟩
  · rw [Lazy.lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [Lazy.obs, mul_one, if_neg hold, mul_zero, tsum_zero]
    exact zero_le
end Step
noncomputable def cfInd (s : RefSample) : ENNReal := if CFK s.answers s.trace then 1 else 0
noncomputable def cfCost (s : RefSample) : ENNReal := ((57 * s.trace.length * contacts s.answers s.trace : Nat) : ENNReal)
theorem chainAt_injective : Function.Injective chainAt := by
  rintro ⟨⟨lay, tree, leaf⟩, i⟩ ⟨⟨lay', tree', leaf'⟩, i'⟩ h
  simp only [chainAt, leafOf, ChainAddr.mk.injEq, LeafAddr.mk.injEq] at h
  obtain ⟨⟨rfl, ht, hl⟩, hi⟩ := h
  have : tree = tree' := Fin.ext ht
  have : leaf = leaf' := Fin.ext hl
  have : i = i' := Fin.ext hi
  subst tree leaf i
  rfl
theorem exists_chainAt {a : ChainAddr} (ha : WotsExtract.SourceChain a) : ∃ p, chainAt p = a := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 4096 :=
    (Nat.pow_le_pow_right (by norm_num) (Extract.height_le a.key.lay)).trans (by norm_num)
  have hcc := Mask.chainCount_le a.key.lay
  exact ⟨⟨⟨a.key.lay, ⟨a.key.tree, ht⟩, ⟨a.key.leaf, by omega⟩⟩, ⟨a.chain, by omega⟩⟩, rfl⟩
theorem contacts_eq_contactCount (s : RefSample) : contacts s.answers s.trace = contactCount s := by
  unfold contacts contactCount
  apply Finset.card_bij (fun p _ => chainAt p)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Finset.mem_filter, mem_sourceChains]
    exact hp
  · intro p _ p' _ h
    exact chainAt_injective h
  · intro a ha
    rw [Finset.mem_filter, mem_sourceChains] at ha
    obtain ⟨p, rfl⟩ := exists_chainAt ha.1
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha
theorem cfCost_le (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * cfCost s ≤
      ((57 * q : Nat) : ENNReal) * ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : referenceExperiment adversary q s = 0
  · simp [hs]
  · have hlen := reference_trace_length adversary q s ((PMF.mem_support_iff _ _).mpr hs)
    rw [mul_left_comm]
    refine mul_le_mul' le_rfl ?_
    unfold cfCost
    rw [contacts_eq_contactCount]
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlen)
end Enc
end SigGolfCandidate.T3.Security.Wots
