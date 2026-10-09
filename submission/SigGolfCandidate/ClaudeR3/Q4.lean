import SigGolfCandidate.ClaudeR3.P1
import SigGolfCandidate.ClaudeWCT.WCT9.Core

set_option maxRecDepth 200000

namespace ClaudeR3.Tab
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open ClaudeWCT.WCT9 (wordDigit routineCost routineCosts childExtra Child Rank)

def lev (b : Rank) : ℕ := routineCost b - 75

def keyU (u : Fin 6 → Fin 6) : ℕ := ∑ b : Rank, if (∀ j, wordDigit b j < u j) then 1024 ^ lev b else 0

set_option maxRecDepth 100000 in
theorem codeWords_eq' : ClaudeWCT.WCT9.codeWords = words := by decide +kernel

set_option maxRecDepth 100000 in
theorem levs_eq : levs = routineCosts.map (· - 75) := by decide +kernel

theorem levs_length : levs.length = 563 := by
  rw [levs_eq, List.length_map, ClaudeWCT.WCT9.routineCosts_length]

theorem words_length' : words.length = 563 := by
  rw [← codeWords_eq']; exact ClaudeWCT.WCT9.codeWords_length

theorem words_get (b : Rank) : words[b.val]'(by rw [words_length']; exact b.isLt) = List.ofFn (wordDigit b) := by
  have h := ClaudeWCT.WCT9.ofFn_wordDigit b
  rw [ClaudeWCT.WCT9.codeword_embed] at h
  rw [h]
  simp only [codeWords_eq']

theorem levs_get (b : Rank) : levs[b.val]'(by rw [levs_length]; exact b.isLt) = lev b := by
  simp only [levs_eq, List.getElem_map]
  rfl

theorem keyItems_eq : keyItems = List.ofFn (fun b : Rank => (List.ofFn (wordDigit b), 1024 ^ lev b)) := by
  apply List.ext_getElem
  · rw [keyItems, List.length_zipWith, words_length', levs_length, List.length_ofFn]; rfl
  · intro i h1 h2
    have hi : i < 563 := by rwa [List.length_ofFn] at h2
    rw [List.getElem_ofFn]
    simp only [keyItems, List.getElem_zipWith]
    rw [words_get ⟨i, hi⟩, levs_get ⟨i, hi⟩]

theorem lookup_keyT (u : Fin 6 → Fin 6) : lookup keyT (digitsOf u) = keyU u := by
  have hlen : ∀ p ∈ keyItems, p.1.length = 6 := by
    intro p hp
    rw [keyItems_eq, List.mem_ofFn] at hp
    obtain ⟨b, rfl⟩ := hp
    simp
  rw [keyT, lookupW 6 keyItems hlen _ (digitsOf_length u) (digitsOf_le u), wsum, keyItems_eq,
    List.map_ofFn, List.sum_ofFn, keyU]
  refine sum_congr rfl fun b _ => ?_
  exact if_congr (ltB_ofFn_iff _ u) rfl rfl

theorem ofFn_wordDigit_list' : List.ofFn (fun b : Rank => List.ofFn (wordDigit b)) = words := by
  apply List.ext_getElem
  · rw [List.length_ofFn, words_length']
  · intro i h1 h2
    have hi : i < 563 := by rwa [List.length_ofFn] at h1
    rw [List.getElem_ofFn, ← words_get ⟨i, hi⟩]

theorem wordsOf_wordDigit' : WordsOf wordDigit := by
  unfold WordsOf
  rw [Fin.univ_val_map, ofFn_wordDigit_list']

theorem wordDigit_le4 (b : Rank) (j : Fin 6) : wordDigit b j ≤ 4 := ClaudeWCT.WCT9.wordDigit_le_four b j

def digit (k l : ℕ) : ℕ := k / 1024 ^ l % 1024

noncomputable def rhoU (u : Fin 6 → Fin 6) : ℕ[X] := ∑ b : Rank, if (∀ j, wordDigit b j < u j) then X ^ lev b else 0

theorem rhoU_eval (u : Fin 6 → Fin 6) : (rhoU u).eval 1024 = keyU u := by
  simp [rhoU, keyU, eval_finsetSum, apply_ite]

theorem rhoU_eval_one (u : Fin 6 → Fin 6) : (rhoU u).eval 1 = #{b : Rank | ∀ j, wordDigit b j < u j} := by
  simp [rhoU, eval_finsetSum, apply_ite, Finset.sum_boole]

theorem lev_le (b : Rank) : lev b ≤ 14 := by
  have := (ClaudeWCT.WCT9.routineCost_bounds b).2
  unfold lev; omega

theorem rhoU_coeff_lt (u : Fin 6 → Fin 6) (i : ℕ) : (rhoU u).coeff i < 1024 := by
  refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
  rw [rhoU_eval_one]
  have := card_le_univ (filter (fun b : Rank => ∀ j, wordDigit b j < u j) univ)
  simp only [Fintype.card_fin] at this
  omega

theorem rhoU_natDegree (u : Fin 6 → Fin 6) : (rhoU u).natDegree ≤ 14 := by
  unfold rhoU
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  split_ifs
  · rw [natDegree_X_pow]; exact lev_le b
  · simp

theorem rhoU_eq_digits (u : Fin 6 → Fin 6) :
    rhoU u = ∑ l ∈ range 15, C (digit (keyU u) l) * X ^ l := by
  conv_lhs => rw [as_sum_range' (rhoU u) 15 (by have := rhoU_natDegree u; omega)]
  refine sum_congr rfl fun l _ => ?_
  rw [digit, ← rhoU_eval, ClaudeWCT.Numerics.eval_div_pow_mod (by norm_num) l _ (rhoU_coeff_lt u),
    C_mul_X_pow_eq_monomial]

def extCount (e : ℕ) : ℕ := #{c : Child | childExtra c = e}

theorem extCount_vals : extCount 0 = 2 ∧ extCount 1 = 72 ∧ extCount 2 = 52 ∧ extCount 3 = 2 := by
  unfold extCount; decide

theorem childExtra_le (c : Child) : childExtra c ≤ 3 := by
  unfold childExtra ClaudeWCT.WCT9.maxChildSave; omega

theorem sum_child {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ c : Child, f (childExtra c) = ∑ e ∈ range 4, extCount e • f e := by
  rw [← sum_fiberwise_of_maps_to (g := childExtra) (t := range 4)
    (fun c _ => mem_range.mpr (by have := childExtra_le c; omega))]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_congr rfl fun c hc => by rw [(mem_filter.mp hc).2], sum_const]
  rfl

end ClaudeR3.Tab
