import SigGolfCandidate.ClaudeWCT_Bank_WCTHonest
import SigGolfCandidate.ClaudeWCT_Numerics_N600Cover
import SigGolfCandidate.ClaudeWCT_Numerics_N600Price
import SigGolfCandidate.ClaudeWCT_Bank_WCTAccept
set_option Elab.async false

namespace ClaudeWCT.Numerics.WCTEnvelope
open Finset ENNReal
open ClaudeWCT.Numerics.Thinning (env ListCov)
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Bank.WCT (WProposal proposal outIdx CoveredP scoreP price)
open ClaudeWCT.WCT9 (wordDigit Coord Child Rank)
theorem codeWords_eq : ClaudeWCT.WCT9.codeWords = N600.words := by decide +kernel
set_option maxRecDepth 100000 in
theorem ofFn_wordDigit_list :
    List.ofFn (fun r : Fin 563 => List.ofFn (wordDigit r)) = N600.words := by
  rw [← codeWords_eq]
  apply List.ext_getElem
  · exact (List.length_ofFn).trans ClaudeWCT.WCT9.codeWords_length.symm
  · intro i hi hj
    have hi' : i < 563 := by rwa [List.length_ofFn] at hi
    rw [List.getElem_ofFn]
    have h := ClaudeWCT.WCT9.ofFn_wordDigit ⟨i, hi'⟩
    rw [ClaudeWCT.WCT9.codeword_embed] at h
    exact h
theorem wordsOf_wordDigit : N600.WordsOf wordDigit := by
  unfold N600.WordsOf
  rw [Fin.univ_val_map, ofFn_wordDigit_list]
theorem w1Table_wordDigit : N600.W1Table wordDigit :=
  fun p => N600.w1_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four p
theorem w2Table_wordDigit : N600.W2Table wordDigit :=
  fun p => N600.w2_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four p
theorem wfTable_wordDigit (i : Fin 6) : N600.WFTable wordDigit i :=
  fun p => N600.wf_table wordsOf_wordDigit ClaudeWCT.WCT9.wordDigit_le_four i p
theorem card_rank : Fintype.card Rank = 563 := Fintype.card_fin 563
theorem card_child : Fintype.card Child = 128 := Fintype.card_fin 128
abbrev Coords := Coord → Child × Rank
theorem card_coords : Fintype.card Coords = N600.Q ^ 9 :=
  N600.card_table card_rank card_child
theorem mem_atIndex {α β : Type} [DecidableEq α] (index : α) (e : β) (W : List (α × β)) :
    e ∈ atIndex index W ↔ (index, e) ∈ W := by
  unfold atIndex
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨i, e'⟩, hmem, h⟩
    by_cases hi : i = index
    · simp only [hi, if_true, Option.some.injEq] at h
      rw [← hi, ← h]
      exact hmem
    · simp [hi] at h
  · intro h
    exact ⟨(index, e), h, by simp⟩
theorem coveredP_iff (W : List WProposal) (N : SigGolfCandidate.T3.HashOutput) :
    CoveredP W N ↔ ListCov wordDigit (atIndex (outIdx N) W) (proposal N).2 := by
  unfold CoveredP ClaudeWCT.Bank.WCT.SlotCoveredP ListCov
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p.2, (mem_atIndex _ _ _).mpr ?_, h2, h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨e, he, h2, h3⟩
    exact ⟨(outIdx N, e), (mem_atIndex _ _ _).mp he, rfl, h2, h3⟩
theorem price_scale :
    (2 : ENNReal) ^ 128 * ((1353 * 2 ^ 58 : ℕ) : ENNReal) * ((N600.Q ^ 9 : ℕ) : ENNReal) *
        ((2 ^ 256 : ℕ) : ENNReal)⁻¹ = N600.priceScale := by
  rw [← div_eq_mul_inv]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by unfold N600.priceScale; finiteness)).mp
  unfold N600.priceScale
  norm_num [N600.Q, ENNReal.toReal_mul, ENNReal.toReal_div]
theorem price_eq (W : List WProposal) : price W = N600.priceN wordDigit W := by
  classical
  set g : WProposal → ENNReal := fun p => if ListCov wordDigit (atIndex p.1 W) p.2 then 1 else 0 with hg
  have hs : ∀ N, scoreP W N = if ClaudeWCT.WCT9.admissible N = true then g (proposal N) else 0 := by
    intro N
    unfold scoreP
    by_cases hadm : ClaudeWCT.WCT9.admissible N = true
    · simp only [hadm, true_and, if_true, hg]
      exact if_congr (coveredP_iff W N) rfl rfl
    · simp [hadm]
  have hsum : ∑ p, g p = ((N600.Q ^ 9 : ℕ) : ENNReal) *
      ∑ index : Fin (2 ^ 31), env (n := 9) wordDigit (atIndex index W) := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun index _ => ?_
    unfold env finiteAverage
    rw [card_coords, ENNReal.mul_div_cancel (by simp [N600.Q]) (by simp)]
  unfold price SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [ClaudeWCT.Bank.WCT.sum_admissible g, hsum, Fintype.card_bitVec, N600.priceN, ← price_scale]
  unfold ClaudeWCT.WCT9.gateLimit
  simp only [div_eq_mul_inv]
  ring
end ClaudeWCT.Numerics.WCTEnvelope

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
abbrev PairChoice (β : Type) := Fin 2 × (Fin 64 × β) × (Fin 64 × β)
abbrev ForestChoice (β : Type) := (Fin 4 → PairChoice β) × (Fin 128 × β)

def choice {β : Type} (a : AlphabetOf β) : ForestChoice β :=
  (fun p => ((a.1.1 p).1,
    ((a.1.1 p).2.1,a.2 ⟨2*p.val,by omega⟩),
    ((a.1.1 p).2.2,a.2 ⟨2*p.val+1,by omega⟩)),(a.1.2,a.2 8))
def unchoice {β : Type} (a : ForestChoice β) : AlphabetOf β :=
  ((fun p => ((a.1 p).1,(a.1 p).2.1.1,(a.1 p).2.2.1),a.2.1),
    fun k => if hk : k.val<8 then
      if k.val%2=0 then (a.1 ⟨k.val/2,by omega⟩).2.1.2
      else (a.1 ⟨k.val/2,by omega⟩).2.2.2
    else a.2.2)
def choiceEquiv (β : Type) : AlphabetOf β ≃ ForestChoice β where
  toFun := choice
  invFun := unchoice
  left_inv a := by
    apply Prod.ext
    · rfl
    · funext k; fin_cases k <;> rfl
  right_inv a := by
    apply Prod.ext
    · funext p
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · apply Prod.ext
          · rfl
          · fin_cases p <;> rfl
        · apply Prod.ext
          · rfl
          · fin_cases p <;> rfl
    · rfl

theorem covAt_splitRanks {β : Type} [Fintype β] {r : Nat}
    (val : β → Fin 6 → Nat) (o : Fin r → Fin 2) (A : Fin r → Fin 64 × β)
    (s : Fin 2) (target : Fin 64 × β) :
    CovAt val target.1 (val target.2) (splitRanks o A s) ↔
      ∀ t, ∃ j, o j=s ∧ (A j).1=target.1 ∧ val target.2 t ≤ val (A j).2 t := by
  constructor
  · intro h t
    obtain ⟨j,hj,hv⟩ := h t
    let z := (fiberIndex o s).symm j
    exact ⟨z.val,z.property,by simpa only [splitRanks_apply] using hj,
      by simpa only [splitRanks_apply] using hv⟩
  · intro h t
    obtain ⟨j,hj,hc,hv⟩ := h t
    refine ⟨fiberIndex o s ⟨j,hj⟩,?_,?_⟩
    · simpa only [splitRanks_apply, Equiv.symm_apply_apply] using hc
    · simpa only [splitRanks_apply, Equiv.symm_apply_apply] using hv

def PairCovered {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) (a : PairChoice β) : Prop :=
  CovAt val a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
  CovAt val a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)
def ForestCovered {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) (a : ForestChoice β) : Prop :=
  (∀ p, PairCovered val (h.1 p) (a.1 p)) ∧ CovAt val a.2.1 (val a.2.2) h.2

theorem card_and_prod {α β : Type} [Fintype α] [Fintype β] (p : α → Prop) (q : β → Prop) :
    #{a : α × β | p a.1 ∧ q a.2} = #{a : α | p a} * #{b : β | q b} := by
  classical
  simp only [card_filter, Fintype.sum_prod_type]
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hp : p a <;> by_cases hq : q b <;> simp [hp,hq]

noncomputable def pairCoveredEquiv {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) :
    {a : PairChoice β // PairCovered val h a} ≃
      (s : Fin 2) × {a : Fin 64 × β // CovAt val a.1 (val a.2) (splitRanks h.1 h.2.1 s)} ×
        {b : Fin 64 × β // CovAt val b.1 (val b.2) (splitRanks h.1 h.2.2 s)} where
  toFun a := ⟨a.val.1, ⟨a.val.2.1,a.property.1⟩,⟨a.val.2.2,a.property.2⟩⟩
  invFun a := ⟨(a.1,a.2.1.val,a.2.2.val),a.2.1.property,a.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem pairCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) : #{a : PairChoice β | PairCovered val h a} = pairCoverage val h := by
  have he := Fintype.card_congr (pairCoveredEquiv val h)
  simp only [Fintype.card_subtype,Fintype.card_sigma,Fintype.card_prod] at he
  calc
    _ = ∑ s : Fin 2, coordinateCoverage val (splitRanks h.1 h.2.1 s) *
      coordinateCoverage val (splitRanks h.1 h.2.2 s) := he
    _ = _ := by rw [Fin.sum_univ_two]; rfl

noncomputable def forestCoveredEquiv {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) :
    {a : ForestChoice β // ForestCovered val h a} ≃
      ((p : Fin 4) → {a : PairChoice β // PairCovered val (h.1 p) a}) ×
        {b : Fin 128 × β // CovAt val b.1 (val b.2) h.2} where
  toFun a := (fun p => ⟨a.val.1 p,a.property.1 p⟩,⟨a.val.2,a.property.2⟩)
  invFun a := ⟨(fun p => (a.1 p).val,a.2.val),(fun p => (a.1 p).property),a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem forestCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) : #{a : ForestChoice β | ForestCovered val h a} = forestCoverage val h := by
  have he := Fintype.card_congr (forestCoveredEquiv val h)
  simp only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_pi] at he
  calc
    _ = (∏ p, #{a : PairChoice β | PairCovered val (h.1 p) a}) * coordinateCoverage val h.2 := he
    _ = _ := by simp only [pairCovered_card]; rfl

#print axioms covAt_splitRanks
#print axioms pairCovered_card
#print axioms forestCovered_card
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

theorem rawChild_first (s : Selectors) (p : Fin 4) :
    (rawChild s ⟨2*p.val,by omega⟩).val = 64*(s.1 p).1.val+(s.1 p).2.1.val := by
  fin_cases p <;> rfl

theorem rawChild_second (s : Selectors) (p : Fin 4) :
    (rawChild s ⟨2*p.val+1,by omega⟩).val = 2*(s.1 p).2.2.val+(s.1 p).1.val := by
  fin_cases p <;> rfl

theorem rawChild_first_eq (s u : Selectors) (p : Fin 4) :
    rawChild s ⟨2*p.val,by omega⟩ = rawChild u ⟨2*p.val,by omega⟩ ↔
      (s.1 p).1=(u.1 p).1 ∧ (s.1 p).2.1=(u.1 p).2.1 := by
  rw [Fin.ext_iff, rawChild_first, rawChild_first]
  have ha := (s.1 p).2.1.isLt
  have hb := (u.1 p).2.1.isLt
  simp only [Fin.ext_iff]
  omega

theorem rawChild_second_eq (s u : Selectors) (p : Fin 4) :
    rawChild s ⟨2*p.val+1,by omega⟩ = rawChild u ⟨2*p.val+1,by omega⟩ ↔
      (s.1 p).1=(u.1 p).1 ∧ (s.1 p).2.2=(u.1 p).2.2 := by
  rw [Fin.ext_iff, rawChild_second, rawChild_second]
  have ha := (s.1 p).1.isLt
  have hb := (u.1 p).1.isLt
  simp only [Fin.ext_iff]
  omega

def AlphabetCovered {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, ∃ j,
    rawChild (h j).1 k = rawChild a.1 k ∧ val (a.2 k) t ≤ val ((h j).2 k) t

theorem forestCovered_choice {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) :
    ForestCovered val (splitHistory h) (choice a) ↔ AlphabetCovered val h a := by
  have hfirst (p : Fin 4) :
      CovAt val ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ t : Fin 6, ∃ j, rawChild (h j).1 ⟨2*p.val,by omega⟩ = rawChild a.1 ⟨2*p.val,by omega⟩ ∧
        val (a.2 ⟨2*p.val,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val,by omega⟩) t := by
    rw [covAt_splitRanks]
    simp only [splitHistory, choice, rawChild_first_eq, and_assoc]
  have hsecond (p : Fin 4) :
      CovAt val ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ t : Fin 6, ∃ j, rawChild (h j).1 ⟨2*p.val+1,by omega⟩ = rawChild a.1 ⟨2*p.val+1,by omega⟩ ∧
        val (a.2 ⟨2*p.val+1,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val+1,by omega⟩) t := by
    rw [covAt_splitRanks]
    simp only [splitHistory, choice, rawChild_second_eq, and_assoc]
  constructor
  · rintro ⟨hp,hs⟩ k t
    have hA : ∀ p : Fin 4, ∃ j, rawChild (h j).1 ⟨2*p.val,by omega⟩ = rawChild a.1 ⟨2*p.val,by omega⟩ ∧
        val (a.2 ⟨2*p.val,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val,by omega⟩) t :=
      fun p => ((hfirst p).mp (hp p).1) t
    have hB : ∀ p : Fin 4, ∃ j, rawChild (h j).1 ⟨2*p.val+1,by omega⟩ = rawChild a.1 ⟨2*p.val+1,by omega⟩ ∧
        val (a.2 ⟨2*p.val+1,by omega⟩) t ≤ val ((h j).2 ⟨2*p.val+1,by omega⟩) t :=
      fun p => ((hsecond p).mp (hp p).2) t
    fin_cases k
    · exact hA 0
    · exact hB 0
    · exact hA 1
    · exact hB 1
    · exact hA 2
    · exact hB 2
    · exact hA 3
    · exact hB 3
    · exact hs t
  · intro hc
    refine ⟨fun p => ⟨(hfirst p).mpr ?_,(hsecond p).mpr ?_⟩,?_⟩
    · exact hc ⟨2*p.val,by omega⟩
    · exact hc ⟨2*p.val+1,by omega⟩
    · exact hc 8

theorem alphabetCovered_card {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    (Finset.univ.filter fun a => AlphabetCovered val h a).card = forestCoverage val (splitHistory h) := by
  classical
  have e := (choiceEquiv β).subtypeEquiv (fun a => (forestCovered_choice val h a).symm)
  have hc := Fintype.card_congr e
  simp only [Fintype.card_subtype] at hc
  exact hc.trans (forestCovered_card val (splitHistory h))

#print axioms forestCovered_choice
#print axioms alphabetCovered_card
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def ListAlphabetCovered {β : Type} (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, ∃ e ∈ W,
    rawChild e.1 k = rawChild a.1 k ∧ val (a.2 k) t ≤ val (e.2 k) t
noncomputable def bucketEnv {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) : ENNReal :=
  finiteAverage (fun a => if ListAlphabetCovered val W a then 1 else 0)

theorem listAlphabetCovered_ofFn {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) :
    ListAlphabetCovered val (List.ofFn h) a ↔ AlphabetCovered val h a := by
  simp only [ListAlphabetCovered, AlphabetCovered, List.mem_ofFn]
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨e, ⟨j,rfl⟩, he⟩
    exact ⟨j,he⟩
  · rintro ⟨j,hj⟩
    exact ⟨h j,⟨j,rfl⟩,hj⟩

theorem bucketEnv_ofFn {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    bucketEnv val (List.ofFn h) =
      (SharedCoverage.forestCoverage val (splitHistory h) : ENNReal)/Fintype.card (AlphabetOf β) := by
  unfold bucketEnv finiteAverage
  simp_rw [listAlphabetCovered_ofFn]
  rw [← natCast_card_filter, alphabetCovered_card]

theorem bucketEnv_mono {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (a : AlphabetOf β) (W : List (AlphabetOf β)) : bucketEnv val W ≤ bucketEnv val (a::W) := by
  unfold bucketEnv finiteAverage
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro target _
  split_ifs with h1 h2
  · exact le_rfl
  · apply False.elim
    apply h2
    intro k t
    obtain ⟨e,he,hc⟩ := h1 k t
    exact ⟨e,List.mem_cons_of_mem a he,hc⟩
  · exact zero_le_one
  · exact le_rfl

theorem coveredP_bucket (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput) :
    CoveredP W N ↔ ListAlphabetCovered ClaudeWCT.WCT9.wordDigit
      (atIndex (proposal N).1 W) (proposal N).2 := by
  unfold CoveredP SlotCoveredP ListAlphabetCovered
  refine forall_congr' fun k => forall_congr' fun t => ?_
  constructor
  · rintro ⟨p,hp,h1,h2,h3⟩
    refine ⟨p.2,(WCTEnvelope.mem_atIndex _ _ _).mpr ?_,h2,h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨a,ha,h2,h3⟩
    exact ⟨((proposal N).1,a),(WCTEnvelope.mem_atIndex _ _ _).mp ha,rfl,h2,h3⟩

theorem price_scale :
    (2:ENNReal)^128 * ((734*2^62:Nat):ENNReal) *
      (SharedMoments.alphabetSize:ENNReal) * ((2^256:Nat):ENNReal)⁻¹ =
      (SharedMoments.priceScaleTotal:ENNReal)/(2^31) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [SharedMoments.alphabetSize,SharedMoments.priceScaleTotal,ENNReal.toReal_mul,
    ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]

theorem price_eq_buckets (W : List Proposal) :
    price W = (SharedMoments.priceScaleTotal:ENNReal)/(2^31) *
      ∑ index : Fin (2^31), bucketEnv ClaudeWCT.WCT9.wordDigit (atIndex index W) := by
  let g : Proposal → ENNReal := fun p =>
    if ListAlphabetCovered ClaudeWCT.WCT9.wordDigit (atIndex p.1 W) p.2 then 1 else 0
  have hs (N : SigGolfCandidate.T3.HashOutput) : scoreP W N =
      if admissible N=true then g (proposal N) else 0 := by
    unfold scoreP
    by_cases ha : admissible N=true
    · simp only [ha,true_and,if_true,g]
      exact if_congr (coveredP_bucket W N) rfl rfl
    · simp [ha]
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hsum : (∑ p,g p) = (SharedMoments.alphabetSize:ENNReal)*
      ∑ index : Fin (2^31), bucketEnv ClaudeWCT.WCT9.wordDigit (atIndex index W) := by
    rw [Fintype.sum_prod_type,mul_sum]
    apply sum_congr rfl
    intro index _
    unfold bucketEnv finiteAverage
    rw [hc,ENNReal.mul_div_cancel (by norm_num [SharedMoments.alphabetSize]) (by simp)]
  unfold price SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [sum_admissible g,hsum,Fintype.card_bitVec,← price_scale]
  simp only [div_eq_mul_inv]
  ring

#print axioms bucketEnv_ofFn
#print axioms price_eq_buckets
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfCandidate.T3.BPORS.History (atIndex)
open SphincsSecurity.Concrete (binomialAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

/-- The actual cap-conditioned bucket law is bounded by the finite paired
history model, for any nonnegative payoff, including capped MGF and residual. -/
theorem law_bucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg honestCoordLaw r (fun W => f (bucketEnv ClaudeWCT.WCT9.wordDigit W)) ≤
      kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal)/
          SharedMoments.alphabetSize))/(SharedMoments.alphabetSize:ENNReal)^r) := by
  have hc : Fintype.card (AlphabetOf (Fin 563)) = SharedMoments.alphabetSize :=
    alphabet_card (Fintype.card_fin 563)
  have hf (h : Fin r → Alphabet) :
      f (bucketEnv ClaudeWCT.WCT9.wordDigit (List.ofFn h)) =
        f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h) : ENNReal)/
          SharedMoments.alphabetSize) :=
    congrArg f ((bucketEnv_ofFn ClaudeWCT.WCT9.wordDigit h).trans
      (congrArg (fun n : Nat =>
        (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h) : ENNReal)/(n:ENNReal)) hc))
  exact law_history_le r (fun W => f (bucketEnv ClaudeWCT.WCT9.wordDigit W))
    (fun h => f ((SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h : ENNReal)/
      SharedMoments.alphabetSize)) hf


end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def priceBucket (W : List Alphabet) : ENNReal :=
  (SharedMoments.priceScaleTotal : ENNReal)/(2^31) * bucketEnv ClaudeWCT.WCT9.wordDigit W

theorem price_eq_sum (W : List Proposal) :
    price W = ∑ index : Fin (2^31), priceBucket (atIndex index W) := by
  rw [price_eq_buckets]
  exact Finset.mul_sum ..

theorem bucketEnv_sublist {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {W V : List (AlphabetOf β)} (hWV : ∀ x ∈ W, x ∈ V) : bucketEnv val W ≤ bucketEnv val V := by
  unfold bucketEnv SigGolfResearch.Gate6.Moments.finiteAverage
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro target _
  split_ifs with hW hV
  · exact le_rfl
  · apply False.elim
    apply hV
    intro k t
    obtain ⟨e,he,hc⟩ := hW k t
    exact ⟨e,hWV e he,hc⟩
  · exact zero_le_one
  · exact le_rfl

theorem priceBucket_insert (L R : List Alphabet) (a : Alphabet) :
    priceBucket (L++R) ≤ priceBucket (L++a::R) := by
  apply mul_le_mul' le_rfl
  apply bucketEnv_sublist
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (List.mem_cons_of_mem a hx)

/-- The actual paired price has the marked-index bank excess bound once its
single-bucket capped exponential and residual moments have been certified. -/
theorem price_excess_of_bucket_bounds (T : Nat) (cap : ENNReal) (hcap : cap ≠ ⊤)
    (theta slope bound residualBound resultBound : ℝ)
    (htheta : 0 ≤ theta) (hslope : 0 < slope) (hbound : 0 ≤ bound) (hresBound : 0 ≤ residualBound)
    (hmgf : (2^31:ENNReal) * Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun L => ENNReal.ofReal (Real.exp (slope*(min (priceBucket L) cap).toReal))-1) ≤
        ENNReal.ofReal bound)
    (hres : (2^31:ENNReal) * Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun L => priceBucket L-cap) ≤ ENNReal.ofReal residualBound)
    (hscalar : (3/(8*slope))*Real.exp (bound-slope*theta)+residualBound ≤ resultBound) :
    Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta) ≤ ENNReal.ofReal resultBound := by
  have hm : (∑ _i : Fin (2^31), Law.coordAverage (Fintype.card (Fin (2^31)):ENNReal)⁻¹
      honestCoordLaw T
      (fun L => ENNReal.ofReal (Real.exp (slope*(min (priceBucket L) cap).toReal))-1)) ≤
        ENNReal.ofReal bound := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_pow,Nat.cast_ofNat] using hmgf
  have hr : (∑ _i : Fin (2^31), Law.coordAverage (Fintype.card (Fin (2^31)):ENNReal)⁻¹
      honestCoordLaw T (fun L => priceBucket L-cap)) ≤ ENNReal.ofReal residualBound := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_pow,Nat.cast_ofNat] using hres
  have he : (fun W : List Proposal => price W-ENNReal.ofReal theta) =
      (fun W => (∑ i : Fin (2^31), priceBucket (atIndex i W))-ENNReal.ofReal theta) := by
    funext W
    rw [price_eq_sum]
  rw [he]
  exact SharedPathWinsor.law_bucket_excess_general honestCoordLaw honestCoordLaw_sum T
    priceBucket cap hcap theta slope bound residualBound resultBound htheta hslope hbound hresBound
    (fun L a R => priceBucket_insert L R a) hm hr hscalar

#print axioms price_eq_sum
#print axioms priceBucket_insert
#print axioms price_excess_of_bucket_bounds
end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal
 theorem normalize_row_arithmetic (a S M D κ fee : ENNReal) (r : Nat)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hS0 : S ≠ 0) (hSt : S ≠ ⊤)
    (hM0 : M ≠ 0) (hMt : M ≠ ⊤) (hD0 : D ≠ 0) (hDt : D ≠ ⊤) :
    (κ^r*((a/S)*fee)/D^r)/(M*a*D/S) = κ^r*fee/(M*D^(r+1)) := by
  have hMD : (M*D^r*D)⁻¹ = M⁻¹*(D^r)⁻¹*D⁻¹ := by
    rw [ENNReal.mul_inv (Or.inr hDt) (Or.inr hD0),
      ENNReal.mul_inv (Or.inl hM0) (Or.inl hMt)]
  have hMAD : (M*a*D*S⁻¹)⁻¹ = M⁻¹*a⁻¹*D⁻¹*S := by
    rw [ENNReal.mul_inv (Or.inr (by simp [hS0])) (Or.inr (by simp [hSt])),
      ENNReal.mul_inv (Or.inr hDt) (Or.inr hD0),
      ENNReal.mul_inv (Or.inl hM0) (Or.inl hMt), inv_inv]
  simp only [div_eq_mul_inv, pow_succ]
  rw [hMAD, ← mul_assoc M (D^r) D, hMD]
  calc
    _ = κ^r*fee*M⁻¹*(D^r)⁻¹*D⁻¹*(a*a⁻¹)*(S*S⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel ha0 hat, ENNReal.mul_inv_cancel hS0 hSt]; ring

#print axioms normalize_row_arithmetic
end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] Finset.univ

noncomputable def feeCoefficient : ENNReal := 734/2^66

theorem price_coefficient :
    (SharedMoments.priceScaleTotal:ENNReal)/(2^31)/(SharedMoments.alphabetSize:ENNReal) = feeCoefficient := by
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold SharedMoments.alphabetSize; finiteness)
    (by unfold feeCoefficient; finiteness)).mp
  norm_num [SharedMoments.priceScaleTotal,SharedMoments.alphabetSize,feeCoefficient,
    ENNReal.toReal_div]

theorem priceBucket_ofFn {r : Nat} (h : Fin r → Alphabet) :
    priceBucket (List.ofFn h) = feeCoefficient *
      (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
  have hc : Fintype.card (AlphabetOf (Fin 563)) = SharedMoments.alphabetSize :=
    alphabet_card (Fintype.card_fin 563)
  have hb := (bucketEnv_ofFn ClaudeWCT.WCT9.wordDigit h).trans
    (congrArg (fun n : Nat =>
      (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal)/(n:ENNReal)) hc)
  change (SharedMoments.priceScaleTotal:ENNReal)/(2^31)*_ = _
  rw [hb, ← price_coefficient]
  simp only [div_eq_mul_inv]
  ring

theorem law_priceBucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg honestCoordLaw r (fun W => f (priceBucket W)) ≤
      kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r) :=
  law_history_le r (fun W => f (priceBucket W))
    (fun h => f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))
    (fun h => congrArg f (priceBucket_ofFn h))

theorem lawAvg_div {β : Type} [Fintype β] (v : β → ENNReal) (r : Nat)
    (f : List β → ENNReal) (C : ENNReal) :
    Law.lawAvg v r (fun W => f W/C) = Law.lawAvg v r f/C := by
  simpa only [div_eq_mul_inv,mul_comm] using Law.lawAvg_mul_left v r C⁻¹ f

theorem law_normalized_fee_row (r : Nat) (f : ENNReal → ENNReal)
    (S M fee : ENNReal) (hS0 : S ≠ 0) (hSt : S ≠ ⊤) (hM0 : M ≠ 0) (hMt : M ≠ ⊤)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/S*fee) :
    Law.lawAvg honestCoordLaw r
      (fun W => f (priceBucket W)/(M*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
        kappa^r*fee/(M*(SharedMoments.alphabetSize:ENNReal)^(r+1)) := by
  rw [lawAvg_div]
  calc
    _ ≤ (kappa^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r))/(M*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (law_priceBucket_payoff_le r f) _
    _ ≤ (kappa^r*((feeCoefficient/S)*fee)/(SharedMoments.alphabetSize:ENNReal)^r)/
        (M*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize kappa fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      hS0 hSt hM0 hMt (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

#print axioms priceBucket_ofFn
#print axioms law_priceBucket_payoff_le
#print axioms law_normalized_fee_row
end ClaudeWCT.Bank.Paired


namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem alphabet_power (r : Nat) :
    SharedMoments.alphabetSize^r * 16^r = SharedMoments.fieldSize^(9*r) := by
  rw [← mul_pow]
  have h : SharedMoments.alphabetSize*16=SharedMoments.fieldSize^9 := by
    norm_num [SharedMoments.alphabetSize,SharedMoments.fieldSize]
  rw [h,pow_mul]

 theorem normalized_denominator (r M fee : Nat) (hM : 0<M) (κ : ENNReal) :
    κ^r*(fee:ENNReal)/((M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1)) =
      κ^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  have hD : (0:ENNReal)<SharedMoments.alphabetSize := by norm_num [SharedMoments.alphabetSize]
  have hF : (0:ENNReal)<SharedMoments.fieldSize := by norm_num [SharedMoments.fieldSize]
  have hb0 : (M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hM.ne') (pow_ne_zero _ hD.ne')
  have hbt : (M:ENNReal)*(SharedMoments.alphabetSize:ENNReal)^(r+1) ≠ ⊤ := by finiteness
  have hd0 : ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.mul_pos hM (by decide +kernel : 0<SharedMoments.alphabetSize))
      (Nat.pow_pos (by decide +kernel : 0<SharedMoments.fieldSize))).ne'
  have hdt : ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_eq_div_iff hd0 hdt hb0 hbt).2
  simp only [Nat.cast_mul,Nat.cast_pow,pow_succ]
  have hp : (SharedMoments.fieldSize:ENNReal)^(9*r) =
      (SharedMoments.alphabetSize:ENNReal)^r*(16:ENNReal)^r := by
    exact_mod_cast (alphabet_power r).symm
  rw [hp]
  ring

 theorem law_normalized_fee_row_fields (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg honestCoordLaw r
      (fun W => f (priceBucket W)/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      kappa^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [← normalized_denominator r M fee hM kappa]
  exact law_normalized_fee_row r f S M fee (by positivity) (by finiteness)
    (by positivity) (by finiteness) hfee

 theorem law_normalized_le_one (r : Nat) (f : List Alphabet → ENNReal) (C : ENNReal)
    (hC0 : C ≠ 0) (hCt : C ≠ ⊤) (hbound : ∀ W, f W≤C) :
    Law.lawAvg honestCoordLaw r (fun W => f W/C) ≤ 1 := by
  calc
    _ ≤ Law.lawAvg honestCoordLaw r (fun _ => (1:ENNReal)) :=
      Law.lawAvg_mono honestCoordLaw r (fun W =>
        (ENNReal.div_le_div_right (hbound W) C).trans_eq (ENNReal.div_self hC0 hCt))
    _ = 1 := Law.lawAvg_const honestCoordLaw honestCoordLaw_sum r 1

 theorem coordAverage_div {β : Type} [Fintype β] (v : β → ENNReal) (T : Nat)
    (f : List β → ENNReal) (C p : ENNReal) :
    Law.coordAverage p v T (fun W => f W/C) = Law.coordAverage p v T f/C := by
  unfold Law.coordAverage
  simp_rw [lawAvg_div,div_eq_mul_inv]
  exact binomialAverage_mul_right p C⁻¹ T (fun r => Law.lawAvg v r f)

 theorem coordAverage_scaled {β : Type} [Fintype β] (v : β → ENNReal) (T : Nat)
    (f : List β → ENNReal) (C I p : ENNReal) (hC0 : C≠0) (hCt : C≠⊤) :
    (I*C)*Law.coordAverage p v T (fun W => f W/C) = I*Law.coordAverage p v T f := by
  rw [coordAverage_div]
  simp only [div_eq_mul_inv]
  calc
    _ = I*Law.coordAverage p v T f*(C*C⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hC0 hCt,mul_one]

#print axioms normalized_denominator
#print axioms law_normalized_fee_row_fields
#print axioms law_normalized_le_one
#print axioms coordAverage_scaled
end ClaudeWCT.Bank.Paired

/-! ## Binomial thinning (opus-kappa)

The honest cap-conditioned coordinate law satisfies `vA ≤ kappa·vU`. For every statistic that is monotone
under insertion of one letter, `coordAverage p vA T f ≤ coordAverage (kappa·p) vU T f`: the honest
`Bin(T,p)` stream of accepted letters is the accepted part of a `Bin(T,kappa·p)` stream of uniform letters.
This replaces the `kappa^r` tilt by the Poisson weight `e^(-2 kappa) (2 kappa)^r / r!`. -/
namespace ClaudeWCT.Numerics.Law
open ENNReal Finset

theorem coordAverage_thin {β : Type} [Fintype β] (p κ : ENNReal) (vA vU : β → ENNReal)
    (hA : ∑ b, vA b = 1) (hU : ∑ b, vU b = 1) (hdens : ∀ b, vA b ≤ κ * vU b)
    (hκ : 1 ≤ κ) (hκp : κ * p ≤ 1) (T : ℕ) (f : List β → ENNReal)
    (hf : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R)) :
    coordAverage p vA T f ≤ coordAverage (κ * p) vU T f := by
  have hp1 : p ≤ κ * p := le_mul_of_one_le_left' hκ
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (hp1.trans hκp)
  have hsumd : ∑ b, (κ * vU b - vA b) = κ - 1 := by
    have h : ∑ b, (κ * vU b - vA b) + ∑ b, vA b = κ := by
      rw [← sum_add_distrib]
      simp_rw [tsub_add_cancel_of_le (hdens _)]
      rw [← mul_sum, hU, mul_one]
    rw [hA] at h
    exact ENNReal.eq_sub_of_add_eq one_ne_top h
  have hsplit : 1 - p = (1 - κ * p) + p * (κ - 1) := by
    rw [ENNReal.mul_sub (fun _ _ => hpt), mul_one, mul_comm p κ]
    exact (tsub_add_tsub_cancel hκp hp1).symm
  induction T generalizing f with
  | zero => exact le_rfl
  | succ T ih =>
    rw [coordAverage_succ, coordAverage_succ]
    have hf' : ∀ b : β, ∀ L c R, f (b :: (L ++ R)) ≤ f (b :: (L ++ c :: R)) :=
      fun b L c R => by simpa using hf (b :: L) c R
    set X := coordAverage (κ * p) vU T f with hXdef
    set Y : β → ENNReal := fun b => coordAverage (κ * p) vU T (fun L => f (b :: L)) with hYdef
    have hXY : ∀ b, X ≤ Y b := fun b =>
      coordAverage_mono _ _ _ fun L => by simpa using hf [] b L
    have h1 : coordAverage p vA T f ≤ X := ih f hf
    have h2 : ∀ b, coordAverage p vA T (fun L => f (b :: L)) ≤ Y b :=
      fun b => ih _ (fun L c R => hf' b L c R)
    calc (1 - p) * coordAverage p vA T f + p * ∑ b, vA b * coordAverage p vA T (fun L => f (b :: L))
        ≤ (1 - p) * X + p * ∑ b, vA b * Y b :=
          add_le_add (mul_le_mul' le_rfl h1)
            (mul_le_mul' le_rfl (sum_le_sum fun b _ => mul_le_mul' le_rfl (h2 b)))
      _ = (1 - κ * p) * X + p * ∑ b, ((κ * vU b - vA b) * X + vA b * Y b) := by
          rw [sum_add_distrib, ← sum_mul, hsumd, hsplit]
          ring
      _ ≤ (1 - κ * p) * X + p * ∑ b, ((κ * vU b - vA b) * Y b + vA b * Y b) := by
          gcongr with b
          exact hXY b
      _ = (1 - κ * p) * X + κ * p * ∑ b, vU b * Y b := by
          congr 1
          simp_rw [← add_mul, tsub_add_cancel_of_le (hdens _)]
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun b _ => by ring

#print axioms coordAverage_thin
end ClaudeWCT.Numerics.Law

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

noncomputable def uniformCoordLaw (_ : Alphabet) : ENNReal := (Fintype.card Alphabet : ENNReal)⁻¹

theorem uniformCoordLaw_sum : ∑ a, uniformCoordLaw a = 1 := by
  simp only [uniformCoordLaw, sum_const, card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

theorem uniformCoordLaw_density (a : Alphabet) :
    uniformCoordLaw a ≤ 1 * (Fintype.card Alphabet : ENNReal)⁻¹ := by
  simp [uniformCoordLaw]

theorem kappa_mul_rate_le_one : kappa * (2^31 : ENNReal)⁻¹ ≤ 1 := by
  rw [kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc)
    (by simp)) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- The honest per-instance law is the thinning of the uniform law at rate `kappa * 2^-31`. -/
theorem coordAverage_honest_thin (T : ℕ) (f : List Alphabet → ENNReal)
    (hf : ∀ L b R, f (L ++ R) ≤ f (L ++ b :: R)) :
    Law.coordAverage (2^31 : ENNReal)⁻¹ honestCoordLaw T f ≤
      Law.coordAverage (kappa * (2^31 : ENNReal)⁻¹) uniformCoordLaw T f :=
  Law.coordAverage_thin _ _ _ _ honestCoordLaw_sum uniformCoordLaw_sum
    honestCoordLaw_density kappa_one_le kappa_mul_rate_le_one T f hf

theorem uniform_priceBucket_payoff_le (r : Nat) (f : ENNReal → ENNReal) :
    Law.lawAvg uniformCoordLaw r (fun W => f (priceBucket W)) ≤
      1^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r) := by
  have h := Law.lawAvg_le_uniform uniformCoordLaw 1 uniformCoordLaw_density r
    (fun W => f (priceBucket W))
  rw [uniform_history_average r (fun W => f (priceBucket W))
    (fun h => f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))
    (fun h => congrArg f (priceBucket_ofFn h))] at h
  have hc : Fintype.card Alphabet = SharedMoments.alphabetSize := alphabet_card rfl
  simpa only [hc] using h

theorem uniform_normalized_fee_row_fields (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal)
    (hfee : (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg uniformCoordLaw r
      (fun W => f (priceBucket W)/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      1^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [← normalized_denominator r M fee hM 1, lawAvg_div]
  calc
    _ ≤ (1^r * ((∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)))/
        (SharedMoments.alphabetSize:ENNReal)^r))/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (uniform_priceBucket_payoff_le r f) _
    _ ≤ (1^r*((feeCoefficient/(S:ENNReal))*(fee:ENNReal))/(SharedMoments.alphabetSize:ENNReal)^r)/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize 1 fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      (by positivity) (by finiteness) (by positivity) (by finiteness)
      (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

theorem uniform_normalized_le_one (r : Nat) (f : List Alphabet → ENNReal) (C : ENNReal)
    (hC0 : C ≠ 0) (hCt : C ≠ ⊤) (hbound : ∀ W, f W≤C) :
    Law.lawAvg uniformCoordLaw r (fun W => f W/C) ≤ 1 := by
  calc
    _ ≤ Law.lawAvg uniformCoordLaw r (fun _ => (1:ENNReal)) :=
      Law.lawAvg_mono uniformCoordLaw r (fun W =>
        (ENNReal.div_le_div_right (hbound W) C).trans_eq (ENNReal.div_self hC0 hCt))
    _ = 1 := Law.lawAvg_const uniformCoordLaw uniformCoordLaw_sum r 1

#print axioms coordAverage_honest_thin
#print axioms uniform_normalized_fee_row_fields
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem bucketEnv_le_one {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) : bucketEnv val W ≤ 1 := by
  classical
  unfold bucketEnv finiteAverage
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc
    _ ≤ ∑ _a : AlphabetOf β, (1:ENNReal) := Finset.sum_le_sum (fun a _ => by split_ifs <;> simp)
    _ = _ := by simp

 theorem fee_price_scale : feeCoefficient*(SharedMoments.alphabetSize:ENNReal) =
    (SharedMoments.priceScaleTotal:ENNReal)/(2^31) := by
  rw [← price_coefficient]
  exact ENNReal.div_mul_cancel (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

 theorem priceBucket_le (W : List Alphabet) :
    priceBucket W ≤ feeCoefficient*(SharedMoments.alphabetSize:ENNReal) := by
  rw [fee_price_scale]
  exact (mul_le_mul' le_rfl (bucketEnv_le_one ClaudeWCT.WCT9.wordDigit W)).trans_eq (mul_one _)

 theorem priceBucket_ne_top (W : List Alphabet) : priceBucket W ≠ ⊤ :=
  ne_top_of_le_ne_top (by unfold feeCoefficient; finiteness) (priceBucket_le W)

 noncomputable def cappedIncrement (x : ENNReal) : ENNReal :=
  ENNReal.ofReal (Real.exp (6*(min x ((6:ENNReal)/5)).toReal))-1
 noncomputable def cappedResidual (x : ENNReal) : ENNReal := x-(6:ENNReal)/5

 theorem cappedIncrement_real (x : ENNReal) (hx : x ≠ ⊤) :
    cappedIncrement x = ENNReal.ofReal (Real.exp (6*min x.toReal (6/5))-1) := by
  rw [cappedIncrement,ENNReal.toReal_min hx (by finiteness),ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat]
  rw [ENNReal.ofReal_sub _ (by norm_num),ENNReal.ofReal_one]

 theorem cappedResidual_real (x : ENNReal) (hx : x ≠ ⊤) :
    cappedResidual x = ENNReal.ofReal (max 0 (x.toReal-6/5)) := by
  rw [ENNReal.ofReal_max,ENNReal.ofReal_zero,max_eq_right (by positivity),
    ENNReal.ofReal_sub _ (by norm_num),ENNReal.ofReal_toReal hx]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<5)]
  norm_num [cappedResidual]

 theorem feeCoefficient_real : feeCoefficient.toReal = (734:ℝ)/2^66 := by
  norm_num [feeCoefficient,ENNReal.toReal_div]

 theorem cappedIncrement_nat (n : Nat) :
    cappedIncrement (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (Real.exp (6*min ((734:ℝ)/2^66*(n:ℝ)) (6/5))-1) := by
  rw [cappedIncrement_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_nat (n : Nat) :
    cappedResidual (feeCoefficient*(n:ENNReal)) =
      ENNReal.ofReal (max 0 ((734:ℝ)/2^66*(n:ℝ)-6/5)) := by
  rw [cappedResidual_real _ (by unfold feeCoefficient; finiteness),
    ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast]

 theorem cappedResidual_bound (W : List Alphabet) :
    cappedResidual (priceBucket W) ≤ feeCoefficient*SharedMoments.alphabetSize :=
  (tsub_le_self).trans (priceBucket_le W)

#print axioms bucketEnv_le_one
#print axioms priceBucket_le
#print axioms cappedIncrement_nat
#print axioms cappedResidual_nat
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem normalizer_scale (M S : Nat) :
    (2^31:ENNReal)*((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) =
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S := by
  have he : (2^31:ENNReal)*(feeCoefficient*SharedMoments.alphabetSize) =
      (SharedMoments.priceScaleTotal:ENNReal) := by
    rw [fee_price_scale]
    simp only [div_eq_mul_inv]
    calc
      _ = (SharedMoments.priceScaleTotal:ENNReal)*((2^31:ENNReal)*(2^31:ENNReal)⁻¹) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by finiteness),mul_one]
  simp only [div_eq_mul_inv,Nat.cast_mul]
  calc
    _ = (M:ENNReal)*((2^31:ENNReal)*(feeCoefficient*SharedMoments.alphabetSize))*(S:ENNReal)⁻¹ := by ring
    _ = _ := by rw [he]

 theorem uniform_coordAverage_bound_of_rows (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal) (fees : Nat → Nat) (bound : ENNReal)
    (hfees : ∀ r≤80, (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W, f (priceBucket W) ≤
      (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ g : Nat → ENNReal,
      (∀ r≤80, g r ≤ 1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → g r ≤ 1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T
      (fun W => f (priceBucket W)) ≤ bound := by
  let C : ENNReal := (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S
  have hC0 : C≠0 := by
    have hMc : (M:ENNReal) ≠ 0 := by exact_mod_cast hM.ne'
    have hfc : feeCoefficient ≠ 0 := by norm_num [feeCoefficient]
    have hDc : (SharedMoments.alphabetSize:ENNReal) ≠ 0 := by norm_num [SharedMoments.alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc, ENNReal.natCast_ne_top S⟩
  have hCt : C≠⊤ := by dsimp [C,feeCoefficient]; finiteness
  let g : Nat → ENNReal := fun r => Law.lawAvg uniformCoordLaw r (fun W => f (priceBucket W)/C)
  have hg := hcheck g (fun r hr => uniform_normalized_fee_row_fields r M S (fees r) hM hS f (hfees r hr))
    (fun r _ => uniform_normalized_le_one r (fun W => f (priceBucket W)) C hC0 hCt hpoint)
  calc
    _ = ((2^31:ENNReal)*C)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T
      (fun W => f (priceBucket W)/C) :=
      (coordAverage_scaled uniformCoordLaw T (fun W => f (priceBucket W)) C (2^31) _ hC0 hCt).symm
    _ = ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g := by
      rw [show (2^31:ENNReal)*C=((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S from normalizer_scale M S]
      rfl
    _ ≤ bound := hg

/-- Thinned row certificate for the honest law: any payoff `f` monotone in the bucket price is
bounded through `coordAverage_honest_thin` and the uniform rows (no `kappa^r` tilt). -/
 theorem coordAverage_bound_of_rows (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : ENNReal → ENNReal) (fees : Nat → Nat) (bound : ENNReal)
    (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (hfees : ∀ r≤80, (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      f (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
        feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W, f (priceBucket W) ≤
      (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ g : Nat → ENNReal,
      (∀ r≤80, g r ≤ 1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → g r ≤ 1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        binomialAverage (kappa*(2^31:ENNReal)⁻¹) T g ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T
      (fun W => f (priceBucket W)) ≤ bound :=
  (mul_le_mul' le_rfl (coordAverage_honest_thin T (fun W => f (priceBucket W))
    (fun L b R => hmono _ _ (priceBucket_insert L R b)))).trans
    (uniform_coordAverage_bound_of_rows T M S hM hS f fees bound hfees hpoint hcheck)

#print axioms normalizer_scale
#print axioms uniform_coordAverage_bound_of_rows
#print axioms coordAverage_bound_of_rows
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedFees SharedMoments
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem cappedIncrement_bound (W : List Alphabet) :
    cappedIncrement (priceBucket W) ≤
      (maxFee:ENNReal)*feeCoefficient*alphabetSize/scale := by
  have hx := ENNReal.toReal_mono (by unfold feeCoefficient; finiteness) (priceBucket_le W)
  rw [ENNReal.toReal_mul,feeCoefficient_real,ENNReal.toReal_natCast] at hx
  have h := (capped_payoff_of_coverage_bound (priceBucket W).toReal
    ((734:ℝ)/2^66) (alphabetSize:ℝ) ENNReal.toReal_nonneg hx).1
  rw [cappedIncrement_real _ (priceBucket_ne_top W)]
  calc
    _ ≤ ENNReal.ofReal ((maxFee:ℝ)*((734:ℝ)/2^66)*(alphabetSize:ℝ)/scale) :=
      ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast scale_pos : (0:ℝ)<scale),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.ofReal_natCast]
      rw [← feeCoefficient_real, ENNReal.ofReal_toReal (by unfold feeCoefficient; finiteness)]

 theorem residual_normalizer :
    (scale:ENNReal)*feeCoefficient*alphabetSize/scale = feeCoefficient*alphabetSize := by
  have hs0 : (scale:ENNReal) ≠ 0 := by exact_mod_cast scale_pos.ne'
  have hst : (scale:ENNReal) ≠ ⊤ := by finiteness
  simp only [div_eq_mul_inv]
  calc _ = (feeCoefficient*alphabetSize)*((scale:ENNReal)*(scale:ENNReal)⁻¹) := by ring
       _ = _ := by rw [ENNReal.mul_inv_cancel hs0 hst,mul_one]

 theorem cappedResidual_normalized_bound (W : List Alphabet) :
    cappedResidual (priceBucket W) ≤
      (scale:ENNReal)*feeCoefficient*alphabetSize/scale := by
  rw [residual_normalizer]
  exact cappedResidual_bound W

#print axioms cappedIncrement_bound
#print axioms cappedResidual_normalized_bound
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedFees SharedMoments SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The finite coverage certificate still to be supplied by the paired
histogram calculation. All sampling and conditioning factors are outside it. -/
def FiniteFeeBound : Prop := ∀ r≤80,
  (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
    cappedIncrement (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
      feeCoefficient/(scale:ENNReal)*((certifiedPayoff r).1:ENNReal) ∧
  (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
    cappedResidual (feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal))) ≤
      feeCoefficient/(scale:ENNReal)*((certifiedPayoff r).2:ENNReal)

 theorem fee_positive : 0 < maxFee := by
  by_contra hn
  have hz : maxFee=0 := Nat.eq_zero_of_not_pos hn
  have h := (capped_payoff_of_coverage_bound 1 1 1 (by norm_num) (by norm_num)).1
  rw [hz] at h
  norm_num at h

 theorem cappedIncrement_mono {x y : ENNReal} (h : x ≤ y) : cappedIncrement x ≤ cappedIncrement y := by
  unfold cappedIncrement
  apply tsub_le_tsub_right
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (min_le_right _ _)) (min_le_min h le_rfl)

 theorem cappedResidual_mono {x y : ENNReal} (h : x ≤ y) : cappedResidual x ≤ cappedResidual y :=
  tsub_le_tsub_right h _

 theorem kappa_toReal : kappa.toReal =
    (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count := by
  rw [kappa_exact, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- Window for the thinned rate `kappa * 2^-31` (rejection_ennreal style, tangent line of exp at 2):
`(1 - kappa 2^-31)^(T-80) ≤ 13283369e-8` for the cap-777 `kappa`. -/
 theorem thin_window (T : ℕ) (hT : 2 ^ 32 ≤ T) :
    (1 - kappa * (2^31 : ENNReal)⁻¹) ^ (T - 80) ≤
      ((13283369 : ℕ) : ENNReal) / ((100000000 : ℕ) : ENNReal) := by
  have hq1 := kappa_mul_rate_le_one
  have hfin : (1 - kappa * (2^31 : ENNReal)⁻¹) ^ (T - 80) ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  apply (ENNReal.toReal_le_toReal hfin (by finiteness)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_mul,
    kappa_toReal, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  set k : ℝ := (ClaudeWCT.Numerics.SharedFtsCount.total : ℝ) / ClaudeWCT.Numerics.SharedFtsCount.count with hk
  have hkv : k = 52416169542617085727767971710947931910569984 / 51927206731424509281114869451843031004872704 := by
    rw [hk]; norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count]
  set n := T - 80 with hn
  have hn0 : (2:ℝ)^32 - 80 ≤ n := by
    have : 2^32 - 80 ≤ n := by omega
    have h' : ((2^32 - 80 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    norm_num at h' ⊢; linarith
  have h0 : (0 : ℝ) ≤ 1 - k * (2^31)⁻¹ := by rw [hkv]; norm_num
  have hp : (1 - k * (2^31)⁻¹ : ℝ) ≤ Real.exp (-(k * (2^31)⁻¹)) := Real.one_sub_le_exp_neg _
  have hpow : (1 - k * (2^31)⁻¹ : ℝ) ^ n ≤ Real.exp (-(n * (k * (2^31)⁻¹))) := by
    calc (1 - k * (2^31)⁻¹ : ℝ) ^ n ≤ Real.exp (-(k * (2^31)⁻¹)) ^ n := pow_le_pow_left₀ h0 hp n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  set a0 : ℝ := ((2:ℝ)^32 - 80) * (k * (2^31)⁻¹) with ha0
  have ha : a0 ≤ n * (k * (2^31)⁻¹) :=
    mul_le_mul_of_nonneg_right hn0 (by rw [hkv]; norm_num)
  have hlow : (100000000 : ℝ) / 13283369 ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1) := by
    rw [ha0, hkv]; norm_num
  have hexp : (100000000 : ℝ) / 13283369 ≤ Real.exp (n * (k * (2^31)⁻¹)) :=
    hlow.trans ((ClaudeWCT.Numerics.PoissonReflect.exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  refine hpow.trans ?_
  rw [Real.exp_neg]
  have hpos : (0:ℝ) < 100000000 / 13283369 := by norm_num
  calc (Real.exp (n * (k * (2^31)⁻¹)))⁻¹ ≤ ((100000000 : ℝ) / 13283369)⁻¹ :=
        inv_anti₀ hpos hexp
    _ = ((13283369 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) := by norm_num

/-- Thinned Poisson parameter: `2^32 · kappa · 2^-31 = 2 kappa ≤ 2.018833` (cap 777). -/
 theorem thin_lambda :
    ((2^32 : ℕ) : ENNReal) * (kappa * (2^31 : ENNReal)⁻¹) * 1 ≤
      ((2018833 : ℕ) : ENNReal) / ((1000000 : ℕ) : ENNReal) := by
  rw [mul_one, kappa_exact]
  have hc : (ClaudeWCT.Numerics.SharedFtsCount.count : ENNReal) ≠ 0 := by
    norm_num [ClaudeWCT.Numerics.SharedFtsCount.count]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.mul_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hc) (by simp))) (by finiteness)).mp
  norm_num [ClaudeWCT.Numerics.SharedFtsCount.total, ClaudeWCT.Numerics.SharedFtsCount.count,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- Honest shared MGF through thinning: `≤ 6.945` for cap 777 (same `FiniteFeeBound` rows). -/
 theorem coord_mgf_certified (hfees : FiniteFeeBound) :
    (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw (2^32)
      (fun W => cappedIncrement (priceBucket W)) ≤ (6945:ENNReal)/1000 := by
  apply coordAverage_bound_of_rows (2^32) maxFee scale fee_positive scale_pos
    cappedIncrement (fun r => (certifiedPayoff r).1) (6945/1000)
    (fun _ _ h => cappedIncrement_mono h)
    (fun r hr => (hfees r hr).1) cappedIncrement_bound
  intro g hp ht
  exact shared_mgf_bound_of_rows (2^32) _ kappa_mul_rate_le_one (thin_window _ le_rfl)
    1 le_rfl thin_lambda g hp ht

/-- Honest shared residual through thinning: `≤ 7831e-7` for cap 777. -/
 theorem coord_residual_certified (hfees : FiniteFeeBound) :
    (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw (2^32)
      (fun W => cappedResidual (priceBucket W)) ≤ (7831:ENNReal)/10000000 := by
  apply coordAverage_bound_of_rows (2^32) scale scale scale_pos scale_pos
    cappedResidual (fun r => (certifiedPayoff r).2) (7831/10000000)
    (fun _ _ h => cappedResidual_mono h)
    (fun r hr => (hfees r hr).2) cappedResidual_normalized_bound
  intro g hp ht
  have h := shared_residual_bound_of_rows (2^32) _ kappa_mul_rate_le_one (thin_window _ le_rfl)
    1 le_rfl thin_lambda g hp ht
  have hs0 : (scale:ENNReal) ≠ 0 := by exact_mod_cast scale_pos.ne'
  have hst : (scale:ENNReal) ≠ ⊤ := by finiteness
  have he : ((scale*priceScaleTotal:Nat):ENNReal)/(scale:ENNReal) =
      (priceScaleTotal:ENNReal) := by
    simp only [Nat.cast_mul,div_eq_mul_inv]
    calc _ = (priceScaleTotal:ENNReal)*((scale:ENNReal)*(scale:ENNReal)⁻¹) := by ring
         _ = _ := by rw [ENNReal.mul_inv_cancel hs0 hst,mul_one]
  rwa [he]

 theorem finiteFees_of_real
    (hfees : ∀ r≤80,
      (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        ENNReal.ofReal (Real.exp (6*min ((734:ℝ)/2^66*
          (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ℝ)) (6/5))-1)) ≤
        ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((certifiedPayoff r).1:ENNReal) ∧
      (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
        ENNReal.ofReal (max 0 ((734:ℝ)/2^66*
          (SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ℝ)-6/5))) ≤
        ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((certifiedPayoff r).2:ENNReal)) :
    FiniteFeeBound := by
  intro r hr
  have hf : ENNReal.ofReal ((734:ℝ)/2^66)=feeCoefficient := by
    rw [←feeCoefficient_real,ENNReal.ofReal_toReal (by unfold feeCoefficient; finiteness)]
  simpa only [cappedIncrement_nat,cappedResidual_nat,hf] using hfees r hr

#print axioms coord_mgf_certified
#print axioms coord_residual_certified
#print axioms finiteFees_of_real
end ClaudeWCT.Bank.Paired

/-! Scalar endpoints for the cap-777 thinned certificate (shared MGF `6.945`, residual `7831e-7`). -/
namespace ClaudeWCT.Numerics.SharedPathWinsor.Rows18Thin
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem endpoint_middle :
    (3 / 48 : ℝ) * Real.exp (6945 / 1000 - 6 * (99847 / 50000 - 1 / 1024)) +
      7831 / 10000000 ≤ 149 / 125000 := by
  let x : ℝ := 6 * (99847 / 50000 - 1 / 1024) - 6945 / 1000
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (153 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 18)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (153 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 6945 / 1000 - 6 * (99847 / 50000 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_high :
    (3 / 48 : ℝ) * Real.exp (6945 / 1000 - 6 * (2 - 6 / 2500 - 1 / 1024)) +
      7831 / 10000000 ≤ 2979 / 2500000 := by
  let x : ℝ := 6 * (2 - 6 / 2500 - 1 / 1024) - 6945 / 1000
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (1535 / 10 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 18)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (1535 / 10 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 6945 / 1000 - 6 * (2 - 6 / 2500 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_tiny :
    (3 / 48 : ℝ) * Real.exp (6945 / 1000 - 6 * (249 / 125 - 1 / 1024)) +
      7831 / 10000000 ≤ 18 / 5000 := by
  let x : ℝ := 6 * (249 / 125 - 1 / 1024) - 6945 / 1000
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (100 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 18)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (100 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 6945 / 1000 - 6 * (249 / 125 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_low :
    (3 / 48 : ℝ) * Real.exp (6945 / 1000 - 6 * (1 - 1 / 1024)) +
      7831 / 10000000 ≤ 49 / 100 := by
  have hx : (6945 / 1000 - 6 * (1 - 1 / 1024) : ℝ) ≤ 1 := by norm_num
  have he := (Real.exp_le_exp.mpr hx).trans (le_of_lt Real.exp_one_lt_d9)
  nlinarith

#print axioms endpoint_middle
#print axioms endpoint_high
#print axioms endpoint_tiny
#print axioms endpoint_low
end ClaudeWCT.Numerics.SharedPathWinsor.Rows18Thin

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem price_excess_certified (hfees : FiniteFeeBound) (theta resultBound : ℝ)
    (htheta : 0 ≤ theta)
    (hscalar : (3/48)*Real.exp (6945/1000-6*theta)+7831/10000000 ≤ resultBound) :
    Law.lawAvg honestLaw (2^32) (fun W => price W-ENNReal.ofReal theta) ≤
      ENNReal.ofReal resultBound := by
  apply price_excess_of_bucket_bounds (2^32) (6/5) (by finiteness)
    theta 6 (6945/1000) (7831/10000000) resultBound htheta (by norm_num) (by norm_num) (by norm_num)
  · have h := coord_mgf_certified hfees
    simpa only [cappedIncrement, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<1000),
      ENNReal.ofReal_ofNat] using h
  · have h := coord_residual_certified hfees
    simpa only [cappedResidual, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<10000000),
      ENNReal.ofReal_ofNat] using h
  · convert hscalar using 1 <;> norm_num

 theorem excess_middle_certified (hfees : FiniteFeeBound) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((99847:ℝ)/50000-1/1024)) ≤
        ENNReal.ofReal ((149:ℝ)/125000) :=
  price_excess_certified hfees _ _ (by norm_num) SharedPathWinsor.Rows18Thin.endpoint_middle

 theorem excess_high_certified (hfees : FiniteFeeBound) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((2:ℝ)-6/2500-1/1024)) ≤
        ENNReal.ofReal ((2979:ℝ)/2500000) :=
  price_excess_certified hfees _ _ (by norm_num) SharedPathWinsor.Rows18Thin.endpoint_high

 theorem excess_low_certified (hfees : FiniteFeeBound) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal ((1:ℝ)-1/1024)) ≤
        ENNReal.ofReal ((49:ℝ)/100) :=
  price_excess_certified hfees _ _ (by norm_num) SharedPathWinsor.Rows18Thin.endpoint_low

 theorem tsub_convex (x theta eta a b : ENNReal) (hab : a+b=1) :
    x-(a*theta+b*eta) ≤ a*(x-theta)+b*(x-eta) := by
  apply (tsub_le_iff_right).2
  calc x = a*x+b*x := by rw [← add_mul,hab,one_mul]
       _ ≤ a*(theta+(x-theta))+b*(eta+(x-eta)) :=
         add_le_add (mul_le_mul' le_rfl le_add_tsub) (mul_le_mul' le_rfl le_add_tsub)
       _ = _ := by ring

 theorem price_excess_affine (T : Nat) (theta eta A B t : ℝ)
    (htheta : 0 ≤ theta) (heta : 0 ≤ eta) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hfirst : Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta) ≤ ENNReal.ofReal A)
    (hsecond : Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal eta) ≤ ENNReal.ofReal B) :
    Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal ((1-t)*theta+t*eta)) ≤
      ENNReal.ofReal ((1-t)*A+t*B) := by
  have ha0 : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hab : ENNReal.ofReal (1-t)+ENNReal.ofReal t=1 := by
    rw [←ENNReal.ofReal_add ha0 ht0]
    ring_nf
    exact ENNReal.ofReal_one
  have harg : ENNReal.ofReal ((1-t)*theta+t*eta) =
      ENNReal.ofReal (1-t)*ENNReal.ofReal theta+ENNReal.ofReal t*ENNReal.ofReal eta := by
    rw [ENNReal.ofReal_add (mul_nonneg ha0 htheta) (mul_nonneg ht0 heta),
      ENNReal.ofReal_mul ha0, ENNReal.ofReal_mul ht0]
  rw [harg]
  calc
    _ ≤ Law.lawAvg honestLaw T (fun W =>
      ENNReal.ofReal (1-t)*(price W-ENNReal.ofReal theta)+
      ENNReal.ofReal t*(price W-ENNReal.ofReal eta)) :=
        Law.lawAvg_mono _ _ (fun W => tsub_convex _ _ _ _ _ hab)
    _ = ENNReal.ofReal (1-t)*Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal theta)+
        ENNReal.ofReal t*Law.lawAvg honestLaw T (fun W => price W-ENNReal.ofReal eta) := by
      rw [Law.lawAvg_add,Law.lawAvg_mul_left,Law.lawAvg_mul_left]
    _ ≤ ENNReal.ofReal (1-t)*ENNReal.ofReal A+ENNReal.ofReal t*ENNReal.ofReal B :=
      add_le_add (mul_le_mul' le_rfl hfirst) (mul_le_mul' le_rfl hsecond)
    _ = _ := by
      rw [←ENNReal.ofReal_mul ha0,←ENNReal.ofReal_mul ht0,
        ←ENNReal.ofReal_add (mul_nonneg ha0 hA) (mul_nonneg ht0 hB)]

 theorem excess_large_certified (hfees : FiniteFeeBound) (y : ℝ)
    (hy0 : 3/2500 ≤ y) (hy1 : y ≤ 1/2) :
    Law.lawAvg honestLaw (2^32)
      (fun W => price W-ENNReal.ofReal (2-2*y-1/1024)) ≤
        ENNReal.ofReal ((993/1000)*y) := by
  let t : ℝ := (y-3/2500)/(1/2-3/2500)
  have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hy0) (by norm_num)
  have ht1 : t≤1 := (div_le_one (by norm_num : (0:ℝ)<1/2-3/2500)).2 (by linarith)
  have h := price_excess_affine (2^32) (2-6/2500-1/1024) (1-1/1024)
    (2979/2500000) (49/100) t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ht0 ht1 (excess_high_certified hfees) (excess_low_certified hfees)
  have harg : (1-t)*(2-6/2500-1/1024)+t*(1-1/1024) = 2-2*y-1/1024 := by
    dsimp [t]; ring
  have hgap : (993/1000)*y-((1-t)*(2979/2500000)+t*(49/100)) = t*(13/2000) := by
    dsimp [t]; ring
  have hval : (1-t)*(2979/2500000)+t*(49/100) ≤ (993/1000)*y := by nlinarith
  rw [harg] at h
  exact h.trans (ENNReal.ofReal_le_ofReal hval)

#print axioms price_excess_certified
#print axioms price_excess_affine
#print axioms excess_large_certified
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
open SharedMoments SphincsSecurity.Concrete
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem law_marked_sum {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β]
    (v : β → ENNReal) (hv : ∑ b,v b=1) (T : Nat) (f : List β → ENNReal) :
    Law.lawAvg (Law.marked (α:=α) v) T (fun W => ∑ i:α,f (atIndex i W)) =
      (Fintype.card α:ENNReal)*Law.coordAverage (Fintype.card α:ENNReal)⁻¹ v T f := by
  rw [Law.lawAvg_sum]
  simp only [Law.law_marked_atIndex v hv, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rfl

 theorem law_price_coordAverage (T : Nat) :
    Law.lawAvg honestLaw T price =
      (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T priceBucket := by
  have he : price = fun W => ∑ i : Fin (2^31),priceBucket (atIndex i W) := funext price_eq_sum
  rw [he]
  have h := law_marked_sum (α:=Fin (2^31)) honestCoordLaw honestCoordLaw_sum T priceBucket
  simpa only [honestLaw,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

 theorem first_finite_row (r : Nat) (hr : r≤80) :
    (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      feeCoefficient*(SharedCoverage.forestCoverage ClaudeWCT.WCT9.wordDigit h:ENNReal)) =
        feeCoefficient*(forestMoment r:ENNReal) := by
  rw [← Finset.mul_sum,←Nat.cast_sum]
  have h := SharedCoverage.forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit rows_checked r (by omega)
  exact congrArg (fun n : Nat => feeCoefficient*(n:ENNReal)) h

 theorem law_price_mean_bound : Law.lawAvg honestLaw (2^32) price ≤ (849:ENNReal)/1000 := by
  rw [law_price_coordAverage]
  apply coordAverage_bound_of_rows (2^32) 1 1 (by norm_num) (by norm_num)
    id forestMoment (849/1000) (fun _ _ h => h)
  · intro r hr
    simpa only [id_eq,Nat.cast_one,div_one] using (first_finite_row r hr).le
  · intro W
    simpa only [id_eq,Nat.cast_one,one_mul,div_one] using priceBucket_le W
  · intro g hp ht
    have h := first_bound_of_rows (2^32) _ kappa_mul_rate_le_one (thin_window _ le_rfl)
      1 le_rfl thin_lambda g (by simpa only [Nat.one_mul] using hp) ht
    simpa only [Nat.one_mul,Nat.cast_one,div_one] using h

#print axioms law_marked_sum
#print axioms law_price_coordAverage
#print axioms law_price_mean_bound
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem uniform_history_le_of_le (r : Nat) (f : List Alphabet → ENNReal)
    (g : SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g (splitHistory h)) :
    Law.lawAvg uniformCoordLaw r f ≤ 1^r *
      ((∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r) := by
  have hu : SphincsSecurity.Concrete.uniformWordAverage r f ≤
      (∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r := by
    rw [SigGolfResearch.Gate6.Moments.word_array_average]
    unfold SigGolfResearch.Gate6.Moments.finiteAverage
    have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card rfl
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,hc]
    rw [←sum_history]
    exact ENNReal.div_le_div_right (Finset.sum_le_sum (fun h _ => hfg h)) _
  exact (Law.lawAvg_le_uniform uniformCoordLaw 1 uniformCoordLaw_density r f).trans
    (mul_le_mul' le_rfl hu)

 theorem uniform_normalized_history_row (r M S fee : Nat) (hM : 0<M) (hS : 0<S)
    (f : List Alphabet → ENNReal) (g : SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (hfg : ∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g (splitHistory h))
    (hfee : (∑ h,g h) ≤ feeCoefficient/(S:ENNReal)*(fee:ENNReal)) :
    Law.lawAvg uniformCoordLaw r
      (fun W => f W/((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)) ≤
      1^r*((16^r*fee:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal) := by
  rw [←normalized_denominator r M fee hM 1,lawAvg_div]
  calc
    _ ≤ (1^r*((∑ h,g h)/(SharedMoments.alphabetSize:ENNReal)^r))/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) :=
      ENNReal.div_le_div_right (uniform_history_le_of_le r f g hfg) _
    _ ≤ (1^r*((feeCoefficient/(S:ENNReal))*(fee:ENNReal))/(SharedMoments.alphabetSize:ENNReal)^r)/
        ((M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S) := by
      apply ENNReal.div_le_div_right
      rw [mul_div_assoc]
      exact mul_le_mul' le_rfl (ENNReal.div_le_div_right hfee _)
    _ = _ := normalize_row_arithmetic feeCoefficient S M SharedMoments.alphabetSize 1 fee r
      (by norm_num [feeCoefficient]) (by unfold feeCoefficient; finiteness)
      (by positivity) (by finiteness) (by positivity) (by finiteness)
      (by norm_num [SharedMoments.alphabetSize]) (by finiteness)

/-- Thinned history certificate: an insertion-monotone `f` is bounded through
`coordAverage_honest_thin` and uniform history rows (no `kappa^r` tilt). -/
 theorem coordAverage_history_bound (T M S : Nat) (hM : 0<M) (hS : 0<S)
    (f : List Alphabet → ENNReal)
    (g : (r : Nat) → SharedCoverage.ForestHistory (Fin 563) r → ENNReal)
    (fees : Nat → Nat) (bound : ENNReal)
    (hins : ∀ L b R,f (L++R) ≤ f (L++b::R))
    (hfg : ∀ r≤80,∀ h : Fin r → Alphabet,f (List.ofFn h) ≤ g r (splitHistory h))
    (hfees : ∀ r≤80,(∑ h,g r h) ≤ feeCoefficient/(S:ENNReal)*(fees r:ENNReal))
    (hpoint : ∀ W,f W≤(M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S)
    (hcheck : ∀ v : Nat → ENNReal,
      (∀ r≤80,v r≤1^r*((16^r*fees r:Nat):ENNReal)/
        ((M*SharedMoments.alphabetSize*SharedMoments.fieldSize^(9*r):Nat):ENNReal)) →
      (∀ r,80 < r → v r≤1) →
      ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        SphincsSecurity.Concrete.binomialAverage (kappa*(2^31:ENNReal)⁻¹) T v ≤ bound) :
    (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T f ≤ bound := by
  refine (mul_le_mul' le_rfl (coordAverage_honest_thin T f hins)).trans ?_
  let C : ENNReal := (M:ENNReal)*feeCoefficient*SharedMoments.alphabetSize/S
  have hC0 : C≠0 := by
    have hMc : (M:ENNReal)≠0 := by exact_mod_cast hM.ne'
    have hfc : feeCoefficient≠0 := by norm_num [feeCoefficient]
    have hDc : (SharedMoments.alphabetSize:ENNReal)≠0 := by norm_num [SharedMoments.alphabetSize]
    exact ENNReal.div_ne_zero.mpr ⟨mul_ne_zero (mul_ne_zero hMc hfc) hDc,ENNReal.natCast_ne_top S⟩
  have hCt : C≠⊤ := by dsimp [C,feeCoefficient]; finiteness
  let v : Nat → ENNReal := fun r => Law.lawAvg uniformCoordLaw r (fun W => f W/C)
  have hv := hcheck v
    (fun r hr => uniform_normalized_history_row r M S (fees r) hM hS f (g r) (hfg r hr) (hfees r hr))
    (fun r _ => uniform_normalized_le_one r f C hC0 hCt hpoint)
  calc
    _ = ((2^31:ENNReal)*C)*Law.coordAverage (kappa*(2^31:ENNReal)⁻¹) uniformCoordLaw T (fun W => f W/C) :=
      (coordAverage_scaled uniformCoordLaw T f C (2^31) (kappa*(2^31:ENNReal)⁻¹) hC0 hCt).symm
    _ = ((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S *
        SphincsSecurity.Concrete.binomialAverage (kappa*(2^31:ENNReal)⁻¹) T v := by
      rw [show (2^31:ENNReal)*C=((M*SharedMoments.priceScaleTotal:Nat):ENNReal)/S from normalizer_scale M S]
      rfl
    _ ≤ bound := hv

#print axioms uniform_history_le_of_le
#print axioms coordAverage_history_bound
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open SharedCoverage Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

 theorem card_filter_congr_any {α : Type} [Fintype α] (P Q : α → Prop)
    (dP : DecidablePred P) (dQ : DecidablePred Q) (h : ∀ a,P a↔Q a) :
    (@Finset.filter α P dP Finset.univ).card = (@Finset.filter α Q dQ Finset.univ).card := by
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter]
  exact and_congr Iff.rfl (h a)

def PairNearAt {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) (side : Fin 2) (t : Fin 6) (a : PairChoice β) : Prop :=
  if side=0 then
    CovAtExcept val t a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
    CovAt val a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)
  else
    CovAt val a.2.1.1 (val a.2.1.2) (splitRanks h.1 h.2.1 a.1) ∧
    CovAtExcept val t a.2.2.1 (val a.2.2.2) (splitRanks h.1 h.2.2 a.1)

 theorem pairPredicate_card {β : Type} [Fintype β]
    (P Q : Fin 2 → Fin 64 × β → Prop) :
    #{a : PairChoice β | P a.1 a.2.1 ∧ Q a.1 a.2.2} =
      ∑ s : Fin 2, #{a | P s a} * #{b | Q s b} := by
  let e : {a : PairChoice β // P a.1 a.2.1 ∧ Q a.1 a.2.2} ≃
      (s : Fin 2) × {a : Fin 64 × β // P s a} × {b : Fin 64 × β // Q s b} :=
    { toFun := fun a => ⟨a.val.1,⟨a.val.2.1,a.property.1⟩,⟨a.val.2.2,a.property.2⟩⟩
      invFun := fun a => ⟨(a.1,a.2.1.val,a.2.2.val),a.2.1.property,a.2.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_subtype,Fintype.card_sigma,Fintype.card_prod] using he

 theorem pairNearAt_sum {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : PairHistory β r) :
    (∑ side : Fin 2, ∑ t : Fin 6, #{a : PairChoice β | PairNearAt val h side t a}) =
      pairNear val h := by
  have hleft (t : Fin 6) : #{a : PairChoice β | PairNearAt val h 0 t a} =
      ∑ s : Fin 2, #{a : Fin 64 × β | CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.1 s)} *
        coordinateCoverage val (splitRanks h.1 h.2.2 s) := by
    have hh := pairPredicate_card
      (fun s a => CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.1 s))
      (fun s a => CovAt val a.1 (val a.2) (splitRanks h.1 h.2.2 s))
    convert hh using 1
    · apply card_filter_congr_any; intro a; simp only [PairNearAt,ite_true]
    · apply Finset.sum_congr rfl
      intro z _
      apply congrArg₂ Nat.mul
      · apply card_filter_congr_any; intro a; rfl
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
  have hright (t : Fin 6) : #{a : PairChoice β | PairNearAt val h 1 t a} =
      ∑ s : Fin 2, coordinateCoverage val (splitRanks h.1 h.2.1 s) *
        #{a : Fin 64 × β | CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.2 s)} := by
    have hh := pairPredicate_card
      (fun s a => CovAt val a.1 (val a.2) (splitRanks h.1 h.2.1 s))
      (fun s a => CovAtExcept val t a.1 (val a.2) (splitRanks h.1 h.2.2 s))
    convert hh using 1
    · apply card_filter_congr_any; intro a; simp only [PairNearAt,show (1:Fin 2)≠0 by decide,ite_false]
    · apply Finset.sum_congr rfl
      intro z _
      apply congrArg₂ Nat.mul
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
      · apply card_filter_congr_any; intro a; rfl
  rw [Fin.sum_univ_two]
  simp_rw [hleft,hright]
  simp only [Fin.sum_univ_two,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum]
  unfold pairNear selectorKernel coordinateNear coordinateCoverage
  ring

abbrev ForestHole := (Fin 4 × Fin 2 × Fin 6) ⊕ Fin 6

def ForestNearAt {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) (hole : ForestHole) (a : ForestChoice β) : Prop :=
  match hole with
  | .inl v => (∀ p, if p=v.1 then PairNearAt val (h.1 p) v.2.1 v.2.2 (a.1 p)
                    else PairCovered val (h.1 p) (a.1 p)) ∧ CovAt val a.2.1 (val a.2.2) h.2
  | .inr t => (∀ p, PairCovered val (h.1 p) (a.1 p)) ∧ CovAtExcept val t a.2.1 (val a.2.2) h.2

 theorem forestPredicate_card {β : Type} [Fintype β]
    (P : Fin 4 → PairChoice β → Prop) (Q : Fin 128 × β → Prop) :
    #{a : ForestChoice β | (∀ p, P p (a.1 p)) ∧ Q a.2} =
      (∏ p, #{a | P p a}) * #{b | Q b} := by
  let e : {a : ForestChoice β // (∀ p,P p (a.1 p)) ∧ Q a.2} ≃
      ((p:Fin 4) → {a : PairChoice β // P p a}) × {b : Fin 128 × β // Q b} :=
    { toFun := fun a => (fun p => ⟨a.val.1 p,a.property.1 p⟩,⟨a.val.2,a.property.2⟩)
      invFun := fun a => ⟨(fun p => (a.1 p).val,a.2.val),(fun p => (a.1 p).property),a.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_pi] using he

 theorem sum_prod_replace {δ : Type} [Fintype δ] (p : Fin 4)
    (f : δ → Fin 4 → Nat) (g : Fin 4 → Nat) :
    (∑ d, ∏ i : Fin 4, if i=p then f d i else g i) =
      ∏ i : Fin 4, if i=p then ∑ d,f d i else g i := by
  fin_cases p <;> simp [Fin.prod_univ_succ,←Finset.sum_mul,←Finset.mul_sum]

 theorem forestNearAt_sum {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : ForestHistory β r) :
    (∑ hole : ForestHole, #{a : ForestChoice β | ForestNearAt val h hole a}) =
      forestNear val h := by
  have hleft (k : Fin 4) (side : Fin 2) (t : Fin 6) :
      #{a : ForestChoice β | ForestNearAt val h (.inl (k,side,t)) a} =
      (∏ p : Fin 4, #{a : PairChoice β | if p=k then PairNearAt val (h.1 p) side t a
        else PairCovered val (h.1 p) a}) * coordinateCoverage val h.2 := by
    have hh := forestPredicate_card
      (fun p a => if p=k then PairNearAt val (h.1 p) side t a else PairCovered val (h.1 p) a)
      (fun a => CovAt val a.1 (val a.2) h.2)
    convert hh using 1
    · apply card_filter_congr_any; intro a; rfl
    · apply congrArg₂ Nat.mul
      · apply Finset.prod_congr rfl
        intro p _
        apply card_filter_congr_any; intro a; rfl
      · unfold coordinateCoverage
        apply card_filter_congr_any; intro a; rfl
  have hright (t : Fin 6) :
      #{a : ForestChoice β | ForestNearAt val h (.inr t) a} =
      (∏ p : Fin 4, pairCoverage val (h.1 p)) *
        #{a : Fin 128 × β | CovAtExcept val t a.1 (val a.2) h.2} := by
    have hh := forestPredicate_card (fun p a => PairCovered val (h.1 p) a)
      (fun a => CovAtExcept val t a.1 (val a.2) h.2)
    simp only [pairCovered_card] at hh
    convert hh using 1
    · apply card_filter_congr_any; intro a; rfl
    · apply congrArg₂ Nat.mul
      · rfl
      · apply card_filter_congr_any; intro a; rfl
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  simp_rw [hleft,hright]
  have hcard (p k : Fin 4) (side : Fin 2) (t : Fin 6) :
      #{a : PairChoice β | if p=k then PairNearAt val (h.1 p) side t a else PairCovered val (h.1 p) a} =
        if p=k then #{a : PairChoice β | PairNearAt val (h.1 p) side t a} else pairCoverage val (h.1 p) := by
    by_cases hp : p=k <;> simp only [hp,ite_true,ite_false,pairCovered_card]
  simp_rw [hcard]
  simp only [←Finset.sum_mul,←Finset.mul_sum]
  have hsum (k : Fin 4) :
      (∑ side : Fin 2, ∑ t : Fin 6, ∏ p : Fin 4,
        if p=k then #{a : PairChoice β | PairNearAt val (h.1 p) side t a} else pairCoverage val (h.1 p)) =
      ∏ p : Fin 4, if p=k then pairNear val (h.1 p) else pairCoverage val (h.1 p) := by
    simp_rw [sum_prod_replace]
    simp only [sum_prod_replace,pairNearAt_sum]
  simp_rw [hsum]
  rfl

#print axioms pairNearAt_sum
#print axioms forestNearAt_sum
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ClaudeWCT.Numerics ClaudeWCT.Numerics.N600
open SharedCoverage Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def pairCoord (p : Fin 4) (side : Fin 2) : Fin 9 := ⟨2*p.val+side.val,by omega⟩
def holeCoord : ForestHole → Fin 9 × Fin 6
  | .inl v => (pairCoord v.1 v.2.1,v.2.2)
  | .inr t => (8,t)
def coordHole (c : Fin 9 × Fin 6) : ForestHole :=
  if hc : c.1.val<8 then .inl (⟨c.1.val/2,by omega⟩,⟨c.1.val%2,by omega⟩,c.2)
  else .inr c.2

def holeEquiv : ForestHole ≃ Fin 9 × Fin 6 where
  toFun := holeCoord
  invFun := coordHole
  left_inv h := by
    rcases h with ⟨p,s,t⟩|t
    · fin_cases p <;> fin_cases s <;> simp [coordHole,holeCoord,pairCoord]
    · rfl
  right_inv c := by
    rcases c with ⟨k,t⟩
    fin_cases k <;> simp [coordHole,holeCoord,pairCoord]

 theorem pairCoord_inj (p q : Fin 4) (s t : Fin 2) :
    pairCoord p s=pairCoord q t ↔ p=q ∧ s=t := by
  simp only [pairCoord,Fin.ext_iff]
  have hs := s.isLt
  have ht := t.isLt
  omega

 theorem pairCoord_ne_singleton (p : Fin 4) (s : Fin 2) : pairCoord p s ≠ 8 := by
  intro he
  have hh := congrArg Fin.val he
  have hp := p.isLt
  have hs := s.isLt
  change 2*p.val+s.val=8 at hh
  omega

 theorem covAtExcept_splitRanks {β : Type} [Fintype β] {r : Nat}
    (val : β → Fin 6 → Nat) (o : Fin r → Fin 2) (A : Fin r → Fin 64 × β)
    (s : Fin 2) (target : Fin 64 × β) (t : Fin 6) :
    CovAtExcept val t target.1 (val target.2) (splitRanks o A s) ↔
      ∀ u,u≠t → ∃ j,o j=s ∧ (A j).1=target.1 ∧ val target.2 u≤val (A j).2 u := by
  constructor
  · intro h u hu
    obtain ⟨j,hj,hv⟩ := h u hu
    let z := (fiberIndex o s).symm j
    exact ⟨z.val,z.property,by simpa only [splitRanks_apply] using hj,
      by simpa only [splitRanks_apply] using hv⟩
  · intro h u hu
    obtain ⟨j,hj,hc,hv⟩ := h u hu
    refine ⟨fiberIndex o s ⟨j,hj⟩,?_,?_⟩
    · simpa only [splitRanks_apply,Equiv.symm_apply_apply] using hc
    · simpa only [splitRanks_apply,Equiv.symm_apply_apply] using hv

def AlphabetNearAt {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (hole : ForestHole) (a : AlphabetOf β) : Prop :=
  ∀ k : Fin 9, ∀ t : Fin 6, (k,t)≠holeCoord hole → ∃ j,
    rawChild (h j).1 k=rawChild a.1 k ∧ val (a.2 k) t≤val ((h j).2 k) t

 theorem alphabetNear_forest {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (hole : ForestHole) (a : AlphabetOf β)
    (hn : AlphabetNearAt val h hole a) : ForestNearAt val (splitHistory h) hole (choice a) := by
  let P : Fin 9 → Fin 6 → Prop := fun k t => ∃ j,
    rawChild (h j).1 k=rawChild a.1 k ∧ val (a.2 k) t≤val ((h j).2 k) t
  have hfirst (p : Fin 4) :
      CovAt val ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ t,P (pairCoord p 0) t := by
    rw [covAt_splitRanks]
    simp only [P,pairCoord,Fin.val_zero,Nat.add_zero]
    simp only [splitHistory,choice,rawChild_first_eq,and_assoc]
  have hsecond (p : Fin 4) :
      CovAt val ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ t,P (pairCoord p 1) t := by
    rw [covAt_splitRanks]
    simp only [P,pairCoord,Fin.val_one]
    simp only [splitHistory,choice,rawChild_second_eq,and_assoc]
  have hfirstE (p : Fin 4) (t : Fin 6) :
      CovAtExcept val t ((choice a).1 p).2.1.1 (val ((choice a).1 p).2.1.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.1 ((choice a).1 p).1) ↔
      ∀ u,u≠t → P (pairCoord p 0) u := by
    rw [covAtExcept_splitRanks]
    simp only [P,pairCoord,Fin.val_zero,Nat.add_zero]
    simp only [splitHistory,choice,rawChild_first_eq,and_assoc]
  have hsecondE (p : Fin 4) (t : Fin 6) :
      CovAtExcept val t ((choice a).1 p).2.2.1 (val ((choice a).1 p).2.2.2)
        (splitRanks ((splitHistory h).1 p).1 ((splitHistory h).1 p).2.2 ((choice a).1 p).1) ↔
      ∀ u,u≠t → P (pairCoord p 1) u := by
    rw [covAtExcept_splitRanks]
    simp only [P,pairCoord,Fin.val_one]
    simp only [splitHistory,choice,rawChild_second_eq,and_assoc]
  rcases hole with ⟨p,s,t⟩|t
  · refine ⟨?_,?_⟩
    · intro q
      by_cases hq:q=p
      · subst q
        rw [if_pos rfl]
        fin_cases s
        · refine ⟨(hfirstE p t).mpr ?_,(hsecond p).mpr ?_⟩
          · intro u hu
            exact hn _ _ (fun he => hu (congrArg Prod.snd he))
          · intro u
            apply hn
            intro he
            have hc := (pairCoord_inj p p 1 0).mp (congrArg Prod.fst he)
            exact (by decide : (1:Fin 2)≠0) hc.2
        · refine ⟨(hfirst p).mpr ?_,(hsecondE p t).mpr ?_⟩
          · intro u
            apply hn
            intro he
            have hc := (pairCoord_inj p p 0 1).mp (congrArg Prod.fst he)
            exact (by decide : (0:Fin 2)≠1) hc.2
          · intro u hu
            exact hn _ _ (fun he => hu (congrArg Prod.snd he))
      · rw [if_neg hq]
        refine ⟨(hfirst q).mpr ?_,(hsecond q).mpr ?_⟩ <;> intro u <;> apply hn <;> intro he
        · exact hq ((pairCoord_inj q p 0 s).mp (congrArg Prod.fst he)).1
        · exact hq ((pairCoord_inj q p 1 s).mp (congrArg Prod.fst he)).1
    · intro u
      exact hn 8 u (fun he => pairCoord_ne_singleton p s (congrArg Prod.fst he).symm)
  · refine ⟨?_,?_⟩
    · intro p
      refine ⟨(hfirst p).mpr ?_,(hsecond p).mpr ?_⟩ <;> intro u <;> apply hn <;> intro he
      · exact pairCoord_ne_singleton p 0 (congrArg Prod.fst he)
      · exact pairCoord_ne_singleton p 1 (congrArg Prod.fst he)
    · intro u hu
      exact hn 8 u (fun he => hu (congrArg Prod.snd he))

 theorem alphabetNear_sum_le {β : Type} [Fintype β] (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) :
    (∑ hole : ForestHole, #{a : AlphabetOf β | AlphabetNearAt val h hole a}) ≤
      forestNear val (splitHistory h) := by
  rw [←forestNearAt_sum]
  apply Finset.sum_le_sum
  intro hole _
  let e : {a : AlphabetOf β // AlphabetNearAt val h hole a} ≃
      {a : ForestChoice β // AlphabetNearAt val h hole ((choiceEquiv β).symm a)} :=
    (choiceEquiv β).subtypeEquiv (fun a => by rw [(choiceEquiv β).symm_apply_apply a])
  have he := Fintype.card_congr e
  simp only [Fintype.card_subtype] at he
  rw [he]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨_,ha⟩ := Finset.mem_filter.mp ha
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  have hh := alphabetNear_forest val h hole ((choiceEquiv β).symm a) ha
  simpa only [show choice ((choiceEquiv β).symm a)=a from (choiceEquiv β).apply_symm_apply a] using hh

#print axioms holeEquiv
#print axioms alphabetNear_forest
#print axioms alphabetNear_sum_le
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

def ListAlphabetNear {β : Type} (val : β → Fin 6 → Nat)
    (W : List (AlphabetOf β)) (a : AlphabetOf β) (hole : Fin 9 × Fin 6) : Prop :=
  ∀ k : Fin 9,∀ t : Fin 6,(k,t)≠hole → ∃ e∈W,
    rawChild e.1 k=rawChild a.1 k ∧ val (a.2 k) t≤val (e.2 k) t
noncomputable def nearBucket (W : List Alphabet) : ENNReal :=
  (SharedMoments.priceScaleTotal:ENNReal)/(2^31) *
    finiteAverage (fun a => ∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit W a hole then 1 else 0)

def NearCoveredAtP (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput)
    (hole : Fin 9 × Fin 6) : Prop :=
  ∀ k t,(k,t)≠hole → SlotCoveredP W N k t
noncomputable def nearScoreP (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput) : ENNReal :=
  if admissible N=true then ∑ hole : Fin 9 × Fin 6,if NearCoveredAtP W N hole then 1 else 0 else 0
noncomputable def nearPrice (W : List Proposal) : ENNReal :=
  (2:ENNReal)^128 * SigGolfCandidate.T3.BPORS.finiteAverage (nearScoreP W)

 theorem listAlphabetNear_ofFn {β : Type} (val : β → Fin 6 → Nat) {r : Nat}
    (h : Fin r → AlphabetOf β) (a : AlphabetOf β) (hole : ForestHole) :
    ListAlphabetNear val (List.ofFn h) a (holeCoord hole) ↔ AlphabetNearAt val h hole a := by
  simp only [ListAlphabetNear,AlphabetNearAt,List.mem_ofFn]
  refine forall_congr' fun k => forall_congr' fun t => forall_congr' fun ht => ?_
  constructor
  · rintro ⟨e,⟨j,rfl⟩,he⟩
    exact ⟨j,he⟩
  · rintro ⟨j,hj⟩
    exact ⟨h j,⟨j,rfl⟩,hj⟩

 theorem nearBucket_ofFn_le {r : Nat} (h : Fin r → Alphabet) :
    nearBucket (List.ofFn h) ≤ feeCoefficient*
      (SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hs : (∑ a : Alphabet,∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (List.ofFn h) a hole then (1:ENNReal) else 0) ≤
      (SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal) := by
    rw [sum_comm]
    conv_lhs => rw [←Equiv.sum_comp holeEquiv]
    change (∑ hole : ForestHole,∑ a : Alphabet,if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (List.ofFn h) a (holeCoord hole) then (1:ENNReal) else 0) ≤ _
    simp_rw [listAlphabetNear_ofFn,←natCast_card_filter]
    rw [←Nat.cast_sum]
    exact_mod_cast alphabetNear_sum_le ClaudeWCT.WCT9.wordDigit h
  unfold nearBucket finiteAverage
  rw [hc,←fee_price_scale]
  calc
    _ ≤ (feeCoefficient*SharedMoments.alphabetSize)*
        ((SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit (splitHistory h):ENNReal)/
          SharedMoments.alphabetSize) := mul_le_mul' le_rfl (ENNReal.div_le_div_right hs _)
    _ = _ := by
      rw [mul_assoc,ENNReal.mul_div_cancel
        (by norm_num [SharedMoments.alphabetSize]) (by simp)]

 theorem nearBucket_bound (W : List Alphabet) :
    nearBucket W ≤ (54:ENNReal)*feeCoefficient*SharedMoments.alphabetSize := by
  unfold nearBucket finiteAverage
  have hsum : (∑ a : Alphabet,∑ hole : Fin 9 × Fin 6,
      if ListAlphabetNear ClaudeWCT.WCT9.wordDigit W a hole then (1:ENNReal) else 0) ≤
      (Fintype.card Alphabet:ENNReal)*54 := by
    calc
      _ ≤ ∑ _ : Alphabet,∑ _ : Fin 9 × Fin 6,(1:ENNReal) := by
        apply sum_le_sum;intro a _;apply sum_le_sum;intro hole _;split_ifs <;> simp
      _ = _ := by simp
  have hc : Fintype.card Alphabet≠0 := Fintype.card_ne_zero
  have he := ENNReal.div_le_div_right hsum (Fintype.card Alphabet:ENNReal)
  rw [mul_div_assoc,ENNReal.mul_div_cancel (by exact_mod_cast hc) (by simp)] at he
  calc
    _ ≤ (SharedMoments.priceScaleTotal:ENNReal)/(2^31)*54 := mul_le_mul' le_rfl he
    _ = _ := by rw [←fee_price_scale];ring

 theorem nearCoveredAtP_bucket (W : List Proposal) (N : SigGolfCandidate.T3.HashOutput)
    (hole : Fin 9 × Fin 6) :
    NearCoveredAtP W N hole ↔ ListAlphabetNear ClaudeWCT.WCT9.wordDigit
      (atIndex (proposal N).1 W) (proposal N).2 hole := by
  unfold NearCoveredAtP SlotCoveredP ListAlphabetNear
  refine forall_congr' fun k => forall_congr' fun t => forall_congr' fun ht => ?_
  constructor
  · rintro ⟨p,hp,h1,h2,h3⟩
    refine ⟨p.2,(WCTEnvelope.mem_atIndex _ _ _).mpr ?_,h2,h3⟩
    rw [←h1];exact hp
  · rintro ⟨a,ha,h2,h3⟩
    exact ⟨((proposal N).1,a),(WCTEnvelope.mem_atIndex _ _ _).mp ha,rfl,h2,h3⟩

 theorem nearPrice_eq_sum (W : List Proposal) : nearPrice W =
    ∑ index : Fin (2^31),nearBucket (atIndex index W) := by
  let g : Proposal → ENNReal := fun p => ∑ hole : Fin 9 × Fin 6,
    if ListAlphabetNear ClaudeWCT.WCT9.wordDigit (atIndex p.1 W) p.2 hole then 1 else 0
  have hs (N : SigGolfCandidate.T3.HashOutput) : nearScoreP W N =
      if admissible N=true then g (proposal N) else 0 := by
    unfold nearScoreP
    congr 1
    apply sum_congr rfl
    intro hole _
    exact if_congr (nearCoveredAtP_bucket W N hole) rfl rfl
  have hc : Fintype.card Alphabet=SharedMoments.alphabetSize := alphabet_card (Fintype.card_fin 563)
  have hsum : (∑ p,g p) = (SharedMoments.alphabetSize:ENNReal)*
      ∑ index : Fin (2^31),finiteAverage (fun a => g (index,a)) := by
    rw [Fintype.sum_prod_type,mul_sum]
    apply sum_congr rfl;intro index _
    unfold finiteAverage
    rw [hc,ENNReal.mul_div_cancel (by norm_num [SharedMoments.alphabetSize]) (by simp)]
  unfold nearPrice SigGolfCandidate.T3.BPORS.finiteAverage
  simp_rw [hs]
  rw [sum_admissible g,hsum,Fintype.card_bitVec]
  unfold nearBucket
  rw [←mul_sum,←price_scale]
  simp only [div_eq_mul_inv]
  ring

 theorem nearBucket_insert (L R : List Alphabet) (b : Alphabet) :
    nearBucket (L++R) ≤ nearBucket (L++b::R) := by
  unfold nearBucket finiteAverage
  apply mul_le_mul' le_rfl
  apply ENNReal.div_le_div_right
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro hole _
  by_cases h1 : ListAlphabetNear ClaudeWCT.WCT9.wordDigit (L++R) a hole
  · have h2 : ListAlphabetNear ClaudeWCT.WCT9.wordDigit (L++b::R) a hole := by
      intro k t hne
      obtain ⟨e,he,hc⟩ := h1 k t hne
      refine ⟨e,?_,hc⟩
      rcases List.mem_append.mp he with he|he
      · exact List.mem_append_left _ he
      · exact List.mem_append_right _ (List.mem_cons_of_mem b he)
    simp only [if_pos h1,if_pos h2,le_refl]
  · simp only [if_neg h1]
    exact zero_le

#print axioms nearBucket_ofFn_le
#print axioms nearBucket_bound
#print axioms nearPrice_eq_sum
#print axioms nearBucket_insert
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open Finset ENNReal ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedMoments
open SigGolfCandidate.T3.BPORS.History (atIndex)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

 theorem law_nearPrice_coordAverage (T : Nat) :
    Law.lawAvg honestLaw T nearPrice =
      (2^31:ENNReal)*Law.coordAverage (2^31:ENNReal)⁻¹ honestCoordLaw T nearBucket := by
  have he : nearPrice = fun W => ∑ i : Fin (2^31),nearBucket (atIndex i W) := funext nearPrice_eq_sum
  rw [he]
  have h := law_marked_sum (α:=Fin (2^31)) honestCoordLaw honestCoordLaw_sum T nearBucket
  simpa only [honestLaw,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

 theorem near_finite_row (r : Nat) (hr : r≤80) :
    (∑ h : SharedCoverage.ForestHistory (Fin 563) r,
      feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal)) =
        feeCoefficient*(forestNearMoment r:ENNReal) := by
  rw [←Finset.mul_sum,←Nat.cast_sum]
  have h := SharedCoverage.forest_near_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    WCTEnvelope.w1Table_wordDigit WCTEnvelope.wfTable_wordDigit rows_checked r (by omega)
  exact congrArg (fun n : Nat => feeCoefficient*(n:ENNReal)) h

 theorem law_nearPrice_mean_bound : Law.lawAvg honestLaw (2^32) nearPrice ≤ 351 := by
  rw [law_nearPrice_coordAverage]
  apply coordAverage_history_bound (2^32) 54 1 (by norm_num) (by norm_num)
    nearBucket (fun _ h => feeCoefficient*(SharedCoverage.forestNear ClaudeWCT.WCT9.wordDigit h:ENNReal))
    forestNearMoment 351 (fun L b R => nearBucket_insert L R b)
  · intro r _ h
    exact nearBucket_ofFn_le h
  · intro r hr
    simpa only [Nat.cast_one,div_one] using (near_finite_row r hr).le
  · intro W
    simpa only [Nat.cast_one,Nat.cast_ofNat,div_one] using nearBucket_bound W
  · intro g hp ht
    have h := near_bound_of_rows (2^32) _ kappa_mul_rate_le_one (thin_window _ le_rfl)
      1 le_rfl thin_lambda g hp ht
    simpa only [Nat.cast_one,div_one] using h

#print axioms near_finite_row
#print axioms law_nearPrice_mean_bound
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleComp.EvalDist ENNReal Finset ClaudeWCT.Numerics
open SigGolfCandidate.T3 SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 def NearCovered (X : List HashOutput) (N : HashOutput) : Prop :=
  ∃ hole,NearCoveredAtP (X.map proposal) N hole
noncomputable def nearScore (X : List HashOutput) (N : HashOutput) : ENNReal :=
  nearScoreP (X.map proposal) N

 theorem nearCoveredAtP_source (X : List HashOutput) (N : HashOutput) (hole : Fin 9 × Fin 6) :
    NearCoveredAtP (X.map proposal) N hole ↔
      ∀ k t,(k,t)≠hole → ∃ output∈X,ClaudeWCT.WCT9.digestIndex output=ClaudeWCT.WCT9.digestIndex N ∧
        SharedForest.rawChildFromOutput output k=SharedForest.rawChildFromOutput N k ∧
        ClaudeWCT.WCT9.wordDigit (SharedForest.forestRank N k.val) t≤
          ClaudeWCT.WCT9.wordDigit (SharedForest.forestRank output k.val) t := by
  unfold NearCoveredAtP
  exact forall_congr' fun k => forall_congr' fun t => imp_congr_right fun _ => slotCoveredP_source X N k t

 theorem nearCoveredAtP_append (W V : List Proposal) (N : HashOutput) (hole : Fin 9 × Fin 6)
    (h : NearCoveredAtP W N hole) : NearCoveredAtP (W++V) N hole := by
  intro k t hne
  obtain ⟨p,hp,h1,h2,h3⟩ := h k t hne
  exact ⟨p,List.mem_append_left V hp,h1,h2,h3⟩

 theorem nearScore_append_mono (X Y : List HashOutput) (N : HashOutput) :
    nearScore X N≤nearScore (X++Y) N := by
  unfold nearScore nearScoreP
  rw [List.map_append]
  split_ifs with ha
  · apply sum_le_sum
    intro hole _
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (nearCoveredAtP_append _ _ N hole h1) h2
    · exact zero_le_one
    · exact le_rfl
  · exact le_rfl

 theorem one_le_nearScore (X : List HashOutput) (N : HashOutput)
    (ha : admissible N=true) (h : NearCovered X N) : 1≤nearScore X N := by
  obtain ⟨hole,hh⟩ := h
  unfold nearScore nearScoreP
  rw [if_pos ha]
  have hs := Finset.single_le_sum (s:=Finset.univ) (a:=hole)
    (f:=fun h => if NearCoveredAtP (X.map proposal) N h then (1:ENNReal) else 0)
    (fun _ _ => zero_le) (mem_univ hole)
  simpa only [if_pos hh] using hs

 theorem average_nearScore (X : List HashOutput) :
    BPORS.finiteAverage (nearScore X) = nearPrice (X.map proposal)/2^128 := by
  unfold nearPrice nearScore
  rw [mul_comm,ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]

noncomputable def withCoverage {P : Type} [Fintype P] [SampleableType P]
    (S : FtsBankSpec P) (score : List HashOutput → HashOutput → ENNReal)
    (covered : List HashOutput → HashOutput → Prop)
    (hscore : ∀ X N,S.admissible N=true → covered X N → 1 ≤ score X N)
    (hmono : ∀ X Y N,score X N ≤ score (X++Y) N)
    (price : List P → ENNReal)
    (havg : ∀ X,BPORS.finiteAverage (score X)=price (X.map S.proposal)/2^128)
    (rate : ENNReal)
    (hrate : Law.lawAvg S.law S.horizon (fun W => price W-S.specTheta)≤rate) : FtsBankSpec P :=
  { S with
    score := score
    covered := covered
    one_le_score := hscore
    score_append_mono := hmono
    price := price
    average_score := havg
    excessRate := rate
    excess_le := hrate }

noncomputable def nearLawSpec : FtsBankSpec Proposal :=
  withCoverage lawSpec nearScore NearCovered one_le_nearScore nearScore_append_mono
    nearPrice average_nearScore 351
    ((Law.lawAvg_mono honestLaw (2^32) (fun _ => tsub_le_self)).trans law_nearPrice_mean_bound)

#print axioms nearLawSpec
#print axioms nearCoveredAtP_source
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.WCTEnvelope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem wordDigit_coordinate_coeff (K : Nat) (hK : K ∈ [64,128])
    (r : Nat) (hr : r ≤ 20) (c : Nat) :
    (coordinatePoly K r).coeff c ≤
      (univ.filter fun E : Fin r → Fin K × Fin 563 =>
        coordinateCoverage ClaudeWCT.WCT9.wordDigit E=c).card := by
  have hpoly (j : Nat) (hj1 : 1 ≤ j) (hj8 : j ≤ 8) :
      lawPoly coverageLaw 563 j = naturalDataPoly (coverageHData j) :=
    lawPoly_eq_data coverageLaw 563 j
      (coverageLaw_eq_packed ClaudeWCT.WCT9.wordDigit wordsOf_wordDigit
        ClaudeWCT.WCT9.wordDigit_le_four (Fintype.card_fin 563)
        coverageH_packed j hj1 hj8)
      (coverageHData_bounds ⟨j, by omega⟩)
  exact coordinatePoly_coeff_below ClaudeWCT.WCT9.wordDigit coverageLaw
    (coverageLaw_correct ClaudeWCT.WCT9.wordDigit wordsOf_wordDigit
      ClaudeWCT.WCT9.wordDigit_le_four)
    (Fintype.card_fin 563) K hK ⟨r, by omega⟩ coverageLaw_zero_poly
    ((hpoly 1 (by decide) (by decide)).trans coverageH1_poly)
    (fun j hj1 hj8 => hpoly j (by omega) hj8) c

#print axioms wordDigit_coordinate_coeff
end ClaudeWCT.Numerics.SharedCoverage

namespace ClaudeWCT.Numerics.SharedFees
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.WCTEnvelope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem certifiedPayoff_global (r : Nat) (hr : r=0 ∨ 19≤r) :
    certifiedPayoff r=(maxFee*forestMoment r,scale*forestMoment r) := by
  rcases hr with h | h
  · subst r
    decide +kernel
  · have he : r=(r-19)+19 := by omega
    rw [he]
    rfl

theorem wordDigit_finite_payoffs
    (hrows : ∀ r, 1≤r → r≤18 → rowDots r=certifiedPayoff r)
    (r : Nat) (hr : r≤80) :
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (Real.exp (6*min ((734:ℝ)/2^66*(forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((certifiedPayoff r).1:ENNReal) ∧
    (∑ h : ForestHistory (Fin 563) r, ENNReal.ofReal
      (max 0 ((734:ℝ)/2^66*(forestCoverage ClaudeWCT.WCT9.wordDigit h : ℝ)-6/5))) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((certifiedPayoff r).2:ENNReal) := by
  have ht := forest_coverage_data ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
    w1Table_wordDigit rows_checked r (by omega)
  by_cases hg : r=0 ∨ 19≤r
  · rw [certifiedPayoff_global r hg]
    exact actual_forest_fee_global ClaudeWCT.WCT9.wordDigit r ht
  · have hlo : 1≤r := by omega
    have hhi : r≤18 := by omega
    have h := actual_forest_fee_row ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563)
      r hlo (by omega) (fun K hK u hu j =>
        wordDigit_coordinate_coeff K hK u (by omega) j) ht
    rwa [hrows r hlo hhi] at h

#print axioms certifiedPayoff_global
#print axioms wordDigit_finite_payoffs
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedPathForest
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem wordDigit_rowDots_convolution (r : Nat) (hr : r≤20) :
    rowDots r=convolutionDots r (SharedPathPacked.forest r) := by
  have hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K × Fin 563 =>
        coordinateCoverage ClaudeWCT.WCT9.wordDigit E=j).card :=
    fun K hK u hu j => wordDigit_coordinate_coeff K hK u (by omega) j
  exact rowDots_convolution r hr (actualPoly r)
    (actual_encoding ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp)
    (actual_coeff_small ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp)
    ((actual_mass_le ClaudeWCT.WCT9.wordDigit (Fintype.card_fin 563) r hr hp).trans
      (forest_mass_3072 r hr))

#print axioms wordDigit_rowDots_convolution
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem smallRows_checked (r : Nat) (hr : r≤4) : rowDots r=certifiedPayoff r := by
  interval_cases r
  · exact row_0
  · exact row_1
  · exact row_2
  · exact row_3
  · exact row_4

theorem wordDigit_rows_of_convolutions
    (hconv : ∀ r, 5≤r → r≤18 →
      convolutionDots r (SharedPathPacked.forest r)=certifiedPayoff r)
    (r : Nat) (hlo : 1≤r) (hhi : r≤18) : rowDots r=certifiedPayoff r := by
  by_cases hs : r≤4
  · exact smallRows_checked r hs
  · exact (wordDigit_rowDots_convolution r (by omega)).trans (hconv r (by omega) hhi)

#print axioms smallRows_checked
#print axioms wordDigit_rows_of_convolutions
end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Bank.Paired
open ClaudeWCT.Numerics

theorem finiteFees_of_convolutions
    (hconv : ∀ r, 5≤r → r≤18 →
      SharedFees.convolutionDots r (SharedPathPacked.forest r)=SharedFees.certifiedPayoff r) :
    FiniteFeeBound :=
  finiteFees_of_real (fun r hr => SharedFees.wordDigit_finite_payoffs
    (SharedFees.wordDigit_rows_of_convolutions hconv) r hr)

#print axioms finiteFees_of_convolutions
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
/-- Every row in the exact paired-forest fee envelope is kernel checked. -/
theorem finiteFees_checked : FiniteFeeBound :=
  finiteFees_of_convolutions ClaudeWCT.Numerics.SharedGeneratedForest.convolution_rows_checked
#print axioms finiteFees_checked
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open ENNReal Finset ClaudeWCT.Numerics
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Cap 777: the tiny threshold has its own endpoint (exact value `0.0012037 ≤ 18/5000`); the old
middle/low interpolation would give `0.003614 > 18/5000` with the new middle value. -/
theorem excess_tiny_certified (hfees : FiniteFeeBound) :
    Law.lawAvg honestLaw (2^32)
      (fun W=>price W-ENNReal.ofReal ((249:ℝ)/125-1/1024)) ≤
        ENNReal.ofReal ((18:ℝ)/5000) :=
  price_excess_certified hfees _ _ (by norm_num) SharedPathWinsor.Rows18Thin.endpoint_tiny
#print axioms excess_tiny_certified
end ClaudeWCT.Bank.Paired
