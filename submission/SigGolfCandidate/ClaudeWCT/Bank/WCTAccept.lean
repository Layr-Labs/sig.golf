import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.ClaudeWCT.Bank.WCTSpec

section
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev DigestCoordinates := (Fin (2 ^ 31) × BitVec 12) ×
  (Coord → Fin 128 × Fin 16384) × (BitVec 1 × BitVec 1 × BitVec 1 × Fin (2 ^ 21))
def digestCoordinates (output : HashOutput) : DigestCoordinates :=
  (((output.extractLsb' 33 31).toFin, output.extractLsb' 21 12),
    (fun coord => ((output.extractLsb' (childBase coord.val) 7).toFin,
      (output.extractLsb' (fieldBase coord.val) 14).toFin)),
    (output.extractLsb' 106 1, output.extractLsb' 170 1, output.extractLsb' 234 1,
      (output.extractLsb' 235 21).toFin))
def admissibleView (view : DigestCoordinates) : Bool :=
  decide (view.2.2.2.2.2.val < 1092) &&
    (List.finRange 9).all (fun coord => decide ((view.2.1 coord).2.val < 16200))
theorem bit_cover : ∀ position, position < 256 →
    (33 ≤ position ∧ position < 64) ∨ (21 ≤ position ∧ position < 33) ∨ position = 106 ∨ position = 170 ∨
      position = 234 ∨ 235 ≤ position ∨
      (∃ coord : Coord, childBase coord.val ≤ position ∧ position < childBase coord.val + 7) ∨
      ∃ coord : Coord, fieldBase coord.val ≤ position ∧ position < fieldBase coord.val + 14 := by
  decide
theorem digestCoordinates_injective : Function.Injective digestCoordinates := by
  intro left right he
  apply BitVec.eq_of_getLsbD_eq
  intro position hp
  rcases bit_cover position hp with hindex | hunused | h106 | h170 | h234 | hgate | ⟨coord, hlo, hhi⟩ |
      ⟨coord, hlo, hhi⟩
  · have hc := congrArg (fun x : DigestCoordinates => (BitVec.ofFin x.1.1 : BitVec 31)) he
    change left.extractLsb' 33 31 = right.extractLsb' 33 31 at hc
    have hb := congrArg (fun bits : BitVec 31 => bits.getLsbD (position - 33)) hc
    have hbit : position - 33 < 31 := by omega
    have hoff : 33 + (position - 33) = position := by omega
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · have hc := congrArg (fun x : DigestCoordinates => x.1.2) he
    change left.extractLsb' 21 12 = right.extractLsb' 21 12 at hc
    have hb := congrArg (fun bits : BitVec 12 => bits.getLsbD (position - 21)) hc
    have hbit : position - 21 < 12 := by omega
    have hoff : 21 + (position - 21) = position := by omega
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · subst position
    have hc := congrArg (fun x : DigestCoordinates => x.2.2.1) he
    change left.extractLsb' 106 1 = right.extractLsb' 106 1 at hc
    have hb := congrArg (fun bits : BitVec 1 => bits.getLsbD 0) hc
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_lt_one, decide_true, Bool.true_and,
      Nat.add_zero] using hb
  · subst position
    have hc := congrArg (fun x : DigestCoordinates => x.2.2.2.1) he
    change left.extractLsb' 170 1 = right.extractLsb' 170 1 at hc
    have hb := congrArg (fun bits : BitVec 1 => bits.getLsbD 0) hc
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_lt_one, decide_true, Bool.true_and,
      Nat.add_zero] using hb
  · subst position
    have hc := congrArg (fun x : DigestCoordinates => x.2.2.2.2.1) he
    change left.extractLsb' 234 1 = right.extractLsb' 234 1 at hc
    have hb := congrArg (fun bits : BitVec 1 => bits.getLsbD 0) hc
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_lt_one, decide_true, Bool.true_and,
      Nat.add_zero] using hb
  · have hc := congrArg (fun x : DigestCoordinates => (BitVec.ofFin x.2.2.2.2.2 : BitVec 21)) he
    change left.extractLsb' 235 21 = right.extractLsb' 235 21 at hc
    have hb := congrArg (fun bits : BitVec 21 => bits.getLsbD (position - 235)) hc
    have hbit : position - 235 < 21 := by omega
    have hoff : 235 + (position - 235) = position := by omega
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · let within := position - childBase coord.val
    have hbit : within < 7 := by dsimp only [within]; omega
    have hoff : childBase coord.val + within = position := by dsimp only [within]; omega
    have hc := congrArg (fun x : DigestCoordinates =>
      (BitVec.ofFin (x.2.1 coord).1 : BitVec 7)) he
    change left.extractLsb' (childBase coord.val) 7 =
      right.extractLsb' (childBase coord.val) 7 at hc
    have hb := congrArg (fun bits : BitVec 7 => bits.getLsbD within) hc
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · let within := position - fieldBase coord.val
    have hbit : within < 14 := by dsimp only [within]; omega
    have hoff : fieldBase coord.val + within = position := by dsimp only [within]; omega
    have hc := congrArg (fun x : DigestCoordinates =>
      (BitVec.ofFin (x.2.1 coord).2 : BitVec 14)) he
    change left.extractLsb' (fieldBase coord.val) 14 =
      right.extractLsb' (fieldBase coord.val) 14 at hc
    have hb := congrArg (fun bits : BitVec 14 => bits.getLsbD within) hc
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
theorem digestCoordinates_bijective : Function.Bijective digestCoordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨digestCoordinates_injective, ?_⟩
  simp only [DigestCoordinates, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bitVec]
  norm_num
theorem index_decode (output : HashOutput) :
    (digestCoordinates output).1.1.val = digestIndex output := by
  simp only [digestCoordinates, digestIndex, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem gate_decode (output : HashOutput) :
    (digestCoordinates output).2.2.2.2.2.val = output.toNat / 2 ^ 235 % 2 ^ 21 := by
  simp only [digestCoordinates, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem child_decode (output : HashOutput) (coord : Coord) :
    ((digestCoordinates output).2.1 coord).1 = child output coord := by
  apply Fin.ext
  simp only [digestCoordinates, child, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem field_decode (output : HashOutput) (coord : Coord) :
    ((digestCoordinates output).2.1 coord).2.val = field output coord := by
  simp only [digestCoordinates, field, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem rank_decode (output : HashOutput) (coord : Coord) :
    (rank output coord).val = ((digestCoordinates output).2.1 coord).2.val % 600 := by
  rw [field_decode, rank_val]
theorem admissible_decode (output : HashOutput) :
    admissibleView (digestCoordinates output) = admissible output := by
  rw [Bool.eq_iff_iff, admissible_iff]
  unfold admissibleView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_true_left, gate_decode, field_decode]
theorem uniform_coordinates :
    𝒮[digestCoordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ DigestCoordinates : ProbComp DigestCoordinates)] := by
  exact evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := DigestCoordinates)
    digestCoordinates digestCoordinates_bijective
end ClaudeWCT.WCT9
end
section
namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open ClaudeWCT.WCT9 (Coord Child Rank child rank DigestCoordinates digestCoordinates admissibleView)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def viewProposal (v : DigestCoordinates) : WProposal :=
  (v.1.1, fun k => ((v.2.1 k).1, ⟨(v.2.1 k).2.val % 600, Nat.mod_lt _ (by decide)⟩))
theorem viewProposal_decode (x : HashOutput) : viewProposal (digestCoordinates x) = proposal x := by
  refine Prod.ext (Fin.ext ?_) (funext fun k => Prod.ext (WCT9.child_decode x k) (Fin.ext ?_))
  · exact WCT9.index_decode x
  · exact (WCT9.rank_decode x k).symm
theorem admissibleView_iff (v : DigestCoordinates) :
    admissibleView v = true ↔ v.2.2.2.2.2.val < 1092 ∧ ∀ k : Coord, (v.2.1 k).2.val < 16200 := by
  unfold admissibleView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_true_left]
abbrev FibreData := (Coord → Fin 27) × Fin 1092 × (BitVec 12 × BitVec 1 × BitVec 1 × BitVec 1)
def fibreEquiv (p : WProposal) :
    {v : DigestCoordinates // admissibleView v = true ∧ viewProposal v = p} ≃ FibreData where
  toFun v := (fun k => ⟨(v.1.2.1 k).2.val / 600, by
      have := ((admissibleView_iff v.1).1 v.2.1).2 k
      omega⟩, ⟨v.1.2.2.2.2.2.val, ((admissibleView_iff v.1).1 v.2.1).1⟩,
      (v.1.1.2, v.1.2.2.1, v.1.2.2.2.1, v.1.2.2.2.2.1))
  invFun s := ⟨((p.1, s.2.2.1), fun k => ((p.2 k).1, ⟨(p.2 k).2.val + 600 * (s.1 k).val, by
      have h1 := (p.2 k).2.isLt
      have h2 := (s.1 k).isLt
      omega⟩), (s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2, ⟨s.2.1.val, by have := s.2.1.isLt; omega⟩)), by
    refine ⟨(admissibleView_iff _).2 ⟨s.2.1.isLt, fun k => ?_⟩, ?_⟩
    · have h1 := (p.2 k).2.isLt
      have h2 := (s.1 k).isLt
      show (p.2 k).2.val + 600 * (s.1 k).val < 16200
      omega
    · refine Prod.ext rfl (funext fun k => Prod.ext rfl (Fin.ext ?_))
      have h1 := (p.2 k).2.isLt
      show ((p.2 k).2.val + 600 * (s.1 k).val) % 600 = (p.2 k).2.val
      omega⟩
  left_inv v := by
    obtain ⟨⟨⟨i, u⟩, f, b1, b2, b3, g⟩, hadm, hp⟩ := v
    subst hp
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext (funext fun k => Prod.ext rfl (Fin.ext ?_)) rfl)
    show (f k).2.val % 600 + 600 * ((f k).2.val / 600) = (f k).2.val
    omega
  right_inv s := by
    obtain ⟨q, g, u, b1, b2, b3⟩ := s
    refine Prod.ext (funext fun k => Fin.ext ?_) rfl
    have h1 := (p.2 k).2.isLt
    show ((p.2 k).2.val + 600 * (q k).val) / 600 = (q k).val
    omega
theorem card_fibreData : Fintype.card FibreData = 27 ^ 9 * 1092 * 2 ^ 15 := by
  simp only [FibreData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  norm_num
theorem card_fibre (p : WProposal) :
    (Finset.univ.filter (fun x : HashOutput => WCT9.admissible x = true ∧ proposal x = p)).card =
      27 ^ 9 * 1092 * 2 ^ 15 := by
  have e : {x : HashOutput // WCT9.admissible x = true ∧ proposal x = p} ≃
      {v : DigestCoordinates // admissibleView v = true ∧ viewProposal v = p} :=
    (Equiv.ofBijective digestCoordinates WCT9.digestCoordinates_bijective).subtypeEquiv
      (fun x => by
        change WCT9.admissible x = true ∧ proposal x = p ↔
          admissibleView (digestCoordinates x) = true ∧ viewProposal (digestCoordinates x) = p
        rw [WCT9.admissible_decode, viewProposal_decode])
  have hc := Fintype.card_congr (e.trans (fibreEquiv p))
  rw [card_fibreData, Fintype.card_subtype] at hc
  exact hc
theorem sum_admissible (g : WProposal → ENNReal) :
    (∑ x : HashOutput, if WCT9.admissible x = true then g (proposal x) else 0) =
      ((27 ^ 9 * 1092 * 2 ^ 15 : Nat) : ENNReal) * ∑ p, g p := by
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise _ proposal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
    Finset.filter_filter, card_fibre, nsmul_eq_mul]
theorem sum_admissible_one :
    (∑ x : HashOutput, if WCT9.admissible x = true then (1 : ENNReal) else 0) =
      ((27 ^ 9 * 1092 * 2 ^ 15 : Nat) : ENNReal) * (Fintype.card WProposal : ENNReal) := by
  rw [sum_admissible (fun _ => 1), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
theorem acceptance_eq_ratio :
    Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((27 ^ 9 * 1092 * 2 ^ 15 : Nat) : ENNReal) * (Fintype.card WProposal : ENNReal) /
        (Fintype.card HashOutput : ENNReal) := by
  rw [← expectedValue_ite_one, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_admissible_one]
theorem acceptedProposalUniform : AcceptedProposalUniform := by
  intro g
  rw [acceptance_eq_ratio, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_admissible]
  have hP : (Fintype.card WProposal : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hP' : (Fintype.card WProposal : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [div_eq_mul_inv]
  calc ((27 ^ 9 * 1092 * 2 ^ 15 : Nat) : ENNReal) * (∑ p, g p) * (Fintype.card HashOutput : ENNReal)⁻¹
      = ((27 ^ 9 * 1092 * 2 ^ 15 : Nat) : ENNReal) * (∑ p, g p) * (Fintype.card HashOutput : ENNReal)⁻¹ *
          ((Fintype.card WProposal : ENNReal)⁻¹ * (Fintype.card WProposal : ENNReal)) := by
        rw [ENNReal.inv_mul_cancel hP hP', mul_one]
    _ = _ := by ring
theorem acceptance_eq :
    Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (1092 * 16200 ^ 9 : ENNReal) / 2 ^ 147 := by
  rw [acceptance_eq_ratio]
  simp only [WProposal, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num
theorem acceptanceBound : AcceptanceBound := by
  unfold AcceptanceBound
  rw [acceptance_eq]
  have h0 : (1092 * 16200 ^ 9 : ENNReal) ≤ 2 ^ 141 := by
    exact_mod_cast (show (1092 * 16200 ^ 9 : Nat) ≤ 2 ^ 141 by norm_num)
  have h : (1092 * 16200 ^ 9 : ENNReal) / 2 ^ 147 ≤ 2 ^ 141 / 2 ^ 147 := ENNReal.div_le_div_right h0 _
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num
end ClaudeWCT.Bank.WCT
end
