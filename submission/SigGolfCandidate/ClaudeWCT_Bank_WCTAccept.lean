import SigGolfCandidate.Research_V7Composed198Gate
import SigGolfCandidate.ClaudeWCT_WCT9_Basic
import SigGolfCandidate.ClaudeWCT_Bank_WCTSpec

section
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev DigestCoordinates := Fin (2 ^ 31) × (Coord → Fin 128 × Fin 1024) × (Fin 58 → Bool) × Fin (2 ^ 14)
def unusedBits : List Nat :=
  (List.range 16).map (· + 17) ++ (List.range 4).map (· + 81) ++ (List.range 5).map (· + 102) ++
    (List.range 4).map (· + 117) ++ (List.range 4).map (· + 145) ++ (List.range 5).map (· + 166) ++
    (List.range 4).map (· + 181) ++ (List.range 4).map (· + 209) ++ (List.range 12).map (· + 230)
def unusedPos (i : Fin 58) : Nat := unusedBits.getD i.val 0
def digestCoordinates (output : HashOutput) : DigestCoordinates :=
  ((output.extractLsb' 33 31).toFin,
    (fun coord => ((output.extractLsb' (childBase coord.val) 7).toFin,
      (output.extractLsb' (fieldBase coord.val) 10).toFin)),
    (fun i => output.getLsbD (unusedPos i)),
    (output.extractLsb' 242 14).toFin)
def admissibleView (view : DigestCoordinates) : Bool :=
  decide (view.2.2.2.val < WCT9.gateLimit) &&
    (List.finRange 9).all (fun coord => decide ((view.2.1 coord).2.val < 563))
theorem bit_cover : ∀ position, position < 256 →
    (33 ≤ position ∧ position < 64) ∨ 242 ≤ position ∨
      (∃ coord : Coord, childBase coord.val ≤ position ∧ position < childBase coord.val + 7) ∨
      (∃ coord : Coord, fieldBase coord.val ≤ position ∧ position < fieldBase coord.val + 10) ∨
      ∃ i : Fin 58, unusedPos i = position := by
  decide +kernel
theorem digestCoordinates_injective : Function.Injective digestCoordinates := by
  intro left right he
  apply BitVec.eq_of_getLsbD_eq
  intro position hp
  rcases bit_cover position hp with hindex | hgate | ⟨coord, hlo, hhi⟩ | ⟨coord, hlo, hhi⟩ | ⟨i, hi⟩
  · have hc := congrArg (fun x : DigestCoordinates => (BitVec.ofFin x.1 : BitVec 31)) he
    change left.extractLsb' 33 31 = right.extractLsb' 33 31 at hc
    have hb := congrArg (fun bits : BitVec 31 => bits.getLsbD (position - 33)) hc
    have hbit : position - 33 < 31 := by omega
    have hoff : 33 + (position - 33) = position := by omega
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · have hc := congrArg (fun x : DigestCoordinates => (BitVec.ofFin x.2.2.2 : BitVec 14)) he
    change left.extractLsb' 242 14 = right.extractLsb' 242 14 at hc
    have hb := congrArg (fun bits : BitVec 14 => bits.getLsbD (position - 242)) hc
    have hbit : position - 242 < 14 := by omega
    have hoff : 242 + (position - 242) = position := by omega
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
    have hbit : within < 10 := by dsimp only [within]; omega
    have hoff : fieldBase coord.val + within = position := by dsimp only [within]; omega
    have hc := congrArg (fun x : DigestCoordinates =>
      (BitVec.ofFin (x.2.1 coord).2 : BitVec 10)) he
    change left.extractLsb' (fieldBase coord.val) 10 =
      right.extractLsb' (fieldBase coord.val) 10 at hc
    have hb := congrArg (fun bits : BitVec 10 => bits.getLsbD within) hc
    simpa only [BitVec.getLsbD_extractLsb', hbit, decide_true, Bool.true_and, hoff] using hb
  · have hc := congrArg (fun x : DigestCoordinates => x.2.2.1 i) he
    change left.getLsbD (unusedPos i) = right.getLsbD (unusedPos i) at hc
    rw [hi] at hc
    exact hc
theorem digestCoordinates_bijective : Function.Bijective digestCoordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨digestCoordinates_injective, ?_⟩
  simp only [DigestCoordinates, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bitVec, Fintype.card_bool]
  norm_num
theorem index_decode (output : HashOutput) :
    (digestCoordinates output).1.val = digestIndex output := by
  simp only [digestCoordinates, digestIndex, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
theorem gate_decode (output : HashOutput) :
    (digestCoordinates output).2.2.2.val = output.toNat / 2 ^ 242 % 2 ^ 14 := by
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
    (rank output coord).val = ((digestCoordinates output).2.1 coord).2.val % 563 := by
  rw [field_decode, rank_val]
theorem admissible_decode (output : HashOutput) :
    admissibleView (digestCoordinates output) = admissible output := by
  rw [Bool.eq_iff_iff, admissible_iff]
  unfold admissibleView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_true_left, gate_decode, field_decode, gateLimit]
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
  (v.1, fun k => ((v.2.1 k).1, ⟨(v.2.1 k).2.val % 563, Nat.mod_lt _ (by decide)⟩))
theorem viewProposal_decode (x : HashOutput) : viewProposal (digestCoordinates x) = proposal x := by
  refine Prod.ext (Fin.ext ?_) (funext fun k => Prod.ext (WCT9.child_decode x k) (Fin.ext ?_))
  · exact WCT9.index_decode x
  · exact (WCT9.rank_decode x k).symm
theorem admissibleView_iff (v : DigestCoordinates) :
    admissibleView v = true ↔ v.2.2.2.val < WCT9.gateLimit ∧ ∀ k : Coord, (v.2.1 k).2.val < 563 := by
  unfold admissibleView
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_true_left]
abbrev FibreData := Fin WCT9.gateLimit × (Fin 58 → Bool)
def fibreEquiv (p : WProposal) :
    {v : DigestCoordinates // admissibleView v = true ∧ viewProposal v = p} ≃ FibreData where
  toFun v := (⟨v.1.2.2.2.val, ((admissibleView_iff v.1).1 v.2.1).1⟩, v.1.2.2.1)
  invFun s := ⟨(p.1, fun k => ((p.2 k).1, ⟨(p.2 k).2.val, by
      have h1 := (p.2 k).2.isLt
      omega⟩), s.2, ⟨s.1.val, by
        have := s.1.isLt
        have hgate : WCT9.gateLimit ≤ 2 ^ 14 := by decide
        omega⟩), by
    refine ⟨(admissibleView_iff _).2 ⟨s.1.isLt, fun k => (p.2 k).2.isLt⟩, ?_⟩
    refine Prod.ext rfl (funext fun k => Prod.ext rfl (Fin.ext ?_))
    exact Nat.mod_eq_of_lt (p.2 k).2.isLt⟩
  left_inv v := by
    obtain ⟨⟨i, f, u, g⟩, hadm, hp⟩ := v
    subst hp
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext (funext fun k => Prod.ext rfl (Fin.ext ?_)) rfl)
    exact Nat.mod_eq_of_lt (((admissibleView_iff _).1 hadm).2 k)
  right_inv s := rfl
theorem card_fibreData : Fintype.card FibreData = WCT9.gateLimit * 2 ^ 58 := by
  simp only [FibreData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
theorem card_fibre (p : WProposal) :
    (Finset.univ.filter (fun x : HashOutput => WCT9.admissible x = true ∧ proposal x = p)).card =
      WCT9.gateLimit * 2 ^ 58 := by
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
      ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * ∑ p, g p := by
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise _ proposal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
    Finset.filter_filter, card_fibre, nsmul_eq_mul]
theorem sum_admissible_one :
    (∑ x : HashOutput, if WCT9.admissible x = true then (1 : ENNReal) else 0) =
      ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (Fintype.card WProposal : ENNReal) := by
  rw [sum_admissible (fun _ => 1), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
theorem acceptance_eq_ratio :
    Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (Fintype.card WProposal : ENNReal) /
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
  calc ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (∑ p, g p) * (Fintype.card HashOutput : ENNReal)⁻¹
      = ((WCT9.gateLimit * 2 ^ 58 : Nat) : ENNReal) * (∑ p, g p) * (Fintype.card HashOutput : ENNReal)⁻¹ *
          ((Fintype.card WProposal : ENNReal)⁻¹ * (Fintype.card WProposal : ENNReal)) := by
        rw [ENNReal.inv_mul_cancel hP hP', mul_one]
    _ = _ := by ring
theorem acceptance_eq :
    Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (WCT9.gateLimit * 563 ^ 9 : ENNReal) / 2 ^ 104 := by
  rw [acceptance_eq_ratio]
  simp only [WProposal, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num
  ring
theorem acceptanceBound : AcceptanceBound := by
  unfold AcceptanceBound
  rw [acceptance_eq]
  have h0 : (WCT9.gateLimit * 563 ^ 9 : ENNReal) ≤ 2 ^ 98 := by
    exact_mod_cast (show (WCT9.gateLimit * 563 ^ 9 : Nat) ≤ 2 ^ 98 by norm_num [WCT9.gateLimit])
  have h : (WCT9.gateLimit * 563 ^ 9 : ENNReal) / 2 ^ 104 ≤ 2 ^ 98 / 2 ^ 104 := ENNReal.div_le_div_right h0 _
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num
end ClaudeWCT.Bank.WCT
end

/-! Exact digest fibers for the paired shared-path forest. -/
namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev PairSelector := Fin 2 × Fin 64 × Fin 64
abbrev Selectors := (Fin 4 → PairSelector) × Fin 128
abbrev RawFields := Selectors × (Fin 9 → Fin 1024) × Fin (2^31) × Fin (2^14)
abbrev Coordinates := RawFields × (Fin 62 → Bool)
def rankBase (k : Nat) : Nat := [13,77,89,101,141,153,165,205,217].getD k 0
def spareBase (k : Nat) : Nat := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 87, 88, 99, 100, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 151, 152, 163, 164, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 215, 216, 227, 228, 236, 237, 238, 239, 240, 241].getD k 0
def position (i : Nat) : Nat :=
  if i < 52 then 64*(i/13)+i%13
  else if i < 59 then 229+(i-52)
  else if i < 149 then rankBase ((i-59)/10)+(i-59)%10
  else if i < 180 then 33+(i-149)
  else if i < 194 then 242+(i-180)
  else spareBase (i-194)
def inversePosition (k : Nat) : Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 204, 205, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 206, 207, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 225, 226, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 227, 228, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 246, 247, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 248, 249, 52, 53, 54, 55, 56, 57, 58, 250, 251, 252, 253, 254, 255, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193].getD k 0
theorem inverse_bound : ∀ k : Fin 256, inversePosition k.val < 256 := by decide +kernel
theorem inverse_correct : ∀ k : Fin 256, position (inversePosition k.val) = k.val := by decide +kernel

def rawFields (a : HashOutput) : RawFields :=
  ((fun k => ((a.extractLsb' (64*k.val+6) 1).toFin,
      (a.extractLsb' (64*k.val) 6).toFin, (a.extractLsb' (64*k.val+7) 6).toFin),
    (a.extractLsb' 229 7).toFin),
    fun k => (a.extractLsb' (rankBase k.val) 10).toFin,
    (a.extractLsb' 33 31).toFin, (a.extractLsb' 242 14).toFin)
def coordinates (a : HashOutput) : Coordinates :=
  (rawFields a, fun k => a.getLsbD (spareBase k.val))

theorem coordinates_injective : Function.Injective coordinates := by
  intro a b he
  have hb : ∀ i : Fin 256, a.getLsbD (position i.val) = b.getLsbD (position i.val) := by
    intro i
    unfold position
    split_ifs with h0 h1 h2 h3 h4
    · have hk : i.val/13<4 := by omega
      by_cases hsmall : i.val%13<6
      · have e := congrArg (fun v : Coordinates =>
          (BitVec.ofFin (v.1.1.1 ⟨i.val/13,hk⟩).2.1 : BitVec 6).getLsbD (i.val%13)) he
        simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
          BitVec.getLsbD_extractLsb', hsmall, decide_true, Bool.true_and] using e
      · by_cases hmid : i.val%13=6
        · have e := congrArg (fun v : Coordinates =>
            (BitVec.ofFin (v.1.1.1 ⟨i.val/13,hk⟩).1 : BitVec 1).getLsbD 0) he
          simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
            BitVec.getLsbD_extractLsb', Nat.zero_lt_succ, decide_true, Bool.true_and,
            Nat.add_zero, hmid] using e
        · have hwithin : i.val%13-7<6 := by omega
          have hoff : 64*(i.val/13)+7+(i.val%13-7)=64*(i.val/13)+i.val%13 := by omega
          have e := congrArg (fun v : Coordinates =>
            (BitVec.ofFin (v.1.1.1 ⟨i.val/13,hk⟩).2.2 : BitVec 6).getLsbD (i.val%13-7)) he
          simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
            BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and, hoff] using e
    · have hk : i.val-52<7 := by omega
      have e := congrArg (fun v : Coordinates =>
        (BitVec.ofFin v.1.1.2 : BitVec 7).getLsbD (i.val-52)) he
      simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
        BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : (i.val-59)/10<9 := by omega
      have e := congrArg (fun v : Coordinates =>
        (BitVec.ofFin (v.1.2.1 ⟨(i.val-59)/10,hk⟩) : BitVec 10).getLsbD ((i.val-59)%10)) he
      simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
        BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0<10), decide_true, Bool.true_and] using e
    · have hk : i.val-149<31 := by omega
      have e := congrArg (fun v : Coordinates =>
        (BitVec.ofFin v.1.2.2.1 : BitVec 31).getLsbD (i.val-149)) he
      simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
        BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-180<14 := by omega
      have e := congrArg (fun v : Coordinates =>
        (BitVec.ofFin v.1.2.2.2 : BitVec 14).getLsbD (i.val-180)) he
      simpa only [coordinates, rawFields, BitVec.ofFin_toFin,
        BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and] using e
    · have hk : i.val-194<62 := by omega
      exact congrArg (fun v : Coordinates => v.2 ⟨i.val-194,hk⟩) he
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := hb ⟨inversePosition i,inverse_bound ⟨i,hi⟩⟩
  simpa only [inverse_correct ⟨i,hi⟩] using e

theorem coordinates_bijective : Function.Bijective coordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨coordinates_injective, ?_⟩
  simp only [Coordinates, RawFields, Selectors, PairSelector,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec, Fintype.card_bool]
  norm_num
noncomputable def coordinatesEquiv : HashOutput ≃ Coordinates :=
  Equiv.ofBijective coordinates coordinates_bijective

theorem uniform_coordinates :
    𝒮[coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ Coordinates : ProbComp Coordinates)] :=
  evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := Coordinates) coordinates coordinates_bijective
end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev Alphabet := Selectors × (Fin 9 → Fin 563)
abbrev Proposal := Fin (2^31) × Alphabet

def viewProposal (v : Coordinates) : Proposal :=
  (v.1.2.2.1, v.1.1, fun k => ⟨(v.1.2.1 k).val % 563, Nat.mod_lt _ (by decide)⟩)
def proposal (a : HashOutput) : Proposal := viewProposal (coordinates a)
def admissibleView (v : Coordinates) : Bool :=
  decide (v.1.2.2.2.val < 791) && (List.finRange 9).all (fun k => decide ((v.1.2.1 k).val < 563))
def admissible (a : HashOutput) : Bool := admissibleView (coordinates a)

theorem admissibleView_iff (v : Coordinates) :
    admissibleView v = true ↔ v.1.2.2.2.val < 791 ∧ ∀ k : Fin 9, (v.1.2.1 k).val < 563 := by
  simp only [admissibleView, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_true_left]
abbrev FibreData := Fin 791 × (Fin 62 → Bool)
def fibreEquiv (p : Proposal) :
    {v : Coordinates // admissibleView v = true ∧ viewProposal v = p} ≃ FibreData where
  toFun v := (⟨v.1.1.2.2.2.val, ((admissibleView_iff v.1).1 v.2.1).1⟩, v.1.2)
  invFun s := ⟨((p.2.1, fun k => ⟨(p.2.2 k).val, by have := (p.2.2 k).isLt; omega⟩,
    p.1, ⟨s.1.val, by have := s.1.isLt; omega⟩), s.2), by
    refine ⟨(admissibleView_iff _).2 ⟨s.1.isLt, fun k => (p.2.2 k).isLt⟩, ?_⟩
    refine Prod.ext rfl (Prod.ext rfl (funext fun k => Fin.ext ?_))
    exact Nat.mod_eq_of_lt (p.2.2 k).isLt⟩
  left_inv v := by
    obtain ⟨⟨⟨sel, ranks, i, g⟩, spare⟩, hadm, hp⟩ := v
    subst hp
    apply Subtype.ext
    refine Prod.ext (Prod.ext rfl (Prod.ext (funext fun k => Fin.ext ?_) rfl)) rfl
    exact Nat.mod_eq_of_lt (((admissibleView_iff _).1 hadm).2 k)
  right_inv s := rfl

theorem card_fibre (p : Proposal) :
    (Finset.univ.filter (fun a : HashOutput => admissible a = true ∧ proposal a = p)).card =
      791 * 2^62 := by
  have e : {a : HashOutput // admissible a = true ∧ proposal a = p} ≃
      {v : Coordinates // admissibleView v = true ∧ viewProposal v = p} :=
    coordinatesEquiv.subtypeEquiv (fun _ => Iff.rfl)
  have hc := Fintype.card_congr (e.trans (fibreEquiv p))
  simpa only [FibreData, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_subtype] using hc

theorem sum_admissible (g : Proposal → ENNReal) :
    (∑ a : HashOutput, if admissible a = true then g (proposal a) else 0) =
      ((791 * 2^62 : Nat) : ENNReal) * ∑ p, g p := by
  rw [← Finset.sum_filter, ← Finset.sum_fiberwise _ proposal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]),
    Finset.sum_const, Finset.filter_filter, card_fibre, nsmul_eq_mul]

theorem acceptance_eq :
    Pr[fun a : HashOutput => admissible a = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (791 * 563^9 : ENNReal) / 2^104 := by
  rw [← expectedValue_ite_one, BPORS.expected_uniform_eq_finiteAverage]
  unfold SigGolfResearch.Gate6.Moments.finiteAverage
  rw [sum_admissible (fun _ => 1), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  simp only [Proposal, Alphabet, Selectors, PairSelector, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bitVec]
  rw [ENNReal.div_eq_div_iff (by positivity) (by finiteness) (by positivity) (by finiteness)]
  norm_num

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.Research
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def lowField (s : Selectors) (k : Fin 9) : Nat :=
  if h : k.val < 8 then
    let pair := s.1 ⟨k.val/2,by omega⟩
    if k.val % 2 = 0 then pair.2.1.val % 32 else pair.2.2.val % 32
  else s.2.val / 2 % 32

def coordinateCost (a : Alphabet) (k : Fin 9) : Nat :=
  ClaudeWCT.WCT9.routineCost (a.2 k) +
    if SharedForest.firstCoord k.val then SharedForest.aCorrection (lowField a.1 k)
    else SharedForest.bCorrection (lowField a.1 k)
def cost (a : Alphabet) : Nat := ((List.finRange 9).map (coordinateCost a)).sum
/-- The producer's joint cap 777 (`SharedForest.digestAccepted`). -/
def capOk (a : Alphabet) : Bool := decide (cost a ≤ 777)
def producer (a : HashOutput) : Bool := admissible a && capOk (proposal a).2

theorem proposal_index (a : HashOutput) : (proposal a).1.val = ClaudeWCT.WCT9.digestIndex a := by
  simp only [proposal, viewProposal, coordinates, rawFields, BitVec.val_toFin,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem proposal_rank (a : HashOutput) (k : Fin 9) :
    (proposal a).2.2 k = SharedForest.forestRank a k.val := by
  apply Fin.ext
  simp only [proposal, viewProposal, coordinates, rawFields, BitVec.val_toFin,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem proposal_lowField (a : HashOutput) (k : Fin 9) :
    lowField (proposal a).2.1 k = (SharedForest.costField a k).val := by
  fin_cases k <;>
    simp only [lowField, proposal, viewProposal, coordinates, rawFields,
      SharedForest.costField, SharedForest.costFieldBase, SharedForest.rawChildBase,
      SharedForest.firstCoord, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, BitVec.val_toFin, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  all_goals norm_num
  all_goals omega

theorem coordinateCost_source (a : HashOutput) (k : Fin 9) :
    coordinateCost (proposal a).2 k = SharedForest.coordinateAccountingCost a k := by
  rw [coordinateCost, proposal_rank, proposal_lowField]
  rw [SharedForest.coordinateAccountingCost, SharedForest.accountingCorrection_field]

theorem cost_source (a : HashOutput) : cost (proposal a).2 = SharedForest.jointAccountingCost a := by
  have h : coordinateCost (proposal a).2 = SharedForest.coordinateAccountingCost a :=
    funext (coordinateCost_source a)
  simp only [cost, SharedForest.jointAccountingCost, h]

theorem admissible_source (a : HashOutput) :
    admissible a = (decide (a.toNat/2^242%16384 < 791) && SharedForest.ranksAccepted a) := by
  simp only [admissible, admissibleView, coordinates, rawFields, BitVec.val_toFin,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rfl

theorem producer_source (a : HashOutput) : producer a = SharedForest.digestAccepted a := by
  rw [producer, admissible_source, capOk, cost_source]
  rfl

end ClaudeWCT.Bank.Paired

namespace ClaudeWCT.Bank.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rawChild (s : Selectors) (k : Fin 9) : Fin 128 :=
  if hk : k.val<8 then
    let p := s.1 ⟨k.val/2,by omega⟩
    if k.val%2=0 then ⟨64*p.1.val+p.2.1.val,by have := p.1.isLt; have := p.2.1.isLt; omega⟩
    else ⟨2*p.2.2.val+p.1.val,by have := p.1.isLt; have := p.2.2.isLt; omega⟩
  else s.2

theorem proposal_child (a : HashOutput) (k : Fin 9) :
    rawChild (proposal a).2.1 k = SharedForest.rawChildFromOutput a k := by
  apply Fin.ext
  fin_cases k <;>
    simp only [rawChild, proposal, viewProposal, coordinates, rawFields,
      SharedForest.rawChildFromOutput, SharedForest.rawChildBase,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, BitVec.val_toFin, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  all_goals norm_num
  all_goals omega

end ClaudeWCT.Bank.Paired
