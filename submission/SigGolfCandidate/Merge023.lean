import SigGolfCandidate.Merge005
import SigGolfCandidate.Merge009
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge022

-- ==== merged from T3_Gate6_SourceBridge ====
section

section
namespace SigGolfResearch.Gate6
set_option maxHeartbeats 500000
theorem digestRecord_index (output : BitVec 256) :
    (digestRecord output).1.1.val=output.toNat%2^31 := by
  simp [digestRecord,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
theorem digestRecord_bucket (output : BitVec 256) (c : Bank) :
    ((digestRecord output).1.2 c).val=output.toNat/2^(31+25*c.val)%16 := by
  simp [digestRecord,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
theorem digestRecord_leaf (output : BitVec 256) (c : Bank) (j : Fin 3) :
    ((digestRecord output).2.1 c j).val=
      output.toNat/2^(31+25*c.val)/2^(4+7*j.val)%128 := by
  simp only [digestRecord,BitVec.val_toFin,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 3
  omega
theorem digestRecord_gate (output : BitVec 256) :
    (digestRecord output).2.2.1.val=output.toNat/2^206%8 := by
  simp [digestRecord,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
theorem digestRecord_gate_zero (output : BitVec 256) :
    (digestRecord output).2.2.1=0 ↔ output.toNat/2^206%8=0 := by
  rw [←digestRecord_gate]
  exact Fin.ext_iff
theorem digest_acceptance_iff (output : BitVec 256) :
    DigestAccepted output ↔ output.toNat/2^206%8=0 ∧
      (∀ c, Function.Injective ((digestRecord output).2.1 c)) ∧
      (∑ c,childAuth ((digestRecord output).2.1 c))≤87 := by
  change ((digestRecord output).2.2.1=0 ∧ _ ∧ _) ↔ _
  rw [digestRecord_gate_zero]
end SigGolfResearch.Gate6
end
section
namespace SigGolfResearch.Gate6.Source
open SigGolfCandidate.T3 SigGolfCandidate.Budget.Octopus
open OracleComp ENNReal Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def sortedChild (v : Triple) : List Nat := (valList v).mergeSort (· ≤ ·)
theorem sortedChild_nodup (v : Triple) :
    (sortedChild v).Nodup ↔ Function.Injective v := by
  rw [sortedChild,(List.mergeSort_perm (valList v) (· ≤ ·)).nodup_iff]
  exact valList_nodup v
theorem sortedChild_length (v : Triple) : (sortedChild v).length=3 := by
  simp [sortedChild,valList]
theorem sortedChild_eq (v : Triple) (hv : Function.Injective v) :
    sortedChild v=(valList v).toFinset.sort := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (List.pairwise_mergeSort' _ _) (Finset.pairwise_sort _ _)
  refine (List.mergeSort_perm _ _).trans ?_
  rw [List.perm_ext_iff_of_nodup ((valList_nodup v).mpr hv) (Finset.sort_nodup _ _)]
  intro a
  simp
theorem authCount_eq_octH (leaves : List Nat) (hlen : leaves.length=3) (hn : leaves.Nodup) :
    authCount leaves=octH 7 leaves := by
  obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hlen
  have hab : a ≠ b := by intro he;subst b;simp at hn
  have hbc : b ≠ c := by intro he;subst c;simp at hn
  have hx1 : a ^^^ b ≠ 0 := Nat.xor_ne_zero_iff.mpr hab
  have hx2 : b ^^^ c ≠ 0 := Nat.xor_ne_zero_iff.mpr hbc
  simp only [authCount,octH,xorSum,List.drop_succ_cons,List.drop_zero,List.tail_cons,
    List.zip_cons_cons,List.zip_nil_right,List.map_cons,List.map_nil,
    List.zipWith_cons_cons,List.zipWith_nil_right,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,bitLen,hx1,hx2,ite_false]
  omega
theorem source_child_auth (v : Triple) (hv : Function.Injective v) :
    authCount (sortedChild v)=childAuth v := by
  rw [authCount_eq_octH _ (sortedChild_length v) ((sortedChild_nodup v).mpr hv),sortedChild_eq v hv]
  rfl
def rawSelections (raw : RawRecord) : List Selection :=
  List.ofFn fun c : Bank => ⟨(raw.1.2 c).val,sortedChild (raw.2.1 c)⟩
theorem source_selections (output : BitVec 256) :
    rawSelections (digestRecord output)=selections output := by
  apply List.ext_getElem
  · simp [rawSelections,selections]
  · intro c hc hc'
    simp only [rawSelections,List.getElem_ofFn,selections,List.getElem_map,List.getElem_range]
    congr 1
    · exact digestRecord_bucket output ⟨c,by simpa [rawSelections] using hc⟩
    · simp only [sortedChild,valList]
      congr 1
      apply List.ext_getElem
      · simp [valList]
      · intro j hj hj'
        simp only [sortedChild,valList,List.getElem_ofFn,List.getElem_map,List.getElem_range]
        exact digestRecord_leaf output ⟨c,by simpa [rawSelections] using hc⟩ ⟨j,by simpa using hj⟩
theorem source_leaf_condition (output : BitVec 256) :
    SigGolfCandidate.T3.admissible (selections output)=true ↔
      (∀ c,Function.Injective ((digestRecord output).2.1 c)) ∧
      28+(∑ c,authCount (sortedChild ((digestRecord output).2.1 c)))≤115 := by
  rw [←source_selections]
  simp only [rawSelections,SigGolfCandidate.T3.admissible,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
    List.mem_ofFn,forall_exists_index,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  constructor
  · rintro ⟨hi,hc⟩
    exact ⟨fun c => (sortedChild_nodup _).mp (hi _ c rfl),hc⟩
  · rintro ⟨hi,hc⟩
    refine ⟨?_,hc⟩
    intro x c hx
    subst x
    exact (sortedChild_nodup _).mpr (hi c)
theorem actual_predicate_iff (output : BitVec 256) :
    digestAdmissible output=true ↔ DigestAccepted output := by
  rw [digestAdmissible,Bool.and_eq_true,source_leaf_condition,digestGate,decide_eq_true_eq,
    digest_acceptance_iff]
  have he (hi : ∀ c,Function.Injective ((digestRecord output).2.1 c)) :
      (∑ c,authCount (sortedChild ((digestRecord output).2.1 c)))=
        ∑ c,childAuth ((digestRecord output).2.1 c) :=
    Finset.sum_congr rfl (fun c _ => source_child_auth _ (hi c))
  constructor
  · rintro ⟨⟨hi,hc⟩,hg⟩
    rw [he hi] at hc
    exact ⟨hg,hi,by omega⟩
  · rintro ⟨hg,hi,hc⟩
    exact ⟨⟨hi,by rw [he hi];omega⟩,hg⟩
theorem actual_acceptance_exact :
    Pr[fun output => digestAdmissible output=true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=acceptance := by
  simp_rw [actual_predicate_iff]
  exact digest_acceptance_exact
theorem actual_mark_joint_exact (mark : MarkedLabel) :
    Pr[fun output => digestAdmissible output=true ∧ (digestRecord output).1=mark |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))]=acceptance/2^59 := by
  simp_rw [actual_predicate_iff]
  exact digest_mark_joint_exact mark
end SigGolfResearch.Gate6.Source
end
end
-- ==== merged from SphincsSecurity_Proof_Base_BinomialMoments ====
section

namespace SphincsSecurity.Concrete
open ENNReal
noncomputable def binomialAverage (rate : ENNReal) : Nat → (Nat → ENNReal) → ENNReal
  | 0, f => f 0
  | steps + 1, f =>
      (1 - rate) * binomialAverage rate steps f +
        rate * binomialAverage rate steps (fun count => f (count + 1))
theorem binomialAverage_zero (rate : ENNReal) (f : Nat → ENNReal) :
    binomialAverage rate 0 f = f 0 := rfl
theorem binomialAverage_succ (rate : ENNReal) (steps : Nat) (f : Nat → ENNReal) :
    binomialAverage rate (steps + 1) f =
      (1 - rate) * binomialAverage rate steps f +
        rate * binomialAverage rate steps (fun count => f (count + 1)) := rfl
theorem binomialAverage_add (rate : ENNReal) (steps : Nat) (f g : Nat → ENNReal) :
    binomialAverage rate steps (fun count => f count + g count) =
      binomialAverage rate steps f + binomialAverage rate steps g := by
  induction steps generalizing f g with
  | zero => rfl
  | succ steps ih =>
      simp only [binomialAverage_succ, ih, mul_add]
      ac_rfl
theorem binomialAverage_mul_left (rate factor : ENNReal) (steps : Nat) (f : Nat → ENNReal) :
    binomialAverage rate steps (fun count => factor * f count) =
      factor * binomialAverage rate steps f := by
  induction steps generalizing f with
  | zero => rfl
  | succ steps ih =>
      simp only [binomialAverage_succ, ih]
      ring
theorem binomialAverage_mul_right (rate factor : ENNReal) (steps : Nat) (f : Nat → ENNReal) :
    binomialAverage rate steps (fun count => f count * factor) =
      binomialAverage rate steps f * factor := by
  simpa only [mul_comm] using binomialAverage_mul_left rate factor steps f
theorem binomialAverage_sum {α : Type*} (rate : ENNReal) (steps : Nat) (set : Finset α)
    (f : α → Nat → ENNReal) :
    binomialAverage rate steps (fun count => ∑ i ∈ set, f i count) =
      ∑ i ∈ set, binomialAverage rate steps (f i) := by
  induction steps generalizing f with
  | zero => rfl
  | succ steps ih =>
      simp only [binomialAverage_succ, ih, Finset.mul_sum, Finset.sum_add_distrib]
theorem binomialAverage_mono (rate : ENNReal) (steps : Nat) {f g : Nat → ENNReal}
    (h : ∀ count, f count ≤ g count) :
    binomialAverage rate steps f ≤ binomialAverage rate steps g := by
  induction steps generalizing f g with
  | zero => exact h 0
  | succ steps ih =>
      exact add_le_add (mul_le_mul' le_rfl (ih h))
        (mul_le_mul' le_rfl (ih (fun count => h (count + 1))))
theorem bernoulli_mix_increment {rate : ENNReal} (hrate : rate ≤ 1) (value increment : ENNReal) :
    (1 - rate) * value + rate * (value + increment) = value + rate * increment := by
  calc
    _ = (1 - rate + rate) * value + rate * increment := by ring
    _ = _ := by rw [tsub_add_cancel_of_le hrate, one_mul]
theorem binomialAverage_const {rate : ENNReal} (hrate : rate ≤ 1) (steps : Nat) (value : ENNReal) :
    binomialAverage rate steps (fun _ => value) = value := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [binomialAverage_succ, ih, ← add_mul, tsub_add_cancel_of_le hrate, one_mul]
theorem binomialAverage_choose {rate : ENNReal} (hrate : rate ≤ 1) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (count.choose degree : ENNReal)) =
      (steps.choose degree : ENNReal) * rate ^ degree := by
  induction steps generalizing degree with
  | zero =>
      cases degree <;> simp [binomialAverage_zero]
  | succ steps ih =>
      cases degree with
      | zero => simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, binomialAverage_const hrate]
      | succ degree =>
          rw [binomialAverage_succ]
          simp_rw [Nat.choose_succ_succ, Nat.cast_add]
          rw [binomialAverage_add]
          simp_rw [ih]
          rw [add_comm ((steps.choose degree : ENNReal) * rate ^ degree), bernoulli_mix_increment hrate]
          simp only [Nat.succ_eq_add_one, pow_succ]
          ring
theorem binomialAverage_descFactorial {rate : ENNReal} (hrate : rate ≤ 1) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (count.descFactorial degree : ENNReal)) =
      (steps.descFactorial degree : ENNReal) * rate ^ degree := by
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [binomialAverage_mul_left, binomialAverage_choose hrate]
  ring
theorem mul_descFactorial_eq (count degree : Nat) :
    count * count.descFactorial degree =
      count.descFactorial (degree + 1) + degree * count.descFactorial degree := by
  by_cases h : degree ≤ count
  · rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.mul_zero,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.mul_zero, Nat.add_zero]
theorem power_eq_stirling_descFactorial (count degree : Nat) :
    count ^ degree = ∑ order ∈ Finset.range (degree + 1),
      Nat.stirlingSecond degree order * count.descFactorial order := by
  induction degree with
  | zero => simp
  | succ degree ih =>
      rw [pow_succ, ih, Finset.sum_mul,
        Finset.sum_range_succ' (fun order => Nat.stirlingSecond (degree + 1) order * count.descFactorial order)]
      simp only [Nat.stirlingSecond_succ_zero, Nat.zero_mul, Nat.add_zero,
        Nat.stirlingSecond_succ_succ, Nat.add_mul, Finset.sum_add_distrib]
      have hshift :
          (∑ order ∈ Finset.range (degree + 1),
            (order + 1) * Nat.stirlingSecond degree (order + 1) * count.descFactorial (order + 1)) =
          ∑ order ∈ Finset.range (degree + 1),
            order * Nat.stirlingSecond degree order * count.descFactorial order := by
        let f := fun order => order * Nat.stirlingSecond degree order * count.descFactorial order
        change (∑ order ∈ Finset.range (degree + 1), f (order + 1)) =
          ∑ order ∈ Finset.range (degree + 1), f order
        calc
          _ = ∑ order ∈ Finset.range (degree + 2), f order := by
            simpa [f] using (Finset.sum_range_succ' f (degree + 1)).symm
          _ = _ := by
            rw [Finset.sum_range_succ]
            simp [f, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self degree)]
      simp only [Nat.add_mul, Finset.sum_add_distrib] at hshift
      rw [hshift, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro order _
      calc
        _ = Nat.stirlingSecond degree order * (count * count.descFactorial order) := by ring
        _ = _ := by rw [mul_descFactorial_eq]; ring
theorem binomialAverage_power {rate : ENNReal} (hrate : rate ≤ 1) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (count : ENNReal) ^ degree) =
      ∑ order ∈ Finset.range (degree + 1),
        (Nat.stirlingSecond degree order : ENNReal) *
          (steps.descFactorial order : ENNReal) * rate ^ order := by
  have hpower (count : Nat) : (count : ENNReal) ^ degree =
      ∑ order ∈ Finset.range (degree + 1),
        (Nat.stirlingSecond degree order : ENNReal) * (count.descFactorial order : ENNReal) := by
    exact_mod_cast power_eq_stirling_descFactorial count degree
  simp_rw [hpower]
  rw [binomialAverage_sum]
  apply Finset.sum_congr rfl
  intro order _
  rw [binomialAverage_mul_left, binomialAverage_descFactorial hrate]
  ring
theorem stirlingSecond_le_choose_mul_pow (degree order : Nat) :
    Nat.stirlingSecond degree order ≤ degree.choose order * degree ^ (degree - order) := by
  induction degree generalizing order with
  | zero => cases order <;> simp
  | succ degree ih =>
      cases order with
      | zero => simp
      | succ order =>
          by_cases hlt : order < degree
          · have hpow : (order + 1) * degree ^ (degree - (order + 1)) ≤
                (degree + 1) ^ (degree - order) := by
              calc
                _ ≤ (degree + 1) * (degree + 1) ^ (degree - (order + 1)) :=
                  Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.le_succ _) _)
                _ = _ := by
                  rw [← pow_succ']
                  congr 1
                  omega
            calc
              _ = (order + 1) * Nat.stirlingSecond degree (order + 1) +
                    Nat.stirlingSecond degree order := Nat.stirlingSecond_succ_succ _ _
              _ ≤ (order + 1) * (degree.choose (order + 1) * degree ^ (degree - (order + 1))) +
                    degree.choose order * degree ^ (degree - order) :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ (ih _)) (ih _)
              _ = degree.choose (order + 1) * ((order + 1) * degree ^ (degree - (order + 1))) +
                    degree.choose order * degree ^ (degree - order) := by ring
              _ ≤ degree.choose (order + 1) * (degree + 1) ^ (degree - order) +
                    degree.choose order * (degree + 1) ^ (degree - order) :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ hpow)
                    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _))
              _ = _ := by
                  rw [Nat.choose_succ_succ]
                  simp only [Nat.add_sub_add_right]
                  ring
          · by_cases heq : order = degree
            · subst order; simp [Nat.stirlingSecond_self]
            · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]
              exact Nat.zero_le _
theorem binomialAverage_power_le {rate : ENNReal} (hrate : rate ≤ 1) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (count : ENNReal) ^ degree) ≤
      ((steps : ENNReal) * rate + degree) ^ degree := by
  rw [binomialAverage_power hrate]
  calc
    _ ≤ ∑ order ∈ Finset.range (degree + 1),
        (degree.choose order : ENNReal) * (degree : ENNReal) ^ (degree - order) *
          ((steps : ENNReal) * rate) ^ order := by
      apply Finset.sum_le_sum
      intro order _
      have hc : (Nat.stirlingSecond degree order : ENNReal) ≤
          (degree.choose order : ENNReal) * (degree : ENNReal) ^ (degree - order) := by
        exact_mod_cast stirlingSecond_le_choose_mul_pow degree order
      have hf : (steps.descFactorial order : ENNReal) ≤ (steps : ENNReal) ^ order := by
        exact_mod_cast Nat.descFactorial_le_pow steps order
      apply (mul_le_mul' (mul_le_mul' hc hf) le_rfl).trans_eq
      rw [mul_pow]
      ring
    _ = _ := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro order _
      ring
theorem binomialAverage_shifted_power (rate shift : ENNReal) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (shift + count) ^ degree) =
      ∑ order ∈ Finset.range (degree + 1),
        (degree.choose order : ENNReal) * shift ^ (degree - order) *
          binomialAverage rate steps (fun count => (count : ENNReal) ^ order) := by
  have hpower (count : Nat) : (shift + count) ^ degree =
      ∑ order ∈ Finset.range (degree + 1),
        (degree.choose order : ENNReal) * shift ^ (degree - order) * (count : ENNReal) ^ order := by
    rw [add_comm shift, add_pow]
    apply Finset.sum_congr rfl
    intro order _
    ring
  simp_rw [hpower]
  rw [binomialAverage_sum]
  simp_rw [binomialAverage_mul_left]
theorem binomialAverage_shifted_power_le {rate : ENNReal} (hrate : rate ≤ 1)
    (shift : ENNReal) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (shift + count) ^ degree) ≤
      (shift + steps * rate + degree) ^ degree := by
  rw [binomialAverage_shifted_power]
  calc
    _ ≤ ∑ order ∈ Finset.range (degree + 1),
        (degree.choose order : ENNReal) * shift ^ (degree - order) *
          ((steps : ENNReal) * rate + degree) ^ order := by
      apply Finset.sum_le_sum
      intro order horder
      have ho : order ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp horder)
      exact mul_le_mul' le_rfl ((binomialAverage_power_le hrate steps order).trans
        (pow_le_pow_left' (add_le_add le_rfl (Nat.cast_le.mpr ho)) _))
    _ = _ := by
      rw [show shift + steps * rate + degree = steps * rate + degree + shift by ac_rfl, add_pow]
      apply Finset.sum_congr rfl
      intro order _
      ring
theorem binomialAverage_power_mono_of_factorial {rate nextRate : ENNReal}
    (hrate : rate ≤ 1) (hnext : nextRate ≤ 1) (steps nextSteps degree : Nat)
    (hmoments : ∀ order, order ≤ degree →
      (steps.descFactorial order : ENNReal) * rate ^ order ≤
        (nextSteps.descFactorial order : ENNReal) * nextRate ^ order) :
    binomialAverage rate steps (fun count => (count : ENNReal) ^ degree) ≤
      binomialAverage nextRate nextSteps (fun count => (count : ENNReal) ^ degree) := by
  rw [binomialAverage_power hrate, binomialAverage_power hnext]
  apply Finset.sum_le_sum
  intro order horder
  simp only [mul_assoc]
  exact mul_le_mul' le_rfl (hmoments order (Nat.le_of_lt_succ (Finset.mem_range.mp horder)))
theorem binomialAverage_shifted_power_mono_of_factorial {rate nextRate shift nextShift : ENNReal}
    (hrate : rate ≤ 1) (hnext : nextRate ≤ 1) (hshift : shift ≤ nextShift)
    (steps nextSteps degree : Nat)
    (hmoments : ∀ order, order ≤ degree →
      (steps.descFactorial order : ENNReal) * rate ^ order ≤
        (nextSteps.descFactorial order : ENNReal) * nextRate ^ order) :
    binomialAverage rate steps (fun count => (shift + count) ^ degree) ≤
      binomialAverage nextRate nextSteps (fun count => (nextShift + count) ^ degree) := by
  apply (binomialAverage_mono rate steps (fun count =>
    pow_le_pow_left' (add_le_add hshift (le_rfl (a := (count : ENNReal)))) degree)).trans
  rw [binomialAverage_shifted_power, binomialAverage_shifted_power]
  apply Finset.sum_le_sum
  intro order horder
  apply mul_le_mul' le_rfl
  exact binomialAverage_power_mono_of_factorial hrate hnext steps nextSteps order
    (fun j hj => hmoments j (hj.trans (Nat.le_of_lt_succ (Finset.mem_range.mp horder))))
theorem mass_pow_le_descFactorial (mass : ENNReal) (count degree : Nat)
    (hroom : mass + degree ≤ ((count + 1 : Nat) : ENNReal)) :
    mass ^ degree ≤ (count.descFactorial degree : ENNReal) := by
  have hdegree : degree ≤ count + 1 := Nat.cast_le.mp ((le_add_left le_rfl).trans hroom)
  have hcancel : ((count + 1 - degree : Nat) : ENNReal) + degree = ((count + 1 : Nat) : ENNReal) := by
    exact_mod_cast Nat.sub_add_cancel hdegree
  have hmass : mass ≤ ((count + 1 - degree : Nat) : ENNReal) :=
    ENNReal.le_of_add_le_add_right (by finiteness) (hroom.trans_eq hcancel.symm)
  apply (pow_le_pow_left' hmass degree).trans
  exact_mod_cast Nat.pow_sub_le_descFactorial count degree
theorem binomialAverage_shifted_power_le_of_room {rate nextRate shift nextShift mass : ENNReal}
    (hrate : rate ≤ 1) (hnext : nextRate ≤ 1) (hshift : shift ≤ nextShift)
    (steps nextSteps degree : Nat)
    (hmean : (steps : ENNReal) * rate ≤ mass * nextRate)
    (hroom : mass + degree ≤ ((nextSteps + 1 : Nat) : ENNReal)) :
    binomialAverage rate steps (fun count => (shift + count) ^ degree) ≤
      binomialAverage nextRate nextSteps (fun count => (nextShift + count) ^ degree) := by
  apply binomialAverage_shifted_power_mono_of_factorial hrate hnext hshift steps nextSteps degree
  intro order horder
  have hfall : (steps.descFactorial order : ENNReal) ≤ (steps : ENNReal) ^ order := by
    exact_mod_cast Nat.descFactorial_le_pow steps order
  calc
    _ ≤ (steps : ENNReal) ^ order * rate ^ order := mul_le_mul' hfall le_rfl
    _ = ((steps : ENNReal) * rate) ^ order := (mul_pow _ _ _).symm
    _ ≤ (mass * nextRate) ^ order := pow_le_pow_left' hmean order
    _ = mass ^ order * nextRate ^ order := mul_pow _ _ _
    _ ≤ _ := mul_le_mul'
      (mass_pow_le_descFactorial mass nextSteps order
        ((add_le_add le_rfl (Nat.cast_le.mpr horder)).trans hroom)) le_rfl
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Arith ====
section

namespace SphincsSecurity
theorem nat_xor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl
theorem div_pow_succ (x k : Nat) : x / 2 ^ (k + 1) = x / 2 ^ k / 2 := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
theorem xor_one_div_two (j : Nat) : Nat.xor (2 * j) 1 / 2 = j := by
  rw [nat_xor_eq, show (2 : Nat) = 2 ^ 1 from rfl, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib, Nat.shiftRight_eq_div_pow]
  simp
theorem xor_one_two_mul (j : Nat) : Nat.xor (2 * j) 1 = 2 * j + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => rw [nat_xor_eq]; simp [Nat.testBit_zero]
  | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, xor_one_div_two, Nat.mul_add_div (by omega)]
      simp
theorem xor_one_two_mul_add_one (j : Nat) : Nat.xor (2 * j + 1) 1 = 2 * j := by
  rw [← xor_one_two_mul j, nat_xor_eq, nat_xor_eq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
theorem index_sibling_cases (c : Nat) :
    ∃ j, (c = 2 * j ∧ Nat.xor c 1 = 2 * j + 1 ∧ c % 2 = 0)
      ∨ (c = 2 * j + 1 ∧ Nat.xor c 1 = 2 * j ∧ c % 2 = 1) := by
  obtain ⟨j, hj⟩ : ∃ j, c / 2 = j := ⟨c / 2, rfl⟩
  have hdm := Nat.div_add_mod c 2
  rcases Nat.mod_two_eq_zero_or_one c with hmod | hmod
  · have hc : c = 2 * j := by omega
    exact ⟨j, Or.inl ⟨hc, by rw [hc]; exact xor_one_two_mul j, hmod⟩⟩
  · have hc : c = 2 * j + 1 := by omega
    exact ⟨j, Or.inr ⟨hc, by rw [hc]; exact xor_one_two_mul_add_one j, hmod⟩⟩
theorem testBit_iff_div_mod (x k : Nat) : x.testBit k = true ↔ x / 2 ^ k % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_Extract ====
section

namespace SphincsSecurity.Concrete
open OracleComp
variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (path : Nat → Digest)
def honestNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx)
def foldValue (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (treeFold parameter lay tree leaf path levels value)
def orderedPayload (bit : Bool) (current sibling : Digest) : HashInput :=
  bit.rec (nodePayload current sibling) (nodePayload sibling current)
@[simp] theorem orderedPayload_false (current sibling : Digest) :
    orderedPayload false current sibling = nodePayload current sibling := rfl
@[simp] theorem orderedPayload_true (current sibling : Digest) :
    orderedPayload true current sibling = nodePayload sibling current := rfl
def treeFoldPayload (value : Digest) (level : Nat) : HashInput :=
  orderedPayload (leaf.val.testBit level)
    (foldValue f parameter lay tree leaf path value level) (path level)
theorem eval_tweakableHash (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn f (tweakableHash parameter domain payload)
      = truncateHash (f (tweakableHashInput parameter domain payload)) := by
  simp only [tweakableHash, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
    evalWithAnswerFn_pure]
theorem honestNode_succ (level nodeIdx : Nat) :
    honestNode f parameter lay tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
          (nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
            (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestNode, treeNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]
theorem foldValue_succ (value : Digest) (level : Nat) :
    foldValue f parameter lay tree leaf path value (level + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.node lay tree (level + 1) (leaf.val / 2 ^ (level + 1)))
          (treeFoldPayload f parameter lay tree leaf path value level))) := by
  simp only [foldValue, treeFoldPayload, treeFold_succ_eq, evalWithAnswerFn_bind, orderedPayload]
  cases leaf.val.testBit level <;> rfl
def NodeHit (level nodeIdx : Nat) (payload : HashInput) : Prop :=
  payload ≠ nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
      (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))
    ∧ truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload))
      = honestNode f parameter lay tree secret (level + 1) nodeIdx
theorem treeFold_extract (value : Digest) (levels : Nat)
    (hfold : foldValue f parameter lay tree leaf path value levels
      = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels)) :
    (value = honestNode f parameter lay tree secret 0 leaf.val
        ∧ ∀ level, level < levels → path level
            = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∨ ∃ level, level < levels
          ∧ NodeHit f parameter lay tree secret level (leaf.val / 2 ^ (level + 1))
              (treeFoldPayload f parameter lay tree leaf path value level) := by
  induction levels with
  | zero =>
      left
      refine ⟨?_, fun level hlevel => absurd hlevel (by omega)⟩
      simpa [foldValue] using hfold
  | succ levels ih =>
      obtain ⟨j, hcase⟩ := index_sibling_cases (leaf.val / 2 ^ levels)
      have hj : leaf.val / 2 ^ (levels + 1) = j := by
        rw [div_pow_succ]
        rcases hcase with ⟨hc, _, _⟩ | ⟨hc, _, _⟩ <;> omega
      have hhash : truncateHash (f (tweakableHashInput parameter
            (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
            (treeFoldPayload f parameter lay tree leaf path value levels)))
          = honestNode f parameter lay tree secret (levels + 1) (leaf.val / 2 ^ (levels + 1)) := by
        rw [← foldValue_succ]
        exact hfold
      by_cases hagree : treeFoldPayload f parameter lay tree leaf path value levels
          = nodePayload (honestNode f parameter lay tree secret levels (2 * j))
              (honestNode f parameter lay tree secret levels (2 * j + 1))
      · have hstep : foldValue f parameter lay tree leaf path value levels
              = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels)
            ∧ path levels = honestNode f parameter lay tree secret levels
              (Nat.xor (leaf.val / 2 ^ levels) 1) := by
          rw [treeFoldPayload] at hagree
          rcases hcase with ⟨hc, hsibling, hmod⟩ | ⟨hc, hsibling, hmod⟩
          · rw [show leaf.val.testBit levels = false by
              rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hcur, hsib⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
          · rw [show leaf.val.testBit levels = true by
              rw [testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hsib, hcur⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
        rcases ih hstep.1 with ⟨hvalue, hpaths⟩ | ⟨level, hlevel, hnode⟩
        · left
          refine ⟨hvalue, fun level hlevel => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | heq
          · exact hpaths level hlt
          · subst heq; exact hstep.2
        · exact Or.inr ⟨level, by omega, hnode⟩
      · right
        exact ⟨levels, by omega, by rw [hj]; exact hagree, hhash⟩
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Support ====
section

namespace SphincsSecurity
open OracleComp OracleSpec
def queriedInputs {alpha : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec alpha) :
    List HashInput :=
  ((simulateQ (f.withLogging) oa).run).2.map Sigma.fst
@[simp] theorem queriedInputs_pure {alpha : Type} (f : QueryImpl HashSpec Id) (x : alpha) :
    queriedInputs f (pure x) = [] := by
  rfl
@[simp] theorem queriedInputs_query_bind {alpha : Type} (f : QueryImpl HashSpec Id)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec alpha) :
    queriedInputs f (liftM (HashSpec.query input) >>= next)
      = input :: queriedInputs f (next (f input)) := by
  rfl
theorem queriedInputs_bind {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta) :
    queriedInputs f (oa >>= next)
      = queriedInputs f oa ++ queriedInputs f (next (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind input rest ih =>
      rw [bind_assoc, queriedInputs_query_bind, queriedInputs_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, List.cons_append]
theorem queriedInputs_mono_bind_left {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta)
    {input : HashInput} (hinput : input ∈ queriedInputs f oa) :
    input ∈ queriedInputs f (oa >>= next) := by
  rw [queriedInputs_bind]
  exact List.mem_append_left _ hinput
theorem queriedInputs_mono_bind_right {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta)
    {input : HashInput} (hinput : input ∈ queriedInputs f (next (evalWithAnswerFn f oa))) :
    input ∈ queriedInputs f (oa >>= next) := by
  rw [queriedInputs_bind]
  exact List.mem_append_right _ hinput
@[simp] theorem queriedInputs_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    queriedInputs f (Concrete.tweakableHash parameter domain payload)
      = [tweakableHashInput parameter domain payload] := by
  change queriedInputs f
    (liftM (HashSpec.query (tweakableHashInput parameter domain payload)) >>=
      fun answer => pure (truncateHash answer)) = _
  rw [queriedInputs_query_bind, queriedInputs_pure]
theorem replay_of_mem_support {alpha : Type} (oa : OracleComp HashSpec alpha)
    (cache : QueryCache HashSpec) (a : alpha) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f) :
    cache ≤ cache' ∧ evalWithAnswerFn f oa = a
      ∧ ∀ input, input ∈ queriedInputs f oa → cache' input ≠ none := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      refine ⟨le_rfl, rfl, ?_⟩
      simp
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      change (answer, cacheMid) ∈ support ((randomOracle input).run cache) at hquery
      have hcached : cacheMid input = some answer := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
              Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hcache
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sample, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            exact QueryCache.cacheQuery_self cache input answer
      obtain ⟨hle, heval, hqueries⟩ := ih answer cacheMid a cache' hrest hf
      have hcached' : cache' input = some answer := hle hcached
      have hfinput : f input = answer := hf hcached'
      refine ⟨(QueryImpl.withCaching_cache_le uniformSampleImpl input cache
        (answer, cacheMid) hquery).trans hle, ?_, ?_⟩
      · rw [evalWithAnswerFn_bind,
          show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
            simulateQ_spec_query f input, hfinput]
        exact heval
      · intro input₀ hqueried
        rw [queriedInputs_query_bind, List.mem_cons, hfinput] at hqueried
        rcases hqueried with rfl | hqueried
        · simp [hcached']
        · exact hqueries input₀ hqueried
theorem replay_of_mem_support_of_le {alpha : Type} (oa : OracleComp HashSpec alpha)
    (cache : QueryCache HashSpec) (a : alpha) (cache' finalCache : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (hle : cache' ≤ finalCache) (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    evalWithAnswerFn f oa = a
      ∧ ∀ input, input ∈ queriedInputs f oa → finalCache input ≠ none := by
  have hf' : cache'.AgreesWithFn f := fun _ _ hcached => hf (hle hcached)
  obtain ⟨_, heval, hqueries⟩ := replay_of_mem_support oa cache a cache' hmem f hf'
  refine ⟨heval, fun input hinput => ?_⟩
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hqueries input hinput)
  rw [hle hanswer]
  simp
theorem cache_eq_none_of_not_mem_queriedInputs {alpha : Type}
    (oa : OracleComp HashSpec alpha) (cache : QueryCache HashSpec)
    (a : alpha) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f)
    (target : HashInput) (hnone : cache target = none)
    (hnot : target ∉ queriedInputs f oa) : cache' target = none := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact hnone
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      change (answer, cacheMid) ∈ support ((randomOracle input).run cache) at hquery
      have hcached : cacheMid input = some answer := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache,
              support_pure, Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hcache
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sample, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            exact QueryCache.cacheQuery_self cache input answer
      have hle : cacheMid ≤ cache' :=
        (replay_of_mem_support (next answer) cacheMid a cache' hrest f hf).1
      have hfinput : f input = answer := hf (hle hcached)
      have htarget : target ≠ input := by
        intro heq
        apply hnot
        rw [queriedInputs_query_bind]
        exact List.mem_cons.2 (Or.inl heq)
      have hmid : cacheMid target = none := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache,
              support_pure, Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hnone
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sample, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            rwa [QueryCache.cacheQuery_of_ne _ _ htarget]
      apply ih answer cacheMid a cache' hrest hf hmid
      rw [queriedInputs_query_bind, List.mem_cons, hfinput] at hnot
      intro htail
      exact hnot (Or.inr htail)
theorem exists_answerFn_replay_of_mem_support {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache)) :
    cache ≤ cache' ∧
      ∃ f : QueryImpl HashSpec Id, cache'.AgreesWithFn f ∧ evalWithAnswerFn f oa = a
        ∧ ∀ input, input ∈ queriedInputs f oa → cache' input ≠ none := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) cache'
      refine ⟨le_rfl, f, hf, rfl, ?_⟩
      intro input hqueried
      simp at hqueried
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      change (answer, cacheMid) ∈ support ((randomOracle input).run cache) at hquery
      have hcached : cacheMid input = some answer := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
              Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hcache
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sample, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            exact QueryCache.cacheQuery_self cache input answer
      obtain ⟨hle, f, hf, heval, hqueries⟩ := ih answer cacheMid a cache' hrest
      have hcached' : cache' input = some answer := hle hcached
      have hfinput : f input = answer := hf hcached'
      refine ⟨(QueryImpl.withCaching_cache_le uniformSampleImpl input cache
        (answer, cacheMid) hquery).trans hle, f, hf, ?_, ?_⟩
      rw [evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, hfinput]
      exact heval
      intro input₀ hqueried
      rw [queriedInputs_query_bind, List.mem_cons, hfinput] at hqueried
      rcases hqueried with rfl | hqueried
      · simp [hcached']
      · exact hqueries input₀ hqueried
theorem exists_answerFn_agrees_final_of_mem_support {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache)) :
    cache ≤ cache' ∧
      ∃ f : QueryImpl HashSpec Id, cache'.AgreesWithFn f ∧ evalWithAnswerFn f oa = a := by
  obtain ⟨hle, f, hf, heval, _⟩ := exists_answerFn_replay_of_mem_support oa cache a cache' hmem
  exact ⟨hle, f, hf, heval⟩
theorem simulateQ_romImpl_liftM {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ romImpl (liftM oa : OracleComp OracleWorld α)
      = simulateQ (randomOracle : QueryImpl HashSpec _) oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa
namespace Concrete
open OracleComp
theorem verifyLayers_succ_extract (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (signature : Signature) (remaining : Nat) (hlayer : remaining < numLayers)
    (message : Digest) (target : Digest)
    (hverify : evalWithAnswerFn f
        (verifyLayers parameter index signature (remaining + 1) message) = some target) :
    ∃ leafValue, evalWithAnswerFn f (otsLeafAttempt parameter ⟨remaining, hlayer⟩
          (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
          (signature.counter ⟨remaining, hlayer⟩) (signature.chainValue ⟨remaining, hlayer⟩))
        = some leafValue
      ∧ evalWithAnswerFn f (verifyLayers parameter index signature remaining
          (foldValue f parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
            (leafIndexAt index ⟨remaining, hlayer⟩) (signaturePath signature ⟨remaining, hlayer⟩)
            leafValue (layerHeight ⟨remaining, hlayer⟩))) = some target := by
  rcases hleaf : evalWithAnswerFn f (otsLeafAttempt parameter ⟨remaining, hlayer⟩
      (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
      (signature.counter ⟨remaining, hlayer⟩) (signature.chainValue ⟨remaining, hlayer⟩))
    with _ | leafValue
  · rw [verifyLayers_succ_eq, dif_pos hlayer, evalWithAnswerFn_bind, hleaf] at hverify
    simp at hverify
  · refine ⟨leafValue, rfl, ?_⟩
    rw [verifyLayers_succ_eq, dif_pos hlayer, evalWithAnswerFn_bind, hleaf] at hverify
    simpa [foldValue, evalWithAnswerFn_bind] using hverify
end Concrete
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_HonestFts ====
section

namespace SphincsSecurity.Concrete
open OracleComp
variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (tree : FtsTree)
  (secret : FtsLeaf → Digest)
theorem ftsLeafOfNat_val (leaf : FtsLeaf) : ftsLeafOfNat leaf.val = leaf := by
  ext
  simp [ftsLeafOfNat, Nat.mod_eq_of_lt leaf.isLt]
def honestFtsNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx)
theorem honestFtsNode_succ (level nodeIdx : Nat) :
    honestFtsNode f parameter index tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter
          (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx))
          (nodePayload (honestFtsNode f parameter index tree secret level (2 * nodeIdx))
            (honestFtsNode f parameter index tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestFtsNode, ftsNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]
theorem honestFtsNode_zero (leafIdx : FtsLeaf) :
    honestFtsNode f parameter index tree secret 0 leafIdx.val
      = truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leafIdx.val)
          (digestBytes (secret leafIdx)))) := by
  simp only [honestFtsNode, ftsNode_zero_eq, ftsLeafOfNat_val, ftsLeafHash, eval_tweakableHash]
def honestFtsHeap (heap : Nat) : Digest :=
  if h : 0 < heap ∧ heap < 2 ^ ftsTreeHeight then
    truncateHash (f (tweakableHashInput parameter (.ftsNode index tree heap)
      (nodePayload (honestFtsHeap (2 * heap)) (honestFtsHeap (2 * heap + 1)))))
  else
    honestFtsNode f parameter index tree secret 0 (heap - 2 ^ ftsTreeHeight)
termination_by 2 ^ ftsTreeHeight - heap
decreasing_by all_goals omega
theorem honestFtsHeap_node (heap : Nat) (hpos : 0 < heap) (hlt : heap < 2 ^ ftsTreeHeight) :
    honestFtsHeap f parameter index tree secret heap
      = truncateHash (f (tweakableHashInput parameter (.ftsNode index tree heap)
          (nodePayload (honestFtsHeap f parameter index tree secret (2 * heap))
            (honestFtsHeap f parameter index tree secret (2 * heap + 1))))) := by
  rw [honestFtsHeap, dif_pos ⟨hpos, hlt⟩]
theorem honestFtsHeap_leaf (leafIdx : Nat) :
    honestFtsHeap f parameter index tree secret (2 ^ ftsTreeHeight + leafIdx)
      = honestFtsNode f parameter index tree secret 0 leafIdx := by
  rw [honestFtsHeap, dif_neg (by omega), Nat.add_sub_cancel_left]
theorem honestFtsHeap_leaf' (leaf : FtsLeaf) :
    honestFtsHeap f parameter index tree secret (2 ^ ftsTreeHeight + leaf.val)
      = truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leaf.val)
          (digestBytes (secret leaf)))) := by
  rw [honestFtsHeap_leaf, honestFtsNode_zero]
theorem ftsHeapIndex_zero (nodeIdx : Nat) : ftsHeapIndex 0 nodeIdx = 2 ^ ftsTreeHeight + nodeIdx := rfl
theorem honestFtsNode_eq_heap (level nodeIdx : Nat) (hlevel : level ≤ ftsTreeHeight)
    (hnode : nodeIdx < 2 ^ (ftsTreeHeight - level)) :
    honestFtsNode f parameter index tree secret level nodeIdx
      = honestFtsHeap f parameter index tree secret (ftsHeapIndex level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero => rw [ftsHeapIndex_zero, honestFtsHeap_leaf]
  | succ level ih =>
      have hpow : 2 ^ (ftsTreeHeight - level) = 2 * 2 ^ (ftsTreeHeight - (level + 1)) := by
        rw [← pow_succ']; congr 1; omega
      have hpos : 0 < 2 ^ (ftsTreeHeight - (level + 1)) := Nat.two_pow_pos _
      have hle : 2 ^ (ftsTreeHeight - (level + 1)) ≤ 2 ^ (ftsTreeHeight - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have htop : 2 ^ (ftsTreeHeight - 1) * 2 = 2 ^ ftsTreeHeight := by decide
      rw [honestFtsNode_succ, honestFtsHeap_node f parameter index tree secret _
        (by unfold ftsHeapIndex; omega) (by unfold ftsHeapIndex; omega),
        ih (2 * nodeIdx) (by omega) (by omega), ih (2 * nodeIdx + 1) (by omega) (by omega)]
      have h1 : ftsHeapIndex level (2 * nodeIdx) = 2 * ftsHeapIndex (level + 1) nodeIdx := by
        unfold ftsHeapIndex; omega
      have h2 : ftsHeapIndex level (2 * nodeIdx + 1) = 2 * ftsHeapIndex (level + 1) nodeIdx + 1 := by
        unfold ftsHeapIndex; omega
      rw [h1, h2]
def honestFtsKey (secret : FtsTree → FtsLeaf → Digest) : Digest :=
  evalWithAnswerFn f (ftsKey parameter index secret)
theorem honestFtsKey_eq_node (secret : FtsTree → FtsLeaf → Digest) :
    honestFtsKey f parameter index secret
      = honestFtsNode f parameter index porsTree (secret porsTree) ftsTreeHeight 0 := rfl
theorem honestFtsKey_eq_heap (secret : FtsTree → FtsLeaf → Digest) :
    honestFtsKey f parameter index secret
      = honestFtsHeap f parameter index porsTree (secret porsTree) 1 := by
  rw [honestFtsKey_eq_node, honestFtsNode_eq_heap f parameter index porsTree _ ftsTreeHeight 0
    le_rfl (by decide)]
  rfl
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_ExtractChain ====
section

namespace SphincsSecurity.Concrete
open OracleComp
variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : Digest)
def honestChain (position : Nat) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 position secret)
def walkValue (start : Nat) (value : Digest) (steps : Nat) : Digest :=
  evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value)
theorem honestChain_succ (position : Nat) (hposition : position < chainLength - 1) :
    honestChain f parameter lay tree leaf chainIdx secret (position + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨position, hposition⟩)
          (digestBytes (honestChain f parameter lay tree leaf chainIdx secret position)))) := by
  simp only [honestChain, chainWalk, evalWithAnswerFn_bind, Nat.zero_add, dif_pos hposition,
    eval_tweakableHash]
theorem walkValue_succ (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps < chainLength - 1) :
    walkValue f parameter lay tree leaf chainIdx start value (steps + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨start + steps, hrange⟩)
          (digestBytes (walkValue f parameter lay tree leaf chainIdx start value steps)))) := by
  simp only [walkValue, chainWalk, evalWithAnswerFn_bind, dif_pos hrange, eval_tweakableHash]
def ChainHit (position : Nat) (hposition : position < chainLength - 1) (payload : Digest) : Prop :=
  payload ≠ honestChain f parameter lay tree leaf chainIdx secret position
    ∧ truncateHash (f (tweakableHashInput parameter
        (.chain lay tree leaf chainIdx ⟨position, hposition⟩) (digestBytes payload)))
      = honestChain f parameter lay tree leaf chainIdx secret (position + 1)
theorem chainWalk_extract (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps ≤ chainLength - 1)
    (hwalk : walkValue f parameter lay tree leaf chainIdx start value steps
      = honestChain f parameter lay tree leaf chainIdx secret (start + steps)) :
    value = honestChain f parameter lay tree leaf chainIdx secret start
      ∨ ∃ (offset : Nat) (hoffset : start + offset < chainLength - 1), offset < steps
          ∧ ChainHit f parameter lay tree leaf chainIdx secret (start + offset) hoffset
              (walkValue f parameter lay tree leaf chainIdx start value offset) := by
  induction steps with
  | zero =>
      left
      simpa [walkValue, chainWalk] using hwalk
  | succ steps ih =>
      have hlt : start + steps < chainLength - 1 := by omega
      by_cases hagree : walkValue f parameter lay tree leaf chainIdx start value steps
          = honestChain f parameter lay tree leaf chainIdx secret (start + steps)
      · rcases ih (by omega) hagree with hvalue | ⟨offset, hoffset, hlt', hhit⟩
        · exact Or.inl hvalue
        · exact Or.inr ⟨offset, hoffset, by omega, hhit⟩
      · refine Or.inr ⟨steps, hlt, by omega, hagree, ?_⟩
        rw [← walkValue_succ f parameter lay tree leaf chainIdx start value steps hlt, hwalk,
          show start + (steps + 1) = start + steps + 1 by omega]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Eval ====
section

namespace SphincsSecurity.Concrete
open OracleComp
variable {α : Type} (f : QueryImpl HashSpec Id)
@[simp]
theorem evalWithAnswerFn_sequenceFin {n : Nat} (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn f (sequenceFin computation) = fun index => evalWithAnswerFn f (computation index) := by
  induction n with
  | zero => funext index; exact index.elim0
  | succ n ih =>
      funext index
      simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      cases index using Fin.cases <;> rfl
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Ots_OneTime ====
section

section
namespace SphincsSecurity.Concrete
variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]
theorem chainWalk_add (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    chainWalk (m := m) parameter lay tree leaf chainIdx start (a + b) value
      = (do
          let mid ← chainWalk (m := m) parameter lay tree leaf chainIdx start a value
          chainWalk parameter lay tree leaf chainIdx (start + a) b mid) := by
  induction b with
  | zero => simp [chainWalk]
  | succ b ih =>
      show chainWalk (m := m) parameter lay tree leaf chainIdx start (a + b + 1) value = _
      simp only [chainWalk, ih, bind_assoc, Nat.add_assoc]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open OracleComp
variable {α : Type} (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
  (tree : TreeIndex) (leaf : LeafIndex)
theorem eval_chainWalk_add (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start (a + b) value)
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + a) b
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start a value))) := by
  rw [chainWalk_add, evalWithAnswerFn_bind]
theorem eval_recoverChain (chainIdx : ChainIndex) (digit : Digit) (value : Digest) :
    evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
        (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)))
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) value) := by
  have hdigit : digit.val + (chainLength - 1 - digit.val) = chainLength - 1 := by
    have hlt := digit.isLt
    simp only [chainLength, winternitzBits] at hlt
    simp only [chainLength, winternitzBits]
    omega
  calc evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)))
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx
          (0 + digit.val) (chainLength - 1 - digit.val)
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value))) := by
        rw [recoverChain, Nat.zero_add]
    _ = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0
          (digit.val + (chainLength - 1 - digit.val)) value) := (eval_chainWalk_add ..).symm
    _ = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) value) := by
        rw [hdigit]
theorem eval_oneTimePublicKey (secret : ChainIndex → Digest) :
    evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret)
      = fun chainIdx => evalWithAnswerFn f
          (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)) := by
  simp [oneTimePublicKey]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Ots_ExtractOts ====
section

namespace SphincsSecurity.Concrete
open OracleComp
variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)
theorem leafOfNat_val : leafOfNat leaf.val = leaf := by
  ext
  simp [leafOfNat, Nat.mod_eq_of_lt leaf.isLt]
def honestEndpoints (chainIdx : ChainIndex) : Digest :=
  honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx) (chainLength - 1)
theorem honestEndpoints_def : honestEndpoints f parameter lay tree secret leaf
    = fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret leaf chainIdx)) :=
  rfl
def LeafHit (payload : HashInput) : Prop :=
  payload ≠ leafPayload (honestEndpoints f parameter lay tree secret leaf)
    ∧ truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf) payload))
      = honestNode f parameter lay tree secret 0 leaf.val
theorem honestNode_zero_eq_leafHash :
    honestNode f parameter lay tree secret 0 leaf.val
      = truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf)
          (leafPayload (honestEndpoints f parameter lay tree secret leaf)))) := by
  simp only [honestNode, treeNode_zero_eq, leafOfNat_val, evalWithAnswerFn_bind, leafHash,
    eval_tweakableHash, eval_oneTimePublicKey, honestEndpoints_def]
theorem otsLeaf_extract (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some codeword)
    (hleaf : evalWithAnswerFn f (otsLeafAttempt parameter lay tree leaf message counter values)
      = some (honestNode f parameter lay tree secret 0 leaf.val)) :
    (∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val)
      ∨ LeafHit f parameter lay tree secret leaf
          (leafPayload fun chainIdx => walkValue f parameter lay tree leaf chainIdx
            (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val))
      ∨ ∃ (chainIdx : ChainIndex) (offset : Nat)
          (hoffset : (codeword chainIdx).val + offset < chainLength - 1), offset < chainLength - 1
            - (codeword chainIdx).val
            ∧ ChainHit f parameter lay tree leaf chainIdx (secret leaf chainIdx)
                ((codeword chainIdx).val + offset) hoffset
                (walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
                  (values chainIdx) offset) := by
  classical
  have hrecovered : evalWithAnswerFn f (leafHash parameter lay tree leaf
        (fun chainIdx => walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
          (values chainIdx) (chainLength - 1 - (codeword chainIdx).val)))
      = honestNode f parameter lay tree secret 0 leaf.val := by
    simp only [otsLeafAttempt, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hencode,
      evalWithAnswerFn_sequenceFin] at hleaf
    simpa [walkValue, recoverChain] using hleaf
  by_cases hpayload : (leafPayload fun chainIdx => walkValue f parameter lay tree leaf chainIdx
      (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val))
      = leafPayload (honestEndpoints f parameter lay tree secret leaf)
  · have hendpoints := leafPayload_injective hpayload
    have hchains : ∀ chainIdx : ChainIndex,
        values chainIdx = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val
          ∨ ∃ (offset : Nat) (hoffset : (codeword chainIdx).val + offset < chainLength - 1),
              offset < chainLength - 1 - (codeword chainIdx).val
                ∧ ChainHit f parameter lay tree leaf chainIdx (secret leaf chainIdx)
                    ((codeword chainIdx).val + offset) hoffset
                    (walkValue f parameter lay tree leaf chainIdx (codeword chainIdx).val
                      (values chainIdx) offset) := by
      intro chainIdx
      have hdigit : (codeword chainIdx).val ≤ chainLength - 1 := by
        have := (codeword chainIdx).isLt
        simp only [chainLength, winternitzBits] at this ⊢
        omega
      refine chainWalk_extract f parameter lay tree leaf chainIdx (secret leaf chainIdx)
        (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val)
        (by omega) ?_
      have := congrFun hendpoints chainIdx
      rw [show (codeword chainIdx).val + (chainLength - 1 - (codeword chainIdx).val)
        = chainLength - 1 by omega]
      exact this
    by_cases hall : ∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leaf chainIdx (secret leaf chainIdx)
            (codeword chainIdx).val
    · exact Or.inl hall
    · obtain ⟨chainIdx, hne⟩ := not_forall.mp hall
      rcases hchains chainIdx with hhonest | ⟨offset, hoffset, hlt, hhit⟩
      · exact absurd hhonest hne
      · exact Or.inr (Or.inr ⟨chainIdx, offset, hoffset, hlt, hhit⟩)
  · exact Or.inr (Or.inl ⟨hpayload, by
      rw [← hrecovered, leafHash, eval_tweakableHash]⟩)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_Position ====
section

namespace SphincsSecurity
open OracleComp
inductive Position where
  | chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (heap : Fin (2 ^ ftsTreeHeight))
  deriving DecidableEq, Fintype
namespace Position
def domain : Position → HashDomain
  | .chain lay tree leafIdx chainIdx step => HashDomain.chain lay tree leafIdx chainIdx step
  | .leaf lay tree leafIdx => HashDomain.leaf lay tree leafIdx
  | .node lay tree level nodeIdx => HashDomain.node lay tree (level.val + 1) nodeIdx.val
  | .ftsLeaf index tree leafIdx => HashDomain.ftsLeaf index tree leafIdx.val
  | .ftsNode index tree heap => HashDomain.ftsNode index tree heap.val
theorem domain_inRange (p : Position) : p.domain.InRange := by
  cases p with
  | node lay tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [maxLayerHeight] at hlevel hnode
      show level.val + 1 < 2 ^ 32 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, by omega⟩
  | ftsNode index tree heap =>
      have hheap := heap.isLt
      simp only [ftsTreeHeight] at hheap
      show heap.val < 2 ^ 32
      omega
  | ftsLeaf index tree leafIdx =>
      have hleaf := leafIdx.isLt
      simp only [ftsTreeHeight] at hleaf
      show leafIdx.val < 2 ^ 32
      omega
  | chain => exact (trivial : True)
  | leaf => exact (trivial : True)
theorem domain_injective {p q : Position} (h : p.domain = q.domain) : p = q := by
  cases p <;> cases q <;> simp only [domain] at h <;> simp_all [Fin.ext_iff]
def lastChainStep : ChainStep := ⟨chainLength - 2, by have := OtsCode.two_le_chainLength; omega⟩
def children : Position → List Position
  | .chain lay tree leafIdx chainIdx step =>
      if h : 0 < step.val then [.chain lay tree leafIdx chainIdx ⟨step.val - 1, by omega⟩] else []
  | .leaf lay tree leafIdx =>
      List.ofFn fun chainIdx : ChainIndex => .chain lay tree leafIdx chainIdx lastChainStep
  | .node lay tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight then
        if hlevel : 0 < level.val then
          [.node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
            .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .ftsLeaf _ _ _ => []
  | .ftsNode index tree heap =>
      if hpos : 0 < heap.val then
        if hidx : 2 * heap.val + 1 < 2 ^ ftsTreeHeight then
          [.ftsNode index tree ⟨2 * heap.val, by omega⟩, .ftsNode index tree ⟨2 * heap.val + 1, hidx⟩]
        else
          [.ftsLeaf index tree ⟨2 * heap.val - 2 ^ ftsTreeHeight, by have := heap.isLt; omega⟩,
            .ftsLeaf index tree ⟨2 * heap.val + 1 - 2 ^ ftsTreeHeight, by have := heap.isLt; omega⟩]
      else []
theorem children_length_le (p : Position) : p.children.length ≤ numChains := by
  have htwo := OtsCode.two_le_numChains
  cases p <;> simp only [children] <;> (try split_ifs) <;>
    simp only [List.length_ofFn, List.length_cons, List.length_nil] <;> omega
def depth : Position → Nat
  | .chain _ _ _ _ step => step.val
  | .leaf _ _ _ => chainLength
  | .node _ _ level _ => chainLength + 1 + level.val
  | .ftsLeaf _ _ _ => 0
  | .ftsNode _ _ heap => ftsTreeHeight - Nat.log2 heap.val
theorem depth_lt_of_mem_children {c d : Position} (hmem : c ∈ d.children) :
    c.depth < d.depth := by
  cases d with
  | chain lay tree leafIdx chainIdx step =>
      rw [children] at hmem
      split at hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        simp only [depth]
        omega
      · simp at hmem
  | leaf =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨chainIdx, hmem⟩ := hmem
      subst hmem
      have := OtsCode.two_le_chainLength
      simp only [depth, lastChainStep]
      omega
  | node lay tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | ftsLeaf => simp [children] at hmem
  | ftsNode index tree heap =>
      rw [children] at hmem
      have hheap := heap.isLt
      split at hmem
      · rename_i hpos
        have hlog : Nat.log2 heap.val < ftsTreeHeight := by
          rw [Nat.log2_lt (by omega)]; exact hheap
        split at hmem
        · rename_i hidx
          rcases List.mem_pair.mp hmem with h | h <;> subst h <;> simp only [depth]
          · have : Nat.log2 (2 * heap.val) = Nat.log2 heap.val + 1 := by
              exact Nat.log2_two_mul (by omega)
            omega
          · have : Nat.log2 (2 * heap.val + 1) = Nat.log2 heap.val + 1 := by
              rw [Nat.log2_def, if_pos (by omega), show (2 * heap.val + 1) / 2 = heap.val by omega]
            omega
        · rcases List.mem_pair.mp hmem with h | h <;> subst h <;> simp only [depth] <;> omega
      · simp at hmem
end Position
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_Honest ====
section

namespace SphincsSecurity
open OracleComp
namespace Concrete
variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
theorem honestChain_zero (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (secret : Digest) :
    honestChain f parameter lay tree leafIdx chainIdx secret 0 = secret := by
  simp [honestChain, chainWalk]
end Concrete
variable (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
noncomputable def honestPayload : Position → HashInput
  | .chain lay tree leafIdx chainIdx step =>
      Concrete.digestBytes (Concrete.honestChain f parameter lay tree leafIdx chainIdx
        (otsSecret lay tree leafIdx chainIdx) step.val)
  | .leaf lay tree leafIdx =>
      Concrete.leafPayload
        (Concrete.honestEndpoints f parameter lay tree (otsSecret lay tree) leafIdx)
  | .node lay tree level nodeIdx =>
      Concrete.nodePayload
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val (2 * nodeIdx.val))
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val
          (2 * nodeIdx.val + 1))
  | .ftsLeaf index tree leafIdx => Concrete.digestBytes (ftsSecret index tree leafIdx)
  | .ftsNode index tree heap =>
      Concrete.nodePayload
        (Concrete.honestFtsHeap f parameter index tree (ftsSecret index tree) (2 * heap.val))
        (Concrete.honestFtsHeap f parameter index tree (ftsSecret index tree) (2 * heap.val + 1))
noncomputable def honestInput (p : Position) : HashInput :=
  tweakableHashInput parameter p.domain (honestPayload f parameter otsSecret ftsSecret p)
noncomputable def honestValue (p : Position) : Digest :=
  truncateHash (f (honestInput f parameter otsSecret ftsSecret p))
theorem honestValue_chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    honestValue f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
      = Concrete.honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (step.val + 1) := by
  rw [Concrete.honestChain_succ f parameter lay tree leafIdx chainIdx _ step.val step.isLt]
  rfl
theorem honestValue_leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.leaf lay tree leafIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) 0 leafIdx.val := by
  rw [Concrete.honestNode_zero_eq_leafHash f parameter lay tree (otsSecret lay tree) leafIdx]
  rfl
theorem honestValue_node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.node lay tree level nodeIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) (level.val + 1)
          nodeIdx.val := by
  rw [Concrete.honestNode_succ f parameter lay tree (otsSecret lay tree) level.val nodeIdx.val]
  rfl
theorem honestValue_ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) :
    honestValue f parameter otsSecret ftsSecret (.ftsLeaf index tree leafIdx)
      = Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) 0 leafIdx.val := by
  rw [Concrete.honestFtsNode_zero f parameter index tree (ftsSecret index tree) leafIdx]
  rfl
theorem honestValue_ftsNode (index : Index) (tree : FtsTree) (heap : Fin (2 ^ ftsTreeHeight))
    (hpos : 0 < heap.val) :
    honestValue f parameter otsSecret ftsSecret (.ftsNode index tree heap)
      = Concrete.honestFtsHeap f parameter index tree (ftsSecret index tree) heap.val := by
  rw [Concrete.honestFtsHeap_node f parameter index tree (ftsSecret index tree) heap.val hpos heap.isLt]
  rfl
def Position.ftsRoot (index : Index) : Position := .ftsNode index Concrete.porsTree ⟨1, by decide⟩
theorem honestValue_ftsRoot (index : Index) :
    honestValue f parameter otsSecret ftsSecret (Position.ftsRoot index)
      = Concrete.honestFtsKey f parameter index (ftsSecret index) := by
  rw [Position.ftsRoot, honestValue_ftsNode f parameter otsSecret ftsSecret index _ _ (by decide),
    Concrete.honestFtsKey_eq_heap]
def Position.Valid : Position → Prop
  | .node _ _ _ nodeIdx => 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight
  | .ftsNode _ _ heap => 0 < heap.val
  | _ => True
noncomputable def childValues (p : Position) : List Digest :=
  p.children.map (honestValue f parameter otsSecret ftsSecret)
noncomputable def slots : Position → List Digest
  | .chain lay tree leafIdx chainIdx step =>
      if step.val = 0 then [otsSecret lay tree leafIdx chainIdx]
      else childValues f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
  | .ftsLeaf index tree leafIdx => [ftsSecret index tree leafIdx]
  | p => childValues f parameter otsSecret ftsSecret p
theorem honestPayload_eq_slots {p : Position} (hvalid : p.Valid) :
    honestPayload f parameter otsSecret ftsSecret p
      = (slots f parameter otsSecret ftsSecret p).flatMap Concrete.digestBytes := by
  cases p with
  | chain lay tree leafIdx chainIdx step =>
      rcases Nat.eq_zero_or_pos step.val with hstep | hstep
      · have hslots : slots f parameter otsSecret ftsSecret
            (.chain lay tree leafIdx chainIdx step) = [otsSecret lay tree leafIdx chainIdx] := by
          simp only [slots, if_pos hstep]
        rw [hslots]
        simp only [honestPayload, hstep, Concrete.honestChain_zero, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      · obtain ⟨s, hs⟩ : ∃ s, step.val = s + 1 := ⟨step.val - 1, by omega⟩
        have hslt : s < chainLength - 1 := by have := step.isLt; omega
        have hchildren : (Position.chain lay tree leafIdx chainIdx step).children
            = [.chain lay tree leafIdx chainIdx ⟨s, hslt⟩] := by
          rw [Position.children, dif_pos hstep]
          simp only [List.cons.injEq, Position.chain.injEq, Fin.mk.injEq, and_true, true_and]
          omega
        have hslots : slots f parameter otsSecret ftsSecret
            (.chain lay tree leafIdx chainIdx step)
            = [honestValue f parameter otsSecret ftsSecret
                (.chain lay tree leafIdx chainIdx ⟨s, hslt⟩)] := by
          simp only [slots, if_neg (by omega : ¬ step.val = 0), childValues, hchildren,
            List.map_cons, List.map_nil]
        rw [hslots, honestValue_chain]
        simp only [honestPayload, List.flatMap_cons, List.flatMap_nil, List.append_nil, hs]
  | leaf lay tree leafIdx =>
      have hslots : slots f parameter otsSecret ftsSecret (.leaf lay tree leafIdx)
          = List.ofFn fun chainIdx : ChainIndex => honestValue f parameter otsSecret ftsSecret
              (.chain lay tree leafIdx chainIdx Position.lastChainStep) := by
        simp only [slots, childValues, Position.children, List.map_ofFn, Function.comp_def]
      rw [hslots]
      simp only [honestPayload, Concrete.leafPayload]
      refine congrArg _ (congrArg _ (funext fun chainIdx => ?_))
      rw [honestValue_chain]
      rfl
  | node lay tree level nodeIdx =>
      simp only [Position.Valid] at hvalid
      rcases Nat.eq_zero_or_pos level.val with hlevel | hlevel
      · have hchildren : (Position.node lay tree level nodeIdx).children
            = [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
              .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_neg (by omega)]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_leaf, honestValue_leaf, hlevel]
      · have hchildren : (Position.node lay tree level nodeIdx).children
            = [.node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩
                ⟨2 * nodeIdx.val, by omega⟩,
              .node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩
                ⟨2 * nodeIdx.val + 1, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_pos hlevel]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_node, honestValue_node, show level.val - 1 + 1 = level.val from by omega]
  | ftsLeaf index tree leafIdx =>
      simp [slots, honestPayload]
  | ftsNode index tree heap =>
      simp only [Position.Valid] at hvalid
      have hheap := heap.isLt
      have heven : (2 : Nat) ^ ftsTreeHeight = 2 * 2 ^ (ftsTreeHeight - 1) := rfl
      by_cases hidx : 2 * heap.val + 1 < 2 ^ ftsTreeHeight
      · have hchildren : (Position.ftsNode index tree heap).children
            = [.ftsNode index tree ⟨2 * heap.val, by omega⟩,
              .ftsNode index tree ⟨2 * heap.val + 1, hidx⟩] := by
          rw [Position.children, dif_pos hvalid, dif_pos hidx]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_ftsNode _ _ _ _ _ _ _ (by simp only; omega),
          honestValue_ftsNode _ _ _ _ _ _ _ (by simp only; omega)]
      · have hchildren : (Position.ftsNode index tree heap).children
            = [.ftsLeaf index tree ⟨2 * heap.val - 2 ^ ftsTreeHeight, by omega⟩,
              .ftsLeaf index tree ⟨2 * heap.val + 1 - 2 ^ ftsTreeHeight, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_neg hidx]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_ftsLeaf, honestValue_ftsLeaf, ← Concrete.honestFtsHeap_leaf,
          ← Concrete.honestFtsHeap_leaf]
        simp only
        rw [show 2 ^ ftsTreeHeight + (2 * heap.val - 2 ^ ftsTreeHeight) = 2 * heap.val by omega,
          show 2 ^ ftsTreeHeight + (2 * heap.val + 1 - 2 ^ ftsTreeHeight) = 2 * heap.val + 1 by omega]
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_Settled ====
section

namespace SphincsSecurity
open OracleComp OracleSpec
def fromCache (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0
theorem agreesWithFn_fromCache (cache : QueryCache HashSpec) :
    cache.AgreesWithFn (fromCache cache) := by
  intro input answer hcached
  simp [fromCache, hcached]
variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
variable {parameter} {otsSecret} {ftsSecret}
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Cached ====
section

section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
theorem sequenceFin_component_query_mem {alpha : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha) (index : Fin n) {input : HashInput}
    (hinput : input ∈ queriedInputs f (computation index)) :
    input ∈ queriedInputs f (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      cases index using Fin.cases with
      | zero =>
          rw [sequenceFin]
          exact queriedInputs_mono_bind_left f (computation 0) _ hinput
      | succ index =>
          rw [sequenceFin]
          apply queriedInputs_mono_bind_right f (computation 0)
          apply queriedInputs_mono_bind_left
          exact ih (fun index : Fin n => computation index.succ) index hinput
theorem chainWalk_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) (offset : Nat)
    (hoffset : offset < steps) (hrange : start + offset < chainLength - 1) :
    tweakableHashInput parameter (.chain lay tree leafIdx chainIdx ⟨start + offset, hrange⟩)
        (digestBytes (walkValue f parameter lay tree leafIdx chainIdx start value offset))
      ∈ queriedInputs f (chainWalk parameter lay tree leafIdx chainIdx start steps value) := by
  induction steps generalizing offset with
  | zero => omega
  | succ steps ih =>
      rw [chainWalk]
      split_ifs with hstep
      · rw [queriedInputs_bind]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hoffset with hlt | heq
        · exact List.mem_append_left _ (ih offset hlt hrange)
        · subst offset
          apply List.mem_append_right _
          simp only [walkValue, queriedInputs_tweakableHash, List.mem_singleton]
      · rw [queriedInputs_bind]
        apply List.mem_append_left
        exact ih offset (by omega) hrange
theorem leafHash_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    tweakableHashInput parameter (.leaf lay tree leafIdx) (leafPayload endpoints)
      ∈ queriedInputs f (leafHash parameter lay tree leafIdx endpoints) := by
  simp [leafHash]
theorem otsLeaf_leaf_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter)
      = some codeword) :
    tweakableHashInput parameter (.leaf lay tree leafIdx)
        (leafPayload fun chainIdx => walkValue f parameter lay tree leafIdx chainIdx
          (codeword chainIdx).val (values chainIdx) (chainLength - 1 - (codeword chainIdx).val))
      ∈ queriedInputs f (otsLeafAttempt parameter lay tree leafIdx message counter values) := by
  simp only [otsLeafAttempt]
  apply queriedInputs_mono_bind_right
  rw [hencode]
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  simpa only [evalWithAnswerFn_sequenceFin, recoverChain, walkValue] using
    leafHash_query_mem f parameter lay tree leafIdx
      (fun chainIdx => evalWithAnswerFn f
        (recoverChain parameter lay tree leafIdx chainIdx (codeword chainIdx) (values chainIdx)))
theorem otsLeaf_chain_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter)
      = some codeword) (chainIdx : ChainIndex) (offset : Nat)
    (hoffset : offset < chainLength - 1 - (codeword chainIdx).val)
    (hrange : (codeword chainIdx).val + offset < chainLength - 1) :
    tweakableHashInput parameter
        (.chain lay tree leafIdx chainIdx ⟨(codeword chainIdx).val + offset, hrange⟩)
        (digestBytes (walkValue f parameter lay tree leafIdx chainIdx (codeword chainIdx).val
          (values chainIdx) offset))
      ∈ queriedInputs f (otsLeafAttempt parameter lay tree leafIdx message counter values) := by
  simp only [otsLeafAttempt]
  apply queriedInputs_mono_bind_right
  rw [hencode]
  apply queriedInputs_mono_bind_left
  apply sequenceFin_component_query_mem f _ chainIdx
  exact chainWalk_query_mem f parameter lay tree leafIdx chainIdx (codeword chainIdx).val
    (chainLength - 1 - (codeword chainIdx).val) (values chainIdx) offset hoffset hrange
theorem ftsLeafHash_query_mem (index : Index) (tree : FtsTree) (leafIdx : Nat)
    (secret : Digest) :
    tweakableHashInput parameter (.ftsLeaf index tree leafIdx) (digestBytes secret)
      ∈ queriedInputs f (ftsLeafHash parameter index tree leafIdx secret) := by
  simp [ftsLeafHash]
theorem treeFold_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (path : Nat → Digest) (value : Digest) (levels offset : Nat) (hoffset : offset < levels) :
    tweakableHashInput parameter
        (.node lay tree (offset + 1) (leafIdx.val / 2 ^ (offset + 1)))
        (treeFoldPayload f parameter lay tree leafIdx path value offset)
      ∈ queriedInputs f (treeFold parameter lay tree leafIdx path levels value) := by
  induction levels generalizing offset with
  | zero => omega
  | succ levels ih =>
      rw [treeFold_succ_eq, queriedInputs_bind]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hoffset with hlt | heq
      · exact List.mem_append_left _ (ih offset hlt)
      · subst offset
        apply List.mem_append_right _
        simp only [foldValue, treeFoldPayload]
        cases leafIdx.val.testBit levels <;> simp
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity
open OracleComp OracleSpec
def CachedRun {alpha : Type} (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) : Prop :=
  ∀ input ∈ queriedInputs f oa, cache input ≠ none
theorem CachedRun.pure {alpha : Type} (cache : QueryCache HashSpec)
    (f : QueryImpl HashSpec Id) (value : alpha) :
    CachedRun cache f (pure value) := by
  simp [CachedRun]
theorem CachedRun.bind_left {alpha beta : Type} {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta} (h : CachedRun cache f (oa >>= next)) :
    CachedRun cache f oa := by
  intro input hinput
  exact h input (queriedInputs_mono_bind_left f oa next hinput)
theorem CachedRun.bind_right {alpha beta : Type} {cache : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta} (h : CachedRun cache f (oa >>= next)) :
    CachedRun cache f (next (evalWithAnswerFn f oa)) := by
  intro input hinput
  exact h input (queriedInputs_mono_bind_right f oa next hinput)
theorem CachedRun.mono {alpha : Type} {cache cache' : QueryCache HashSpec}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    (hle : cache ≤ cache') (h : CachedRun cache f oa) :
    CachedRun cache' f oa := by
  intro input hinput
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (h input hinput)
  rw [hle hanswer]
  simp
namespace Concrete
variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}
end Concrete
end SphincsSecurity
end
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Slot ====
section

namespace SphincsSecurity
open OracleComp
def payloadOf (input : HashInput) : HashInput := input.drop 32
theorem payloadOf_tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : payloadOf (tweakableHashInput parameter domain payload) = payload := by
  have hlength : (tweakBytes domain ++ bytesLE 16 parameter).length = 32 := by
    simp [tweakBytes_length, bytesLE_length 16 parameter]
  simp only [payloadOf, tweakableHashInput]
  rw [← hlength, List.drop_left]
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Charge ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
def AtPosition (input : HashInput) (p : Position) : Prop :=
  ∃ payload, input = tweakableHashInput parameter p.domain payload
theorem atPosition_unique {input : HashInput} {p q : Position} (hp : AtPosition parameter input p)
    (hq : AtPosition parameter input q) : p = q := by
  obtain ⟨payload, hpayload⟩ := hp
  obtain ⟨payload', hpayload'⟩ := hq
  exact Position.domain_injective (tweakableHashInput_injective parameter
    (Position.domain_inRange p) (Position.domain_inRange q) (hpayload ▸ hpayload')).1
theorem le_cacheQuery {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none) : cache ≤ cache.cacheQuery input answer := by
  intro x u hx
  by_cases hxeq : x = input
  · rw [hxeq, huncached] at hx
    simp at hx
  · rwa [QueryCache.cacheQuery_of_ne _ _ hxeq]
def Finite (cache : QueryCache HashSpec) : Prop := {input | cache input ≠ none}.Finite
theorem finite_empty : Finite (∅ : QueryCache HashSpec) := by
  simp [Finite]
theorem Finite.of_enncard_le {cache : QueryCache HashSpec} {q : Nat}
    (hle : QueryCache.enncard cache ≤ (q : ℝ≥0∞)) : Finite cache := by
  rw [QueryCache.enncard] at hle
  have hfiniteToSet : cache.toSet.Finite := by
    rw [← Set.encard_ne_top_iff]
    intro htop
    rw [htop] at hle
    exact not_top_le_coe hle
  let cachedInputs : Set HashInput := {input | cache input ≠ none}
  have hsubset : cachedInputs ⊆ Sigma.fst '' cache.toSet := by
    intro input hcached
    obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
    exact ⟨⟨input, answer⟩, hanswer, rfl⟩
  exact (hfiniteToSet.image Sigma.fst).subset hsubset
theorem Finite.cachedInputs_ncard_toENNReal_eq_enncard
    {cache : QueryCache HashSpec} (hfinite : Finite cache) :
    ({input | cache input ≠ none}.ncard : ℝ≥0∞) = QueryCache.enncard cache := by
  let cachedInputs : Set HashInput := {input | cache input ≠ none}
  have himage : Sigma.fst '' cache.toSet = cachedInputs := by
    ext input
    constructor
    · rintro ⟨⟨cachedInput, answer⟩, hcached, heq⟩
      subst input
      change cache cachedInput = some answer at hcached
      exact Option.ne_none_iff_exists'.mpr ⟨answer, hcached⟩
    · intro hcached
      obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
      exact ⟨⟨input, answer⟩, hanswer, rfl⟩
  have hinjective : Set.InjOn Sigma.fst cache.toSet := by
    rintro ⟨leftInput, leftAnswer⟩ hleft ⟨rightInput, rightAnswer⟩ hright heq
    simp only at heq
    subst rightInput
    change cache leftInput = some leftAnswer at hleft
    change cache leftInput = some rightAnswer at hright
    have hanswer : leftAnswer = rightAnswer := by
      rw [hleft] at hright
      exact Option.some.inj hright
    subst rightAnswer
    rfl
  have hencard : cachedInputs.encard = cache.toSet.encard := by
    rw [← himage]
    exact hinjective.encard_image
  have hcast := hfinite.cast_ncard_eq.trans hencard
  simpa only [cachedInputs, QueryCache.enncard, ENat.toENNReal_coe] using
    congrArg ENat.toENNReal hcast
theorem finite_cacheQuery {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (input : HashInput) (answer : HashOutput) : Finite (cache.cacheQuery input answer) := by
  refine Set.Finite.subset (hfinite.insert input) fun x hx => ?_
  by_cases hxeq : x = input
  · exact Set.mem_insert_iff.mpr (Or.inl hxeq)
  · refine Set.mem_insert_iff.mpr (Or.inr ?_)
    simpa only [Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ hxeq] using hx
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Scheme_SignSupport ====
section

section
namespace SphincsSecurity.Concrete
open OracleComp
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]
theorem layerMessage_bottomLayer (secretKey : SecretKey) (index : Index) :
    layerMessage (m := m) secretKey index bottomLayer
      = ftsKey secretKey.parameter index (secretKey.ftsSecret index) := by
  rw [layerMessage, dif_neg (by decide)]
theorem layerMessage_of_lt (secretKey : SecretKey) (index : Index) (lay : Layer)
    (hbelow : lay.val + 1 < numLayers) :
    layerMessage (m := m) secretKey index lay
      = treeRoot secretKey.parameter ⟨lay.val + 1, hbelow⟩
          (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
          (secretKey.otsSecret ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)) := by
  rw [layerMessage, dif_pos hbelow]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}
theorem counters_of_verify (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn f (verify publicKey message signature) = true) :
    CountersInRange signature := by
  by_contra hcounters
  rw [verify_eq_of_not_counters publicKey message signature hcounters] at hverify
  simp at hverify
theorem verify_extract (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn f (verify publicKey message signature) = true)
    (hrun : CachedRun cache f (verify publicKey message signature)) :
    ∃ digest : MessageDigest,
      evalWithAnswerFn f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest
        ∧ CachedRun cache f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness)
        ∧ ∃ ftsPublicKey : Digest,
          evalWithAnswerFn f (ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts) = some ftsPublicKey
            ∧ evalWithAnswerFn f
              (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey)
              = some publicKey.root
            ∧ CachedRun cache f (ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts)
            ∧ CachedRun cache f
              (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey) := by
  have hcounters := counters_of_verify publicKey message signature hverify
  let digest := evalWithAnswerFn f
    (messageDigest publicKey.parameter publicKey.root message signature.randomness)
  rw [verify_eq _ _ _ hcounters] at hverify hrun
  rw [evalWithAnswerFn_bind] at hverify
  have hmessageRun := hrun.bind_left
  have hafterDigest := hrun.bind_right
  change evalWithAnswerFn f (do
    match ← ftsRecover publicKey.parameter (digestIndex digest) (slotValue (digestLeaves digest))
        signature.fts with
    | none => pure false
    | some ftsPublicKey =>
        match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
            ftsPublicKey with
        | none => pure false
        | some root => pure (decide (root = publicKey.root))) = true at hverify
  change CachedRun cache f (do
    match ← ftsRecover publicKey.parameter (digestIndex digest) (slotValue (digestLeaves digest))
        signature.fts with
    | none => pure false
    | some ftsPublicKey =>
        match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
            ftsPublicKey with
        | none => pure false
        | some root => pure (decide (root = publicKey.root))) at hafterDigest
  have hfts := hafterDigest.bind_left
  rw [evalWithAnswerFn_bind] at hverify
  have hafterFts := hafterDigest.bind_right
  revert hverify hafterFts
  cases hkey : evalWithAnswerFn f (ftsRecover publicKey.parameter (digestIndex digest)
      (slotValue (digestLeaves digest)) signature.fts) with
  | none => intro hverify; simp at hverify
  | some ftsPublicKey =>
      intro hverify hafterFts
      simp only at hverify hafterFts
      rw [evalWithAnswerFn_bind] at hverify
      have hlayersRun := hafterFts.bind_left
      refine ⟨digest, rfl, hmessageRun, ftsPublicKey, hkey, ?_, hfts, hlayersRun⟩
      cases hresult : evalWithAnswerFn f
          (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey) with
      | none =>
          rw [hresult] at hverify
          simp at hverify
      | some root =>
          rw [hresult] at hverify
          simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hverify
          simp [hverify]
theorem verifyLayers_succ_extract_cached (index : Index) (signature : Signature)
    (remaining : Nat) (hlayer : remaining < numLayers) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (remaining + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (remaining + 1) message)) :
    ∃ leafValue,
      let lay : Layer := ⟨remaining, hlayer⟩
      let tree := treeIndexAt index lay
      let leafIdx := leafIndexAt index lay
      let rootValue := foldValue f parameter lay tree leafIdx (signaturePath signature lay)
        leafValue (layerHeight lay)
      evalWithAnswerFn f (otsLeafAttempt parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay)) = some leafValue
        ∧ evalWithAnswerFn f (verifyLayers parameter index signature remaining rootValue)
          = some target
        ∧ CachedRun cache f (otsLeafAttempt parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay))
        ∧ CachedRun cache f (treeFold parameter lay tree leafIdx (signaturePath signature lay)
          (layerHeight lay) leafValue)
        ∧ CachedRun cache f (verifyLayers parameter index signature remaining rootValue) := by
  obtain ⟨leafValue, hleaf, hrest⟩ :=
    verifyLayers_succ_extract f parameter index signature remaining hlayer message target hverify
  rw [verifyLayers_succ_eq, dif_pos hlayer] at hrun
  have hots := hrun.bind_left
  have hafter := hrun.bind_right
  rw [hleaf] at hafter
  exact ⟨leafValue, hleaf, hrest, hots, hafter.bind_left, hafter.bind_right⟩
def LayerFrame (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target leafValue : Digest) : Prop :=
  evalWithAnswerFn f
        (otsLeafAttempt parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay)) = some leafValue
      ∧ evalWithAnswerFn f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay))) = some target
      ∧ CachedRun cache f
        (otsLeafAttempt parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay))
      ∧ CachedRun cache f
        (treeFold parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) (layerHeight lay) leafValue)
      ∧ CachedRun cache f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay)))
def LayerRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest) : Prop :=
  ∃ leafValue, LayerFrame f cache parameter index signature lay message target leafValue
theorem layerRun_of_verify (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (lay.val + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (lay.val + 1) message)) :
    LayerRun f cache parameter index signature lay message target := by
  obtain ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩ :=
    verifyLayers_succ_extract_cached (f := f) (cache := cache) index signature lay.val lay.isLt
      message target hverify hrun
  exact ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩
theorem hypertree_walk (key : SecretKey) (index : Index) (signature : Signature) (Q : Layer → Prop)
    (hstep : ∀ lay message leafValue,
      LayerFrame f cache key.parameter index signature lay message key.root leafValue →
      foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) leafValue (layerHeight lay) =
        honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay))
          (layerHeight lay) 0 →
      message = evalWithAnswerFn f (layerMessage key index lay) ∧ Q lay)
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)
      (layerHeight topLayer) 0)
    (ftsPublicKey : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers key.parameter index signature numLayers ftsPublicKey) = some key.root)
    (hrun : CachedRun cache f (verifyLayers key.parameter index signature numLayers ftsPublicKey)) :
    (∀ lay, Q lay) ∧ ftsPublicKey = evalWithAnswerFn f (layerMessage key index bottomLayer) := by
  have hwalk : ∀ remaining, (hr : remaining ≤ numLayers) → ∀ message,
      evalWithAnswerFn f (verifyLayers key.parameter index signature remaining message) = some key.root →
      CachedRun cache f (verifyLayers key.parameter index signature remaining message) →
      (∀ lay : Layer, lay.val < remaining → Q lay) ∧
        (∀ h : 0 < remaining,
          message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by have := hr; omega⟩)) ∧
        (remaining = 0 → message = key.root) := by
    intro remaining
    induction remaining with
    | zero =>
        intro _ message hv _
        simp only [verifyLayers_zero_eq, evalWithAnswerFn_pure, Option.some.injEq] at hv
        exact ⟨fun lay h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _),
          fun _ => hv⟩
    | succ r ih =>
        intro hr message hv hc
        have hlayer : r < numLayers := by omega
        let lay : Layer := ⟨r, hlayer⟩
        obtain ⟨leafValue, hframe⟩ :=
          layerRun_of_verify (f := f) (cache := cache) index signature lay message key.root hv hc
        have hrest := ih (by omega) _ hframe.2.1 hframe.2.2.2.2
        have hfold : foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay) =
            honestNode f key.parameter lay (treeIndexAt index lay)
              (key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0 := by
          rcases Nat.eq_zero_or_pos r with hzero | hpos
          · have htop : lay = topLayer := Fin.ext hzero
            have htree : treeIndexAt index lay = rootTree := by
              rw [htop]
              exact Fin.ext (treeIndexAt_topLayer index)
            rw [hrest.2.2 hzero, hroot, htree, htop]
          · rw [hrest.2.1 hpos]
            have hbelow : r - 1 + 1 < numLayers := by omega
            rw [layerMessage_of_lt key index ⟨r - 1, by omega⟩ hbelow]
            have hl : (⟨r - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            simp only [hl]
            rfl
        obtain ⟨hmessage, hq⟩ := hstep lay message leafValue hframe hfold
        refine ⟨fun other hother => ?_, fun _ => hmessage, fun h => absurd h (Nat.succ_ne_zero r)⟩
        by_cases heq : other.val = r
        · have : other = lay := Fin.ext heq
          rw [this]
          exact hq
        · exact hrest.1 other (by omega)
  obtain ⟨hq, hmessage, _⟩ := hwalk numLayers le_rfl ftsPublicKey hverify hrun
  exact ⟨fun lay => hq lay lay.isLt, hmessage (by decide)⟩
def HonestLayerOpening (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (values : ChainIndex → Digest) (path : Nat → Digest) : Prop :=
  ∃ codeword : Encoding,
    evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter) = some codeword
      ∧ (∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (codeword chainIdx).val)
      ∧ ∀ level, level < layerHeight lay → path level
        = honestNode f parameter lay tree (otsSecret lay tree) level
          (Nat.xor (leafIdx.val / 2 ^ level) 1)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity
open OracleComp OracleSpec
noncomputable def replayRomImpl (f : QueryImpl HashSpec Id) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (f.liftTarget ProbComp).withCaching
noncomputable def replayHashImpl (f : QueryImpl HashSpec Id) :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp) :=
  (f.liftTarget ProbComp).withCaching
theorem replayRom_of_mem_support {alpha : Type} (oa : OracleComp OracleWorld alpha)
    (cache : QueryCache HashSpec) (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support ((simulateQ romImpl oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    (a, finalCache) ∈ support ((simulateQ (replayRomImpl f) oa).run cache) := by
  induction oa using OracleComp.inductionOn generalizing cache a finalCache with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hmem
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem ⊢
      obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
      refine ⟨⟨answer, middleCache⟩, ?_, ih answer middleCache a finalCache hrest hf⟩
      cases input with
      | inl sample =>
          change (answer, middleCache) ∈ support (((unifFwdImpl HashSpec) sample).run cache)
            at hquery ⊢
          exact hquery
      | inr hashInput =>
          change HashOutput at answer
          change (answer, middleCache) ∈ support
            (((randomOracle : QueryImpl HashSpec _) hashInput).run cache) at hquery
          have hmiddleLe : middleCache ≤ finalCache :=
            simulateQ_romImpl_cache_le (next answer) middleCache _ hrest
          change (answer, middleCache) ∈ support
            ((((f.liftTarget ProbComp).withCaching : QueryImpl HashSpec _) hashInput).run cache)
          cases hcache : cache hashInput with
          | some old =>
              rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
                Set.mem_singleton_iff] at hquery
              obtain ⟨rfl, rfl⟩ := hquery
              rw [QueryImpl.withCaching_run_some _ hcache, support_pure, Set.mem_singleton_iff]
          | none =>
              rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
              obtain ⟨sampled, _, heq⟩ := hquery
              obtain ⟨rfl, rfl⟩ := heq
              have hfanswer : f hashInput = answer :=
                hf (hmiddleLe (QueryCache.cacheQuery_self cache hashInput answer))
              rw [QueryImpl.withCaching_run_none _ hcache, support_map]
              refine ⟨f hashInput, ?_, ?_⟩
              · change f hashInput ∈ support (pure (f hashInput) : ProbComp HashOutput)
                exact Set.mem_singleton _
              · rw [hfanswer]
theorem replayHash_mem_randomOracle {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (cache : QueryCache HashSpec)
    (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support
      ((simulateQ (replayHashImpl f) oa).run cache)) :
    (a, finalCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache) := by
  induction oa using OracleComp.inductionOn generalizing cache a finalCache with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hmem
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem ⊢
      obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
      refine ⟨⟨answer, middleCache⟩, ?_, ih answer middleCache a finalCache hrest⟩
      change (answer, middleCache) ∈ support
        ((((f.liftTarget ProbComp).withCaching : QueryImpl HashSpec _) input).run cache)
        at hquery
      change (answer, middleCache) ∈ support
        (((randomOracle : QueryImpl HashSpec _) input).run cache)
      cases hcache : cache input with
      | some old =>
          rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
            Set.mem_singleton_iff] at hquery
          obtain ⟨rfl, rfl⟩ := hquery
          rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
            Set.mem_singleton_iff]
      | none =>
          rw [QueryImpl.withCaching_run_none _ hcache, support_map] at hquery
          obtain ⟨sampled, hsampled, heq⟩ := hquery
          have hsampledEq : sampled = f input := by
            change sampled ∈ support (pure (f input) : ProbComp HashOutput) at hsampled
            simpa using hsampled
          subst sampled
          obtain ⟨rfl, rfl⟩ := heq
          rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map]
          exact ⟨f input, by simp [uniformSampleImpl], rfl⟩
theorem replayHash_of_mem_support {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (cache : QueryCache HashSpec)
    (a : alpha) (finalCache : QueryCache HashSpec)
    (hmem : (a, finalCache) ∈ support
      ((simulateQ (replayHashImpl f) oa).run cache))
    (hf : finalCache.AgreesWithFn f) :
    cache ≤ finalCache ∧ evalWithAnswerFn f oa = a ∧ CachedRun finalCache f oa := by
  have hrandom := replayHash_mem_randomOracle f oa cache a finalCache hmem
  obtain ⟨hle, heval, hqueries⟩ := replay_of_mem_support oa cache a finalCache hrandom f hf
  exact ⟨hle, heval, hqueries⟩
theorem simulateQ_replayRom_liftM {alpha : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) :
    simulateQ (replayRomImpl f) (liftM oa : OracleComp OracleWorld alpha)
      = simulateQ (replayHashImpl f) oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa
end SphincsSecurity
end
section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
abbrev LayerPart :=
  Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)
def SuccessfulDigestRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : Prop :=
  randomness ∈ support sampleRandomness
    ∧ evalWithAnswerFn f (signAttempt secretKey message randomness) = some (index, leaves)
    ∧ CachedRun cache f (signAttempt secretKey message randomness)
theorem SuccessfulDigestRun.extract {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {randomness : Randomness} {index : Index}
    {leaves : IndexGroup → FtsLeaf}
    (hrun : SuccessfulDigestRun f cache secretKey message randomness index leaves) :
    randomness ∈ support sampleRandomness
      ∧ ∃ digest : MessageDigest,
        evalWithAnswerFn f
            (messageDigest secretKey.parameter secretKey.root message randomness) = digest
          ∧ Admissible digest
          ∧ index = digestIndex digest
          ∧ leaves = digestLeaves digest
          ∧ CachedRun cache f
            (messageDigest secretKey.parameter secretKey.root message randomness) := by
  refine ⟨hrun.1, ?_⟩
  have heval := hrun.2.1
  simp only [signAttempt, evalWithAnswerFn_bind] at heval
  let digest := evalWithAnswerFn f
    (messageDigest secretKey.parameter secretKey.root message randomness)
  by_cases hadmissible : Admissible digest
  · simp only [show Admissible (evalWithAnswerFn f
        (messageDigest secretKey.parameter secretKey.root message randomness)) from hadmissible,
      if_true, evalWithAnswerFn_pure] at heval
    have hresult : (digestIndex digest, digestLeaves digest) = (index, leaves) :=
      Option.some.inj heval
    have hfields := Prod.mk.inj hresult
    refine ⟨digest, rfl, hadmissible, hfields.1.symm, hfields.2.symm, ?_⟩
    exact hrun.2.2.bind_left
  · simp only [show ¬ Admissible (evalWithAnswerFn f
        (messageDigest secretKey.parameter secretKey.root message randomness)) from hadmissible,
      if_false, evalWithAnswerFn_pure] at heval
    simp at heval
theorem successfulDigestLoop_of_mem_support (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (message : Message) (attempts : Nat) (randomness : Randomness)
    (index : Index) (leaves : IndexGroup → FtsLeaf)
    (beforeCache afterCache finalCache : QueryCache HashSpec)
    (hmem : (some (randomness, index, leaves), afterCache) ∈ support
      ((simulateQ (replayRomImpl f) (signDigestLoop attempts secretKey message)).run beforeCache))
    (hleFinal : afterCache ≤ finalCache) (hf : finalCache.AgreesWithFn f) :
    SuccessfulDigestRun f finalCache secretKey message randomness index leaves := by
  induction attempts generalizing beforeCache afterCache randomness index leaves with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      cases hmem.1
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨sampledRandomness, sampleCache⟩, hsample, hrest⟩ := hmem
      have hsample' : (sampledRandomness, sampleCache) ∈ support
          ((simulateQ (unifFwdImpl HashSpec) sampleRandomness).run beforeCache) := by
        simpa only [replayRomImpl, QueryImpl.simulateQ_add_liftM_left] using hsample
      rw [unifFwdImpl.simulateQ_run, support_map] at hsample'
      obtain ⟨sampledRandomness', hsampled, heq⟩ := hsample'
      obtain ⟨rfl, rfl⟩ := heq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      cases attempt with
      | none =>
          exact ih (randomness := randomness) (index := index) (leaves := leaves)
            (beforeCache := attemptCache) (afterCache := afterCache) hfinish hleFinal
      | some selected =>
          obtain ⟨selectedIndex, selectedLeaves⟩ := selected
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hfinish
          obtain ⟨hresult, hcache⟩ := hfinish
          obtain ⟨rfl, rfl, rfl⟩ := hresult
          have hleAttempt : attemptCache ≤ finalCache := by
            rw [← hcache]
            exact hleFinal
          have hattempt' : (some (index, leaves), attemptCache) ∈ support
              ((simulateQ (replayHashImpl f)
                (signAttempt secretKey message randomness)).run beforeCache) := by
            simpa only [simulateQ_replayRom_liftM] using hattempt
          have hfAttempt : attemptCache.AgreesWithFn f :=
            fun _ _ hcached => hf (hleAttempt hcached)
          obtain ⟨_, heval, hcached⟩ := replayHash_of_mem_support f
            (signAttempt secretKey message randomness) beforeCache (some (index, leaves))
            attemptCache hattempt' hfAttempt
          exact ⟨hsampled, heval, hcached.mono hleAttempt⟩
theorem index_eq_of_bottom_position_eq {left right : Index}
    (htree : treeIndexAt left bottomLayer = treeIndexAt right bottomLayer)
    (hleaf : leafIndexAt left bottomLayer = leafIndexAt right bottomLayer) : left = right := by
  apply Fin.ext
  have htreeVal := congrArg Fin.val htree
  have hleafVal := congrArg Fin.val hleaf
  have habove : heightAbove bottomLayer = 29 := by decide
  have hheight : layerHeight bottomLayer = 5 := by decide
  have hleftTree : (treeIndexAt left bottomLayer).val = left.val / 32 := by
    rw [treeIndexAt_val, habove]
    norm_num [totalHeight]
  have hrightTree : (treeIndexAt right bottomLayer).val = right.val / 32 := by
    rw [treeIndexAt_val, habove]
    norm_num [totalHeight]
  have hleftLeaf : (leafIndexAt left bottomLayer).val = left.val % 32 := by
    rw [leafIndexAt_bottomLayer, hheight]
    norm_num
  have hrightLeaf : (leafIndexAt right bottomLayer).val = right.val % 32 := by
    rw [leafIndexAt_bottomLayer, hheight]
    norm_num
  rw [hleftTree, hrightTree] at htreeVal
  rw [hleftLeaf, hrightLeaf] at hleafVal
  omega
theorem nextTree_eq_of_position_eq {left right : Index} (lay : Layer)
    (hbelow : lay.val + 1 < numLayers)
    (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    treeIndexAt left ⟨lay.val + 1, hbelow⟩ = treeIndexAt right ⟨lay.val + 1, hbelow⟩ := by
  apply Fin.ext
  rw [layers_link left lay hbelow, layers_link right lay hbelow, congrArg Fin.val htree,
    congrArg Fin.val hleaf]
theorem layerMessage_eq_of_position_eq (secretKey : SecretKey) (left right : Index)
    (lay : Layer) (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    layerMessage (m := OracleComp HashSpec) secretKey left lay =
      layerMessage secretKey right lay := by
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [layerMessage_of_lt secretKey left lay hbelow, layerMessage_of_lt secretKey right lay hbelow,
      nextTree_eq_of_position_eq lay hbelow htree hleaf]
  · have hbottom : lay = bottomLayer := Fin.ext (by
      have := lay.isLt
      simp only [bottomLayer]
      omega)
    subst hbottom
    have hindex := index_eq_of_bottom_position_eq htree hleaf
    subst right
    rfl
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Ots_EncodingCached ====
section

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
theorem CachedRun.encode_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {lay : Layer}
    {tree : TreeIndex} {leafIdx : LeafIndex} {message : Digest} {counter : Counter}
    (hrun : CachedRun cache f (encodeAttempt parameter lay tree leafIdx message counter)) :
    cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes message ++ counterBytes counter)) ≠ none := by
  apply hrun
  rw [encodeAttempt]
  apply queriedInputs_mono_bind_left
  simp only [queriedInputs_tweakableHash, List.mem_singleton]
theorem CachedRun.otsLeaf_encode_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {lay : Layer}
    {tree : TreeIndex} {leafIdx : LeafIndex} {message : Digest} {counter : Counter}
    {values : ChainIndex → Digest}
    (hrun : CachedRun cache f (otsLeafAttempt parameter lay tree leafIdx message counter values)) :
    cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes message ++ counterBytes counter)) ≠ none :=
  CachedRun.encode_cached hrun.bind_left
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Scheme_ForgeryClassify ====
section

section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
theorem decode_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter)
      = some codeword) :
    OtsCode.decode (truncateHash (f (tweakableHashInput parameter
      (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter))))
        = some codeword := by
  simpa only [encodeAttempt, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_tweakableHash] using hencode
theorem valid_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter)
      = some codeword) : OtsCode.Valid codeword :=
  OtsCode.decode_valid
    (decode_of_eval_encode_eq_some f parameter lay tree leafIdx message counter codeword hencode)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
def FullyHonestOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (signature : Signature) : Prop :=
  (∀ lay, HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeafAttempt secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay) (signature.chainValue lay)))
    ∧ signature.fts = evalWithAnswerFn f (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index))
    ∧ CachedRun cache f
      (ftsRecover secretKey.parameter index (slotValue leaves) signature.fts)
theorem exact_bottom_message_eq_fts_key (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex bottomLayer = treeIndexAt forgedIndex bottomLayer)
    (hleaf : leafIndexAt signedIndex bottomLayer = leafIndexAt forgedIndex bottomLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex bottomLayer) = message) :
    message = honestFtsKey f secretKey.parameter forgedIndex (secretKey.ftsSecret forgedIndex) := by
  have hindex := index_eq_of_bottom_position_eq htree hleaf
  subst signedIndex
  rw [← hmessage, layerMessage_bottomLayer]
  rfl
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Scheme_Replay ====
section

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
theorem messageDigestPayload_injective (root : Digest) {leftMessage rightMessage : Message}
    {leftRandomness rightRandomness : Randomness}
    (h : messageDigestPayload root leftMessage leftRandomness
      = messageDigestPayload root rightMessage rightRandomness) :
    leftMessage = rightMessage ∧ leftRandomness = rightRandomness := by
  simp only [messageDigestPayload] at h
  obtain ⟨hrandomness, hrest⟩ := List.append_inj h (by simp [bytesLE_length]; exact (bytesLE_length 16 _).trans (bytesLE_length 16 _).symm)
  have hrandomness' := List.append_cancel_right hrandomness
  exact ⟨bytesLE_injective hrest, bytesLE_injective hrandomness'⟩
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeProbability ====
section

section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
abbrev SigningEntry := (request : Message) × SigningSpec.Range request
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
abbrev FewTimeView := Index × (IndexGroup → FtsLeaf)
theorem fewTimeView_card : Fintype.card FewTimeView =
    2 ^ (totalHeight + ftsTreeHeight * ftsOpenings) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ← pow_mul, ← pow_add]
noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeUniform ====
section

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
namespace Concrete
abbrev FullDigestView := Index × (IndexGroup → FtsLeaf)
def fullDigestView (digest : MessageDigest) : FullDigestView :=
  (digestIndex digest, digestLeaves digest)
def hashOutputFewTimeView (output : HashOutput) : FewTimeView :=
  fullDigestView (truncateMessageDigest output)
abbrev DigestUnusedBits := BitVec (messageDigestBits - (totalHeight + ftsTreeHeight * ftsOpenings))
def digestUnusedBits (digest : MessageDigest) : DigestUnusedBits :=
  digest.extractLsb' (totalHeight + ftsTreeHeight * ftsOpenings) (messageDigestBits - (totalHeight + ftsTreeHeight * ftsOpenings))
def digestCoordinates (digest : MessageDigest) : FewTimeView × DigestUnusedBits :=
  (fullDigestView digest, digestUnusedBits digest)
theorem digestCoordinates_injective : Function.Injective digestCoordinates := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  have hbits : messageDigestBits = 256 := rfl
  by_cases hindex : position < totalHeight
  · have hcomponent := congrArg (fun view : FewTimeView × DigestUnusedBits => BitVec.ofFin view.1.1) heq
    have hbit := congrArg (fun bits : BitVec totalHeight => bits.getLsbD position) hcomponent
    simpa [digestCoordinates, fullDigestView, digestIndex, BitVec.getLsbD_extractLsb', hindex] using hbit
  · by_cases hslots : position < totalHeight + ftsTreeHeight * ftsOpenings
    · let treeIndex := (position - totalHeight) / ftsTreeHeight
      have htreeIndex : treeIndex < ftsOpenings := by
        have hslots' : position < 244 := by simpa [totalHeight, ftsTreeHeight, ftsOpenings] using hslots
        have hindex' : 34 ≤ position := by
          simpa [totalHeight] using Nat.le_of_not_gt hindex
        simp only [treeIndex, ftsOpenings, ftsTreeHeight, totalHeight]
        omega
      let tree : IndexGroup := ⟨treeIndex, htreeIndex⟩
      let within := (position - totalHeight) % ftsTreeHeight
      have hwithin : within < ftsTreeHeight := by
        simp only [within, ftsTreeHeight]
        omega
      have hoffset : totalHeight + ftsTreeHeight * tree.val + within = position := by
        have hindex' : totalHeight ≤ position := Nat.le_of_not_gt hindex
        simp only [tree, treeIndex, within]
        calc
          totalHeight + ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight) +
              (position - totalHeight) % ftsTreeHeight =
              totalHeight + ((position - totalHeight) % ftsTreeHeight +
                ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight)) := by omega
          _ = totalHeight + (position - totalHeight) := by rw [Nat.mod_add_div]
          _ = position := Nat.add_sub_of_le hindex'
      have hcomponent := congrArg (fun view : FewTimeView × DigestUnusedBits => BitVec.ofFin (view.1.2 tree)) heq
      change left.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight =
        right.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight at hcomponent
      have hbit := congrArg (fun bits : BitVec ftsTreeHeight => bits.getLsbD within) hcomponent
      simp only [BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and] at hbit
      rwa [hoffset] at hbit
    · have hcomponent := congrArg (fun view : FewTimeView × DigestUnusedBits => view.2) heq
      change digestUnusedBits left = digestUnusedBits right at hcomponent
      have hlow : totalHeight + ftsTreeHeight * ftsOpenings ≤ position := Nat.le_of_not_gt hslots
      have hwithin : position - (totalHeight + ftsTreeHeight * ftsOpenings) <
          messageDigestBits - (totalHeight + ftsTreeHeight * ftsOpenings) := by
        rw [hbits] at hposition ⊢
        simp only [totalHeight, ftsTreeHeight, ftsOpenings] at hlow ⊢
        omega
      have hbit := congrArg (fun bits : DigestUnusedBits =>
        bits.getLsbD (position - (totalHeight + ftsTreeHeight * ftsOpenings))) hcomponent
      simp only [digestUnusedBits, BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and,
        Nat.add_sub_of_le hlow] at hbit
      exact hbit
theorem digestCoordinates_bijective : Function.Bijective digestCoordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨digestCoordinates_injective, ?_⟩
  simp only [Fintype.card_bitVec, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rfl
noncomputable def digestCoordinatesEquiv : MessageDigest ≃ FewTimeView × DigestUnusedBits :=
  Equiv.ofBijective digestCoordinates digestCoordinates_bijective
set_option maxRecDepth 100000 in
theorem evalDist_hashOutput_digestCoordinates_uniform :
    𝒮[(fun output : HashOutput => digestCoordinates (truncateMessageDigest output)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ (FewTimeView × DigestUnusedBits) : ProbComp (FewTimeView × DigestUnusedBits))] := by
  calc
    𝒮[(fun output : HashOutput => digestCoordinates (truncateMessageDigest output)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        digestCoordinates <$>
          𝒮[truncateMessageDigest <$> ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [evalSPMF_map, evalSPMF_map, Functor.map_map]
    _ = digestCoordinates <$>
          𝒮[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
      rw [show truncateMessageDigest =
          (fun output : HashOutput => output.extractLsb' 0 messageDigestBits) from rfl,
        evalDist_hashOutput_extract_uniform
          (show messageDigestBits ≤ hashOutputBits by decide)]
    _ = 𝒮[digestCoordinates <$>
          ($ᵗ MessageDigest : ProbComp MessageDigest)] := by
      rw [evalSPMF_map]
    _ = 𝒮[($ᵗ (FewTimeView × DigestUnusedBits) :
          ProbComp (FewTimeView × DigestUnusedBits))] :=
      evalSPMF_map_bijective_uniform_cross
        (α := MessageDigest) (β := FewTimeView × DigestUnusedBits)
        digestCoordinates digestCoordinates_bijective
abbrev HashOutputCoordinates :=
  (FewTimeView × DigestUnusedBits) × BitVec (hashOutputBits - messageDigestBits)
noncomputable def hashOutputCoordinatesEquiv : HashOutput ≃ HashOutputCoordinates :=
  (splitHashOutputEquiv messageDigestBits
      (show messageDigestBits ≤ hashOutputBits by decide)).trans
    (Equiv.prodCongr digestCoordinatesEquiv
      (Equiv.refl (BitVec (hashOutputBits - messageDigestBits))))
theorem hashOutputCoordinatesEquiv_apply (output : HashOutput) :
    hashOutputCoordinatesEquiv output =
      ((hashOutputFewTimeView output,
          digestUnusedBits (truncateMessageDigest output)),
        output.extractLsb' messageDigestBits (hashOutputBits - messageDigestBits)) := rfl
set_option maxRecDepth 100000 in
theorem evalDist_uniformHashOutput_bind_coordinates {Result : Type}
    (continuation : HashOutput → ProbComp Result) :
    𝒮[($ᵗ HashOutput : ProbComp HashOutput) >>= continuation] =
      𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates => continuation (hashOutputCoordinatesEquiv.symm coordinates)] := by
  have hmap :
      𝒮[hashOutputCoordinatesEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
        𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] :=
    evalSPMF_map_bijective_uniform_cross
      (α := HashOutput) (β := HashOutputCoordinates)
      hashOutputCoordinatesEquiv hashOutputCoordinatesEquiv.bijective
  have hcomputation :
      (hashOutputCoordinatesEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)) >>=
          (fun coordinates =>
            continuation (hashOutputCoordinatesEquiv.symm coordinates)) =
        ($ᵗ HashOutput : ProbComp HashOutput) >>= continuation := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [← hcomputation, evalSPMF_bind, hmap, ← evalSPMF_bind]
set_option maxRecDepth 100000 in
theorem evalDist_randomOracle_fresh_bind_coordinates {Result : Type}
    (input : HashInput) (cache : QueryCache HashSpec) (hcache : cache input = none)
    (continuation : HashOutput × QueryCache HashSpec → ProbComp Result) :
    𝒮[(randomOracle input).run cache >>= continuation] =
      𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates =>
          let output := hashOutputCoordinatesEquiv.symm coordinates
          continuation (output, cache.cacheQuery input output)] := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hcache]
  change 𝒮[((fun output : HashOutput => (output, cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation] = _
  have hcomputation :
      ((fun output : HashOutput => (output, cache.cacheQuery input output)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation =
        ($ᵗ HashOutput : ProbComp HashOutput) >>= fun output =>
          continuation (output, cache.cacheQuery input output) := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [hcomputation]
  exact evalDist_uniformHashOutput_bind_coordinates fun output =>
    continuation (output, cache.cacheQuery input output)
def signAttemptResultOfOutput (output : HashOutput) :
    Option (Index × (IndexGroup → FtsLeaf)) :=
  let digest := truncateMessageDigest output
  if Admissible digest then some (digestIndex digest, digestLeaves digest) else none
theorem hashOutputCoordinatesEquiv_symm_digestCoordinates
    (coordinates : HashOutputCoordinates) :
    digestCoordinates (truncateMessageDigest (hashOutputCoordinatesEquiv.symm coordinates)) =
      coordinates.1 := by
  have heq := hashOutputCoordinatesEquiv.apply_symm_apply coordinates
  rw [hashOutputCoordinatesEquiv_apply] at heq
  exact congrArg Prod.fst heq
theorem hashOutputCoordinatesEquiv_symm_view (coordinates : HashOutputCoordinates) :
    hashOutputFewTimeView (hashOutputCoordinatesEquiv.symm coordinates) = coordinates.1.1 := by
  change (digestCoordinates
    (truncateMessageDigest (hashOutputCoordinatesEquiv.symm coordinates))).1 = coordinates.1.1
  exact congrArg Prod.fst (hashOutputCoordinatesEquiv_symm_digestCoordinates coordinates)
theorem signAttemptResultOfOutput_ne_none_iff (output : HashOutput) :
    signAttemptResultOfOutput output ≠ none ↔
      Admissible (truncateMessageDigest output) := by
  simp only [signAttemptResultOfOutput]
  split <;> simp_all
theorem admissible_iff_view (output : HashOutput) :
    Admissible (truncateMessageDigest output) ↔ AdmissibleLeaves (hashOutputFewTimeView output).2 := Iff.rfl
theorem signAttemptResultOfOutput_coordinates_ne_none_iff
    (coordinates : HashOutputCoordinates) :
    signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates) ≠ none ↔
      AdmissibleLeaves coordinates.1.1.2 := by
  rw [signAttemptResultOfOutput_ne_none_iff, admissible_iff_view, hashOutputCoordinatesEquiv_symm_view]
theorem signAttemptResultOfOutput_coordinates_view
    (coordinates : HashOutputCoordinates) (index : Index)
    (leaves : IndexGroup → FtsLeaf)
    (hresult : signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates) =
      some (index, leaves)) :
    (index, leaves) = coordinates.1.1 := by
  let output := hashOutputCoordinatesEquiv.symm coordinates
  simp only [signAttemptResultOfOutput] at hresult
  split at hresult
  · have hpair := Option.some.inj hresult
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact hashOutputCoordinatesEquiv_symm_view coordinates
  · simp at hresult
theorem signAttemptResultOfOutput_view (output : HashOutput) (index : Index)
    (leaves : IndexGroup → FtsLeaf)
    (hresult : signAttemptResultOfOutput output = some (index, leaves)) :
    (index, leaves) = hashOutputFewTimeView output := by
  let coordinates := hashOutputCoordinatesEquiv output
  calc
    (index, leaves) = coordinates.1.1 := by
      apply signAttemptResultOfOutput_coordinates_view coordinates index leaves
      simpa [coordinates] using hresult
    _ = hashOutputFewTimeView output := by
      dsimp only [coordinates]
      rw [hashOutputCoordinatesEquiv_apply]
theorem simulateQ_signAttempt_run_eq (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAttempt secretKey message randomness)).run cache =
        (randomOracle (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness))).run cache >>=
            fun result => pure (signAttemptResultOfOutput result.1, result.2) := by
  have hquery :
      simulateQ (randomOracle : QueryImpl HashSpec _)
          (oracleHash (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message randomness)) :
              OracleComp HashSpec HashOutput) =
        randomOracle (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) := by
    change simulateQ (randomOracle : QueryImpl HashSpec _)
      (liftM (HashSpec.query (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)))) = _
    exact simulateQ_spec_query
      (impl := (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp)))
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness))
  rw [signAttempt, simulateQ_bind, StateT.run_bind, messageDigest,
    simulateQ_bind, StateT.run_bind, hquery]
  simp only [signAttemptResultOfOutput, simulateQ_pure, StateT.run_pure]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro result
  split <;> rfl
set_option maxRecDepth 100000 in
theorem evalDist_signAttempt_fresh_bind_coordinates {Result : Type}
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec)
    (hcache : cache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none)
    (continuation :
      Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec →
        ProbComp Result) :
    𝒮[(simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run cache >>= continuation] =
      𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates =>
          let output := hashOutputCoordinatesEquiv.symm coordinates
          continuation (signAttemptResultOfOutput output,
            cache.cacheQuery
              (tweakableHashInput secretKey.parameter .message
                (messageDigestPayload secretKey.root message randomness)) output)] := by
  rw [simulateQ_signAttempt_run_eq]
  simp only [bind_assoc, pure_bind]
  exact evalDist_randomOracle_fresh_bind_coordinates
    (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) cache hcache
    (fun result => continuation (signAttemptResultOfOutput result.1, result.2))
end Concrete
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_JointProbeMessageAnswers ====
section

namespace SphincsSecurity.Concrete.FtsProbeSimulation
open _root_.OracleComp OracleSpec ENNReal
noncomputable def messageAnswers (parameter : PublicParameter) (cache : QueryCache HashSpec) : HashInput → Option HashOutput :=
  fun payload => cache (tweakableHashInput parameter .message payload)
end SphincsSecurity.Concrete.FtsProbeSimulation
end
-- ==== merged from SphincsSecurity_Proof_Fts_JointProbeMessageReserve ====
section

namespace SphincsSecurity.Concrete.FtsProbeSimulation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def MessageHashInput (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ payload, tweakableHashInput parameter .message payload = input
end SphincsSecurity.Concrete.FtsProbeSimulation
end
-- ==== merged from SphincsSecurity_Proof_Fts_CacheMessageWeight ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def cacheMessageEntryWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  match cache input with
  | none => 0
  | some output => if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) then
      weight input (hashOutputFewTimeView output) else 0
noncomputable def cacheMessageWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) : ENNReal :=
  ∑' input, cacheMessageEntryWeight parameter weight cache input
theorem cacheMessageWeight_messageAnswers_congr (parameter : PublicParameter)
    (before after : QueryCache HashSpec) (hanswers : messageAnswers parameter before = messageAnswers parameter after)
    (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight parameter weight before = cacheMessageWeight parameter weight after := by
  apply tsum_congr
  intro input
  by_cases hm : MessageHashInput parameter input
  · obtain ⟨payload, rfl⟩ := hm
    have heq := congrFun hanswers payload
    change before (tweakableHashInput parameter .message payload) = after (tweakableHashInput parameter .message payload) at heq
    simp only [cacheMessageEntryWeight, heq]
  · unfold cacheMessageEntryWeight
    cases before input <;> cases after input <;> simp [hm]
theorem cacheMessageWeight_mono (parameter : PublicParameter)
    (first second : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec)
    (h : ∀ input target, first input target ≤ second input target) :
    cacheMessageWeight parameter first cache ≤ cacheMessageWeight parameter second cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  unfold cacheMessageEntryWeight
  cases cache input with
  | none => exact le_rfl
  | some output => simp only; split_ifs; exact h input _; exact le_rfl
theorem cacheMessageWeight_add (parameter : PublicParameter)
    (first second : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) :
    cacheMessageWeight parameter (fun input target => first input target + second input target) cache =
      cacheMessageWeight parameter first cache + cacheMessageWeight parameter second cache := by
  rw [cacheMessageWeight, cacheMessageWeight, cacheMessageWeight, ← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  unfold cacheMessageEntryWeight
  cases cache input <;> simp only
  · exact (add_zero _).symm
  · split_ifs <;> simp only [add_zero]
theorem cacheMessageWeight_mul_right (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) (factor : ENNReal) :
    cacheMessageWeight parameter (fun input view => weight input view * factor) cache =
      cacheMessageWeight parameter weight cache * factor := by
  unfold cacheMessageWeight
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro input
  unfold cacheMessageEntryWeight
  cases cache input with
  | none => exact (zero_mul _).symm
  | some output => simp only; split_ifs <;> simp only [zero_mul]
theorem cacheMessageWeight_sum {α : Type} [DecidableEq α] (parameter : PublicParameter) (indices : Finset α)
    (weight : α → HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) :
    cacheMessageWeight parameter (fun input source => ∑ index ∈ indices, weight index input source) cache =
      ∑ index ∈ indices, cacheMessageWeight parameter (weight index) cache := by
  induction indices using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, cacheMessageWeight, cacheMessageEntryWeight]
      apply ENNReal.tsum_eq_zero.mpr
      intro input
      cases cache input <;> simp
  | @insert index indices hnot ih =>
      simp only [Finset.sum_insert hnot, cacheMessageWeight_add, ih]
theorem cacheMessageWeight_of_no_message (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec)
    (hnone : ∀ input, MessageHashInput parameter input → cache input = none) :
    cacheMessageWeight parameter weight cache = 0 := by
  unfold cacheMessageWeight
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases hcache : cache input with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood
      · rw [hnone input hgood.1] at hcache
        contradiction
      · rfl
theorem cacheMessageWeight_cacheQuery (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hfresh : cache input = none) :
    cacheMessageWeight parameter weight (cache.cacheQuery input output) =
      cacheMessageWeight parameter weight cache +
        (if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) then
          weight input (hashOutputFewTimeView output) else 0) := by
  unfold cacheMessageWeight
  rw [ENNReal.tsum_eq_add_tsum_ite (f := cacheMessageEntryWeight parameter weight (cache.cacheQuery input output)) input,
    ENNReal.tsum_eq_add_tsum_ite (f := cacheMessageEntryWeight parameter weight cache) input]
  simp only [cacheMessageEntryWeight, QueryCache.cacheQuery_self, hfresh, zero_add]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro other
  by_cases heq : other = input
  · simp only [heq, if_true]
  · simp only [heq, if_false, QueryCache.cacheQuery_of_ne cache output heq]
theorem expected_cacheMessageWeight {α : Type} (parameter : PublicParameter)
    (weight : α → HashInput → FewTimeView → ENNReal) (computation : ProbComp α)
    (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | computation] * cacheMessageWeight parameter (weight result) cache) =
      cacheMessageWeight parameter (fun input target => ∑' result, Pr[= result | computation] * weight result input target) cache := by
  simp only [cacheMessageWeight, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro input
  unfold cacheMessageEntryWeight
  cases cache input with
  | none => simp only [mul_zero, tsum_zero]
  | some output => simp only; split_ifs <;> simp only [mul_zero, tsum_zero]
theorem cacheMessageWeight_fresh_restriction (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (cache : QueryCache HashSpec) :
    cacheMessageWeight parameter (fun input target => if cache input = none then weight input target else 0) cache = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases hcache : cache input <;> simp [hcache]
theorem cacheMessageWeight_of_le (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (before after : QueryCache HashSpec)
    (hcache : before ≤ after) :
    cacheMessageWeight parameter weight after = cacheMessageWeight parameter weight before +
      cacheMessageWeight parameter (fun input target => if before input = none then weight input target else 0) after := by
  rw [cacheMessageWeight, cacheMessageWeight, cacheMessageWeight, ← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  cases hbefore : before input with
  | none => simp only [cacheMessageEntryWeight, hbefore, if_true, zero_add]
  | some output =>
      simp only [cacheMessageEntryWeight, hbefore, hcache hbefore, reduceCtorEq, if_false]
      split_ifs <;> simp only [add_zero]
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_CacheIndexMultiplicity ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def cachedIndexMultiplicity (parameter : PublicParameter) (cache : QueryCache HashSpec) (index : Index) : ENNReal :=
  cacheMessageWeight parameter (fun _ source => if source.1 = index then 1 else 0) cache
theorem cachedIndexMultiplicity_cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hfresh : cache input = none) (index : Index) :
    cachedIndexMultiplicity parameter (cache.cacheQuery input output) index = cachedIndexMultiplicity parameter cache index +
      (if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index then 1 else 0) := by
  rw [cachedIndexMultiplicity, cacheMessageWeight_cacheQuery parameter _ cache input output hfresh]
  simp only [← ite_and, and_assoc]
  rfl
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeConditionalCoverage ====
section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def CoveredFewTimeView {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) : Prop :=
  ∀ tree, ∃ slot view, views slot = some view ∧ view.1 = target.1 ∧ target.2 tree ∈ Set.range view.2
noncomputable def signingSlotsAtIndex {n : Nat} (views : Fin n → Option FewTimeView) (index : Index) : Finset (Fin n) :=
  Finset.univ.filter (fun slot => ∃ view, views slot = some view ∧ view.1 = index)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_ObservedAdaptiveCoverBound ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def observedSigningView? (answers : HashInput → Option HashOutput) (root : Digest) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  let answer ← answers (messageDigestPayload root entry.1 signature.randomness)
  pure (hashOutputFewTimeView answer)
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def eligibleSigningView? (answers : HashInput → Option HashOutput) (root : Digest)
    (targetPayload : HashInput) (entry : SigningEntry) : Option FewTimeView := do
  let signature ← entry.2
  if messageDigestPayload root entry.1 signature.randomness = targetPayload then none
  else observedSigningView? answers root entry
noncomputable def eligibleSigningViews (answers : HashInput → Option HashOutput) (root : Digest)
    (targetPayload : HashInput) (log : QueryLog SigningSpec) : Fin log.length → Option FewTimeView :=
  fun slot => eligibleSigningView? answers root targetPayload (log.get slot)
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def fixedSigningViews (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) (input : HashInput) : Fin log.length → Option FewTimeView :=
  eligibleSigningViews (messageAnswers parameter cache) root (payloadOf input) log
def SigningDigestsCached (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (root : Digest) (log : QueryLog SigningSpec) : Prop :=
  ∀ entry ∈ log, ∀ signature, entry.2 = some signature →
    messageAnswers parameter cache (messageDigestPayload root entry.1 signature.randomness) ≠ none
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_CachedTargetIncrement ====
section

section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def observedOptionalSigningViews (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) : Fin log.length → Option FewTimeView :=
  fun slot => observedSigningView? answers root (log.get slot)
theorem observedSigningView?_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (entry : SigningEntry)
    (hsigned : ∀ signature, entry.2 = some signature →
      messageAnswers parameter before (messageDigestPayload root entry.1 signature.randomness) ≠ none) :
    observedSigningView? (messageAnswers parameter after) root entry = observedSigningView? (messageAnswers parameter before) root entry := by
  cases hresponse : entry.2 with
  | none => simp [observedSigningView?, hresponse]
  | some signature =>
      obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned signature hresponse)
      have hafter : messageAnswers parameter after (messageDigestPayload root entry.1 signature.randomness) = some output := hcache houtput
      simp [observedSigningView?, hresponse, houtput, hafter]
theorem observedOptionalSigningViews_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log) :
    observedOptionalSigningViews (messageAnswers parameter after) root log =
      observedOptionalSigningViews (messageAnswers parameter before) root log := by
  funext slot
  exact observedSigningView?_cache_stable parameter root before after hcache (log.get slot) (hsigned _ (List.get_mem _ _))
theorem signingSlotsAtIndex_log_card {α : Type} (log : List α) (view : α → Option FewTimeView) (index : Index) :
    (signingSlotsAtIndex (fun slot => view (log.get slot)) index).card =
      (log.map (fun entry => if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0)).sum := by
  rw [signingSlotsAtIndex, Finset.card_eq_sum_ones, Finset.sum_filter, ← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map log
    (fun entry => if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0))
theorem signingSlotsAtIndex_log_append_card {α : Type} (log : List α) (entry : α)
    (view : α → Option FewTimeView) (index : Index) :
    (signingSlotsAtIndex (fun slot => view ((log ++ [entry]).get slot)) index).card =
      (signingSlotsAtIndex (fun slot => view (log.get slot)) index).card +
        if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0 := by
  simp only [signingSlotsAtIndex_log_card, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem eligibleSigningViews_fresh_eq_observed (parameter : PublicParameter) (root : Digest)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput)
    (hfresh : before (tweakableHashInput parameter .message payload) = none)
    (hsigned : SigningDigestsCached parameter before root log) :
    eligibleSigningViews (messageAnswers parameter before) root payload log =
      observedOptionalSigningViews (messageAnswers parameter before) root log := by
  funext slot
  simp only [eligibleSigningViews, observedOptionalSigningViews]
  cases hresponse : (log.get slot).2 with
  | none =>
      change Option.bind (log.get slot).2 _ = Option.bind (log.get slot).2 _
      rw [hresponse]
      rfl
  | some signature =>
      have hne : messageDigestPayload root (log.get slot).1 signature.randomness ≠ payload := by
        intro heq
        have hcached := hsigned (log.get slot) (List.get_mem _ _) signature hresponse
        apply hcached
        change before (tweakableHashInput parameter .message (messageDigestPayload root (log.get slot).1 signature.randomness)) = none
        rwa [heq]
      unfold eligibleSigningView?
      rw [hresponse]
      change (if messageDigestPayload root (log.get slot).1 signature.randomness = payload then none else _) = _
      rw [if_neg hne]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_TargetShapeOperators ====
section

section
namespace SphincsSecurity.Concrete
attribute [local instance] Classical.propDecidable
structure TargetShapeValid (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : Prop where
  nonempty : ∀ group ∈ groups, group.Nonempty
  disjoint : ∀ first ∈ groups, ∀ second ∈ groups, first ≠ second → Disjoint first second
  remaining : ∀ group ∈ groups, Disjoint group remaining
theorem TargetShapeValid.subsets {groups kept : Finset (Finset IndexGroup)} {remaining trees : Finset IndexGroup}
    (hvalid : TargetShapeValid groups remaining) (hgroups : kept ⊆ groups) (htrees : trees ⊆ remaining) :
    TargetShapeValid kept trees where
  nonempty group hgroup := hvalid.nonempty group (hgroups hgroup)
  disjoint first hfirst second hsecond hne := hvalid.disjoint first (hgroups hfirst) second (hgroups hsecond) hne
  remaining group hgroup := (hvalid.remaining group (hgroups hgroup)).mono_right htrees
theorem TargetShapeValid.new_group {groups : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hvalid : TargetShapeValid groups remaining) (hselected : selected.Nonempty) (hsub : selected ⊆ remaining) : selected ∉ groups := by
  intro hmem
  obtain ⟨tree, htree⟩ := hselected
  exact Finset.disjoint_left.mp (hvalid.remaining selected hmem) htree (hsub htree)
theorem TargetShapeValid.reuse {groups : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hvalid : TargetShapeValid groups remaining) (hselected : selected.Nonempty) (hsub : selected ⊆ remaining) :
    TargetShapeValid (insert selected groups) (remaining \ selected) := by
  constructor
  · intro group hgroup
    rcases Finset.mem_insert.mp hgroup with rfl | hgroup
    · exact hselected
    · exact hvalid.nonempty group hgroup
  · intro first hfirst second hsecond hne
    rcases Finset.mem_insert.mp hfirst with rfl | hfirstOld
    · rcases Finset.mem_insert.mp hsecond with rfl | hsecond
      · exact (hne rfl).elim
      · exact ((hvalid.remaining second hsecond).mono_right hsub).symm
    · rcases Finset.mem_insert.mp hsecond with rfl | hsecond
      · exact (hvalid.remaining first hfirstOld).mono_right hsub
      · exact hvalid.disjoint first hfirstOld second hsecond hne
  · intro group hgroup
    rcases Finset.mem_insert.mp hgroup with rfl | hgroup
    · exact Finset.disjoint_left.mpr (fun tree htree hrest => (Finset.mem_sdiff.mp hrest).2 htree)
    · exact (hvalid.remaining group hgroup).mono_right Finset.sdiff_subset
end SphincsSecurity.Concrete
end
section
namespace SphincsSecurity.Concrete
open ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
abbrev TargetShapeVector := Finset (Finset IndexGroup) → Finset IndexGroup → ENNReal
noncomputable def targetCacheAll (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  ∑ kept ∈ groups.powerset, f kept remaining
noncomputable def targetCacheLower (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  ∑ kept ∈ groups.powerset.erase groups, f kept remaining
noncomputable def targetTreeLower (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  ∑ selected ∈ remaining.powerset.erase ∅, f groups (remaining \ selected)
noncomputable def targetReuseStep (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  ∑ selected ∈ remaining.powerset.erase ∅, f (insert selected groups) (remaining \ selected)
theorem targetCacheAll_eq (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetCacheAll f groups remaining = f groups remaining + targetCacheLower f groups remaining := by
  exact (Finset.add_sum_erase _ _ (Finset.mem_powerset.mpr (Finset.Subset.refl groups))).symm
theorem targetCacheLower_add (f g : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetCacheLower (fun G R => f G R + g G R) groups remaining = targetCacheLower f groups remaining + targetCacheLower g groups remaining := by
  simp only [targetCacheLower, Finset.sum_add_distrib]
theorem targetTreeLower_add (f g : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetTreeLower (fun G R => f G R + g G R) groups remaining = targetTreeLower f groups remaining + targetTreeLower g groups remaining := by
  simp only [targetTreeLower, Finset.sum_add_distrib]
theorem targetReuseStep_add (f g : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetReuseStep (fun G R => f G R + g G R) groups remaining = targetReuseStep f groups remaining + targetReuseStep g groups remaining := by
  simp only [targetReuseStep, Finset.sum_add_distrib]
theorem targetCacheLower_mul (c : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetCacheLower (fun G R => c * f G R) groups remaining = c * targetCacheLower f groups remaining := by
  simp only [targetCacheLower, Finset.mul_sum]
theorem targetTreeLower_mul (c : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetTreeLower (fun G R => c * f G R) groups remaining = c * targetTreeLower f groups remaining := by
  simp only [targetTreeLower, Finset.mul_sum]
theorem targetReuseStep_mul (c : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetReuseStep (fun G R => c * f G R) groups remaining = c * targetReuseStep f groups remaining := by
  simp only [targetReuseStep, Finset.mul_sum]
theorem targetCacheLower_tree_commute (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetCacheLower (targetTreeLower f) groups remaining = targetTreeLower (targetCacheLower f) groups remaining := by
  unfold targetCacheLower targetTreeLower
  exact Finset.sum_comm
private theorem sum_erase_as_indicator {α : Type} [DecidableEq α] (s : Finset α) (a : α) (f : α → ENNReal) :
    (∑ x ∈ s.erase a, f x) = ∑ x ∈ s, if x = a then 0 else f x := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x = a <;> simp only [h, ne_eq, not_true_eq_false, not_false_eq_true, if_true, if_false]
theorem targetCacheLower_insert (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining selected : Finset IndexGroup)
    (hnot : selected ∉ groups) :
    targetCacheLower f (insert selected groups) remaining = targetCacheAll f groups remaining +
      targetCacheLower (fun G R => f (insert selected G) R) groups remaining := by
  unfold targetCacheLower targetCacheAll
  rw [sum_erase_as_indicator, Finset.sum_powerset_insert hnot]
  rw [sum_erase_as_indicator]
  congr 1
  · apply Finset.sum_congr rfl
    intro kept hkept
    have hne : kept ≠ insert selected groups := by
      intro heq
      exact hnot ((Finset.mem_powerset.mp hkept) (heq ▸ Finset.mem_insert_self selected groups))
    exact if_neg hne
  · apply Finset.sum_congr rfl
    intro kept hkept
    have hkeptNot : selected ∉ kept := fun hmem => hnot ((Finset.mem_powerset.mp hkept) hmem)
    have heq : insert selected kept = insert selected groups ↔ kept = groups := by
      constructor
      · intro heq
        have h := congrArg (fun s : Finset (Finset IndexGroup) => s.erase selected) heq
        simpa only [Finset.erase_insert hkeptNot, Finset.erase_insert hnot] using h
      · rintro rfl; rfl
    simp only [heq]
theorem targetReuse_cache_commute (f : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup)
    (hvalid : TargetShapeValid groups remaining) :
    targetReuseStep (targetCacheLower f) groups remaining =
      targetCacheLower (targetReuseStep f) groups remaining + targetTreeLower f groups remaining +
        targetCacheLower (targetTreeLower f) groups remaining := by
  unfold targetReuseStep
  have hinsert (selected : Finset IndexGroup) (hselected : selected ∈ remaining.powerset.erase ∅) :
      targetCacheLower f (insert selected groups) (remaining \ selected) = targetCacheAll f groups (remaining \ selected) +
        targetCacheLower (fun G R => f (insert selected G) R) groups (remaining \ selected) :=
    targetCacheLower_insert f groups _ selected (hvalid.new_group
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
      (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2))
  rw [Finset.sum_congr rfl hinsert]
  simp only [targetCacheAll_eq, Finset.sum_add_distrib, targetCacheLower, targetTreeLower]
  rw [Finset.sum_comm (s := remaining.powerset.erase ∅) (t := groups.powerset.erase groups)]
  rw [Finset.sum_comm (s := remaining.powerset.erase ∅) (t := groups.powerset.erase groups)]
  ring
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Fts_TargetShapeReindex ====
section

namespace SphincsSecurity.Concrete
open ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def targetGroupAt (groups : Finset (Finset IndexGroup)) (slot : Fin groups.card) : Finset IndexGroup :=
  (groups.equivFin.symm slot).val
theorem targetGroupAt_mem (groups : Finset (Finset IndexGroup)) (slot : Fin groups.card) : targetGroupAt groups slot ∈ groups :=
  (groups.equivFin.symm slot).property
theorem targetGroupAt_injective (groups : Finset (Finset IndexGroup)) : Function.Injective (targetGroupAt groups) :=
  fun _ _ h => groups.equivFin.symm.injective (Subtype.ext h)
theorem targetGroupAt_image (groups : Finset (Finset IndexGroup)) : Finset.univ.image (targetGroupAt groups) = groups := by
  ext group
  constructor
  · intro h
    obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp h
    exact targetGroupAt_mem groups slot
  · intro h
    exact Finset.mem_image.mpr ⟨groups.equivFin ⟨group, h⟩, Finset.mem_univ _, by simp [targetGroupAt]⟩
theorem prod_targetGroupAt (groups : Finset (Finset IndexGroup)) (f : Finset IndexGroup → ENNReal) :
    (∏ slot : Fin groups.card, f (targetGroupAt groups slot)) = ∏ group ∈ groups, f group := by
  calc
    _ = ∏ group ∈ Finset.univ.image (targetGroupAt groups), f group :=
      (Finset.prod_image (targetGroupAt_injective groups).injOn).symm
    _ = _ := by rw [targetGroupAt_image]
theorem sum_targetGroupAt_proper (groups : Finset (Finset IndexGroup)) (f : Finset (Finset IndexGroup) → ENNReal) :
    (∑ kept ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase Finset.univ,
      f (kept.image (targetGroupAt groups))) = ∑ kept ∈ groups.powerset.erase groups, f kept := by
  have hi := Finset.image_injective (targetGroupAt_injective groups)
  rw [← Finset.sum_image hi.injOn, Finset.image_erase hi, ← Finset.powerset_image, targetGroupAt_image]
theorem sum_targetGroupAt_nonempty (groups : Finset (Finset IndexGroup)) (f : Finset (Finset IndexGroup) → ENNReal) :
    (∑ selected ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
      f (selected.image (targetGroupAt groups))) = ∑ removed ∈ groups.powerset.erase ∅, f removed := by
  have hi := Finset.image_injective (targetGroupAt_injective groups)
  rw [← Finset.sum_image hi.injOn, Finset.image_erase hi, ← Finset.powerset_image, targetGroupAt_image,
    Finset.image_empty]
theorem biUnion_targetGroupAt (groups : Finset (Finset IndexGroup)) (selected : Finset (Fin groups.card)) :
    selected.biUnion (targetGroupAt groups) = (selected.image (targetGroupAt groups)).biUnion id := by
  rw [Finset.image_biUnion]
  rfl
theorem prod_targetGroupAt_compl (groups : Finset (Finset IndexGroup)) (selected : Finset (Fin groups.card))
    (f : Finset IndexGroup → ENNReal) :
    (∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ selected, f (targetGroupAt groups slot)) =
      ∏ group ∈ groups \ selected.image (targetGroupAt groups), f group := by
  rw [← Finset.prod_image (targetGroupAt_injective groups).injOn,
    Finset.image_sdiff _ _ (targetGroupAt_injective groups), targetGroupAt_image]
theorem sum_nonempty_sdiff_eq_proper {α : Type} [DecidableEq α] (s : Finset α) (f : Finset α → ENNReal) :
    (∑ removed ∈ s.powerset.erase ∅, f (s \ removed)) = ∑ kept ∈ s.powerset.erase s, f kept := by
  apply Finset.sum_bij' (fun removed _ => s \ removed) (fun kept _ => s \ kept)
  · intro removed hremoved
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hremoved
    exact Finset.mem_erase.mpr ⟨(Finset.sdiff_ssubset (Finset.mem_powerset.mp hsub)
      (Finset.nonempty_iff_ne_empty.mpr hne)).ne, Finset.mem_powerset.mpr Finset.sdiff_subset⟩
  · intro kept hkept
    obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hkept
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr Finset.sdiff_subset⟩
    intro hempty
    exact hne (Finset.Subset.antisymm (Finset.mem_powerset.mp hsub) (Finset.sdiff_eq_empty_iff_subset.mp hempty))
  · intro removed hremoved
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2)
  · intro kept hkept
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_erase.mp hkept).2)
  · intro _ _; rfl
theorem sum_targetGroupAt_removed_products (groups : Finset (Finset IndexGroup)) (f : Finset IndexGroup → ENNReal) :
    (∑ removed ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
      ∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ removed, f (targetGroupAt groups slot)) =
      ∑ kept ∈ groups.powerset.erase groups, ∏ group ∈ kept, f group := by
  rw [sum_nonempty_sdiff_eq_proper _ (fun kept => ∏ slot ∈ kept, f (targetGroupAt groups slot))]
  simp only [← Finset.prod_image (targetGroupAt_injective groups).injOn]
  exact sum_targetGroupAt_proper groups (fun kept => ∏ group ∈ kept, f group)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_TargetShapeEnvelope ====
section

namespace SphincsSecurity.Concrete
open ENNReal
attribute [local instance] Classical.propDecidable
abbrev TargetRate := Finset IndexGroup → ENNReal
def constRate (value : ENNReal) : TargetRate := fun _ => value
def groupCoordinates (groups : Finset (Finset IndexGroup)) : Finset IndexGroup := groups.biUnion id
noncomputable def targetArrivalStep (arrival : TargetRate) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) : ENNReal :=
  ∑ removed ∈ groups.powerset.erase ∅, arrival (groupCoordinates removed) * f (groups \ removed) remaining
noncomputable def targetFreshStep (rate : TargetRate) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) : ENNReal :=
  ∑ removed ∈ groups.powerset, ∑ selected ∈ remaining.powerset,
    if removed = ∅ ∧ selected = ∅ then 0 else
      rate (groupCoordinates removed ∪ selected) * f (groups \ removed) (remaining \ selected)
noncomputable def targetShapeQuery (arrival : TargetRate) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) : ENNReal :=
  f groups remaining + targetArrivalStep arrival f groups remaining
noncomputable def targetShapeSigning (rate : TargetRate) (reuse : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  f groups remaining + targetFreshStep rate f groups remaining + reuse * targetReuseStep f groups remaining
theorem targetArrivalStep_add (arrival : TargetRate) (f g : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetArrivalStep arrival (fun G R => f G R + g G R) groups remaining =
      targetArrivalStep arrival f groups remaining + targetArrivalStep arrival g groups remaining := by
  simp only [targetArrivalStep, mul_add, Finset.sum_add_distrib]
theorem targetArrivalStep_mul (arrival : TargetRate) (c : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetArrivalStep arrival (fun G R => c * f G R) groups remaining = c * targetArrivalStep arrival f groups remaining := by
  simp only [targetArrivalStep, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring
theorem targetFreshStep_add (rate : TargetRate) (f g : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetFreshStep rate (fun G R => f G R + g G R) groups remaining =
      targetFreshStep rate f groups remaining + targetFreshStep rate g groups remaining := by
  simp only [targetFreshStep, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  split_ifs
  · simp
  · rw [mul_add]
theorem targetFreshStep_mul (rate : TargetRate) (c : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetFreshStep rate (fun G R => c * f G R) groups remaining = c * targetFreshStep rate f groups remaining := by
  simp only [targetFreshStep, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  split_ifs
  · simp
  · ring
theorem targetArrivalStep_const (value : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetArrivalStep (constRate value) f groups remaining = value * targetCacheLower f groups remaining := by
  unfold targetArrivalStep targetCacheLower constRate
  rw [← Finset.mul_sum]
  congr 1
  exact sum_nonempty_sdiff_eq_proper groups (fun kept => f kept remaining)
private theorem sum_powerset_split_empty {α : Type} [DecidableEq α] (s : Finset α) (g : Finset α → ENNReal) :
    ∑ x ∈ s.powerset, g x = g ∅ + ∑ x ∈ s.powerset.erase ∅, g x :=
  (Finset.add_sum_erase _ _ (Finset.empty_mem_powerset s)).symm
theorem targetFreshStep_const (value : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetFreshStep (constRate value) f groups remaining =
      value * (targetCacheLower f groups remaining + targetTreeLower f groups remaining +
        targetCacheLower (targetTreeLower f) groups remaining) := by
  unfold targetFreshStep constRate
  have hfirst : (∑ selected ∈ remaining.powerset,
      if (∅ : Finset (Finset IndexGroup)) = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        value * f (groups \ ∅) (remaining \ selected)) = value * targetTreeLower f groups remaining := by
    rw [sum_powerset_split_empty, if_pos ⟨rfl, rfl⟩, zero_add]
    unfold targetTreeLower
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected hselected
    rw [if_neg (fun h => (Finset.mem_erase.mp hselected).1 h.2), Finset.sdiff_empty]
  have hrest : ∀ removed ∈ groups.powerset.erase ∅, (∑ selected ∈ remaining.powerset,
      if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        value * f (groups \ removed) (remaining \ selected)) =
      value * f (groups \ removed) remaining + value * targetTreeLower f (groups \ removed) remaining := by
    intro removed hremoved
    have hne : removed ≠ ∅ := (Finset.mem_erase.mp hremoved).1
    rw [sum_powerset_split_empty, if_neg (fun h => hne h.1), Finset.sdiff_empty]
    congr 1
    unfold targetTreeLower
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected _
    rw [if_neg (fun h => hne h.1)]
  rw [sum_powerset_split_empty, hfirst, Finset.sum_congr rfl hrest, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  unfold targetCacheLower
  rw [sum_nonempty_sdiff_eq_proper groups (fun kept => f kept remaining),
    sum_nonempty_sdiff_eq_proper groups (fun kept => targetTreeLower f kept remaining)]
  ring
theorem targetShapeQuery_const (value : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetShapeQuery (constRate value) f groups remaining = f groups remaining + value * targetCacheLower f groups remaining := by
  rw [targetShapeQuery, targetArrivalStep_const]
theorem targetShapeSigning_const (value reuse : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetShapeSigning (constRate value) reuse f groups remaining =
      f groups remaining + value * (targetCacheLower f groups remaining + targetTreeLower f groups remaining +
        targetCacheLower (targetTreeLower f) groups remaining) + reuse * targetReuseStep f groups remaining := by
  rw [targetShapeSigning, targetFreshStep_const]
def TargetShapeLE (f g : TargetShapeVector) : Prop := ∀ groups remaining, TargetShapeValid groups remaining → f groups remaining ≤ g groups remaining
theorem TargetShapeLE.refl (f : TargetShapeVector) : TargetShapeLE f f := fun _ _ _ => le_rfl
theorem TargetShapeLE.trans {f g h : TargetShapeVector} (hfg : TargetShapeLE f g) (hgh : TargetShapeLE g h) : TargetShapeLE f h :=
  fun G R hv => (hfg G R hv).trans (hgh G R hv)
theorem targetCacheLower_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetCacheLower f) (targetCacheLower g) := by
  intro groups remaining hvalid
  exact Finset.sum_le_sum (fun kept hkept => h kept remaining
    (hvalid.subsets (Finset.mem_powerset.mp (Finset.mem_erase.mp hkept).2) (Finset.Subset.refl _)))
theorem targetTreeLower_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetTreeLower f) (targetTreeLower g) := by
  intro groups remaining hvalid
  exact Finset.sum_le_sum (fun _ _ => h _ _ (hvalid.subsets (Finset.Subset.refl _) Finset.sdiff_subset))
theorem targetReuseStep_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetReuseStep f) (targetReuseStep g) := by
  intro groups remaining hvalid
  apply Finset.sum_le_sum
  intro selected hselected
  exact h _ _ (hvalid.reuse
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2))
theorem targetArrivalStep_shape_mono (arrival : TargetRate) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetArrivalStep arrival f) (targetArrivalStep arrival g) := by
  intro groups remaining hvalid
  exact Finset.sum_le_sum (fun _ _ => mul_le_mul' le_rfl
    (h _ _ (hvalid.subsets Finset.sdiff_subset (Finset.Subset.refl _))))
theorem targetFreshStep_shape_mono (rate : TargetRate) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetFreshStep rate f) (targetFreshStep rate g) := by
  intro groups remaining hvalid
  apply Finset.sum_le_sum
  intro _ _
  apply Finset.sum_le_sum
  intro _ _
  split_ifs
  · exact le_rfl
  · exact mul_le_mul' le_rfl (h _ _ (hvalid.subsets Finset.sdiff_subset Finset.sdiff_subset))
theorem targetShapeQuery_mono (arrival : TargetRate) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetShapeQuery arrival f) (targetShapeQuery arrival g) := by
  intro groups remaining hvalid
  exact add_le_add (h groups remaining hvalid) (targetArrivalStep_shape_mono arrival h groups remaining hvalid)
theorem targetShapeSigning_mono (rate : TargetRate) (reuse : ENNReal) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetShapeSigning rate reuse f) (targetShapeSigning rate reuse g) := by
  intro groups remaining hvalid
  exact add_le_add (add_le_add (h groups remaining hvalid) (targetFreshStep_shape_mono rate h groups remaining hvalid))
    (mul_le_mul' le_rfl (targetReuseStep_shape_mono h groups remaining hvalid))
private theorem sum_erase_empty_indicator {α : Type} [DecidableEq α] (s : Finset (Finset α)) (g : Finset α → ENNReal) :
    ∑ x ∈ s.erase ∅, g x = ∑ x ∈ s, if x = ∅ then 0 else g x := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = ∅ <;> simp [hx]
theorem targetArrival_fresh_commute (arrival rate : TargetRate) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetArrivalStep arrival (targetFreshStep rate f) groups remaining =
      targetFreshStep rate (targetArrivalStep arrival f) groups remaining := by
  unfold targetArrivalStep targetFreshStep
  rw [sum_erase_empty_indicator]
  simp only [sum_erase_empty_indicator, Finset.mul_sum]
  have hleft : ∀ A ∈ groups.powerset,
      (if A = ∅ then 0 else ∑ S ∈ (groups \ A).powerset, ∑ sel ∈ remaining.powerset,
        arrival (groupCoordinates A) * if S = ∅ ∧ sel = ∅ then 0 else
          rate (groupCoordinates S ∪ sel) * f ((groups \ A) \ S) (remaining \ sel)) =
      ∑ S ∈ (groups \ A).powerset, ∑ sel ∈ remaining.powerset,
        (if A = ∅ ∨ (S = ∅ ∧ sel = ∅) then 0 else
          arrival (groupCoordinates A) * rate (groupCoordinates S ∪ sel) * f (groups \ (A ∪ S)) (remaining \ sel)) := by
    intro A _
    by_cases hA : A = ∅
    · simp [hA]
    · rw [if_neg hA]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro sel _
      rw [sdiff_sdiff_left, Finset.sup_eq_union]
      split_ifs <;> simp_all [mul_assoc]
  have hright : ∀ S ∈ groups.powerset, ∀ sel ∈ remaining.powerset,
      (if S = ∅ ∧ sel = ∅ then 0 else rate (groupCoordinates S ∪ sel) *
        ∑ A ∈ (groups \ S).powerset, if A = ∅ then 0 else arrival (groupCoordinates A) * f ((groups \ S) \ A) (remaining \ sel)) =
      ∑ A ∈ (groups \ S).powerset,
        (if A = ∅ ∨ (S = ∅ ∧ sel = ∅) then 0 else
          arrival (groupCoordinates A) * rate (groupCoordinates S ∪ sel) * f (groups \ (A ∪ S)) (remaining \ sel)) := by
    intro S _ sel _
    by_cases hS : S = ∅ ∧ sel = ∅
    · simp [hS]
    · rw [if_neg hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      rw [sdiff_sdiff_left, Finset.sup_eq_union, Finset.union_comm S A]
      split_ifs <;> simp_all
      ring
  rw [Finset.sum_congr rfl hleft]
  simp only [Finset.mul_sum] at hright
  rw [Finset.sum_congr rfl (fun S hS => Finset.sum_congr rfl (fun sel hsel => hright S hS sel hsel))]
  rw [Finset.sum_comm' (t' := groups.powerset) (s' := fun S => (groups \ S).powerset)]
  · apply Finset.sum_congr rfl
    intro S _
    exact Finset.sum_comm
  · intro A S
    simp only [Finset.mem_powerset, Finset.subset_sdiff]
    constructor
    · rintro ⟨hA, hS, hdisj⟩
      exact ⟨⟨hA, hdisj.symm⟩, hS⟩
    · rintro ⟨⟨hA, hdisj⟩, hS⟩
      exact ⟨hA, hS, hdisj.symm⟩
theorem targetArrival_reuse_le (arrival : TargetRate) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetArrivalStep arrival (targetReuseStep f) groups remaining ≤
      targetReuseStep (targetArrivalStep arrival f) groups remaining := by
  unfold targetArrivalStep targetReuseStep
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro selected hselected
  have hnot : selected ∉ groups := hvalid.new_group
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2)
  have hterm : ∀ A ∈ groups.powerset.erase ∅,
      arrival (groupCoordinates A) * f (insert selected (groups \ A)) (remaining \ selected) =
        arrival (groupCoordinates A) * f (insert selected groups \ A) (remaining \ selected) := by
    intro A hA
    have hsel : selected ∉ A := fun h => hnot (Finset.mem_powerset.mp (Finset.mem_erase.mp hA).2 h)
    rw [Finset.insert_sdiff_of_notMem _ hsel]
  rw [Finset.sum_congr rfl hterm]
  apply Finset.sum_le_sum_of_subset
  intro A hA
  obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hA
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hsub).trans (Finset.subset_insert _ _))⟩
theorem targetShapeQuery_signing_le (rate : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (f : TargetShapeVector) :
    TargetShapeLE (targetShapeQuery arrival (targetShapeSigning rate reuse f)) (targetShapeSigning rate reuse (targetShapeQuery arrival f)) := by
  intro groups remaining hvalid
  have hleft : targetShapeQuery arrival (targetShapeSigning rate reuse f) groups remaining =
      f groups remaining + targetFreshStep rate f groups remaining + reuse * targetReuseStep f groups remaining +
        (targetArrivalStep arrival f groups remaining + targetArrivalStep arrival (targetFreshStep rate f) groups remaining +
          reuse * targetArrivalStep arrival (targetReuseStep f) groups remaining) := by
    unfold targetShapeQuery
    change _ + targetArrivalStep arrival
      (fun G R => (f G R + targetFreshStep rate f G R) + reuse * targetReuseStep f G R) groups remaining = _
    rw [targetArrivalStep_add, targetArrivalStep_mul, targetArrivalStep_add]
    rfl
  have hright : targetShapeSigning rate reuse (targetShapeQuery arrival f) groups remaining =
      f groups remaining + targetArrivalStep arrival f groups remaining +
        (targetFreshStep rate f groups remaining + targetFreshStep rate (targetArrivalStep arrival f) groups remaining) +
          reuse * (targetReuseStep f groups remaining + targetReuseStep (targetArrivalStep arrival f) groups remaining) := by
    unfold targetShapeSigning targetShapeQuery
    change _ + targetFreshStep rate (fun G R => f G R + targetArrivalStep arrival f G R) groups remaining +
      reuse * targetReuseStep (fun G R => f G R + targetArrivalStep arrival f G R) groups remaining = _
    rw [targetFreshStep_add, targetReuseStep_add]
  rw [hleft, hright, targetArrival_fresh_commute]
  have h := targetArrival_reuse_le arrival f groups remaining hvalid
  calc
    _ = f groups remaining + targetArrivalStep arrival f groups remaining +
        (targetFreshStep rate f groups remaining + targetFreshStep rate (targetArrivalStep arrival f) groups remaining) +
          reuse * (targetReuseStep f groups remaining + targetArrivalStep arrival (targetReuseStep f) groups remaining) := by ring
    _ ≤ _ := by gcongr
noncomputable def targetShapeEnvelope (rate : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signings : Nat)
    (f : TargetShapeVector) : TargetShapeVector :=
  (targetShapeSigning rate reuse)^[signings] ((targetShapeQuery arrival)^[queries] f)
theorem targetShapeSigning_iterate_mono (rate : TargetRate) (reuse : ENNReal) (signings : Nat) {f g : TargetShapeVector}
    (h : TargetShapeLE f g) :
    TargetShapeLE ((targetShapeSigning rate reuse)^[signings] f) ((targetShapeSigning rate reuse)^[signings] g) := by
  induction signings with
  | zero => exact h
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact targetShapeSigning_mono rate reuse ih
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_TargetShapeContinuation ====
section

namespace SphincsSecurity.Concrete
open ENNReal
theorem targetShapeQuery_iterate_mono (arrival : TargetRate) (queries : Nat) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE ((targetShapeQuery arrival)^[queries] f) ((targetShapeQuery arrival)^[queries] g) := by
  induction queries with
  | zero => exact h
  | succ queries ih =>
      simp only [Function.iterate_succ_apply']
      exact targetShapeQuery_mono arrival ih
theorem targetShapeEnvelope_mono (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signings : Nat)
    {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetShapeEnvelope uniform reuse arrival queries signings f) (targetShapeEnvelope uniform reuse arrival queries signings g) :=
  targetShapeSigning_iterate_mono uniform reuse signings (targetShapeQuery_iterate_mono arrival queries h)
theorem targetShapeEnvelope_queries_mono (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (signings : Nat) (f : TargetShapeVector)
    {small large : Nat} (h : small ≤ large) :
    TargetShapeLE (targetShapeEnvelope uniform reuse arrival small signings f) (targetShapeEnvelope uniform reuse arrival large signings f) := by
  apply targetShapeSigning_iterate_mono
  intro G R _
  exact Function.monotone_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeQuery arrival f from fun _ _ _ => le_self_add) h f G R
theorem le_targetShapeEnvelope (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signings : Nat) (f : TargetShapeVector) :
    f ≤ targetShapeEnvelope uniform reuse arrival queries signings f :=
  (Function.id_le_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeQuery arrival f from fun _ _ _ => le_self_add) queries f).trans
    (Function.id_le_iterate_of_id_le (show ∀ f : TargetShapeVector, f ≤ targetShapeSigning uniform reuse f from
      fun _ _ _ => le_self_add.trans le_self_add) signings _)
theorem targetShapeEnvelope_query (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signings : Nat) (f : TargetShapeVector) :
    targetShapeEnvelope uniform reuse arrival queries signings (targetShapeQuery arrival f) =
      targetShapeEnvelope uniform reuse arrival (queries + 1) signings f := by
  simp only [targetShapeEnvelope, Function.iterate_succ_apply]
theorem targetShapeQuery_iterate_signing_le (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries : Nat) (f : TargetShapeVector) :
    TargetShapeLE ((targetShapeQuery arrival)^[queries] (targetShapeSigning uniform reuse f))
      (targetShapeSigning uniform reuse ((targetShapeQuery arrival)^[queries] f)) := by
  induction queries with
  | zero => exact TargetShapeLE.refl _
  | succ queries ih =>
      simp only [Function.iterate_succ_apply']
      exact (targetShapeQuery_mono arrival ih).trans (targetShapeQuery_signing_le uniform reuse arrival _)
theorem targetShapeEnvelope_signing_le (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signings : Nat) (f : TargetShapeVector) :
    TargetShapeLE (targetShapeEnvelope uniform reuse arrival queries signings (targetShapeSigning uniform reuse f))
      (targetShapeEnvelope uniform reuse arrival queries (signings + 1) f) := by
  unfold targetShapeEnvelope
  rw [Function.iterate_succ_apply]
  exact targetShapeSigning_iterate_mono uniform reuse signings (targetShapeQuery_iterate_signing_le uniform reuse arrival queries f)
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_TargetShapeExpectation ====
section

namespace SphincsSecurity.Concrete
open ENNReal
theorem targetCacheLower_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetCacheLower (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetCacheLower (moments result) groups remaining := by
  unfold targetCacheLower
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
theorem targetTreeLower_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetTreeLower (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetTreeLower (moments result) groups remaining := by
  unfold targetTreeLower
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
theorem targetReuseStep_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetReuseStep (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetReuseStep (moments result) groups remaining := by
  unfold targetReuseStep
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
theorem targetArrivalStep_tsum {α : Type} (arrival : TargetRate) (moments : α → TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetArrivalStep arrival (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetArrivalStep arrival (moments result) groups remaining := by
  unfold targetArrivalStep
  simp only [← ENNReal.tsum_mul_left]
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
theorem targetFreshStep_tsum {α : Type} (rate : TargetRate) (moments : α → TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetFreshStep rate (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetFreshStep rate (moments result) groups remaining := by
  unfold targetFreshStep
  have hinner : ∀ removed selected,
      (if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        rate (groupCoordinates removed ∪ selected) * ∑' result, moments result (groups \ removed) (remaining \ selected)) =
      ∑' result, (if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        rate (groupCoordinates removed ∪ selected) * moments result (groups \ removed) (remaining \ selected)) := by
    intro removed selected
    split_ifs
    · simp
    · exact ENNReal.tsum_mul_left.symm
  simp only [hinner]
  calc
    _ = ∑ removed ∈ groups.powerset, ∑' result, ∑ selected ∈ remaining.powerset,
        (if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
          rate (groupCoordinates removed ∪ selected) * moments result (groups \ removed) (remaining \ selected)) :=
      Finset.sum_congr rfl (fun _ _ => (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm)
    _ = _ := (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
theorem targetShapeQuery_tsum {α : Type} (arrival : TargetRate) (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeQuery arrival (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeQuery arrival (moments result) groups remaining := by
  simp only [targetShapeQuery, targetArrivalStep_tsum, ENNReal.tsum_add]
theorem targetShapeSigning_tsum {α : Type} (uniform : TargetRate) (reuse : ENNReal) (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeSigning uniform reuse (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeSigning uniform reuse (moments result) groups remaining := by
  simp only [targetShapeSigning, targetFreshStep_tsum, targetReuseStep_tsum, ENNReal.tsum_mul_left, ENNReal.tsum_add]
theorem targetShapeQuery_mul (arrival : TargetRate) (scalar : ENNReal) (moments : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeQuery arrival (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeQuery arrival moments groups remaining := by
  simp only [targetShapeQuery, targetArrivalStep_mul]
  ring
theorem targetShapeSigning_mul (uniform : TargetRate) (reuse scalar : ENNReal) (moments : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeSigning uniform reuse (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeSigning uniform reuse moments groups remaining := by
  simp only [targetShapeSigning, targetFreshStep_mul, targetReuseStep_mul]
  ring
theorem targetShapeEnvelope_tsum {α : Type} (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signatures : Nat)
    (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeEnvelope uniform reuse arrival queries signatures (moments result) groups remaining := by
  have hquery (count : Nat) : (targetShapeQuery arrival)^[count] (fun G R => ∑' result, moments result G R) =
      fun G R => ∑' result, (targetShapeQuery arrival)^[count] (moments result) G R := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [Function.iterate_succ_apply', ih]
        funext G R
        exact targetShapeQuery_tsum arrival _ G R
  unfold targetShapeEnvelope
  rw [hquery]
  induction signatures generalizing groups remaining with
  | zero => rfl
  | succ signatures ih =>
      simp only [Function.iterate_succ_apply']
      have hsign : (targetShapeSigning uniform reuse)^[signatures]
          (fun G R => ∑' result, (targetShapeQuery arrival)^[queries] (moments result) G R) =
          fun G R => ∑' result, (targetShapeSigning uniform reuse)^[signatures] ((targetShapeQuery arrival)^[queries] (moments result)) G R := by
        funext G R
        exact ih G R
      rw [hsign]
      exact targetShapeSigning_tsum uniform reuse _ groups remaining
theorem targetShapeEnvelope_mul (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (scalar : ENNReal) (queries signatures : Nat)
    (moments : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeEnvelope uniform reuse arrival queries signatures moments groups remaining := by
  have hquery (count : Nat) : (targetShapeQuery arrival)^[count] (fun G R => scalar * moments G R) =
      fun G R => scalar * (targetShapeQuery arrival)^[count] moments G R := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [Function.iterate_succ_apply', ih]
        funext G R
        exact targetShapeQuery_mul arrival scalar _ G R
  unfold targetShapeEnvelope
  rw [hquery]
  induction signatures generalizing groups remaining with
  | zero => rfl
  | succ signatures ih =>
      simp only [Function.iterate_succ_apply']
      have hsign : (targetShapeSigning uniform reuse)^[signatures]
          (fun G R => scalar * (targetShapeQuery arrival)^[queries] moments G R) =
          fun G R => scalar * (targetShapeSigning uniform reuse)^[signatures] ((targetShapeQuery arrival)^[queries] moments) G R := by
        funext G R
        exact ih G R
      rw [hsign]
      exact targetShapeSigning_mul uniform reuse scalar _ groups remaining
theorem targetShapeEnvelope_expected {α : Type} (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signatures : Nat)
    (weight : α → ENNReal) (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    (∑' result, weight result * targetShapeEnvelope uniform reuse arrival queries signatures (moments result) groups remaining) =
      targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => ∑' result, weight result * moments result G R) groups remaining := by
  rw [targetShapeEnvelope_tsum]
  apply tsum_congr
  intro result
  exact (targetShapeEnvelope_mul uniform reuse arrival (weight result) queries signatures (moments result) groups remaining).symm
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Scheme_BuildEval ====
section

section
namespace SphincsSecurity.Concrete
def ScheduleRead (r : Nat × Nat) : Prop := r.1 < ftsTreeHeight ∧ r.2 < 2 ^ (ftsTreeHeight - r.1)
def ScheduleGood (state : ScheduleState) : Prop :=
  (∀ segment ∈ state.done, ∀ r ∈ segment.reads, ScheduleRead r) ∧ ∀ r ∈ state.reads, ScheduleRead r
theorem heap_climb (v height : Nat) (hv : v < 2 ^ ftsTreeHeight) (hheight : height ≤ ftsTreeHeight) :
    (2 ^ ftsTreeHeight + v) / 2 ^ height = 2 ^ (ftsTreeHeight - height) + v / 2 ^ height
      ∧ v / 2 ^ height < 2 ^ (ftsTreeHeight - height) := by
  have hsplit : 2 ^ ftsTreeHeight = 2 ^ (ftsTreeHeight - height) * 2 ^ height := by
    rw [← pow_add, Nat.sub_add_cancel hheight]
  have hpos : 0 < 2 ^ height := Nat.two_pow_pos _
  refine ⟨?_, ?_⟩
  · rw [hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.add_comm]
  · rw [Nat.div_lt_iff_lt_mul hpos, ← hsplit]
    exact hv
theorem scheduleStep_good (v height : Nat) (hv : v < 2 ^ ftsTreeHeight) (hheight : height < ftsTreeHeight)
    (state : ScheduleState) (hheap : state.heap = (2 ^ ftsTreeHeight + v) / 2 ^ height)
    (hgood : ScheduleGood state) :
    ScheduleGood (scheduleStep state height)
      ∧ (scheduleStep state height).heap = (2 ^ ftsTreeHeight + v) / 2 ^ (height + 1) := by
  obtain ⟨hclimb, hoffset⟩ := heap_climb v height hv hheight.le
  have heven : 2 ^ (ftsTreeHeight - height) = 2 * 2 ^ (ftsTreeHeight - height - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hhalf : (2 ^ ftsTreeHeight + v) / 2 ^ (height + 1) = state.heap / 2 := by
    rw [hheap, div_pow_succ]
  have hfold : ScheduleGood { state with
      reads := state.reads ++ [(height, (state.heap ^^^ 1) - 2 ^ (ftsTreeHeight - height))],
      heap := state.heap / 2 } := by
    refine ⟨hgood.1, fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact hgood.2 r hr
    · rw [List.mem_singleton] at hr
      subst r
      refine ⟨hheight, ?_⟩
      obtain ⟨j, hcase⟩ := index_sibling_cases state.heap
      rw [← nat_xor_eq]
      simp only
      rcases hcase with ⟨hc, hx, _⟩ | ⟨hc, hx, _⟩ <;> rw [hx] <;> omega
  unfold scheduleStep
  split
  · rename_i top rest hstack
    split
    · refine ⟨⟨fun segment hsegment => ?_, fun r hr => by simp at hr⟩, hhalf.symm⟩
      rcases List.mem_append.mp hsegment with hsegment | hsegment
      · exact hgood.1 segment hsegment
      · rw [List.mem_singleton] at hsegment
        subst segment
        exact hgood.2
    · exact ⟨hfold, hhalf.symm⟩
  · exact ⟨hfold, hhalf.symm⟩
theorem foldl_scheduleStep_good (v : Nat) (hv : v < 2 ^ ftsTreeHeight) :
    ∀ n, n ≤ ftsTreeHeight → ∀ state : ScheduleState, state.heap = 2 ^ ftsTreeHeight + v →
      ScheduleGood state →
      ScheduleGood ((List.range n).foldl scheduleStep state)
        ∧ ((List.range n).foldl scheduleStep state).heap = (2 ^ ftsTreeHeight + v) / 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro _ state hheap hgood
      simp only [List.range_zero, List.foldl_nil, pow_zero, Nat.div_one]
      exact ⟨hgood, hheap⟩
  | succ n ih =>
      intro hn state hheap hgood
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hgood', hheap'⟩ := ih (by omega) state hheap hgood
      exact scheduleStep_good v n hv (by omega) _ hheap' hgood'
theorem bitLength_xor_le (v w : Nat) (hv : v < 2 ^ ftsTreeHeight) (hw : w < 2 ^ ftsTreeHeight) :
    bitLength (v ^^^ w) ≤ ftsTreeHeight := by
  have hlt : v ^^^ w < 2 ^ ftsTreeHeight := Nat.xor_lt_two_pow hv hw
  unfold bitLength
  split
  · omega
  · rename_i hne
    have := (Nat.log2_lt hne).mpr hlt
    omega
theorem leafClimb_good (v top : Nat) (hv : v < 2 ^ ftsTreeHeight) (htop : top ≤ ftsTreeHeight)
    (state : ScheduleState) (hgood : ScheduleGood state) :
    let climbed := (List.range top).foldl scheduleStep
      { state with heap := 2 ^ ftsTreeHeight ||| v,
                   parity := decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), reads := [] }
    ScheduleGood { climbed with done := climbed.done ++ [⟨false, climbed.parity, climbed.reads⟩] } := by
  intro climbed
  have hor : 2 ^ ftsTreeHeight ||| v = 2 ^ ftsTreeHeight + v := by
    have := Nat.two_pow_add_eq_or_of_lt hv 1
    simpa using this.symm
  obtain ⟨hclimb, _⟩ := foldl_scheduleStep_good v hv top htop
    { state with heap := 2 ^ ftsTreeHeight ||| v,
                 parity := decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), reads := [] }
    hor ⟨hgood.1, fun r hr => by simp at hr⟩
  refine ⟨fun segment hsegment => ?_, hclimb.2⟩
  rcases List.mem_append.mp hsegment with hsegment | hsegment
  · exact hclimb.1 segment hsegment
  · rw [List.mem_singleton] at hsegment
    subst segment
    exact hclimb.2
theorem scheduleLeaves_good : ∀ (sorted : List Nat), (∀ v ∈ sorted, v < 2 ^ ftsTreeHeight) →
    ∀ state : ScheduleState, ScheduleGood state → ScheduleGood (scheduleLeaves sorted state) := by
  intro sorted
  induction sorted with
  | nil => intro _ state hgood; exact hgood
  | cons v rest ih =>
      intro hsorted state hgood
      have hv : v < 2 ^ ftsTreeHeight := hsorted v (List.mem_cons_self ..)
      have hrest : ∀ w ∈ rest, w < 2 ^ ftsTreeHeight := fun w hw => hsorted w (List.mem_cons_of_mem _ hw)
      cases rest with
      | nil =>
          rw [scheduleLeaves.eq_2, scheduleLeaves.eq_1]
          exact leafClimb_good v ftsTreeHeight hv le_rfl state hgood
      | cons w rest' =>
          rw [scheduleLeaves.eq_def]
          dsimp only
          apply ih hrest
          have hle := bitLength_xor_le v w hv (hrest w (List.mem_cons_self ..))
          have hclosed := leafClimb_good v (bitLength (v ^^^ w) - 1) hv (by omega) state hgood
          exact ⟨hclosed.1, hclosed.2⟩
theorem schedule_read (sorted : List Nat) (hsorted : ∀ v ∈ sorted, v < 2 ^ ftsTreeHeight) :
    ∀ segment ∈ schedule sorted, ∀ r ∈ segment.reads, ScheduleRead r :=
  (scheduleLeaves_good sorted hsorted ⟨[], [], 0, false, []⟩
    ⟨fun segment hsegment => by simp at hsegment, fun r hr => by simp at hr⟩).1
theorem sortedLeaves_lt (leaves : IndexGroup → FtsLeaf) :
    ∀ v ∈ sortedLeaves leaves, v < 2 ^ ftsTreeHeight := by
  intro v hv
  simp only [sortedLeaves, List.mem_map] at hv
  obtain ⟨r, _, rfl⟩ := hv
  exact (leaves r).isLt
theorem honestFts_congr (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node node' : Nat → Nat → Digest)
    (hnode : ∀ segment ∈ schedule (sortedLeaves leaves), ∀ r ∈ segment.reads,
      node r.1 r.2 = node' r.1 r.2) :
    honestFts leaves secret node = honestFts leaves secret node' := by
  unfold honestFts
  dsimp only
  rw [FtsSignature.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext j
  generalize hsegment : (schedule (sortedLeaves leaves)).getD j.val default = segment
  have hmem : segment ∈ schedule (sortedLeaves leaves) ∨ segment = default := by
    rw [← hsegment, List.getD_eq_getElem?_getD]
    cases h : (schedule (sortedLeaves leaves))[j.val]? with
    | none => exact Or.inr rfl
    | some s => exact Or.inl (List.mem_of_getElem? h)
  refine congrArg (ScheduleSegment.toSegment segment) ?_
  funext i
  have hi : i.val < segment.reads.length :=
    Nat.lt_of_lt_of_le i.isLt (Nat.mod_le _ _)
  rw [List.getD_eq_getElem _ _ hi]
  rcases hmem with hmem | hdefault
  · exact hnode segment hmem _ (List.getElem_mem hi)
  · subst hdefault
    exact (Nat.not_lt_zero i.val hi).elim
theorem honestFts_congr_tree (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node node' : Nat → Nat → Digest)
    (hnode : ∀ level nodeIdx, level < ftsTreeHeight → nodeIdx < 2 ^ (ftsTreeHeight - level) →
      node level nodeIdx = node' level nodeIdx) :
    honestFts leaves secret node = honestFts leaves secret node' :=
  honestFts_congr leaves secret node node' fun segment hsegment r hr =>
    let hread := schedule_read _ (sortedLeaves_lt leaves) segment hsegment r hr
    hnode r.1 r.2 hread.1 hread.2
end SphincsSecurity.Concrete
end
section
open OracleComp OracleSpec
namespace SphincsSecurity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit true
set_option maxRecDepth 4096
def restrictPath (lay : Layer) (path : Fin maxLayerHeight → α) : Fin (layerHeight lay) → α :=
  fun level => path (level.castLE (layerHeight_le lay))
end SphincsSecurity
end
section
namespace SphincsSecurity.Concrete
open OracleComp
variable (f : QueryImpl HashSpec Id)
theorem sequenceFin_option_eq {α : Type} {n : Nat} (values : Fin n → Option α) :
    sequenceFin (m := Option) values =
      if h : ∀ i, (values i).isSome then some (fun i => (values i).get (h i)) else none := by
  induction n with
  | zero =>
      rw [dif_pos (fun i => i.elim0)]
      simp only [sequenceFin]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      cases h0 : values 0 with
      | none =>
          rw [dif_neg (fun h => by have := h 0; rw [h0] at this; simp at this)]
          rw [sequenceFin, h0]
          rfl
      | some head =>
          have hstep : sequenceFin (m := Option) values =
              sequenceFin (m := Option) (fun i : Fin n => values i.succ) >>= fun tail =>
                some (Fin.cases head tail) := by
            rw [sequenceFin, h0]
            rfl
          rw [hstep, ih]
          by_cases hall : ∀ i, (values i).isSome
          · rw [dif_pos (fun i : Fin n => hall i.succ), dif_pos hall]
            simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
            funext i
            cases i using Fin.cases with
            | zero => simp [h0]
            | succ i => rfl
          · rw [dif_neg hall]
            have htail : ¬ ∀ i : Fin n, (values i.succ).isSome := by
              intro htail
              apply hall
              intro i
              cases i using Fin.cases with
              | zero => simp [h0]
              | succ i => exact htail i
            rw [dif_neg htail]
            rfl
theorem eval_buildLevel (hashNode : Nat → Digest → Digest → OracleComp HashSpec Digest)
    (width : Nat) (below : Nat → Digest) :
    evalWithAnswerFn f (buildLevel hashNode width below) = fun nodeIdx =>
      if h : nodeIdx < width then
        evalWithAnswerFn f (hashNode nodeIdx (below (2 * nodeIdx)) (below (2 * nodeIdx + 1)))
      else 0 := by
  simp only [buildLevel, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]
theorem eval_buildLevels (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (height : Nat) (leaves : Nat → Digest) (node : Nat → Nat → Digest)
    (hleaf : ∀ nodeIdx, nodeIdx < 2 ^ height → leaves nodeIdx = node 0 nodeIdx)
    (hnode : ∀ level nodeIdx, level < height → nodeIdx < 2 ^ (height - (level + 1)) →
      evalWithAnswerFn f (hashNode (level + 1) nodeIdx (node level (2 * nodeIdx))
        (node level (2 * nodeIdx + 1))) = node (level + 1) nodeIdx)
    (levels : Nat) (hlevels : levels ≤ height) :
    ∀ level, level ≤ levels → ∀ nodeIdx, nodeIdx < 2 ^ (height - level) →
      evalWithAnswerFn f (buildLevels hashNode height leaves levels) level nodeIdx
        = node level nodeIdx := by
  induction levels with
  | zero =>
      intro level hlevel nodeIdx hnodeIdx
      have hl : level = 0 := by omega
      subst hl
      simp only [buildLevels, evalWithAnswerFn_pure]
      exact hleaf nodeIdx (by simpa using hnodeIdx)
  | succ levels ih =>
      intro level hlevel nodeIdx hnodeIdx
      simp only [buildLevels, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_buildLevel]
      by_cases hl : level = levels + 1
      · subst hl
        rw [if_pos rfl, dif_pos hnodeIdx]
        have hpow : 2 ^ (height - levels) = 2 * 2 ^ (height - (levels + 1)) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [ih (by omega) levels le_rfl (2 * nodeIdx) (by omega),
          ih (by omega) levels le_rfl (2 * nodeIdx + 1) (by omega)]
        exact hnode levels nodeIdx (by omega) hnodeIdx
      · rw [if_neg hl]
        exact ih (by omega) level (by omega) nodeIdx hnodeIdx
theorem eval_buildChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : OracleComp HashSpec Digest) (digit : Digit) :
    evalWithAnswerFn f (buildChain parameter lay tree leaf chainIdx secret digit.val) =
      (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val
          (evalWithAnswerFn f secret)),
        evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1)
          (evalWithAnswerFn f secret))) := by
  simp only [buildChain, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  congr 1
  have h := eval_recoverChain f parameter lay tree leaf chainIdx digit (evalWithAnswerFn f secret)
  simpa only [recoverChain] using h
theorem eval_buildLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    evalWithAnswerFn f (buildLeaf parameter lay tree leaf (secret leaf) digits) =
      (fun chainIdx => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0
          (digits chainIdx).val (evalWithAnswerFn f (secret leaf chainIdx))),
        honestNode f parameter lay tree (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx))
          0 leaf.val) := by
  rw [honestNode_zero_eq_leafHash]
  simp only [buildLeaf, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_buildChain,
    evalWithAnswerFn_pure, leafHash, eval_tweakableHash]
  rfl
theorem xor_div_lt {leaf height level : Nat} (hleaf : leaf < 2 ^ height) (hlevel : level < height) :
    Nat.xor (leaf / 2 ^ level) 1 < 2 ^ (height - level) := by
  have hdiv : leaf / 2 ^ level < 2 ^ (height - level) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    rwa [Nat.sub_add_cancel hlevel.le]
  exact Nat.xor_lt_two_pow hdiv (Nat.one_lt_two_pow (by omega))
theorem eval_buildLayerTree_table (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    let leaves := evalWithAnswerFn f (sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
      buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
        (if leafNat.val = leaf.val then digits else zeroEncoding))
    ∀ level, level ≤ layerHeight lay → ∀ nodeIdx, nodeIdx < 2 ^ (layerHeight lay - level) →
      evalWithAnswerFn f (buildLevels
        (fun level nodeIdx left right =>
          tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
        (layerHeight lay)
        (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
        (layerHeight lay)) level nodeIdx
        = honestNode f parameter lay tree
            (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)) level nodeIdx := by
  intro leaves level hlevel nodeIdx hnodeIdx
  apply eval_buildLevels f _ _ _
    (fun level nodeIdx => honestNode f parameter lay tree
      (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)) level nodeIdx)
  · intro nodeIdx hnodeIdx
    rw [dif_pos hnodeIdx]
    simp only [leaves, evalWithAnswerFn_sequenceFin, eval_buildLeaf]
    congr 1
    simp only [leafOfNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hnodeIdx
      (Nat.pow_le_pow_right (by omega) (layerHeight_le lay)))]
  · intro level nodeIdx _ _
    rw [eval_tweakableHash, honestNode_succ]
  · exact le_rfl
  · exact hlevel
  · exact hnodeIdx
theorem eval_buildLayerTree (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (hleaf : leaf.val < 2 ^ layerHeight lay) (digits : Encoding) :
    let result := evalWithAnswerFn f (buildLayerTree parameter lay tree secret leaf digits)
    let table := fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)
    result.1 = (fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (digits chainIdx).val (table leaf chainIdx)))
      ∧ (∀ level, level < layerHeight lay →
          result.2.1 level = honestNode f parameter lay tree table level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∧ result.2.2 = honestNode f parameter lay tree table (layerHeight lay) 0 := by
  intro result table
  have htable := eval_buildLayerTree_table f parameter lay tree secret leaf digits
  simp only [result, buildLayerTree, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  refine ⟨?_, ?_, ?_⟩
  · rw [dif_pos hleaf]
    simp only [evalWithAnswerFn_sequenceFin, eval_buildLeaf]
    funext chainIdx
    simp only [leafOfNat_val, if_true, table]
  · intro level hlevel
    exact htable level hlevel.le _ (xor_div_lt hleaf hlevel)
  · exact htable _ le_rfl 0 (by simp)
theorem eval_buildLayerTree_root (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (hleaf : leaf.val < 2 ^ layerHeight lay) (digits : Encoding) :
    (evalWithAnswerFn f (buildLayerTree parameter lay tree secret leaf digits)).2.2
      = evalWithAnswerFn f (treeRoot parameter lay tree
          (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx))) :=
  (eval_buildLayerTree f parameter lay tree secret leaf hleaf digits).2.2
theorem eval_keygenRoot (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    evalWithAnswerFn f (keygenRoot parameter secret)
      = evalWithAnswerFn f (treeRoot parameter topLayer rootTree secret) := by
  have h := eval_buildLayerTree_root f parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩
    (Nat.two_pow_pos _) zeroEncoding
  simp only [evalWithAnswerFn_pure] at h
  unfold keygenRoot
  rw [evalWithAnswerFn_bind]
  split
  next values path root hresult =>
    rw [evalWithAnswerFn_pure, ← h, hresult]
theorem buildLayerTree_eq_table (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTree parameter lay tree secret leaf digits =
      (fun built : (Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest) =>
        ((if h : leaf.val < 2 ^ layerHeight lay then (built.1 ⟨leaf.val, h⟩).1 else fun _ => 0),
          (fun level => built.2 level (Nat.xor (leaf.val / 2 ^ level) 1)), built.2 (layerHeight lay) 0)) <$>
        buildLayerTable parameter lay tree secret leaf digits := by
  simp only [buildLayerTree, buildLayerTable, map_bind, bind_assoc, pure_bind, map_pure]
theorem eval_keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (level : Nat) (hlevel : level ≤ layerHeight topLayer) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (layerHeight topLayer - level)) :
    evalWithAnswerFn f (keygenTable parameter secret) level nodeIdx
      = honestNode f parameter topLayer rootTree secret level nodeIdx := by
  have htable := eval_buildLayerTree_table f parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
    level hlevel nodeIdx hnodeIdx
  simp only [evalWithAnswerFn_pure] at htable
  unfold keygenTable
  rw [evalWithAnswerFn_bind]
  split
  next leaves table hresult =>
    rw [evalWithAnswerFn_pure]
    have hsnd := congrArg Prod.snd hresult
    simp only [buildLayerTable, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hsnd
    rw [← hsnd]
    exact htable
def TopAgrees (key : SecretKey) (topNode : Nat → Nat → OracleComp HashSpec Digest) : Prop :=
  ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
    evalWithAnswerFn f (topNode level nodeIdx)
      = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) level nodeIdx
abbrev KeyTopHonest (key : SecretKey) : Prop :=
  TopAgrees f key (fun level nodeIdx => pure (key.top level nodeIdx))
noncomputable def honestTop (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    Nat → Nat → Digest :=
  evalWithAnswerFn f (keygenTable parameter secret)
theorem honestTop_root (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    honestTop f parameter secret (layerHeight topLayer) 0 =
      honestNode f parameter topLayer rootTree secret (layerHeight topLayer) 0 :=
  eval_keygenTable f parameter secret _ le_rfl 0 (by rw [Nat.sub_self, pow_zero]; exact Nat.one_pos)
theorem keyTopHonest_of_eq (key : SecretKey)
    (h : key.top = honestTop f key.parameter (key.otsSecret topLayer rootTree)) : KeyTopHonest f key := by
  intro level hlevel nodeIdx hnodeIdx
  have hheight : layerHeight topLayer = maxLayerHeight := rfl
  have heval := eval_keygenTable f key.parameter (key.otsSecret topLayer rootTree) level
    (by rw [hheight]; exact hlevel.le) nodeIdx (by rw [hheight]; exact hnodeIdx)
  rw [evalWithAnswerFn_pure, h]
  exact heval
theorem keyTopHonest_withTop (key : SecretKey) :
    KeyTopHonest f { key with top := honestTop f key.parameter (key.otsSecret topLayer rootTree) } :=
  keyTopHonest_of_eq f _ rfl
theorem eval_buildFtsTree (parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → OracleComp HashSpec Digest) :
    let result := evalWithAnswerFn f (buildFtsTree parameter index secret)
    let table := fun leaf => evalWithAnswerFn f (secret leaf)
    result.1 = table
      ∧ ∀ level, level ≤ ftsTreeHeight → ∀ nodeIdx, nodeIdx < 2 ^ (ftsTreeHeight - level) →
          result.2 level nodeIdx = honestFtsNode f parameter index porsTree table level nodeIdx := by
  intro result table
  have htable : ∀ level, level ≤ ftsTreeHeight → ∀ nodeIdx, nodeIdx < 2 ^ (ftsTreeHeight - level) →
      evalWithAnswerFn f (buildLevels
        (fun level nodeIdx left right =>
          tweakableHash parameter (.ftsNode index porsTree (ftsHeapIndex level nodeIdx))
            (nodePayload left right))
        ftsTreeHeight
        (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then
          ((evalWithAnswerFn f (sequenceFin fun leafIdx : FtsLeaf => do
            let value ← secret leafIdx
            let hashed ← ftsLeafHash parameter index porsTree leafIdx.val value
            return (value, hashed))) ⟨nodeIdx, h⟩).2 else 0)
        ftsTreeHeight) level nodeIdx
        = honestFtsNode f parameter index porsTree table level nodeIdx := by
    apply eval_buildLevels f _ _ _ (fun level nodeIdx => honestFtsNode f parameter index porsTree table level nodeIdx)
    · intro nodeIdx hnodeIdx
      rw [dif_pos hnodeIdx]
      have h := honestFtsNode_zero f parameter index porsTree table ⟨nodeIdx, hnodeIdx⟩
      simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        ftsLeafHash, eval_tweakableHash] at h ⊢
      exact h.symm
    · intro level nodeIdx _ _
      rw [eval_tweakableHash, honestFtsNode_succ]
    · exact le_rfl
  simp only [result, buildFtsTree, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  refine ⟨?_, ?_⟩
  · simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, table]
  · exact htable
theorem eval_ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsOpen parameter index leaves secret)
      = honestFts leaves (secret porsTree) (honestFtsNode f parameter index porsTree (secret porsTree)) := by
  simp only [ftsOpen, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]
  rfl
theorem eval_buildFtsTree_open (parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → OracleComp HashSpec Digest) (leaves : IndexGroup → FtsLeaf) :
    let result := evalWithAnswerFn f (buildFtsTree parameter index secret)
    let table := fun (_ : FtsTree) leaf => evalWithAnswerFn f (secret leaf)
    honestFts leaves result.1 result.2 = evalWithAnswerFn f (ftsOpen parameter index leaves table)
      ∧ result.2 ftsTreeHeight 0 = evalWithAnswerFn f (ftsKey parameter index table) := by
  intro result table
  obtain ⟨hsecrets, hnodes⟩ := eval_buildFtsTree f parameter index secret
  refine ⟨?_, ?_⟩
  · rw [eval_ftsOpen, hsecrets]
    exact honestFts_congr_tree leaves _ _ _ fun level nodeIdx hlevel hnode =>
      hnodes level hlevel.le nodeIdx hnode
  · exact hnodes ftsTreeHeight le_rfl 0 (by simp)
theorem eval_otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat) :
    evalWithAnswerFn f (otsSignFrom parameter lay tree leaf secret message attempts counter)
      = (evalWithAnswerFn f (encodingSearch parameter lay tree leaf message attempts counter)).map
          fun result => (result.1, fun chainIdx => evalWithAnswerFn f
            (chainWalk parameter lay tree leaf chainIdx 0 (result.2 chainIdx).val (secret chainIdx))) := by
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
      simp only [otsSignFrom, encodingSearch, evalWithAnswerFn_bind, encode_eq]
      cases evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message
          (BitVec.ofNat counterBits counter)) with
      | none => exact ih (counter + 1)
      | some word =>
          simp only [evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure,
            Option.map_some]
def LayerOutput.toPadded (lay : Layer) (output : LayerOutput) : PaddedLayer :=
  (output.1, output.2.1, fun level => if level.val < layerHeight lay then output.2.2 level.val else 0)
theorem LayerOutput.toSignature_eq (lay : Layer) (output : LayerOutput) :
    LayerOutput.toSignature lay output = LayerSignature.ofPadded lay (LayerOutput.toPadded lay output) := by
  simp only [LayerOutput.toSignature, LayerOutput.toPadded, LayerSignature.ofPadded, Fin.val_castLE]
  congr
  funext level
  rw [if_pos level.isLt]
theorem eval_treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    evalWithAnswerFn f (treePath parameter lay tree secret leaf) = fun level =>
      if level.val < layerHeight lay then
        honestNode f parameter lay tree secret level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
      else 0 := by
  simp only [treePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs <;> rfl
theorem eval_signLayers (key : SecretKey) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hsecret : ∀ lay tree leaf chainIdx,
      evalWithAnswerFn f (secret lay tree leaf chainIdx) = key.otsSecret lay tree leaf chainIdx)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (htop : TopAgrees f key topNode)
    (remaining : Nat) (hremaining : remaining ≤ numLayers) (message : Digest)
    (hmessage : ∀ h : 0 < remaining,
      message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩)) :
    match evalWithAnswerFn f (signLayers key.parameter index secret topNode remaining message) with
    | none => ∃ lay : Layer, lay.val < remaining ∧ evalWithAnswerFn f (signLayer key index lay) = none
    | some parts => ∀ lay : Layer, lay.val < remaining →
        evalWithAnswerFn f (signLayer key index lay) = some (LayerOutput.toPadded lay (parts lay)) := by
  induction remaining generalizing message with
  | zero =>
      simp only [signLayers, evalWithAnswerFn_pure]
      intro lay hlay
      omega
  | succ remaining ih =>
      have hlayer : remaining < numLayers := by omega
      let lay : Layer := ⟨remaining, hlayer⟩
      have hmsg : message = evalWithAnswerFn f (layerMessage key index lay) := hmessage (by omega)
      have htable : (fun leaf chainIdx => evalWithAnswerFn f
          (secret lay (treeIndexAt index lay) leaf chainIdx)) =
          key.otsSecret lay (treeIndexAt index lay) := by
        funext leaf chainIdx
        exact hsecret _ _ _ _
      have hspec : evalWithAnswerFn f (signLayer key index lay) =
          (evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0)).map fun result =>
              (result.1, fun chainIdx => evalWithAnswerFn f
                (chainWalk key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx 0
                  (result.2 chainIdx).val
                  (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)),
                evalWithAnswerFn f (treePath key.parameter lay (treeIndexAt index lay)
                  (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay))) := by
        simp only [signLayer, evalWithAnswerFn_bind, ← hmsg, otsSign, eval_otsSignFrom]
        cases evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0) with
        | none => rfl
        | some result => simp only [Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      by_cases hzero : remaining = 0
      · subst hzero
        have htree : treeIndexAt index lay = rootTree := Fin.ext (treeIndexAt_topLayer index)
        simp only [signLayers, dif_pos hlayer, ↓reduceIte, signTopLayer, evalWithAnswerFn_bind]
        rw [show topLayer = lay from rfl]
        cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) message encodingAttemptLimit 0) with
        | none =>
            refine ⟨lay, Nat.lt_succ_self _, ?_⟩
            rw [hspec, hsearch]
            rfl
        | some result =>
            obtain ⟨counter, word⟩ := result
            simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalWithAnswerFn_sequenceFin]
            intro other hother
            have hother' : other = lay := Fin.ext (by simp [lay]; omega)
            rw [hother', if_pos rfl, hspec, hsearch]
            simp only [Option.map_some, LayerOutput.toPadded, Option.some.injEq, Prod.mk.injEq, true_and]
            refine ⟨?_, ?_⟩
            · funext chainIdx
              rw [hsecret]
            · rw [eval_treePath]
              funext level
              have hheight : layerHeight lay = maxLayerHeight := rfl
              rw [hheight]
              split_ifs with hlevel
              · rw [htree]
                exact (htop level.val hlevel _ (xor_div_lt (leafIndexAt_lt index lay) hlevel)).symm
              · exact absurd level.isLt hlevel
      simp only [signLayers, dif_pos hlayer, if_neg hzero, evalWithAnswerFn_bind]
      cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
          (leafIndexAt index lay) message encodingAttemptLimit 0) with
      | none =>
          refine ⟨lay, Nat.lt_succ_self _, ?_⟩
          rw [hspec, hsearch]
          rfl
      | some result =>
          obtain ⟨counter, word⟩ := result
          have hbuild := eval_buildLayerTree f key.parameter lay (treeIndexAt index lay)
            (secret lay (treeIndexAt index lay)) (leafIndexAt index lay) (leafIndexAt_lt index lay) word
          rw [htable] at hbuild
          simp only [evalWithAnswerFn_bind]
          revert hbuild
          generalize evalWithAnswerFn f (buildLayerTree key.parameter lay (treeIndexAt index lay)
            (secret lay (treeIndexAt index lay)) (leafIndexAt index lay) word) = built
          rcases built with ⟨values, path, root⟩
          rintro ⟨hvalues, hpath, hroot⟩
          simp only at hvalues hpath hroot
          have hnext : ∀ h : 0 < remaining,
              root = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩) := by
            intro h
            have hbelow : remaining - 1 + 1 < numLayers := by omega
            rw [layerMessage, dif_pos hbelow]
            have hlay : (⟨remaining - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            rw [hlay, hroot]
            simp only [treeRoot, honestNode]
          have hrest := ih (by omega) root hnext
          revert hrest
          cases evalWithAnswerFn f (signLayers key.parameter index secret topNode remaining root) with
          | none =>
              rintro ⟨other, hother, hnone⟩
              exact ⟨other, by omega, hnone⟩
          | some rest =>
              intro hrest other hother
              by_cases hl : other = lay
              · subst hl
                have hif : (if lay = (⟨remaining, hlayer⟩ : Layer) then
                    (counter, (values, path, root).1, (values, path, root).2.1) else rest lay) =
                    (counter, values, path) := if_pos rfl
                simp only [hif]
                rw [hspec, hsearch]
                simp only [Option.map_some, LayerOutput.toPadded, Option.some.injEq, Prod.mk.injEq,
                  true_and]
                refine ⟨hvalues.symm, ?_⟩
                rw [eval_treePath]
                funext level
                split_ifs with hlevel
                · exact (hpath level.val hlevel).symm
                · rfl
              · have hif : (if other = (⟨remaining, hlayer⟩ : Layer) then
                    (counter, values, path) else rest other) = rest other := if_neg hl
                simp only [hif]
                exact hrest other (by
                  have : other.val ≠ remaining := fun h => hl (Fin.ext h)
                  omega)
theorem signAfterDigest_eq_signFrom (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) :
    (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signFrom key.parameter index (fun tree leaf => pure (key.ftsSecret index tree leaf))
        (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx))
        (fun level nodeIdx => pure (key.top level nodeIdx)) randomness leaves := by
  rw [signAfterDigest]
def signatureValue (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : Option Signature :=
  (sequenceFin (m := Option) fun lay => evalWithAnswerFn f (signLayer key index lay)).map fun parts =>
    { randomness := randomness
      fts := evalWithAnswerFn f (ftsOpen key.parameter index leaves (key.ftsSecret index))
      layers := fun lay => LayerSignature.ofPadded lay (parts lay) }
theorem layerMessage_bottomLayer_eq (key : SecretKey) (index : Index) :
    (layerMessage key index bottomLayer : OracleComp HashSpec Digest) =
      ftsKey key.parameter index (key.ftsSecret index) := by
  rw [layerMessage, dif_neg (by decide)]
theorem eval_signFrom (key : SecretKey) (index : Index)
    (ftsGet : FtsTree → FtsLeaf → OracleComp HashSpec Digest)
    (otsGet : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hfts : ∀ tree leaf, evalWithAnswerFn f (ftsGet tree leaf) = key.ftsSecret index tree leaf)
    (hots : ∀ lay tree leaf chainIdx,
      evalWithAnswerFn f (otsGet lay tree leaf chainIdx) = key.otsSecret lay tree leaf chainIdx)
    (topGet : Nat → Nat → OracleComp HashSpec Digest) (htop : TopAgrees f key topGet)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (signFrom key.parameter index ftsGet otsGet topGet randomness leaves) =
      signatureValue f key randomness index leaves := by
  have hforest := eval_buildFtsTree_open f key.parameter index (ftsGet porsTree) leaves
  have htable : (fun (_ : FtsTree) leaf => evalWithAnswerFn f (ftsGet porsTree leaf)) = key.ftsSecret index := by
    funext tree leaf
    rw [Subsingleton.elim tree porsTree]
    exact hfts porsTree leaf
  rw [htable] at hforest
  unfold signFrom
  rw [evalWithAnswerFn_bind]
  revert hforest
  generalize evalWithAnswerFn f (buildFtsTree key.parameter index (ftsGet porsTree)) = built
  rcases built with ⟨secrets, table⟩
  rintro ⟨hopen, hkey⟩
  simp only at hopen hkey
  have hlayers := eval_signLayers f key index otsGet hots topGet htop numLayers le_rfl
      (table ftsTreeHeight 0) (by
    intro _
    rw [hkey]
    change _ = evalWithAnswerFn f (layerMessage key index bottomLayer)
    rw [layerMessage_bottomLayer_eq])
  simp only [evalWithAnswerFn_bind]
  unfold signatureValue
  rw [sequenceFin_option_eq]
  revert hlayers
  cases evalWithAnswerFn f (signLayers key.parameter index otsGet topGet numLayers (table ftsTreeHeight 0)) with
  | none =>
      rintro ⟨lay, _, hnone⟩
      rw [dif_neg (fun hall => by have := hall lay; rw [hnone] at this; simp at this)]
      rfl
  | some parts =>
      intro hparts
      have hall : ∀ lay, (evalWithAnswerFn f (signLayer key index lay)).isSome := fun lay => by
        rw [hparts lay lay.isLt]
        rfl
      rw [dif_pos hall]
      simp only [evalWithAnswerFn_pure, Option.map_some, Option.some.injEq]
      rw [hopen]
      congr 1
      funext lay
      rw [LayerOutput.toSignature_eq]
      congr 1
      simp only [hparts lay lay.isLt, Option.get_some]
theorem eval_signAfterDigest (key : SecretKey) (htop : KeyTopHonest f key) (randomness : Randomness)
    (index : Index) (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signatureValue f key randomness index leaves := by
  rw [signAfterDigest_eq_signFrom]
  exact eval_signFrom f key index _ _ (fun _ _ => rfl) (fun _ _ _ _ => rfl) _ htop randomness leaves
def TopRegionEq {m : Type → Type} (topNode topNode' : Nat → Nat → m Digest) : Prop :=
  ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
    topNode level nodeIdx = topNode' level nodeIdx
theorem signTopLayer_congr_top {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → m Digest) (topNode topNode' : Nat → Nat → m Digest)
    (htop : TopRegionEq topNode topNode') (message : Digest) :
    signTopLayer parameter index secret topNode message = signTopLayer parameter index secret topNode' message := by
  have hpath : (fun level : Fin maxLayerHeight =>
      topNode level.val (Nat.xor ((leafIndexAt index topLayer).val / 2 ^ level.val) 1)) =
      (fun level : Fin maxLayerHeight =>
        topNode' level.val (Nat.xor ((leafIndexAt index topLayer).val / 2 ^ level.val) 1)) :=
    funext fun level => htop _ level.isLt _ (xor_div_lt (leafIndexAt_lt index topLayer) level.isLt)
  simp only [signTopLayer, hpath]
theorem signLayers_congr_top {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) (topNode topNode' : Nat → Nat → m Digest)
    (htop : TopRegionEq topNode topNode') (remaining : Nat) (message : Digest) :
    signLayers parameter index secret topNode remaining message =
      signLayers parameter index secret topNode' remaining message := by
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
      rw [signLayers, signLayers]
      split
      · split
        · rw [signTopLayer_congr_top parameter index _ topNode topNode' htop]
        · simp only [ih]
      · rfl
theorem signAfterDigest_congr_top (key key' : SecretKey) (hparameter : key.parameter = key'.parameter)
    (hots : key.otsSecret = key'.otsSecret) (hfts : key.ftsSecret = key'.ftsSecret)
    (htop : TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (key.top level nodeIdx))
      (fun level nodeIdx => pure (key'.top level nodeIdx)))
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) =
      signAfterDigest key' randomness index leaves := by
  rw [signAfterDigest_eq_signFrom, signAfterDigest_eq_signFrom, ← hparameter, ← hots, ← hfts]
  unfold signFrom
  simp only [signLayers_congr_top key.parameter index _ _ _ htop]
end SphincsSecurity.Concrete
end
end
-- ==== merged from SphincsSecurity_Proof_Hypertree_RootCache ====
section

namespace SphincsSecurity
open OracleComp OracleSpec
def QueriesAtPositions {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec alpha) : Prop :=
  ∀ input, input ∈ queriedInputs f oa →
    ∃ p : Position, ∃ payload : HashInput,
      input = tweakableHashInput parameter p.domain payload
theorem QueriesAtPositions.pure {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (value : alpha) :
    QueriesAtPositions parameter f (pure value) := by
  simp [QueriesAtPositions]
theorem QueriesAtPositions.bind {alpha beta : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta}
    (hleft : QueriesAtPositions parameter f oa)
    (hright : QueriesAtPositions parameter f (next (evalWithAnswerFn f oa))) :
    QueriesAtPositions parameter f (oa >>= next) := by
  intro input hinput
  rw [queriedInputs_bind] at hinput
  rcases List.mem_append.mp hinput with hinput | hinput
  · exact hleft input hinput
  · exact hright input hinput
theorem QueriesAtPositions.tweakableHash (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (p : Position) (payload : HashInput) :
    QueriesAtPositions parameter f
      (Concrete.tweakableHash parameter p.domain payload) := by
  intro input hinput
  simp only [queriedInputs_tweakableHash, List.mem_singleton] at hinput
  subst input
  exact ⟨p, payload, rfl⟩
namespace Concrete
theorem queriesAtPositions_sequenceFin {alpha : Type} {n : Nat}
    (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomputation : ∀ index, QueriesAtPositions parameter f (computation index)) :
    QueriesAtPositions parameter f (sequenceFin computation) := by
  induction n with
  | zero => exact QueriesAtPositions.pure parameter f _
  | succ n ih =>
      rw [sequenceFin]
      apply QueriesAtPositions.bind (hcomputation 0)
      apply QueriesAtPositions.bind
      · exact ih (fun index : Fin n => computation index.succ)
          (fun index => hcomputation index.succ)
      · exact QueriesAtPositions.pure parameter f _
theorem queriesAtPositions_chainWalk (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) :
    QueriesAtPositions parameter f
      (chainWalk parameter lay tree leafIdx chainIdx start steps value) := by
  induction steps with
  | zero => exact QueriesAtPositions.pure parameter f value
  | succ steps ih =>
      rw [chainWalk]
      apply QueriesAtPositions.bind ih
      split_ifs with hstep
      · exact QueriesAtPositions.tweakableHash parameter f
          (.chain lay tree leafIdx chainIdx ⟨start + steps, hstep⟩) _
      · exact QueriesAtPositions.pure parameter f _
theorem queriesAtPositions_oneTimePublicKey (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) :
    QueriesAtPositions parameter f
      (oneTimePublicKey parameter lay tree leafIdx secret) := by
  apply queriesAtPositions_sequenceFin
  intro chainIdx
  exact queriesAtPositions_chainWalk parameter f lay tree leafIdx chainIdx 0
    (chainLength - 1) (secret chainIdx)
def RootTreeRange (level nodeIdx : Nat) : Prop :=
  2 ^ level * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight
private theorem RootTreeRange.index_lt {level nodeIdx : Nat}
    (h : RootTreeRange level nodeIdx) : nodeIdx < 2 ^ maxLayerHeight := by
  have hpow : 1 ≤ 2 ^ level := one_le_pow₀ (by omega)
  simp only [RootTreeRange] at h
  nlinarith
private theorem RootTreeRange.left {level nodeIdx : Nat}
    (h : RootTreeRange (level + 1) nodeIdx) : RootTreeRange level (2 * nodeIdx) := by
  simp only [RootTreeRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]
private theorem RootTreeRange.right {level nodeIdx : Nat}
    (h : RootTreeRange (level + 1) nodeIdx) : RootTreeRange level (2 * nodeIdx + 1) := by
  simp only [RootTreeRange, pow_succ] at h ⊢
  nlinarith [Nat.zero_le (2 ^ level), Nat.zero_le nodeIdx]
theorem queriesAtPositions_treeNode (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight) (hrange : RootTreeRange level nodeIdx) :
    QueriesAtPositions parameter f (treeNode parameter lay tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq]
      apply QueriesAtPositions.bind
      · exact queriesAtPositions_oneTimePublicKey parameter f lay tree (leafOfNat nodeIdx)
          (secret (leafOfNat nodeIdx))
      · exact QueriesAtPositions.tweakableHash parameter f
          (.leaf lay tree (leafOfNat nodeIdx)) _
  | succ level ih =>
      rw [treeNode_succ_eq]
      apply QueriesAtPositions.bind
      · exact ih (2 * nodeIdx) (by omega) (RootTreeRange.left hrange)
      apply QueriesAtPositions.bind
      · exact ih (2 * nodeIdx + 1) (by omega) (RootTreeRange.right hrange)
      · exact QueriesAtPositions.tweakableHash parameter f
          (.node lay tree ⟨level, by omega⟩ ⟨nodeIdx, hrange.index_lt⟩) _
theorem queriesAtPositions_treeRoot (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) :
    QueriesAtPositions parameter f (treeRoot parameter lay tree secret) := by
  apply queriesAtPositions_treeNode parameter f lay tree secret (layerHeight lay) 0
  · exact layerHeight_le lay
  · simp only [RootTreeRange, zero_add, mul_one]
    exact pow_le_pow_right' (by omega) (layerHeight_le lay)
theorem messageInput_not_mem_queriedInputs_treeRoot (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (payload : HashInput) :
    tweakableHashInput parameter .message payload ∉
      queriedInputs f (treeRoot parameter lay tree secret) := by
  intro hmem
  obtain ⟨p, structuralPayload, heq⟩ :=
    queriesAtPositions_treeRoot parameter f lay tree secret _ hmem
  have hdomain := (tweakableHashInput_injective parameter
    (show HashDomain.message.InRange from trivial) p.domain_inRange heq).1
  cases p <;> simp [Position.domain] at hdomain
theorem treeRoot_cache_message_none (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (root : Digest) (rootCache : QueryCache HashSpec)
    (hroot : (root, rootCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (treeRoot parameter lay tree secret)).run ∅))
    (payload : HashInput) :
    rootCache (tweakableHashInput parameter .message payload) = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) rootCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (treeRoot parameter lay tree secret) ∅ root rootCache hroot f hf
  · simp
  · exact messageInput_not_mem_queriedInputs_treeRoot parameter f lay tree secret payload
end Concrete
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Scheme_NoMessage ====
section

namespace SphincsSecurity
open OracleComp OracleSpec
def AvoidsMessageQueries {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec alpha) : Prop :=
  ∀ payload, tweakableHashInput parameter .message payload ∉ queriedInputs f oa
theorem AvoidsMessageQueries.pure {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (value : alpha) :
    AvoidsMessageQueries parameter f (pure value) := by
  simp [AvoidsMessageQueries]
theorem AvoidsMessageQueries.bind {alpha beta : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta}
    (hleft : AvoidsMessageQueries parameter f oa)
    (hright : AvoidsMessageQueries parameter f (next (evalWithAnswerFn f oa))) :
    AvoidsMessageQueries parameter f (oa >>= next) := by
  intro payload hmem
  rw [queriedInputs_bind] at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft payload hmem
  · exact hright payload hmem
theorem AvoidsMessageQueries.tweakableHash (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (domain : HashDomain) (hdomain : domain ≠ .message)
    (payload : HashInput) :
    AvoidsMessageQueries parameter f
      (Concrete.tweakableHash parameter domain payload) := by
  intro messagePayload hmem
  simp only [queriedInputs_tweakableHash, List.mem_singleton] at hmem
  exact tweakableHashInput_ne_message parameter domain hdomain payload messagePayload hmem.symm
theorem QueriesAtPositions.avoidsMessage {alpha : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    (h : QueriesAtPositions parameter f oa) : AvoidsMessageQueries parameter f oa := by
  intro payload hmem
  obtain ⟨p, structuralPayload, heq⟩ := h _ hmem
  exact tweakableHashInput_ne_message parameter p.domain (by cases p <;> simp [Position.domain])
    structuralPayload payload heq.symm
namespace Concrete
theorem avoidsMessage_sequenceFin {alpha : Type} {n : Nat}
    (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomputation : ∀ index, AvoidsMessageQueries parameter f (computation index)) :
    AvoidsMessageQueries parameter f (sequenceFin computation) := by
  induction n with
  | zero => exact AvoidsMessageQueries.pure parameter f _
  | succ n ih =>
      rw [sequenceFin]
      apply AvoidsMessageQueries.bind (hcomputation 0)
      apply AvoidsMessageQueries.bind
      · exact ih (fun index : Fin n => computation index.succ)
          (fun index => hcomputation index.succ)
      · exact AvoidsMessageQueries.pure parameter f _
theorem avoidsMessage_chainWalk (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (value : Digest) :
    AvoidsMessageQueries parameter f
      (chainWalk parameter lay tree leafIdx chainIdx start steps value) :=
  (queriesAtPositions_chainWalk parameter f lay tree leafIdx chainIdx start steps value).avoidsMessage
theorem avoidsMessage_oneTimePublicKey (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) :
    AvoidsMessageQueries parameter f
      (oneTimePublicKey parameter lay tree leafIdx secret) :=
  (queriesAtPositions_oneTimePublicKey parameter f lay tree leafIdx secret).avoidsMessage
theorem avoidsMessage_treeNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (level nodeIdx : Nat) :
    AvoidsMessageQueries parameter f (treeNode parameter lay tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq]
      apply AvoidsMessageQueries.bind
      · exact avoidsMessage_oneTimePublicKey parameter f lay tree (leafOfNat nodeIdx)
          (secret (leafOfNat nodeIdx))
      · exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _
  | succ level ih =>
      rw [treeNode_succ_eq]
      apply AvoidsMessageQueries.bind (ih (2 * nodeIdx))
      apply AvoidsMessageQueries.bind (ih (2 * nodeIdx + 1))
      exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _
theorem avoidsMessage_treeRoot (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) :
    AvoidsMessageQueries parameter f (treeRoot parameter lay tree secret) := by
  exact avoidsMessage_treeNode parameter f lay tree secret (layerHeight lay) 0
theorem avoidsMessage_treePath (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (leafIdx : LeafIndex) :
    AvoidsMessageQueries parameter f (treePath parameter lay tree secret leafIdx) := by
  apply avoidsMessage_sequenceFin
  intro level
  split
  · exact avoidsMessage_treeNode parameter f lay tree secret _ _
  · exact AvoidsMessageQueries.pure parameter f _
theorem avoidsMessage_encode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    AvoidsMessageQueries parameter f (encodeAttempt parameter lay tree leafIdx message counter) := by
  simp only [encodeAttempt]
  apply AvoidsMessageQueries.bind
  · exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _
  · exact AvoidsMessageQueries.pure parameter f _
theorem avoidsMessage_otsSignFrom (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat) :
    AvoidsMessageQueries parameter f
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact AvoidsMessageQueries.pure parameter f _
  | succ attempts ih =>
      rw [otsSignFrom]
      apply AvoidsMessageQueries.bind
      · exact avoidsMessage_encode parameter f lay tree leafIdx message _
      split
      · apply AvoidsMessageQueries.bind
        · apply avoidsMessage_sequenceFin
          intro chainIdx
          exact avoidsMessage_chainWalk parameter f lay tree leafIdx chainIdx 0 _ _
        · exact AvoidsMessageQueries.pure parameter f _
      · exact ih (counter + 1)
theorem avoidsMessage_otsSign (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    AvoidsMessageQueries parameter f
      (otsSign parameter lay tree leafIdx secret message) := by
  exact avoidsMessage_otsSignFrom parameter f lay tree leafIdx secret message
    encodingAttemptLimit 0
theorem avoidsMessage_ftsLeafHash (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (leafIdx : Nat) (secret : Digest) :
    AvoidsMessageQueries parameter f (ftsLeafHash parameter index tree leafIdx secret) := by
  exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _
theorem avoidsMessage_ftsNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest)
    (level nodeIdx : Nat) :
    AvoidsMessageQueries parameter f (ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact avoidsMessage_ftsLeafHash parameter f index tree _ _
  | succ level ih =>
      rw [ftsNode_succ_eq]
      apply AvoidsMessageQueries.bind (ih (2 * nodeIdx))
      apply AvoidsMessageQueries.bind (ih (2 * nodeIdx + 1))
      exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _
theorem avoidsMessage_ftsKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    AvoidsMessageQueries parameter f (ftsKey parameter index secret) := by
  rw [ftsKey]
  exact avoidsMessage_ftsNode parameter f index porsTree (secret porsTree) ftsTreeHeight 0
theorem avoidsMessage_ftsOpen (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    AvoidsMessageQueries parameter f (ftsOpen parameter index leaves secret) := by
  unfold ftsOpen
  exact AvoidsMessageQueries.bind (avoidsMessage_sequenceFin _ _ _ fun _ =>
    AvoidsMessageQueries.bind (avoidsMessage_sequenceFin _ _ _ fun _ =>
      avoidsMessage_ftsNode parameter f index porsTree (secret porsTree) _ _)
      (AvoidsMessageQueries.pure _ _ _)) (AvoidsMessageQueries.pure _ _ _)
theorem avoidsMessage_layerMessage (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (index : Index) (lay : Layer) :
    AvoidsMessageQueries secretKey.parameter f (layerMessage secretKey index lay) := by
  rw [layerMessage]
  split
  · exact avoidsMessage_treeRoot secretKey.parameter f _ _ _
  · exact avoidsMessage_ftsKey secretKey.parameter f index (secretKey.ftsSecret index)
theorem avoidsMessage_signLayer (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (index : Index) (lay : Layer) :
    AvoidsMessageQueries secretKey.parameter f (signLayer secretKey index lay) := by
  rw [signLayer]
  apply AvoidsMessageQueries.bind
  · exact avoidsMessage_layerMessage f secretKey index lay
  apply AvoidsMessageQueries.bind
  · exact avoidsMessage_otsSign secretKey.parameter f lay (treeIndexAt index lay)
      (leafIndexAt index lay) _ _
  split
  · exact AvoidsMessageQueries.pure secretKey.parameter f _
  · apply AvoidsMessageQueries.bind
    · exact avoidsMessage_treePath secretKey.parameter f lay (treeIndexAt index lay) _
        (leafIndexAt index lay)
    · exact AvoidsMessageQueries.pure secretKey.parameter f _
theorem AvoidsMessageQueries.bind_all {alpha beta : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta}
    (hleft : AvoidsMessageQueries parameter f oa)
    (hright : ∀ value, AvoidsMessageQueries parameter f (next value)) :
    AvoidsMessageQueries parameter f (oa >>= next) :=
  AvoidsMessageQueries.bind hleft (hright _)
theorem avoidsMessage_buildLevel (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (hashNode : Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ nodeIdx left right, AvoidsMessageQueries parameter f (hashNode nodeIdx left right))
    (width : Nat) (below : Nat → Digest) :
    AvoidsMessageQueries parameter f (buildLevel hashNode width below) := by
  unfold buildLevel
  exact AvoidsMessageQueries.bind_all (avoidsMessage_sequenceFin _ _ _ fun _ => hhash _ _ _)
    fun _ => AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_buildLevels (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ level nodeIdx left right,
      AvoidsMessageQueries parameter f (hashNode level nodeIdx left right))
    (height : Nat) (leaves : Nat → Digest) (levels : Nat) :
    AvoidsMessageQueries parameter f (buildLevels hashNode height leaves levels) := by
  induction levels with
  | zero => exact AvoidsMessageQueries.pure _ _ _
  | succ levels ih =>
      rw [buildLevels]
      refine AvoidsMessageQueries.bind_all ih fun table => ?_
      exact AvoidsMessageQueries.bind_all
        (avoidsMessage_buildLevel _ _ _ (hhash (levels + 1)) _ _)
        fun _ => AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_buildChain (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (secret : OracleComp HashSpec Digest) (hsecret : AvoidsMessageQueries parameter f secret)
    (digit : Nat) :
    AvoidsMessageQueries parameter f (buildChain parameter lay tree leafIdx chainIdx secret digit) := by
  unfold buildChain
  refine AvoidsMessageQueries.bind_all hsecret fun _ => ?_
  refine AvoidsMessageQueries.bind_all (avoidsMessage_chainWalk _ _ _ _ _ _ _ _ _) fun _ => ?_
  exact AvoidsMessageQueries.bind_all (avoidsMessage_chainWalk _ _ _ _ _ _ _ _ _)
    fun _ => AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_buildLeaf (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → OracleComp HashSpec Digest)
    (hsecret : ∀ chainIdx, AvoidsMessageQueries parameter f (secret chainIdx)) (digits : Encoding) :
    AvoidsMessageQueries parameter f (buildLeaf parameter lay tree leafIdx secret digits) := by
  unfold buildLeaf
  refine AvoidsMessageQueries.bind_all (avoidsMessage_sequenceFin _ _ _ fun chainIdx =>
    avoidsMessage_buildChain _ _ _ _ _ _ _ (hsecret chainIdx) _) fun _ => ?_
  exact AvoidsMessageQueries.bind_all (AvoidsMessageQueries.tweakableHash _ _ _ (by simp) _)
    fun _ => AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_buildLayerTree (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hsecret : ∀ leafIdx chainIdx, AvoidsMessageQueries parameter f (secret leafIdx chainIdx))
    (leafIdx : LeafIndex) (digits : Encoding) :
    AvoidsMessageQueries parameter f (buildLayerTree parameter lay tree secret leafIdx digits) := by
  unfold buildLayerTree
  refine AvoidsMessageQueries.bind_all (avoidsMessage_sequenceFin _ _ _ fun _ =>
    avoidsMessage_buildLeaf _ _ _ _ _ _ (hsecret _) _) fun _ => ?_
  exact AvoidsMessageQueries.bind_all (avoidsMessage_buildLevels _ _ _
    (fun _ _ _ _ => AvoidsMessageQueries.tweakableHash _ _ _ (by simp) _) _ _ _)
    fun _ => AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_buildFtsTree (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsLeaf → OracleComp HashSpec Digest)
    (hsecret : ∀ leafIdx, AvoidsMessageQueries parameter f (secret leafIdx)) :
    AvoidsMessageQueries parameter f (buildFtsTree parameter index secret) := by
  unfold buildFtsTree
  refine AvoidsMessageQueries.bind_all (avoidsMessage_sequenceFin _ _ _ fun leaf =>
    AvoidsMessageQueries.bind_all (hsecret leaf) fun _ =>
      AvoidsMessageQueries.bind_all (avoidsMessage_ftsLeafHash _ _ _ _ _ _)
        fun _ => AvoidsMessageQueries.pure _ _ _) fun _ => ?_
  exact AvoidsMessageQueries.bind_all (avoidsMessage_buildLevels _ _ _
    (fun _ _ _ _ => AvoidsMessageQueries.tweakableHash _ _ _ (by simp) _) _ _ _)
    fun _ => AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_encodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) (attempts counter : Nat) :
    AvoidsMessageQueries parameter f (encodingSearch parameter lay tree leafIdx message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact AvoidsMessageQueries.pure _ _ _
  | succ attempts ih =>
      rw [encodingSearch]
      refine AvoidsMessageQueries.bind_all (by
        rw [encode_eq]; exact avoidsMessage_encode _ _ _ _ _ _ _) fun result => ?_
      cases result with
      | none => exact ih _
      | some _ => exact AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_buildLayerTable (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hsecret : ∀ leafIdx chainIdx, AvoidsMessageQueries parameter f (secret leafIdx chainIdx))
    (leafIdx : LeafIndex) (digits : Encoding) :
    AvoidsMessageQueries parameter f (buildLayerTable parameter lay tree secret leafIdx digits) := by
  unfold buildLayerTable
  refine AvoidsMessageQueries.bind_all (avoidsMessage_sequenceFin _ _ _ fun _ =>
    avoidsMessage_buildLeaf _ _ _ _ _ _ (hsecret _) _) fun _ => ?_
  exact AvoidsMessageQueries.bind_all (avoidsMessage_buildLevels _ _ _
    (fun _ _ _ _ => AvoidsMessageQueries.tweakableHash _ _ _ (by simp) _) _ _ _)
    fun _ => AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_signTopLayer (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hsecret : ∀ leafIdx chainIdx, AvoidsMessageQueries parameter f (secret leafIdx chainIdx))
    (topNode : Nat → Nat → OracleComp HashSpec Digest)
    (htop : ∀ level nodeIdx, AvoidsMessageQueries parameter f (topNode level nodeIdx))
    (message : Digest) :
    AvoidsMessageQueries parameter f (signTopLayer parameter index secret topNode message) := by
  unfold signTopLayer
  refine AvoidsMessageQueries.bind_all (avoidsMessage_encodingSearch _ _ _ _ _ _ _ _)
    fun result => ?_
  rcases result with _ | ⟨counter, encoding⟩
  · exact AvoidsMessageQueries.pure _ _ _
  refine AvoidsMessageQueries.bind_all (avoidsMessage_sequenceFin _ _ _ fun _ =>
    AvoidsMessageQueries.bind_all (hsecret _ _) fun _ =>
      avoidsMessage_chainWalk _ _ _ _ _ _ _ _ _) fun _ => ?_
  exact AvoidsMessageQueries.bind_all (avoidsMessage_sequenceFin _ _ _ fun _ => htop _ _)
    fun _ => AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_signLayers (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (hsecret : ∀ lay tree leafIdx chainIdx,
      AvoidsMessageQueries parameter f (secret lay tree leafIdx chainIdx))
    (topNode : Nat → Nat → OracleComp HashSpec Digest)
    (htop : ∀ level nodeIdx, AvoidsMessageQueries parameter f (topNode level nodeIdx))
    (remaining : Nat) (message : Digest) :
    AvoidsMessageQueries parameter f (signLayers parameter index secret topNode remaining message) := by
  induction remaining generalizing message with
  | zero => exact AvoidsMessageQueries.pure _ _ _
  | succ remaining ih =>
      rw [signLayers]
      split
      · split
        · refine AvoidsMessageQueries.bind_all (avoidsMessage_signTopLayer _ _ _ _
            (hsecret _ _) _ htop _) fun result => ?_
          rcases result with _ | output <;> exact AvoidsMessageQueries.pure _ _ _
        refine AvoidsMessageQueries.bind_all (avoidsMessage_encodingSearch _ _ _ _ _ _ _ _)
          fun result => ?_
        rcases result with _ | ⟨counter, encoding⟩
        · exact AvoidsMessageQueries.pure _ _ _
        refine AvoidsMessageQueries.bind_all (avoidsMessage_buildLayerTree _ _ _ _ _
          (hsecret _ _) _ _) fun built => ?_
        rcases built with ⟨values, path, root⟩
        refine AvoidsMessageQueries.bind_all (ih root) fun rest => ?_
        rcases rest with _ | rest <;> exact AvoidsMessageQueries.pure _ _ _
      · exact AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_signFrom (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (ftsGet : FtsTree → FtsLeaf → OracleComp HashSpec Digest)
    (otsGet : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest)
    (topGet : Nat → Nat → OracleComp HashSpec Digest)
    (hfts : ∀ tree leafIdx, AvoidsMessageQueries parameter f (ftsGet tree leafIdx))
    (hots : ∀ lay tree leafIdx chainIdx, AvoidsMessageQueries parameter f (otsGet lay tree leafIdx chainIdx))
    (htop : ∀ level nodeIdx, AvoidsMessageQueries parameter f (topGet level nodeIdx))
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    AvoidsMessageQueries parameter f (signFrom parameter index ftsGet otsGet topGet randomness leaves) := by
  unfold signFrom
  refine AvoidsMessageQueries.bind_all (avoidsMessage_buildFtsTree _ _ _ _ (hfts porsTree)) fun built => ?_
  rcases built with ⟨secrets, table⟩
  refine AvoidsMessageQueries.bind_all (avoidsMessage_signLayers _ _ _ _ hots _ htop _ _)
    fun parts => ?_
  rcases parts with _ | parts <;> exact AvoidsMessageQueries.pure _ _ _
theorem avoidsMessage_signAfterDigest (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    AvoidsMessageQueries secretKey.parameter f
      (signAfterDigest secretKey randomness index leaves) := by
  rw [signAfterDigest]
  exact avoidsMessage_signFrom _ _ _ _ _ _ (fun _ _ => AvoidsMessageQueries.pure _ _ _)
    (fun _ _ _ _ => AvoidsMessageQueries.pure _ _ _) (fun _ _ => AvoidsMessageQueries.pure _ _ _)
    randomness leaves
theorem avoidsMessage_keygenRoot (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    AvoidsMessageQueries parameter f (keygenRoot parameter secret) := by
  unfold keygenRoot
  refine AvoidsMessageQueries.bind_all (avoidsMessage_buildLayerTree _ _ _ _ _
    (fun _ _ => AvoidsMessageQueries.pure _ _ _) _ _) fun built => ?_
  rcases built with ⟨values, path, root⟩
  exact AvoidsMessageQueries.pure _ _ _
theorem keygenRoot_cache_message_none (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest)
    (root : Digest) (rootCache : QueryCache HashSpec)
    (hroot : (root, rootCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (keygenRoot parameter secret : OracleComp HashSpec Digest)).run ∅))
    (payload : HashInput) :
    rootCache (tweakableHashInput parameter .message payload) = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) rootCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (keygenRoot parameter secret : OracleComp HashSpec Digest) ∅ root rootCache hroot f hf
  · simp
  · exact avoidsMessage_keygenRoot parameter f secret payload
theorem avoidsMessage_keygenTable (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    AvoidsMessageQueries parameter f (keygenTable parameter secret) := by
  unfold keygenTable
  refine AvoidsMessageQueries.bind_all (avoidsMessage_buildLayerTable _ _ _ _ _
    (fun _ _ => AvoidsMessageQueries.pure _ _ _) _ _) fun built => ?_
  rcases built with ⟨leaves, table⟩
  exact AvoidsMessageQueries.pure _ _ _
theorem keygenTable_cache_message_none (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest)
    (top : Nat → Nat → Digest) (rootCache : QueryCache HashSpec)
    (hroot : (top, rootCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (keygenTable parameter secret : OracleComp HashSpec (Nat → Nat → Digest))).run ∅))
    (payload : HashInput) :
    rootCache (tweakableHashInput parameter .message payload) = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) rootCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (keygenTable parameter secret : OracleComp HashSpec (Nat → Nat → Digest)) ∅ top rootCache hroot f hf
  · simp
  · exact avoidsMessage_keygenTable parameter f secret payload
theorem sign_eq_digestLoop_afterDigest (secretKey : SecretKey) (message : Message) :
    sign secretKey message = (do
      match ← signDigestLoop digestAttemptLimit secretKey message with
      | none => return none
      | some (randomness, index, leaves) =>
          liftM (signAfterDigest secretKey randomness index leaves :
            OracleComp HashSpec (Option Signature))) := sign_eq secretKey message
end Concrete
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_MessagePrehit ====
section

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
noncomputable local instance instSampleableTypeRandomness : SampleableType Randomness :=
  Concrete.randomnessSampleableType
def cachedMessageInputSet (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) :
    Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cache.toSet | ∃ randomness,
    entry.1 = tweakableHashInput parameter .message
      (Concrete.messageDigestPayload root message randomness)}
noncomputable def cachedMessageEntryCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (root : Digest) (message : Message) : ℝ≥0∞ :=
  (((cachedMessageInputSet cache parameter root message).encard : ENat) : ℝ≥0∞)
theorem card_randomness : Fintype.card Randomness = 2 ^ randomnessBits := by
  simp [digestBits, randomnessBits]
noncomputable def Concrete.signDigestLoopContinuation
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (randomness : Randomness)
    (result : Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec) :
    ProbComp (Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) :=
  match result.1 with
  | some (index, leaves) => pure (some (randomness, index, leaves), result.2)
  | none => (simulateQ romImpl
      (Concrete.signDigestLoop attempts secretKey message)).run result.2
attribute [irreducible] Concrete.signDigestLoopContinuation
theorem Concrete.signDigestLoop_run_succ_eq
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.signDigestLoop (attempts + 1) secretKey message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))).run cache >>=
          Concrete.signDigestLoopContinuation attempts secretKey message randomness) := by
  rw [Concrete.signDigestLoop, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ romImpl (liftM Concrete.sampleRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$> Concrete.sampleRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.sampleRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.sampleRandomness cache
  rw [hsampleRun, Concrete.sampleRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, StateT.run_bind]
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) =
        simulateQ randomOracle
          (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.signAttempt secretKey message randomness :
        OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result with
  | none => simp [Concrete.signDigestLoopContinuation]
  | some selected =>
      rcases selected with ⟨index, leaves⟩
      simp [Concrete.signDigestLoopContinuation]
theorem Concrete.signAfterDigest_some_randomness (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (signature : Signature)
    (heval : evalWithAnswerFn f
      (Concrete.signAfterDigest secretKey randomness index leaves) = some signature) :
    signature.randomness = randomness := by
  rw [Concrete.signAfterDigest_eq_signFrom, signFrom] at heval
  simp only [evalWithAnswerFn_bind] at heval
  split at heval
  · simp only [evalWithAnswerFn_pure, Option.some.injEq] at heval
    subst signature
    rfl
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at heval
theorem Concrete.signAfterDigest_support_some_randomness
    (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (beforeCache afterCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (Concrete.signAfterDigest secretKey randomness index leaves)).run beforeCache)) :
    signature.randomness = randomness := by
  obtain ⟨_, answerFn, _, heval⟩ :=
    exists_answerFn_agrees_final_of_mem_support
      (Concrete.signAfterDigest secretKey randomness index leaves)
      beforeCache (some signature) afterCache hmem
  exact Concrete.signAfterDigest_some_randomness answerFn secretKey randomness index leaves
    signature heval
end SphincsSecurity
end
-- ==== merged from SphincsSecurity_Proof_Fts_SignerDigestSource ====
section

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
@[simp] theorem queriedInputs_signAttempt (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    queriedInputs f (signAttempt secretKey message randomness) =
      [tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)] := by
  rw [signAttempt, queriedInputs_bind]
  change queriedInputs f
      (liftM (HashSpec.query (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness))) >>=
          fun answer => pure (truncateMessageDigest answer)) ++ _ = _
  rw [queriedInputs_query_bind, queriedInputs_pure]
  split <;> simp
theorem signAttempt_cache_other_none (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (beforeCache afterCache : QueryCache HashSpec)
    (attempt : Option (Index × (IndexGroup → FtsLeaf)))
    (hmem : (attempt, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run beforeCache))
    (target : HashInput) (hbefore : beforeCache target = none)
    (hne : target ≠ tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) :
    afterCache target = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) afterCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (signAttempt secretKey message randomness) beforeCache attempt afterCache hmem f hf target hbefore
  simp [hne]
theorem signAfterDigest_cache_message_none (secretKey : SecretKey)
    (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (beforeCache afterCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAfterDigest secretKey randomness index leaves)).run beforeCache))
    (payload : HashInput) (hbefore : beforeCache
      (tweakableHashInput secretKey.parameter .message payload) = none) :
    afterCache (tweakableHashInput secretKey.parameter .message payload) = none := by
  obtain ⟨answerFn, hagree⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) afterCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (signAfterDigest secretKey randomness index leaves) beforeCache result afterCache
      hmem answerFn hagree _ hbefore
  exact avoidsMessage_signAfterDigest answerFn secretKey randomness index leaves payload
end SphincsSecurity.Concrete
end
-- ==== merged from SphincsSecurity_Proof_Fts_FewTimeLoop ====
section

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
set_option maxRecDepth 100000
theorem signAttempt_result_of_cached (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (beforeCache afterCache : QueryCache HashSpec)
    (attempt : Option (Index × (IndexGroup → FtsLeaf))) (output : HashOutput)
    (hcached : afterCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output)
    (hmem : (attempt, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
        (signAttempt secretKey message randomness)).run beforeCache)) :
    attempt = signAttemptResultOfOutput output := by
  obtain ⟨_, f, hf, heval⟩ := exists_answerFn_agrees_final_of_mem_support
    (signAttempt secretKey message randomness) beforeCache attempt afterCache hmem
  have hfinput : f (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = output :=
    hf hcached
  simp only [signAttempt, messageDigest, oracleHash, evalWithAnswerFn_bind,
    evalWithAnswerFn_query, hfinput] at heval
  simp only [signAttemptResultOfOutput]
  by_cases hadmissible : Admissible (truncateMessageDigest output)
  · simpa only [hadmissible, if_true, evalWithAnswerFn_pure] using heval.symm
  · simpa only [hadmissible, if_false, evalWithAnswerFn_pure] using heval.symm
end SphincsSecurity.Concrete
end
