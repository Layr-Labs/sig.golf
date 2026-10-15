import SigGolfCandidate.ClaudeWCT.Numerics.N600PricePart2

set_option Elab.async false



namespace SigGolfCandidate.Research.SharedFtsModel
attribute [local irreducible] Finset.univ
open scoped BigOperators
open Finset ClaudeWCT.WCT9 SharedPathPacking
open ClaudeWCT.Numerics.SharedFtsCount
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
abbrev Coordinate := Fin 32 × Fin 563
abbrev «Word» := (Fin 4 → Coordinate) × (Fin 5 → Coordinate)
def coordWeight (isA : Bool) (w : Coordinate) : Nat :=
  routineCost w.2 - 75 + (if isA then SharedForest.aCorrection w.1.val else SharedForest.bCorrection w.1.val)
def weight (w : «Word») : Nat :=
  (∑ i, coordWeight true (w.1 i)) + ∑ i, coordWeight false (w.2 i)

theorem rank_list : List.ofFn routineCost = routineCosts := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, routineCosts_length]
  · intro k hk hk'
    rw [List.getElem_ofFn]
    rfl

theorem weighted_ofFn_fold {n : Nat} (v : Fin n → Nat) (bits base : Nat) :
    (∑ i, (2^bits) ^ (v i - base)) =
      (List.ofFn v).foldl (fun s c => s + (1 <<< (bits * (c - base)))) 0 := by
  have hf : ∀ (xs : List Nat) (acc : Nat),
      xs.foldl (fun s c => s + (1 <<< (bits * (c - base)))) acc =
        acc + (xs.map (fun c => (2^bits) ^ (c - base))).sum := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons x xs ih =>
        intro acc
        rw [List.foldl_cons, ih]
        simp only [Nat.shiftLeft_eq, one_mul, ← pow_mul, List.map_cons,
          List.sum_cons, Nat.add_assoc]
  rw [hf, Nat.zero_add, List.map_ofFn, List.sum_ofFn]
  rfl

theorem rank_weight : (∑ r : Fin 563, radix ^ (routineCost r - 75)) = rankPacked := by
  have h := weighted_ofFn_fold routineCost 256 75
  rw [rank_list] at h
  exact h
theorem a_weight_poly (R : Nat) : (∑ c : Fin 32, R ^ SharedForest.aCorrection c.val) =
      4 + 16*R + 5*R^2 + 5*R^3 + R^5 + R^6 := by
  norm_num [Fin.sum_univ_succ, Fin.succ, SharedForest.aCorrection,
    saves, current, block, bitAt, plans, List.range_succ, List.range_zero]
  ring
theorem b_weight_poly (R : Nat) : (∑ c : Fin 32, R ^ SharedForest.bCorrection c.val) =
      4 + 16*R + 5*R^2 + 5*R^3 + R^4 + R^5 := by
  norm_num [Fin.sum_univ_succ, Fin.succ, SharedForest.bCorrection,
    saves, current, block, bitAt, plans, List.range_succ, List.range_zero]
  ring
theorem a_weight : (∑ c : Fin 32, radix ^ SharedForest.aCorrection c.val) = fieldA := a_weight_poly radix
theorem b_weight : (∑ c : Fin 32, radix ^ SharedForest.bCorrection c.val) = fieldBC := b_weight_poly radix

theorem sum_prod_pow {α β : Type} [Fintype α] [Fintype β]
    (R : Nat) (u : α → Nat) (v : β → Nat) :
    (∑ w : α × β, R ^ (v w.2 + u w.1)) = (∑ r, R ^ v r) * ∑ c, R ^ u c := by
  rw [Fintype.sum_prod_type]
  simp only [pow_add, ← Finset.sum_mul]
  rw [← Finset.mul_sum]

theorem coord_weight (isA : Bool) :
    (∑ w : Coordinate, radix ^ coordWeight isA w) = rankPacked * (if isA then fieldA else fieldBC) := by
  have hc : (∑ c : Fin 32, radix ^ (if isA then SharedForest.aCorrection c.val else SharedForest.bCorrection c.val)) =
      (if isA then fieldA else fieldBC) := by
    cases isA
    · exact b_weight
    · exact a_weight
  calc
    _ = (∑ r : Fin 563, radix ^ (routineCost r - 75)) *
        ∑ c : Fin 32, radix ^ (if isA then SharedForest.aCorrection c.val else SharedForest.bCorrection c.val) :=
      sum_prod_pow radix _ _
    _ = _ := congrArg₂ Nat.mul rank_weight hc

theorem weighted_pair {α : Type} [Fintype α]
    (R n m : Nat) (f g : α → Nat) :
    (∑ w : (Fin n → α) × (Fin m → α), R ^ ((∑ i, f (w.1 i)) + ∑ i, g (w.2 i))) =
      (∑ a, R ^ f a)^n * (∑ a, R ^ g a)^m := by
  rw [Fintype.sum_prod_type]
  simp only [pow_add]
  rw [← Finset.sum_mul_sum,
    SigGolfResearch.NonbinaryTop.Counting.weighted_tuples,
    SigGolfResearch.NonbinaryTop.Counting.weighted_tuples]

theorem weighted_words : (∑ w : «Word», radix ^ weight w) = fieldForestPacked := by
  calc
    _ = (∑ c : Coordinate, radix ^ coordWeight true c)^4 *
        (∑ c : Coordinate, radix ^ coordWeight false c)^5 :=
      weighted_pair radix 4 5 _ _
    _ = (rankPacked * fieldA)^4 * (rankPacked * fieldBC)^5 :=
      congrArg₂ (fun x y : Nat => x^4*y^5) (coord_weight true) (coord_weight false)
    _ = fieldForestPacked := rfl

theorem word_card_small : Fintype.card «Word» < radix - 1 := by
  norm_num [«Word», Coordinate, Fintype.card_prod, Fintype.card_fun, radix]

theorem accepted_card : (Finset.univ.filter fun w : «Word» => weight w ≤ 113).card = fieldRetained := by
  rw [SigGolfResearch.Gate6.generic_capped_card weight radix 113
    (by norm_num [radix]) word_card_small, weighted_words]
  rfl

theorem accepted_card_exact :
    (Finset.univ.filter fun w : «Word» => weight w ≤ 113).card * 4^9 = count := by
  rw [accepted_card, field_retained_eq]

end SigGolfCandidate.Research.SharedFtsModel


namespace SigGolfCandidate.Research.SharedFtsModel
open scoped BigOperators
open SigGolfCandidate.T3 ClaudeWCT.WCT9 SharedDigestFields

def group (f : Fin 9 → Coordinate) : «Word» :=
  (fun i => f ⟨2*i.val, by omega⟩,
   fun i => f ⟨min (2*i.val+1) 8, by omega⟩)
def ungroup (w : «Word») (k : Fin 9) : Coordinate :=
  if h : k.val < 8 ∧ k.val % 2 = 0 then w.1 ⟨k.val/2, by omega⟩
  else w.2 ⟨k.val/2, by omega⟩

def groupEquiv : (Fin 9 → Coordinate) ≃ «Word» where
  toFun := group
  invFun := ungroup
  left_inv f := by funext k; fin_cases k <;> rfl
  right_inv w := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl

theorem grouped_weight (f : Fin 9 → Coordinate) :
    (∑ k : Fin 9, coordWeight (SharedForest.firstCoord k.val) (f k)) = weight (group f) := by
  simp only [weight, group, Fin.sum_univ_succ]
  simp only [SharedForest.firstCoord, Fin.val_zero, Fin.val_succ]
  norm_num [Fin.succ]
  omega

def encodeFields (w : «Word») (index : BitVec 31) (gate : Fin 734) : Fields :=
  (fun k => BitVec.ofNat 5 (ungroup w k).1.val,
   fun k => BitVec.ofNat 10 (ungroup w k).2.val,
   index, BitVec.ofNat 14 gate.val)
def decodeFields (f : Fields) : «Word» :=
  group (fun k => (⟨(f.1 k).toNat, (f.1 k).isLt⟩, decodedRank f k))

theorem cost_encode_nat (w : «Word») (index : BitVec 31) (gate : Fin 734) (k : Fin 9) :
    ((encodeFields w index gate).1 k).toNat = (ungroup w k).1.val := by
  simp only [encodeFields, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (ungroup w k).1.isLt

theorem rank_encode_nat (w : «Word») (index : BitVec 31) (gate : Fin 734) (k : Fin 9) :
    ((encodeFields w index gate).2.1 k).toNat = (ungroup w k).2.val := by
  simp only [encodeFields, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h := (ungroup w k).2.isLt
  omega

theorem decodedRank_encode (w : «Word») (index : BitVec 31) (gate : Fin 734) (k : Fin 9) :
    decodedRank (encodeFields w index gate) k = (ungroup w k).2 := by
  apply Fin.ext
  simp only [decodedRank, rank_encode_nat, Nat.mod_eq_of_lt (ungroup w k).2.isLt]

theorem decode_encode (w : «Word») (index : BitVec 31) (gate : Fin 734) :
    decodeFields (encodeFields w index gate) = w := by
  have h : (fun k => (⟨((encodeFields w index gate).1 k).toNat,
      ((encodeFields w index gate).1 k).isLt⟩, decodedRank (encodeFields w index gate) k)) = ungroup w := by
    funext k
    apply Prod.ext
    · apply Fin.ext; exact cost_encode_nat w index gate k
    · exact decodedRank_encode w index gate k
  change group _ = w
  rw [h]
  exact groupEquiv.apply_symm_apply w

theorem cost_encode (w : «Word») (index : BitVec 31) (gate : Fin 734) :
    cost (encodeFields w index gate) = 675 + weight w := by
  have hc : coordinateCost (encodeFields w index gate) = fun k =>
      75 + coordWeight (SharedForest.firstCoord k.val) (ungroup w k) := by
    funext k
    simp only [coordinateCost, decodedRank_encode, cost_encode_nat, coordWeight]
    have h := (routineCost_bounds (ungroup w k).2).1
    omega
  unfold cost
  rw [hc, ← List.ofFn_eq_map, List.sum_ofFn]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, grouped_weight, show group (ungroup w) = w from groupEquiv.apply_symm_apply w]
end SigGolfCandidate.Research.SharedFtsModel


namespace SigGolfCandidate.Research.SharedFtsModel
open scoped BigOperators
open SigGolfCandidate.T3 ClaudeWCT.WCT9 SharedDigestFields
set_option maxHeartbeats 2000000
attribute [local irreducible] SharedDigestFields.cost SharedDigestFields.coordinateCost ClaudeWCT.WCT9.routineCost

theorem accepted_iff (f : Fields) : accepted f = true ↔
    f.2.2.2.toNat < 734 ∧ (∀ k, (f.2.1 k).toNat < 563) ∧ cost f ≤ 788 := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  simp only [List.mem_finRange, forall_const]
  tauto

theorem ungroup_decode (f : Fields) : ungroup (decodeFields f) =
    fun k => (⟨(f.1 k).toNat, (f.1 k).isLt⟩, decodedRank f k) :=
  groupEquiv.symm_apply_apply (fun k => (⟨(f.1 k).toNat, (f.1 k).isLt⟩, decodedRank f k))

theorem encode_decode (f : Fields) (hg : f.2.2.2.toNat < 734)
    (hr : ∀ k, (f.2.1 k).toNat < 563) :
    encodeFields (decodeFields f) f.2.2.1 ⟨f.2.2.2.toNat,hg⟩ = f := by
  apply Prod.ext
  · funext k
    apply BitVec.eq_of_toNat_eq
    rw [cost_encode_nat]
    exact congrArg (fun g => (g k).1.val) (ungroup_decode f)
  · apply Prod.ext
    · funext k
      apply BitVec.eq_of_toNat_eq
      rw [rank_encode_nat]
      change (ungroup (decodeFields f) k).2.val = _
      rw [ungroup_decode]
      exact Nat.mod_eq_of_lt (hr k)
    · apply Prod.ext
      · rfl
      · apply BitVec.eq_of_toNat_eq
        change f.2.2.2.toNat % 2^14 = f.2.2.2.toNat
        exact Nat.mod_eq_of_lt f.2.2.2.isLt

theorem accepted_encode (w : «Word») (hw : weight w ≤ 113) (index : BitVec 31) (gate : Fin 734) :
    accepted (encodeFields w index gate) = true := by
  apply (accepted_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change gate.val % 2^14 < 734
    rw [Nat.mod_eq_of_lt (by have h := gate.isLt; omega)]
    exact gate.isLt
  · intro k
    rw [rank_encode_nat]
    exact (ungroup w k).2.isLt
  · rw [cost_encode]
    omega

theorem weight_decode (f : Fields) (hf : accepted f = true) : weight (decodeFields f) ≤ 113 := by
  obtain ⟨hg,hr,hc⟩ := (accepted_iff f).mp hf
  have he := encode_decode f hg hr
  have hw := cost_encode (decodeFields f) f.2.2.1 ⟨f.2.2.2.toNat,hg⟩
  rw [he] at hw
  omega

def acceptedEquiv : {f : Fields // accepted f = true} ≃
    {w : «Word» // weight w ≤ 113} × BitVec 31 × Fin 734 where
  toFun f := (⟨decodeFields f.val, weight_decode f.val f.property⟩,
    f.val.2.2.1, ⟨f.val.2.2.2.toNat, ((accepted_iff _).mp f.property).1⟩)
  invFun v := ⟨encodeFields v.1.val v.2.1 v.2.2, accepted_encode _ v.1.property _ _⟩
  left_inv f := by
    apply Subtype.ext
    exact encode_decode f.val ((accepted_iff _).mp f.property).1 ((accepted_iff _).mp f.property).2.1
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      exact decode_encode _ _ _
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        change v.2.2.val % 2^14 = v.2.2.val
        exact Nat.mod_eq_of_lt (by have h := v.2.2.isLt; omega)

theorem accepted_fields_card : Fintype.card {f : Fields // accepted f = true} =
    (Finset.univ.filter fun w : «Word» => weight w ≤ 113).card * 2^31 * 734 := by
  rw [Fintype.card_congr acceptedEquiv]
  simp only [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_fin,
    Fintype.card_subtype (fun w : «Word» => weight w ≤ 113)]
  omega

end SigGolfCandidate.Research.SharedFtsModel


namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset

theorem card_filter_congr_generic {α : Type} [Fintype α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) : (univ.filter p).card = (univ.filter q).card := by
  apply congrArg Finset.card
  exact Finset.filter_congr (fun a _ => h a)

theorem top_split (w s c : Nat) (hs : s ≤ 219) (hc : c < 244) :
    256*w+s = 256*145+c+12 ↔ w=145 ∧ s=c+12 := by omega

theorem lower_split (z w s zeros c : Nat) (hs : s ≤ 117) (hw : w ≤ 301)
    (hc : c < 128) :
    65536*z+128*w+s = 65536*zeros+128*201+c ↔ z=zeros ∧ w=201 ∧ s=c := by omega

theorem digit_histogram_of_weighted {α : Type} [Fintype α]
    (g : α → Nat) (P : α → Prop) [DecidablePred P]
    (bits packed k : Nat) (hc : Fintype.card α < 2^bits)
    (hp : (∑ a, (2^bits)^(g a)) = packed)
    (he : ∀ a, g a = k ↔ P a) :
    digit bits packed k = (univ.filter P).card := by
  classical
  exact ((congrArg (fun n => digit bits n k) hp).symm.trans
    (digit_histogram g bits hc k)).trans (card_filter_congr_generic _ _ he)

attribute [local irreducible] digit
  SigGolfResearch.NonbinaryTop.EffectiveCounting.group5
  SigGolfResearch.NonbinaryTop.EffectiveCounting.group8
  SigGolfResearch.NonbinaryTop.EffectiveCounting.gateGroup8
  SigGolfResearch.LowerEffectiveCounting.group
  SigGolfResearch.LowerEffectiveCounting.tail

theorem top_event (credit : Nat) (hc : credit < 244) (w : SigGolfResearch.NonbinaryTop.Codec.Word) :
    SigGolfResearch.NonbinaryTop.EffectiveCounting.stat w = 256*145+credit+12 ↔
      SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
      SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = credit+12 := by
  rw [SigGolfResearch.NonbinaryTop.EffectiveCounting.stat_eq]
  exact top_split _ _ _ (SigGolfResearch.NonbinaryTop.EffectiveCounting.score_le w) hc


theorem top_weighted : (∑ w : SigGolfResearch.NonbinaryTop.Codec.Word,
    (2^136)^SigGolfResearch.NonbinaryTop.EffectiveCounting.stat w) =
      SigGolfResearch.NonbinaryTop.EffectiveCounting.packed :=
  SigGolfResearch.NonbinaryTop.EffectiveCounting.weighted_words (2^136)


theorem top_card : Fintype.card SigGolfResearch.NonbinaryTop.Codec.Word < 2^136 :=
  Nat.lt_of_lt_of_le SigGolfResearch.NonbinaryTop.Counting.word_card_small (Nat.sub_le _ _)

theorem top_digit (credit : Nat) (hc : credit < 244) :
    digit 136 SigGolfResearch.NonbinaryTop.EffectiveCounting.packed
      (256*145+credit+12) =
    (univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
      SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
      SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = credit+12).card := by
  exact digit_histogram_of_weighted _ _ _ _ _ top_card top_weighted (top_event credit hc)
end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

def digit (B p i : Nat) : Nat := p / B^i % B

def packFun (B n : Nat) (f : Nat → Nat) : Nat := ∑ i ∈ range n, f i * B^i

theorem digit_low (B p n i : Nat) (hi : i < n) :
    digit B (p % B^n) i = digit B p i := by
  unfold digit
  have he : n = i+(n-i) := by omega
  rw [he, pow_add, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self B (by omega : n-i ≠ 0))

theorem digit_high (B p n i : Nat) :
    digit B (p / B^n) i = digit B p (n+i) := by
  simp only [digit, Nat.div_div_eq_div_mul, pow_add]

theorem packFun_split (B n m : Nat) (f : Nat → Nat) :
    packFun B (n+m) f = packFun B n f + B^n * packFun B m (fun i => f (n+i)) := by
  simp only [packFun, Finset.sum_range_add, pow_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem packFun_digits (B p n : Nat) : packFun B n (digit B p) = p % B^n := by
  induction n with
  | zero => simp only [packFun, pow_zero, Finset.range_zero, Finset.sum_empty]; exact (Nat.mod_one p).symm
  | succ n ih =>
    simp only [packFun, Finset.sum_range_succ] at ih ⊢
    rw [ih, pow_succ, Nat.mod_mul]
    simp only [digit]
    ring

end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

def cross (B : Nat) : Nat → Nat → Nat → Nat
  | 0, a, b => a*b
  | h+1, a, b =>
    let q := B^(2^h)
    cross B h (a%q) (b%q) + q*cross B h (a/q) (b/q)

theorem cross_zero_left (B h b : Nat) : cross B h 0 b = 0 := by
  induction h generalizing b with
  | zero => simp [cross]
  | succ h ih => simp [cross, ih]

theorem cross_zero_right (B h a : Nat) : cross B h a 0 = 0 := by
  induction h generalizing a with
  | zero => simp [cross]
  | succ h ih => simp [cross, ih]

theorem cross_model (B : Nat) (hB : 0 < B) (h a b : Nat)
    (ha : a < B^(2^h)) (hb : b < B^(2^h)) :
    cross B h a b = packFun B (2^h) (fun i => digit B a i * digit B b i) := by
  induction h generalizing a b with
  | zero =>
    simp only [pow_zero, pow_one] at ha hb
    simp [cross, packFun, digit, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  | succ h ih =>
    have he : 2^(h+1) = 2^h+2^h := by simp only [pow_succ]; omega
    have hp : B^(2^(h+1)) = B^(2^h)*B^(2^h) := by rw [he, pow_add]
    have hq : 0 < B^(2^h) := pow_pos hB _
    have ha' : a/B^(2^h) < B^(2^h) := (Nat.div_lt_iff_lt_mul hq).2 (by simpa only [hp] using ha)
    have hb' : b/B^(2^h) < B^(2^h) := (Nat.div_lt_iff_lt_mul hq).2 (by simpa only [hp] using hb)
    rw [cross, ih _ _ (Nat.mod_lt _ hq) (Nat.mod_lt _ hq), ih _ _ ha' hb', he, packFun_split]
    congr 1
    · unfold packFun
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only
      rw [digit_low _ _ _ _ (mem_range.mp hi), digit_low _ _ _ _ (mem_range.mp hi)]
    · congr 1
      unfold packFun
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      rw [digit_high, digit_high]

end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000

theorem hadamard_eq_cross (h a b : Nat) :
    hadamard h a b = cross (2^1024) h a b := by
  induction h generalizing a b with
  | zero => rfl
  | succ h ih =>
    rw [hadamard]
    split_ifs with hz
    · rcases hz with rfl | rfl
      · exact (cross_zero_left _ _ _).symm
      · exact (cross_zero_right _ _ _).symm
    · simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow]
      simp only [Nat.and_two_pow_sub_one_eq_mod]
      simp only [pow_mul, ih, cross]
      rw [Nat.mul_comm (cross _ _ _ _)]

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

def changeBase (B C : Nat) : Nat → Nat → Nat
  | 0, a => a
  | h+1, a =>
    let q := B^(2^h)
    changeBase B C h (a%q) + C^(2^h)*changeBase B C h (a/q)

theorem changeBase_zero (B C h : Nat) : changeBase B C h 0 = 0 := by
  induction h with
  | zero => rfl
  | succ h ih => simp [changeBase, ih]

theorem changeBase_model (B C : Nat) (hB : 0 < B) (h a : Nat)
    (ha : a < B^(2^h)) :
    changeBase B C h a = packFun C (2^h) (digit B a) := by
  induction h generalizing a with
  | zero =>
    simp only [pow_zero, pow_one] at ha
    simp [changeBase, packFun, digit, Nat.mod_eq_of_lt ha]
  | succ h ih =>
    have he : 2^(h+1) = 2^h+2^h := by simp only [pow_succ]; omega
    have hp : B^(2^(h+1)) = B^(2^h)*B^(2^h) := by rw [he, pow_add]
    have hq : 0 < B^(2^h) := pow_pos hB _
    have ha' : a/B^(2^h) < B^(2^h) := (Nat.div_lt_iff_lt_mul hq).2 (by simpa only [hp] using ha)
    rw [changeBase, ih _ (Nat.mod_lt _ hq), ih _ ha', he, packFun_split]
    congr 1
    · unfold packFun
      apply Finset.sum_congr rfl
      intro i hi
      try dsimp only
      rw [digit_low _ _ _ _ (mem_range.mp hi)]
    · congr 1
      unfold packFun
      apply Finset.sum_congr rfl
      intro i _
      try dsimp only
      rw [digit_high]

end ClaudeWCT.Numerics.SharedDigitBlock

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000

theorem spread_eq_changeBase (h a : Nat) :
    spread h a = changeBase (2^1024) (2^4096) h a := by
  induction h generalizing a with
  | zero => rfl
  | succ h ih =>
    rw [spread]
    split_ifs with hz
    · subst a
      exact (changeBase_zero _ _ _).symm
    · simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow]
      simp only [Nat.and_two_pow_sub_one_eq_mod]
      simp only [pow_mul, ih, changeBase]
      rw [Nat.mul_comm (changeBase _ _ _ _)]

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def geomPoly (n : Nat) : Nat[X] := ∑ i ∈ range n, Polynomial.monomial i 1

theorem geomPoly_eval (B n : Nat) : (geomPoly n).eval B = ∑ i ∈ range n, B^i := by
  simp only [geomPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_mul]

theorem prefixes_eq (a : Nat) :
    prefixes a = (a * (geomPoly 2048).eval (2^1024)) % (2^1024)^2048 := by
  rw [geomPoly_eval, Nat.geomSum_eq (by decide +kernel : 2 ≤ 2^1024)]
  unfold prefixes cutMask
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [pow_mul]

theorem prefixes_coefficient (P : Nat[X]) (i : Nat) (hi : i < 2048)
    (hb : ∀ j, (P*geomPoly 2048).coeff j < 2^1024) :
    digit (2^1024) (prefixes (P.eval (2^1024))) i = (P*geomPoly 2048).coeff i := by
  rw [prefixes_eq, ← Polynomial.eval_mul, digit_low _ _ _ _ hi]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) i _ hb

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem digit_shift_ge (B p n i : Nat) (hB : 0 < B) (hi : n ≤ i) :
    digit B (p*B^n) i = digit B p (i-n) := by
  have he : i = (i-n)+n := by omega
  unfold digit
  conv_lhs => rw [he, pow_add]
  rw [Nat.mul_div_mul_right _ _ (pow_pos hB _)]

theorem digit_shift_lt (B p n i : Nat) (hB : 0 < B) (hi : i < n) :
    digit B (p*B^n) i = 0 := by
  have he : n = (n-i)+i := by omega
  unfold digit
  rw [he, pow_add, ← Nat.mul_assoc, Nat.mul_div_left _ (pow_pos hB _)]
  have hd : B ∣ B^(n-i) := dvd_pow_self B (by omega : n-i ≠ 0)
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hd p)

theorem digit_shift (B p n i : Nat) (hB : 0 < B) :
    digit B (p*B^n) i = if n ≤ i then digit B p (i-n) else 0 := by
  split_ifs with hi
  · exact digit_shift_ge _ _ _ _ hB hi
  · exact digit_shift_lt _ _ _ _ hB (by omega)

theorem packFun_add (B n : Nat) (f g : Nat → Nat) :
    packFun B n (fun i => f i+g i) = packFun B n f + packFun B n g := by
  simp only [packFun, Nat.add_mul, Finset.sum_add_distrib]

theorem packFun_sub (B n : Nat) (f g : Nat → Nat) (hle : ∀ i, i<n → g i ≤ f i) :
    packFun B n (fun i => f i-g i) = packFun B n f - packFun B n g := by
  have he : packFun B n f = packFun B n g + packFun B n (fun i => f i-g i) := by
    rw [← packFun_add]
    unfold packFun
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [Nat.add_sub_of_le (hle i (mem_range.mp hi))]
  rw [he, Nat.add_sub_cancel_left]

theorem sub_packed_digits (B n a b : Nat) (ha : a < B^n) (hb : b < B^n)
    (hle : ∀ i, i<n → digit B b i ≤ digit B a i) :
    a-b = packFun B n (fun i => digit B a i - digit B b i) := by
  rw [packFun_sub _ _ _ _ hle, packFun_digits, packFun_digits,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000

noncomputable def polyOf (n : Nat) (f : Nat → Nat) : Nat[X] :=
  ∑ i ∈ range n, Polynomial.monomial i (f i)

theorem polyOf_eval (B n : Nat) (f : Nat → Nat) : (polyOf n f).eval B = packFun B n f := by
  simp only [polyOf, packFun, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem polyOf_coeff (n : Nat) (f : Nat → Nat) (i : Nat) :
    (polyOf n f).coeff i = if i<n then f i else 0 := by
  simp [polyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, eq_comm]

theorem digit_packFun (B n : Nat) (f : Nat → Nat) (hB : 0 < B)
    (hf : ∀ j, j<n → f j < B) (i : Nat) (hi : i<n) :
    digit B (packFun B n f) i = f i := by
  have hb (j : Nat) : (polyOf n f).coeff j < B := by
    rw [polyOf_coeff]
    split_ifs with hj
    · exact hf j hj
    · exact hB
  rw [← polyOf_eval]
  exact (ClaudeWCT.Numerics.eval_div_pow_mod hB i _ hb).trans
    (by rw [polyOf_coeff, if_pos hi])

theorem digit_sub (B n a b : Nat) (hB : 0<B) (ha : a<B^n) (hb : b<B^n)
    (hle : ∀ j, j<n → digit B b j ≤ digit B a j) (i : Nat) (hi : i<n) :
    digit B (a-b) i = digit B a i - digit B b i := by
  rw [sub_packed_digits _ _ _ _ ha hb hle]
  apply digit_packFun _ _ _ hB _ _ hi
  intro j _
  exact (Nat.sub_le _ _).trans_lt (Nat.mod_lt _ hB)

end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset
attribute [local irreducible] digit
  SigGolfResearch.NonbinaryTop.EffectiveCounting.group5
  SigGolfResearch.NonbinaryTop.EffectiveCounting.gateGroup8

theorem gate_split (w s c : Nat) (g : Prop) [Decidable g]
    (hs : s ≤ 219) (hw : w ≤ 225) (hc : c < 244) :
    256*w+s+65536*(if g then 1 else 0) = 65536+256*145+c+12 ↔
      w=145 ∧ s=c+12 ∧ g := by
  by_cases hg : g
  · rw [if_pos hg, Nat.mul_one]
    constructor
    · intro he
      have he' : 256*w+s = 256*145+c+12 := by omega
      exact ⟨(top_split w s c hs hc).1 he' |>.1, (top_split w s c hs hc).1 he' |>.2, hg⟩
    · rintro ⟨hw', hs', _⟩
      omega
  · rw [if_neg hg, Nat.mul_zero, Nat.add_zero]
    constructor
    · intro he
      omega
    · rintro ⟨_, _, hg'⟩
      exact (hg hg').elim

theorem top_gate_event (credit : Nat) (hc : credit < 244) (w : SigGolfResearch.NonbinaryTop.Codec.Word) :
    SigGolfResearch.NonbinaryTop.EffectiveCounting.gateStat w = 65536+256*145+credit+12 ↔
      SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
      SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = credit+12 ∧
      SigGolfResearch.NonbinaryTop.EffectiveCounting.gateWord w := by
  rw [SigGolfResearch.NonbinaryTop.EffectiveCounting.gateStat_eq]
  exact gate_split _ _ _ _ (SigGolfResearch.NonbinaryTop.EffectiveCounting.score_le w)
    (SigGolfResearch.NonbinaryTop.EffectiveCounting.weight_le_225 w) hc

theorem top_gate_weighted : (∑ w : SigGolfResearch.NonbinaryTop.Codec.Word,
    (2^136)^SigGolfResearch.NonbinaryTop.EffectiveCounting.gateStat w) =
      SigGolfResearch.NonbinaryTop.EffectiveCounting.gatePacked :=
  SigGolfResearch.NonbinaryTop.EffectiveCounting.gate_weighted_words (2^136)

theorem top_gate_digit (credit : Nat) (hc : credit < 244) :
    digit 136 SigGolfResearch.NonbinaryTop.EffectiveCounting.gatePacked (65536+256*145+credit+12) =
      (univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
        SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
        SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = credit+12 ∧
        SigGolfResearch.NonbinaryTop.EffectiveCounting.gateWord w).card := by
  exact digit_histogram_of_weighted _ _ _ _ _ top_card top_gate_weighted (top_gate_event credit hc)
end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem window_eq (a lo hi : Nat) :
    window a lo hi = (a*(2^1024)^lo) % (2^1024)^2048 -
      (a*(2^1024)^(hi+1)) % (2^1024)^2048 := by
  unfold window cutMask
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  simp only [pow_mul]

theorem window_digits (a lo hi i : Nat) (hlo : lo ≤ hi) (hi' : i < 2048)
    (hmono : ∀ j k, j ≤ k → k<2048 → digit (2^1024) a j ≤ digit (2^1024) a k) :
    digit (2^1024) (window a lo hi) i =
      (if lo ≤ i then digit (2^1024) a (i-lo) else 0) -
      (if hi+1 ≤ i then digit (2^1024) a (i-(hi+1)) else 0) := by
  let B : Nat := 2^1024
  have hB : 0<B := pow_pos (by decide) _
  have hp : 0<B^2048 := pow_pos hB _
  have hd (k j : Nat) (hj : j<2048) :
      digit B ((a*B^k)%B^2048) j = if k ≤ j then digit B a (j-k) else 0 := by
    rw [digit_low _ _ _ _ hj, digit_shift _ _ _ _ hB]
  have hle (j : Nat) (hj : j<2048) :
      digit B ((a*B^(hi+1))%B^2048) j ≤ digit B ((a*B^lo)%B^2048) j := by
    rw [hd _ _ hj, hd _ _ hj]
    by_cases hh : hi+1 ≤ j
    · have hl : lo ≤ j := by omega
      rw [if_pos hh, if_pos hl]
      exact hmono _ _ (by omega) (by omega)
    · rw [if_neg hh]
      exact Nat.zero_le _
  rw [window_eq]
  change digit B ((a*B^lo)%B^2048 - (a*B^(hi+1))%B^2048) i = _
  rw [digit_sub _ _ _ _ hB (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hle i hi',
    hd _ _ hi', hd _ _ hi']

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem geomPoly_coeff (n i : Nat) : (geomPoly n).coeff i = if i<n then 1 else 0 :=
  polyOf_coeff n (fun _ => 1) i

theorem prefix_poly_coefficient (P : Nat[X]) (n i : Nat) (hi : i<n) :
    (P*geomPoly n).coeff i = ∑ k ∈ range (i+1), P.coeff k := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [geomPoly_coeff, if_pos (by have hk' := mem_range.mp hk; omega), Nat.mul_one]

theorem prefix_poly_monotone (P : Nat[X]) (n j k : Nat) (hj : j≤k) (hk : k<n) :
    (P*geomPoly n).coeff j ≤ (P*geomPoly n).coeff k := by
  rw [prefix_poly_coefficient _ _ _ (by omega), prefix_poly_coefficient _ _ _ hk]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun _ _ _ => Nat.zero_le _)

theorem prefixes_digits_monotone (P : Nat[X])
    (hb : ∀ j, (P*geomPoly 2048).coeff j < 2^1024)
    (j k : Nat) (hj : j≤k) (hk : k<2048) :
    digit (2^1024) (prefixes (P.eval (2^1024))) j ≤
      digit (2^1024) (prefixes (P.eval (2^1024))) k := by
  rw [prefixes_coefficient _ _ (by omega) hb, prefixes_coefficient _ _ hk hb]
  exact prefix_poly_monotone _ _ _ _ hj hk

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem hadamard_11_model (a b : Nat)
    (ha : a < (2^1024)^2048) (hb : b < (2^1024)^2048) :
    hadamard 11 a b = packFun (2^1024) 2048
      (fun i => digit (2^1024) a i * digit (2^1024) b i) := by
  have hq : (2:Nat)^11 = 2048 := by decide
  have ha' : a < (2^1024)^(2^11) := by simpa only [hq] using ha
  have hb' : b < (2^1024)^(2^11) := by simpa only [hq] using hb
  rw [hadamard_eq_cross]
  have h := cross_model (2^1024) (pow_pos (by decide) _) 11 a b ha' hb'
  simpa only [hq] using h

theorem window_bound (a lo hi : Nat) : window a lo hi < (2^1024)^2048 := by
  rw [window_eq]
  exact (Nat.sub_le _ _).trans_lt (Nat.mod_lt _ (pow_pos (pow_pos (by decide) _) _))

theorem directedFirst_model (a pref : Cell) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048) :
    directedFirst a pref lo hi shift =
      (packFun (2^1024) 2048 (fun i =>
        digit (2^1024) a.2 i * digit (2^1024) (window pref.1 lo hi) i +
        digit (2^1024) a.1 i * digit (2^1024) (window pref.2 lo hi) i) *
        (2^1024)^shift) % (2^1024)^2048 := by
  unfold directedFirst
  rw [hadamard_11_model _ _ haF (window_bound _ _ _),
    hadamard_11_model _ _ haP (window_bound _ _ _), ← packFun_add]
  unfold cutMask
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  simp only [pow_mul]

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset
open scoped BigOperators

theorem packFun_const_mul (B n c : Nat) (f : Nat → Nat) :
    packFun B n (fun i => c * f i) = c * packFun B n f := by
  simp only [packFun, Finset.mul_sum, Nat.mul_assoc]

theorem packFun_sum {α : Type} [Fintype α] (B n : Nat) (f : α → Nat → Nat) :
    packFun B n (fun i => ∑ a, f a i) = ∑ a, packFun B n (f a) := by
  simp only [packFun, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem packFun_window (B p n start : Nat) :
    packFun B n (fun i => digit B p (start+i)) = p / B^start % B^n := by
  conv_lhs => arg 3; ext i; rw [← digit_high]
  exact packFun_digits B (p / B^start) n

theorem digit_window_sum {α : Type} [Fintype α] (B n : Nat)
    (p start coeff : α → Nat) (hB : 0 < B)
    (hsmall : ∀ i, i<n → (∑ a, coeff a * digit B (p a) (start a+i)) < B)
    (i : Nat) (hi : i<n) :
    digit B (∑ a, coeff a * (p a / B^(start a) % B^n)) i =
      ∑ a, coeff a * digit B (p a) (start a+i) := by
  have he : (∑ a, coeff a * (p a / B^(start a) % B^n)) =
      packFun B n (fun j => ∑ a, coeff a * digit B (p a) (start a+j)) := by
    rw [packFun_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [packFun_const_mul, packFun_window]
  rw [he]
  exact digit_packFun B n _ hB hsmall i hi
end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def bucketSeries : List Nat → Nat → Nat → Cell
  | [], _, _ => (0,0)
  | b::bs, c, p =>
    let n := p % 2^512
    let v := bucketSeries bs (c+1) (p / 2^512)
    (n*(2^1024)^b+v.1, (c*n)*(2^1024)^b+v.2)

theorem bucketSeries_zero (bs : List Nat) (c : Nat) : bucketSeries bs c 0 = (0,0) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [bucketSeries, ih]

theorem bucket_eq_series (bs : List Nat) (c p : Nat) : bucket bs c p = bucketSeries bs c p := by
  induction bs generalizing c p with
  | nil => rfl
  | cons b bs ih =>
    by_cases hp : p=0
    · subst p
      rw [bucketSeries_zero]
      simp only [bucket, if_true]
    · simp only [bucket, if_neg hp, Nat.and_two_pow_sub_one_eq_mod,
        Nat.shiftRight_eq_div_pow, ih]
      dsimp only [bucketSeries]
      split_ifs with hn
      · simp only [hn, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Prod.mk.eta]
      · simp only [Nat.shiftLeft_eq, pow_mul]

end ClaudeWCT.Numerics.SharedPathList

namespace ClaudeWCT.Numerics.CanonicalHistogram
open CanonicalCompression
theorem top_histogram_digits : ∀ c : Fin 204,
    coefficient 136 (packHistogram 136 16 204 topAcceptedHistogram) c.val =
      histogramWeight topAcceptedHistogram (c.val+16) := by decide +kernel

theorem lower_histogram_digits : ∀ c : Fin 128,
    coefficient 132 (packHistogram 132 0 128 lowerHistogram) c.val =
      histogramWeight lowerHistogram c.val := by decide +kernel
end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset

theorem top_card_three : 3 * Fintype.card SigGolfResearch.NonbinaryTop.Codec.Word < 2^136 := by
  norm_num [SigGolfResearch.NonbinaryTop.Codec.Word,
    SigGolfResearch.NonbinaryTop.Codec.Triple8, SigGolfResearch.NonbinaryTop.Codec.Triple5,
    Fintype.card_prod, Fintype.card_fun]

theorem lower_card_seven : 7 * Fintype.card SigGolfResearch.LowerEffectiveCounting.«Word» < 2^132 := by
  let forget : SigGolfResearch.LowerEffectiveCounting.«Word» →
      (Fin 14 → SigGolfResearch.NonbinaryTop.Codec.Triple8) × Fin 8 :=
    fun w => (fun q => (w.1 q).val, w.2)
  have hi : Function.Injective forget := by
    intro a b hab
    apply Prod.ext
    · funext q
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst hab) q
    · change (forget a).2 = (forget b).2
      exact congrArg Prod.snd hab
  have hc := Fintype.card_le_of_injective forget hi
  norm_num [Fintype.card_prod, Fintype.card_fun, SigGolfResearch.NonbinaryTop.Codec.Triple8] at hc ⊢
  omega
end ClaudeWCT.Numerics.CanonicalCounting

namespace ClaudeWCT.Numerics.CanonicalCounting
open Finset
open scoped BigOperators

theorem count_fibers_fin {α : Type} [Fintype α] (g : α → Nat) (P : α → Prop)
    [DecidablePred P] (n : Nat) :
    (∑ j : Fin n, (univ.filter fun a => g a = j.val ∧ P a).card) =
      (univ.filter fun a => g a < n ∧ P a).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : P a
  · simp only [hp, and_true]
    by_cases hg : g a < n
    · let j : Fin n := ⟨g a, hg⟩
      have he (k : Fin n) : g a = k.val ↔ k = j := by
        simp only [j, Fin.ext_iff]
        omega
      simp only [he, if_pos hg]
      simp
    · have he (k : Fin n) : ¬g a = k.val := by
        have := k.isLt
        omega
      simp only [he, if_neg, hg, if_false, Finset.sum_const_zero]
  · simp only [hp, and_false, if_false, Finset.sum_const_zero]

end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedPathList
open Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def binnedPoly : List Nat → (Nat → Nat) → Nat[X]
  | [], _ => 0
  | b::bs, f => C (f 0) * X^b + binnedPoly bs (fun j => f (j+1))

theorem quotient_digit (B p j : Nat) :
    (p / B) / B^j % B = p / B^(j+1) % B := by
  rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm B]

theorem bucketSeries_poly (bs : List Nat) (c p : Nat) :
    (bucketSeries bs c p).1 =
      (binnedPoly bs (fun j => (p / (2^512)^j) % 2^512)).eval (2^1024) ∧
    (bucketSeries bs c p).2 =
      (binnedPoly bs (fun j => (c+j) * ((p / (2^512)^j) % 2^512))).eval (2^1024) := by
  induction bs generalizing c p with
  | nil => simp only [bucketSeries, binnedPoly, Polynomial.eval_zero, and_self]
  | cons b bs ih =>
    have h := ih (c+1) (p / 2^512)
    simp only [bucketSeries, binnedPoly, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, pow_zero,
      Nat.div_one, Nat.add_zero]
    constructor
    · rw [h.1]
      congr 2
      apply congrArg (binnedPoly bs)
      funext j
      exact quotient_digit (2^512) p j
    · rw [h.2]
      congr 2
      apply congrArg (binnedPoly bs)
      funext j
      rw [quotient_digit]
      congr 1
      omega

theorem binnedPoly_coeff (bs : List Nat) (f : Nat → Nat) (k : Nat) :
    (binnedPoly bs f).coeff k =
      (bs.mapIdx (fun j b => if b=k then f j else 0)).sum := by
  induction bs generalizing f with
  | nil => simp [binnedPoly]
  | cons b bs ih =>
    simp only [binnedPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, List.mapIdx_cons, List.sum_cons, ih]
    simp only [mul_ite, Nat.mul_one, Nat.mul_zero, eq_comm]

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset
open scoped BigOperators
open SharedDigitBlock

theorem bits_digit_eq (bits p i : Nat) :
    (p >>> (bits*i)) % 2^bits = digit (2^bits) p i := by
  simp only [digit, Nat.shiftRight_eq_div_pow, pow_mul]

theorem shift_window_eq (bits p start len : Nat) :
    (p >>> (bits*start)) % 2^(bits*len) = p / (2^bits)^start % (2^bits)^len := by
  simp only [Nat.shiftRight_eq_div_pow, pow_mul]

theorem two_window_digits (B len start gateStart p g encoded : Nat) (hB : 0<B)
    (f h : Nat → Nat)
    (hp : ∀ i, i<len → digit B p (start+i) = f i)
    (hg : ∀ i, i<len → digit B g (gateStart+i) = h i)
    (hbound : ∀ i, i<len → f i + 2*h i < B)
    (he : encoded = p / B^start % B^len + 2*(g / B^gateStart % B^len))
    (i : Nat) (hi : i<len) : digit B encoded i = f i + 2*h i := by
  let ps : Fin 2 → Nat := ![p,g]
  let starts : Fin 2 → Nat := ![start,gateStart]
  let coeffs : Fin 2 → Nat := ![1,2]
  have hs (j : Nat) (hj : j<len) :
      (∑ a : Fin 2, coeffs a * digit B (ps a) (starts a+j)) = f j+2*h j := by
    simp only [Fin.sum_univ_two, ps, starts, coeffs, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.one_mul, hp j hj, hg j hj]
  have hsmall (j : Nat) (hj : j<len) :
      (∑ a : Fin 2, coeffs a * digit B (ps a) (starts a+j)) < B := by
    rw [hs j hj]
    exact hbound j hj
  have hn : (∑ a : Fin 2, coeffs a * (ps a / B^(starts a) % B^len)) = encoded := by
    simp only [Fin.sum_univ_two, ps, starts, coeffs, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.one_mul]
    exact he.symm
  rw [← hn]
  exact (digit_window_sum B len ps starts coeffs hB hsmall i hi).trans (hs i hi)
end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem bucket_polynomial (bs : List Nat) (c : Nat) (P : Nat[X])
    (hP : ∀ i, P.coeff i < 2^512) :
    bucket bs c (P.eval (2^512)) =
      ((binnedPoly bs P.coeff).eval (2^1024),
       (binnedPoly bs (fun j => (c+j)*P.coeff j)).eval (2^1024)) := by
  rw [bucket_eq_series]
  have h := bucketSeries_poly bs c (P.eval (2^512))
  have hd (j : Nat) : P.eval (2^512) / (2^512)^j % 2^512 = P.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) j P hP
  simp_rw [hd] at h
  exact Prod.ext h.1 h.2

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_eq_sum (bs : List Nat) (f : Nat → Nat) :
    binnedPoly bs f = ∑ i : Fin bs.length, C (f i) * X^(bs[i]) := by
  induction bs generalizing f with
  | nil => simp [binnedPoly]
  | cons b bs ih =>
    rw [binnedPoly]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, List.getElem_cons_zero, Fin.val_zero, Fin.val_succ, List.getElem_cons_succ]
    rw [ih]
    simp only [Fin.getElem_fin]

theorem binnedPoly_finite_coeff (bs : List Nat) (f : Nat → Nat) (k : Nat) :
    (binnedPoly bs f).coeff k = ∑ i : Fin bs.length, if bs[i] = k then f i else 0 := by
  rw [binnedPoly_eq_sum]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, Nat.mul_one, Nat.mul_zero, eq_comm]

theorem binnedPoly_mono (bs : List Nat) (f g : Nat → Nat)
    (h : ∀ i, i<bs.length → f i ≤ g i) (k : Nat) :
    (binnedPoly bs f).coeff k ≤ (binnedPoly bs g).coeff k := by
  rw [binnedPoly_finite_coeff, binnedPoly_finite_coeff]
  apply sum_le_sum
  intro i _
  split_ifs
  · exact h i i.isLt
  · rfl

theorem binnedPoly_eval_one (bs : List Nat) (f : Nat → Nat) :
    (binnedPoly bs f).eval 1 = ∑ i : Fin bs.length, f i := by
  rw [binnedPoly_eq_sum, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, Nat.mul_one]

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_fiber_coeff {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (k : Nat) :
    (binnedPoly bs (fun i => ∑ a, if value a=i then weight a else 0)).coeff k =
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then weight a else 0) else 0 := by
  rw [binnedPoly_finite_coeff]
  have he (i : Fin bs.length) :
      (if bs[i] = k then ∑ a, if value a=i.val then weight a else 0 else 0) =
      ∑ a, if bs[i] = k then (if value a=i.val then weight a else 0) else 0 := by
    by_cases hi : bs[i] = k
    · simp only [if_pos hi]
    · simp only [if_neg hi, Finset.sum_const_zero]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a < bs.length
  · rw [dif_pos ha]
    let i : Fin bs.length := ⟨value a, ha⟩
    rw [Finset.sum_eq_single i]
    · simp only [i, Fin.getElem_fin, if_true]
    · intro j _ hji
      have hn : value a ≠ j.val := by
        intro he
        apply hji
        exact Fin.ext he.symm
      simp only [if_neg hn, ite_self]
    · exact fun hi => (hi (Finset.mem_univ _)).elim
  · rw [dif_neg ha]
    apply Finset.sum_eq_zero
    intro i _
    have hn : value a ≠ i.val := by intro he; exact ha (he ▸ i.isLt)
    simp only [if_neg hn, ite_self]

theorem binnedPoly_fiber_lower {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (f : Nat → Nat)
    (hf : ∀ i, i<bs.length → f i ≤ ∑ a, if value a=i then weight a else 0)
    (k : Nat) :
    (binnedPoly bs f).coeff k ≤
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then weight a else 0) else 0 := by
  rw [← binnedPoly_fiber_coeff]
  exact binnedPoly_mono bs f _ hf k

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {K r : Nat} (E : Fin r → Fin K × β) :
    coordinateCoverage val E ≤ K*563 := by
  classical
  unfold coordinateCoverage
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (by simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hβ])

theorem pair_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : PairHistory β r) :
    pairCoverage val h ≤ 2*(64*563)^2 := by
  have hb (s : Fin 2) : selectorValue (fun _ => coordinateCoverage val)
      h.1 h.2.1 h.2.2 s ≤ (64*563)^2 := by
    unfold selectorValue
    rw [pow_two]
    exact Nat.mul_le_mul (coordinate_coverage_le val hβ _) (coordinate_coverage_le val hβ _)
  unfold pairCoverage
  calc _ ≤ (64*563)^2+(64*563)^2 := Nat.add_le_add (hb 0) (hb 1)
       _ = _ := by omega

theorem forest_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : ForestHistory β r) : forestCoverage val h ≤ alphabetSize := by
  have hp : (∏ i : Fin 4, pairCoverage val (h.1 i)) ≤ (2*(64*563)^2)^4 := by
    calc _ ≤ ∏ _i : Fin 4, (2*(64*563)^2) :=
          Finset.prod_le_prod' (fun i _ => pair_coverage_le val hβ (h.1 i))
         _ = _ := by rw [Fin.prod_const]
  exact Nat.mul_le_mul hp (coordinate_coverage_le val hβ h.2)

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedFees
open ENNReal
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.PoissonReflect
open SphincsSecurity.Concrete
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem shared_mgf_bound_of_rows (T : Nat) (hT : 2^32 ≤ T)
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * (2^31:ENNReal)⁻¹ * κ ≤ (2013623:ENNReal)/1000000)
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r * (certifiedPayoff r).1 : Nat) : ENNReal) /
        ((maxFee*alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    ((maxFee*priceScaleTotal : Nat) : ENNReal)/scale *
      binomialAverage (2^31:ENNReal)⁻¹ T g ≤ (69:ENNReal)/10 := by
  apply poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r * (certifiedPayoff r).1)
    (dbase := maxFee*alphabetSize) (sn := maxFee*priceScaleTotal)
    (sd := scale) (Mn := 69) (Md := 10) (R := 80)
    (show poissonCheckQ _ _ _ _ _ _ _ _ _ _ _ _ = true from shared_mgf_checked)
    (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num [scale]) (by norm_num)
    rate_le_one κ hκ hlam (rejection_window_sharp T hT) g
  · intro r hr
    simpa only [mul_div_assoc] using hpay r hr
  · exact htail

theorem shared_residual_bound_of_rows (T : Nat) (hT : 2^32 ≤ T)
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal) * (2^31:ENNReal)⁻¹ * κ ≤ (2013623:ENNReal)/1000000)
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r * (certifiedPayoff r).2 : Nat) : ENNReal) /
        ((scale*alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    (priceScaleTotal : ENNReal) *
      binomialAverage (2^31:ENNReal)⁻¹ T g ≤ (193:ENNReal)/250000 := by
  have h := poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r * (certifiedPayoff r).2)
    (dbase := scale*alphabetSize) (sn := priceScaleTotal)
    (sd := 1) (Mn := 193) (Md := 250000) (R := 80)
    (show poissonCheckQ _ _ _ _ _ _ _ _ _ _ _ _ = true from shared_residual_checked)
    (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by norm_num [scale, alphabetSize]) (by norm_num) (by norm_num)
    rate_le_one κ hκ hlam (rejection_window_sharp T hT) g
    (fun r hr => by simpa only [mul_div_assoc] using hpay r hr) htail
  simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using h

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset
open scoped BigOperators
set_option quotPrecheck false

local notation "topCount" credit:arg =>
  (univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
    SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
    SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = credit+12).card

local notation "topGateCount" credit:arg =>
  (univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
    SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
    SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = credit+12 ∧
    SigGolfResearch.NonbinaryTop.EffectiveCounting.gateWord w).card

theorem top_counts_bound (credit : Nat) :
    topCount credit + 2 * topGateCount credit < 2^136 := by
  have h1 : topCount credit ≤ Fintype.card SigGolfResearch.NonbinaryTop.Codec.Word :=
    Finset.card_filter_le _ _
  have h2 : topGateCount credit ≤ Fintype.card SigGolfResearch.NonbinaryTop.Codec.Word :=
    Finset.card_filter_le _ _
  have h3 := CanonicalCounting.top_card_three
  omega

theorem counting_digit_eq (bits p i : Nat) :
    CanonicalCounting.digit bits p i = SharedDigitBlock.digit (2^bits) p i :=
  bits_digit_eq bits p i

theorem top_count_digit (i : Nat) (hi : i<204) :
    SharedDigitBlock.digit (2^136) SigGolfResearch.NonbinaryTop.EffectiveCounting.packed
      (256*145+16+12+i) = topCount (i+16) := by
  have h := CanonicalCounting.top_digit (i+16) (by omega)
  rw [counting_digit_eq] at h
  have he : 256*145+16+12+i = 256*145+(i+16)+12 := by omega
  rw [he]
  exact h

theorem top_gate_count_digit (i : Nat) (hi : i<204) :
    SharedDigitBlock.digit (2^136) SigGolfResearch.NonbinaryTop.EffectiveCounting.gatePacked
      (65536+(256*145+16+12)+i) = topGateCount (i+16) := by
  have h := CanonicalCounting.top_gate_digit (i+16) (by omega)
  rw [counting_digit_eq] at h
  have he : 65536+(256*145+16+12)+i = 65536+256*145+(i+16)+12 := by omega
  rw [he]
  exact h

theorem top_counts_from_packed (encoded : Nat)
    (he : encoded =
      (SigGolfResearch.NonbinaryTop.EffectiveCounting.packed >>> (136*(256*145+16+12))) % 2^(136*204) +
      2*((SigGolfResearch.NonbinaryTop.EffectiveCounting.gatePacked >>> (136*(65536+(256*145+16+12)))) % 2^(136*204)))
    (i : Nat) (hi : i<204) :
    coefficient 136 encoded i = topCount (i+16)+2*topGateCount (i+16) := by
  have he' := he
  simp only [shift_window_eq] at he'
  exact (bits_digit_eq 136 encoded i).trans
    (two_window_digits (2^136) 204 (256*145+16+12) (65536+(256*145+16+12))
      SigGolfResearch.NonbinaryTop.EffectiveCounting.packed
      SigGolfResearch.NonbinaryTop.EffectiveCounting.gatePacked encoded (by positivity)
      (fun j => topCount (j+16)) (fun j => topGateCount (j+16))
      top_count_digit top_gate_count_digit (fun j _ => top_counts_bound (j+16)) he' i hi)
end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem window_prefix_interval (P : Nat[X])
    (hb : ∀ j, (P*geomPoly 2048).coeff j < 2^1024)
    (lo hi i : Nat) (hlo : lo ≤ hi) (hi' : i<2048) :
    digit (2^1024) (window (prefixes (P.eval (2^1024))) lo hi) i =
      if lo ≤ i then ∑ j ∈ Ico (i-hi) (i-lo+1), P.coeff j else 0 := by
  rw [window_digits _ _ _ _ hlo hi' (prefixes_digits_monotone P hb)]
  by_cases hl : lo ≤ i
  · simp only [if_pos hl]
    rw [prefixes_coefficient _ _ (by omega) hb,
      prefix_poly_coefficient _ _ _ (by omega)]
    by_cases hh : hi+1 ≤ i
    · rw [if_pos hh, prefixes_coefficient _ _ (by omega) hb,
        prefix_poly_coefficient _ _ _ (by omega)]
      have he : i-(hi+1)+1 = i-hi := by omega
      rw [he]
      have hs := Finset.sum_range_add_sum_Ico P.coeff (show i-hi ≤ i-lo+1 by omega)
      omega
    · rw [if_neg hh, Nat.sub_zero]
      have he : i-hi = 0 := by omega
      rw [he, Nat.Ico_zero_eq_range]
  · have hh : ¬hi+1 ≤ i := by omega
    simp only [if_neg hl, if_neg hh, Nat.sub_self]

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset CanonicalCompression

theorem top_histogram_counts_of_check (hcheck : topHistogramCheck = true) (c : Fin 204) :
    (univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
      SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
      SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = c.val+16+12).card +
    2*(univ.filter fun w : SigGolfResearch.NonbinaryTop.Codec.Word =>
      SigGolfResearch.NonbinaryTop.Counting.weight w = 145 ∧
      SigGolfResearch.NonbinaryTop.EffectiveCounting.score w = c.val+16+12 ∧
      SigGolfResearch.NonbinaryTop.EffectiveCounting.gateWord w).card =
    histogramWeight topAcceptedHistogram (c.val+16) := by
  have he : packHistogram 136 16 204 topAcceptedHistogram =
      (SigGolfResearch.NonbinaryTop.EffectiveCounting.packed >>> (136*(256*145+16+12))) % 2^(136*204) +
      2*((SigGolfResearch.NonbinaryTop.EffectiveCounting.gatePacked >>> (136*(65536+(256*145+16+12)))) % 2^(136*204)) :=
    by simpa only [topHistogramCheck, decide_eq_true_eq] using hcheck
  exact (top_counts_from_packed _ he c.val c.isLt).symm.trans (top_histogram_digits c)
end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.Thinning
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_near_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {K r : Nat} (E : Fin r → Fin K × β) : coordinateNear val E ≤ 6*(K*563) := by
  classical
  unfold coordinateNear
  calc _ ≤ ∑ _i : Fin 6, K*563 := Finset.sum_le_sum (fun i _ =>
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
            (by simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hβ]))
       _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

theorem pair_near_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : PairHistory β r) : pairNear val h ≤ 12*(2*(64*563)^2) := by
  have hs (s : Fin 2) : selectorKernel
      (fun _ A B => coordinateNear val A * coordinateCoverage val B +
        coordinateCoverage val A * coordinateNear val B) h.1 h.2.1 h.2.2 s ≤ 12*(64*563)^2 := by
    unfold selectorKernel
    calc _ ≤ (6*(64*563))*(64*563)+(64*563)*(6*(64*563)) :=
          Nat.add_le_add
            (Nat.mul_le_mul (coordinate_near_le val hβ _) (coordinate_coverage_le val hβ _))
            (Nat.mul_le_mul (coordinate_coverage_le val hβ _) (coordinate_near_le val hβ _))
         _ = _ := by ring
  unfold pairNear
  exact (Nat.add_le_add (hs 0) (hs 1)).trans_eq (by ring)

theorem marked_product_const (a b : Nat) (k : Fin 4) :
    (∏ i : Fin 4, if i=k then a else b) = a*b^3 := by
  fin_cases k <;> simp [Fin.prod_univ_succ] <;> ring

theorem forest_near_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563)
    {r : Nat} (h : ForestHistory β r) : forestNear val h ≤ 54*alphabetSize := by
  let D : Nat := 2*(64*563)^2
  have hmark (k : Fin 4) :
      (∏ i, if i=k then pairNear val (h.1 i) else pairCoverage val (h.1 i)) ≤ 12*D^4 := by
    calc _ ≤ ∏ i : Fin 4, if i=k then 12*D else D := by
              apply Finset.prod_le_prod'
              intro i _
              split_ifs
              · exact pair_near_le val hβ _
              · exact pair_coverage_le val hβ _
         _ = 12*D^4 := by rw [marked_product_const]; ring
  have hs : (∑ k : Fin 4, ∏ i, if i=k then pairNear val (h.1 i) else
      pairCoverage val (h.1 i)) ≤ 4*(12*D^4) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
      Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) => hmark k)
  have hp : (∏ i : Fin 4, pairCoverage val (h.1 i)) ≤ D^4 := by
    calc _ ≤ ∏ _i : Fin 4, D := Finset.prod_le_prod' (fun i _ => pair_coverage_le val hβ _)
         _ = _ := by rw [Fin.prod_const]
  unfold forestNear
  calc _ ≤ (4*(12*D^4))*(128*563) + D^4*(6*(128*563)) :=
          Nat.add_le_add
            (Nat.mul_le_mul hs (coordinate_coverage_le val hβ h.2))
            (Nat.mul_le_mul hp (coordinate_near_le val hβ h.2))
       _ = 54*alphabetSize := by unfold alphabetSize D; ring

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedMoments
open ENNReal
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.PoissonReflect
open SphincsSecurity.Concrete
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem first_bound_of_rows (T : Nat) (hT : 2^32 ≤ T)
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal)*(2^31:ENNReal)⁻¹*κ ≤ (2013623:ENNReal)/1000000)
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r*forestMoment r : Nat) : ENNReal) /
        ((alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    (priceScaleTotal : ENNReal)*binomialAverage (2^31:ENNReal)⁻¹ T g ≤ (845:ENNReal)/1000 := by
  have h := poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r*forestMoment r) (dbase := alphabetSize)
    (sn := priceScaleTotal) (sd := 1) (Mn := 845) (Md := 1000) (R := 80)
    first_moment_checked (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by norm_num [alphabetSize]) (by norm_num) (by norm_num)
    rate_le_one κ hκ hlam (rejection_window_sharp T hT) g
    (fun r hr => by simpa only [mul_div_assoc] using hpay r hr) htail
  simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using h

theorem near_bound_of_rows (T : Nat) (hT : 2^32 ≤ T)
    (κ : ENNReal) (hκ : 1 ≤ κ)
    (hlam : (T : ENNReal)*(2^31:ENNReal)⁻¹*κ ≤ (2013623:ENNReal)/1000000)
    (g : Nat → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ κ^r *
      ((16^r*forestNearMoment r : Nat) : ENNReal) /
        ((54*alphabetSize*fieldSize^(9*r) : Nat) : ENNReal))
    (htail : ∀ r, 80<r → g r ≤ 1) :
    ((54*priceScaleTotal : Nat) : ENNReal)*binomialAverage (2^31:ENNReal)⁻¹ T g ≤ 350 := by
  have h := poissonCheckQ_sound_tilt (Qv := fieldSize)
    (f := fun r => 16^r*forestNearMoment r) (dbase := 54*alphabetSize)
    (sn := 54*priceScaleTotal) (sd := 1) (Mn := 350) (Md := 1) (R := 80)
    near_moment_checked (by norm_num [fieldSize]) (by norm_num) (by norm_num)
    (by norm_num [alphabetSize]) (by norm_num) (by norm_num)
    rate_le_one κ hκ hlam (rejection_window_sharp T hT) g
    (fun r hr => by simpa only [mul_div_assoc] using hpay r hr) htail
  simpa only [Nat.cast_one, Nat.cast_ofNat, div_one] using h

end ClaudeWCT.Numerics.SharedMoments

namespace ClaudeWCT.Numerics.CanonicalHistogram
open OracleComp OracleSpec ENNReal Finset CanonicalCompression
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical

theorem selected_top_histogram_card (hcheck : topHistogramCheck = true)
    (floor : Nat) (c : Fin 204) (hf : floor ≤ c.val+16) :
    (univ.filter fun answer : HashOutput => accepted 0 floor
      (fun ds => CanonicalPolicy.credit 0 ds = c.val+16) (encodingAnswer 0 answer)).card =
      histogramWeight topAcceptedHistogram (c.val+16)*2^127 := by
  rw [selected_top_credit_card floor (c.val+16) hf]
  rw [top_histogram_counts_of_check hcheck c]

theorem selected_top_histogram_probability (hcheck : topHistogramCheck = true)
    (floor : Nat) (c : Fin 204) (hf : floor ≤ c.val+16) :
    Pr[fun answer => accepted 0 floor (fun ds => CanonicalPolicy.credit 0 ds = c.val+16)
      (encodingAnswer 0 answer) | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight topAcceptedHistogram (c.val+16) : ENNReal)/2^129 := by
  rw [selected_uniform_probability _ _ _ _ (selected_top_histogram_card hcheck floor c hf)]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256 = 2^129*2^127 by rw [← pow_add]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)
end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset
theorem lower_event (zeros credit : Nat) (hc : credit < 128) (w : SigGolfResearch.LowerEffectiveCounting.Word) :
    SigGolfResearch.LowerEffectiveCounting.stat w = 65536*zeros+128*201+credit ↔
      SigGolfResearch.LowerEffectiveCounting.zeros w = zeros ∧
      SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
      SigGolfResearch.LowerEffectiveCounting.score w = credit := by
  rw [SigGolfResearch.LowerEffectiveCounting.stat_eq]
  exact lower_split _ _ _ _ _ (SigGolfResearch.LowerEffectiveCounting.score_le w)
    (SigGolfResearch.LowerEffectiveCounting.weight_le w) hc

attribute [local irreducible] SigGolfResearch.LowerEffectiveCounting.packedAt
set_option maxRecDepth 100000 in
theorem lower_weighted : (∑ w : SigGolfResearch.LowerEffectiveCounting.Word,
    (2^132)^SigGolfResearch.LowerEffectiveCounting.stat w) =
      SigGolfResearch.LowerEffectiveCounting.packed :=
  SigGolfResearch.LowerEffectiveCounting.weighted_words_at (2^132)

end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weighted_fiber_count {α : Type} [Fintype α] (value : α → Nat) (c j : Nat) :
    (∑ a, if value a=j then c+value a else 0) =
      (c+j) * (Finset.univ.filter fun a => value a=j).card := by
  classical
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a=j
  · simp only [ha, if_true, Nat.mul_one]
  · simp only [if_neg ha, Nat.mul_zero]

theorem bucket_retained_lower {α : Type} [Fintype α]
    (value : α → Nat) (bs : List Nat) (c : Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j < 2^512)
    (hcount : ∀ j, P.coeff j ≤ (Finset.univ.filter fun a => value a=j).card)
    (hprob : ∀ j, (binnedPoly bs P.coeff).coeff j < 2^1024)
    (hfirst : ∀ j, (binnedPoly bs (fun j => (c+j)*P.coeff j)).coeff j < 2^1024)
    (k : Nat) :
    ((bucket bs c (P.eval (2^512))).1 / (2^1024)^k % 2^1024 ≤
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then 1 else 0) else 0) ∧
    ((bucket bs c (P.eval (2^512))).2 / (2^1024)^k % 2^1024 ≤
      ∑ a, if h : value a < bs.length then
        (if bs[value a]'h = k then c+value a else 0) else 0) := by
  classical
  rw [bucket_polynomial bs c P hP]
  constructor
  · rw [ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) k _ hprob]
    apply binnedPoly_fiber_lower bs value (fun _ => 1) P.coeff
    intro j _
    simpa only [Finset.card_filter] using hcount j
  · rw [ClaudeWCT.Numerics.eval_div_pow_mod (pow_pos (by decide) _) k _ hfirst]
    apply binnedPoly_fiber_lower bs value (fun a => c+value a) (fun j => (c+j)*P.coeff j)
    intro j _
    rw [weighted_fiber_count]
    exact Nat.mul_le_mul_left (c+j) (hcount j)

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial
open ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def weightedHistogram {α : Type} [Fintype α]
    (good : α → Prop) (bin weight : α → Nat) : Nat[X] := by
  classical
  exact ∑ a, if good a then C (weight a)*X^(bin a) else 0

theorem weightedHistogram_coeff {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) (k : Nat) :
    (weightedHistogram good bin weight).coeff k =
      ∑ a, if good a ∧ bin a=k then weight a else 0 := by
  classical
  unfold weightedHistogram
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [if_pos hg, Polynomial.coeff_C_mul_X_pow, hg, if_true, true_and, eq_comm]
  · simp only [if_neg hg, Polynomial.coeff_zero, hg, false_and, if_false]

theorem weightedHistogram_mul {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat) :
    weightedHistogram ga ba wa * weightedHistogram gb bb wb =
      weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
        (fun p => ba p.1+bb p.2) (fun p => wa p.1*wb p.2) := by
  classical
  unfold weightedHistogram
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : ga a <;> by_cases hb : gb b
  · simp only [if_pos ha, if_pos hb, if_pos (And.intro ha hb), Polynomial.C_mul, pow_add]
    ring
  · simp only [if_pos ha, if_neg hb, Nat.cast_id, mul_zero, ha, hb, true_and, if_false]
  · simp only [if_neg ha, zero_mul, ha, false_and, if_false]
  · simp only [if_neg ha, zero_mul, ha, false_and, if_false]

theorem weightedHistogram_product_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat)
    (P Q : Nat[X]) (hP : CoeffLE P (weightedHistogram ga ba wa))
    (hQ : CoeffLE Q (weightedHistogram gb bb wb)) :
    CoeffLE (P*Q) (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
      (fun p => ba p.1+bb p.2) (fun p => wa p.1*wb p.2)) := by
  rw [← weightedHistogram_mul]
  exact CoeffLE.mul _ _ _ _ hP hQ

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem sum_finite_fibers {α β : Type} [Fintype α] [DecidableEq β]
    (s : Finset β) (good : α → Prop) [DecidablePred good]
    (label : α → β) (weight : α → Nat) :
    (∑ b ∈ s, ∑ a, if good a ∧ label a=b then weight a else 0) =
      ∑ a, if good a ∧ label a∈s then weight a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [hg, true_and]
    by_cases hs : label a∈s
    · rw [if_pos hs, Finset.sum_eq_single (label a)]
      · simp only [if_true]
      · intro b _ hb
        exact if_neg (Ne.symm hb)
      · exact fun hn => (hn hs).elim
    · rw [if_neg hs]
      apply Finset.sum_eq_zero
      intro b hb
      exact if_neg (by intro he; exact hs (he ▸ hb))
  · simp only [hg, false_and, if_false, Finset.sum_const_zero]

theorem product_fiber_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (i j : Nat) :
    (∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2=j)
      then wa p.1*wb p.2 else 0) =
      (∑ a, if ga a ∧ ba a=i then wa a else 0) *
      (∑ b, if gb b ∧ bb b=j then wb b else 0) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : ga a ∧ ba a=i <;> by_cases hb : gb b ∧ bb b=j <;>
    simp only [ha, hb, true_and, false_and, and_true, and_false, if_true, if_false,
      Nat.zero_mul, Nat.mul_zero]

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directedFirst_digit (a pref : Cell) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048)
    (hsmall : ∀ j, j<2048 →
      digit (2^1024) a.2 j * digit (2^1024) (window pref.1 lo hi) j +
      digit (2^1024) a.1 j * digit (2^1024) (window pref.2 lo hi) j < 2^1024)
    (i : Nat) (hi' : i<2048) :
    digit (2^1024) (directedFirst a pref lo hi shift) i =
      if shift ≤ i then
        digit (2^1024) a.2 (i-shift) * digit (2^1024) (window pref.1 lo hi) (i-shift) +
        digit (2^1024) a.1 (i-shift) * digit (2^1024) (window pref.2 lo hi) (i-shift)
      else 0 := by
  rw [directedFirst_model _ _ _ _ _ haP haF, digit_low _ _ _ _ hi',
    digit_shift _ _ _ _ (pow_pos (by decide) _)]
  by_cases hs : shift ≤ i
  · rw [if_pos hs, if_pos hs]
    exact digit_packFun _ _ _ (pow_pos (by decide) _) hsmall _ (by omega)
  · rw [if_neg hs, if_neg hs]

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset
open scoped BigOperators
set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

local notation "lowerCount" credit:arg =>
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w ≤ 5 ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = credit).card

local notation "lowerFiber" z:arg credit:arg =>
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w = z ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = credit).card

theorem lower_fibers (credit : Nat) : (∑ z : Fin 6, lowerFiber z.val credit) = lowerCount credit := by
  rw [CanonicalCounting.count_fibers_fin]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  omega

theorem lower_counts_bound (credit : Nat) : 7*lowerCount credit < 2^132 := by
  have h : lowerCount credit ≤ Fintype.card SigGolfResearch.LowerEffectiveCounting.«Word» :=
    Finset.card_filter_le _ _
  have hbound := CanonicalCounting.lower_card_seven
  omega

theorem lower_windows_fold (p : Nat) :
    (List.range 6).foldl (fun s zeros =>
      s + ((p >>> (132*(65536*zeros+128*201))) % 2^(132*128))) 0 =
    ∑ z : Fin 6, p / (2^132)^(65536*z.val+128*201) % (2^132)^128 := by
  have hfold (f : Nat → Nat) : (List.range 6).foldl (fun s z => s+f z) 0 =
      ∑ z : Fin 6, f z.val := by
    simp [List.range_succ, Fin.sum_univ_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hfold]
  apply Finset.sum_congr rfl
  intro z _
  exact shift_window_eq 132 p (65536*z.val+128*201) 128

theorem lower_counts_from_digits (p encoded : Nat)
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) p (65536*z.val+128*201+i) = lowerFiber z.val i)
    (he : encoded = 7*(List.range 6).foldl (fun s zeros =>
      s + ((p >>> (132*(65536*zeros+128*201))) % 2^(132*128))) 0)
    (i : Nat) (hi : i<128) : coefficient 132 encoded i = 7*lowerCount i := by
  have hsum (j : Nat) (hj : j<128) :
      (∑ z : Fin 6, 7*SharedDigitBlock.digit (2^132) p (65536*z.val+128*201+j)) =
        7*lowerCount j := by
    rw [← Finset.mul_sum, ← lower_fibers j]
    apply congrArg (fun n : Nat => 7*n)
    apply Finset.sum_congr rfl
    intro z _
    exact hd z j hj
  have he' : encoded = ∑ z : Fin 6,
      7*(p / (2^132)^(65536*z.val+128*201) % (2^132)^128) := by
    rw [he, lower_windows_fold, Finset.mul_sum]
  rw [coefficient, bits_digit_eq, he']
  exact (SharedDigitBlock.digit_window_sum (2^132) 128 (fun _ : Fin 6 => p)
    (fun z => 65536*z.val+128*201) (fun _ => 7) (by positivity)
    (fun j hj => by rw [hsum j hj]; exact lower_counts_bound j) i hi).trans (hsum i hi)
end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset CanonicalCompression
set_option maxRecDepth 100000

theorem lower_histogram_counts_of_check
    (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
      SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
        (65536*z.val+128*201+i) =
      (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
        SigGolfResearch.LowerEffectiveCounting.zeros w = z.val ∧
        SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
        SigGolfResearch.LowerEffectiveCounting.score w = i).card)
    (hcheck : lowerHistogramCheck = true) (c : Fin 128) :
    7*(univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
      SigGolfResearch.LowerEffectiveCounting.zeros w ≤ 5 ∧
      SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
      SigGolfResearch.LowerEffectiveCounting.score w = c.val).card =
    histogramWeight lowerHistogram c.val := by
  have he : packHistogram 132 0 128 lowerHistogram =
      7*(List.range 6).foldl (fun s zeros => s +
        ((SigGolfResearch.LowerEffectiveCounting.packed >>> (132*(65536*zeros+128*201))) % 2^(132*128))) 0 :=
    by simpa only [lowerHistogramCheck, decide_eq_true_eq] using hcheck
  exact (lower_counts_from_digits _ _ hd he c.val c.isLt).symm.trans (lower_histogram_digits c)
end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem product_filtered_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (wa : α → Nat) (wb : β → Nat) :
    (∑ p : α×β, if ga p.1 ∧ gb p.2 then wa p.1*wb p.2 else 0) =
      (∑ a, if ga a then wa a else 0)*(∑ b, if gb b then wb b else 0) := by
  simpa only [and_true] using product_fiber_sum ga gb (fun _ => 0) wa (fun _ => 0) wb 0 0

theorem cross_filtered_sum {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (wa : α → Nat) (wb : β → Nat) :
    (∑ p : α×β, if ga p.1 ∧ gb p.2 then wa p.1+wb p.2 else 0) =
      (∑ a, if ga a then wa a else 0)*(∑ b, if gb b then 1 else 0) +
      (∑ a, if ga a then 1 else 0)*(∑ b, if gb b then wb b else 0) := by
  have he (p : α×β) :
      (if ga p.1 ∧ gb p.2 then wa p.1+wb p.2 else 0) =
      (if ga p.1 ∧ gb p.2 then wa p.1*1 else 0) +
      (if ga p.1 ∧ gb p.2 then 1*wb p.2 else 0) := by
    by_cases hp : ga p.1 ∧ gb p.2 <;> simp only [hp, true_and, if_true, if_false, mul_one, one_mul, Nat.zero_add]
  simp_rw [he]
  rw [Finset.sum_add_distrib, product_filtered_sum ga gb wa (fun _ => 1),
    product_filtered_sum ga gb (fun _ => 1) wb]

theorem directed_fiber_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (ap af bp bf : Nat → Nat)
    (haP : ∀ i, ap i ≤ ∑ a, if ga a ∧ ba a=i then 1 else 0)
    (haF : ∀ i, af i ≤ ∑ a, if ga a ∧ ba a=i then wa a else 0)
    (hbP : ∀ j, bp j ≤ ∑ b, if gb b ∧ bb b=j then 1 else 0)
    (hbF : ∀ j, bf j ≤ ∑ b, if gb b ∧ bb b=j then wb b else 0)
    (i : Nat) (s : Finset Nat) :
    af i*(∑ j ∈ s, bp j) + ap i*(∑ j ∈ s, bf j) ≤
      ∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2∈s)
        then wa p.1+wb p.2 else 0 := by
  rw [cross_filtered_sum (fun a => ga a ∧ ba a=i) (fun b => gb b ∧ bb b∈s) wa wb]
  apply Nat.add_le_add
  · apply Nat.mul_le_mul (haF i)
    rw [← sum_finite_fibers s gb bb (fun _ => 1)]
    exact Finset.sum_le_sum (fun j _ => hbP j)
  · apply Nat.mul_le_mul (haP i)
    rw [← sum_finite_fibers s gb bb wb]
    exact Finset.sum_le_sum (fun j _ => hbF j)

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open scoped BigOperators Polynomial
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directed_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (a pref : Cell)
    (bp bf : Nat → Nat) (lo hi shift : Nat)
    (haP : a.1 < (2^1024)^2048) (haF : a.2 < (2^1024)^2048)
    (hsmall : ∀ j, j<2048 →
      digit (2^1024) a.2 j * digit (2^1024) (window pref.1 lo hi) j +
      digit (2^1024) a.1 j * digit (2^1024) (window pref.2 lo hi) j < 2^1024)
    (hwinP : ∀ j, j<2048 → digit (2^1024) (window pref.1 lo hi) j =
      if lo≤j then ∑ t ∈ Ico (j-hi) (j-lo+1), bp t else 0)
    (hwinF : ∀ j, j<2048 → digit (2^1024) (window pref.2 lo hi) j =
      if lo≤j then ∑ t ∈ Ico (j-hi) (j-lo+1), bf t else 0)
    (hap : ∀ i, digit (2^1024) a.1 i ≤ ∑ x, if ga x ∧ ba x=i then 1 else 0)
    (haf : ∀ i, digit (2^1024) a.2 i ≤ ∑ x, if ga x ∧ ba x=i then wa x else 0)
    (hbp : ∀ i, bp i ≤ ∑ y, if gb y ∧ bb y=i then 1 else 0)
    (hbf : ∀ i, bf i ≤ ∑ y, if gb y ∧ bb y=i then wb y else 0)
    (k : Nat) (hk : k<2048) :
    digit (2^1024) (directedFirst a pref lo hi shift) k ≤
      (weightedHistogram
        (fun p : α×β => ga p.1 ∧ gb p.2 ∧ bb p.2≤ba p.1 ∧
          lo≤ba p.1-bb p.2 ∧ ba p.1-bb p.2≤hi)
        (fun p => ba p.1+shift) (fun p => wa p.1+wb p.2)).coeff k := by
  rw [directedFirst_digit _ _ _ _ _ haP haF hsmall _ hk, weightedHistogram_coeff]
  by_cases hs : shift≤k
  · rw [if_pos hs, hwinP _ (by omega), hwinF _ (by omega)]
    by_cases hl : lo≤k-shift
    · simp only [if_pos hl]
      apply (directed_fiber_lower ga gb ba wa bb wb _ _ bp bf hap haf hbp hbf
        (k-shift) (Ico (k-shift-hi) (k-shift-lo+1))).trans
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      simp only [Finset.mem_Ico]
      apply propext
      constructor
      · rintro ⟨⟨hga, hba⟩, hgb, hlo, hhi⟩
        refine ⟨⟨hga,hgb,?_,?_,?_⟩,?_⟩ <;> omega
      · rintro ⟨⟨hga,hgb,hj,hlo,hhi⟩,hba⟩
        exact ⟨⟨hga,by omega⟩,hgb,by omega,by omega⟩
    · simp only [if_neg hl, Nat.mul_zero, Nat.zero_add]
      exact Nat.zero_le _
  · rw [if_neg hs]
    exact Nat.zero_le _

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.CanonicalHistogram
open OracleComp OracleSpec ENNReal Finset CanonicalCompression
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.ProducerV5.Canonical
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

variable (hd : ∀ (z : Fin 6) (i : Nat), i<128 →
  SharedDigitBlock.digit (2^132) SigGolfResearch.LowerEffectiveCounting.packed
    (65536*z.val+128*201+i) =
  (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
    SigGolfResearch.LowerEffectiveCounting.zeros w = z.val ∧
    SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
    SigGolfResearch.LowerEffectiveCounting.score w = i).card)
include hd

theorem selected_lower_histogram_card (hcheck : lowerHistogramCheck = true)
    (lay : Layer) (hl : lay ≠ 0) (floor : Nat) (c : Fin 128) (hf : floor ≤ c.val) :
    (univ.filter fun answer : HashOutput => accepted lay floor
      (fun ds => CanonicalPolicy.credit lay ds = c.val) (encodingAnswer lay answer)).card =
      histogramWeight lowerHistogram c.val*2^126 := by
  rw [selected_lower_credit_card lay hl floor c.val hf, ← Nat.mul_assoc,
    Nat.mul_comm _ 7, lower_histogram_counts_of_check hd hcheck c]

theorem selected_lower_histogram_probability (hcheck : lowerHistogramCheck = true)
    (lay : Layer) (hl : lay ≠ 0) (floor : Nat) (c : Fin 128) (hf : floor ≤ c.val) :
    Pr[fun answer => accepted lay floor (fun ds => CanonicalPolicy.credit lay ds = c.val)
      (encodingAnswer lay answer) | ($ᵗ HashOutput : ProbComp HashOutput)] =
      (histogramWeight lowerHistogram c.val : ENNReal)/2^130 := by
  rw [selected_uniform_probability _ _ _ _ (selected_lower_histogram_card hd hcheck lay hl floor c hf)]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256 = 2^130*2^126 by rw [← pow_add]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)
end ClaudeWCT.Numerics.CanonicalHistogram


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_eval_one {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat) :
    (weightedHistogram good bin weight).eval 1 = ∑ a, if good a then weight a else 0 := by
  classical
  unfold weightedHistogram
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : good a
  · simp only [if_pos ha, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, Nat.mul_one]
  · simp only [if_neg ha, Polynomial.eval_zero]

theorem weightedHistogram_mass_le {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (M : Nat) (hM : ∀ a, good a → weight a≤M) :
    (weightedHistogram good bin weight).eval 1 ≤ Fintype.card α*M := by
  rw [weightedHistogram_eval_one]
  calc (∑ a, if good a then weight a else 0) ≤ ∑ _a : α, M := by
         apply Finset.sum_le_sum
         intro a _
         split_ifs with ha
         · exact hM a ha
         · exact Nat.zero_le _
       _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem polynomial_coeff_le_mass (P : Nat[X]) (i : Nat) : P.coeff i ≤ P.eval 1 := by
  have h := ClaudeWCT.Numerics.N600.sum_coeff_le_eval_one P {i}
  simpa only [Finset.sum_singleton] using h

theorem polynomial_mass_mono {P Q : Nat[X]} (h : CoeffLE P Q) :
    P.eval 1≤Q.eval 1 := by
  calc P.eval 1 = ∑ i ∈ P.support, P.coeff i := by
         simp [Polynomial.eval_eq_sum, Polynomial.sum_def]
       _ ≤ ∑ i ∈ P.support, Q.coeff i := Finset.sum_le_sum (fun i _ => h i)
       _ ≤ Q.eval 1 := sum_coeff_le_eval_one Q P.support

theorem histogram_lower_mass_le {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (M : Nat) (hM : ∀ a, good a → weight a≤M) :
    P.eval 1 ≤ Fintype.card α*M :=
  (polynomial_mass_mono hP).trans
    (weightedHistogram_mass_le good bin weight M hM)

theorem histogram_lower_coeff_lt {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (M B : Nat) (hM : ∀ a, good a → weight a≤M) (hB : Fintype.card α*M<B)
    (i : Nat) : P.coeff i<B :=
  (polynomial_coeff_le_mass P i).trans_lt
    ((histogram_lower_mass_le good bin weight P hP M hM).trans_lt hB)

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedMoments
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (K r : Nat) :
    Fintype.card (Fin r → Fin K×β) = (K*563)^r := by
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, hβ]

theorem pair_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r : Nat) :
    Fintype.card (PairHistory β r) = (2*(64*563)^2)^r := by
  simp only [PairHistory, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, hβ,
    mul_pow, pow_two, Nat.mul_assoc]

theorem forest_history_card {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r : Nat) :
    Fintype.card (ForestHistory β r) = alphabetSize^r := by
  simp only [ForestHistory, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    pair_history_card hβ r, hβ]
  rw [← pow_mul, Nat.mul_comm r 4, pow_mul]
  rw [← mul_pow]
  rfl

theorem coordinate_mass_small (K r : Nat) (hK : K≤128) (hr : r≤20) :
    (K*563)^r*(K*563) < 2^384 := by
  have hbase : K*563≤128*563 := Nat.mul_le_mul_right _ hK
  have hp : (K*563)^r≤(128*563)^20 :=
    (Nat.pow_le_pow_left hbase r).trans (Nat.pow_le_pow_right (by decide) hr)
  exact (Nat.mul_le_mul hp hbase).trans_lt (by decide +kernel)

theorem pair_mass_small (r : Nat) (hr : r≤20) :
    (2*(64*563)^2)^r*(2*(64*563)^2) < 2^1024 := by
  have hp := Nat.pow_le_pow_right (n:=2*(64*563)^2) (by decide : 0<2*(64*563)^2) hr
  exact (Nat.mul_le_mul_right _ hp).trans_lt (by decide +kernel)

theorem forest_mass_small (r : Nat) (hr : r≤20) :
    alphabetSize^r*alphabetSize < 2^4096 := by
  have hp := Nat.pow_le_pow_right (n:=alphabetSize) (by decide : 0<alphabetSize) hr
  exact (Nat.mul_le_mul_right _ hp).trans_lt (by decide +kernel)

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset ClaudeWCT.Numerics.N600
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem sum_pair_split {α M : Type*} [Fintype α] [AddCommMonoid M]
    (r : Nat) (F : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → M) :
    (∑ o : Fin r → Fin 2, ∑ A : Fin r → α, ∑ B : Fin r → α,
      F (occ o 0) (occ o 1) (splitRanks o A 0) (splitRanks o B 0)
        (splitRanks o A 1) (splitRanks o B 1)) =
      ∑ t ∈ range (r+1), r.choose t •
        (∑ A₀ : Fin t → α, ∑ B₀ : Fin t → α,
          ∑ A₁ : Fin (r-t) → α, ∑ B₁ : Fin (r-t) → α,
            F t (r-t) A₀ B₀ A₁ B₁) := by
  have hs (o : Fin r → Fin 2) :
      (∑ A : Fin r → α, ∑ B : Fin r → α,
        F (occ o 0) (occ o 1) (splitRanks o A 0) (splitRanks o B 0)
          (splitRanks o A 1) (splitRanks o B 1)) =
        ∑ A₀ : Fin (occ o 0) → α, ∑ B₀ : Fin (occ o 0) → α,
          ∑ A₁ : Fin (occ o 1) → α, ∑ B₁ : Fin (occ o 1) → α,
            F (occ o 0) (occ o 1) A₀ B₀ A₁ B₁ := by
    trans ∑ A : Fin r → α, ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
      F (occ o 0) (occ o 1) (splitRanks o A 0) B₀ (splitRanks o A 1) B₁
    · apply Finset.sum_congr rfl
      intro A _
      exact sum_split_selector o (fun B₀ B₁ =>
        F (occ o 0) (occ o 1) (splitRanks o A 0) B₀ (splitRanks o A 1) B₁)
    · rw [sum_split_selector o (fun A₀ A₁ =>
        ∑ B₀ : Fin (occ o 0) → α, ∑ B₁ : Fin (occ o 1) → α,
          F (occ o 0) (occ o 1) A₀ B₀ A₁ B₁)]
      apply Finset.sum_congr rfl
      intro A₀ _
      rw [Finset.sum_comm]
  simp_rw [hs]
  exact sum_selector_occupancy r (fun t u =>
    ∑ A₀ : Fin t → α, ∑ B₀ : Fin t → α, ∑ A₁ : Fin u → α, ∑ B₁ : Fin u → α,
      F t u A₀ B₀ A₁ B₁)

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_histogram_lower {α : Type} [Fintype α]
    (bs : List Nat) (value weight : α → Nat) (f : Nat → Nat)
    (hf : ∀ i, i<bs.length → f i≤∑ a, if value a=i then weight a else 0) :
    CoeffLE (binnedPoly bs f)
      (weightedHistogram (fun a => value a<bs.length)
        (fun a => bs[value a]?.getD 0) weight) := by
  intro k
  have h := binnedPoly_fiber_lower bs value weight f hf k
  rw [weightedHistogram_coeff]
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : value a<bs.length
  · rw [dif_pos ha]
    simp only [ha, true_and, List.getElem?_eq_getElem ha, Option.getD_some]
  · rw [dif_neg ha]
    simp only [ha, false_and, if_false]

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem packFun_lt (B n : Nat) (f : Nat → Nat) (hB : 0<B)
    (hf : ∀ i, i<n → f i<B) : packFun B n f<B^n := by
  induction n with
  | zero => simp only [packFun, Finset.range_zero, Finset.sum_empty, pow_zero]; exact Nat.zero_lt_one
  | succ n ih =>
    have hp := ih (fun i hi => hf i (by omega))
    have hn : f n+1≤B := hf n (by omega)
    have hm := Nat.mul_le_mul_right (B^n) hn
    simp only [packFun, Finset.sum_range_succ] at hp ⊢
    rw [pow_succ]
    nlinarith

theorem polynomial_eval_packFun (P : Nat[X]) (B n : Nat)
    (hz : ∀ i, n ≤ i → P.coeff i=0) : P.eval B=packFun B n P.coeff := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  unfold packFun
  apply Finset.sum_subset
  · intro i hi
    apply Finset.mem_range.mpr
    have hc := Polynomial.mem_support_iff.mp hi
    by_contra hn
    exact hc (hz i (by omega))
  · intro i _ hi
    have hz : P.coeff i=0 := by
      by_contra hn
      exact hi (Polynomial.mem_support_iff.mpr hn)
    rw [hz, Nat.zero_mul]

theorem polynomial_eval_lt (P : Nat[X]) (B n : Nat) (hB : 0<B)
    (hc : ∀ i, i<n → P.coeff i<B) (hz : ∀ i, n ≤ i → P.coeff i=0) :
    P.eval B<B^n := by
  rw [polynomial_eval_packFun P B n hz]
  exact packFun_lt B n P.coeff hB hc

end ClaudeWCT.Numerics.SharedDigitBlock

namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem binnedPoly_coeff_zero (bs : List Nat) (f : Nat → Nat) (n : Nat)
    (hb : ∀ i : Fin bs.length, bs[i]<n) (j : Nat) (hj : n≤j) :
    (binnedPoly bs f).coeff j=0 := by
  rw [binnedPoly_finite_coeff]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (by have h := hb i; omega)

theorem binnedPoly_eval_lt (bs : List Nat) (f : Nat → Nat) (B n : Nat)
    (hB : 0<B) (hb : ∀ i : Fin bs.length, bs[i]<n)
    (hc : ∀ j, (binnedPoly bs f).coeff j<B) : (binnedPoly bs f).eval B<B^n := by
  exact polynomial_eval_lt _ B n hB (fun j _ => hc j) (binnedPoly_coeff_zero bs f n hb)

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem coordinate_histograms_lower {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card) :
    CoeffLE (binnedPoly bs P.coeff)
      (weightedHistogram (fun a => value a<bs.length) (fun a => bs[value a]?.getD 0) (fun _ => 1)) ∧
    CoeffLE (binnedPoly bs (fun j => j*P.coeff j))
      (weightedHistogram (fun a => value a<bs.length) (fun a => bs[value a]?.getD 0) value) := by
  classical
  constructor
  · apply binnedPoly_histogram_lower
    intro j _
    simpa only [Finset.card_filter] using hP j
  · apply binnedPoly_histogram_lower
    intro j _
    have he := weighted_fiber_count value 0 j
    simp only [Nat.zero_add] at he
    rw [he]
    exact Nat.mul_le_mul_left j (hP j)

theorem coordinate_histograms_mass {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M : Nat) (hM : ∀ a, value a≤M) :
    (binnedPoly bs P.coeff).eval 1≤Fintype.card α ∧
    (binnedPoly bs (fun j => j*P.coeff j)).eval 1≤Fintype.card α*M := by
  have hp := coordinate_histograms_lower bs value P hP
  constructor
  · have h := histogram_lower_mass_le _ _ _ _ hp.1 1 (fun _ _ => le_rfl)
    simpa only [Nat.mul_one] using h
  · exact histogram_lower_mass_le _ _ _ _ hp.2 M (fun a _ => hM a)

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_pi {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] (good : (i : ι) → α i → Prop)
    (bin weight : (i : ι) → α i → Nat) :
    (∏ i, weightedHistogram (good i) (bin i) (weight i)) =
      weightedHistogram (fun a : (i : ι) → α i => ∀ i, good i (a i))
        (fun a => ∑ i, bin i (a i)) (fun a => ∏ i, weight i (a i)) := by
  classical
  unfold weightedHistogram
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ∀ i, good i (a i)
  · rw [if_pos ha]
    simp only [ha, if_true]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  · rw [if_neg ha]
    obtain ⟨i, hi⟩ := not_forall.mp ha
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem polynomial_prod_mono {ι : Type} [DecidableEq ι] (P Q : ι → Nat[X])
    (h : ∀ i, CoeffLE (P i) (Q i)) (s : Finset ι) :
    CoeffLE (∏ i ∈ s, P i) (∏ i ∈ s, Q i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; intro k; exact le_rfl
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact CoeffLE.mul _ _ _ _ (h i) ih

theorem weightedHistogram_pi_lower {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] (good : (i : ι) → α i → Prop)
    (bin weight : (i : ι) → α i → Nat) (P : ι → Nat[X])
    (hP : ∀ i, CoeffLE (P i) (weightedHistogram (good i) (bin i) (weight i))) :
    CoeffLE (∏ i, P i)
      (weightedHistogram (fun a : (i : ι) → α i => ∀ i, good i (a i))
        (fun a => ∑ i, bin i (a i)) (fun a => ∏ i, weight i (a i))) := by
  classical
  rw [← weightedHistogram_pi]
  exact polynomial_prod_mono P _ hP Finset.univ

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem bucket_no_carry {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M : Nat) (hM : ∀ a, value a≤M)
    (hcard : Fintype.card α<2^512) (hmass : Fintype.card α*M<2^1024) :
    bucket bs 0 (P.eval (2^512)) =
      ((binnedPoly bs P.coeff).eval (2^1024),
        (binnedPoly bs (fun j => j*P.coeff j)).eval (2^1024)) ∧
    (∀ j, (binnedPoly bs P.coeff).coeff j<2^1024) ∧
    (∀ j, (binnedPoly bs (fun j => j*P.coeff j)).coeff j<2^1024) := by
  classical
  have hc (j : Nat) : P.coeff j<2^512 := by
    have h := (Finset.card_le_card (Finset.filter_subset (fun a => value a=j) Finset.univ))
    rw [Finset.card_univ] at h
    exact (hP j).trans_lt (h.trans_lt hcard)
  have mass := coordinate_histograms_mass bs value P hP M hM
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.zero_add] using bucket_polynomial bs 0 P hc
  · intro j
    exact (polynomial_coeff_le_mass _ j).trans_lt
      (mass.1.trans_lt (hcard.trans_le (by decide +kernel)))
  · intro j
    exact (polynomial_coeff_le_mass _ j).trans_lt (mass.2.trans_lt hmass)

theorem bucket_histogram_bounds {α : Type} [Fintype α]
    (bs : List Nat) (value : α → Nat) (P : Nat[X])
    (hP : ∀ j, P.coeff j≤(Finset.univ.filter fun a => value a=j).card)
    (M n : Nat) (hM : ∀ a, value a≤M)
    (hcard : Fintype.card α<2^512) (hmass : Fintype.card α*M<2^1024)
    (hbin : ∀ i : Fin bs.length, bs[i]<n) :
    (bucket bs 0 (P.eval (2^512))).1<(2^1024)^n ∧
    (bucket bs 0 (P.eval (2^512))).2<(2^1024)^n := by
  have h := bucket_no_carry bs value P hP M hM hcard hmass
  rw [h.1]
  exact ⟨binnedPoly_eval_lt _ _ _ n (pow_pos (by decide) _) hbin h.2.1,
    binnedPoly_eval_lt _ _ _ n (pow_pos (by decide) _) hbin h.2.2⟩

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem forest_histogram_lower {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat)
    (gp : PairHistory β r → Prop) (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) (bq : (Fin r → Fin 128×β) → Nat)
    (P Q : Nat[X])
    (hP : CoeffLE P (weightedHistogram gp bp (pairCoverage val)))
    (hQ : CoeffLE Q (weightedHistogram gq bq (coordinateCoverage val))) :
    CoeffLE (P^4*Q)
      (weightedHistogram (fun h : ForestHistory β r => (∀ i, gp (h.1 i)) ∧ gq h.2)
        (fun h => (∑ i, bp (h.1 i))+bq h.2) (forestCoverage val)) := by
  classical
  have hpi : CoeffLE (P^4)
      (weightedHistogram (fun h : Fin 4 → PairHistory β r => ∀ i, gp (h i))
        (fun h => ∑ i, bp (h i)) (fun h => ∏ i, pairCoverage val (h i))) := by
    simpa only [Fin.prod_const] using
      weightedHistogram_pi_lower (fun _i : Fin 4 => gp) (fun _ => bp)
        (fun _ => pairCoverage val) (fun _ => P) (fun _ => hP)
  exact weightedHistogram_product_lower _ _ _ _ _ _ _ _ hpi hQ

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (good : β → Prop) (bin weight : β → Nat) :
    weightedHistogram (fun a => good (e a)) (fun a => bin (e a)) (fun a => weight (e a)) =
      weightedHistogram good bin weight := by
  classical
  unfold weightedHistogram
  exact e.sum_comp (fun b => if good b then C (weight b)*X^(bin b) else 0)

theorem weightedHistogram_partition {ι α : Type} [Fintype ι] [Fintype α]
    (piece : ι → α → Prop) (good : α → Prop) (label : ι → α → Nat)
    (bin weight : α → Nat)
    (hgood : ∀ i a, piece i a → good a)
    (hbin : ∀ i a, piece i a → label i a=bin a)
    (huniq : ∀ i j a, piece i a → piece j a → i=j) :
    CoeffLE (∑ i, weightedHistogram (piece i) (label i) weight)
      (weightedHistogram good bin weight) := by
  classical
  intro k
  rw [Polynomial.finsetSum_coeff, weightedHistogram_coeff]
  simp_rw [weightedHistogram_coeff]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hex : ∃ i, piece i a
  · obtain ⟨i,hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · rw [hbin i a hi]
      simp only [hi, hgood i a hi, true_and]
      exact le_rfl
    · intro j _ hji
      have hj : ¬piece j a := fun h => hji (huniq j i a h hi)
      simp only [hj, false_and, if_false]
    · exact fun hn => (hn (Finset.mem_univ i)).elim
  · have hz : (∑ i, if piece i a ∧ label i a=k then weight a else 0)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : ¬piece i a := fun h => hex ⟨i,h⟩
      simp only [hi, false_and, if_false]
    rw [hz]
    exact Nat.zero_le _

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.CanonicalCounting
open scoped BigOperators
open Finset

theorem lower_card : Fintype.card SigGolfResearch.LowerEffectiveCounting.«Word» < 2^132 :=
  Nat.lt_of_lt_of_le SigGolfResearch.LowerEffectiveCounting.word_card_small (Nat.sub_le _ _)

theorem lower_digit (zeros credit : Nat) (hc : credit < 128) :
    digit 132 SigGolfResearch.LowerEffectiveCounting.packed
      (65536*zeros+128*201+credit) =
    (univ.filter fun w : SigGolfResearch.LowerEffectiveCounting.«Word» =>
      SigGolfResearch.LowerEffectiveCounting.zeros w = zeros ∧
      SigGolfResearch.LowerEffectiveCounting.weight w = 201 ∧
      SigGolfResearch.LowerEffectiveCounting.score w = credit).card := by
  exact digit_histogram_of_weighted _ _ _ _ _ lower_card lower_weighted (lower_event zeros credit hc)
end ClaudeWCT.Numerics.CanonicalCounting


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem add_run_bounds (i : Fin addRuns.length) :
    addRuns[i].1 ≤ addRuns[i].2.1 ∧ addRuns[i].2.1<2047 ∧ addRuns[i].2.2 ≤ 70 ∧
    addEndpoint addRuns[i].1 addRuns[i].2.2 ∧ addEndpoint addRuns[i].2.1 addRuns[i].2.2 := by
  have h := List.all_eq_true.mp addRuns_valid addRuns[i] (List.getElem_mem _)
  exact of_decide_eq_true h

theorem add_run_unique (i j : Fin addRuns.length) (d : Nat)
    (hi : addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1)
    (hj : addRuns[j].1 ≤ d ∧ d ≤ addRuns[j].2.1) : i=j := by
  rcases lt_trichotomy i.val j.val with hlt|he|hgt
  · have h := List.pairwise_iff_getElem.mp addRuns_ordered i.val j.val i.isLt j.isLt hlt
    simp only [Fin.getElem_fin] at hi hj
    omega
  · exact Fin.ext he
  · have h := List.pairwise_iff_getElem.mp addRuns_ordered j.val i.val j.isLt i.isLt hgt
    simp only [Fin.getElem_fin] at hi hj
    omega

noncomputable def shiftFor (d : Nat) : Nat :=
  if h : ∃ i : Fin addRuns.length, addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1 then
    addRuns[Classical.choose h].2.2 else 0

theorem shiftFor_eq (i : Fin addRuns.length) (d : Nat)
    (hi : addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1) : shiftFor d=addRuns[i].2.2 := by
  have hex : ∃ i : Fin addRuns.length, addRuns[i].1 ≤ d ∧ d ≤ addRuns[i].2.1 := ⟨i,hi⟩
  rw [shiftFor, dif_pos hex]
  exact congrArg (fun e : Fin addRuns.length => addRuns[e].2.2)
    (add_run_unique (Classical.choose hex) i d (Classical.choose_spec hex) hi)

noncomputable def mergeBin (i j : Nat) : Nat := max i j+shiftFor (i-j+(j-i))

theorem mergeBin_comm (i j : Nat) : mergeBin i j=mergeBin j i := by
  unfold mergeBin
  rw [Nat.max_comm, Nat.add_comm (i-j) (j-i)]

theorem mergeBin_forward (e : Fin addRuns.length) (i j : Nat) (hj : j ≤ i)
    (hlo : addRuns[e].1 ≤ i-j) (hhi : i-j ≤ addRuns[e].2.1) :
    mergeBin i j=i+addRuns[e].2.2 := by
  unfold mergeBin
  rw [Nat.max_eq_left hj, Nat.sub_eq_zero_of_le hj, Nat.add_zero, shiftFor_eq e _ ⟨hlo,hhi⟩]

end ClaudeWCT.Numerics.SharedPathList
