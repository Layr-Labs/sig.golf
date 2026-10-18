import SigGolfCandidate.T3.Core
import SigGolfCandidate.Choice.Gated


namespace SigGolfCandidate.T3
theorem lowerWord_lt (v : Digest) : lowerWord v < 2 ^ 126 := by
  unfold lowerWord
  have := v.isLt
  norm_num at *
  omega
theorem lowerPack_toNat (n : Nat) :
    (lowerPack n).toNat = n % 2 ^ 63 + 2 ^ 63 + n / 2 ^ 63 % 2 ^ 63 * 2 ^ 64 + 2 ^ 127 := by
  unfold lowerPack
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num
  omega
theorem lowerSpare_lowerPack (n : Nat) : lowerSpare (lowerPack n) := by
  unfold lowerSpare
  rw [lowerPack_toNat]
  norm_num
  omega
theorem lowerWord_lowerPack {n : Nat} (hn : n < 2 ^ 126) : lowerWord (lowerPack n) = n := by
  unfold lowerWord
  rw [lowerPack_toNat]
  norm_num at *
  omega
theorem lowerPack_lowerWord {v : Digest} (hv : lowerSpare v) : lowerPack (lowerWord v) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [lowerPack_toNat]
  unfold lowerWord
  unfold lowerSpare at hv
  have := v.isLt
  norm_num at *
  omega
theorem testBit_lowerWord (v : Digest) (j : Nat) :
    (lowerWord v).testBit j =
      if j < 63 then v.toNat.testBit j else (decide (j < 126) && v.toNat.testBit (j + 1)) := by
  have h : lowerWord v = 2 ^ 63 * (v.toNat / 2 ^ 64 % 2 ^ 63) + v.toNat % 2 ^ 63 := by unfold lowerWord; ring
  rw [h, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity))]
  split_ifs with hj
  · rw [Nat.testBit_mod_two_pow]; simp [hj]
  · simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    rw [show j - 63 + 64 = j + 1 by omega]
    congr 1
    simp only [decide_eq_decide]
    omega
theorem lowerShift_digit (v : Digest) {i : Nat} (hi : i < 42) :
    v.toNat / 2 ^ lowerShift i % 8 = lowerWord v / 2 ^ (3 * i) % 8 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, testBit_lowerWord]
  by_cases hb : b < 3
  · simp only [hb, decide_true, Bool.true_and]
    unfold lowerShift
    split_ifs with h1 h2 h2
    · rw [Nat.add_comm]
    · omega
    · omega
    · simp only [show b + 3 * i < 126 by omega, decide_true, Bool.true_and]
      congr 1
      omega
  · simp [hb]
theorem coreDigit_lower {lay : Layer} (hl : lay ≠ 0) (v : Digest) {i : Nat} (hi : i < 42) :
    coreDigit lay v i = lowerWord v / 2 ^ (3 * i) % 8 := by
  simp only [coreDigit, hl, if_false]
  exact lowerShift_digit v hi
theorem dataDigits_lowerWord {lay : Layer} (hl : lay ≠ 0) (v : Digest) :
    dataDigits lay v = (List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8 := by
  simp only [dataDigits, dataCount, hl, if_false]
  apply List.map_congr_left
  intro i hi
  exact coreDigit_lower hl v (List.mem_range.mp hi)
theorem decode_lowerWord {lay : Layer} (hl : lay ≠ 0) (v : Digest) :
    decode lay v =
      let digits := (List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8
      if lowerSpare v ∧ digits.sum ≤ target lay ∧ target lay - digits.sum < 8 then
        some (digits ++ [target lay - digits.sum])
      else none := by
  have hb : ¬ v.toNat ≥ 2 ^ encodedBits lay := by
    simp only [encodedBits, hl, if_false]; have := v.isLt; omega
  unfold decode
  rw [if_neg hb, dataDigits_lowerWord hl v]
  simp only [hl, if_false]
def lowerSpareEquiv : {v : Digest // lowerSpare v} ≃ Fin (2 ^ 126) where
  toFun v := ⟨lowerWord v.val, lowerWord_lt v.val⟩
  invFun n := ⟨lowerPack n.val, lowerSpare_lowerPack n.val⟩
  left_inv v := Subtype.ext (lowerPack_lowerWord v.property)
  right_inv n := Fin.ext (lowerWord_lowerPack n.isLt)
theorem card_lowerSpare_filter (P : Nat → Prop) [DecidablePred P] :
    (Finset.univ.filter fun v : Digest => lowerSpare v ∧ P (lowerWord v)).card =
      (Finset.univ.filter fun v : Digest => v.toNat < 2 ^ 126 ∧ P v.toNat).card := by
  classical
  refine Finset.card_bij (fun v _ => BitVec.ofNat 128 (lowerWord v)) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have h := lowerWord_lt v
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h.trans (by norm_num))]
    exact ⟨h, hv.2⟩
  · intro a ha b hb he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have h := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((lowerWord_lt a).trans (by norm_num)),
      Nat.mod_eq_of_lt ((lowerWord_lt b).trans (by norm_num))] at h
    rw [← lowerPack_lowerWord ha.1, ← lowerPack_lowerWord hb.1, h]
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨lowerPack w.toNat, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lowerSpare_lowerPack _, by rw [lowerWord_lowerPack hw.1]; exact hw.2⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, lowerWord_lowerPack hw.1, Nat.mod_eq_of_lt w.isLt]
end SigGolfCandidate.T3

namespace SigGolfCandidate.T3.DualHalf
open SigGolfCandidate.T3 Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000

def selectPair (p : Digest × Digest) : Digest := if lowerSpare p.1 then p.1 else p.2

theorem card_mode {α : Type} [Fintype α] [DecidableEq α]
    (spare lo hi : α → Prop) [DecidablePred spare] [DecidablePred lo] [DecidablePred hi]
    (hlo : ∀ x, lo x → spare x) :
    (univ.filter fun p : α × α => if spare p.1 then lo p.1 else hi p.2).card =
      (univ.filter lo).card * Fintype.card α +
        (univ.filter fun x => ¬ spare x).card * (univ.filter hi).card := by
  classical
  have he : (univ.filter fun p : α × α => if spare p.1 then lo p.1 else hi p.2) =
      ((univ.filter lo) ×ˢ (univ : Finset α)) ∪
        ((univ.filter fun x => ¬spare x) ×ˢ (univ.filter hi)) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_product, and_true]
    by_cases h : spare p.1
    · simp [h]
    · simp [h, show ¬lo p.1 from fun hl => h (hlo _ hl)]
  rw [he, card_union_of_disjoint, card_product, card_product, card_univ]
  exact disjoint_left.mpr fun p hp hq => by
    have hl : lo p.1 := (mem_filter.mp (mem_product.mp hp).1).2
    have hn : ¬spare p.1 := (mem_filter.mp (mem_product.mp hq).1).2
    exact hn (hlo _ hl)

theorem card_spare : (univ.filter lowerSpare).card = 2 ^ 126 := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr SigGolfCandidate.T3.lowerSpareEquiv).trans (Fintype.card_fin _)

theorem card_compl_generic {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (univ.filter fun v => ¬p v).card = Fintype.card α - (univ.filter p).card := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) p
  simp only [card_univ] at h
  omega

theorem card_not_spare : (univ.filter fun v : Digest => ¬lowerSpare v).card = 3 * 2 ^ 126 := by
  calc
    _ = Fintype.card Digest - (univ.filter lowerSpare).card := card_compl_generic lowerSpare
    _ = 2^128 - 2^126 := congrArg₂ (fun x y : Nat => x - y) (Fintype.card_bitVec 128) card_spare
    _ = _ := by norm_num

theorem card_mode_lower (lo hi : Digest → Prop) [DecidablePred lo] [DecidablePred hi]
    (hlo : ∀ d, lo d → lowerSpare d) :
    (univ.filter fun p : Digest × Digest => if lowerSpare p.1 then lo p.1 else hi p.2).card =
      (univ.filter lo).card * 2 ^ 128 + 3 * 2 ^ 126 * (univ.filter hi).card := by
  rw [card_mode lowerSpare lo hi hlo, card_not_spare, Fintype.card_bitVec]

theorem card_select_generic {α : Type} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (d : α) (hd : p d) :
    (univ.filter fun x : α × α => (if p x.1 then x.1 else x.2) = d).card =
      Fintype.card α + (univ.filter fun x => ¬p x).card := by
  classical
  have h := card_mode p (· = d) (· = d) (fun x hx => hx ▸ hd)
  have he : (univ.filter fun x : α × α => (if p x.1 then x.1 else x.2) = d) =
      (univ.filter fun x : α × α => if p x.1 then x.1 = d else x.2 = d) := by
    apply Finset.filter_congr
    intro x hx
    split_ifs <;> rfl
  rw [he]
  have hu : (univ.filter fun x : α => x = d) = {d} := by
    ext x
    simp
  rw [hu, card_singleton, Nat.one_mul, Nat.mul_one] at h
  exact h

theorem card_selectPair_eq (d : Digest) (hd : lowerSpare d) :
    (univ.filter fun p : Digest × Digest => selectPair p = d).card = 7 * 2 ^ 126 := by
  change (univ.filter fun p : Digest × Digest => (if lowerSpare p.1 then p.1 else p.2) = d).card = _
  calc
    _ = Fintype.card Digest + (univ.filter fun v : Digest => ¬lowerSpare v).card :=
      card_select_generic lowerSpare d hd
    _ = 2^128 + 3*2^126 := congrArg₂ (fun x y : Nat => x+y) (Fintype.card_bitVec 128) card_not_spare
    _ = _ := by norm_num
def select (a : HashOutput) : Digest :=
  selectPair (a.extractLsb' 0 128, a.extractLsb' 128 128)

theorem card_select_eq (d : Digest) (hd : lowerSpare d) :
    (univ.filter fun a : HashOutput => select a = d).card = 7 * 2 ^ 126 := by
  calc
    _ = (univ.filter fun p : Digest × Digest => selectPair p = d).card := by
      refine Finset.card_equiv (SphincsSecurity.splitHashOutputEquiv 128 (by decide)) fun a => ?_
      simp only [mem_filter, mem_univ, true_and]
      rfl
    _ = _ := card_selectPair_eq d hd

theorem card_select_pred (p : Digest → Prop) [DecidablePred p]
    (hp : ∀ d, p d → lowerSpare d) :
    (univ.filter fun a : HashOutput => p (select a)).card =
      (univ.filter p).card * (7 * 2^126) := by
  have he : (univ.filter fun a : HashOutput => p (select a)).card =
      (univ.filter fun x : Digest × Digest => if lowerSpare x.1 then p x.1 else p x.2).card := by
    refine Finset.card_equiv (SphincsSecurity.splitHashOutputEquiv 128 (by decide)) fun a => ?_
    simp only [mem_filter, mem_univ, true_and]
    change p (if lowerSpare (a.extractLsb' 0 128) then a.extractLsb' 0 128 else a.extractLsb' 128 128) ↔
      (if lowerSpare (a.extractLsb' 0 128) then p (a.extractLsb' 0 128) else p (a.extractLsb' 128 128))
    split_ifs <;> rfl
  rw [he, card_mode_lower p p hp]
  ring

end SigGolfCandidate.T3.DualHalf


namespace SigGolfCandidate.T3.TopDualHalf
open SigGolfCandidate.T3 Finset
set_option maxHeartbeats 100000
set_option maxRecDepth 1000

/-- Prefer the low hash half when its most significant bit is set. -/
def gate (v : Digest) : Prop := 2 ^ 127 ≤ v.toNat
instance (v : Digest) : Decidable (gate v) := inferInstanceAs (Decidable (2 ^ 127 ≤ v.toNat))
theorem gate_iff_getLsbD (v : Digest) : gate v ↔ v.getLsbD 127 = true := by
  have h : v.getLsbD 127 = decide (2 ^ 127 ≤ v.toNat) := BitVec.getLsbD_last v
  rw [h]
  simp only [gate, decide_eq_true_eq]
def selectPair (p : Digest × Digest) : Digest := if gate p.1 then p.1 else p.2
def select (a : HashOutput) : Digest :=
  selectPair (a.extractLsb' 0 128, a.extractLsb' 128 128)

def gateWord (v : Digest) : Nat := v.toNat % 2 ^ 127
def gatePack (n : Nat) : Digest := BitVec.ofNat 128 (n % 2 ^ 127 + 2 ^ 127)
theorem gateWord_lt (v : Digest) : gateWord v < 2 ^ 127 := Nat.mod_lt _ (by decide)
theorem gatePack_toNat (n : Nat) : (gatePack n).toNat = n % 2 ^ 127 + 2 ^ 127 := by
  unfold gatePack
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num
  omega
theorem gate_gatePack (n : Nat) : gate (gatePack n) := by
  unfold gate
  rw [gatePack_toNat]
  omega
theorem gateWord_gatePack {n : Nat} (hn : n < 2 ^ 127) : gateWord (gatePack n) = n := by
  unfold gateWord
  rw [gatePack_toNat]
  norm_num at *
  omega
theorem gatePack_gateWord {v : Digest} (hv : gate v) : gatePack (gateWord v) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [gatePack_toNat]
  unfold gateWord
  unfold gate at hv
  have := v.isLt
  norm_num at *
  omega
def gateEquiv : {v : Digest // gate v} ≃ Fin (2 ^ 127) where
  toFun v := ⟨gateWord v.val, gateWord_lt v.val⟩
  invFun n := ⟨gatePack n.val, gate_gatePack n.val⟩
  left_inv v := Subtype.ext (gatePack_gateWord v.property)
  right_inv n := Fin.ext (gateWord_gatePack n.isLt)
theorem card_gate : (univ.filter gate).card = 2 ^ 127 := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr gateEquiv).trans (Fintype.card_fin _)
theorem card_not_gate : (univ.filter fun v : Digest => ¬gate v).card = 2 ^ 127 := by
  calc
    _ = Fintype.card Digest - (univ.filter gate).card := DualHalf.card_compl_generic gate
    _ = 2^128 - 2^127 := congrArg₂ (fun x y : Nat => x - y) (Fintype.card_bitVec 128) card_gate
    _ = _ := by norm_num

/-- Exact selected-half count; accepted low words with their high bit set get preference. -/
theorem card_select_pred (p : Digest → Prop) [DecidablePred p] :
    (univ.filter fun a : HashOutput => p (select a)).card =
      (univ.filter fun d => p d ∧ gate d).card * 2 ^ 128 +
        2 ^ 127 * (univ.filter p).card := by
  have he : (univ.filter fun a : HashOutput => p (select a)).card =
      (univ.filter fun x : Digest × Digest => if gate x.1 then p x.1 ∧ gate x.1 else p x.2).card := by
    refine Finset.card_equiv (SphincsSecurity.splitHashOutputEquiv 128 (by decide)) fun a => ?_
    simp only [mem_filter, mem_univ, true_and]
    change p (if gate (a.extractLsb' 0 128) then a.extractLsb' 0 128 else a.extractLsb' 128 128) ↔
      (if gate (a.extractLsb' 0 128) then p (a.extractLsb' 0 128) ∧ gate (a.extractLsb' 0 128) else p (a.extractLsb' 128 128))
    by_cases h : gate (a.extractLsb' 0 128)
    · rw [if_pos h, if_pos h]
      exact ⟨fun hp => ⟨hp, h⟩, fun hp => hp.1⟩
    · rw [if_neg h, if_neg h]
  rw [he, DualHalf.card_mode gate (fun d => p d ∧ gate d) p (fun _ h => h.2),
    card_not_gate, Fintype.card_bitVec]

theorem card_select_pred_le (p : Digest → Prop) [DecidablePred p] :
    (univ.filter fun a : HashOutput => p (select a)).card ≤
      (univ.filter p).card * (7 * 2 ^ 126) := by
  rw [card_select_pred]
  have hc : (univ.filter fun d => p d ∧ gate d).card ≤ (univ.filter p).card := by
    apply Finset.card_le_card
    intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2.1⟩
  calc _ ≤ (univ.filter p).card * 2 ^ 128 + 2 ^ 127 * (univ.filter p).card := by omega
    _ ≤ _ := by omega

end SigGolfCandidate.T3.TopDualHalf


/-! ### Restricted top-half choice (ChoiceHint, configuration (1)+(2))
The top encoding answer is a 256-bit hash output with halves LOW (bits 0..127) and HIGH (bits 128..255).
LOW is *forced* (`blocked`) when its two top bits 126, 127 are both 0 (`LOW < 2^126`). Otherwise the witness
hint bit (bit 4 of the witness byte at rel 22312) selects HIGH. The producer prefers LOW and falls back to HIGH when
LOW fails its predicate and is not forced (`choose`). The verifier reads `read hint` for an arbitrary hint. -/
namespace SigGolfCandidate.T3.TopChoice
open SigGolfCandidate.T3 Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- LOW is forced: bits 126 and 127 of LOW are both zero. -/
def blocked (low : Digest) : Prop := low.toNat < 2 ^ 126
instance (low : Digest) : Decidable (blocked low) := inferInstanceAs (Decidable (low.toNat < 2 ^ 126))
def blockedSet : Finset Digest := univ.filter blocked
/-- Low and high halves of a hash output. -/
def lowHalf (a : HashOutput) : Digest := a.extractLsb' 0 128
def highHalf (a : HashOutput) : Digest := a.extractLsb' 128 128

/-- Verifier read of the top answer for the witness hint `high`: HIGH only when requested and LOW is not
forced. -/
def read (high : Bool) (a : HashOutput) : Digest :=
  if high = true ∧ ¬ blocked (lowHalf a) then highHalf a else lowHalf a
/-- The verifier selected the LOW half. -/
def readLow (high : Bool) (a : HashOutput) : Bool := !(high && !decide (blocked (lowHalf a)))
/-- Producer choice for the acceptance predicate `good`: LOW when it is good or forced, else HIGH. -/
def choose (good : Digest → Prop) [DecidablePred good] (a : HashOutput) : Digest :=
  if good (lowHalf a) ∨ blocked (lowHalf a) then lowHalf a else highHalf a
/-- The producer's (honest) hint: request HIGH exactly when the producer chose it. -/
def chooseHigh (good : Digest → Prop) [DecidablePred good] (a : HashOutput) : Bool :=
  !decide (good (lowHalf a) ∨ blocked (lowHalf a))

theorem blocked_iff_bits (low : Digest) :
    blocked low ↔ low.toNat / 2 ^ 126 = 0 := by
  unfold blocked
  constructor
  · intro h; exact Nat.div_eq_of_lt h
  · intro h
    have := Nat.lt_of_div_eq_zero (by positivity) h
    exact this

theorem read_chooseHigh (good : Digest → Prop) [DecidablePred good] (a : HashOutput) :
    read (chooseHigh good a) a = choose good a := by
  unfold read chooseHigh choose
  by_cases hg : good (lowHalf a) <;> by_cases hb : blocked (lowHalf a) <;> simp [hg, hb]

theorem readLow_chooseHigh (good : Digest → Prop) [DecidablePred good] (a : HashOutput) :
    readLow (chooseHigh good a) a = decide (good (lowHalf a) ∨ blocked (lowHalf a)) := by
  unfold readLow chooseHigh
  by_cases hg : good (lowHalf a) <;> by_cases hb : blocked (lowHalf a) <;> simp [hg, hb]

theorem read_eq (high : Bool) (a : HashOutput) :
    read high a = if readLow high a then lowHalf a else highHalf a := by
  unfold read readLow
  cases high <;> by_cases hb : blocked (lowHalf a) <;> simp [hb]

theorem read_false (a : HashOutput) : read false a = lowHalf a := by simp [read]
theorem readLow_false (a : HashOutput) : readLow false a = true := by simp [readLow]
theorem read_blocked (high : Bool) {a : HashOutput} (h : blocked (lowHalf a)) : read high a = lowHalf a := by
  simp [read, h]
theorem readLow_blocked (high : Bool) {a : HashOutput} (h : blocked (lowHalf a)) : readLow high a = true := by
  simp [readLow, h]

theorem choose_of_good (good : Digest → Prop) [DecidablePred good] {a : HashOutput} (h : good (lowHalf a)) :
    choose good a = lowHalf a := by simp [choose, h]

theorem card_blocked : blockedSet.card = 2 ^ 126 := by
  have hc : blockedSet.card = (Finset.range (2 ^ 126)).card := by
    apply Finset.card_bij (fun v _ => v.toNat)
    · intro v hv
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hv).2
    · intro a _ b _ h
      exact BitVec.eq_of_toNat_eq h
    · intro n hn
      have hn' := Finset.mem_range.mp hn
      have hb : n < 2 ^ 128 := hn'.trans (by norm_num)
      refine ⟨BitVec.ofNat 128 n, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change (BitVec.ofNat 128 n).toNat < 2 ^ 126
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] using hn'
      · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  simpa only [Finset.card_range] using hc

/-- The split of a hash output into (LOW, HIGH). -/
noncomputable def splitEquiv : HashOutput ≃ Digest × Digest :=
  SphincsSecurity.splitHashOutputEquiv 128 (by decide)

theorem splitEquiv_apply (a : HashOutput) : splitEquiv a = (lowHalf a, highHalf a) := rfl

/-- Every read (for any hint, possibly chosen after seeing the whole answer) lies in the gated accepted set. -/
theorem read_mem_accepted (targets : Finset Digest) (high : Bool) (a : HashOutput)
    (h : read high a ∈ targets) : splitEquiv a ∈ Choice.Gated.accepted targets blockedSet := by
  rw [Choice.Gated.mem_accepted, splitEquiv_apply]
  unfold read at h
  split_ifs at h with hc
  · exact Or.inr ⟨fun hb => hc.2 (Finset.mem_filter.mp hb).2, h⟩
  · exact Or.inl h

/-- The 7/4 point-mass bound: the witness hint may depend on the complete hash answer. -/
theorem card_read_le (targets : Finset Digest) (hint : HashOutput → Bool) :
    (univ.filter fun a => read (hint a) a ∈ targets).card ≤ targets.card * (7 * 2 ^ 126) := by
  have hq := Choice.Gated.quarter_upper targets blockedSet (2 ^ 126)
    (by rw [Fintype.card_bitVec]; norm_num) card_blocked
  calc _ ≤ (univ.filter fun a : HashOutput => splitEquiv a ∈ Choice.Gated.accepted targets blockedSet).card :=
        Finset.card_le_card (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          read_mem_accepted targets (hint a) a (Finset.mem_filter.mp ha).2⟩)
    _ = (Choice.Gated.accepted targets blockedSet).card := by
        refine Finset.card_equiv splitEquiv fun a => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ ≤ _ := hq

/-- The union over all hints. -/
theorem card_read_exists_le (targets : Finset Digest) :
    (univ.filter fun a => ∃ high : Bool, read high a ∈ targets).card ≤ targets.card * (7 * 2 ^ 126) := by
  classical
  let hint : HashOutput → Bool := fun a => decide (read true a ∈ targets)
  refine le_trans (Finset.card_le_card ?_) (card_read_le targets hint)
  intro a ha
  obtain ⟨high, hh⟩ := (Finset.mem_filter.mp ha).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_cases ht : read true a ∈ targets
  · simpa [hint, ht] using ht
  · have hf : read false a ∈ targets := by cases high <;> simp_all
    simpa [hint, ht] using hf

/-- Number of LOW words that are neither good nor forced (each lets HIGH through). -/
def freeCount (good : Digest → Prop) [DecidablePred good] : Nat :=
  (univ.filter fun v : Digest => ¬ (good v ∨ blocked v)).card

theorem freeCount_add (good : Digest → Prop) [DecidablePred good] :
    freeCount good + (univ.filter fun v : Digest => good v ∧ ¬ blocked v).card = 3 * 2 ^ 126 := by
  have hc : freeCount good = Fintype.card Digest - (univ.filter fun v : Digest => good v ∨ blocked v).card :=
    DualHalf.card_compl_generic (fun v : Digest => good v ∨ blocked v)
  have hu : (univ.filter fun v : Digest => good v ∨ blocked v) =
      blockedSet ∪ (univ.filter fun v : Digest => good v ∧ ¬ blocked v) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, blockedSet]
    by_cases hb : blocked v
    · exact ⟨fun _ => Or.inl hb, fun _ => Or.inr hb⟩
    · exact ⟨fun h => Or.inr ⟨h.resolve_right hb, hb⟩, fun h => h.elim (fun h' => absurd h' hb) (fun h' => Or.inl h'.1)⟩
  have hd : Disjoint blockedSet (univ.filter fun v : Digest => good v ∧ ¬ blocked v) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2
  have hle : (univ.filter fun v : Digest => good v ∨ blocked v).card ≤ Fintype.card Digest :=
    Finset.card_le_univ _
  rw [hu, Finset.card_union_of_disjoint hd, card_blocked] at hc hle
  rw [Fintype.card_bitVec] at hc hle
  omega

/-- Exact producer selection count: every good LOW is kept; a free LOW lets HIGH through. -/
theorem card_choose_pred (good : Digest → Prop) [DecidablePred good] (p : Digest → Prop) [DecidablePred p]
    (hp : ∀ d, p d → good d) :
    (univ.filter fun a : HashOutput => p (choose good a)).card =
      (univ.filter p).card * (2 ^ 128 + freeCount good) := by
  have he : (univ.filter fun a : HashOutput => p (choose good a)).card =
      (univ.filter fun x : Digest × Digest => if good x.1 ∨ blocked x.1 then p x.1 else p x.2).card := by
    refine Finset.card_equiv splitEquiv fun a => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, splitEquiv_apply]
    unfold choose
    split_ifs <;> rfl
  rw [he, DualHalf.card_mode (fun v => good v ∨ blocked v) p p (fun d h => Or.inl (hp d h)),
    Fintype.card_bitVec]
  unfold freeCount
  ring

/-- Selection count with the forced-set complement made explicit. -/
theorem card_choose_pred_eq (good : Digest → Prop) [DecidablePred good] (p : Digest → Prop) [DecidablePred p]
    (hp : ∀ d, p d → good d) (K : Nat) (hK : (univ.filter fun v : Digest => good v ∧ ¬ blocked v).card = K) :
    (univ.filter fun a : HashOutput => p (choose good a)).card =
      (univ.filter p).card * (2 ^ 128 + 3 * 2 ^ 126 - K) := by
  rw [card_choose_pred good p hp]
  have := freeCount_add good
  rw [hK] at this
  have hK' : K ≤ 3 * 2 ^ 126 := by rw [← this]; exact Nat.le_add_left _ _
  rw [Nat.eq_sub_of_add_eq this, Nat.add_sub_assoc hK']

end SigGolfCandidate.T3.TopChoice

#print axioms SigGolfCandidate.T3.TopChoice.card_read_le
#print axioms SigGolfCandidate.T3.TopChoice.card_choose_pred_eq
