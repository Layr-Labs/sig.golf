import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsSem
import SigGolfCandidate.ClaudeWCT_WCT9_TopDecode
set_option Elab.async false

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.WCT9
set_option maxHeartbeats 1200000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false

private theorem cost_kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q < 17) :
    kss q (c.kOf q) = c.dig (3*q) + c.dig (3*q+1) + c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q (by omega)
  simp only [kss,k1,k2,k3]

private theorem sum_flags (P : Nat → Prop) [DecidablePred P] (L : List Nat) :
    (L.map fun i => if P i then 1 else 0).sum = (L.filter fun i => decide (P i)).length := by
  induction L with
  | nil => simp
  | cons i L ih => by_cases h : P i <;> simp [h, ih, Nat.add_comm]

def bufferCredit (c : NCtx) : Nat :=
  ((List.range 54).map fun i => if c.bufferSafe i then 1 else 0).sum

def exactCredit (c : NCtx) : Nat :=
  ((List.range 54).map fun i => if c.dig i + 1 = topMax i then 1 else 0).sum

def jumps (c : NCtx) : Nat := ((List.range 54).map c.tableJump).sum

theorem bufferSafe_no_jump (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 54)
    (hs : c.bufferSafe i) : c.tableJump i = 0 := by
  obtain ⟨hd, hz | ⟨hp, hmod, hprev⟩⟩ := hs
  · subst i
    have hk := cost_kss_kOf c hds 0 (by decide)
    have hm : topMax 0 = 4 := rfl
    rw [hm] at hd
    simp only [Nat.mul_zero, Nat.zero_add] at hk
    have hsum : 3 ≤ kss 0 (c.kOf 0) := by omega
    simp [tableJump, rowInl, inl, hsum]
  · simp [tableJump, hmod]

theorem chainCost_buffer_balance (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 54) :
    c.chainCost i (c.dig i) + 9*c.dig i +
      (if c.dig i + 1 = topMax i then 1 else 0) +
      4*(if c.bufferSafe i then 1 else 0) = 4 + 9*topMax i + c.tableJump i := by
  have hm := topMax_bounds i
  have hd := hds i hi
  by_cases hs : c.bufferSafe i
  · have hd := hs.1
    have hj := c.bufferSafe_no_jump hds i hi hs
    simp [chainCost, hs, hd, hj, Nat.add_comm]
  · unfold chainCost
    split_ifs <;> omega

theorem chainsCost_buffer_balance (c : NCtx) (hds : c.DigitsOk) :
    c.chainsCost 0 54 + 9*((List.range 54).map c.dig).sum + c.exactCredit + 4*c.bufferCredit =
      2241 + c.jumps := by
  have H : ∀ L : List Nat, (∀ i ∈ L, i < 54) →
      (L.map fun i => c.chainCost i (c.dig i)).sum + 9*(L.map c.dig).sum +
      (L.map fun i => if c.dig i+1=topMax i then 1 else 0).sum +
      4*(L.map fun i => if c.bufferSafe i then 1 else 0).sum =
      (L.map fun i => 4+9*topMax i).sum + (L.map c.tableJump).sum := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih =>
      intro hL
      have hp := c.chainCost_buffer_balance hds i (hL i (by simp))
      have ht := ih (fun j hj => hL j (by simp [hj]))
      simp only [List.map_cons, List.sum_cons]
      omega
  have h := H (List.range 54) (by intro i hi; exact List.mem_range.mp hi)
  have he : ((List.range 54).map fun i => 4+9*topMax i).sum = 2241 := by decide +kernel
  simpa [chainsCost, exactCredit, bufferCredit, jumps, ← List.range_eq_range', he] using h

theorem jumps_source (c : NCtx) (hds : c.DigitsOk) (digits : List Nat)
    (hd : ∀ i, i < 54 → digits.getD i 0 = c.dig i) :
    c.jumps = dispatchPenalty 0 digits := by
  have hg : ∀ q, q < 17 → kss q (c.kOf q) =
      digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 := by
    intro q hq
    rw [cost_kss_kOf c hds q hq, hd _ (by omega), hd _ (by omega), hd _ (by omega)]
  unfold dispatchPenalty topDispatchPenalty
  simp only [ite_true]
  rw [← sum_flags]
  simp [jumps, tableJump, rowInl, inl, hg, List.range_succ, Nat.add_assoc, Nat.not_le]

theorem bufferCredit_source (c : NCtx) (digits : List Nat)
    (hd : ∀ i, i < 54 → digits.getD i 0 = c.dig i) :
    c.bufferCredit = savedCopies 0 digits := by
  unfold bufferCredit savedCopies
  rw [← sum_flags]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi' : i < 54 := List.mem_range.mp hi
  simp only [← c.bufferSafe_source digits hd i hi']

theorem jumps_le_twelve (c : NCtx) : c.jumps ≤ 12 := by
  have h : ∀ i, c.tableJump i ≤
      (if i%3=0 ∧ i<51 ∧ inl (i/3)=false then 1 else 0) := by
    intro i
    unfold tableJump
    by_cases hj : (i%3=0 ∧ i<51) ∧ rowInl (i/3) (c.kOf (i/3))=false
    · rw [if_pos hj]
      have hh : inl (i/3) = false := by
        have hh := hj.2
        simp only [rowInl, Bool.or_eq_false_iff] at hh
        exact hh.1
      simp [hj.1.1, hj.1.2, hh]
    · rw [if_neg hj]
      exact Nat.zero_le _
  have H : ∀ L : List Nat, (L.map c.tableJump).sum ≤
      (L.map fun i => if i%3=0 ∧ i<51 ∧ inl (i/3)=false then 1 else 0).sum := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h i) ih
  have H0 := H (List.range 54)
  have he : ((List.range 54).map fun i => if i%3=0 ∧ i<51 ∧ inl (i/3)=false then 1 else 0).sum=12 := by decide +kernel
  simpa [jumps, he] using H0

theorem chainsCost_any (c : NCtx) (hds : c.DigitsOk) : c.chainsCost 0 54 ≤ 2254 := by
  have hb := c.chainsCost_buffer_balance hds
  have hj := c.jumps_le_twelve
  omega

theorem chainsCost_accepted (c : NCtx) (v : Digest) (digits : List Nat)
    (hdec : decode 0 v = some digits)
    (hd : ∀ i, i < 54 → c.dig i = coreDigit 0 v i) :
    c.chainsCost 0 54 + topCredit v + 4*savedCopies 0 digits = 927 + dispatchPenalty 0 digits := by
  have hsome := decode_top_some hdec
  have hsource : ∀ i, i < 54 → digits.getD i 0 = c.dig i := by
    intro i hi
    rw [hsome.2.2.2, dataDigits_getD 0 v i hi, hd i hi]
  have hm : ∀ i, maxDigit 0 i = topMax i := by
    intro i
    simp [maxDigit, topMax, mx]
    split_ifs <;> omega
  have hds : c.DigitsOk := by
    intro i hi
    rw [hd i hi, ← hm]
    exact T3.Nonbinary.coreDigit_le 0 v i
  have hsum : ((List.range 54).map c.dig).sum = 146 := by
    have he : (List.range 54).map c.dig = dataDigits 0 v := by
      unfold dataDigits
      apply List.map_congr_left
      intro i hi
      exact hd i (List.mem_range.mp hi)
    rw [he]
    exact hsome.2.2.1
  have hcr : c.exactCredit = topCredit v := by
    unfold exactCredit topCredit
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    rw [hd i (List.mem_range.mp hi)]
    have hm := topMax_bounds i
    unfold topMax mx
    split_ifs <;> congr 1 <;> omega
  have hb := c.chainsCost_buffer_balance hds
  rw [hsum, hcr, c.bufferCredit_source digits hsource, c.jumps_source hds digits hsource] at hb
  omega

end SigGolfCandidate.T3M.Nonbinary.NCtx
