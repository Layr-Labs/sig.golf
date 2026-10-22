import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsSem
import SigGolfCandidate.ClaudeWCT_WCT9_TopDecode

namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.WCT9
set_option maxHeartbeats 1200000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false

private theorem cost_kss_kOf (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q < 16) :
    kss q (c.kOf q) = c.dig (3*q) + c.dig (3*q+1) + c.dig (3*q+2) := by
  obtain ⟨k1,k2,k3⟩ := c.kdig_kOf hds q hq
  simp only [kss,k1,k2,k3]

private theorem sum_flags (P : Nat → Prop) [DecidablePred P] (L : List Nat) :
    (L.map fun i => if P i then 1 else 0).sum = (L.filter fun i => decide (P i)).length := by
  induction L with
  | nil => simp
  | cons i L ih => by_cases h : P i <;> simp [h, ih, Nat.add_comm]

def bufferCredit (c : NCtx) : Nat :=
  ((List.range 51).map fun i => if c.bufferSafe i then 1 else 0).sum

def exactCredit (c : NCtx) : Nat :=
  ((List.range 51).map fun i => if c.dig i + 1 = topMax i then 1 else 0).sum

def jumps (c : NCtx) : Nat := ((List.range 51).map c.tableJump).sum

theorem chainCost_buffer_balance (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i < 51) :
    c.chainCost i (c.dig i) + 9*c.dig i +
      (if c.dig i + 1 = topMax i then 1 else 0) +
      4*(if c.bufferSafe i then 1 else 0) = 4 + 9*topMax i + c.tableJump i := by
  have hm := topMax_bounds i
  have hd := hds i (by omega)
  by_cases hs : c.bufferSafe i
  · have hd := hs.1
    simp [chainCost, hs, hd]
    omega
  · unfold chainCost
    split_ifs <;> omega

private theorem sum_map_add (L : List Nat) (f g : Nat → Nat) :
    (L.map fun i => f i + g i).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Campaign T51: the 51 chains' capacity is `4·51 + 9·236 = 2328` plus the table jumps. -/
theorem chainsCost_buffer_balance (c : NCtx) (hds : c.DigitsOk) :
    c.chainsCost 0 51 + 9*((List.range 51).map c.dig).sum + c.exactCredit + 4*c.bufferCredit =
      2328 + c.jumps := by
  have H : ∀ L : List Nat, (∀ i ∈ L, i < 51) →
      (L.map fun j => c.chainCost j (c.dig j)).sum + 9*(L.map c.dig).sum +
        (L.map fun i => if c.dig i + 1 = topMax i then 1 else 0).sum +
        4*(L.map fun i => if c.bufferSafe i then 1 else 0).sum =
      (L.map fun i => 4 + 9*topMax i).sum + (L.map c.tableJump).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons i L ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 := c.chainCost_buffer_balance hds i (hL i (by simp))
      have h2 := ih (fun j hj => hL j (by simp [hj]))
      omega
  have hcap : ((List.range 51).map fun i => 4 + 9*topMax i).sum = 2328 := by decide +kernel
  have := H (List.range 51) (fun i hi => List.mem_range.mp hi)
  rw [hcap] at this
  unfold chainsCost exactCredit bufferCredit jumps
  rw [List.range'_eq_map_range, List.map_map]
  simp only [Function.comp_def, Nat.zero_add]
  exact this

private theorem sum_range_three' (f : Nat → Nat) (n : Nat) :
    ((List.range (3*n)).map f).sum = ((List.range n).map fun q => f (3*q) + f (3*q+1) + f (3*q+2)).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1) = 3*n+1+1+1 by ring, List.range_succ, List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih,
      Nat.add_assoc, Nat.reduceAdd]
    omega

/-- Campaign T51: the r6 groups 0..8 and the r7 pair (group 16) always take their table jump; of the kept r5 groups
only the penalised rows 10, 11, 12 can (digit sum below 3); the checksum chain 50 never does. -/
theorem jumps_source (c : NCtx) (hds : c.DigitsOk) (digits : List Nat)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.jumps = 10 + dispatchPenalty 0 digits := by
  have h51 : c.jumps = ((List.range (3*17)).map c.tableJump).sum := rfl
  have hq : ∀ q ∈ List.range 17, c.tableJump (3*q) + c.tableJump (3*q+1) + c.tableJump (3*q+2) =
      (if q < 9 ∨ q = 16 then 1 else 0) +
        (if (q = 10 ∨ q = 11 ∨ q = 12) ∧
          digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 < 3 then 1 else 0) := by
    intro q hq
    have hq := List.mem_range.mp hq
    have h1 : c.tableJump (3*q+1) = 0 := by
      unfold tableJump; rw [if_neg (by omega)]
    have h2 : c.tableJump (3*q+2) = 0 := by
      unfold tableJump; rw [if_neg (by omega)]
    rw [h1, h2]
    by_cases h16 : q = 16
    · subst h16
      unfold tableJump
      simp [rowInl, inl]
    · rw [hd (3*q) (by omega), hd (3*q+1) (by omega), hd (3*q+2) (by omega),
        ← cost_kss_kOf c hds q (by omega)]
      unfold tableJump
      rw [show 3*q/3 = q by omega]
      simp only [show (3*q)%3 = 0 by omega, show 3*q < 50 by omega, and_self, true_and, rowInl, inl]
      generalize kss q (c.kOf q) = x
      interval_cases q <;> simp <;> omega
  rw [h51, sum_range_three', List.map_congr_left hq]
  have hsplit := sum_map_add (List.range 17) (fun q => if q < 9 ∨ q = 16 then 1 else 0)
    (fun q => if (q = 10 ∨ q = 11 ∨ q = 12) ∧
      digits.getD (3*q) 0 + digits.getD (3*q+1) 0 + digits.getD (3*q+2) 0 < 3 then 1 else 0)
  have h10 : ((List.range 17).map fun q => if q < 9 ∨ q = 16 then 1 else 0).sum = 10 := by decide +kernel
  rw [hsplit, h10]
  unfold dispatchPenalty topDispatchPenalty
  rw [if_pos rfl, sum_flags]

theorem bufferCredit_source (c : NCtx) (digits : List Nat)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.bufferCredit = savedCopies 0 digits := by
  unfold bufferCredit savedCopies
  rw [sum_flags, show chainCount 0 = 51 from rfl]
  apply congrArg List.length
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [decide_eq_decide]
  exact c.bufferSafe_source digits hd i hi'

theorem jumps_le_thirteen (c : NCtx) : c.jumps ≤ 13 := by
  have h : ∀ i, c.tableJump i ≤
      (if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0) := by
    intro i
    unfold tableJump
    by_cases hj : (i%3=0 ∧ i<50) ∧ rowInl (i/3) (c.kOf (i/3))=false
    · rw [if_pos hj]
      have hh : inl (i/3) = false := by
        have hh := hj.2
        simp only [rowInl, Bool.or_eq_false_iff] at hh
        exact hh.1
      simp [hj.1.1, hj.1.2, hh]
    · rw [if_neg hj]
      exact Nat.zero_le _
  have H : ∀ L : List Nat, (L.map c.tableJump).sum ≤
      (L.map fun i => if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0).sum := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h i) ih
  have H0 := H (List.range 51)
  have he : ((List.range 51).map fun i => if i%3=0 ∧ i<50 ∧ inl (i/3)=false then 1 else 0).sum=13 := by
    decide +kernel
  simpa [jumps, he] using H0

theorem chainsCost_any (c : NCtx) (hds : c.DigitsOk) : c.chainsCost 0 51 ≤ 2341 := by
  have hb := c.chainsCost_buffer_balance hds
  have hj := c.jumps_le_thirteen
  omega

/-- Campaign T51 cost law of the 51 chains at an accepted word (digit sum 152):
`2328 + 10 + penalty - 9·152 = 970 + penalty`. -/
theorem chainsCost_accepted (c : NCtx) (hds : c.DigitsOk) (v : Digest) (digits : List Nat)
    (hdec : decode 0 v = some digits)
    (hd : ∀ i, i < 51 → digits.getD i 0 = c.dig i) :
    c.chainsCost 0 51 + topCredit v + 4*savedCopies 0 digits = 970 + dispatchPenalty 0 digits := by
  obtain ⟨-, -, ⟨hs1, -⟩, rfl⟩ := decode_top_some hdec
  have hlen : (dataDigits 0 v ++ [target 0 - (dataDigits 0 v).sum]).length = 51 := by
    simp [dataDigits_top_length]
  have hmap : (List.range 51).map c.dig = dataDigits 0 v ++ [target 0 - (dataDigits 0 v).sum] := by
    apply List.ext_getElem
    · simp [hlen]
    · intro n h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [← hd n (by simpa using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
      rfl
  have hsum : ((List.range 51).map c.dig).sum = 152 := by
    rw [hmap, List.sum_append]
    simp only [List.sum_cons, List.sum_nil]
    have : target 0 = 152 := rfl
    omega
  have hex : c.exactCredit = topCredit v := by
    unfold exactCredit topCredit
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [hd i hi', topMax_eq]
  have hb := c.chainsCost_buffer_balance hds
  have hj := c.jumps_source hds _ hd
  have hc := c.bufferCredit_source _ hd
  rw [hsum, hex, hc, hj] at hb
  omega

end SigGolfCandidate.T3M.Nonbinary.NCtx
