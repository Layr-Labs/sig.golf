import SigGolfCandidate.T3M_Search_Basic
import SigGolfCandidate.T3M_Search_TopWindow
import SigGolfCandidate.T3M_ImageSlice
import SigGolfCandidate.T3M_Images_Slices
import SigGolfCandidate.T3_Proofs
import SigGolfCandidate.T3M_Images_Sign
import SigGolfCandidate.T3M_Images_Expand
import SigGolfCandidate.ClaudeWCT_WCT9_Core

namespace SigGolfCandidate.T3M.Search.Reward
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false
set_option linter.unusedSimpArgs false

/-- The frozen producer's reward routines share this entry and byte layout. -/
def base (b : Nat) (top : Bool) : Nat :=
  if b = 354 then (if top then 43352 else 42947) else (if top then 21343 else 20938)
def nDigits (top : Bool) : Nat := if top then 54 else 43
def maximum (top : Bool) (i : Nat) : Nat := if top && decide (i < 51) then 4 else 7
def direct (top : Bool) (i : Nat) : Bool := decide (i = 0) || (!top && decide (i = 1))
def iw (rd rs imm f op : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm * 2^20 + rs * 2^15 + f * 2^12 + rd * 2^7 + op)
def byteLoad (rd i : Nat) : BitVec 32 := iw rd 10 i 4 3
def minus (rd rs n : Nat) : BitVec 32 := iw rd rs (4096-n) 0 0x13
def eqZero (rd : Nat) : BitVec 32 := iw rd rd 1 3 0x13
def initWords : List (BitVec 32) := [0x20537,0x42050513,0x313]
def digitWords (top : Bool) (i : Nat) : List (BitVec 32) :=
  [byteLoad 28 i, minus 29 28 (maximum top i-1), eqZero 29, 0x1d30333] ++
  (if direct top i then
    [minus 29 28 (maximum top i), eqZero 29, 0x2e9e93, 0x1d30333]
  else if i % 3 ≠ 0 then
    [minus 29 28 (maximum top i), eqZero 29, byteLoad 30 (i-1),
     minus 30 30 (maximum top (i-1)), eqZero 30, 0x1eefeb3, 0x2e9e93, 0x1d30333]
  else [])
def penaltyGroups : List Nat := [0,1,2,3,4,5,6,7,8,10,11,12]
def penaltyWords (q : Nat) : List (BitVec 32) :=
  [byteLoad 28 (3*q),byteLoad 29 (3*q+1),byteLoad 30 (3*q+2),
   0x1de0e33,0x1ee0e33,0x3e3e13,0x41c30333]
def floorWords (top : Bool) : List (BitVec 32) :=
  if top then [0x1500e13] else [0xfff40e13,0x1e3e13,0x9e0e13]
def exitWords (b : Nat) (top : Bool) : List (BitVec 32) :=
  if b = 354 then (if top then [0x1c34463,0x8067,0xe21d506f] else [0x1c34463,0x8067,0xf7cd606f])
  else (if top then [0x1c34463,0x8067,0x8f9eb06f] else [0x1c34463,0x8067,0xa54ec06f])
def code (b : Nat) (top : Bool) : List (BitVec 32) :=
  initWords ++ ((List.range (nDigits top)).map (digitWords top)).flatten ++
    (if top then (penaltyGroups.map penaltyWords).flatten else []) ++ floorWords top ++ exitWords b top


private theorem foldl_chunks (cs : List (List (BitVec 32))) (acc : List (BitVec 32)) :
    cs.foldl (· ++ ·) acc = acc ++ cs.flatten := by
  induction cs generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
  | cons c cs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]

theorem code_length (b : Nat) (top : Bool) : (code b top).length = if top then 599 else 405 := by
  by_cases hb : b = 354 <;> cases top <;> simp [code, exitWords, hb] <;> decide +kernel

theorem eq_small (d m : Nat) (hd : d < 8) (hm : m < 8) (hm0 : 0 < m) :
    (if ((BitVec.ofNat 64 d) + BitVec.ofNat 64 (2^64-m)).ult 1#64 then 1#64 else 0#64) =
      BitVec.ofNat 64 (if d = m then 1 else 0) := by
  interval_cases d <;> interval_cases m <;> decide

def constByte (i : Nat) : E :=
  .un (.ld .bu (i%8)) (.ld (.c (BitVec.ofNat 64 (DIGITS+i/8*8))))
def constFlag (i m : Nat) : E :=
  .bin .sltu (mkAdd (constByte i) (.c (BitVec.ofNat 64 (2^64-m)))) (.c 1)
def constBonus (top : Bool) (i : Nat) : E :=
  if direct top i then .bin .sll (constFlag i (maximum top i)) (.c 2)
  else if i%3 ≠ 0 then .bin .sll
    (.bin .and (constFlag i (maximum top i)) (constFlag (i-1) (maximum top (i-1)))) (.c 2)
  else .c 0
def addReward (top : Bool) (e : E) (i : Nat) : E :=
  mkAdd (mkAdd e (constFlag i (maximum top i-1))) (constBonus top i)
def penaltyExpr (q : Nat) : E :=
  .bin .sltu (mkAdd (mkAdd (constByte (3*q)) (constByte (3*q+1))) (constByte (3*q+2))) (.c 3)
def rewardsExpr (top : Bool) : E := (List.range (nDigits top)).foldl (addReward top) (.c 0)
def scoreExpr (top : Bool) : E :=
  if top then penaltyGroups.foldl (fun e q => mkBin .sub e (penaltyExpr q)) (rewardsExpr top)
  else rewardsExpr top
def floorExpr (top : Bool) : E :=
  if top then .c 21 else mkAdd
    (.bin .sltu (mkAdd (.reg .x8) (.c 18446744073709551615)) (.c 1)) (.c 9)

sym_block low354 := symRun {noAlias:=true} (code 354 false) (pcOf (base 354 false)) 1000
sym_block top354 := symRun {noAlias:=true} (code 354 true) (pcOf (base 354 true)) 1000

def preResult (b : Nat) (top : Bool) : Result :=
  let r := if top then top354.res else low354.res
  ⟨r.st, .ite .lt (scoreExpr top) (floorExpr top)
    (.c (pcOf (base b top + (code b top).length - 1)))
    (.c (pcOf (base b top + (code b top).length - 2))), .branch,
    (code b top).length-2, (code b top).length-2⟩
theorem pre_run (b : Nat) (hb : b=354 ∨ b=543) (top : Bool) :
    symRun {noAlias:=true} (code b top) (pcOf (base b top)) 1000 = some (preResult b top) := by
  rcases hb with rfl | rfl <;> cases top <;> kernel_rfl

open SigGolfCandidate.T3 (Layer Digest)
open ClaudeWCT.WCT9

def credit (top : Bool) (ds : List Nat) (i : Nat) : Nat :=
  if ds.getD i 0 = maximum top i-1 then 1 else 0
def saved (top : Bool) (ds : List Nat) (i : Nat) : Prop :=
  ds.getD i 0 = maximum top i ∧
    (direct top i = true ∨ (i%3 ≠ 0 ∧ ds.getD (i-1) 0 = maximum top (i-1)))
instance (top : Bool) (ds : List Nat) (i : Nat) : Decidable (saved top ds i) := by
  unfold saved; infer_instance
def reward (top : Bool) (ds : List Nat) (i : Nat) : Nat :=
  credit top ds i + 4 * (if saved top ds i then 1 else 0)
def penalty (ds : List Nat) (q : Nat) : Nat :=
  if ds.getD (3*q) 0 + ds.getD (3*q+1) 0 + ds.getD (3*q+2) 0 < 3 then 1 else 0

theorem constByte_eval (s : MachineState) (i : Nat) (hi : i < 54) :
    (constByte i).eval s = (s.getByte (BitVec.ofNat 64 (DIGITS+i))).zeroExtend 64 := by
  rw [constByte, E.eval, UnOp.eval, LoadKind.fromWord, E.eval, E.eval]
  rw [getByte_eq_word _ _ (by dsimp [DIGITS]; omega)]
  congr 2
  · congr 2; dsimp [DIGITS]; omega
  · dsimp [DIGITS]; omega

theorem widen_small (d : Nat) (hd : d < 8) :
    (BitVec.ofNat 8 d).zeroExtend 64 = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  norm_num
  change d % 256 % 18446744073709551616 = d % 18446744073709551616
  rw [Nat.mod_eq_of_lt (by omega : d < 256)]

theorem constFlag_eval (s : MachineState) (i d m : Nat) (hi : i < 54)
    (hd : d < 8) (hm : m < 8) (hm0 : 0 < m)
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS+i)) = BitVec.ofNat 8 d) :
    (constFlag i m).eval s = BitVec.ofNat 64 (if d = m then 1 else 0) := by
  simp only [constFlag, E.eval, mkAdd_eval, constByte_eval s i hi, hb,
    widen_small d hd, BinOp.eval]
  exact eq_small d m hd hm hm0

theorem maximum_bounds (top : Bool) (i : Nat) : 2 ≤ maximum top i ∧ maximum top i < 8 := by
  unfold maximum; split <;> omega

theorem constBonus_eval (s : MachineState) (top : Bool) (ds : List Nat) (i : Nat)
    (hi : i < nDigits top) (hd : ∀ j < nDigits top, ds.getD j 0 < 8)
    (hm : ∀ j < nDigits top, s.getByte (BitVec.ofNat 64 (DIGITS+j)) = BitVec.ofNat 8 (ds.getD j 0)) :
    (constBonus top i).eval s = BitVec.ofNat 64 (4 * (if saved top ds i then 1 else 0)) := by
  have hn : nDigits top ≤ 54 := by cases top <;> decide
  have he := constFlag_eval s i (ds.getD i 0) (maximum top i) (by omega)
    (hd i hi) (maximum_bounds top i).2 (by have := (maximum_bounds top i).1; omega) (hm i hi)
  have hp := constFlag_eval s (i-1) (ds.getD (i-1) 0) (maximum top (i-1)) (by omega)
    (hd (i-1) (by omega)) (maximum_bounds top (i-1)).2
    (by have := (maximum_bounds top (i-1)).1; omega) (hm (i-1) (by omega))
  unfold constBonus saved
  by_cases hh : direct top i = true
  · simp only [hh, ↓reduceIte, E.eval, BinOp.eval, he, true_or, and_true]
    split <;> decide +kernel
  · simp only [hh, Bool.false_eq_true, ↓reduceIte, false_or]
    by_cases hmod : i%3 ≠ 0
    · rw [if_pos hmod]
      by_cases ha : ds.getD i 0 = maximum top i <;>
        by_cases hb : ds.getD (i-1) 0 = maximum top (i-1) <;>
        simp only [hmod, not_false_eq_true, not_true_eq_false, ↓reduceIte, E.eval, BinOp.eval, he, hp, true_and, ha, hb, and_false, and_true, false_and] <;> try rw [if_pos hmod]
      all_goals decide +kernel
    · simp [hmod, E.eval]

theorem addReward_eval (s : MachineState) (top : Bool) (ds : List Nat) (i : Nat) (e : E)
    (hi : i < nDigits top) (hd : ∀ j < nDigits top, ds.getD j 0 < 8)
    (hm : ∀ j < nDigits top, s.getByte (BitVec.ofNat 64 (DIGITS+j)) = BitVec.ofNat 8 (ds.getD j 0)) :
    (addReward top e i).eval s = e.eval s + BitVec.ofNat 64 (reward top ds i) := by
  have hn : nDigits top ≤ 54 := by cases top <;> decide
  have he := constFlag_eval s i (ds.getD i 0) (maximum top i-1) (by omega)
    (hd i hi) (by have := (maximum_bounds top i).2; omega)
    (by have := (maximum_bounds top i).1; omega) (hm i hi)
  simp only [addReward, mkAdd_eval, he, constBonus_eval s top ds i hi hd hm,
    BitVec.add_assoc, ofNat_add_ofNat]
  rfl

theorem rewards_fold_eval (s : MachineState) (top : Bool) (ds : List Nat)
    (hd : ∀ j < nDigits top, ds.getD j 0 < 8)
    (hm : ∀ j < nDigits top, s.getByte (BitVec.ofNat 64 (DIGITS+j)) = BitVec.ofNat 8 (ds.getD j 0))
    (is : List Nat) (hi : ∀ i ∈ is, i < nDigits top) (e : E) :
    (is.foldl (addReward top) e).eval s =
      e.eval s + BitVec.ofNat 64 ((is.map (reward top ds)).sum) := by
  induction is generalizing e with
  | nil => simp [E.eval]
  | cons i is ih =>
    rw [List.foldl_cons, ih (by simp_all), addReward_eval s top ds i e (hi i (by simp)) hd hm]
    simp only [List.map_cons, List.sum_cons, BitVec.add_assoc, ofNat_add_ofNat]

theorem rewardsExpr_eval (s : MachineState) (top : Bool) (ds : List Nat)
    (hd : ∀ j < nDigits top, ds.getD j 0 < 8)
    (hm : ∀ j < nDigits top, s.getByte (BitVec.ofNat 64 (DIGITS+j)) = BitVec.ofNat 8 (ds.getD j 0)) :
    (rewardsExpr top).eval s = BitVec.ofNat 64 (((List.range (nDigits top)).map (reward top ds)).sum) := by
  simpa [rewardsExpr, E.eval] using
    rewards_fold_eval s top ds hd hm (List.range (nDigits top)) (by simp) (.c 0)

theorem penaltyExpr_eval (s : MachineState) (ds : List Nat) (q : Nat) (hq : q < 13)
    (hd : ∀ j < 54, ds.getD j 0 < 8)
    (hm : ∀ j < 54, s.getByte (BitVec.ofNat 64 (DIGITS+j)) = BitVec.ofNat 8 (ds.getD j 0)) :
    (penaltyExpr q).eval s = BitVec.ofNat 64 (penalty ds q) := by
  have h0 := constByte_eval s (3*q) (by omega)
  have h1 := constByte_eval s (3*q+1) (by omega)
  have h2 := constByte_eval s (3*q+2) (by omega)
  rw [hm _ (by omega), widen_small _ (hd _ (by omega))] at h0 h1 h2
  simp only [penaltyExpr, E.eval, mkAdd_eval, h0, h1, h2, ofNat_add_ofNat, BinOp.eval]
  have hs : ds.getD (3*q) 0 + ds.getD (3*q+1) 0 + ds.getD (3*q+2) 0 < 2^64 := by
    have := hd (3*q) (by omega); have := hd (3*q+1) (by omega); have := hd (3*q+2) (by omega); omega
  change (if decide ((ds.getD (3*q) 0 + ds.getD (3*q+1) 0 + ds.getD (3*q+2) 0) % 2^64 < 3) = true
    then (1 : Word) else 0) = _
  rw [Nat.mod_eq_of_lt hs]
  simp only [decide_eq_true_eq, penalty]
  split <;> rfl

theorem penalty_fold_eval (s : MachineState) (ds : List Nat)
    (hd : ∀ j < 54, ds.getD j 0 < 8)
    (hm : ∀ j < 54, s.getByte (BitVec.ofNat 64 (DIGITS+j)) = BitVec.ofNat 8 (ds.getD j 0))
    (qs : List Nat) (hq : ∀ q ∈ qs, q < 13) (e : E) :
    (qs.foldl (fun e q => mkBin .sub e (penaltyExpr q)) e).eval s =
      e.eval s - BitVec.ofNat 64 ((qs.map (penalty ds)).sum) := by
  induction qs generalizing e with
  | nil => simp [E.eval]
  | cons q qs ih =>
    rw [List.foldl_cons, ih (by simp_all), mkBin_eval, BinOp.eval,
      penaltyExpr_eval s ds q (hq q (by simp)) hd hm]
    simp only [List.map_cons, List.sum_cons, BitVec.sub_sub, ofNat_add_ofNat]

/-- Lower layers only (campaign T51: the top layer is scored by the T51 kernel, `T51.trial`). -/
theorem maximum_layer (lay : Layer) (hl : lay ≠ 0) (i : Nat) : maximum (decide (lay=0)) i = T3.maxDigit lay i := by
  simp [maximum, T3.maxDigit, hl]

theorem count_layer (lay : Layer) (hl : lay ≠ 0) : nDigits (decide (lay=0)) = T3.chainCount lay := by
  fin_cases lay <;> first | exact (hl rfl).elim | rfl

theorem saved_layer (lay : Layer) (hl : lay ≠ 0) (ds : List Nat) (i : Nat) :
    saved (decide (lay=0)) ds i ↔ safeZeroCopy lay ds i := by
  simp only [saved, maximum_layer lay hl, safeZeroCopy]
  have hdirect : direct (decide (lay=0)) i = true ↔ i=0 ∨ (lay≠0 ∧ i=1) := by
    simp [direct]
  rw [hdirect]
  constructor
  · rintro ⟨ha, (h0 | h1) | ⟨hm, hp⟩⟩
    · exact ⟨ha, Or.inl h0⟩
    · exact ⟨ha, Or.inr (Or.inl h1)⟩
    · exact ⟨ha, Or.inr (Or.inr ⟨by omega, hm, fun h => hl h.1, hp⟩)⟩
  · rintro ⟨ha, h0 | h1 | ⟨_, hm, _, hp⟩⟩
    · exact ⟨ha, Or.inl (Or.inl h0)⟩
    · exact ⟨ha, Or.inl (Or.inr h1)⟩
    · exact ⟨ha, Or.inr ⟨hm, hp⟩⟩

theorem credit_layer (lay : Layer) (hl : lay ≠ 0) (ds : List Nat) (i : Nat) :
    ds.getD i 0 = maximum (decide (lay=0)) i-1 ↔ ds.getD i 0+1 = T3.maxDigit lay i := by
  rw [← maximum_layer lay hl i]
  have := (maximum_bounds (decide (lay=0)) i).1
  omega

theorem reward_sum_counts (top : Bool) (ds : List Nat) (is : List Nat) :
    (is.map (reward top ds)).sum =
      (is.filter fun i => decide (ds.getD i 0 = maximum top i-1)).length +
      4 * (is.filter fun i => decide (saved top ds i)).length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    by_cases hc : ds.getD i 0 = maximum top i-1 <;>
      by_cases hs : saved top ds i <;>
      simp only [reward, credit, List.map_cons, List.sum_cons, List.filter_cons,
        hc, hs, decide_true, decide_false, if_true, if_false, Bool.false_eq_true,
        List.length_cons, ih] <;> omega

theorem rewardsExpr_layer (s : MachineState) (lay : Layer) (hl : lay ≠ 0) (ds : List Nat)
    (hd : ∀ j < T3.chainCount lay, ds.getD j 0 < 8)
    (hm : ∀ j < T3.chainCount lay, s.getByte (BitVec.ofNat 64 (DIGITS+j)) = BitVec.ofNat 8 (ds.getD j 0)) :
    (rewardsExpr (decide (lay=0))).eval s = BitVec.ofNat 64 (wordCredit lay ds + 4 * savedCopies lay ds) := by
  rw [rewardsExpr_eval s _ ds (by simpa [count_layer lay hl] using hd) (by simpa [count_layer lay hl] using hm),
    reward_sum_counts, count_layer lay hl]
  simp only [credit_layer lay hl, saved_layer lay hl]
  rfl

theorem penalty_sum_count (ds : List Nat) (qs : List Nat) :
    (qs.map (penalty ds)).sum =
      (qs.filter fun q => decide (ds.getD (3*q) 0 + ds.getD (3*q+1) 0 + ds.getD (3*q+2) 0 < 3)).length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases h : ds.getD (3*q) 0 + ds.getD (3*q+1) 0 + ds.getD (3*q+2) 0 < 3 <;>
      simp only [penalty, List.map_cons, List.sum_cons, List.filter_cons,
        h, decide_true, decide_false, if_true, if_false, Bool.false_eq_true,
        List.length_cons, ih] <;> omega



/-- The signed 64-bit score subtraction agrees with the bounded natural reward test. -/
theorem signed_reward_lt (r p f : Nat) (hr : r ≤ 270) (hp : p ≤ 12)
    (hf : f = 9 ∨ f = 10 ∨ f = 21) :
    (BitVec.ofNat 64 r - BitVec.ofNat 64 p).slt (BitVec.ofNat 64 f) =
      decide (r < p + f) := by
  have small_toInt (n : Nat) (hn : n ≤ 270) :
      (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_ofNat']
    apply Int.bmod_eq_of_le <;> norm_num <;> omega
  have hf' : f ≤ 270 := by omega
  rw [BitVec.slt_eq_decide, BitVec.toInt_sub, small_toInt r hr,
    small_toInt p (by omega), small_toInt f hf']
  have hsub : ((r : Int) - p).bmod (2 ^ 64) = (r : Int) - p := by
    apply Int.bmod_eq_of_le <;> norm_num <;> omega
  rw [hsub]
  apply decide_eq_decide.mpr
  omega


theorem pre_obligs (b : Nat) (top : Bool) (s : MachineState) : (preResult b top).obligs s := by
  cases top <;> trivial

theorem pre_preserves (b : Nat) (top : Bool) (s : MachineState) :
    RegsExcept s ((preResult b top).toState s) [.x6,.x10,.x28,.x29,.x30] := by
  cases top <;> intro r hr <;> cases r <;> simp at hr
  all_goals rfl

theorem pre_frame (b : Nat) (top : Bool) (s : MachineState) :
    Frame s ((preResult b top).toState s) (fun _=>False) := by
  cases top <;> intro A hA hn <;> rfl

theorem floorExpr_eval (s : MachineState) (lay : Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    (floorExpr (decide (lay=0))).eval s = BitVec.ofNat 64 (producerFloor lay) := by
  fin_cases lay
  · rfl
  all_goals
    change (floorExpr false).eval s = _
    simp only [floorExpr, Bool.false_eq_true, ↓reduceIte, E.eval, mkAdd_eval, h8, BinOp.eval]
    kernel_rfl

theorem total_reward_bound (lay : Layer) (ds : List Nat) :
    wordCredit lay ds + 4*savedCopies lay ds ≤ 270 := by
  have hc := List.length_filter_le (fun i => decide (ds.getD i 0 + 1 = T3.maxDigit lay i))
    (List.range (T3.chainCount lay))
  have hs := List.length_filter_le (fun i => decide (safeZeroCopy lay ds i))
    (List.range (T3.chainCount lay))
  have hn : T3.chainCount lay ≤ 54 := by fin_cases lay <;> decide
  simp only [List.length_range] at hc hs
  change (List.filter (fun i => decide (ds.getD i 0 + 1 = T3.maxDigit lay i))
    (List.range (T3.chainCount lay))).length + 4 *
    (List.filter (fun i => decide (safeZeroCopy lay ds i)) (List.range (T3.chainCount lay))).length ≤ 270
  omega


theorem floor_values (lay : Layer) : producerFloor lay = 9 ∨ producerFloor lay = 10 ∨ producerFloor lay = 21 := by
  fin_cases lay <;> decide




sym_block returnExit := symRun {noAlias:=true} [0x8067] (pcOf (base 354 false+(code 354 false).length-2)) 2
sym_block failExit := symRun {noAlias:=true} ((exitWords 354 false).drop 2) (pcOf (base 354 false+(code 354 false).length-1)) 2

theorem run_return {b : Nat} (hb : b=354 ∨ b=543) (top : Bool) :
    symRun {noAlias:=true} [0x8067] (pcOf (base b top+(code b top).length-2)) 2 = some returnExit.res := by
  rcases hb with rfl | rfl <;> cases top <;> kernel_rfl

theorem run_fail {b : Nat} (hb : b=354 ∨ b=543) (top : Bool) :
    symRun {noAlias:=true} ((exitWords b top).drop 2) (pcOf (base b top+(code b top).length-1)) 2 =
      some ⟨failExit.res.st,.c (pcOf (b+468)),failExit.res.stop,1,1⟩ := by
  rcases hb with rfl | rfl <;> cases top <;> kernel_rfl





/-- Packed reward lookup data, before digit unpacking. -/
def tripleScore (m a b c : Nat) : Nat :=
  (if a=m-1 then 1 else 0) + (if b=m-1 then 1 else 0) + (if c=m-1 then 1 else 0) +
  4*((if a=m ∧ b=m then 1 else 0)+(if b=m ∧ c=m then 1 else 0))
def lowerLookup (first : Bool) (r : Nat) : Nat :=
  tripleScore 7 (r%8) (r/8%8) (r/64%8) +
  (if first then 4*((if r%8=7 then 1 else 0)+(if r/8%8=7 ∧ r%8≠7 then 1 else 0)) else 0)
def topLookup (kind r : Nat) : Nat :=
  if r<125 then tripleScore 4 (r%5) (r/5%5) (r/25%5) +
    (if kind<2 then 1-(if r%5+r/5%5+r/25%5<3 then 1 else 0) else 0) +
    (if kind=0 ∧ r%5=4 then 4 else 0)
  else 0
def tailLookup (r : Nat) : Nat := tripleScore 7 (r/8%8) (r/64%8) (r%8)
def rewardTableByte (i : Nat) : BitVec 8 := BitVec.ofNat 8 <|
  if i<1536 then lowerLookup true (i-1024)
  else if i<2048 then lowerLookup false (i-1536)
  else if i<2176 then topLookup 0 (i-2048)
  else if i<2304 then topLookup 1 (i-2176)
  else if i<2432 then topLookup 2 (i-2304)
  else tailLookup (i-2432)
def RewardTablesOK (s : MachineState) : Prop :=
  ∀ i, 1024 ≤ i → i < 2944 → s.getByte (BitVec.ofNat 64 (TOP_DATA+i)) = rewardTableByte i
theorem RewardTablesOK.frame {s t : MachineState} {W : Nat → Prop} (h : RewardTablesOK s)
    (hf : Frame s t W) (hd : ∀ i, 1024 ≤ i → i < 2944 → ¬ W ((TOP_DATA+i)/8*8)) : RewardTablesOK t := by
  intro i hi hj
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi hj)).trans (h i hi hj)
/-- Campaign T51: the lower reward tables only (TOP_DATA + 1024..2047); the old top tables at 2048.. are overwritten by
the T51 packed block in the sign image. -/
def LowerTablesOK (s : MachineState) : Prop :=
  ∀ i, 1024 ≤ i → i < 2048 → s.getByte (BitVec.ofNat 64 (TOP_DATA+i)) = rewardTableByte i
theorem LowerTablesOK.frame {s t : MachineState} {W : Nat → Prop} (h : LowerTablesOK s)
    (hf : Frame s t W) (hd : ∀ i, 1024 ≤ i → i < 2048 → ¬ W ((TOP_DATA+i)/8*8)) : LowerTablesOK t := by
  intro i hi hj
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi hj)).trans (h i hi hj)
theorem RewardTablesOK.lower {s : MachineState} (h : RewardTablesOK s) : LowerTablesOK s :=
  fun i hi hj => h i hi (by omega)
instance {s : MachineState} : Coe (RewardTablesOK s) (LowerTablesOK s) := ⟨RewardTablesOK.lower⟩
def topKind (q : Nat) : Nat := if q=0 then 0 else if q∈penaltyGroups then 1 else 2
def packedTopScore (v : T3.Digest) : Nat :=
  ((List.range 17).map (fun q => topLookup (topKind q) (topRank v q))).sum +
    tailLookup (v.toNat / 2^119 % 512)
def fastSignLower : List (BitVec 32) := [0x10005b7,0x80058593,0xa13,0x35513,0x1ff57e13,0xbe0e33,0xc00e4e83,0x1da0a33,0x935513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1235513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1b35513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2435513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2d35513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x3635513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x93d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x123d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1b3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x243d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2d3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x363d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x41988e33,0xffae0e13,0x1e3e13,0x1ca0a33,0xfff40e13,0x1e3e13,0x9e0e13,0x1ca6463,0xed4ec06f,0xf5cec06f]
def fastSignTop : List (BitVec 32) := [0x10005b7,0x80058593,0xa13,0x35513,0x7f57e13,0xbe0e33,0xe4e83,0x1da0a33,0x735513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0xe35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1535513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1c35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x2335513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x2a35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3135513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3835513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3f35513,0x139e13,0x1c56533,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x63d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0xd3d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x143d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1b3d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x223d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x293d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x303d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x373d513,0x1ff57e13,0xbe0e33,0x180e4e83,0x1da0a33,0x2100e13,0x1ca6463,0x814ec06f,0x8c8ec06f]
def fastExpandLower : List (BitVec 32) := [0x10005b7,0x80058593,0xa13,0x35513,0x1ff57e13,0xbe0e33,0xc00e4e83,0x1da0a33,0x935513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1235513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1b35513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2435513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2d35513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x3635513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x93d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x123d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x1b3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x243d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x2d3d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x363d513,0x1ff57e13,0xbe0e33,0xe00e4e83,0x1da0a33,0x41988e33,0xffae0e13,0x1e3e13,0x1ca0a33,0xfff40e13,0x1e3e13,0x9e0e13,0x1ca6463,0xbfdd606f,0xc85d606f]
def fastExpandTop : List (BitVec 32) := [0x10005b7,0x80058593,0xa13,0x35513,0x7f57e13,0xbe0e33,0xe4e83,0x1da0a33,0x735513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0xe35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1535513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1c35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x2335513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x2a35513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3135513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3835513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x3f35513,0x139e13,0x1c56533,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x63d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0xd3d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x143d513,0x7f57e13,0xbe0e33,0x80e4e83,0x1da0a33,0x1b3d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x223d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x293d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x303d513,0x7f57e13,0xbe0e33,0x100e4e83,0x1da0a33,0x373d513,0x1ff57e13,0xbe0e33,0x180e4e83,0x1da0a33,0x2100e13,0x1ca6463,0xd3cd606f,0xdf0d606f]

def fastCode (b : Nat) (top : Bool) : List (BitVec 32) :=
  if b=354 then (if top then fastExpandTop else fastExpandLower)
  else (if top then fastSignTop else fastSignLower)
def RewardAt (image : Image) (b : Nat) : Prop :=
  CodeAt image (pcOf (base b false)) (fastCode b false) ∧ CodeAt image (pcOf (base b true)) (fastCode b true)
theorem fastCode_length (b : Nat) (top : Bool) : (fastCode b top).length = if top then 99 else 83 := by
  by_cases hb : b=354 <;> cases top <;> simp [fastCode, hb, fastExpandTop, fastExpandLower, fastSignTop, fastSignLower]
theorem fast_at_code {image : Image} {b : Nat} (h : RewardAt image b) (top : Bool) :
    CodeAt image (pcOf (base b top)) (fastCode b top) := by cases top; exact h.1; exact h.2

theorem fastCode_sign (top : Bool) :
    (Images.signReferenceCode.drop (base 543 top)).take (fastCode 543 top).length = fastCode 543 top := by
  cases top <;> rw [Images.Slices.signReferenceCode_drop_eq _ (by decide)] <;> decide +kernel
theorem fastCode_expand (top : Bool) :
    (Images.expandReferenceCode.drop (base 354 top)).take (fastCode 354 top).length = fastCode 354 top := by
  cases top <;> rw [Images.Slices.expandReferenceCode_drop_eq _ (by decide)] <;> decide +kernel
theorem at_sign : RewardAt Images.signReferenceImage 543 := by
  constructor <;> apply codeAt_slice (by decide +kernel)
  · exact fastCode_sign false
  · exact fastCode_sign true
theorem at_expand : RewardAt Images.expandReferenceImage 354 := by
  constructor <;> apply codeAt_slice (by decide +kernel)
  · exact fastCode_expand false
  · exact fastCode_expand true

namespace PackedTop
def start (q : Nat) : Nat := 3+5*q+(if q≤9 then 0 else 2)
def plen (q : Nat) : Nat := if q=9 then 5 else 3
def index (v : Digest) (q : Nat) : Nat := if q<17 then topRank v q else v.toNat / 2^119 % 512
def offset (q : Nat) : Nat := if q=17 then 384 else 128*topKind q
def value (v : Digest) (q : Nat) : Nat := if q<17 then topLookup (topKind q) (topRank v q) else tailLookup (index v q)
def prefixCode (q : Nat) : List (BitVec 32) := (fastExpandTop.drop (start q)).take (plen q)
def loadWord (q : Nat) : BitVec 32 := fastExpandTop.getD (start q+plen q) 0
def windowE (q : Nat) : E :=
  if q<9 then mkBin .srl (.reg .x6) (.c (BitVec.ofNat 64 (7*q)))
  else if q=9 then mkBin .or (mkBin .srl (.reg .x6) (.c 63)) (mkBin .sll (.reg .x7) (.c 1))
  else mkBin .srl (.reg .x7) (.c (BitVec.ofNat 64 (7*q-64)))
def indexE (q : Nat) : E := mkBin .and (windowE q) (.c (if q<17 then 127 else 511))
def prefixState (q : Nat) : SymState :=
  ⟨{RegFile.init with r10:=windowE q, r28:=mkAdd (indexE q) (.reg .x11)}, [], []⟩
def prefixResult (b q : Nat) : Result :=
  ⟨prefixState q, .c (pcOf (base b true+start q+plen q)), .endOfCode, plen q, plen q⟩
theorem prefix_run (b q : Nat) (hb : b=354 ∨ b=543) (hq : q<18) :
    symRun {noAlias:=true} (prefixCode q) (pcOf (base b true+start q)) 10 = some (prefixResult b q) := by
  rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl
end PackedTop

theorem fast_slice {image : Image} {b : Nat} (hR : RewardAt image b) (top : Bool) (k n : Nat)
    (hk : k ≤ (fastCode b top).length) :
    CodeAt image (pcOf (base b top+k)) (((fastCode b top).drop k).take n) := by
  have hc := fast_at_code hR top
  have he : fastCode b top = (fastCode b top).take k ++ ((fastCode b top).drop k).take n ++ ((fastCode b top).drop k).drop n := by
    simp only [List.append_assoc, List.take_append_drop]
  rw [he] at hc
  have hx := CodeAt.drop_prefix hc
  convert hx using 1
  simp only [List.length_take, Nat.min_eq_left hk, pcOf, ofNat_add_ofNat]
  congr 1
  omega
namespace PackedTop
theorem index_lt (v : Digest) (q : Nat) : index v q < if q<17 then 128 else 512 := by
  unfold index topRank
  split <;> omega
theorem index_eval (s : MachineState) (v : Digest) (q : Nat) (hq : q<18)
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    (indexE q).eval s = BitVec.ofNat 64 (index v q) := by
  by_cases h9 : q=9
  · subst q
    simp [indexE,windowE,mkBin_eval,E.eval,BinOp.eval,h6,h7]
    change ((v.extractLsb' 0 64 >>> 63) ||| (v.extractLsb' 64 64 <<< 1)) &&& 127#64 = _
    rw [BitVec.or_comm,topWindow_cross]
    simpa [index,topRank] using ext_shr_mask v 63 0 7 (by decide)
  · by_cases hl : q<9
    · have hh : q<17 := by omega
      simp only [indexE,windowE,if_pos hl,if_pos hh,mkBin_eval,E.eval,BinOp.eval,h6]
      rw [show (BitVec.ofNat 64 (7*q)).toNat % 64 = 7*q by simp [Nat.mod_eq_of_lt (by omega : 7*q<64)]]
      simpa [index,topRank,hh] using ext_shr_mask v 0 (7*q) 7 (by omega)
    · by_cases hh : q<17
      · simp only [indexE,windowE,if_neg hl,if_neg h9,if_pos hh,mkBin_eval,E.eval,BinOp.eval,h7]
        rw [show (BitVec.ofNat 64 (7*q-64)).toNat % 64 = 7*q-64 by simp [Nat.mod_eq_of_lt (by omega : 7*q-64<64)]]
        have he := ext_shr_mask v 64 (7*q-64) 7 (by omega)
        simpa [index,hh,topRank,show 64+(7*q-64)=7*q by omega] using he
      · have hq17 : q=17 := by omega
        subst q
        simp [indexE,windowE,mkBin_eval,E.eval,BinOp.eval,h7]
        simpa [index] using ext_shr_mask v 64 55 9 (by decide)
theorem code_prefix {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (q : Nat) (hq : q<18) : CodeAt image (pcOf (base b true+start q)) (prefixCode q) := by
  have hc := fast_slice hR true (start q) (plen q) (by
    rw [fastCode_length]; interval_cases q <;> decide)
  convert hc using 1 <;> rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl
theorem prefix_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (s : MachineState) (v : Digest) (q : Nat) (hq : q<18)
    (hpc : s.pc=pcOf (base b true+start q))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048)) :
    ∃ t, Steps image s (plen q) (plen q) t ∧ t.pc=pcOf (base b true+start q+plen q) ∧
      t.getReg .x28=BitVec.ofNat 64 (TOP_DATA+2048+index v q) ∧
      RegsExcept s t [.x10,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (prefix_run b q hb hq) (code_prefix hb hR q hq) s hpc (by simp [prefixResult,prefixState,rv_simp]),rfl,?_,?_,?_⟩
  · change (mkAdd (indexE q) (.reg .x11)).eval s = _
    rw [mkAdd_eval,E.eval,index_eval s v q hq h6 h7,h11,ofNat_add_ofNat]
    congr 1
    omega
  · intro r hr; cases r <;> simp_all [prefixResult,prefixState,RegFile.init,rv_simp] <;> rfl
  · intro A _ _; rfl
end PackedTop

theorem tripleScore_le (m a b c : Nat) : tripleScore m a b c ≤ 11 := by
  unfold tripleScore
  split_ifs <;> omega
theorem topLookup_le (kind r : Nat) : topLookup kind r ≤ 16 := by
  have h := tripleScore_le 4 (r%5) (r/5%5) (r/25%5)
  unfold topLookup
  split_ifs <;> omega
theorem tailLookup_le (r : Nat) : tailLookup r ≤ 11 := tripleScore_le _ _ _ _
theorem table_top (s : MachineState) (ht : RewardTablesOK s) (kind r : Nat) (hk : kind<3) (hr : r<128) :
    s.getByte (BitVec.ofNat 64 (TOP_DATA+(2048+128*kind+r))) = BitVec.ofNat 8 (topLookup kind r) := by
  rw [ht _ (by omega) (by omega)]
  interval_cases kind <;> simp only [rewardTableByte]
  all_goals split_ifs <;> first | omega | congr 2 <;> omega
theorem table_tail (s : MachineState) (ht : RewardTablesOK s) (r : Nat) (hr : r<512) :
    s.getByte (BitVec.ofNat 64 (TOP_DATA+(2432+r))) = BitVec.ofNat 8 (tailLookup r) := by
  rw [ht _ (by omega) (by omega)]
  simp only [rewardTableByte]
  split_ifs <;> first | omega | congr 2 <;> omega
namespace PackedTop
theorem topKind_lt (q : Nat) : topKind q<3 := by unfold topKind; split_ifs <;> omega
theorem value_le (v : Digest) (q : Nat) : value v q≤16 := by
  unfold value
  split
  · exact topLookup_le _ _
  · exact (tailLookup_le _).trans (by decide)
theorem table_value (s : MachineState) (ht : RewardTablesOK s) (v : Digest) (q : Nat) (hq : q<18) :
    (s.getByte (BitVec.ofNat 64 (TOP_DATA+2048+index v q+offset q))).zeroExtend 64 = BitVec.ofNat 64 (value v q) := by
  have hi := index_lt v q
  have hb : s.getByte (BitVec.ofNat 64 (TOP_DATA+2048+index v q+offset q)) = BitVec.ofNat 8 (value v q) := by
    by_cases hq17 : q=17
    · subst q
      convert table_tail s ht (index v 17) (by simpa using hi) using 1
      · congr 2; norm_num [offset]; omega
      · rfl
    · have hq0 : q<17 := by omega
      convert table_top s ht (topKind q) (topRank v q) (topKind_lt q) (topRank_lt v q) using 1
      · congr 1; simp [index,hq0,offset,hq17,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · simp [value,hq0]
  rw [hb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  have hv := value_le v q
  omega
theorem code_load {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (q : Nat) (hq : q<18) : CodeAt image (pcOf (base b true+start q+plen q)) [loadWord q] := by
  have hc := fast_slice hR true (start q+plen q) 1 (by rw [fastCode_length]; interval_cases q <;> decide)
  convert hc using 1 <;> rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl
theorem load_decode (q : Nat) (hq : q<18) :
    decodeInstruction (loadWord q) = some (.base (.LBU .x29 .x28 (BitVec.ofNat 12 (offset q)))) := by
  interval_cases q <;> kernel_rfl
theorem load_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (s : MachineState) (v : Digest) (q : Nat) (hq : q<18) (ht : RewardTablesOK s)
    (hpc : s.pc=pcOf (base b true+start q+plen q))
    (h28 : s.getReg .x28=BitVec.ofNat 64 (TOP_DATA+2048+index v q)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (base b true+start q+plen q+1) ∧
      t.getReg .x29=BitVec.ofNat 64 (value v q) ∧ RegsExcept s t [.x29] ∧ Frame s t (fun _=>False) := by
  have hoff : signExtend12 (BitVec.ofNat 12 (offset q))=BitVec.ofNat 64 (offset q) := by interval_cases q <;> decide +kernel
  have ha : s.getReg .x28+signExtend12 (BitVec.ofNat 12 (offset q))=BitVec.ofNat 64 (TOP_DATA+2048+index v q+offset q) := by rw [h28,hoff,ofNat_add_ofNat]
  have hv : accessValid (s.getReg .x28+signExtend12 (BitVec.ofNat 12 (offset q))) 1=true := by
    rw [ha,accessValid_iff]
    have hi := index_lt v q
    have ho : offset q≤384 := by unfold offset; split_ifs; omega; have := topKind_lt q; omega
    have hbnd : TOP_DATA+2048+index v q+offset q<2^64 := by unfold TOP_DATA; split_ifs at hi <;> omega
    rw [toNat_ofNat_lt hbnd]
    simp only [MEMORY_BYTES,Nat.mod_one,and_true,true_and]
    unfold TOP_DATA
    split_ifs at hi <;> omega
  have hs := steps_lbu (code_load hb hR q hq) hpc (load_decode q hq) hv
  rw [ha,table_value s ht v q hq] at hs
  refine ⟨_,hs,?_,?_,?_,?_⟩
  · change s.pc+4 = _
    rw [hpc,pcOf_add4]
  · change (s.setReg .x29 (BitVec.ofNat 64 (value v q))).getReg .x29 = _
    exact MachineState.getReg_setReg_eq (by decide)
  · intro r hr; simp only [List.mem_singleton] at hr
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)
  · intro A _ _; rfl
end PackedTop

open ClaudeWCT.WCT9
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false
set_option linter.unusedSimpArgs false



theorem reward_top_group (ds : List Nat) (q : Fin 17) :
    ([3*q.val,3*q.val+1,3*q.val+2].map (reward true ds)).sum =
      tripleScore 4 (ds.getD (3*q.val) 0) (ds.getD (3*q.val+1) 0) (ds.getD (3*q.val+2) 0) +
      (if q.val=0 ∧ ds.getD (3*q.val) 0 = 4 then 4 else 0) := by
  fin_cases q <;>
    simp [reward, credit, saved, maximum, direct, tripleScore, and_comm, -List.getD_eq_getElem?_getD]
  all_goals split_ifs <;> omega


theorem reward_top_tail (ds : List Nat) :
    ([51,52,53].map (reward true ds)).sum = tripleScore 7 (ds.getD 51 0) (ds.getD 52 0) (ds.getD 53 0) := by
  simp [reward, credit, saved, maximum, direct, tripleScore, and_comm, -List.getD_eq_getElem?_getD]

  split_ifs <;> omega


theorem topLookup_add_penalty (q : Fin 17) (r : Nat) (hr : r < 125) :
    topLookup (topKind q.val) r +
        (if q.val ∈ penaltyGroups then (if r%5+r/5%5+r/25%5<3 then 1 else 0) else 0) =
      tripleScore 4 (r%5) (r/5%5) (r/25%5) +
        (if q.val=0 ∧ r%5=4 then 4 else 0) + (if q.val ∈ penaltyGroups then 1 else 0) := by
  fin_cases q <;> simp [topKind, penaltyGroups, topLookup, hr]
  all_goals split_ifs <;> omega




theorem reward_top_grouped (ds : List Nat) :
    ((List.range 54).map (reward true ds)).sum =
      (∑ q : Fin 17, ([3*q.val,3*q.val+1,3*q.val+2].map (reward true ds)).sum) +
      tripleScore 7 (ds.getD 51 0) (ds.getD 52 0) (ds.getD 53 0) := by
  have hi : List.range 54 =
      (List.ofFn fun q : Fin 17 => [3*q.val,3*q.val+1,3*q.val+2]).flatten ++ [51,52,53] := by decide +kernel
  rw [hi, List.map_append, List.sum_append, reward_top_tail]
  simp only [List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn, Function.comp_def, List.sum_ofFn]





namespace PackedTop
def addCode : List (BitVec 32) := [0x1da0a33]
sym_block addBase := symRun {noAlias:=true} addCode 0#64 2
theorem add_run (pc : Word) : symRun {noAlias:=true} addCode pc 2 =
    some ⟨addBase.res.st,.c (pc+4),.endOfCode,1,1⟩ := by rfl
theorem code_add {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (q : Nat) (hq : q<18) : CodeAt image (pcOf (base b true+start q+plen q+1)) addCode := by
  have hc := fast_slice hR true (start q+plen q+1) 1 (by rw [fastCode_length]; interval_cases q <;> decide)
  convert hc using 1 <;> rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl
theorem add_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (s : MachineState) (q : Nat) (hq : q<18) (a z : Word)
    (hpc : s.pc=pcOf (base b true+start q+plen q+1)) (h20 : s.getReg .x20=a) (h29 : s.getReg .x29=z) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (base b true+start q+plen q+2) ∧
      t.getReg .x20=a+z ∧ RegsExcept s t [.x20] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (add_run _) (code_add hb hR q hq) s hpc (by simp [addBase.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,E.eval,pcOf_add4,Nat.add_assoc,Nat.reduceAdd]
  · simpa [addBase.res,rv_simp] using congrArg₂ (fun x y : Word => x+y) h20 h29
  · intro r hr; cases r <;> simp_all [addBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl
theorem start_succ (q : Nat) : start (q+1)=start q+plen q+2 := by
  unfold start plen; split_ifs <;> omega
theorem group_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (s : MachineState) (v : Digest) (q : Nat) (hq : q<18) (acc : Nat) (ht : RewardTablesOK s)
    (hpc : s.pc=pcOf (base b true+start q))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048)) (h20 : s.getReg .x20=BitVec.ofNat 64 acc) :
    ∃ t, Steps image s (plen q+2) (plen q+2) t ∧ t.pc=pcOf (base b true+start (q+1)) ∧
      t.getReg .x20=BitVec.ofNat 64 (acc+value v q) ∧
      RegsExcept s t [.x10,.x20,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t1,s1,p1,g1,r1,f1⟩ := prefix_spec hb hR s v q hq hpc h6 h7 h11
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := load_spec hb hR t1 v q hq (ht.frame f1 (by simp)) p1 g1
  obtain ⟨t3,s3,p3,g3,r3,f3⟩ := add_spec hb hR t2 q hq _ _ p2
    (by rw [r2.get (by decide),r1.get (by decide),h20]) g2
  refine ⟨t3,by simpa only [Nat.add_assoc] using (s1.trans s2).trans s3,?_,?_,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · simpa only [start_succ,Nat.add_assoc] using p3
  · simpa only [ofNat_add_ofNat] using g3
def runningSum (v : Digest) (n : Nat) : Nat := ((List.range n).map (value v)).sum
theorem runningSum_succ (v : Digest) (n : Nat) : runningSum v (n+1)=runningSum v n+value v n := by
  simp [runningSum,List.range_succ]
theorem runningSum_eq (v : Digest) : runningSum v 18=packedTopScore v := by
  rw [runningSum_succ]
  unfold runningSum packedTopScore
  congr 1
theorem iter {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (s : MachineState) (v : Digest) (n : Nat) (hn : n≤18) (ht : RewardTablesOK s)
    (hpc : s.pc=pcOf (base b true+3))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048)) (h20 : s.getReg .x20=0) :
    ∃ t, Steps image s (start n-3) (start n-3) t ∧ t.pc=pcOf (base b true+start n) ∧
      t.getReg .x20=BitVec.ofNat 64 (runningSum v n) ∧
      RegsExcept s t [.x10,.x20,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  induction n with
  | zero => exact ⟨s,Steps.refl _,hpc,h20,RegsExcept.refl _ _,Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨t1,s1,p1,g1,r1,f1⟩ := ih (by omega)
    obtain ⟨t2,s2,p2,g2,r2,f2⟩ := group_spec hb hR t1 v n (by omega) (runningSum v n)
      (ht.frame f1 (by simp)) p1 (by rw [r1.get (by decide),h6])
      (by rw [r1.get (by decide),h7]) (by rw [r1.get (by decide),h11]) g1
    refine ⟨t2,?_,p2,?_,(r1.trans r2).mono (by decide),(f1.trans f2).mono (by simp)⟩
    · have he : start n-3+(plen n+2)=start (n+1)-3 := by
        rw [start_succ]
        have : 3 ≤ start n := by unfold start; omega
        omega
      simpa only [he] using s1.trans s2
    · simpa only [runningSum_succ] using g2
end PackedTop

namespace PackedTop
def initCode : List (BitVec 32) := fastExpandTop.take 3
sym_block initBase := symRun {noAlias:=true} initCode 0#64 4
def initResult (b : Nat) : Result := ⟨initBase.res.st,.c (pcOf (base b true+3)),.endOfCode,3,3⟩
theorem init_run (b : Nat) (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} initCode (pcOf (base b true)) 4 = some (initResult b) := by
  rcases hb with rfl | rfl <;> kernel_rfl
theorem init_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (base b true)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc=pcOf (base b true+3) ∧
      t.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048) ∧ t.getReg .x20=0 ∧
      RegsExcept s t [.x11,.x20] ∧ Frame s t (fun _=>False) := by
  have hc : CodeAt image (pcOf (base b true)) initCode := by
    have hh := fast_slice hR true 0 3 (by omega)
    convert hh using 1 <;> rcases hb with rfl | rfl <;> kernel_rfl
  refine ⟨_,symRun_sound (init_run b hb) hc s hpc (by simp [initResult,initBase.res,rv_simp]),rfl,rfl,rfl,?_,?_⟩
  · intro r hr; cases r <;> simp_all [initResult,initBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl
def branchCode : List (BitVec 32) := (fastExpandTop.drop 95).take 2
sym_block branchBase := symRun {noAlias:=true} branchCode 0#64 3
def branchResult (b : Nat) : Result :=
  ⟨branchBase.res.st,.ite .ltu (.reg .x20) (.c 33) (.c (pcOf (base b true+98)))
    (.c (pcOf (base b true+97))),.branch,2,2⟩
theorem branch_run (b : Nat) (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} branchCode (pcOf (base b true+95)) 3 = some (branchResult b) := by
  rcases hb with rfl | rfl <;> kernel_rfl
theorem branch_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (s : MachineState) (acc : Nat) (ha : acc<2^64)
    (hpc : s.pc=pcOf (base b true+95)) (h20 : s.getReg .x20=BitVec.ofNat 64 acc) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc=(if acc<33 then pcOf (base b true+98) else pcOf (base b true+97)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  have hc : CodeAt image (pcOf (base b true+95)) branchCode := by
    have hh := fast_slice hR true 95 2 (by rw [fastCode_length]; decide)
    convert hh using 1 <;> rcases hb with rfl | rfl <;> kernel_rfl
  refine ⟨_,symRun_sound (branch_run b hb) hc s hpc (by simp [branchResult,branchBase.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult 33#64 then _ else _) = _
    rw [h20,ofNat_ult acc 33 ha (by decide)]
    simp [E.eval]
  · intro r hr; cases r <;> simp_all [branchResult,branchBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl
def exitCode (b : Nat) (good : Bool) : List (BitVec 32) :=
  ((fastCode b true).drop (if good then 97 else 98)).take 1
def exitResult (b : Nat) (good : Bool) : Result :=
  ⟨SymState.init,.c (pcOf (b+if good then 422 else 468)),.jump,1,1⟩
theorem exit_run (b : Nat) (hb : b=354 ∨ b=543) (good : Bool) :
    symRun {noAlias:=true} (exitCode b good) (pcOf (base b true+if good then 97 else 98)) 2 = some (exitResult b good) := by
  rcases hb with rfl | rfl <;> cases good <;> kernel_rfl
theorem exit_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : RewardAt image b)
    (s : MachineState) (good : Bool) (hpc : s.pc=pcOf (base b true+if good then 97 else 98)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+if good then 422 else 468) ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  have hc := fast_slice hR true (if good then 97 else 98) 1 (by rw [fastCode_length]; cases good <;> decide)
  refine ⟨_,symRun_sound (exit_run b hb good) hc s hpc (by simp [exitResult,SymState.init,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl
end PackedTop

end SigGolfCandidate.T3M.Search.Reward
