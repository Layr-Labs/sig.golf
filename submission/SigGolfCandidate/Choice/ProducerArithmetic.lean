import SigGolfCandidate.T3M.Search.TopWindow
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.ClaudeWCT.WCT9.Core

/-! Arithmetic shared by the frozen reward routines and the new selector.
These declarations were factored out of Search.RewardBlocks without changing their statements. -/
namespace SigGolfCandidate.T3M.Search.Reward
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer Digest)
open ClaudeWCT.WCT9
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def nDigits (top : Bool) : Nat := if top then 54 else 43
def maximum (top : Bool) (i : Nat) : Nat := if top && decide (i < 51) then 4 else 7
def direct (top : Bool) (i : Nat) : Bool := decide (i = 0) || (!top && decide (i = 1))

def penaltyGroups : List Nat := [0,1,2,3,4,5,6,7,8,10,11,12]

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


theorem maximum_bounds (top : Bool) (i : Nat) : 2 ≤ maximum top i ∧ maximum top i < 8 := by
  unfold maximum; split <;> omega


theorem maximum_layer (lay : Layer) (i : Nat) : maximum (decide (lay=0)) i = T3.maxDigit lay i := by
  by_cases h : lay=0 <;> simp [maximum, T3.maxDigit, h]
theorem count_layer (lay : Layer) : nDigits (decide (lay=0)) = T3.chainCount lay := by
  fin_cases lay <;> rfl

theorem saved_layer (lay : Layer) (ds : List Nat) (i : Nat) :
    saved (decide (lay=0)) ds i ↔ safeZeroCopy lay ds i := by
  simp only [saved, maximum_layer, safeZeroCopy]
  have hdirect : direct (decide (lay=0)) i = true ↔ i=0 ∨ (lay≠0 ∧ i=1) := by
    simp [direct]
  rw [hdirect]
  constructor
  · rintro ⟨ha, (h0 | h1) | ⟨hm, hp⟩⟩
    · exact ⟨ha, Or.inl h0⟩
    · exact ⟨ha, Or.inr (Or.inl h1)⟩
    · exact ⟨ha, Or.inr (Or.inr ⟨by omega, hm, hp⟩)⟩
  · rintro ⟨ha, h0 | h1 | ⟨_, hm, hp⟩⟩
    · exact ⟨ha, Or.inl (Or.inl h0)⟩
    · exact ⟨ha, Or.inl (Or.inr h1)⟩
    · exact ⟨ha, Or.inr ⟨hm, hp⟩⟩

theorem credit_layer (lay : Layer) (ds : List Nat) (i : Nat) :
    ds.getD i 0 = maximum (decide (lay=0)) i-1 ↔ ds.getD i 0+1 = T3.maxDigit lay i := by
  rw [← maximum_layer lay i]
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

theorem penalty_total (ds : List Nat) : (penaltyGroups.map (penalty ds)).sum = topDispatchPenalty ds := by
  rw [penalty_sum_count]
  have hr : penaltyGroups = (List.range 17).filter (fun q => decide (q ≠ 9 ∧ q < 13)) := by decide +kernel
  rw [hr, List.filter_filter]
  unfold topDispatchPenalty
  apply congrArg List.length
  apply List.filter_congr
  intro q hq
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  tauto


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
def topKind (q : Nat) : Nat := if q=0 then 0 else if q∈penaltyGroups then 1 else 2
def packedTopScore (v : T3.Digest) : Nat :=
  ((List.range 17).map (fun q => topLookup (topKind q) (topRank v q))).sum +
    tailLookup (v.toNat / 2^119 % 512)

theorem topDigits_getD' (v : T3.Digest) (i : Nat) (hi : i < 54) :
    (topDigits (T3.topFlip v)).getD i 0 = T3.coreDigit 0 (T3.topFlip v) i := by
  simp [topDigits, hi]

theorem topDigits_group_getD (v : T3.Digest) (q : Nat) (hq : q < 17) (i : Nat) (hi : i < 3) :
    (topDigits (T3.topFlip v)).getD (3*q+i) 0 = topRank v q / 5^i % 5 := by
  rw [topDigits_getD' _ _ (by omega)]
  simp only [T3.coreDigit, if_pos rfl, if_pos (by omega : 3*q+i<51), T3.topCode_topFlip]
  rw [show (3*q+i)/3=q by omega, show (3*q+i)%3=i by omega]
  rfl

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

theorem tailLookup_digits (v : T3.Digest) :
    tailLookup (v.toNat / 2^119 % 512) =
      tripleScore 7 ((topDigits (T3.topFlip v)).getD 51 0)
        ((topDigits (T3.topFlip v)).getD 52 0) ((topDigits (T3.topFlip v)).getD 53 0) := by
  rw [topDigits_getD' _ _ (by decide), topDigits_getD' _ _ (by decide), topDigits_getD' _ _ (by decide)]
  norm_num [T3.coreDigit, T3.topCode_topFlip, T3.topRawShift, tailLookup]
  congr 1 <;> omega

theorem topLookup_add_penalty (q : Fin 17) (r : Nat) (hr : r < 125) :
    topLookup (topKind q.val) r +
        (if q.val ∈ penaltyGroups then (if r%5+r/5%5+r/25%5<3 then 1 else 0) else 0) =
      tripleScore 4 (r%5) (r/5%5) (r/25%5) +
        (if q.val=0 ∧ r%5=4 then 4 else 0) + (if q.val ∈ penaltyGroups then 1 else 0) := by
  fin_cases q <;> simp [topKind, penaltyGroups, topLookup, hr]
  all_goals split_ifs <;> omega

theorem packed_group_reward (v : T3.Digest) (q : Fin 17) (hr : topRank v q.val < 125) :
    topLookup (topKind q.val) (topRank v q.val) +
      (if q.val ∈ penaltyGroups then penalty (topDigits (T3.topFlip v)) q.val else 0) =
      ([3*q.val,3*q.val+1,3*q.val+2].map (reward true (topDigits (T3.topFlip v)))).sum +
      (if q.val ∈ penaltyGroups then 1 else 0) := by
  rw [reward_top_group]
  have h0 := topDigits_group_getD v q.val q.isLt 0 (by decide)
  simp only [Nat.add_zero, pow_zero, Nat.div_one] at h0
  simpa only [penalty, h0, topDigits_group_getD v q.val q.isLt 0 (by decide),
    topDigits_group_getD v q.val q.isLt 1 (by decide), topDigits_group_getD v q.val q.isLt 2 (by decide),
    Nat.add_zero, pow_zero, pow_one, Nat.div_one, show (5:Nat)^2=25 from rfl] using
    topLookup_add_penalty q (topRank v q.val) hr


theorem reward_top_total (ds : List Nat) :
    ((List.range 54).map (reward true ds)).sum = wordCredit 0 ds + 4 * savedCopies 0 ds := by
  have hc (i : Nat) : ds.getD i 0 = maximum true i - 1 ↔ ds.getD i 0 + 1 = T3.maxDigit 0 i :=
    credit_layer 0 ds i
  have hs (i : Nat) : saved true ds i ↔ safeZeroCopy 0 ds i := saved_layer 0 ds i
  rw [reward_sum_counts]
  simp only [hc, hs]
  rfl

theorem reward_top_grouped (ds : List Nat) :
    ((List.range 54).map (reward true ds)).sum =
      (∑ q : Fin 17, ([3*q.val,3*q.val+1,3*q.val+2].map (reward true ds)).sum) +
      tripleScore 7 (ds.getD 51 0) (ds.getD 52 0) (ds.getD 53 0) := by
  have hi : List.range 54 =
      (List.ofFn fun q : Fin 17 => [3*q.val,3*q.val+1,3*q.val+2]).flatten ++ [51,52,53] := by decide +kernel
  rw [hi, List.map_append, List.sum_append, reward_top_tail]
  simp only [List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn, Function.comp_def, List.sum_ofFn]

theorem penalty_top_grouped (ds : List Nat) :
    (∑ q : Fin 17, if q.val ∈ penaltyGroups then penalty ds q.val else 0) = dispatchPenalty 0 ds := by
  rw [show dispatchPenalty 0 ds = topDispatchPenalty ds from rfl, ← penalty_total]
  simp [Fin.sum_univ_succ, penaltyGroups, Nat.add_assoc]

theorem packedTopScore_reward (v : T3.Digest) (hv : T3.topRanksValid (T3.topFlip v) = true) :
    packedTopScore v + dispatchPenalty 0 (topDigits (T3.topFlip v)) =
      wordCredit 0 (topDigits (T3.topFlip v)) + 4 * savedCopies 0 (topDigits (T3.topFlip v)) + 12 := by
  have hg (q : Fin 17) : topRank v q.val < 125 :=
    (topRanksValid_iff v).mp hv _ (List.mem_map.mpr ⟨q.val, List.mem_range.mpr q.isLt, rfl⟩)
  have hs := Finset.sum_congr rfl (fun q (_ : q ∈ (Finset.univ : Finset (Fin 17))) =>
    packed_group_reward v q (hg q))
  simp only [Finset.sum_add_distrib] at hs
  have ho : (∑ q : Fin 17, if q.val ∈ penaltyGroups then (1:Nat) else 0) = 12 := by decide +kernel
  rw [ho, penalty_top_grouped] at hs
  have hr := reward_top_grouped (topDigits (T3.topFlip v))
  rw [reward_top_total, ← tailLookup_digits] at hr
  have hp : packedTopScore v = (∑ q : Fin 17, topLookup (topKind q.val) (topRank v q.val)) +
      tailLookup (v.toNat / 2^119 % 512) := by
    unfold packedTopScore
    rw [show List.range 17 = List.ofFn (fun q : Fin 17 => q.val) from rfl]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]
  omega




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

/-- The two lookup accumulators used by the assembly selector characterize
exactly the source producer's top-word predicate. -/
theorem producerDecode_top_lookup (v : Digest) :
    producerDecode 0 (T3.topFlip v) =
      if topLookupSum v = 146 ∧ 34 ≤ packedTopScore v
      then some (topDigits (T3.topFlip v)) else none := by
  unfold producerDecode
  rw [decode_top_lookup]
  by_cases hs : topLookupSum v = 146
  · rw [if_pos hs]
    have hv := ((topLookupSum_eq_iff v).mp hs).1
    have hb := packedTopScore_reward v hv
    have hc : producerFloor 0 + dispatchPenalty 0 (topDigits (T3.topFlip v)) ≤
        wordCredit 0 (topDigits (T3.topFlip v)) + 4 * savedCopies 0 (topDigits (T3.topFlip v)) ↔
        34 ≤ packedTopScore v := by
      change 22 + _ ≤ _ ↔ _
      omega
    simp only [hc, producerZeroBound, producerRankBound, true_or, and_true, hs, true_and]
  · simp only [if_neg hs, hs, false_and, if_false]

end SigGolfCandidate.T3M.Search.Reward

#print axioms SigGolfCandidate.T3M.Search.Reward.producerDecode_top_lookup
