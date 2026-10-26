import SigGolfCandidate.Merge009
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge048
import SigGolfCandidate.Merge049
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge053
import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge064
import SigGolfCandidate.Merge066
import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge076

-- ==== merged from T3M_Verify_ChainCheckAll ====
section

namespace SigGolfCandidate.T3M
theorem triCheck_at (t : Nat) (ht : t < 14) : triCheck t 0 256 = true ∧ triCheck t 256 256 = true := by
  interval_cases t
  exacts [⟨triCheck_0_0, triCheck_0_1⟩,
    ⟨triCheck_1_0, triCheck_1_1⟩,
    ⟨triCheck_2_0, triCheck_2_1⟩,
    ⟨triCheck_3_0, triCheck_3_1⟩,
    ⟨triCheck_4_0, triCheck_4_1⟩,
    ⟨triCheck_5_0, triCheck_5_1⟩,
    ⟨triCheck_6_0, triCheck_6_1⟩,
    ⟨triCheck_7_0, triCheck_7_1⟩,
    ⟨triCheck_8_0, triCheck_8_1⟩,
    ⟨triCheck_9_0, triCheck_9_1⟩,
    ⟨triCheck_10_0, triCheck_10_1⟩,
    ⟨triCheck_11_0, triCheck_11_1⟩,
    ⟨triCheck_12_0, triCheck_12_1⟩,
    ⟨triCheck_13_0, triCheck_13_1⟩]
theorem entCheck_at (t k : Nat) (ht : t < 14) (hk : k < 512) : entCheck t k = true := by
  obtain ⟨h0, h1⟩ := triCheck_at t ht
  simp only [triCheck, Bool.and_eq_true] at h0 h1
  by_cases h : k < 256
  · exact List.all_eq_true.mp h0.1 k (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact List.all_eq_true.mp h1.1 k (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
theorem blkCheck_at (t dB dC : Nat) (ht : t < 14) (hB : dB < 8) (hC : dC < 8) :
    blkCheck t dB dC = true := by
  obtain ⟨h0, h1⟩ := triCheck_at t ht
  simp only [triCheck, Bool.and_eq_true] at h0 h1
  have e1 : (8 * dB + dC) / 8 = dB := by omega
  have e2 : (8 * dB + dC) % 8 = dC := by omega
  by_cases h : 8 * dB + dC < 32
  · have := List.all_eq_true.mp h0.2 (8 * dB + dC) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rwa [e1, e2] at this
  · have := List.all_eq_true.mp h1.2 (8 * dB + dC) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rwa [e1, e2] at this
theorem ckCheck_ok : ckCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
private theorem lower_pc_bounds_checked :
    (List.range 14).all (fun t => (List.range 8).all (fun b => (List.range 8).all (fun c =>
      decide (triBase t b c < 257214 ∧ pcX t b c < 257214)))) = true := by decide +kernel

theorem lower_pc_bounds (t b c : Nat) (ht : t < 14) (hb : b < 8) (hc : c < 8) :
    triBase t b c < 257214 ∧ pcX t b c < 257214 := by
  have h := List.all_eq_true.mp lower_pc_bounds_checked t (List.mem_range.mpr ht)
  have h := List.all_eq_true.mp h b (List.mem_range.mpr hb)
  exact of_decide_eq_true (List.all_eq_true.mp h c (List.mem_range.mpr hc))
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_ChainGood ====
section

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
def headOK (c : LCtx) (i : Nat) : Prop := i % 3 = 0 → i ≠ 42 → rankFloor (i/3) ≤ c.kOf (i/3)
theorem kOf_digits (c : LCtx) (t : Nat) (ht : t < 14) :
    c.kOf t % 8 = c.dig (3 * t) ∧ c.kOf t / 8 % 8 = c.dig (3 * t + 1) ∧ c.kOf t / 64 = c.dig (3 * t + 2) := by
  unfold kOf
  have h0 : c.dig (3 * t) < 8 := by unfold dig; split_ifs <;> omega
  have h1 : c.dig (3 * t + 1) < 8 := by unfold dig; split_ifs <;> omega
  have h2 : c.dig (3 * t + 2) < 8 := by unfold dig; split_ifs <;> omega
  refine ⟨?_, ?_, ?_⟩ <;> omega
theorem dig_lt8 (c : LCtx) (i : Nat) (hi : i < 42) : c.dig i < 8 := by unfold dig; split_ifs <;> omega
theorem blk_at (c : LCtx) (i : Nat) (hi : i < 42) :
    blkCheck (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2)) = true :=
  blkCheck_at _ _ _ (by omega) (c.dig_lt8 _ (by omega)) (c.dig_lt8 _ (by omega))
theorem chk_headJ (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 = 0) (hd : c.dig i < 7) (hRank : c.headOK i) :
    vrun (c.startPc i) 7 = some (headJHB .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i)
      (hSlot i (c.dig i)) (lowerG i)) ∧
    vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 = some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))) := by
  obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
  have et : 3 * t / 3 = t := by omega
  have he := entCheck_at t (c.kOf t) (by omega) (c.kOf_lt t (by omega))
  obtain ⟨k1, k2, k3⟩ := c.kOf_digits t (by omega)
  have hRank' : rankFloor t ≤ c.kOf t := by simpa [et] using hRank h0 (by omega)
  unfold entCheck at he
  rw [if_neg (by omega : ¬ c.kOf t < rankFloor t)] at he
  rw [k1, k2, k3, if_neg (by omega), Bool.and_eq_true] at he
  have hs : c.startPc (3 * t) = entW t (c.kOf t) := by
    unfold startPc; rw [if_neg (by omega), if_pos h0, et]
  have hr : c.rungPc (3 * t) (c.dig (3 * t)) = triBase t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) + 2 * c.dig (3 * t) := by
    unfold rungPc tb; rw [if_pos ⟨h0, by omega⟩, et]
  rw [hs, hr]
  exact ⟨rOK_eq he.1, rOK_eq he.2⟩
theorem chk_copyJ (c : LCtx) (i : Nat) (hi : i < 42) (h0 : i % 3 = 0) (hd : c.dig i = 7) (hRank : c.headOK i) (hiz : i ≠ 0) :
    vrun (c.startPc i) 7 = some (copyNB .x22 (offL i) (slotL i) (c.endPc i) (lowerG i)) := by
  obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
  have et : 3 * t / 3 = t := by omega
  have he := entCheck_at t (c.kOf t) (by omega) (c.kOf_lt t (by omega))
  obtain ⟨k1, k2, k3⟩ := c.kOf_digits t (by omega)
  have hRank' : rankFloor t ≤ c.kOf t := by simpa [et] using hRank h0 (by omega)
  unfold entCheck at he
  rw [if_neg (by omega : ¬ c.kOf t < rankFloor t)] at he
  rw [k1, k2, k3, if_pos hd, if_neg (by omega : t ≠ 0)] at he
  have hs : c.startPc (3 * t) = entW t (c.kOf t) := by
    unfold startPc; rw [if_neg (by omega), if_pos h0, et]
  have hq : c.endPc (3 * t) = pcB t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) +
      (if c.dig (3*t+1)=7 then 4 else 0) := by
    unfold endPc tB; rw [if_neg (by omega), if_pos h0, et]
    simp only [hd, true_and, show 0<3*t by omega]
  rw [hs, hq]
  exact rOK_eq he
theorem ck_parts (k : Nat) (hk : k < 8) : partOK 42 k (ckSlot k) = true := by
  have h := ckCheck_ok
  unfold ckCheck at h
  exact List.all_eq_true.mp h k (List.mem_range.mpr hk)
theorem part_at (c : LCtx) (i : Nat) (hi : i ≤ 42) (hnl : i % 3 ≠ 0 ∨ i = 42) (hck : i = 42 → c.ck < 8)
    (hNS : ¬c.bufferSafe i) : partOK i (c.dig i) (c.startPc i) = true := by
  by_cases h42 : i = 42
  · subst h42
    have hs : c.startPc 42 = ckSlot c.ck := by unfold startPc; simp
    rw [hs, c.dig42]; exact ck_parts c.ck (hck rfl)
  have h0 : i % 3 ≠ 0 := by omega
  obtain ⟨t, r, rfl, hr⟩ : ∃ t r, i = 3 * t + r ∧ r < 3 := ⟨i / 3, i % 3, by omega, by omega⟩
  have et : (3 * t + r) / 3 = t := by omega
  have hb := c.blk_at (3 * t + r) (by omega)
  rw [et] at hb
  unfold blkCheck at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨-, hB⟩, hC⟩, -⟩ := hb
  unfold startPc tB tC
  rw [if_neg h42, et, if_neg (by omega)]
  rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
  · have hskip : ¬(t=0 ∧ c.dig (3*t+1)=7) := by
      intro h; apply hNS; exact ⟨h.2, Or.inr (Or.inl (by omega))⟩
    have hjump : ¬(1<3*t+1 ∧ c.dig (3*t+1-1)=7 ∧ c.dig (3*t+1)=7) := by
      intro h; apply hNS; exact ⟨h.2.2, Or.inr (Or.inr ⟨by omega,by omega,h.2.1⟩)⟩
    rw [if_pos (by omega), if_neg hjump, Nat.add_zero]
    simpa only [hskip, decide_false, Nat.add_zero] using hB
  · have hskip : ¬(c.dig (3*t+1)=7 ∧ c.dig (3*t+2)=7) := by
      intro h; apply hNS; refine ⟨h.2, Or.inr (Or.inr ⟨by omega,by omega,?_⟩)⟩
      simpa only [show 3*t+2-1=3*t+1 by omega] using h.1
    rw [if_neg (by omega)]
    simpa only [hskip, decide_false] using hC
theorem chk_headR (c : LCtx) (i : Nat) (hi : i ≤ 42) (hnl : i % 3 ≠ 0 ∨ i = 42) (hck : i = 42 → c.ck < 8)
    (hd : c.dig i < 7) :
    vrun (c.startPc i) 8 =
      some (headRVB .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i
        (lowerG i)) := by
  have hp := c.part_at i hi hnl hck (fun h => by have := h.1; omega)
  unfold partOK at hp
  simp only [partOK, Bool.false_eq_true, ite_false] at hp
  rw [if_neg (by omega), Bool.and_eq_true] at hp
  exact rOK_eq hp.1
theorem chk_copyF (c : LCtx) (i : Nat) (hi : i ≤ 42) (hnl : i % 3 ≠ 0 ∨ i = 42) (hck : i = 42 → c.ck < 8)
    (hd : c.dig i = 7) (hNS : ¬c.bufferSafe i) :
    vrun (c.startPc i) 4 = some (copyFHB .x22 (offL i) (slotL i) (c.startPc i) (lowerG i)) := by
  have hp := c.part_at i hi hnl hck hNS
  unfold partOK at hp
  simp only [Bool.false_eq_true, ite_false] at hp
  rw [if_pos hd] at hp
  exact rOK_eq hp
theorem rungPc_inline (c : LCtx) (i : Nat) (hnl : i % 3 ≠ 0 ∨ i = 42) :
    c.rungPc i (c.dig i) + (if c.dig i = 6 then 2 else 1) = c.startPc i + 4 := by
  unfold rungPc
  rw [if_neg (by omega)]
  split_ifs <;> omega
theorem chk_rung (c : LCtx) (i m : Nat) (hi : i ≤ 42) (hm : c.dig i ≤ m) (hm6 : m ≤ 6)
    (hfirst : (i % 3 ≠ 0 ∨ i = 42) → c.dig i < m) (hck : i = 42 → c.ck < 8) :
    vrun (c.rungPc i m) 3 = some (rungRB m (if m = 6 then some (outL i) else none) (c.rungPc i m)) := by
  by_cases hl : i % 3 = 0 ∧ i ≠ 42
  · obtain ⟨h0, h42⟩ := hl
    obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t := ⟨i / 3, by omega⟩
    have et : 3 * t / 3 = t := by omega
    have hb := c.blk_at (3 * t) (by omega)
    rw [et] at hb
    unfold blkCheck at hb
    simp only [Bool.and_eq_true] at hb
    have := List.all_eq_true.mp hb.1.1.1 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : c.rungPc (3 * t) m = triBase t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) + 2 * m := by
      unfold rungPc tb; rw [if_pos ⟨h0, h42⟩, et]
    rw [hr]
    simpa using rOK_eq this
  · have hnl : i % 3 ≠ 0 ∨ i = 42 := by omega
    have hd := hfirst hnl
    have hp := c.part_at i hi hnl hck (fun h => by have := h.1; omega)
    unfold partOK at hp
    simp only [Bool.false_eq_true, ite_false] at hp
    rw [if_neg (by omega), Bool.and_eq_true] at hp
    have := List.all_eq_true.mp hp.2 m (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    have hr : c.rungPc i m = c.startPc i + 5 + 2 * (m - (c.dig i + 1)) := by
      unfold rungPc
      rw [if_neg hl]
      split_ifs <;> omega
    have hw : outL i = slotL i := by unfold outL; rw [if_neg (by omega)]
    rw [hr, hw]
    exact rOK_eq this
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem chk_rung' (c : LCtx) (i m : Nat) (hi : i ≤ 42) (hm : c.dig i < m) (hm6 : m ≤ 6) (hm1 : 1 ≤ m)
    (hck : i = 42 → c.ck < 8) :
    vrun (c.rungPc i m) 3 = some (rungRB m (if m = 6 then some (outL i) else none) (c.rungPc i m)) :=
  c.chk_rung i m hi (by omega) hm6 (fun _ => hm) hck
/-- The image's chain run from step `m` (C3: chain 0's last step keeps the high half, `stepHigh`). -/
def rest (c : LCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (7 - m)).foldlM
    (fun v step => Verify.vHash (stepHigh i step)
      (chainInputL c.lay c.tree c.leaf (i + c.koff) step (c.pad0 i) (c.pad1 i) (c.padHeader i) v (lowerG i))) v
theorem rest_succ (c : LCtx) (i m : Nat) (h : m ≤ 6) (v : Digest) :
    c.rest i m v =
      Verify.vHash (stepHigh i m)
        (chainInputL c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) (c.padHeader i) v (lowerG i)) >>=
        c.rest i (m + 1) := by
  unfold rest
  rw [show 7 - m = (7 - (m + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]
theorem rest_7 (c : LCtx) (i : Nat) (v : Digest) : c.rest i 7 v = pure v := rfl
theorem chainInputP_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) :
    pad64 (chainInputL lay tree leaf i step p0 p1 headerPad v g) = chainInputL lay tree leaf i step p0 p1 headerPad v g :=
  pad64_of_aligned _ (by rw [chainInputL_length])
theorem chainInputP_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : (toQ (chainInputL lay tree leaf i step p0 p1 headerPad v g)).blocks = 1 := by
  rw [blocks_toQ ⟨by rw [chainInputL_length]; omega, by rw [chainInputL_length]⟩, chainInputL_length]
theorem partLen_le (d : Nat) : partLen d ≤ 20 := by unfold partLen; split_ifs <;> omega
theorem partLen_ge (d : Nat) (hd : d < 8) : 4 ≤ partLen d := by unfold partLen; split_ifs <;> omega
theorem pcB_le_pcX (t b d : Nat) (hb : b<8) (hd : d<8) :
    pcB t b d ≤ pcX t b d := by
  have := partLen_ge b hb; have := partLen_ge d hd
  unfold pcX pcC; split_ifs <;> omega
theorem tX_lt (c : LCtx) (i : Nat) (hi : i < 42) : c.tX i < 257214 := by
  exact (lower_pc_bounds (i/3) _ _ (by omega) (c.dig_lt8 _ (by omega)) (c.dig_lt8 _ (by omega))).2
theorem startPc_lt (c : LCtx) (i : Nat) (hi : i ≤ 42) (hck : c.ck ≤ 8) (hRank : c.headOK i) : c.startPc i < 257214 := by
  by_cases h42 : i=42
  · subst i; simp only [startPc, if_true]; unfold ckSlot; omega
  have hb := c.dig_lt8 (3*(i/3)+1) (by omega)
  have hd := c.dig_lt8 (3*(i/3)+2) (by omega)
  have hx := c.tX_lt i (by omega)
  have hp := partLen_ge _ hb
  have hq := partLen_ge _ hd
  have e1 : i%3=1 → c.dig (3*(i/3)+1)=c.dig i := fun h=>by rw [show 3*(i/3)+1=i by omega]
  unfold startPc; rw [if_neg h42]
  by_cases h3 : i%3=0
  · rw [if_pos h3]
    exact lt_trans (entW_valid (i/3) _ (by omega) (c.kOf_lt _ (by omega)) (hRank h3 h42)) (by omega)
  · rw [if_neg h3]
    unfold tX pcX pcC at hx
    unfold tB tC pcC
    split_ifs at * <;> omega
theorem rungPc_land_lt (c : LCtx) (i m : Nat) (hi : i≤42) (hdm : c.dig i ≤ m)
    (hm : m ≤ 6) (hck : c.ck ≤ 8) : c.rungPc i m + landOff m < 257214 := by
  have hd6 : c.dig i<7 := by omega
  have he : c.endPc i<257214 := by
    by_cases h42 : i=42
    · subst i
      have hlen := partLen_le c.ck
      simp only [endPc,if_true]
      unfold ckSlot
      omega
    · have hb := c.dig_lt8 (3*(i/3)+1) (by omega)
      have hd := c.dig_lt8 (3*(i/3)+2) (by omega)
      have hx := c.tX_lt i (by omega)
      have hp := partLen_ge _ hb
      have hq := partLen_ge _ hd
      have hskip : ¬(0 < i ∧ c.dig i = 7 ∧ c.dig (i+1) = 7) := by omega
      unfold endPc
      simp only [if_neg h42,if_neg hskip,Nat.add_zero]
      unfold tX pcX pcC at hx
      unfold tB tC tX pcX pcC
      split_ifs at * <;> omega
  have hle : c.rungPc i m+landOff m ≤ c.rungPc i 6+3 := by
    unfold rungPc landOff
    split_ifs <;> omega
  rw [c.rungPc_end i hi hd6] at hle
  omega
theorem rungPc_lt (c : LCtx) (i m : Nat) (hi : i≤42) (hdm : c.dig i ≤ m)
    (hm : m ≤ 6) (hck : c.ck ≤ 8) : c.rungPc i m < 257214 := by
  have := c.rungPc_land_lt i m hi hdm hm hck
  omega
def ChainNext (c : LCtx) (s0 : MachineState) (j : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  if j ≤ 42 then c.ChainIn s0 j acc s else c.ChainOut s0 43 acc s
def xCost (i : Nat) : Nat :=
  if i = 42 then 0 else if i % 3 = 2 then (if i = 2 ∨ i = 23 then 2 else 3) else 0
theorem xCost_le (i : Nat) : xCost i ≤ 4 := by unfold xCost; split_ifs <;> omega
theorem end_next (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (i : Nat)
    (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8) (acc : List Digest) (s : MachineState)
    (hs : c.EndInv s0 i acc s) :
    ∃ u, Steps vimage s (xCost i) (xCost i) u ∧ c.ChainNext s0 (i + 1) acc u := by
  by_cases h42 : i = 42
  · subst h42
    refine ⟨s, by simpa [xCost] using Steps.refl s, ?_⟩
    unfold ChainNext; rw [if_neg (by omega)]
    exact c.ckend_out hc acc s hs
  · by_cases h2 : i % 3 = 2
    · by_cases h41 : i = 41
      · subst h41
        have hx := c.blk_at 41 (by omega)
        unfold blkCheck xOK at hx
        simp only [Bool.and_eq_true] at hx
        have hrun : vrun (c.tX 41) 4 = some ctabX := by
          have := rOK_eq hx.2; exact this
        obtain ⟨u, hst, hu⟩ := c.x13_step hc hk (by omega) (by have := c.tX_lt 41 (by omega); omega) hrun acc s hs
        refine ⟨u, by simpa [xCost] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega)]; exact hu
      · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t + 2 := ⟨i / 3, by omega⟩
        have hx := c.blk_at (3 * t + 2) (by omega)
        rw [show (3 * t + 2) / 3 = t by omega] at hx
        unfold blkCheck xOK at hx
        simp only [Bool.and_eq_true] at hx
        rw [if_neg (by omega)] at hx
        by_cases hbf : t = 5 ∨ t = 12
        · rw [if_pos hbf] at hx
          have hrun := rOK_eq hx.2
          have htx : c.tX (3 * t + 2) = pcX t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) := by
            unfold tX; rw [show (3 * t + 2) / 3 = t by omega]
          rw [← htx] at hrun
          obtain ⟨u, hst, hu⟩ := c.xbf_step hc hk t hbf hi.1 (by have := c.tX_lt (3 * t + 2) (by omega); omega) hrun acc s hs
          have hx3 : xCost (3 * t + 2) = 3 := by unfold xCost; split_ifs <;> omega
          refine ⟨u, by rw [hx3]; exact hst, ?_⟩
          unfold ChainNext; rw [if_pos (by omega), show 3 * t + 2 + 1 = 3 * t + 3 by ring]; exact hu
        rw [if_neg hbf] at hx
        have hrun := rOK_eq hx.2
        have htx : c.tX (3 * t + 2) = pcX t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) := by
          unfold tX; rw [show (3 * t + 2) / 3 = t by omega]
        rw [← htx] at hrun
        obtain ⟨u, hst, hu⟩ := c.x_step hc hk t (by omega) hi.1 (by have := c.tX_lt (3 * t + 2) (by omega); omega) hrun acc s hs
        have he : (9 * ((t + 1) % 7) = 9) ↔ (3 * t + 2 = 2 ∨ 3 * t + 2 = 23) := by
          omega
        refine ⟨u, by simpa [xCost, h42, h41, he] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega), show 3 * t + 2 + 1 = 3 * t + 3 by ring]; exact hu
    · refine ⟨s, by simpa [xCost, h42, h2] using Steps.refl s, ?_⟩
      unfold ChainNext; rw [if_pos (by omega)]
      exact c.next_inline s0 i (by omega) h2 acc s hs
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
def preCost (m : Nat) : Nat := 8 + 9 * (6 - m) + (if m < 6 then 1 else 0)
theorem steps_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8) (acc : List Digest)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → Verify.GoodQP P t N C Q A (K (acc ++ [v]))) :
    ∀ k m, m + k = 6 → c.dig i ≤ m → ∀ v s, c.PreHash s0 i acc m v s →
      Verify.GoodQP P s (N + 3 * (7 - m) + 4) (C + preCost m + xCost i) Q (A + preCost m + xCost i)
        (Verify.ccM (c.rest i m v) (fun v => K (acc ++ [v]))) := by
  have hrc : ∀ m, c.dig i ≤ m → m ≤ 6 → c.rungPc i m < 257214 := fun m hd hm => c.rungPc_lt i m hi.2 hd hm hc.2.2.2.2.2.2.1
  have hx4 := xCost_le i
  intro k
  induction k with
  | zero =>
    intro m hm hd v s hs
    obtain rfl : m = 6 := by omega
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i 6 hi (le_refl _) hd acc v s hs
    rw [rest_succ c i 6 (le_refl _)]
    have hf := hs.2.2.2.2.2.2.2.2.2
    have H : ∀ a : BitVec 256, Verify.GoodQP P (writeHash s a) (N + xCost i) (C + xCost i) Q (A + xCost i)
        (Verify.ccM (c.rest i 7 (Verify.vHalf (stepHigh i 6) a)) (fun v => K (acc ++ [v]))) := by
      intro a
      rw [rest_7, Verify.ccM_pure]
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi hck _ _ ((hpost a).2 rfl)
      exact Verify.GoodQP.stepsQ hu (hK _ _ hn) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := Verify.GoodQP.vHash_bind (stepHigh i 6) (f := c.rest i 7) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [chainInputP_pad]; exact hin) H
    rw [chainInputP_pad, chainInputP_blocks] at h3
    exact h3.mono (by omega) (by simp [preCost]; omega) (fun hq => ⟨hq, by simp [preCost]; omega⟩)
  | succ k ih =>
    intro m hm hd v s hs
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
    rw [rest_succ c i m (by omega)]
    have hf := hs.2.2.2.2.2.2.2.2.2
    have H : ∀ a : BitVec 256, Verify.GoodQP P (writeHash s a) (N + 3 * (7 - (m + 1)) + 4 + 2)
        (C + preCost (m + 1) + xCost i + (if m + 1 = 6 then 2 else 1)) Q
        (A + preCost (m + 1) + xCost i + (if m + 1 = 6 then 2 else 1))
        (Verify.ccM (c.rest i (m + 1) (Verify.vHalf (stepHigh i m) a)) (fun v => K (acc ++ [v]))) := by
      intro a
      have hrun := c.chk_rung' i (m + 1) hi.2 (by omega) (by omega) (by omega) hck
      obtain ⟨u, hu, hp⟩ := c.rung_step hc hk i (m + 1) hi (by omega) (hrc _ (by omega) (by omega)) hrun acc _ _
        ((hpost a).1 (by omega))
      have := ih (m + 1) (by omega) (by omega) _ _ hp
      exact Verify.GoodQP.stepsQ hu this (by split <;> omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := Verify.GoodQP.vHash_bind (stepHigh i m) (f := c.rest i (m + 1)) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [chainInputP_pad]; exact hin) H
    rw [chainInputP_pad, chainInputP_blocks] at h3
    refine h3.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · unfold preCost
      by_cases h6 : m + 1 = 6
      · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega
    · unfold preCost
      by_cases h6 : m + 1 = 6
      · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
def zc (_i d : Nat) : Nat := if d = 6 then 1 else 0
def chainCost (i d : Nat) : Nat :=
  (if i % 3 = 0 ∧ i ≠ 42 then (if d = 7 then 5 else 68 - 9 * d)
   else (if d = 7 then 4 else 67 - 9 * d)) - zc i d + xCost i
theorem chk_skipJ (c : LCtx) (hd : c.dig 0 = 7) (hRank : c.headOK 0) :
    vrun (c.startPc 0) 1 = some (skipJB (c.endPc 0)) := by
  have he := entCheck_at 0 (c.kOf 0) (by omega) (c.kOf_lt 0 (by omega))
  obtain ⟨k1,k2,k3⟩ := c.kOf_digits 0 (by omega)
  have hr := hRank (by decide) (by decide)
  simp only [Nat.zero_div] at hr
  unfold entCheck at he
  rw [if_neg (by omega), k1, k2, k3] at he
  simp only [Nat.mul_zero, Nat.zero_add, hd, if_true] at he
  simpa only [startPc,endPc,tB,Nat.zero_div,Nat.zero_mod,Nat.zero_mul,Nat.mul_zero,Nat.zero_add,show (0:Nat)≠42 by decide,
    Nat.lt_irrefl, false_and, if_false, if_true, Nat.add_zero] using rOK_eq he

theorem bufferSafe_pc (c : LCtx) (i : Nat) (hi : i≤42) (hiz : i≠0) (hS : c.bufferSafe i) :
    c.startPc i = c.endPc i := by
  have hd := hS.1
  have h42 : i≠42 := by rcases hS.2 with h|h|h <;> omega
  have hm : i%3≠0 := by rcases hS.2 with h|h|h <;> omega
  unfold startPc endPc
  simp only [if_neg h42, if_neg hm]
  by_cases h1 : i%3=1
  · simp only [if_pos h1]
    have eb : c.dig (3*(i/3)+1)=7 := by rw [show 3*(i/3)+1=i by omega,hd]
    have hp : i≠1 → c.dig (i-1)=7 := by intro hn; rcases hS.2 with h|h|h; omega; omega; exact h.2.2
    unfold tB tC pcC
    rw [eb]
    simp only [partLen, if_true]
    by_cases hz : i=1
    · subst i; norm_num
    · rw [if_pos ⟨by omega,hp hz,hd⟩, if_neg (by omega)]
      omega
  · simp only [if_neg h1]
    have eb : c.dig (3*(i/3)+1)=7 := by
      have hp : c.dig (i-1)=7 := by rcases hS.2 with h|h|h; omega; omega; exact h.2.2
      rwa [show i-1=3*(i/3)+1 by omega] at hp
    have ec : c.dig (3*(i/3)+2)=7 := by rw [show 3*(i/3)+2=i by omega,hd]
    unfold tC tX pcX
    rw [eb,ec]
    simp only [partLen,if_true,and_self,Nat.add_sub_cancel]

theorem copyPc_end (c : LCtx) (i : Nat) (hi : i≤42) (hnl : i%3≠0 ∨ i=42)
    (hd : c.dig i=7) (hNS : ¬c.bufferSafe i) : c.startPc i+4=c.endPc i := by
  by_cases h42 : i=42
  · subst i; rw [dig42] at hd
    simp only [startPc,endPc,if_true,hd]; rfl
  have h0 : i%3≠0 := by omega
  have h1 : i≠1 := by intro h; apply hNS; exact ⟨hd,Or.inr (Or.inl h)⟩
  have hp : c.dig (i-1)≠7 := by
    intro h; apply hNS; exact ⟨hd,Or.inr (Or.inr ⟨by omega,h0,h⟩)⟩
  unfold startPc endPc
  simp only [if_neg h42,if_neg h0]
  by_cases hm : i%3=1
  · simp only [if_pos hm]
    rw [if_neg (by tauto),Nat.add_zero]
    have eb : c.dig (3*(i/3)+1)=7 := by rw [show 3*(i/3)+1=i by omega,hd]
    unfold tB tC pcC
    rw [eb,if_neg (by omega)]
    simp only [partLen, if_true, Nat.sub_zero]
  · simp only [if_neg hm]
    have ec : c.dig (3*(i/3)+2)=7 := by rw [show 3*(i/3)+2=i by omega,hd]
    have eb : c.dig (3*(i/3)+1)≠7 := by simpa only [show 3*(i/3)+1=i-1 by omega] using hp
    unfold tC tX pcX
    rw [ec,if_neg (by tauto)]
    simp only [partLen, if_true, Nat.sub_zero]
theorem chain_good_raw (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8) (hRank : c.headOK i) (hNS : ¬c.bufferSafe i)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → Verify.GoodQP P t N C Q A (K (acc ++ [v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    Verify.GoodQP P s (N + 40) (C + chainCost i (c.dig i)) Q (A + chainCost i (c.dig i))
      (Verify.ccM (c.rest i (c.dig i) (c.val i)) (fun v => K (acc ++ [v]))) := by
  have hx4 := xCost_le i
  have hdl : c.dig i < 8 := by
    by_cases h42 : i = 42
    · subst h42; rw [dig42]; exact hck rfl
    · exact c.dig_lt8 i (by omega)
  have hsp := c.startPc_lt i hi.2 hc.2.2.2.2.2.2.1 hRank
  by_cases h7 : c.dig i = 7
  ·
    rw [h7]
    have hspec : c.rest i 7 (c.val i) = pure (c.val i) := rfl
    rw [hspec, Verify.ccM_pure]
    by_cases hl : i % 3 = 0 ∧ i ≠ 42
    · obtain ⟨h0', h42⟩ := hl
      have hrun := c.chk_copyJ i (by omega) h0' h7 hRank (fun h => hNS ⟨h7,Or.inl h⟩)
      obtain ⟨t, hst, hE⟩ := c.copyJ_step hc hk h0 i ⟨hi.1, by omega⟩
        (Nat.pos_of_ne_zero (fun h => hNS ⟨h7, Or.inl h⟩)) (i / 3 == 0)
        (fun h => by
          have : i = 0 := by simp at h; omega
          exact ⟨this, hko (by omega)⟩)
        (fun h => by simp at h; omega) hsp hrun acc s hs
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi hck _ _ hE
      refine Verify.GoodQP.stepsQ hst (Verify.GoodQP.stepsQ hu (hK _ u hn) (le_refl _) (le_refl _)
        (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost zc; simp [h0', h7, h42]; omega)
        (fun hq => ⟨hq, by unfold chainCost zc; simp [h0', h7, h42]; omega⟩)
    · have hnl : i % 3 ≠ 0 ∨ i = 42 := by omega
      have hrun := c.chk_copyF i hi.2 hnl hck h7 hNS
      have hend := c.copyPc_end i hi.2 hnl h7 hNS
      obtain ⟨t, hst, hE⟩ := c.copyF_step hc hk h0 i hi (by omega) hsp hend hrun acc s hs
      obtain ⟨u, hu, hn⟩ := c.end_next hc hk i hi hck _ _ hE
      refine Verify.GoodQP.stepsQ hst (Verify.GoodQP.stepsQ hu (hK _ u hn) (le_refl _) (le_refl _)
        (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost zc; simp [hl, h7]; omega)
        (fun hq => ⟨hq, by unfold chainCost zc; simp [hl, h7]; omega⟩)
  ·
    have hd : c.dig i < 7 := by omega
    have hsteps := c.steps_good hc hk h0 i hi hck acc K N C A Q hK (6 - c.dig i) (c.dig i) (by omega) (le_refl _)
    have hrp := c.rungPc_lt i (c.dig i) hi.2 (le_refl _) (by omega) hc.2.2.2.2.2.2.1
    by_cases hl : i % 3 = 0 ∧ i ≠ 42
    · obtain ⟨h0', h42⟩ := hl
      have hruns := c.chk_headJ i (by omega) h0' hd hRank
      obtain ⟨t, hst, hP⟩ := c.headJ_step hc hk h0 i hi hd hsp
        (c.rungPc_land_lt i (c.dig i) hi.2 (le_refl _) (by omega) hc.2.2.2.2.2.2.1) hruns.1 hruns.2 acc s hs
      refine Verify.GoodQP.stepsQ hst (hsteps _ _ hP) (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost zc; rw [if_pos (show i % 3 = 0 ∧ i ≠ 42 from ⟨h0', h42⟩), if_neg h7]
        split_ifs <;> omega
      · unfold chainCost preCost zc; rw [if_pos (show i % 3 = 0 ∧ i ≠ 42 from ⟨h0', h42⟩), if_neg h7]
        split_ifs <;> omega
    · have hnl : i % 3 ≠ 0 ∨ i = 42 := by omega
      have hrun := c.chk_headR i hi.2 hnl hck hd
      obtain ⟨t, hst, hP⟩ := c.headR_step hc hk h0 i hi (by omega) hd hsp
        (c.rungPc_inline i hnl) hrun acc s hs
      refine Verify.GoodQP.stepsQ hst (hsteps _ _ hP) (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost zc; rw [if_neg hl, if_neg h7]
        split_ifs <;> omega
      · unfold chainCost preCost zc; rw [if_neg hl, if_neg h7]
        split_ifs <;> omega
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
def bufferCost (c : LCtx) (i : Nat) : Nat := chainCost i (c.dig i) - (if c.bufferSafe i then 4 else 0)
theorem chain_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42)
    (hck : i = 42 → c.ck < 8) (hRank : c.headOK i)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → Verify.GoodQP P t N C Q A (K (acc ++ [v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    Verify.GoodQP P s (N + 40) (C + c.bufferCost i) Q (A + c.bufferCost i)
      (Verify.ccM (c.rest i (c.dig i) (c.bufferVal i)) (fun v=>K (acc++[v]))) := by
  by_cases hSafe : c.bufferSafe i
  · have h7 := hSafe.1
    have hpure : c.rest i (c.dig i) (c.bufferVal i) = pure (c.bufferVal i) := by rw [h7]; rfl
    rw [hpure,Verify.ccM_pure]
    by_cases hz : i=0
    · subst i
      have hr := c.chk_skipJ h7 hRank
      obtain ⟨t,ht,he⟩ := c.buffer_skip_jump hc h0 0 hi hSafe
        (c.startPc_lt 0 hi.2 hc.2.2.2.2.2.2.1 hRank) hr acc hs
      obtain ⟨u,hu,hn⟩ := c.end_next hc hk 0 hi hck _ _ he
      have H := Verify.GoodQP.stepsQ ht (Verify.GoodQP.stepsQ hu (hK _ _ hn)
        (le_refl _) (le_refl _) (fun h=>⟨h,le_refl _⟩))
        (show N+xCost 0+1≤N+40 by simp [xCost])
        (show C+xCost 0+1≤C+c.bufferCost 0 by simp [bufferCost,hSafe,chainCost,h7,zc,xCost])
        (fun h=>⟨h,show A+xCost 0+1≤A+c.bufferCost 0 by simp [bufferCost,hSafe,chainCost,h7,zc,xCost]⟩)
      exact H
    · have he := c.buffer_skip_inline hc h0 i hi hSafe (c.bufferSafe_pc i hi.2 hz hSafe) acc hs
      obtain ⟨u,hu,hn⟩ := c.end_next hc hk i hi hck _ _ he
      have hnmod : ¬(i%3=0 ∧ i≠42) := by rcases hSafe.2 with h|h|h <;> omega
      have hcost : c.bufferCost i = xCost i := by simp only [bufferCost,if_pos hSafe,chainCost,if_neg hnmod,h7,if_true,zc,show (7:Nat)≠6 by decide,if_false,Nat.sub_zero]; omega
      exact Verify.GoodQP.stepsQ hu (hK _ _ hn) (by have:=xCost_le i; omega)
        (by rw [hcost]) (fun h=>⟨h,by rw [hcost]⟩)
  · simpa only [bufferCost,if_neg hSafe,Nat.sub_zero,bufferVal] using
      c.chain_good_raw hc hk h0 hko i hi hck hRank hSafe acc K N C A Q hK s hs

theorem bufferCost_ck (c : LCtx) : c.bufferCost 42 = chainCost 42 c.ck := by
  have hn : ¬c.bufferSafe 42 := by intro h; rcases h.2 with h|h|h <;> omega
  simp only [bufferCost,if_neg hn,Nat.sub_zero,c.dig42]
def chainF (c : LCtx) (ends : List Digest) (i : Nat) : M (List Digest) := do
  let v ← c.rest i (c.dig i) (c.bufferVal i)
  pure (ends ++ [v])
def chainsCost (c : LCtx) (i k : Nat) : Nat := ((List.range' i k).map c.bufferCost).sum
theorem chains_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (last : Nat) (hLast : last ≤ 42)
    (hRanks : ∀ j, c.i0 ≤ j → j < last → c.headOK j) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop) (hK : ∀ ends t, c.ChainIn s0 last ends t → Verify.GoodQP P t N C Q A (K ends)) :
    ∀ k i, i + k = last → c.i0 ≤ i → ∀ acc s, c.ChainIn s0 i acc s →
      Verify.GoodQP P s (N + 40 * k) (C + c.chainsCost i k) Q (A + c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero =>
    intro i hik _ acc s hs
    obtain rfl : i = last := by omega
    simpa [chainsCost] using hK acc s hs
  | succ k ih =>
    intro i hik hi0 acc s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, Verify.ccM_bind]
    have := c.chain_good hc hk h0 hko i ⟨hi0, by omega⟩ (fun h => absurd h (by omega)) (hRanks i hi0 (by omega)) acc
      (fun ends => Verify.ccM ((List.range' (i + 1) k).foldlM c.chainF ends) K)
      (N + 40 * k) (C + c.chainsCost (i + 1) k) (A + c.chainsCost (i + 1) k) Q
      (fun v t ht => by
        have ht' : c.ChainIn s0 (i + 1) (acc ++ [v]) t := by
          unfold ChainNext at ht; rwa [if_pos (by omega)] at ht
        exact ih (i + 1) (by omega) (by omega) (acc ++ [v]) t ht') s hs
    refine this.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega
theorem chains_prefix_fault (c : LCtx) (hc : c.ok) (hi0 : c.i0=0) (hko : c.koff=0)
    {s0 : MachineState} (hk : ∀ p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (j : Nat) (hj : j<14) (hBad : c.kOf j<rankFloor j)
    (hRanks : ∀i,i<3*j→c.headOK i) (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQP P s (1+40*(3*j)) (c.chainsCost 0 (3*j)) False (c.chainsCost 0 (3*j))
      (Verify.ccM ((List.range' 0 (3*j)).foldlM c.chainF []) (fun _ => pure (false, 0))) := by
  have hK : ∀ ends t, c.ChainIn s0 (3*j) ends t → Verify.GoodQP P t 1 0 False 0 (pure (false, 0)) := by
    intro ends t ht
    have hpc := ht.2.2.2
    have hp : t.pc.toNat<0x1000 := by
      rw [hpc]
      simp only [startPc,show ¬3*j=42 by omega,if_false,show 3*j%3=0 by omega,if_true,show 3*j/3=j by omega]
      exact entW_fault_address j (c.kOf j) hj hBad
    have hf : fetch vimage t=none := by unfold fetch; simp [hp]
    intro F hF
    have he : F=(F-1)+1 := by omega
    refine ⟨?_,fun hash=>?_⟩
    · rw [he,execute_fetch_none (F-1) hf,map_pure]; rfl
    · have hx : evalWithAnswerFn hash (Riscv.execute (F-1+1) vimage t)=⟨.failure,t,0,0,0⟩ := by
        rw [execute_fetch_none (F-1) hf]; rfl
      rw [he,hx]
      exact ⟨by simp,Nat.zero_le _,fun h _ => by simp at h⟩
  have H := c.chains_good hc hk h0 (fun _ => hko) (3*j) (by omega) (fun i _ hi=>hRanks i hi)
    (fun _ => pure (false, 0)) 1 0 0 False hK (3*j) 0 (by omega) (by omega) [] s hs
  simpa using H
theorem chainsCost_prefix_le (c : LCtx) (n : Nat) (hn : n≤42) : c.chainsCost 0 n≤c.chainsCost 0 42 := by
  have he : 42=n+(42-n) := by omega
  unfold chainsCost
  conv_rhs => rw [he,←List.range'_append,List.map_append,List.sum_append]
  omega
theorem ck_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (hck : c.ck < 8)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → Verify.GoodQP P t N C Q A (K ends))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 42 acc s) :
    Verify.GoodQP P s (N + 40) (C + chainCost 42 c.ck) Q (A + chainCost 42 c.ck)
      (Verify.ccM (c.chainF acc 42) K) := by
  have := c.chain_good hc hk h0 hko 42 ⟨hc.2.2.2.2.2.2.2.2.1, le_refl _⟩ (fun _ => hck) (by intro _ h; exact (h rfl).elim) acc K N C A Q
    (fun v t ht => by
      have ht' : c.ChainOut s0 43 (acc ++ [v]) t := by unfold ChainNext at ht; rwa [if_neg (by omega)] at ht
      exact hK _ t ht') s hs
  simp only [chainF, Verify.ccM_bind, Verify.ccM_pure]
  rw [dig42] at this ⊢
  simpa only [bufferCost_ck] using this
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
def cbase (i : Nat) : Nat := (if i % 3 = 0 ∧ i ≠ 42 then 68 else 67) + xCost i
theorem chainCost_add (i d : Nat) (hd : d < 8) : chainCost i d + 9 * d + zc i d = cbase i := by
  unfold chainCost zc cbase
  split_ifs <;> omega
def savedCopy (c : LCtx) (i : Nat) : Nat := if c.bufferSafe i then 1 else 0
def savedCopies (c : LCtx) (i k : Nat) : Nat := ((List.range' i k).map c.savedCopy).sum
theorem bufferCost_add (c : LCtx) (i : Nat) (hd : c.dig i<8) :
    c.bufferCost i + 9*c.dig i + zc i (c.dig i) + 4*c.savedCopy i = cbase i := by
  have h := chainCost_add i (c.dig i) hd
  by_cases hs : c.bufferSafe i
  · have hd7 := hs.1
    have hh : 4≤chainCost i (c.dig i) := by rw [hd7]; unfold chainCost zc; split_ifs <;> omega
    simp only [bufferCost,savedCopy,if_pos hs]
    omega
  · simpa only [bufferCost,savedCopy,if_neg hs,Nat.sub_zero,Nat.mul_zero,Nat.add_zero] using h
theorem chainsCost_add (c : LCtx) (hck : c.ck < 8) : ∀ k i, i + k ≤ 43 →
    c.chainsCost i k + 9 * ((List.range' i k).map c.dig).sum + ((List.range' i k).map fun j => zc j (c.dig j)).sum + 4*c.savedCopies i k =
      ((List.range' i k).map cbase).sum := by
  intro k
  induction k with
  | zero => intro i _; simp [chainsCost,savedCopies]
  | succ k ih =>
    intro i hik
    have h := ih (i + 1) (by omega)
    have hd : c.dig i < 8 := by
      by_cases h42 : i = 42
      · subst h42; rw [dig42]; exact hck
      · exact c.dig_lt8 i (by omega)
    have := c.bufferCost_add i hd
    simp only [chainsCost, savedCopies, List.range'_succ, List.map_cons, List.sum_cons] at h ⊢
    omega
theorem cbase_sum43 : ((List.range' 0 43).map cbase).sum = 2935 := by decide +kernel
theorem cbase_sum_top : ((List.range' 33 9).map cbase).sum = 615 := by decide +kernel
def zSum (c : LCtx) (i k : Nat) : Nat := ((List.range' i k).map fun j => zc j (c.dig j)).sum
theorem chainsCost_lower (c : LCtx) (hck : c.ck < 8) (T : Nat) (hT : ((List.range' 0 43).map c.dig).sum = T) :
    c.chainsCost 0 42 + chainCost 42 c.ck + 9 * T + c.zSum 0 43 + 4*c.savedCopies 0 43 = 2935 := by
  have h := c.chainsCost_add hck 43 0 (le_refl _)
  rw [hT, cbase_sum43] at h
  have e : c.chainsCost 0 43 = c.chainsCost 0 42 + chainCost 42 c.ck := by
    unfold chainsCost
    rw [show (43 : Nat) = 42 + 1 from rfl, List.range'_concat, List.map_append, List.sum_append]
    simp [dig42,bufferCost_ck]
  unfold zSum
  omega
theorem chainsCost_top (c : LCtx) (hck : c.ck < 8) (S : Nat) (hS : ((List.range' 33 9).map c.dig).sum = S) :
    c.chainsCost 33 9 + 9 * S + c.zSum 33 9 + 4*c.savedCopies 33 9 = 615 := by
  have h := c.chainsCost_add hck 9 33 (by omega)
  rw [hS, cbase_sum_top] at h
  unfold zSum
  omega
theorem bufferSafe_iff (c : LCtx) (hlay : c.lay ≠ 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) (i : Nat) (hi : i < 43) :
    c.bufferSafe i ↔ ClaudeWCT.WCT9.safeZeroCopy c.lay D i := by
  simp only [bufferSafe, ClaudeWCT.WCT9.safeZeroCopy, maxDigit, if_neg hlay,
    hD i hi, hD (i-1) (by omega), ne_eq, hlay, not_false_eq_true, true_and, if_false, false_and]
theorem bufferSlot_eq (c : LCtx) (hlay : c.lay ≠ 0) (i : Nat) :
    c.bufferSlot i = Verify.WIT + ClaudeWCT.W9.T3M.leafBufferSlot c.lay i := by
  have : 18928 ≤ ClaudeWCT.W9.T3M.leafBufferBase c.lay := by
    generalize c.lay = lay; fin_cases lay <;> decide +kernel
  unfold bufferSlot bufferOffset slotL ClaudeWCT.W9.T3M.leafBufferSlot
  rw [if_neg hlay]
  split_ifs <;> omega
theorem chainSlot_lower {lay : Layer} (hlay : lay ≠ 0) (i : Nat) :
    ClaudeWCT.W9.T3M.chainSlot lay i = lowerSlot i := by
  have : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  simp [ClaudeWCT.W9.T3M.chainSlot, lowerSlot, this]
theorem valueOff_lower {lay : Layer} (hlay : lay ≠ 0) (i : Nat) :
    ClaudeWCT.W9.T3M.valueOff lay i = gVal (lowerG i) := by
  simp [ClaudeWCT.W9.T3M.valueOff, gVal, lowerG, ClaudeWCT.WCT9.isG, hlay]
theorem bufferVal_eq (c : LCtx) (hlay : c.lay ≠ 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hS6 : c.S6 = Verify.WIT + ClaudeWCT.W9.T3M.layerBase c.lay + 16 * ClaudeWCT.W9.T3M.pathSlots c.lay + 520)
    (i : Nat) (hi : i < 43) :
    c.bufferVal i = ClaudeWCT.W9.T3M.wvalueFor c.w c.lay D i := by
  have hb : c.vAt i - Verify.WIT = ClaudeWCT.W9.T3M.chainBlock c.lay i + ClaudeWCT.W9.T3M.valueOff c.lay i := by
    unfold vAt blk ClaudeWCT.W9.T3M.chainBlock
    rw [chainSlot_lower hlay, valueOff_lower hlay, hS6]; omega
  unfold bufferVal ClaudeWCT.W9.T3M.wvalueFor
  simp only [c.bufferSafe_iff hlay D hD i hi]
  split_ifs
  · rw [c.bufferSlot_eq hlay i, Nat.add_sub_cancel_left]
  · simp only [val, ClaudeWCT.W9.T3M.wvalue, hb]
end LCtx
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_LowerDecode ====
section

section
set_option maxRecDepth 10000

namespace ClaudeWCT.WCT9
open SigGolfCandidate.T3
def decodeV5Lower (lay : Layer) (n : Nat) : Option (List Nat) :=
  if n ≥ 2 ^ 126 then none else
  let digits := (List.range 42).map fun i => n / 2 ^ (3 * i) % 8
  let total := digits.sum
  if total ≤ target lay ∧ target lay - total < 8 then some (digits ++ [target lay - total]) else none
def producerDecodeV5Lower (lay : Layer) (n : Nat) : Option (List Nat) :=
  (decodeV5Lower lay n).bind fun digits =>
    if producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits ∧
        producerZeroBound lay digits ∧
        producerRankBound lay (lowerPack n)
    then some digits else none
theorem producerDecode_eq_bind (lay : Layer) (v : Digest) :
    producerDecode lay v =
      (decode lay v).bind fun digits =>
        if producerFloor lay + dispatchPenalty lay digits ≤ wordCredit lay digits + 4 * savedCopies lay digits ∧
        producerZeroBound lay digits ∧ producerRankBound lay v
        then some digits else none := by
  unfold producerDecode
  generalize decode lay v = x
  cases x <;> rfl
theorem decode_lower_eq {lay : Layer} (hlay : lay ≠ 0) (v : Digest) :
    decode lay v = if lowerSpare v then decodeV5Lower lay (lowerWord v) else none := by
  have hw := lowerWord_lt v
  rw [decode_lowerWord hlay v]
  unfold decodeV5Lower
  rw [if_neg (show ¬ lowerWord v ≥ 2 ^ 126 by omega)]
  dsimp only
  by_cases hs : lowerSpare v
  · rw [if_pos hs]
    by_cases hc : ((List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8).sum ≤ target lay ∧
        target lay - ((List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8).sum < 8
    · rw [if_pos ⟨hs, hc⟩, if_pos hc]
    · rw [if_neg (fun h => hc h.2), if_neg hc]
  · rw [if_neg hs, if_neg (fun h => hs h.1)]
theorem producerDecode_lower_eq {lay : Layer} (hlay : lay ≠ 0) (v : Digest) :
    producerDecode lay v = if lowerSpare v then producerDecodeV5Lower lay (lowerWord v) else none := by
  rw [producerDecode_eq_bind, decode_lower_eq hlay]
  by_cases hs : lowerSpare v
  · rw [if_pos hs, if_pos hs]
    unfold producerDecodeV5Lower
    rw [lowerPack_lowerWord hs]
  · rw [if_neg hs, if_neg hs]
    rfl
theorem decode_lowerPack {lay : Layer} (hlay : lay ≠ 0) {n : Nat} (hn : n < 2 ^ 126) :
    decode lay (lowerPack n) = decodeV5Lower lay n := by
  rw [decode_lower_eq hlay, if_pos (lowerSpare_lowerPack n), lowerWord_lowerPack hn]
theorem producerDecode_lowerPack {lay : Layer} (hlay : lay ≠ 0) {n : Nat} (hn : n < 2 ^ 126) :
    producerDecode lay (lowerPack n) = producerDecodeV5Lower lay n := by
  rw [producerDecode_lower_eq hlay, if_pos (lowerSpare_lowerPack n), lowerWord_lowerPack hn]
def lowerEquiv : {n : Nat // n < 2 ^ 126} ≃ {v : Digest // lowerSpare v} where
  toFun n := ⟨lowerPack n.val, lowerSpare_lowerPack n.val⟩
  invFun v := ⟨lowerWord v.val, lowerWord_lt v.val⟩
  left_inv n := Subtype.ext (lowerWord_lowerPack n.property)
  right_inv v := Subtype.ext (lowerPack_lowerWord v.property)
theorem card_lower_transfer (f : Digest → Option (List Nat)) (g : Nat → Option (List Nat))
    (hf : ∀ v, f v = if lowerSpare v then g (lowerWord v) else none)
    (P : Option (List Nat) → Prop) [DecidablePred P] (hP : ¬ P none) :
    (Finset.univ.filter fun v : Digest => P (f v)).card =
      ((Finset.range (2 ^ 126)).filter fun n => P (g n)).card := by
  have hs : ∀ v, P (f v) → lowerSpare v ∧ P (g (lowerWord v)) := by
    intro v hv
    rw [hf] at hv
    by_cases h : lowerSpare v
    · rw [if_pos h] at hv; exact ⟨h, hv⟩
    · rw [if_neg h] at hv; exact absurd hv hP
  refine Finset.card_bij' (fun v _ => lowerWord v) (fun n _ => lowerPack n) ?_ ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_range.mpr (lowerWord_lt v), (hs v hv.2).2⟩
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_filter, hf, if_pos (lowerSpare_lowerPack n), lowerWord_lowerPack hn.1]
    exact ⟨Finset.mem_univ _, hn.2⟩
  · intro v hv
    rw [Finset.mem_filter] at hv
    exact lowerPack_lowerWord (hs v hv.2).1
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    exact lowerWord_lowerPack hn.1
theorem card_decode_lower {lay : Layer} (hlay : lay ≠ 0) (P : Option (List Nat) → Prop) [DecidablePred P]
    (hP : ¬ P none) :
    (Finset.univ.filter fun v : Digest => P (decode lay v)).card =
      ((Finset.range (2 ^ 126)).filter fun n => P (decodeV5Lower lay n)).card :=
  card_lower_transfer (decode lay) (decodeV5Lower lay) (decode_lower_eq hlay) P hP
theorem card_producerDecode_lower {lay : Layer} (hlay : lay ≠ 0) (P : Option (List Nat) → Prop) [DecidablePred P]
    (hP : ¬ P none) :
    (Finset.univ.filter fun v : Digest => P (producerDecode lay v)).card =
      ((Finset.range (2 ^ 126)).filter fun n => P (producerDecodeV5Lower lay n)).card :=
  card_lower_transfer (producerDecode lay) (producerDecodeV5Lower lay) (producerDecode_lower_eq hlay) P hP
end ClaudeWCT.WCT9
end

section



namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]
theorem split3 (n M : Nat) : n &&& (64 * M + 7) = 64 * ((n / 64) &&& M) + n % 8 :=
  land_split n M 3 6 (by decide)
theorem split6 (n M : Nat) : n &&& (4096 * M + 63) = 4096 * ((n / 4096) &&& M) + n % 64 :=
  land_split n M 6 12 (by decide)
theorem split2 (n M : Nat) : n &&& (16 * M + 3) = 16 * ((n / 16) &&& M) + n % 4 :=
  land_split n M 2 4 (by decide)
theorem split4 (n M : Nat) : n &&& (256 * M + 15) = 256 * ((n / 256) &&& M) + n % 16 :=
  land_split n M 4 8 (by decide)
theorem and7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3
theorem and15 (n : Nat) : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4
theorem and3 (n : Nat) : n &&& 3 = n % 4 := Nat.and_two_pow_sub_one_eq_mod n 2
def mask3 : Nat := 8198552921648689607
def mask6 : Nat := 17311559823019733055
def mask2 : Nat := 3689348814741910323
def mask4 : Nat := 1085102592571150095
theorem landM1 (n : Nat) : n &&& mask3 =
    64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 % 8) + n / 64 / 64 % 8) + n / 64 % 8) + n % 8 := by
  rw [show mask3 = 64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * 7 + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7 by
    norm_num [mask3]]
  simp only [split3, and7]
theorem landM2 (n : Nat) : n &&& mask6 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 4096 / 4096 / 4096 / 4096 / 4096 % 16)
    + n / 4096 / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 % 64)
    + n / 4096 % 64) + n % 64 := by
  rw [show mask6 = 4096 * (4096 * (4096 * (4096 * (4096 * 15 + 63) + 63) + 63) + 63) + 63 by norm_num [mask6]]
  simp only [split6, and15]
def sw1 (a b : Nat) : Nat :=
  ((((a / 8 &&& mask3) + (a &&& mask3)) % 18446744073709551616 + (b / 8 &&& mask3)) % 18446744073709551616 +
    (b &&& mask3)) % 18446744073709551616
def lowSwar (a b : Nat) : Nat := ((sw1 a b + sw1 a b / 64) % 18446744073709551616 &&& mask6) % 4095
theorem hdiv64 (c R : Nat) (h : c < 64) : (c + 64 * R) / 64 = R := by omega
theorem hmod64 (c R : Nat) (h : c < 64) : (c + 64 * R) % 64 = c := by omega
theorem landM2' (n : Nat) : n &&& mask6 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 16)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 / 64 / 64 / 64 / 64 % 64)
    + n / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 % 64) + n % 64 := by
  rw [landM2]; simp only [Nat.div_div_eq_div_mul]
theorem fold_mod4095 (a b c d e f : Nat) :
    (a + 4096 * (b + 4096 * (c + 4096 * (d + 4096 * (e + 4096 * f))))) % 4095 =
      (a + b + c + d + e + f) % 4095 := by
  omega
theorem swarLanes (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 : Nat) (h0 : L0 ≤ 28) (h1 : L1 ≤ 28) (h2 : L2 ≤ 28)
    (h3 : L3 ≤ 28) (h4 : L4 ≤ 28) (h5 : L5 ≤ 28) (h6 : L6 ≤ 28) (h7 : L7 ≤ 28) (h8 : L8 ≤ 28) (h9 : L9 ≤ 28)
    (h10 : L10 ≤ 15) (X : Nat)
    (hX : X = L0 + 64 * (L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 +
      64 * (L9 + 64 * L10)))))))))) :
    ((X + X / 64) % 18446744073709551616 &&& mask6) % 4095 =
      L0 + L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10 := by
  have e1 : X / 64 = L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 +
      64 * (L9 + 64 * L10)))))))) := by rw [hX]; exact hdiv64 _ _ (by omega)
  have e2 : X + X / 64 = (L0 + L1) + 64 * ((L1 + L2) + 64 * ((L2 + L3) + 64 * ((L3 + L4) + 64 * ((L4 + L5) +
      64 * ((L5 + L6) + 64 * ((L6 + L7) + 64 * ((L7 + L8) + 64 * ((L8 + L9) + 64 * ((L9 + L10) +
      64 * L10))))))))) := by
    omega
  have e3 : X + X / 64 < 18446744073709551616 := by rw [e2]; omega
  have e4 : (X + X / 64) % 18446744073709551616 &&& mask6 = (L0 + L1) + 4096 * ((L2 + L3) + 4096 * ((L4 + L5) +
      4096 * ((L6 + L7) + 4096 * ((L8 + L9) + 4096 * L10)))) := by
    rw [Nat.mod_eq_of_lt e3, e2, landM2']
    simp (disch := omega) only [hdiv64, hmod64]
    rw [Nat.mod_eq_of_lt (show L10 < 16 by omega)]
    omega
  rw [e4]
  clear e1 e2 e3 e4 hX
  have hlt : L0 + L1 + (L2 + L3) + (L4 + L5) + (L6 + L7) + (L8 + L9) + L10 < 4095 := by omega
  rw [fold_mod4095, Nat.mod_eq_of_lt hlt]
  ac_rfl
def dsum21 (a : Nat) : Nat :=
  a % 8 + a / 8 % 8 + a / 64 % 8 + a / 512 % 8 + a / 4096 % 8 + a / 32768 % 8 + a / 262144 % 8 +
    a / 2097152 % 8 + a / 16777216 % 8 + a / 134217728 % 8 + a / 1073741824 % 8 +
    a / 8589934592 % 8 + a / 68719476736 % 8 + a / 549755813888 % 8 + a / 4398046511104 % 8 +
    a / 35184372088832 % 8 + a / 281474976710656 % 8 + a / 2251799813685248 % 8 +
    a / 18014398509481984 % 8 + a / 144115188075855872 % 8 + a / 1152921504606846976 % 8
theorem dsum21_eq (a : Nat) : dsum21 a = ((List.range 21).map fun i => a / 8 ^ i % 8).sum := by
  simp only [dsum21, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]
theorem lowSwar_eq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 63) :
    lowSwar a b = dsum21 a + a / 2 ^ 63 + dsum21 b := by
  have hat : a / 9223372036854775808 ≤ 1 := by omega
  have ha' : a / 9223372036854775808 % 8 = a / 9223372036854775808 := Nat.mod_eq_of_lt (by omega)
  have hb' : b / 9223372036854775808 = 0 := Nat.div_eq_of_lt hb
  unfold lowSwar dsum21
  generalize hX : sw1 a b = X
  unfold sw1 at hX
  simp only [landM1, Nat.div_div_eq_div_mul] at hX
  norm_num at hX
  rw [ha'] at hX
  simp only [hb', Nat.zero_mod, Nat.mul_zero] at hX
  norm_num
  clear ha'
  generalize a / 9223372036854775808 = a21 at *
  have ha0 : a % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a % 8 = a0 at *
  have ha1 : a / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8 % 8 = a1 at *
  have ha2 : a / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 64 % 8 = a2 at *
  have ha3 : a / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 512 % 8 = a3 at *
  have ha4 : a / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4096 % 8 = a4 at *
  have ha5 : a / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 32768 % 8 = a5 at *
  have ha6 : a / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 262144 % 8 = a6 at *
  have ha7 : a / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2097152 % 8 = a7 at *
  have ha8 : a / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 16777216 % 8 = a8 at *
  have ha9 : a / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 134217728 % 8 = a9 at *
  have ha10 : a / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1073741824 % 8 = a10 at *
  have ha11 : a / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8589934592 % 8 = a11 at *
  have ha12 : a / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 68719476736 % 8 = a12 at *
  have ha13 : a / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 549755813888 % 8 = a13 at *
  have ha14 : a / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4398046511104 % 8 = a14 at *
  have ha15 : a / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 35184372088832 % 8 = a15 at *
  have ha16 : a / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 281474976710656 % 8 = a16 at *
  have ha17 : a / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2251799813685248 % 8 = a17 at *
  have ha18 : a / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 18014398509481984 % 8 = a18 at *
  have ha19 : a / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 144115188075855872 % 8 = a19 at *
  have ha20 : a / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1152921504606846976 % 8 = a20 at *
  have hb0 : b % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b % 8 = b0 at *
  have hb1 : b / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8 % 8 = b1 at *
  have hb2 : b / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 64 % 8 = b2 at *
  have hb3 : b / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 512 % 8 = b3 at *
  have hb4 : b / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4096 % 8 = b4 at *
  have hb5 : b / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 32768 % 8 = b5 at *
  have hb6 : b / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 262144 % 8 = b6 at *
  have hb7 : b / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2097152 % 8 = b7 at *
  have hb8 : b / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 16777216 % 8 = b8 at *
  have hb9 : b / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 134217728 % 8 = b9 at *
  have hb10 : b / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1073741824 % 8 = b10 at *
  have hb11 : b / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8589934592 % 8 = b11 at *
  have hb12 : b / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 68719476736 % 8 = b12 at *
  have hb13 : b / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 549755813888 % 8 = b13 at *
  have hb14 : b / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4398046511104 % 8 = b14 at *
  have hb15 : b / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 35184372088832 % 8 = b15 at *
  have hb16 : b / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 281474976710656 % 8 = b16 at *
  have hb17 : b / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2251799813685248 % 8 = b17 at *
  have hb18 : b / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 18014398509481984 % 8 = b18 at *
  have hb19 : b / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 144115188075855872 % 8 = b19 at *
  have hb20 : b / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1152921504606846976 % 8 = b20 at *
  clear ha hb hb'
  rw [swarLanes (a0 + a1 + b0 + b1) (a2 + a3 + b2 + b3) (a4 + a5 + b4 + b5) (a6 + a7 + b6 + b7)
    (a8 + a9 + b8 + b9) (a10 + a11 + b10 + b11) (a12 + a13 + b12 + b13) (a14 + a15 + b14 + b15)
    (a16 + a17 + b16 + b17) (a18 + a19 + b18 + b19) (a20 + a21 + b20) (by clear hX; omega)
    (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega)
    (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) X (by
    rw [← hX]
    clear hX
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    omega)]
  clear hX
  ac_rfl
theorem div_mod_add_pow (x y k m w : Nat) (h : k + w ≤ m) :
    (x + 2 ^ m * y) / 2 ^ k % 2 ^ w = x / 2 ^ k % 2 ^ w := by
  have e : 2 ^ m * y = 2 ^ k * (2 ^ w * (2 ^ (m - k - w) * y)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.add_mul_mod_self_left]
theorem div_add_pow (x y k m : Nat) (h : k ≤ m) :
    (x + 2 ^ m * y) / 2 ^ k = x / 2 ^ k + 2 ^ (m - k) * y := by
  have e : 2 ^ m * y = 2 ^ k * (2 ^ (m - k) * y) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
theorem dig_carry (b c j : Nat) (hb : b % 2 = 0) (hc : c ≤ 1) (hj : 0 < j) :
    (b + c) / 2 ^ (3 * j) % 8 = b / 2 ^ (3 * j) % 8 := by
  have e : (b + c) / 2 = b / 2 := by omega
  have p : 2 ^ (3 * j) = 2 * 2 ^ (3 * j - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  rw [p, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e]
theorem dig_carry0 (b c : Nat) (hb : b % 2 = 0) (hc : c ≤ 1) : (b + c) % 8 = b % 8 + c := by omega
theorem sum_range_add (f : Nat → Nat) (m n : Nat) :
    ((List.range (m + n)).map f).sum = ((List.range m).map f).sum + ((List.range n).map fun j => f (m + j)).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl
theorem sum_range_succ' (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f).sum = f 0 + ((List.range n).map fun j => f (j + 1)).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  rfl
theorem sum_congr_range (f g : Nat → Nat) (n : Nat) (h : ∀ i < n, f i = g i) :
    ((List.range n).map f).sum = ((List.range n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)
theorem dsum21_pow (a : Nat) : dsum21 a = ((List.range 21).map fun i => a / 2 ^ (3 * i) % 2 ^ 3).sum := by
  rw [dsum21_eq]
  apply sum_congr_range
  intro i _
  rw [Nat.pow_mul]; rfl
theorem lowDigits_sum (v0 v1 : Nat) (h0 : v0 < 2 ^ 64) :
    ((List.range 42).map fun i => (v0 + 2 ^ 64 * v1) / 2 ^ (3 * i) % 2 ^ 3).sum =
      dsum21 v0 + v0 / 2 ^ 63 + dsum21 (2 * v1) := by
  rw [show 42 = 21 + 21 from rfl, sum_range_add, dsum21_pow, dsum21_pow]
  have hlow : ∀ i < 21, (v0 + 2 ^ 64 * v1) / 2 ^ (3 * i) % 2 ^ 3 = v0 / 2 ^ (3 * i) % 2 ^ 3 :=
    fun i hi => div_mod_add_pow _ _ _ _ _ (by omega)
  rw [sum_congr_range _ _ 21 hlow]
  have hc : v0 / 2 ^ 63 ≤ 1 := by
    have : v0 / 2 ^ 63 < 2 := Nat.div_lt_of_lt_mul (by rw [show 2 ^ 63 * 2 = 2 ^ 64 by norm_num]; exact h0)
    omega
  have hW : ∀ j, (v0 + 2 ^ 64 * v1) / 2 ^ (3 * (21 + j)) % 2 ^ 3 = (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8 := by
    intro j
    rw [show 3 * (21 + j) = 63 + 3 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_add_pow _ _ _ _ (by omega)]
    norm_num
    rw [Nat.add_comm]
  simp only [hW]
  have e1 : ((List.range 21).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8).sum =
      v0 / 2 ^ 63 + ((List.range 21).map fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3).sum := by
    have s1 : ((List.range 21).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8).sum =
        (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * 0) % 8 +
          ((List.range 20).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * (j + 1)) % 8).sum :=
      sum_range_succ' (fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8) 20
    have s2 : ((List.range 21).map fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3).sum =
        2 * v1 / 2 ^ (3 * 0) % 2 ^ 3 + ((List.range 20).map fun j => 2 * v1 / 2 ^ (3 * (j + 1)) % 2 ^ 3).sum :=
      sum_range_succ' (fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3) 20
    have hj : ∀ j < 20, (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * (j + 1)) % 8 = 2 * v1 / 2 ^ (3 * (j + 1)) % 2 ^ 3 :=
      fun j _ => dig_carry _ _ _ (by omega) hc (by omega)
    rw [s1, s2, sum_congr_range _ _ 20 hj]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    rw [dig_carry0 _ _ (by omega) hc]
    norm_num
    omega
  rw [e1]
  omega
def lowSum (V : Nat) : Nat := lowSwar (V % 2 ^ 64) (2 * (V / 2 ^ 64))
theorem lowSum_lt (V : Nat) : lowSum V < 4095 := Nat.mod_lt _ (by norm_num)
theorem lowSum_eq (V : Nat) (h : V / 2 ^ 64 < 2 ^ 62) :
    lowSum V = ((List.range 42).map fun i => V / 2 ^ (3 * i) % 2 ^ 3).sum := by
  unfold lowSum
  rw [lowSwar_eq _ _ (Nat.mod_lt _ (by norm_num)) (by omega)]
  have hV : V = V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64) := (Nat.mod_add_div V (2 ^ 64)).symm
  have := lowDigits_sum (V % 2 ^ 64) (V / 2 ^ 64) (Nat.mod_lt _ (by norm_num))
  rw [← hV] at this
  exact this.symm
theorem target_le (lay : Layer) : target lay ≤ 202 := by
  fin_cases lay <;> decide
def lowSumS1 (v : Digest) : Nat := lowSwar (v.toNat % 2 ^ 63) (v.toNat / 2 ^ 64 % 2 ^ 63)
theorem lowSumS1_lt (v : Digest) : lowSumS1 v < 4095 := Nat.mod_lt _ (by norm_num)
theorem lowerWord_eq (v : Digest) :
    lowerWord v = v.toNat % 2 ^ 63 + 2 ^ 63 * (v.toNat / 2 ^ 64 % 2 ^ 63) := by
  unfold lowerWord; ring
theorem lowerWord_digits_sum (A B : Nat) (hA : A < 2 ^ 63) :
    ((List.range 42).map fun i => (A + 2 ^ 63 * B) / 2 ^ (3 * i) % 8).sum = dsum21 A + dsum21 B := by
  rw [show 42 = 21 + 21 from rfl, sum_range_add, dsum21_pow, dsum21_pow]
  have hlow : ∀ i < 21, (A + 2 ^ 63 * B) / 2 ^ (3 * i) % 8 = A / 2 ^ (3 * i) % 2 ^ 3 := by
    intro i hi
    have := div_mod_add_pow A B (3 * i) 63 3 (by omega)
    simpa using this
  rw [sum_congr_range _ _ 21 hlow]
  have hhi : ∀ j < 21, (A + 2 ^ 63 * B) / 2 ^ (3 * (21 + j)) % 8 = B / 2 ^ (3 * j) % 2 ^ 3 := by
    intro j _
    rw [show 3 * (21 + j) = 63 + 3 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_add_pow _ _ _ _ (le_refl _), Nat.div_eq_of_lt hA]
    simp
  rw [sum_congr_range _ _ 21 hhi]
theorem lowSumS1_eq (v : Digest) :
    lowSumS1 v = ((List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8).sum := by
  unfold lowSumS1
  have hA : v.toNat % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by norm_num)
  rw [lowSwar_eq _ _ (by omega) (Nat.mod_lt _ (by norm_num)), lowerWord_eq,
    lowerWord_digits_sum _ _ hA, Nat.div_eq_of_lt hA, Nat.add_zero]
theorem decode_lower_v6 (lay : Layer) (hlay : lay ≠ 0) (value : Digest) :
    decode lay value =
      if lowerSpare value then
        (if (target lay + 2 ^ 64 - lowSumS1 value) % 2 ^ 64 < 8 then
          some (((List.range 42).map fun i => lowerWord value / 2 ^ (3 * i) % 8) ++
            [(target lay + 2 ^ 64 - lowSumS1 value) % 2 ^ 64])
        else none)
      else none := by
  have ht := target_le lay
  have hS := lowSumS1_lt value
  rw [ClaudeWCT.WCT9.decode_lower_eq hlay value]
  by_cases hs : lowerSpare value
  · rw [if_pos hs, if_pos hs]
    unfold ClaudeWCT.WCT9.decodeV5Lower
    rw [if_neg (by have := lowerWord_lt value; omega)]
    dsimp only
    rw [← lowSumS1_eq]
    by_cases hc : lowSumS1 value ≤ target lay ∧ target lay - lowSumS1 value < 8
    · rw [if_pos hc, if_pos (by omega)]
      congr 3
      omega
    · rw [if_neg hc, if_neg (by omega)]
  · rw [if_neg hs, if_neg hs]
end SigGolfCandidate.T3M
end

namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
abbrev canonicalDecode := ClaudeWCT.WCT9.CanonicalPolicy.decode
def canonicalTarget (lay : Layer) : Nat := target (ClaudeWCT.WCT9.CanonicalPolicy.normalLayer lay)
theorem canonical_decode_lower_v6 (lay : Layer) (hlay : lay ≠ 0) (value : Digest) :
    canonicalDecode lay value =
      if lowerSpare value then
        (if (canonicalTarget lay + 2 ^ 64 - lowSumS1 value) % 2 ^ 64 < 8 then
          some (((List.range 42).map fun i => lowerWord value / 2 ^ (3 * i) % 8) ++
            [(canonicalTarget lay + 2 ^ 64 - lowSumS1 value) % 2 ^ 64])
        else none)
      else none := by
  simpa only [canonicalDecode, ClaudeWCT.WCT9.CanonicalPolicy.decode,
    canonicalTarget, ClaudeWCT.WCT9.CanonicalPolicy.normalLayer, if_neg hlay] using
    decode_lower_v6 (1 : Layer) (by decide) value
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_LayerSem ====
section

set_option Elab.async false

section
namespace SigGolfCandidate.T3M.Verify
theorem swar7_split (x m : BitVec 64) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x[i] <;> cases m[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]; cases x[i] <;> cases m[i] <;> rfl
theorem swar7_period : ∀ i : Fin 61,
    (0x71c71c71c71c71c7#64).getLsbD i.val = !(0x71c71c71c71c71c7#64).getLsbD (i.val + 3) := by
  decide +kernel
theorem swar7_shift (x : BitVec 64) :
    (x >>> 3) &&& 0x71c71c71c71c71c7#64 = (x &&& ~~~0x71c71c71c71c71c7#64) >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 61
  · have hp := swar7_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 3 + i = i + 3 by omega]
    simp [show i + 3 < 64 by omega]
  · have hx : x.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar7_low (x : BitVec 64) : (x &&& ~~~0x71c71c71c71c71c7#64).toNat % 8 = 0 := by
  have h7 : (x &&& ~~~0x71c71c71c71c71c7#64) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 3
    · have : (0x71c71c71c71c71c7#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +kernel
      simp [this]
    · have : (7#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 7 < 2 ^ 3 := by decide +kernel
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide +kernel) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar7_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 63) :
    ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64)) +
      (((a + b) - ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64))) >>> 3) =
    ((a >>> 3) &&& 0x71c71c71c71c71c7#64) + (a &&& 0x71c71c71c71c71c7#64) +
      ((b >>> 3) &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64) := by
  rw [swar7_shift a, swar7_shift b]
  set M : BitVec 64 := 0x71c71c71c71c71c7#64 with hM
  have la := swar7_low a
  have lb := swar7_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0x8e38e38e38e38e38 := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat ≤ 0x0e38e38e38e38e38 := by
    have hb' : b.toNat % 2 ^ 63 = b.toNat := Nat.mod_eq_of_lt hb
    have he := Nat.and_mod_two_pow (a := b.toNat) (b := (~~~M).toNat) (n := 63)
    rw [hb', Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hb)] at he
    rw [BitVec.toNat_and, he]
    simpa [hM] using (Nat.and_le_right : b.toNat &&& ((~~~M).toNat % 2 ^ 63) ≤ (~~~M).toNat % 2 ^ 63)
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 3 = ((a &&& ~~~M) >>> 3) + ((b &&& ~~~M) >>> 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
theorem swar2_period : ∀ i : Fin 62,
    (0x3333333333333333#64).getLsbD i.val = !(0x3333333333333333#64).getLsbD (i.val + 2) := by
  decide +kernel
theorem swar2_shift (x : BitVec 64) :
    (x >>> 2) &&& 0x3333333333333333#64 = (x &&& ~~~0x3333333333333333#64) >>> 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 62
  · have hp := swar2_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 2 + i = i + 2 by omega]
    simp [show i + 2 < 64 by omega]
  · have hx : x.getLsbD (2 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar2_low (x : BitVec 64) : (x &&& ~~~0x3333333333333333#64).toNat % 4 = 0 := by
  have h7 : (x &&& ~~~0x3333333333333333#64) &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 2
    · have : (0x3333333333333333#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide +kernel
      simp [this]
    · have : (3#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 3 < 2 ^ 2 := by decide +kernel
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide +kernel) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (3#64).toNat = 2 ^ 2 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar2_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 34) :
    ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64)) +
      (((a + b) - ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64))) >>> 2) =
    ((a >>> 2) &&& 0x3333333333333333#64) + (a &&& 0x3333333333333333#64) +
      ((b >>> 2) &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64) := by
  rw [swar2_shift a, swar2_shift b]
  set M : BitVec 64 := 0x3333333333333333#64 with hM
  have la := swar2_low a
  have lb := swar2_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0xcccccccccccccccc := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat < 2 ^ 34 := by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_left hb
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 2 = ((a &&& ~~~M) >>> 2) + ((b &&& ~~~M) >>> 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
end SigGolfCandidate.T3M.Verify
end
section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
open ClaudeWCT.WCT9 (LayerMsg)
def below (lay : Nat) : Nat := [19,12,6,0].getD lay 0
/-- Start of the witness leaf-buffer region still unread at layer `lay` (C3: the top region includes the top leaf's
pad and tweak high word). -/
def bufferStart (lay : Nat) : Nat := [21088,20368,19648,18928].getD lay 0
def layerEnd (lay : Nat) : Nat := [11144,13792,16360,18928].getD lay 0
def cpIdx (index lay : Nat) : Nat := if lay = 3 then 0 else index / 2 ^ below (lay + 1) % 2 ^ hL (lay + 1)
def MsgAt (w : ClaudeWCT.W9.T3M.WBytes) (index lay : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  match msg with
  | .forest _ => False
  | .pair left right => if lay = 3 then DigAt s WIT left ∧ DigAt s (WIT + 48) right ∧
      s.getMem (BitVec.ofNat 64 (WIT + 24)) = wword w 3 else
      lay < 3 ∧ DigAt s (rowA lay (cpIdx index lay)) left ∧
      DigAt s (rowA lay (cpIdx index lay) + 48) right ∧
      (∀ j, j = 3 ∨ j = 4 ∨ j = 5 →
        s.getMem (BitVec.ofNat 64 (rowA lay (cpIdx index lay) + 8 * j)) =
          wword w ((rowA lay (cpIdx index lay) - WIT) / 8 + j))
theorem MsgAt.pair_low {w : ClaudeWCT.W9.T3M.WBytes} {index lay : Nat} {left right : Digest} {s : MachineState}
    (h : MsgAt w index lay (.pair left right) s) (h3 : lay ≠ 3) :
    lay < 3 ∧ DigAt s (rowA lay (cpIdx index lay)) left ∧
      DigAt s (rowA lay (cpIdx index lay) + 48) right ∧
      (∀ j, j = 3 ∨ j = 4 ∨ j = 5 →
        s.getMem (BitVec.ofNat 64 (rowA lay (cpIdx index lay) + 8 * j)) =
          wword w ((rowA lay (cpIdx index lay) - WIT) / 8 + j)) := by
  simpa only [MsgAt, if_neg h3] using h
theorem MsgAt.pair_top {w : ClaudeWCT.W9.T3M.WBytes} {index : Nat} {left right : Digest} {s : MachineState}
    (h : MsgAt w index 3 (.pair left right) s) : DigAt s WIT left ∧ DigAt s (WIT + 48) right ∧
      s.getMem (BitVec.ofNat 64 (WIT + 24)) = wword w 3 := by
  simpa only [MsgAt, ↓reduceIte] using h
structure LayerIn (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index lay : Nat) (msg : LayerMsg)
    (s : MachineState) : Prop where
  lay4 : lay < 4
  idx : index < 2 ^ 31
  copy : s.pc = pcOf (T3M.setupPc lay (trPc lay (cpIdx index lay)))
  glob : Glob (preK lay) w pk s
  route : s.getReg (rReg lay) = BitVec.ofNat 64 (index / 2 ^ below lay)
  word : lay < 3 → s.getReg .x28 = T3.hyperWord lay (index / 2 ^ below lay)
  msg : MsgAt w index lay msg s
  orig : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay) s
  hdr3 : lay = 3 → s.getMem (BitVec.ofNat 64 (TOPLOAD + 32)) = BitVec.ofNat 64 (hyperBase 3) ∧
    s.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21328 ∧
    (∀ k, k < 5 → s.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) = BitVec.ofNat 64 (topWords.getD k 0))
  dst : lay < 3 → ∃ d, s.getReg .x12 = BitVec.ofNat 64 d ∧
    ((d + 16 = rowA lay (cpIdx index lay) ∧ WIT + layerEnd lay + 16 ≤ rowA lay (cpIdx index lay)) ∨
      d = rowA lay (cpIdx index lay) + 48)
  bufferOrig : Verify.Orig w (fun o => bufferStart lay ≤ o ∧ o < 21984) s
  /-- Layer 3: the nested FTS leaves `a2` at one of its two last heap outputs; the L3 encoding writes there. -/
  dst3 : lay = 3 → s.getReg .x12 = BitVec.ofNat 64 4112 ∨ s.getReg .x12 = BitVec.ofNat 64 4176
  /-- C4 (D7): the L3 encoding block reloads `s2` from this stack word (0xFFF). -/
  d0 : lay = 3 → s.getMem (BitVec.ofNat 64 (TOPB9 - 304)) = 0xFFF
structure EncPre (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index lay c : Nat)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc lay c + stepsA lay)
  glob : Glob (bK lay c) w pk t
  word : t.getReg .x28 = T3.hyperWord lay (index / 2 ^ below lay)
  s7 : ∀ L : Layer, L.val = lay → lay < 3 →
    t.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay (route index L).1)
  t5 : ∀ L : Layer, L.val = lay →
    (lay ≠ 0 → lay < 3 → t.getReg .x31 = BitVec.ofNat 64 (route index L).2) ∧
    (lay = 0 → t.getReg .x31 = BitVec.ofNat 64 (route index L).1)
  orig : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay) t
  hdr3 : lay = 3 → t.getMem (BitVec.ofNat 64 (TOPLOAD + 32)) = BitVec.ofNat 64 (hyperBase 3) ∧
    t.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21328 ∧
    (∀ k, k < 5 → t.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) = BitVec.ofNat 64 (topWords.getD k 0))
  index3 : lay = 3 → t.getReg .x22 = BitVec.ofNat 64 index
  /-- C2: the root window's left child is written 16 bytes low (its HIGH half lands on the window). -/
  dst : lay < 3 → ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧
    ((d + 16 = rowA lay c ∧ WIT + layerEnd lay + 16 ≤ rowA lay c) ∨ d = rowA lay c + 48)
  bufferOrig : Verify.Orig w (fun o => bufferStart lay ≤ o ∧ o < 21984) t
  dst3 : lay = 3 → t.getReg .x12 = BitVec.ofNat 64 4112 ∨ t.getReg .x12 = BitVec.ofNat 64 4176
def rejectSteps (lay : Nat) : Nat := stepsA lay + if lay = 3 then 21 else 3
def EncodingSetup : Prop :=
  ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ((ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow →
    ∃ u, Steps image s (rejectSteps lay.val) (rejectSteps lay.val) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
  ((ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < ClaudeWCT.WCT9.verifyWindow →
    ∃ t, Steps image s (stepsA lay.val) (stepsA lay.val) t ∧
      fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)
        (ClaudeWCT.W9.T3M.wbcHigh w index lay))) ∧
      EncPre w pk index lay.val (cpIdx index lay.val) t)
def layerLoop (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) : Nat → LayerMsg → T3.M (Option Digest)
  | 0, .forest root => pure (some root)
  | 0, .pair _ _ => pure none
  | n + 1, msg => ClaudeWCT.W9.T3M.layersCanonicalBC w index (n + 1) msg
end SigGolfCandidate.T3M.BC
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
def below (lay : Nat) : Nat := [19,12,6,0].getD lay 0
def layerEnd (lay : Nat) : Nat := [11144,13792,16360,18928].getD lay 0
theorem hL_eq (lay : Layer) : hL lay.val = height lay := by fin_cases lay <;> rfl
/-- Campaign T51 (endpad top leaf): `end_0` at 25216, the tweak at 25232, `end_i` at `25232 + 16 i` (`i >= 1`). -/
def slotT (i : Nat) : Nat := if i = 0 then 25216 else 25232 + 16 * i
theorem below_eq (lay : Layer) : below lay.val = (![19, 12, 6, 0] : Layer → Nat) lay := by fin_cases lay <;> rfl
theorem tgtL_eq (lay : Layer) : tgtL lay.val = canonicalTarget lay := by fin_cases lay <;> rfl

abbrev LayerIn := BC.LayerIn
theorem route_fst (index : Nat) (lay : Layer) : (route index lay).1 = index / 2 ^ below lay.val % 2 ^ hL lay.val := by
  simp only [route, below_eq, hL_eq]
theorem route_snd (index : Nat) (lay : Layer) : (route index lay).2 = index / 2 ^ (below lay.val + hL lay.val) := by
  simp only [route, below_eq, hL_eq]
theorem leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ hL lay.val := by
  rw [route_fst]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
theorem hL_le (lay : Layer) : 6 ≤ hL lay.val ∧ hL lay.val ≤ 12 := by fin_cases lay <;> decide +kernel
theorem tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  rw [route_snd]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
theorem tree_actual_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 < 2 ^ (31 - height lay) := by
  rw [route_snd]
  fin_cases lay <;> norm_num [below, hL, height] at * <;> omega
theorem routed_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  rw [route_snd, route_fst, ← hL_eq]
  fin_cases lay <;> norm_num [below, hL] at * <;> omega
theorem leaf_lt32 (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h1 := leaf_lt index lay
  have h2 := (hL_le lay).2
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega : hL lay.val ≤ 32))
theorem route_evals (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) (s : MachineState)
    (h : s.getReg (rReg lay.val) = BitVec.ofNat 64 (index / 2 ^ below lay.val)) :
    (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 ∧
      (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 ∧
      (tpE lay.val).eval s = BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1) ∧
      (s7E lay.val).eval s = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) := by
  have hl := leaf_lt index lay
  have ht := tree_lt index lay hidx
  have hl32 := leaf_lt32 index lay
  have hU : index / 2 ^ below lay.val < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hlE : (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 := by
    rw [route_fst]
    unfold leafE
    split
    · rename_i h0
      have hl0 : lay = 0 := Fin.ext h0
      subst hl0
      simp only [E.eval]
      rw [show rReg (0 : Layer).val = .x31 from rfl] at h
      rw [h]; congr 1
      simp only [show below (0 : Layer).val = 19 from rfl, show hL (0 : Layer).val = 12 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp only [E.eval, BinOp.eval, h, kw]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hU, Nat.mod_eq_of_lt (show 2 ^ hL lay.val - 1 < 2 ^ 64 by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide +kernel) (hL_le lay).2; omega),
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)))]
  have htE : (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 := by
    rw [route_snd]
    simp only [treeE, E.eval, BinOp.eval, h, kw]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hU,
      Nat.mod_eq_of_lt (show hL lay.val < 2 ^ 64 by have := (hL_le lay).2; omega),
      Nat.mod_eq_of_lt (show hL lay.val < 64 by have := (hL_le lay).2; omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  refine ⟨hlE, htE, ?_, ?_⟩
  · by_cases h0 : lay.val = 0
    ·
      have hz : (route index lay).2 = 0 := by
        have : lay = 0 := Fin.ext h0
        subst this
        rw [route_snd]; exact Nat.div_eq_of_lt (by simpa [below, hL] using hidx)
      simp only [tpE, if_pos h0, E.eval, BinOp.eval, hlE, kw]
      rw [hz, hdr1_eq _ _ (by norm_num) hl32]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
        show 32 % 64 = 32 from rfl, Nat.shiftLeft_eq]
      have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      ring
    simp only [tpE, if_neg h0, E.eval, BinOp.eval, hlE, htE, kw]
    rw [hdr1_eq _ _ ht hl32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
      show 32 % 64 = 32 from rfl, Nat.mod_eq_of_lt (show (route index lay).2 < 2 ^ 64 by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (route index lay).1 * 2 ^ 32 < 2 ^ 64 by
        have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
        omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (route index lay).2 + 2 ^ 32 * (route index lay).1 < 2 ^ 64 by omega)]
    rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ht]
    ring
  · by_cases h0 : lay.val = 0
    · have hl0 : (route index lay).1 < 4096 := by simpa [hL, h0] using hl
      simp only [s7E, dispatchHeap, if_pos h0, E.eval, BinOp.eval, hlE, kw]
      rw [h0]
      simp only [s7Bias, hL, List.getD_cons_zero]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show (4 : Nat) < 2 ^ 64 by decide),
        show 4 % 64 = 4 from rfl, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (show (route index lay).1 * 2 ^ 4 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 16 * 2 ^ 12 < 2 ^ 64 by decide),
        BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 16 * (4096 + (route index lay).1) < 2 ^ 64 by omega)]
      have h16 : (route index lay).1 * 2 ^ 4 < 2 ^ 16 := by omega
      rw [Nat.lor_comm, show (16 * 2 ^ 12 : Nat) = 2 ^ 16 * 1 by decide, ← Nat.two_pow_add_eq_or_of_lt h16]
      omega
    · simp only [s7E, if_neg h0, E.eval, BinOp.eval, hlE, kw, dispatchHeap]
      change BitVec.ofNat 64 (route index lay).1 + BitVec.ofNat 64 (s7Bias lay.val) =
        BitVec.ofNat 64 (s7Bias lay.val + (route index lay).1)
      rw [ofNat_add_ofNat]
      simp [Nat.add_comm]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 lowerSpare lowerWord)
theorem ctrE_eval (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (s : MachineState) (hH : WitHdr w s) :
    (ctrE 3).eval s = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wbcCtr w index 3).toNat := by
  have hw := hH 4 (by decide +kernel) (by decide +kernel)
  rw [show WIT + 8 * 4 = 0x1030 + 8 * ((3 + 1) / 2) by unfold WIT; rfl] at hw
  show LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 (0x1030 + 8 * ((3 + 1) / 2)))) (4 * ((3 + 1) % 2)) = _
  rw [hw]
  exact BC.counterWord w 4
theorem ctr_lt (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) :
    (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < 2 ^ 32 :=
  (ClaudeWCT.W9.T3M.wbcCtr w index lay).isLt
theorem copy_parts (lay c : Nat) (h : BC.copyCheck lay c = true) :
    specB (BC.allowed lay c) [] (BC.setupGk lay) (runAt (BC.preK lay) [] (T3M.setupPc lay (trPc lay c))
      []) (BC.specA lay c) [] (BC.bKS lay c) (BC.keepA lay) = true ∧
    (lay ≠ 0 →
      specB [] [] baseK (runAt (BC.bKB lay c) [] (trPc lay c + stepsA lay + 1)
        [.br (decide (lay = 3)), .br false, .jmp])
        (specBl lay (trPc lay c)) BC.oblB (postBlC lay (trPc lay c)) (keepB lay) = true ∧
      specB [] [] [] (runAt (BC.bKB lay c) [] (trPc lay c + stepsA lay + 1)
        [.br (decide (lay = 3)), .br true]) (rejCk lay) BC.oblB [] [] = true) := by
  unfold BC.copyCheck BC.setupCheck at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, fun h0 => ?_⟩
  rw [if_neg h0] at h
  simp only [Bool.and_eq_true] at h
  tauto
theorem copy_parts_hi (lay c : Nat) (h : BC.copyCheck lay c = true) (h0 : lay ≠ 0) :
    specB [] [] baseK (runAt (BC.bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br (decide (lay ≠ 3)), .br true, .br false, .jmp]) (specBlHi lay (trPc lay c)) BC.oblBHi
      (postBlC lay (trPc lay c)) (keepB lay) = true ∧
    specB [] [] [] (runAt (BC.bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br (decide (lay ≠ 3)), .br true, .br true]) (rejCkHi lay) BC.oblBHi [] [] = true := by
  unfold BC.copyCheck at h
  rw [if_neg h0] at h
  simp only [Bool.and_eq_true] at h
  tauto
abbrev EncPre := BC.EncPre
theorem hw4_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 4 lay.val = hdr0 4 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring
theorem toNat_srl (x : Word) (k : Nat) (hk : k < 64) : (x >>> ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]
theorem toNat_sll (x : Word) (k : Nat) (hk : k < 64) :
    (x <<< ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftLeft_eq]
theorem toNat_andc (x : Word) (k : Nat) (hk : k < 2 ^ 64) : (x &&& BitVec.ofNat 64 k).toNat = x.toNat &&& k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
theorem toNat_remuc (x : Word) (k : Nat) (hk : 0 < k) (hk' : k < 2 ^ 64) :
    (rv64_remu x (BitVec.ofNat 64 k)).toNat = x.toNat % k := by
  unfold rv64_remu
  have hne : (BitVec.ofNat 64 k == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk'] at this
    simp at this; omega
  rw [hne]
  simp only [Bool.false_eq_true, if_false, BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']
structure AnsAt (u : MachineState) (a : BitVec 256) : Prop where
  lo : a6E.eval u = a.extractLsb' 0 64
  hi : a7E.eval u = a.extractLsb' 64 64
abbrev ansV (a : BitVec 256) : Nat := (a.extractLsb' 0 128).toNat
theorem ansV_split (a : BitVec 256) :
    ansV a = (a.extractLsb' 0 64).toNat + 2 ^ 64 * (a.extractLsb' 64 64).toNat := by
  simp only [ansV, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  generalize a.toNat = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
theorem ansV_lo (a : BitVec 256) : ansV a % 2 ^ 64 = (a.extractLsb' 0 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega
theorem ansV_hi (a : BitVec 256) : ansV a / 2 ^ 64 = (a.extractLsb' 64 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega
theorem a6E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a6E.eval u = a.extractLsb' 0 64 := h.lo
theorem a7E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a7E.eval u = a.extractLsb' 64 64 := h.hi
theorem toNat_clr63 (x : BitVec 64) : (BitVec.ofNat 64 (x.toNat % 2 ^ 63)).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_ofNat]; omega
theorem clr63_M1 (x : BitVec 64) :
    x &&& 0x71c71c71c71c71c7#64 = BitVec.ofNat 64 (x.toNat % 2 ^ 63) &&& 0x71c71c71c71c71c7#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and, toNat_clr63]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_land, Nat.testBit_mod_two_pow]
  by_cases hi : i < 63
  · simp [hi]
  · have : Nat.testBit 8198552921648689607 i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (show 8198552921648689607 < 2 ^ 63 by decide +kernel)
        (Nat.pow_le_pow_right (by decide +kernel) (by omega)))
    simp [this]
theorem add_clr63 (x y : BitVec 64) (hx : 2 ^ 63 ≤ x.toNat) (hy : 2 ^ 63 ≤ y.toNat) :
    x + y = BitVec.ofNat 64 (x.toNat % 2 ^ 63) + BitVec.ofNat 64 (y.toNat % 2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega
theorem sw1_bv (x y : BitVec 64) :
    (((x >>> 3) &&& 0x71c71c71c71c71c7#64) + (x &&& 0x71c71c71c71c71c7#64) +
      ((y >>> 3) &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64)).toNat = sw1 x.toNat y.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold sw1 mask3
  rfl
theorem swS1 (x y : BitVec 64) (hx : 2 ^ 63 ≤ x.toNat) (hy : 2 ^ 63 ≤ y.toNat) :
    (((x &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64)) +
      (((x + y) - ((x &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64))) >>> 3)).toNat =
    sw1 (x.toNat % 2 ^ 63) (y.toNat % 2 ^ 63) := by
  rw [clr63_M1 x, clr63_M1 y, add_clr63 x y hx hy,
    Verify.swar7_eq _ _ (by rw [toNat_clr63]; omega), sw1_bv, toNat_clr63, toNat_clr63]
abbrev ansD (a : BitVec 256) : Digest := a.extractLsb' 0 128
theorem ansD_lo (a : BitVec 256) : (ansD a).toNat % 2 ^ 64 = (a.extractLsb' 0 64).toNat := ansV_lo a
theorem ansD_hi (a : BitVec 256) : (ansD a).toNat / 2 ^ 64 = (a.extractLsb' 64 64).toNat := ansV_hi a
theorem spare_iff (a : BitVec 256) :
    lowerSpare (ansD a) ↔ 2 ^ 63 ≤ (a.extractLsb' 0 64).toNat ∧ 2 ^ 63 ≤ (a.extractLsb' 64 64).toNat := by
  have hlo := ansD_lo a
  have hhi := ansD_hi a
  have hlt := (ansD a).isLt
  have h0 := (a.extractLsb' 0 64).isLt
  have h1 := (a.extractLsb' 64 64).isLt
  unfold lowerSpare
  constructor
  · rintro ⟨e0, e1⟩; constructor <;> omega
  · rintro ⟨e0, e1⟩; constructor <;> omega
theorem sumE_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hs : lowerSpare (ansD a))
    (lay : Nat) (hm1 : (M1E lay).eval u = BitVec.ofNat 64 M1c)
    (hm2 : (M2E lay).eval u = BitVec.ofNat 64 M2c) :
    ((sumE lay).eval u).toNat = lowSumS1 (ansD a) := by
  obtain ⟨h6, h7⟩ := (spare_iff a).mp hs
  have he : (BitVec.ofNat 64 3).toNat % 64 = 3 := by decide +kernel
  have hs1 : ((sw1E lay).eval u).toNat = sw1 ((a.extractLsb' 0 64).toNat % 2 ^ 63) ((a.extractLsb' 64 64).toNat % 2 ^ 63) := by
    simp only [sw1E, swLowE, E.eval, BinOp.eval, kw, hm1, M1c, he, a6E_eval h, a7E_eval h]
    exact swS1 _ _ h6 h7
  have hlo : (a.extractLsb' 0 64).toNat % 2 ^ 63 = (ansD a).toNat % 2 ^ 63 := by
    rw [← ansD_lo]; omega
  have hhi : (a.extractLsb' 64 64).toNat % 2 ^ 63 = (ansD a).toNat / 2 ^ 64 % 2 ^ 63 := by
    rw [← ansD_hi]
  unfold lowSumS1 lowSwar
  simp only [sumE, E.eval, BinOp.eval, kw, hm2]
  rw [toNat_remuc _ _ (by norm_num) (by norm_num), toNat_andc _ _ (by norm_num [M2c]), BitVec.toNat_add,
    toNat_srl _ 6 (by norm_num), hs1, hlo, hhi]
  rfl
theorem spareBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (lay : Nat) (d : Bool) :
    Br.holds u (spareBr lay d) ↔ d = decide (¬ lowerSpare (ansD a)) := by
  have hb : Br.holds u (spareBr lay d) ↔
      (!((a.extractLsb' 0 64).msb && (a.extractLsb' 64 64).msb)) = d := by
    by_cases h3 : lay = 3
    · simp only [spareBr, if_pos h3, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a6E_eval h, a7E_eval h, kw]
      rw [show (BitVec.ofNat 64 0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_and]
      cases (a.extractLsb' 0 64).msb <;> cases (a.extractLsb' 64 64).msb <;> cases d <;> decide
    · simp only [spareBr, if_neg h3, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a6E_eval h, a7E_eval h, kw]
      rw [show (BitVec.ofNat 64 0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_and]
  have e := spare_iff a
  have hd : decide (¬ lowerSpare (ansD a)) = !((a.extractLsb' 0 64).msb && (a.extractLsb' 64 64).msb) := by
    rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, decide_not, ← Bool.decide_and, decide_eq_decide.mpr e]
  rw [hb, hd]
  exact eq_comm
def ckOf (lay : Layer) (a : BitVec 256) : Nat := (tgtL lay.val + 2 ^ 64 - lowSumS1 (ansD a)) % 2 ^ 64
theorem ckBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hs : lowerSpare (ansD a)) (lay : Layer)
    (hm1 : (M1E lay.val).eval u = BitVec.ofNat 64 M1c)
    (hm2 : (M2E lay.val).eval u = BitVec.ofNat 64 M2c)
    (d : Bool) :
    Br.holds u (ckBr lay.val d) ↔ d = decide (¬ ckOf lay a < 8) := by
  have hS := lowSumS1_lt (ansD a)
  have hT : tgtL lay.val ≤ 202 := by fin_cases lay <;> decide +kernel
  have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide +kernel
  have ht4 : ((t4E lay.val).eval u).toNat = (lowSumS1 (ansD a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 := by
    simp only [t4E, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, sumE_eval h hs lay.val hm1 hm2, BitVec.toNat_ofNat]
    omega
  have hiff : (lowSumS1 (ansD a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 ↔ ckOf lay a < 8 := by
    unfold ckOf; omega
  have key : BitVec.ult (BitVec.ofNat 64 7) ((t4E lay.val).eval u) = decide (¬ ckOf lay a < 8) := by
    simp only [BitVec.ult, ht4, BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 7 by norm_num, decide_eq_decide]
    constructor
    · intro h1 h2
      have := hiff.mpr h2
      omega
    · intro h1
      by_contra h2
      exact h1 (hiff.mp (by omega))
  simp only [ckBr, Br.holds, CmpOp.eval]
  show BitVec.ult ((kw 7).eval u) ((t4E lay.val).eval u) = d ↔ _
  rw [show (kw 7).eval u = BitVec.ofNat 64 7 from rfl, key]; exact eq_comm
def highView (a : BitVec 256) : BitVec 256 := a >>> 128
theorem highView_extract (a : BitVec 256) (start len : Nat) :
    (highView a).extractLsb' start len = a.extractLsb' (start+128) len := by
  apply BitVec.eq_of_toNat_eq
  simp only [highView, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm]
structure AnsAtHi (u : MachineState) (a : BitVec 256) : Prop where
  lo : a6HiE.eval u = a.extractLsb' 0 64
  hi : a7HiE.eval u = a.extractLsb' 64 64
theorem a6HiE_eval {u : MachineState} {a : BitVec 256} (h : AnsAtHi u a) : a6HiE.eval u = a.extractLsb' 0 64 := h.lo
theorem a7HiE_eval {u : MachineState} {a : BitVec 256} (h : AnsAtHi u a) : a7HiE.eval u = a.extractLsb' 64 64 := h.hi
theorem sumHiE_eval {u : MachineState} {a : BitVec 256} (h : AnsAtHi u a) (hs : lowerSpare (ansD a))
    (lay : Nat) (hm1 : (M1E lay).eval u = BitVec.ofNat 64 M1c)
    (hm2 : (M2E lay).eval u = BitVec.ofNat 64 M2c) :
    ((sumHiE lay).eval u).toNat = lowSumS1 (ansD a) := by
  obtain ⟨h6, h7⟩ := (spare_iff a).mp hs
  have he : (BitVec.ofNat 64 3).toNat % 64 = 3 := by decide +kernel
  have hs1 : ((sw1HiE lay).eval u).toNat = sw1 ((a.extractLsb' 0 64).toNat % 2 ^ 63) ((a.extractLsb' 64 64).toNat % 2 ^ 63) := by
    simp only [sw1HiE, swLowHiE, E.eval, BinOp.eval, kw, hm1, M1c, he, a6HiE_eval h, a7HiE_eval h]
    exact swS1 _ _ h6 h7
  have hlo : (a.extractLsb' 0 64).toNat % 2 ^ 63 = (ansD a).toNat % 2 ^ 63 := by
    rw [← ansD_lo]; omega
  have hhi : (a.extractLsb' 64 64).toNat % 2 ^ 63 = (ansD a).toNat / 2 ^ 64 % 2 ^ 63 := by
    rw [← ansD_hi]
  unfold lowSumS1 lowSwar
  simp only [sumHiE, E.eval, BinOp.eval, kw, hm2]
  rw [toNat_remuc _ _ (by norm_num) (by norm_num), toNat_andc _ _ (by norm_num [M2c]), BitVec.toNat_add,
    toNat_srl _ 6 (by norm_num), hs1, hlo, hhi]
  rfl
theorem spareHiBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAtHi u a) (lay : Nat) (d : Bool) :
    Br.holds u (spareHiBr lay d) ↔ d = decide (¬ lowerSpare (ansD a)) := by
  have hb : Br.holds u (spareHiBr lay d) ↔
      (!((a.extractLsb' 0 64).msb && (a.extractLsb' 64 64).msb)) = d := by
    simp only [spareHiBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a6HiE_eval h, a7HiE_eval h, kw]
    rw [show (BitVec.ofNat 64 0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_and]
    cases (a.extractLsb' 0 64).msb <;> cases (a.extractLsb' 64 64).msb <;> cases d <;> decide
  have e := spare_iff a
  have hd : decide (¬ lowerSpare (ansD a)) = !((a.extractLsb' 0 64).msb && (a.extractLsb' 64 64).msb) := by
    rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, decide_not, ← Bool.decide_and, decide_eq_decide.mpr e]
  rw [hb, hd]
  exact eq_comm
theorem ckHiBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAtHi u a) (hs : lowerSpare (ansD a)) (lay : Layer)
    (hm1 : (M1E lay.val).eval u = BitVec.ofNat 64 M1c)
    (hm2 : (M2E lay.val).eval u = BitVec.ofNat 64 M2c)
    (d : Bool) :
    Br.holds u (ckHiBr lay.val d) ↔ d = decide (¬ ckOf lay a < 8) := by
  have hS := lowSumS1_lt (ansD a)
  have hT : tgtL lay.val ≤ 202 := by fin_cases lay <;> decide +kernel
  have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide +kernel
  have ht4 : ((t4HiE lay.val).eval u).toNat = (lowSumS1 (ansD a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 := by
    simp only [t4HiE, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, sumHiE_eval h hs lay.val hm1 hm2, BitVec.toNat_ofNat]
    omega
  have hiff : (lowSumS1 (ansD a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 ↔ ckOf lay a < 8 := by
    unfold ckOf; omega
  have key : BitVec.ult (BitVec.ofNat 64 7) ((t4HiE lay.val).eval u) = decide (¬ ckOf lay a < 8) := by
    simp only [BitVec.ult, ht4, BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 7 by norm_num, decide_eq_decide]
    constructor
    · intro h1 h2
      have := hiff.mpr h2
      omega
    · intro h1
      by_contra h2
      exact h1 (hiff.mp (by omega))
  simp only [ckHiBr, Br.holds, CmpOp.eval]
  show BitVec.ult ((kw 7).eval u) ((t4HiE lay.val).eval u) = d ↔ _
  rw [show (kw 7).eval u = BitVec.ofNat 64 7 from rfl, key]; exact eq_comm
def lctxOf (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) : LCtx :=
  ⟨w, lay, 0, 0, (route index lay).2, (route index lay).1, s6v lay.val, a.extractLsb' 0 64, a.extractLsb' 64 64,
    ckOf lay a, ckSlot (ckOf lay a) + partLen (ckOf lay a), by fin_cases lay <;> decide +kernel⟩
def lfS7 (lay leaf : Nat) : Nat := dispatchHeap lay leaf * 2 ^ s7Sh lay
theorem mod_pow_div_mod (v m k w : Nat) (h : k + w ≤ m) : v % 2 ^ m / 2 ^ k % 2 ^ w = v / 2 ^ k % 2 ^ w := by
  conv_rhs => rw [← Nat.mod_add_div v (2 ^ m)]
  rw [div_mod_add_pow _ _ _ _ _ h]
theorem getD_map_range (f : Nat → Nat) (n i : Nat) (h : i < n) : ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl
theorem lctx_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (hlay : lay ≠ 0)
    (ds : List Nat) (hds : canonicalDecode lay (ansD a) = some ds) :
    ∀ i < 43, (lctxOf w index lay a).dig i = ds.getD i 0 := by
  rw [canonical_decode_lower_v6 lay hlay] at hds
  split at hds
  · split at hds
    · simp only [Option.some.injEq] at hds
      subst hds
      intro i hi
      unfold LCtx.dig lctxOf
      simp only []
      have hlw := lowerWord_eq (ansD a)
      by_cases h21 : i < 21
      · rw [if_pos h21, List.getD_append _ _ _ _ (by simp; omega), getD_map_range _ 42 i (by omega)]
        have e8 : (8 : Nat) ^ i = 2 ^ (3 * i) := by rw [Nat.pow_mul]
        rw [← ansD_lo, e8, hlw]
        have h1 := mod_pow_div_mod (ansD a).toNat 64 (3 * i) 3 (by omega)
        have h2 := mod_pow_div_mod (ansD a).toNat 63 (3 * i) 3 (by omega)
        have h3 := div_mod_add_pow ((ansD a).toNat % 2 ^ 63) ((ansD a).toNat / 2 ^ 64 % 2 ^ 63) (3 * i) 63 3
          (by omega)
        rw [show (2 : Nat) ^ 3 = 8 from rfl] at h1 h2 h3
        rw [h1, h3, h2]
      · by_cases h42 : i < 42
        · rw [if_neg h21, if_pos h42, List.getD_append _ _ _ _ (by simp; omega), getD_map_range _ 42 i (by omega)]
          have e8 : (8 : Nat) ^ (i - 21) = 2 ^ (3 * (i - 21)) := by rw [Nat.pow_mul]
          rw [← ansD_hi, e8, hlw, show 3 * i = 63 + 3 * (i - 21) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
            div_add_pow _ _ _ _ (le_refl _), Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)), Nat.sub_self,
            Nat.pow_zero, Nat.one_mul, Nat.zero_add]
          have h2 := mod_pow_div_mod ((ansD a).toNat / 2 ^ 64) 63 (3 * (i - 21)) 3 (by omega)
          rw [show (2 : Nat) ^ 3 = 8 from rfl] at h2
          exact h2.symm
        · have hi42 : i = 42 := by omega
          subst hi42
          rw [if_neg h21, if_neg h42, List.getD_append_right _ _ _ _ (by simp)]
          rw [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
          show ckOf lay a = _
          unfold ckOf
          rw [tgtL_eq]
    · cases hds
  · cases hds
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 lowerSpare lowerWord)
theorem xtrTab_bound : (xtrTab.all fun r => r.all fun x => decide (x < 160000)) = true := by decide +kernel
theorem getD_lt_of_all : ∀ (l : List Nat) (B c : Nat), 0 < B → (l.all fun x => decide (x < B)) = true →
    l.getD c 0 < B
  | [], B, c, hB, _ => by simpa using hB
  | x :: l, B, 0, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | x :: l, B, c + 1, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all l B c hB h.2
theorem getD_getD_lt : ∀ (L : List (List Nat)) (i j B : Nat), 0 < B →
    (L.all fun r => r.all fun x => decide (x < B)) = true → (L.getD i []).getD j 0 < B
  | [], i, j, B, hB, _ => by simpa using hB
  | r :: L, 0, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all r B j hB h.1
  | r :: L, i + 1, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_getD_lt L i j B hB h.2
theorem trPc_lt (lay c : Nat) : trPc lay c < 160000 :=
  getD_getD_lt xtrTab lay c 160000 (by norm_num) xtrTab_bound
theorem origW_of {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P : Nat → Prop} (hO : Verify.Orig w P s) (A : Nat)
    (hA : WIT ≤ A) (h8 : (A - WIT) % 8 = 0) (hx : A - WIT < WX) (hP : P (A - WIT)) : OrigW w s A := by
  have := hO.word (A - WIT) h8 hx hP
  rw [show WIT + (A - WIT) = A by omega] at this
  unfold OrigW
  rw [this, wword, show 64 * ((A - WIT) / 8) = 8 * (A - WIT) by omega]
theorem knownOK_cons (p : Reg × Word) (ps : List (Reg × Word)) (s : MachineState)
    (hp : s.getReg p.1 = p.2) (hps : KnownOK ps s) : KnownOK (p :: ps) s := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact hps q hq
theorem knownOK_at (ps : List (Reg × Word)) (s : MachineState) (i : Nat) (p : Reg × Word)
    (hk : KnownOK ps s) (he : ps[i]? = some p) : s.getReg p.1 = p.2 :=
  hk p (List.mem_of_getElem? he)
theorem ofNat64_add_zero_bridge (v : Word) (n : Nat) (h : v = BitVec.ofNat 64 n) :
    v = BitVec.ofNat 64 (n + 0) := by simpa only [Nat.add_zero] using h
theorem ofNat64_add_zero_bridge385 (v : Word) (n : Nat) (h : v = BitVec.ofNat 64 (n + 385)) :
    v = BitVec.ofNat 64 (n + 0 + 385) := by simpa only [Nat.add_zero] using h
theorem knownOK_sixteen (s : MachineState)
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : Reg × Word}
    (h0 : s.getReg p0.1 = p0.2) (h1 : s.getReg p1.1 = p1.2)
    (h2 : s.getReg p2.1 = p2.2) (h3 : s.getReg p3.1 = p3.2)
    (h4 : s.getReg p4.1 = p4.2) (h5 : s.getReg p5.1 = p5.2)
    (h6 : s.getReg p6.1 = p6.2) (h7 : s.getReg p7.1 = p7.2)
    (h8 : s.getReg p8.1 = p8.2) (h9 : s.getReg p9.1 = p9.2)
    (h10 : s.getReg p10.1 = p10.2) (h11 : s.getReg p11.1 = p11.2)
    (h12 : s.getReg p12.1 = p12.2) (h13 : s.getReg p13.1 = p13.2)
    (h14 : s.getReg p14.1 = p14.2) (h15 : s.getReg p15.1 = p15.2) :
    KnownOK [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] s := by
  iterate 16
    refine knownOK_cons _ _ _ ?_ ?_
    rotate_left
  · intro q hq; cases hq
  all_goals assumption
theorem knownOK_seventeen (s : MachineState)
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 : Reg × Word}
    (h0 : s.getReg p0.1 = p0.2) (h1 : s.getReg p1.1 = p1.2)
    (h2 : s.getReg p2.1 = p2.2) (h3 : s.getReg p3.1 = p3.2)
    (h4 : s.getReg p4.1 = p4.2) (h5 : s.getReg p5.1 = p5.2)
    (h6 : s.getReg p6.1 = p6.2) (h7 : s.getReg p7.1 = p7.2)
    (h8 : s.getReg p8.1 = p8.2) (h9 : s.getReg p9.1 = p9.2)
    (h10 : s.getReg p10.1 = p10.2) (h11 : s.getReg p11.1 = p11.2)
    (h12 : s.getReg p12.1 = p12.2) (h13 : s.getReg p13.1 = p13.2)
    (h14 : s.getReg p14.1 = p14.2) (h15 : s.getReg p15.1 = p15.2) (h16 : s.getReg p16.1 = p16.2) :
    KnownOK [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16] s := by
  iterate 17
    refine knownOK_cons _ _ _ ?_ ?_
    rotate_left
  · intro q hq; cases hq
  all_goals assumption
theorem hyperWord_packed (lay : Layer) (tree leaf : Nat) :
    T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) = BitVec.ofNat 64 (packedPrefix lay tree leaf + 385) := by
  unfold T3.hyperWord packedPrefix packedHi
  have := lay.isLt
  rw [Nat.mod_eq_of_lt (show lay.val < 256 by omega)]
  apply congrArg (BitVec.ofNat 64)
  omega
theorem routed_eq (index : Nat) (lay : Layer) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 = index / 2 ^ below lay.val := by
  rw [route_fst, route_snd, ← hL_eq, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  simpa only [Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div (index / 2 ^ below lay.val) (2 ^ hL lay.val))
theorem hyperWord_route (index : Nat) (lay : Layer) :
    T3.hyperWord lay.val (index / 2 ^ below lay.val) =
      BitVec.ofNat 64 (packedPrefix lay (route index lay).2 (route index lay).1 + 385) := by
  rw [← routed_eq, hyperWord_packed]
theorem hyperWord_x28v (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) :
    T3.hyperWord lay.val (index / 2 ^ below lay.val) = BitVec.ofNat 64 (lctxOf w index lay a).x28v := by
  have e : (lctxOf w index lay a).x28v = packedPrefix lay (route index lay).2 (route index lay).1 + 385 :=
    LCtx.x28v_eq _ rfl
  rw [e]
  exact hyperWord_route index lay
set_option maxRecDepth 10000 in
theorem lctxOf_known (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (p : Nat)
    (s : MachineState) (hk : KnownOK (postBl lay.val p) s)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (lctxOf w index lay a).x28v)
    (h16 : s.getReg .x16 = a.extractLsb' 0 64)
    (h17 : s.getReg .x17 = a.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 (ckOf lay a)) :
    KnownOK (lctxOf w index lay a).known s := by
  unfold LCtx.known
  refine knownOK_seventeen s ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact knownOK_at _ s 0 (.x5, 0) hk rfl
  · exact knownOK_at _ s 6 (.x11, 64) hk rfl
  · exact knownOK_at _ s 7 (.x7, 1) hk rfl
  · exact knownOK_at _ s 8 (.x13, 2) hk rfl
  · exact knownOK_at _ s 9 (.x19, 3) hk rfl
  · exact knownOK_at _ s 10 (.x20, 4) hk rfl
  · exact knownOK_at _ s 11 (.x21, 5) hk rfl
  · exact knownOK_at _ s 12 (.x26, 6) hk rfl
  · exact h28
  · exact knownOK_at _ s 3 (.x9, 0x7fc00) hk rfl
  · exact knownOK_at _ s 15 (.x27, 0x3fe00) hk rfl
  · exact knownOK_at _ s 14 (.x5, 0) hk rfl
  · exact knownOK_at _ s 17 (.x22, BitVec.ofNat 64 (s6v lay.val)) hk rfl
  · exact h16
  · exact h17
  · exact h29
  · have e : (lctxOf w index lay a).bufferOffset = bufferBias lay.val := by
      fin_cases lay
      · exact absurd rfl hlay
      all_goals rfl
    rw [e]
    exact knownOK_at _ s 16 (.x4, BitVec.ofNat 64 (bufferBias lay.val)) hk rfl
theorem rowA_facts : ∀ lay c, lay < 3 → c < nCopy lay →
    rowA lay c % 8 = 0 ∧ WLO ≤ rowA lay c ∧ rowA lay c + 96 ≤ 2 ^ 23 ∧ WIT + BC.layerEnd lay ≤ rowA lay c := by
  have h : ([0, 1, 2].all fun lay => (List.range (nCopy lay)).all fun c =>
      decide (rowA lay c % 8 = 0 ∧ WLO ≤ rowA lay c ∧ rowA lay c + 96 ≤ 2 ^ 23 ∧
        WIT + BC.layerEnd lay ≤ rowA lay c)) = true := by decide +kernel
  intro lay c hl hc
  have h1 := List.all_eq_true.mp h lay (by simp; omega)
  exact of_decide_eq_true (List.all_eq_true.mp h1 c (List.mem_range.mpr hc))
theorem cpIdx_lt (index : Nat) (lay : Nat) (hl : lay < 4) : BC.cpIdx index lay < nCopy lay := by
  have hn := BC.nCopy_eq
  unfold BC.cpIdx
  interval_cases lay <;> simp only [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2] <;> norm_num [hL] <;> exact Nat.mod_lt _ (by norm_num)
theorem oblB_holds (u : MachineState) (d : Nat) (hd : u.getReg .x12 = BitVec.ofNat 64 d) (h8 : d % 8 = 0)
    (hlt : d + 16 ≤ 2 ^ 23) : ∀ o ∈ BC.oblB, o.holds u := by
  intro o ho
  simp only [BC.oblB, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;>
    simp only [Oblig.holds, Addr.eval, E.eval, hd, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq,
      MEMORY_BYTES, BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl,
      show (0 : Word).toNat = 0 from rfl] <;> omega
theorem encB_step_low (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t)
    (a : BitVec 256) (hsp : lowerSpare (ansD a)) :
    (canonicalDecode lay (ansD a) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1 ∧ k ≤ 27 ∧ cy ≤ 30) ∧
    (canonicalDecode lay (ansD a) ≠ none → ∃ s0, Steps image (writeHash t a) (bSt lay.val) (bCy lay.val) s0 ∧
        (lctxOf w index lay a).ok ∧
        (∀ p ∈ (lctxOf w index lay a).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay a).Orig0 s0 ∧
        (lctxOf w index lay a).ChainIn s0 0 [] s0 ∧ Glob (chainK lay.val) w pk s0 ∧
        Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (lfS7 lay.val (route index lay).1) ∧
        s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2 ∧
        s0.getReg .x2 = BitVec.ofNat 64 0xffbde0 ∧
        Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) s0) := by
  set u := writeHash t a with hu
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hcc := copy_parts lay.val c (BC.copyCheck_at lay.val c lay.isLt hc)
  have hB := hcc.2 h0
  have hkt : KnownOK (BC.bK lay.val c) t := ht.glob.1
  obtain ⟨d, h12, hdc⟩ : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧
      (if lay.val = 3 then (d = 4112 ∨ d = 4176) else
        ((d + 16 = rowA lay.val c ∧ WIT + BC.layerEnd lay.val + 16 ≤ rowA lay.val c) ∨ d = rowA lay.val c + 48)) := by
    by_cases h3 : lay.val = 3
    · rcases ht.dst3 h3 with hd | hd
      · exact ⟨4112, hd, by rw [if_pos h3]; exact Or.inl rfl⟩
      · exact ⟨4176, hd, by rw [if_pos h3]; exact Or.inr rfl⟩
    · obtain ⟨d, hd, hdd⟩ := ht.dst (by have := lay.isLt; omega)
      exact ⟨d, hd, by rw [if_neg h3]; exact hdd⟩
  have hdf : d % 8 = 0 ∧ d + 32 ≤ 2 ^ 23 ∧ safeDest d = true ∧ (lay.val ≠ 3 → WIT + layerEnd lay.val ≤ d) := by
    by_cases h3 : lay.val = 3
    · rw [if_pos h3] at hdc
      rcases hdc with rfl | rfl <;>
        exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun h => absurd h3 h⟩
    · rw [if_neg h3] at hdc
      obtain ⟨r16, rlo, rhi, rend⟩ := rowA_facts lay.val c (by have := lay.isLt; omega) hc
      have hd8 : d % 8 = 0 := by rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
      have hd32 : d + 32 ≤ 2 ^ 23 := by rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
      have hlo : WLO ≤ d := by
        have hle : 48 ≤ BC.layerEnd lay.val := by
          have := lay.isLt; unfold BC.layerEnd
          rcases (show lay.val = 0 ∨ lay.val = 1 ∨ lay.val = 2 ∨ lay.val = 3 by omega) with h | h | h | h <;> simp [h]
        rcases hdc with ⟨hd1, hd2⟩ | rfl <;> (have := rlo; unfold WLO at this ⊢; omega)
      refine ⟨hd8, hd32, safeDest_hi d hlo hd8 hd32, fun _ => ?_⟩
      have : layerEnd lay.val = BC.layerEnd lay.val := rfl
      rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
  obtain ⟨hd8, hd32, hsafe, hdend⟩ := hdf
  have hku : KnownOK (BC.bK lay.val c) u := fun p hp => by rw [hu, writeHash_getReg]; exact hkt p hp
  have hkuB : KnownOK (BC.bKB lay.val c) u := fun p hp => hku p (List.mem_of_mem_filter hp)
  have hx12u : u.getReg .x12 = BitVec.ofNat 64 d := by rw [hu, writeHash_getReg]; exact h12
  have hobl : ∀ o ∈ BC.oblB, o.holds u := oblB_holds u d hx12u hd8 (by omega)
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hans : AnsAt u a := by
    constructor
    · simp only [a6E, E.eval]
      rw [hx12u, hu]
      exact writeHash_at0 t a d h12 (by omega)
    · simp only [a7E, E.eval, BinOp.eval, kw]
      rw [hx12u, hu, ofNat_add_ofNat]
      exact writeHash_at8 t a d h12 (by omega)
  have hm1 : (M1E lay.val).eval u = BitVec.ofNat 64 M1c := by
    by_cases h3 : lay.val = 3
    · simp only [M1E, if_pos h3, E.eval, kw]
      have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
      rw [hu, writeHash_frame t a d (TOPLOAD + 8) h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 1 (by decide +kernel)).trans (by decide +kernel)
    · simp only [M1E, if_neg h3, E.eval, kw]
  have hm2 : (M2E lay.val).eval u = BitVec.ofNat 64 M2c := by
    by_cases h3 : lay.val = 3
    · simp only [M2E, if_pos h3, E.eval, kw]
      have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
      rw [hu, writeHash_frame t a d TOPLOAD h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 0 (by decide +kernel)).trans (by decide +kernel)
    · simp only [M2E, if_neg h3, E.eval, kw]
  have hmask : (maskE lay.val).eval u = BitVec.ofNat 64 0x7fc00 := by
    by_cases h3 : lay.val = 3
    · simp only [maskE, if_pos h3, E.eval, kw]
      have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
      rw [hu, writeHash_frame t a d (TOPLOAD + 24) h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 3 (by decide +kernel)).trans (by decide +kernel)
    · simp only [maskE, if_neg h3, E.eval, kw]
  have hdec := canonical_decode_lower_v6 lay hlay (ansD a)
  have hS := lowSumS1_lt (ansD a)
  constructor
  · intro hnone
    have hs := hsp
    have hck : ¬ ckOf lay a < 8 := by
      intro hck
      rw [hdec, if_pos hs, if_pos (by rw [← tgtL_eq]; exact hck)] at hnone
      cases hnone
    obtain ⟨v, hv⟩ := spec_run hB.2 u hpcu hkuB (by
      intro b hb; simp only [rejCk, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (ckBr_iff hans hs lay hm1 hm2 true).mpr (by rw [decide_eq_true hck])
      · exact (spareBr_iff hans lay.val false).mpr (by rw [decide_eq_false (not_not_intro hs)])) hobl
    exact ⟨v, if lay.val = 3 then 23 else 20, if lay.val = 3 then 26 else 23, hv.steps, hv.ecall rfl,
      hv.regs (.x5, kw 1) (by simp [rejCk]), hv.regs (.x10, kw 1) (by simp [rejCk]),
      by split_ifs <;> norm_num, by split_ifs <;> norm_num⟩
  · intro hsome
    have hs : lowerSpare (ansD a) := by
      by_contra hs
      apply hsome; rw [hdec, if_neg hs]
    have hck : ckOf lay a < 8 := by
      by_contra hck
      apply hsome
      rw [hdec, if_pos hs, if_neg (by rw [← tgtL_eq]; exact hck)]
    obtain ⟨h6, h7⟩ := (spare_iff a).mp hs
    obtain ⟨s0, hs0⟩ := spec_run hB.1 u hpcu hkuB (by
      intro b hb; simp only [specBl, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (ckBr_iff hans hs lay hm1 hm2 false).mpr (by rw [decide_eq_false (not_not_intro hck)])
      · exact (spareBr_iff hans lay.val false).mpr (by rw [decide_eq_false (not_not_intro hs)])) hobl
    set L := lctxOf w index lay a with hL
    have hko : KnownOK (postBl lay.val (trPc lay.val c)) s0 := by
      have hk0 := hs0.known
      by_cases h3 : lay.val = 3
      · rw [postBlC, if_pos h3] at hk0
        have e22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) := by
          rw [hs0.regs (.x22, .ld (kw (TOPLOAD - 8))) (by simp [specBl, h3]), h3]
          change u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = _
          have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
          rw [hu, writeHash_frame t a d (TOPLOAD - 8) h12 (by unfold TOPLOAD; omega)
            (by omega) (Or.inr (by unfold TOPLOAD; omega))]
          exact (ht.hdr3 h3).2.1
        have e24 : s0.getReg .x24 = BitVec.ofNat 64 M2c := by
          rw [hs0.regs (.x24, .ld (kw TOPLOAD)) (by simp [specBl, h3])]
          simpa only [M2E, if_pos h3] using hm2
        have e1 : s0.getReg .x1 = BitVec.ofNat 64 M1c := by
          rw [hs0.regs (.x1, .ld (kw (TOPLOAD + 8))) (by simp [specBl, h3])]
          simpa only [M1E, if_pos h3] using hm1
        have e2 : s0.getReg .x9 = BitVec.ofNat 64 0x7fc00 := by
          rw [hs0.regs (.x9, .ld (kw (TOPLOAD + 24))) (by simp [specBl, h3])]
          simpa only [maskE, if_pos h3] using hmask
        have e27 : s0.getReg .x27 = BitVec.ofNat 64 0x3fe00 := by
          rw [hs0.regs (.x27, .bin .srl (maskE 3) (kw 1)) (by simp [specBl, h3])]
          simp only [E.eval, BinOp.eval, kw]
          rw [show (maskE 3).eval u = BitVec.ofNat 64 0x7fc00 by rwa [← h3]]
          rfl
        have e4 : s0.getReg .x4 = BitVec.ofNat 64 (bufferBias lay.val) := by
          rw [hs0.regs (.x4, .ld (kw (TOPB9+56))) (by simp [specBl, h3]), h3]
          change u.getMem (BitVec.ofNat 64 (TOPB9+56)) = _
          have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
          rw [hu, writeHash_frame t a d (TOPB9+56) h12 (by unfold TOPB9; omega)
            (by omega) (Or.inr (by unfold TOPB9; omega))]
          exact ht.glob.2.2.2.2.2.buffer3
        intro q hq
        simp only [postBl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with hq | rfl | rfl | rfl
        · by_cases hq24 : q = (.x24, BitVec.ofNat 64 M2c)
          · subst hq24; exact e24
          by_cases hq1 : q = (.x1, BitVec.ofNat 64 M1c)
          · subst hq1; exact e1
          by_cases hq2 : q = (.x9, 0x7fc00)
          · subst hq2; exact e2
          by_cases hq27 : q = (.x27, 0x3fe00)
          · subst hq27; exact e27
          by_cases hq4 : q = (.x4, BitVec.ofNat 64 (bufferBias lay.val))
          · subst hq4; exact e4
          apply hk0 q
          apply List.mem_append_left
          rw [List.mem_filter]
          refine ⟨hq, ?_⟩
          simp only [chainK, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          all_goals first | contradiction | decide
        · exact e22
        · exact hk0 _ (by simp)
        · exact hk0 _ (by simp)
      · rw [postBlC, if_neg h3] at hk0
        exact hk0
    have hkeep := hs0.keep
    have e29 : ((t4E lay.val).eval u) = 7#64 - BitVec.ofNat 64 (ckOf lay a) := by
      have hT : tgtL lay.val ≤ 202 := by fin_cases lay <;> decide +kernel
      have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide +kernel
      have hle : lowSumS1 (ansD a) ≤ tgtL lay.val ∧ tgtL lay.val - lowSumS1 (ansD a) < 8 := by
        unfold ckOf at hck; omega
      have hcv : ckOf lay a = tgtL lay.val - lowSumS1 (ansD a) := by unfold ckOf; omega
      rw [hcv]
      apply BitVec.eq_of_toNat_eq
      simp only [t4E, E.eval, BinOp.eval, kw]
      rw [BitVec.toNat_add, sumE_eval hans hs lay.val hm1 hm2, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, rfl,
        by simp [hL, lctxOf], tree_actual_lt index lay hidx, ?_, ?_, ?_⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v, Verify.WIT]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; omega
      · simpa only [hL, lctxOf, hL_eq] using leaf_lt index lay
      · simp only [hL, lctxOf]; exact h6
      · simp only [hL, lctxOf]; exact h7
    have hGu : Glob (BC.bK lay.val c) w pk u := Glob_writeHash ht.glob a d h12 hsafe
    have hGs0 := hs0.glob _ w pk hGu (RelOK.nil u)
    have hOu : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) u := by
      have := Orig_writeHash ht.orig a d h12 (by omega)
      have hL8 : layerEnd lay.val % 8 = 0 := by
        fin_cases lay <;> decide +kernel
      intro j hj hp
      refine this j hj ⟨hp, ?_⟩
      have hp2 := hp.2
      by_cases h3 : lay.val = 3
      · rw [if_pos h3] at hdc
        exact Or.inr (by unfold WIT; rcases hdc with hdc | hdc <;> omega)
      · have hx := hdend h3
        exact Or.inl (by omega)
    have hOs0 : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) s0 := by
      have := hs0.orig_const hOu
      exact this.mono (fun o ho => ⟨ho, by simp⟩)
    have hBd : d + 32 ≤ WIT + BC.bufferStart lay.val := by
      have ht : ∀ l c, l < 3 → c < nCopy l → rowA l c + 80 ≤ WIT + BC.bufferStart l := by
        have H : ([0,1,2].all fun l => (List.range (nCopy l)).all fun c =>
          decide (rowA l c + 80 ≤ WIT + BC.bufferStart l)) = true := by decide +kernel
        intro l c hl hc
        exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp H l (by simp; omega)) c (List.mem_range.mpr hc))
      by_cases h3 : lay.val = 3
      · rw [if_pos h3] at hdc; rcases hdc with rfl | rfl <;> (rw [h3]; decide +kernel)
      · rw [if_neg h3] at hdc
        have H := ht lay.val c (by have := lay.isLt; omega) hc
        rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
    have hBu : Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) u := by
      have H := Orig_writeHash ht.bufferOrig a d h12 (by omega)
      exact H.mono (fun o ho => ⟨ho, Or.inr (by omega)⟩)
    have hBs0 : Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) s0 := by
      exact (hs0.orig_const hBu).mono (fun o ho => ⟨ho, by simp⟩)
    have hpc0 : s0.pc = pcOf (L.startPc 0) := by
      rw [hs0.spc (tgtl lay.val) rfl]
      have hk0 : L.kOf 0 = (a.extractLsb' 0 64).toNat % 512 := by
        rw [L.kOf_eq 0 (by norm_num), if_pos (by norm_num)]
        show (a.extractLsb' 0 64).toNat / 2 ^ (9 * (0 % 7)) % 512 = _
        rw [show 9 * (0 % 7) = 0 from rfl, pow_zero, Nat.div_one]
      have hm : ((a.extractLsb' 0 64) <<< ((BitVec.ofNat 64 10).toNat % 64) &&& BitVec.ofNat 64 0x7fc00) =
          BitVec.ofNat 64 (1024 * L.kOf 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_andc _ _ (by norm_num), toNat_sll _ 10 (by norm_num),
          show (0x7fc00 : Nat) = 2^10 * (2^9-1) by norm_num,
          land_mask_pow, field_shl_pow _ _ _ _ (le_refl _) (by norm_num), hk0,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 1024 * ((a.extractLsb' 0 64).toNat % 512) < 2 ^ 64 by omega)]
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        rfl
      have hadd : (tgtl lay.val).eval u =
          (BitVec.ofNat 64 (1024 * L.kOf 0) + BitVec.ofNat 64 1992) &&& ~~~1#64 := by
        simp only [tgtl, x14l, E.eval, BinOp.eval, a6E_eval hans, kw, hmask, hm]
      rw [hadd, ofNat_add_ofNat, even_andNot1' _ (by omega)]
      unfold LCtx.startPc
      simp only [Nat.reduceEqDiff, if_false, Nat.zero_div, Nat.zero_mod, ite_true]
      rw [entW_address 0 (L.kOf 0) (by norm_num) (by rw [hk0]; omega)]
      rfl
    have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := fun q hq => hko q (by simp [postBl, hq])
    refine ⟨s0, hs0.steps, hLok, ?_, ?_, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl,
      hGs0.2.2.2.2.2, hpc0⟩, ⟨hkL, hGs0.2.1, hGs0.2.2.1, hGs0.2.2.2.1, hGs0.2.2.2.2⟩, hOs0, ?_, ?_, ?_, hBs0⟩
    · apply lctxOf_known w index lay hlay a (trPc lay.val c) s0 hko
      · rw [hkeep .x28 (by unfold keepB; split_ifs <;> simp), hu, writeHash_getReg, ht.word,
          show BC.below lay.val = below lay.val from rfl, hyperWord_x28v w index lay a]
      · rw [hs0.regs (.x16, a6E) (by simp [specBl]), a6E_eval hans]
      · rw [hs0.regs (.x17, a7E) (by simp [specBl]), a7E_eval hans]
      · rw [hs0.regs (.x29, t4E lay.val) (by simp [specBl]), e29]
    · constructor
      · intro i hi hi' k hk
        have hb := L.blk_props hLok i hi'
        have hls := LCtx.lowerSlot_props i hi'
        have hS6 : L.S6 = s6v lay.val := rfl
        apply origW_of hOs0 _ (by unfold WIT; omega) (by
            unfold WIT; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v, Verify.WIT] at * <;> omega)
          (by unfold WIT WX; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v, Verify.WIT] at * <;> omega)
        simp only [LCtx.blk, hS6]
        unfold WIT
        fin_cases lay <;> simp [s6v, layerEnd, Verify.WIT] at * <;> omega
      · intro i hi hi' k hk
        rw [L.bufferSlot_eq hlay i]
        change OrigW w s0 (0x1020 + ClaudeWCT.W9.T3M.leafBufferSlot lay i + 8*k)
        have hn : chainCount lay = 43 := by
          have H : ∀ l : Layer, l ≠ 0 → chainCount l = 43 := by decide +kernel
          exact H lay hlay
        have hb := ClaudeWCT.W9.T3M.leafBufferSlot_bounds lay i (by omega)
        have hlo : BC.bufferStart lay.val ≤ ClaudeWCT.W9.T3M.leafBufferSlot lay i := by
          have e : BC.bufferStart lay.val = ClaudeWCT.W9.T3M.leafBufferBase lay := by
            fin_cases lay <;> first | exact absurd rfl hlay | rfl
          rw [e]; unfold ClaudeWCT.W9.T3M.leafBufferSlot; omega
        apply origW_of hBs0 _ (by unfold WIT; omega) (by unfold WIT; omega) (by unfold WIT WX; omega)
        unfold WIT; constructor <;> omega
    · rw [hs0.regs (.x23, s23E lay.val) (by simp [specBl])]
      have hs7u : (if lay.val = 3 then (s7E 3).eval u else u.getReg .x23) =
          BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) := by
        by_cases h3 : lay.val = 3
        · obtain rfl : lay = 3 := Fin.ext h3
          rw [if_pos h3]
          have h22u : u.getReg (rReg 3) = BitVec.ofNat 64 (index / 2 ^ below 3) := by
            rw [show rReg 3 = .x22 from rfl, show below 3 = 0 from rfl, pow_zero, Nat.div_one, hu, writeHash_getReg]
            exact ht.index3 rfl
          exact (route_evals index 3 hidx u h22u).2.2.2
        · rw [if_neg h3, hu, writeHash_getReg]
          exact ht.s7 lay rfl (by have := lay.isLt; omega)
      have hs23 : (s23E lay.val).eval u =
          BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) <<< ((BitVec.ofNat 64 (s7Sh lay.val)).toNat % 64) := by
        by_cases h3 : lay.val = 3
        · rw [if_pos h3] at hs7u
          rw [s23E, s7Sh, if_pos h3, if_neg (by omega : lay.val ≠ 1)]
          simp only [E.eval, BinOp.eval, hs7u, kw]
        · rw [if_neg h3] at hs7u
          simp only [s23E, if_neg h3, E.eval, BinOp.eval, hs7u, kw]
      rw [hs23]
      have hsh : s7Sh lay.val < 64 := by unfold s7Sh; split_ifs <;> omega
      have hb : s7Bias lay.val ≤ 4096 := by fin_cases lay <;> decide +kernel
      have hl := leaf_lt32 index lay
      have hD : dispatchHeap lay.val (route index lay).1 < 2 ^ 64 := by unfold dispatchHeap; split_ifs <;> omega
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sll _ _ hsh, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD]
      rfl
    · by_cases h3 : lay.val = 3
      · obtain rfl : lay = 3 := Fin.ext h3
        rw [hs0.regs (.x31, treeE 3) (by simp [specBl])]
        have h22u : u.getReg (rReg 3) = BitVec.ofNat 64 (index / 2 ^ below 3) := by
          rw [show rReg 3 = .x22 from rfl, show below 3 = 0 from rfl, pow_zero, Nat.div_one, hu, writeHash_getReg]
          exact ht.index3 rfl
        exact (route_evals index 3 hidx u h22u).2.1
      · rw [hkeep .x31 (by simp [keepB, h3]), hu, writeHash_getReg, (ht.t5 lay rfl).1 h0 (by have := lay.isLt; omega)]
    · exact hko (.x2, BitVec.ofNat 64 0xffbde0) (by simp [postBl])
theorem encB_step_hi (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t)
    (a : BitVec 256) (hlo : ¬ lowerSpare (ansD a)) (hsp : lowerSpare (ansD (highView a))) :
    (canonicalDecode lay (ansD (highView a)) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1 ∧ k ≤ 27 ∧ cy ≤ 30) ∧
    (canonicalDecode lay (ansD (highView a)) ≠ none → ∃ s0, Steps image (writeHash t a) (bSt lay.val+4) (bCy lay.val+4) s0 ∧
        (lctxOf w index lay (highView a)).ok ∧
        (∀ p ∈ (lctxOf w index lay (highView a)).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay (highView a)).Orig0 s0 ∧
        (lctxOf w index lay (highView a)).ChainIn s0 0 [] s0 ∧ Glob (chainK lay.val) w pk s0 ∧
        Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (lfS7 lay.val (route index lay).1) ∧
        s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2 ∧
        s0.getReg .x2 = BitVec.ofNat 64 0xffbde0 ∧
        Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) s0) := by
  let b := highView a
  set u := writeHash t a with hu
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hB := copy_parts_hi lay.val c (BC.copyCheck_at lay.val c lay.isLt hc) h0
  have hkt : KnownOK (BC.bK lay.val c) t := ht.glob.1
  obtain ⟨d, h12, hdc⟩ : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧
      (if lay.val = 3 then (d = 4112 ∨ d = 4176) else
        ((d + 16 = rowA lay.val c ∧ WIT + BC.layerEnd lay.val + 16 ≤ rowA lay.val c) ∨ d = rowA lay.val c + 48)) := by
    by_cases h3 : lay.val = 3
    · rcases ht.dst3 h3 with hd | hd
      · exact ⟨4112, hd, by rw [if_pos h3]; exact Or.inl rfl⟩
      · exact ⟨4176, hd, by rw [if_pos h3]; exact Or.inr rfl⟩
    · obtain ⟨d, hd, hdd⟩ := ht.dst (by have := lay.isLt; omega)
      exact ⟨d, hd, by rw [if_neg h3]; exact hdd⟩
  have hdf : d % 8 = 0 ∧ d + 32 ≤ 2 ^ 23 ∧ safeDest d = true ∧ (lay.val ≠ 3 → WIT + layerEnd lay.val ≤ d) := by
    by_cases h3 : lay.val = 3
    · rw [if_pos h3] at hdc
      rcases hdc with rfl | rfl <;>
        exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun h => absurd h3 h⟩
    · rw [if_neg h3] at hdc
      obtain ⟨r16, rlo, rhi, rend⟩ := rowA_facts lay.val c (by have := lay.isLt; omega) hc
      have hd8 : d % 8 = 0 := by rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
      have hd32 : d + 32 ≤ 2 ^ 23 := by rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
      have hlo : WLO ≤ d := by
        have hle : 48 ≤ BC.layerEnd lay.val := by
          have := lay.isLt; unfold BC.layerEnd
          rcases (show lay.val = 0 ∨ lay.val = 1 ∨ lay.val = 2 ∨ lay.val = 3 by omega) with h | h | h | h <;> simp [h]
        rcases hdc with ⟨hd1, hd2⟩ | rfl <;> (have := rlo; unfold WLO at this ⊢; omega)
      refine ⟨hd8, hd32, safeDest_hi d hlo hd8 hd32, fun _ => ?_⟩
      have : layerEnd lay.val = BC.layerEnd lay.val := rfl
      rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
  obtain ⟨hd8, hd32, hsafe, hdend⟩ := hdf
  have hku : KnownOK (BC.bK lay.val c) u := fun p hp => by rw [hu, writeHash_getReg]; exact hkt p hp
  have hkuB : KnownOK (BC.bKB lay.val c) u := fun p hp => hku p (List.mem_of_mem_filter hp)
  have hx12u : u.getReg .x12 = BitVec.ofNat 64 d := by rw [hu, writeHash_getReg]; exact h12
  have hobl : ∀ o ∈ BC.oblBHi, o.holds u := by
    intro o ho
    simp only [BC.oblBHi, BC.oblB, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with (rfl | rfl) | rfl | rfl <;>
      simp only [Oblig.holds, Addr.eval, E.eval, hx12u, accessValid, rangeValid, Bool.and_eq_true,
        decide_eq_true_eq, MEMORY_BYTES, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (24 : Word).toNat = 24 from rfl, show (16 : Word).toNat = 16 from rfl,
        show (8 : Word).toNat = 8 from rfl, show (0 : Word).toNat = 0 from rfl] <;> omega
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hansLow : AnsAt u a := by
    constructor
    · simp only [a6E, E.eval]; rw [hx12u, hu]
      exact writeHash_at0 t a d h12 (by omega)
    · simp only [a7E, E.eval, BinOp.eval, kw]; rw [hx12u, hu, ofNat_add_ofNat]
      exact writeHash_at8 t a d h12 (by omega)
  have hans : AnsAtHi u b := by
    constructor
    · simp only [a6HiE, E.eval, BinOp.eval, kw]; rw [hx12u, hu, ofNat_add_ofNat]
      rw [show b.extractLsb' 0 64 = a.extractLsb' 128 64 from highView_extract a 0 64]
      exact writeHash_at16 t a d h12 (by omega)
    · simp only [a7HiE, E.eval, BinOp.eval, kw]; rw [hx12u, hu, ofNat_add_ofNat]
      rw [show b.extractLsb' 64 64 = a.extractLsb' 192 64 from highView_extract a 64 64]
      exact writeHash_at24 t a d h12 (by omega)
  have hm1 : (M1E lay.val).eval u = BitVec.ofNat 64 M1c := by
    by_cases h3 : lay.val = 3
    · simp only [M1E, if_pos h3, E.eval, kw]
      have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
      rw [hu, writeHash_frame t a d (TOPLOAD + 8) h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 1 (by decide +kernel)).trans (by decide +kernel)
    · simp only [M1E, if_neg h3, E.eval, kw]
  have hm2 : (M2E lay.val).eval u = BitVec.ofNat 64 M2c := by
    by_cases h3 : lay.val = 3
    · simp only [M2E, if_pos h3, E.eval, kw]
      have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
      rw [hu, writeHash_frame t a d TOPLOAD h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 0 (by decide +kernel)).trans (by decide +kernel)
    · simp only [M2E, if_neg h3, E.eval, kw]
  have hmask : (maskE lay.val).eval u = BitVec.ofNat 64 0x7fc00 := by
    by_cases h3 : lay.val = 3
    · simp only [maskE, if_pos h3, E.eval, kw]
      have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
      rw [hu, writeHash_frame t a d (TOPLOAD + 24) h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 3 (by decide +kernel)).trans (by decide +kernel)
    · simp only [maskE, if_neg h3, E.eval, kw]
  have hdec := canonical_decode_lower_v6 lay hlay (ansD b)
  have hS := lowSumS1_lt (ansD b)
  constructor
  · intro hnone
    have hs := hsp
    have hck : ¬ ckOf lay b < 8 := by
      intro hck
      rw [hdec, if_pos hs, if_pos (by rw [← tgtL_eq]; exact hck)] at hnone
      cases hnone
    obtain ⟨v, hv⟩ := spec_run hB.2 u hpcu hkuB (by
      intro b hb; simp only [rejCkHi, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact (ckHiBr_iff hans hs lay hm1 hm2 true).mpr (by rw [decide_eq_true hck])
      · exact (spareHiBr_iff hans lay.val false).mpr (by rw [decide_eq_false (not_not_intro hs)])
      · exact (spareBr_iff hansLow lay.val true).mpr (by rw [decide_eq_true hlo])) hobl
    exact ⟨v, (if lay.val = 3 then 23 else 20)+4, (if lay.val = 3 then 26 else 23)+4, hv.steps, hv.ecall rfl,
      hv.regs (.x5, kw 1) (by simp [rejCkHi]), hv.regs (.x10, kw 1) (by simp [rejCkHi]),
      by split_ifs <;> norm_num, by split_ifs <;> norm_num⟩
  · intro hsome
    have hs : lowerSpare (ansD b) := by
      by_contra hs
      apply hsome; rw [hdec, if_neg hs]
    have hck : ckOf lay b < 8 := by
      by_contra hck
      apply hsome
      rw [hdec, if_pos hs, if_neg (by rw [← tgtL_eq]; exact hck)]
    obtain ⟨h6, h7⟩ := (spare_iff b).mp hs
    obtain ⟨s0, hs0⟩ := spec_run hB.1 u hpcu hkuB (by
      intro b hb; simp only [specBlHi, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact (ckHiBr_iff hans hs lay hm1 hm2 false).mpr (by rw [decide_eq_false (not_not_intro hck)])
      · exact (spareHiBr_iff hans lay.val false).mpr (by rw [decide_eq_false (not_not_intro hs)])
      · exact (spareBr_iff hansLow lay.val true).mpr (by rw [decide_eq_true hlo])) hobl
    set L := lctxOf w index lay b with hL
    have hko : KnownOK (postBl lay.val (trPc lay.val c)) s0 := by
      have hk0 := hs0.known
      by_cases h3 : lay.val = 3
      · rw [postBlC, if_pos h3] at hk0
        have e22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) := by
          rw [hs0.regs (.x22, .ld (kw (TOPLOAD - 8))) (by simp [specBlHi, h3]), h3]
          change u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = _
          have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
          rw [hu, writeHash_frame t a d (TOPLOAD - 8) h12 (by unfold TOPLOAD; omega)
            (by omega) (Or.inr (by unfold TOPLOAD; omega))]
          exact (ht.hdr3 h3).2.1
        have e24 : s0.getReg .x24 = BitVec.ofNat 64 M2c := by
          rw [hs0.regs (.x24, .ld (kw TOPLOAD)) (by simp [specBlHi, h3])]
          simpa only [M2E, if_pos h3] using hm2
        have e1 : s0.getReg .x1 = BitVec.ofNat 64 M1c := by
          rw [hs0.regs (.x1, .ld (kw (TOPLOAD + 8))) (by simp [specBlHi, h3])]
          simpa only [M1E, if_pos h3] using hm1
        have e2 : s0.getReg .x9 = BitVec.ofNat 64 0x7fc00 := by
          rw [hs0.regs (.x9, .ld (kw (TOPLOAD + 24))) (by simp [specBlHi, h3])]
          simpa only [maskE, if_pos h3] using hmask
        have e27 : s0.getReg .x27 = BitVec.ofNat 64 0x3fe00 := by
          rw [hs0.regs (.x27, .bin .srl (maskE 3) (kw 1)) (by simp [specBlHi, h3])]
          simp only [E.eval, BinOp.eval, kw]
          rw [show (maskE 3).eval u = BitVec.ofNat 64 0x7fc00 by rwa [← h3]]
          rfl
        have e4 : s0.getReg .x4 = BitVec.ofNat 64 (bufferBias lay.val) := by
          rw [hs0.regs (.x4, .ld (kw (TOPB9+56))) (by simp [specBlHi, h3]), h3]
          change u.getMem (BitVec.ofNat 64 (TOPB9+56)) = _
          have hd3 : d ≤ 4176 := by rw [if_pos h3] at hdc; rcases hdc with hdc | hdc <;> omega
          rw [hu, writeHash_frame t a d (TOPB9+56) h12 (by unfold TOPB9; omega)
            (by omega) (Or.inr (by unfold TOPB9; omega))]
          exact ht.glob.2.2.2.2.2.buffer3
        intro q hq
        simp only [postBl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with hq | rfl | rfl | rfl
        · by_cases hq24 : q = (.x24, BitVec.ofNat 64 M2c)
          · subst hq24; exact e24
          by_cases hq1 : q = (.x1, BitVec.ofNat 64 M1c)
          · subst hq1; exact e1
          by_cases hq2 : q = (.x9, 0x7fc00)
          · subst hq2; exact e2
          by_cases hq27 : q = (.x27, 0x3fe00)
          · subst hq27; exact e27
          by_cases hq4 : q = (.x4, BitVec.ofNat 64 (bufferBias lay.val))
          · subst hq4; exact e4
          apply hk0 q
          apply List.mem_append_left
          rw [List.mem_filter]
          refine ⟨hq, ?_⟩
          simp only [chainK, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          all_goals first | contradiction | decide
        · exact e22
        · exact hk0 _ (by simp)
        · exact hk0 _ (by simp)
      · rw [postBlC, if_neg h3] at hk0
        exact hk0
    have hkeep := hs0.keep
    have e29 : ((t4HiE lay.val).eval u) = 7#64 - BitVec.ofNat 64 (ckOf lay b) := by
      have hT : tgtL lay.val ≤ 202 := by fin_cases lay <;> decide +kernel
      have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide +kernel
      have hle : lowSumS1 (ansD b) ≤ tgtL lay.val ∧ tgtL lay.val - lowSumS1 (ansD b) < 8 := by
        unfold ckOf at hck; omega
      have hcv : ckOf lay b = tgtL lay.val - lowSumS1 (ansD b) := by unfold ckOf; omega
      rw [hcv]
      apply BitVec.eq_of_toNat_eq
      simp only [t4HiE, E.eval, BinOp.eval, kw]
      rw [BitVec.toNat_add, sumHiE_eval hans hs lay.val hm1 hm2, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, rfl,
        by simp [hL, lctxOf], tree_actual_lt index lay hidx, ?_, ?_, ?_⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v, Verify.WIT]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; omega
      · simpa only [hL, lctxOf, hL_eq] using leaf_lt index lay
      · simp only [hL, lctxOf]; exact h6
      · simp only [hL, lctxOf]; exact h7
    have hGu : Glob (BC.bK lay.val c) w pk u := Glob_writeHash ht.glob a d h12 hsafe
    have hGs0 := hs0.glob _ w pk hGu (RelOK.nil u)
    have hOu : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) u := by
      have := Orig_writeHash ht.orig a d h12 (by omega)
      have hL8 : layerEnd lay.val % 8 = 0 := by
        fin_cases lay <;> decide +kernel
      intro j hj hp
      refine this j hj ⟨hp, ?_⟩
      have hp2 := hp.2
      by_cases h3 : lay.val = 3
      · rw [if_pos h3] at hdc
        exact Or.inr (by unfold WIT; rcases hdc with hdc | hdc <;> omega)
      · have hx := hdend h3
        exact Or.inl (by omega)
    have hOs0 : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) s0 := by
      have := hs0.orig_const hOu
      exact this.mono (fun o ho => ⟨ho, by simp⟩)
    have hBd : d + 32 ≤ WIT + BC.bufferStart lay.val := by
      have ht : ∀ l c, l < 3 → c < nCopy l → rowA l c + 80 ≤ WIT + BC.bufferStart l := by
        have H : ([0,1,2].all fun l => (List.range (nCopy l)).all fun c =>
          decide (rowA l c + 80 ≤ WIT + BC.bufferStart l)) = true := by decide +kernel
        intro l c hl hc
        exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp H l (by simp; omega)) c (List.mem_range.mpr hc))
      by_cases h3 : lay.val = 3
      · rw [if_pos h3] at hdc; rcases hdc with rfl | rfl <;> (rw [h3]; decide +kernel)
      · rw [if_neg h3] at hdc
        have H := ht lay.val c (by have := lay.isLt; omega) hc
        rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
    have hBu : Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) u := by
      have H := Orig_writeHash ht.bufferOrig a d h12 (by omega)
      exact H.mono (fun o ho => ⟨ho, Or.inr (by omega)⟩)
    have hBs0 : Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) s0 := by
      exact (hs0.orig_const hBu).mono (fun o ho => ⟨ho, by simp⟩)
    have hpc0 : s0.pc = pcOf (L.startPc 0) := by
      rw [hs0.spc (tgtHi lay.val) rfl]
      have hk0 : L.kOf 0 = (b.extractLsb' 0 64).toNat % 512 := by
        rw [L.kOf_eq 0 (by norm_num), if_pos (by norm_num)]
        show (b.extractLsb' 0 64).toNat / 2 ^ (9 * (0 % 7)) % 512 = _
        rw [show 9 * (0 % 7) = 0 from rfl, pow_zero, Nat.div_one]
      have hm : ((b.extractLsb' 0 64) <<< ((BitVec.ofNat 64 10).toNat % 64) &&& BitVec.ofNat 64 0x7fc00) =
          BitVec.ofNat 64 (1024 * L.kOf 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_andc _ _ (by norm_num), toNat_sll _ 10 (by norm_num),
          show (0x7fc00 : Nat) = 2^10 * (2^9-1) by norm_num,
          land_mask_pow, field_shl_pow _ _ _ _ (le_refl _) (by norm_num), hk0,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 1024 * ((b.extractLsb' 0 64).toNat % 512) < 2 ^ 64 by omega)]
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        rfl
      have hadd : (tgtHi lay.val).eval u =
          (BitVec.ofNat 64 (1024 * L.kOf 0) + BitVec.ofNat 64 1992) &&& ~~~1#64 := by
        simp only [tgtHi, x14Hi, E.eval, BinOp.eval, a6HiE_eval hans, kw, hmask, hm]
      rw [hadd, ofNat_add_ofNat, even_andNot1' _ (by omega)]
      unfold LCtx.startPc
      simp only [Nat.reduceEqDiff, if_false, Nat.zero_div, Nat.zero_mod, ite_true]
      rw [entW_address 0 (L.kOf 0) (by norm_num) (by rw [hk0]; omega)]
      rfl
    have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := fun q hq => hko q (by simp [postBl, hq])
    refine ⟨s0, hs0.steps, hLok, ?_, ?_, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl,
      hGs0.2.2.2.2.2, hpc0⟩, ⟨hkL, hGs0.2.1, hGs0.2.2.1, hGs0.2.2.2.1, hGs0.2.2.2.2⟩, hOs0, ?_, ?_, ?_, hBs0⟩
    · apply lctxOf_known w index lay hlay b (trPc lay.val c) s0 hko
      · rw [hkeep .x28 (by unfold keepB; split_ifs <;> simp), hu, writeHash_getReg, ht.word,
          show BC.below lay.val = below lay.val from rfl, hyperWord_x28v w index lay b]
      · rw [hs0.regs (.x16, a6HiE) (by simp [specBlHi]), a6HiE_eval hans]
      · rw [hs0.regs (.x17, a7HiE) (by simp [specBlHi]), a7HiE_eval hans]
      · rw [hs0.regs (.x29, t4HiE lay.val) (by simp [specBlHi]), e29]
    · constructor
      · intro i hi hi' k hk
        have hb := L.blk_props hLok i hi'
        have hls := LCtx.lowerSlot_props i hi'
        have hS6 : L.S6 = s6v lay.val := rfl
        apply origW_of hOs0 _ (by unfold WIT; omega) (by
            unfold WIT; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v, Verify.WIT] at * <;> omega)
          (by unfold WIT WX; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v, Verify.WIT] at * <;> omega)
        simp only [LCtx.blk, hS6]
        unfold WIT
        fin_cases lay <;> simp [s6v, layerEnd, Verify.WIT] at * <;> omega
      · intro i hi hi' k hk
        rw [L.bufferSlot_eq hlay i]
        change OrigW w s0 (0x1020 + ClaudeWCT.W9.T3M.leafBufferSlot lay i + 8*k)
        have hn : chainCount lay = 43 := by
          have H : ∀ l : Layer, l ≠ 0 → chainCount l = 43 := by decide +kernel
          exact H lay hlay
        have hb := ClaudeWCT.W9.T3M.leafBufferSlot_bounds lay i (by omega)
        have hlo : BC.bufferStart lay.val ≤ ClaudeWCT.W9.T3M.leafBufferSlot lay i := by
          have e : BC.bufferStart lay.val = ClaudeWCT.W9.T3M.leafBufferBase lay := by
            fin_cases lay <;> first | exact absurd rfl hlay | rfl
          rw [e]; unfold ClaudeWCT.W9.T3M.leafBufferSlot; omega
        apply origW_of hBs0 _ (by unfold WIT; omega) (by unfold WIT; omega) (by unfold WIT WX; omega)
        unfold WIT; constructor <;> omega
    · rw [hs0.regs (.x23, s23E lay.val) (by simp [specBlHi])]
      have hs7u : (if lay.val = 3 then (s7E 3).eval u else u.getReg .x23) =
          BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) := by
        by_cases h3 : lay.val = 3
        · obtain rfl : lay = 3 := Fin.ext h3
          rw [if_pos h3]
          have h22u : u.getReg (rReg 3) = BitVec.ofNat 64 (index / 2 ^ below 3) := by
            rw [show rReg 3 = .x22 from rfl, show below 3 = 0 from rfl, pow_zero, Nat.div_one, hu, writeHash_getReg]
            exact ht.index3 rfl
          exact (route_evals index 3 hidx u h22u).2.2.2
        · rw [if_neg h3, hu, writeHash_getReg]
          exact ht.s7 lay rfl (by have := lay.isLt; omega)
      have hs23 : (s23E lay.val).eval u =
          BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) <<< ((BitVec.ofNat 64 (s7Sh lay.val)).toNat % 64) := by
        by_cases h3 : lay.val = 3
        · rw [if_pos h3] at hs7u
          rw [s23E, s7Sh, if_pos h3, if_neg (by omega : lay.val ≠ 1)]
          simp only [E.eval, BinOp.eval, hs7u, kw]
        · rw [if_neg h3] at hs7u
          simp only [s23E, if_neg h3, E.eval, BinOp.eval, hs7u, kw]
      rw [hs23]
      have hsh : s7Sh lay.val < 64 := by unfold s7Sh; split_ifs <;> omega
      have hb : s7Bias lay.val ≤ 4096 := by fin_cases lay <;> decide +kernel
      have hl := leaf_lt32 index lay
      have hD : dispatchHeap lay.val (route index lay).1 < 2 ^ 64 := by unfold dispatchHeap; split_ifs <;> omega
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sll _ _ hsh, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD]
      rfl
    · by_cases h3 : lay.val = 3
      · obtain rfl : lay = 3 := Fin.ext h3
        rw [hs0.regs (.x31, treeE 3) (by simp [specBlHi])]
        have h22u : u.getReg (rReg 3) = BitVec.ofNat 64 (index / 2 ^ below 3) := by
          rw [show rReg 3 = .x22 from rfl, show below 3 = 0 from rfl, pow_zero, Nat.div_one, hu, writeHash_getReg]
          exact ht.index3 rfl
        exact (route_evals index 3 hidx u h22u).2.1
      · rw [hkeep .x31 (by simp [keepB, h3]), hu, writeHash_getReg, (ht.t5 lay rfl).1 h0 (by have := lay.isLt; omega)]
    · exact hko (.x2, BitVec.ofNat 64 0xffbde0) (by simp [postBl])
theorem encB_step_trap (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat)
    (lay : Layer) (hlay : lay ≠ 0) (c : Nat) (hc : c < nCopy lay.val)
    (t : MachineState) (ht : EncPre w pk index lay.val c t) (a : BitVec 256)
    (hlo : ¬ lowerSpare (ansD a)) (hhi : ¬ lowerSpare (ansD (highView a))) :
    ∃ v, Steps image (writeHash t a) 8 8 v ∧ fetch image v = none := by
  let b := highView a
  set u := writeHash t a with hu
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hfull := BC.copyCheck_at lay.val c lay.isLt hc
  unfold BC.copyCheck at hfull
  rw [if_neg h0] at hfull
  simp only [Bool.and_eq_true] at hfull
  have hB : specB [] [] [] (runAt (BC.bKB lay.val c) [spareTrap lay.val c]
      (trPc lay.val c + stepsA lay.val + 1) [.br (decide (lay.val ≠ 3)), .br false])
      (rejBothSpare lay.val c) BC.oblBHi [] [] = true := by tauto
  have hzero : vlook (spareTrap lay.val c) = some 0 := by
    have H : (vlook (spareTrap lay.val c) == some 0) = true := by tauto
    simpa only [beq_iff_eq] using H
  have hkt : KnownOK (BC.bK lay.val c) t := ht.glob.1
  obtain ⟨d, h12, hdc⟩ : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧
      (if lay.val = 3 then (d = 4112 ∨ d = 4176) else
        ((d + 16 = rowA lay.val c ∧ WIT + BC.layerEnd lay.val + 16 ≤ rowA lay.val c) ∨ d = rowA lay.val c + 48)) := by
    by_cases h3 : lay.val = 3
    · rcases ht.dst3 h3 with hd | hd
      · exact ⟨4112, hd, by rw [if_pos h3]; exact Or.inl rfl⟩
      · exact ⟨4176, hd, by rw [if_pos h3]; exact Or.inr rfl⟩
    · obtain ⟨d, hd, hdd⟩ := ht.dst (by have := lay.isLt; omega)
      exact ⟨d, hd, by rw [if_neg h3]; exact hdd⟩
  have hdf : d % 8 = 0 ∧ d + 32 ≤ 2 ^ 23 ∧ safeDest d = true ∧ (lay.val ≠ 3 → WIT + layerEnd lay.val ≤ d) := by
    by_cases h3 : lay.val = 3
    · rw [if_pos h3] at hdc
      rcases hdc with rfl | rfl <;>
        exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun h => absurd h3 h⟩
    · rw [if_neg h3] at hdc
      obtain ⟨r16, rlo, rhi, rend⟩ := rowA_facts lay.val c (by have := lay.isLt; omega) hc
      have hd8 : d % 8 = 0 := by rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
      have hd32 : d + 32 ≤ 2 ^ 23 := by rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
      have hlo : WLO ≤ d := by
        have hle : 48 ≤ BC.layerEnd lay.val := by
          have := lay.isLt; unfold BC.layerEnd
          rcases (show lay.val = 0 ∨ lay.val = 1 ∨ lay.val = 2 ∨ lay.val = 3 by omega) with h | h | h | h <;> simp [h]
        rcases hdc with ⟨hd1, hd2⟩ | rfl <;> (have := rlo; unfold WLO at this ⊢; omega)
      refine ⟨hd8, hd32, safeDest_hi d hlo hd8 hd32, fun _ => ?_⟩
      have : layerEnd lay.val = BC.layerEnd lay.val := rfl
      rcases hdc with ⟨hd1, hd2⟩ | rfl <;> omega
  obtain ⟨hd8, hd32, hsafe, hdend⟩ := hdf
  have hku : KnownOK (BC.bK lay.val c) u := fun p hp => by rw [hu, writeHash_getReg]; exact hkt p hp
  have hkuB : KnownOK (BC.bKB lay.val c) u := fun p hp => hku p (List.mem_of_mem_filter hp)
  have hx12u : u.getReg .x12 = BitVec.ofNat 64 d := by rw [hu, writeHash_getReg]; exact h12
  have hobl : ∀ o ∈ BC.oblBHi, o.holds u := by
    intro o ho
    simp only [BC.oblBHi, BC.oblB, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with (rfl | rfl) | rfl | rfl <;>
      simp only [Oblig.holds, Addr.eval, E.eval, hx12u, accessValid, rangeValid, Bool.and_eq_true,
        decide_eq_true_eq, MEMORY_BYTES, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (24 : Word).toNat = 24 from rfl, show (16 : Word).toNat = 16 from rfl,
        show (8 : Word).toNat = 8 from rfl, show (0 : Word).toNat = 0 from rfl] <;> omega
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hansLow : AnsAt u a := by
    constructor
    · simp only [a6E, E.eval]; rw [hx12u, hu]
      exact writeHash_at0 t a d h12 (by omega)
    · simp only [a7E, E.eval, BinOp.eval, kw]; rw [hx12u, hu, ofNat_add_ofNat]
      exact writeHash_at8 t a d h12 (by omega)
  have hans : AnsAtHi u b := by
    constructor
    · simp only [a6HiE, E.eval, BinOp.eval, kw]; rw [hx12u, hu, ofNat_add_ofNat]
      rw [show b.extractLsb' 0 64 = a.extractLsb' 128 64 from highView_extract a 0 64]
      exact writeHash_at16 t a d h12 (by omega)
    · simp only [a7HiE, E.eval, BinOp.eval, kw]; rw [hx12u, hu, ofNat_add_ofNat]
      rw [show b.extractLsb' 64 64 = a.extractLsb' 192 64 from highView_extract a 64 64]
      exact writeHash_at24 t a d h12 (by omega)
  obtain ⟨v, hv⟩ := spec_run hB u hpcu hkuB (by
    intro b hb
    simp only [rejBothSpare, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact (spareHiBr_iff hans lay.val true).mpr (by rw [decide_eq_true hhi])
    · exact (spareBr_iff hansLow lay.val true).mpr (by rw [decide_eq_true hlo])) hobl
  refine ⟨v, hv.steps, ?_⟩
  have hp : v.pc = pcOf (spareTrap lay.val c) := hv.pc rfl
  have hb : spareTrap lay.val c < 257214 := by
    have H : ((List.range 4).all fun l => (List.range (nCopy l)).all fun c =>
      decide (spareTrap l c < 257214)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp H lay.val
      (List.mem_range.mpr lay.isLt)) c (List.mem_range.mpr hc))
  have hn : (pcOf (spareTrap lay.val c)).toNat = 0x1000 + 4*spareTrap lay.val c := by
    unfold pcOf; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have H := fetch_of_look vlook_ok (pc := pcOf (spareTrap lay.val c))
    (by simp only [hn]; simp <;> omega)
    (by simpa only [hn, show (0x1000 + 4*spareTrap lay.val c-0x1000)/4 = spareTrap lay.val c by omega] using hzero) v hp
  exact H

def selectedView (a : BitVec 256) : BitVec 256 := if lowerSpare (ansD a) then a else highView a

theorem selectedView_answer (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) :
    ansD (selectedView a) = ClaudeWCT.WCT9.encodingAnswer lay a := by
  by_cases hs : lowerSpare (ansD a)
  · rw [selectedView, if_pos hs, ClaudeWCT.WCT9.encodingAnswer_lower_low lay hlay a hs]
  · rw [selectedView, if_neg hs, ClaudeWCT.WCT9.encodingAnswer_lower_high lay hlay a hs]
    exact highView_extract a 0 128

/-- Path-aware lower encoding block (configuration (1)+(2)): the LOW half costs `bCy`, the HIGH half `bCy + 4`. -/
theorem encB_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t)
    (a : BitVec 256) :
    (canonicalDecode lay (ansD (selectedView a)) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        (fetch image v = none ∨ (fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1)) ∧ k ≤ 27 ∧ cy ≤ 30) ∧
    (canonicalDecode lay (ansD (selectedView a)) ≠ none → ∃ s0 k cy, Steps image (writeHash t a) k cy s0 ∧ k ≤ bSt lay.val+4 ∧
        cy + (if lowerSpare (ansD a) then 4 else 0) ≤ bCy lay.val+4 ∧
        (lctxOf w index lay (selectedView a)).ok ∧
        (∀ p ∈ (lctxOf w index lay (selectedView a)).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay (selectedView a)).Orig0 s0 ∧
        (lctxOf w index lay (selectedView a)).ChainIn s0 0 [] s0 ∧ Glob (chainK lay.val) w pk s0 ∧
        Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (lfS7 lay.val (route index lay).1) ∧
        s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2 ∧
        s0.getReg .x2 = BitVec.ofNat 64 0xffbde0 ∧
        Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) s0) := by
  by_cases hlo : lowerSpare (ansD a)
  · simp only [selectedView, if_pos hlo]
    have H := encB_step_low w pk index lay hlay c hc hidx t ht a hlo
    constructor
    · intro hn
      obtain ⟨v,k,cy,hst,hf,h5,h10,hk,hcy⟩ := H.1 hn
      exact ⟨v,k,cy,hst,Or.inr ⟨hf,h5,h10⟩,hk,hcy⟩
    · intro hn
      obtain ⟨s0,hst,hrest⟩ := H.2 hn
      exact ⟨s0,bSt lay.val,bCy lay.val,hst,by omega,by simp [hlo],hrest⟩
  · simp only [selectedView, if_neg hlo]
    by_cases hhi : lowerSpare (ansD (highView a))
    · have H := encB_step_hi w pk index lay hlay c hc hidx t ht a hlo hhi
      constructor
      · intro hn
        obtain ⟨v,k,cy,hst,hf,h5,h10,hk,hcy⟩ := H.1 hn
        exact ⟨v,k,cy,hst,Or.inr ⟨hf,h5,h10⟩,hk,hcy⟩
      · intro hn
        obtain ⟨s0,hst,hrest⟩ := H.2 hn
        exact ⟨s0,bSt lay.val+4,bCy lay.val+4,hst,le_refl _,by simp [hlo],hrest⟩
    · constructor
      · intro _
        obtain ⟨v,hst,hf⟩ := encB_step_trap w pk index lay hlay c hc t ht a hlo hhi
        exact ⟨v,8,8,hst,Or.inl hf,by omega,by omega⟩
      · intro hn
        exact (hn (by rw [canonical_decode_lower_v6 lay hlay,if_neg hhi])).elim

theorem Verify.GoodQP.fetch_none {P : Hash → Prop} {s : MachineState} {Q : Prop} {A : Nat}
    (hf : fetch image s = none) : GoodQP P s 1 0 Q A (pure (false,0)) := by
  intro F hF
  have he : F = (F-1)+1 := by omega
  refine ⟨?_,fun hash => ?_⟩
  · rw [he,execute_fetch_none (F-1) hf,map_pure]; rfl
  · have hx : evalWithAnswerFn hash (Riscv.execute (F-1+1) image s) = ⟨.failure,s,0,0,0⟩ := by
      rw [execute_fetch_none (F-1) hf]; rfl
    rw [he,hx]
    exact ⟨by simp,Nat.zero_le _,fun h _ => by simp at h⟩
end SigGolfCandidate.T3M
end
end
-- ==== merged from T3M_Verify_LeafSem ====
section

section


set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def keepLfAll (lay : Nat) : List Reg :=
  if lay = 0 then [.x1, .x2, .x7, .x13, .x19, .x20, .x12, .x21, .x16, .x17, .x8, .x9, .x24, .x22, .x23,
    .x25, .x26, .x28, .x29, .x31, .x30]
  else [.x1, .x2, .x13, .x19, .x20, .x12, .x21, .x16, .x17, .x8, .x9, .x24, .x22, .x23,
    .x6, .x26, .x29, .x31, .x30] ++ (if lay = 1 then [] else [.x25, .x28])
/-- Campaign T51: the 6 final tails at `Nonbinary.ckTail d` (after the checksum chain 50 with digit `d`): main's tail
without the `bne` (7 words ending in the leaf `jalr`). There is no tail reject: the checksum range was checked by the
checksum dispatch. -/
def fusedLeafCheck6 (d : Nat) : Bool :=
  specB (lfAllowed 0) [] (gkL 0) (runAt (leafK 0) [] (Nonbinary.ckTail d) [.jmp]) (specLf 0) [] (postLf 0) (keepLfAll 0)
theorem fusedLeafChecks6 : (List.range 6).all fusedLeafCheck6 = true := by decide +kernel
theorem fusedLeafCheck6_at (d : Nat) (hd : d < 6) : fusedLeafCheck6 d = true :=
  List.all_eq_true.mp fusedLeafChecks6 d (List.mem_range.mpr hd)
end SigGolfCandidate.T3M
end

section


section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3 OracleComp
theorem mapM_congr' {α β : Type} {f g : α → M β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h x (by simp), mapM_congr' l (fun y hy => h y (by simp [hy]))]
theorem finRange_mapM {β : Type} (n : Nat) (g : Nat → M β) :
    (List.finRange n).mapM (fun i => g i.val) = (List.range n).mapM g := by
  have e : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp
  rw [← e, List.mapM_map]; rfl
theorem foldlM_app_mapM (f : Nat → M Digest) : ∀ (n a : Nat) (acc : List Digest),
    (List.range' a n).foldlM (fun e i => do let v ← f i; pure (e ++ [v])) acc =
      (fun l => acc ++ l) <$> (List.range' a n).mapM f
  | 0, a, acc => by simp
  | n + 1, a, acc => by
    rw [List.range'_succ, List.foldlM_cons, List.mapM_cons]
    simp only [bind_assoc, pure_bind, foldlM_app_mapM f n (a + 1), map_bind, bind_map_left, map_pure]
    congr 1; funext v
    rw [← bind_pure_comp]
    congr 1; funext l; simp
namespace QCtx
theorem sum_range'_eq (f g : Nat → Nat) (a n : Nat) (h : ∀ i, a ≤ i → i < a + n → f i = g i) :
    ((List.range' a n).map f).sum = ((List.range' a n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have := List.mem_range'_1.mp hi
  exact h i this.1 this.2
end QCtx
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
theorem chainCount_lower (lay : Layer) (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem decode_lower_sum (lay : Layer) (hlay : lay ≠ 0) (value : Digest) (ds : List Nat)
    (h : decode lay value = some ds) : ds.length = 43 ∧ ds.sum = target lay := by
  unfold decode at h
  split at h
  · cases h
  · simp only [if_neg hlay] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      have hl : (dataDigits lay value).length = 42 := by simp [dataDigits, dataCount, hlay]
      refine ⟨by simp [hl], ?_⟩
      rw [List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · cases h
theorem sum_dig (c : LCtx) (D : List Nat) (hD : ∀ i < 43, c.dig i = D.getD i 0) (hl : D.length = 43) :
    ((List.range' 0 43).map c.dig).sum = D.sum := by
  have hE : D = (List.range' 0 43).map fun i => D.getD i 0 := by
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range']
    rw [show 0 + 1 * i = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  conv_rhs => rw [hE]
  exact QCtx.sum_range'_eq _ _ 0 43 (fun i _ hi => hD i (by omega))
end LCtx
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
theorem leafHash_eq (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = projHash (leafHalfHigh lay leaf) (T3.leafInput lay tree leaf ends) := rfl
def dw (e : Digest) : List (BitVec 64) := [e.extractLsb' 0 64, e.extractLsb' 64 64]
theorem flatMap_length16 : ∀ (L : List Digest), (L.flatMap (SphincsSecurity.bytesLE 16)).length = 16 * L.length
  | [] => rfl
  | e :: L => by
    rw [List.flatMap_cons, List.length_append, flatMap_length16 L, SphincsSecurity.bytesLE_length]; simp; ring
abbrev leafWord (lay : Layer) (tree leaf : Nat) : BitVec 64 := T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)
/-- C3: the verifier's leaf input (top pad and tweak high word from the witness). -/
abbrev lfIn (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (tree leaf : Nat) (ends : List Digest) : List UInt8 :=
  ClaudeWCT.WCT9.leafInputW lay tree leaf (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w lay) ends
/-- Campaign T51 ("endpad"): the top leaf has the lower shape `end_0 | tweak | end_1..end_50`. -/
theorem leafInput_top (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest) :
    ClaudeWCT.WCT9.leafInputW 0 tree leaf pad hi ends =
      SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++ SphincsSecurity.bytesLE 16 (hi ++ leafWord 0 tree leaf) ++
        (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16) := by
  unfold ClaudeWCT.WCT9.leafInputW ClaudeWCT.WCT9.leafTweakW; rw [if_pos rfl]
theorem leafInput_low (lay : Layer) (h : lay ≠ 0) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64)
    (ends : List Digest) :
    ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends =
      SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++ SphincsSecurity.bytesLE 16 (hi ++ leafWord lay tree leaf) ++
        (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16) := by
  simp only [ClaudeWCT.WCT9.leafInputW, ClaudeWCT.WCT9.leafTweakW, if_neg h]
theorem readWords_digs (t : MachineState) : ∀ (L : List Digest) (A : Nat),
    (∀ j < L.length, DigAt t (A + 16 * j) (L.getD j 0)) →
      t.readWords (BitVec.ofNat 64 A) (2 * L.length) = L.flatMap dw
  | [], _, _ => rfl
  | e :: L, A, h => by
    rw [List.length_cons, show 2 * (L.length + 1) = 2 + 2 * L.length by ring, readWords_add, readWords_two,
      show A + 8 * 2 = A + 16 by ring, readWords_digs t L (A + 16) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [show A + 16 * (j + 1) = A + 16 + 16 * j by ring, List.getD_cons_succ] at this),
      List.flatMap_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0.1, h0.2]; rfl
theorem getD_drop1 (L : List Digest) (j : Nat) : (L.drop 1).getD j 0 = L.getD (j + 1) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2; omega
theorem lowLeaf_hashInput (t : MachineState) (lay : Layer) (hlay : lay ≠ 0) (tree leaf : Nat) (pad : Digest)
    (hi : BitVec 64) (ends : List Digest)
    (off : Nat) (hoff : off % 16 = 0) (hbound : off + 1472 < 2 ^ 64)
    (hn : ends.length = 43) (h10 : t.getReg .x10 = BitVec.ofNat 64 (off + 768))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 704) (hS : ∀ j < 43, DigAt t (off + slotL j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 (off + 784)) = leafWord lay tree leaf)
    (hT1 : t.getMem (BitVec.ofNat 64 (off + 792)) = hi) :
    hashInput t = toQ (pad64 (ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends)) ∧
      (toQ (pad64 (ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends))).blocks = 11 := by
  have hl : (ClaudeWCT.WCT9.leafInputW lay tree leaf pad hi ends).length = 64 * (10 + 1) := by
    rw [leafInput_low lay hlay, List.length_append, List.length_append, flatMap_length16,
      SphincsSecurity.bytesLE_length, SphincsSecurity.bytesLE_length, List.length_drop, hn] <;> norm_num
  rw [pad64_of_aligned _ (by simp [hl])]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 10 (off + 768) hl h10 (by omega) (by omega) (by simpa using h11) (by omega)
  rw [leafInput_low lay hlay, wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]), Verify.wordsOf_append64, wordsOf_bytesLE16,
    wordsOf_flatMap16, show 8 * (10 + 1) = 2 + (2 + 2 * (ends.drop 1).length) by simp [hn],
    readWords_add, readWords_add, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotL 0 = 768 from rfl] at e0
  rw [show (off + 768) + 8 * 2 = (off + 784) by omega, show (off + 784) + 8 = (off + 792) by omega, show (off + 784) + 8 * 2 = (off + 800) by omega,
    e0.1, show (off + 768) + 8 = ((off + 768) : Nat) + 8 by omega, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) (off + 800) (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show off + slotL (j + 1) = (off + 800) + 16 * j by unfold slotL; simp; omega] at this)]
  rfl
/-- Campaign T51: the top leaf hash input (832 bytes, 13 blocks) read from `25216`: `end_0` at `slotT 0 = 25216`,
the tweak at 25232 / 25240, `end_j` at `slotT j = 25232 + 16 j` (`j >= 1`). -/
theorem topLeaf_hashInput (t : MachineState) (tree leaf : Nat) (pad : Digest) (hi : BitVec 64) (ends : List Digest)
    (hn : ends.length = 51) (h10 : t.getReg .x10 = BitVec.ofNat 64 25216)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 832) (hS : ∀ j < 51, DigAt t (slotT j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 25232) = leafWord 0 tree leaf)
    (hT1 : t.getMem (BitVec.ofNat 64 25240) = hi) :
    hashInput t = toQ (pad64 (ClaudeWCT.WCT9.leafInputW 0 tree leaf pad hi ends)) ∧
      (toQ (pad64 (ClaudeWCT.WCT9.leafInputW 0 tree leaf pad hi ends))).blocks = 13 := by
  have hl : (ClaudeWCT.WCT9.leafInputW 0 tree leaf pad hi ends).length = 64 * (12 + 1) := by
    rw [leafInput_top, List.length_append, List.length_append, flatMap_length16, SphincsSecurity.bytesLE_length,
      SphincsSecurity.bytesLE_length, List.length_drop, hn]
  have e0 := hS 0 (by omega)
  have hE0 : t.getMem (BitVec.ofNat 64 25216) = (ends.getD 0 0).extractLsb' 0 64 := e0.1
  have hE1 : t.getMem (BitVec.ofNat 64 25224) = (ends.getD 0 0).extractLsb' 64 64 := e0.2
  rw [pad64_of_aligned _ (by simp [hl])]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 12 25216 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [leafInput_top, wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]), Verify.wordsOf_append64, wordsOf_bytesLE16,
    wordsOf_flatMap16, show 8 * (12 + 1) = 2 + (2 + 2 * (ends.drop 1).length) by simp [hn],
    readWords_add, readWords_add, readWords_two, readWords_two]
  rw [show 25216 + 8 * 2 = 25232 by rfl, show 25232 + 8 = 25240 by rfl, show 25232 + 8 * 2 = 25248 by rfl,
    show 25216 + 8 = (25224 : Nat) by rfl, hE0, hE1, hT0, hT1,
    readWords_digs t (ends.drop 1) 25248 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotT (j + 1) = 25248 + 16 * j by unfold slotT; simp; omega] at this)]
  rfl
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
def lfBase (lay : Nat) : Nat := bufferBase lay
def lfBytes (lay : Nat) : Nat := if lay = 0 then 832 else 704
def lfBlocks (lay : Nat) : Nat := if lay = 0 then 13 else 11
def lfSlot (lay j : Nat) : Nat := if lay = 0 then slotT j else bufferBias lay + slotL j
def stabBits (lay : Nat) : Nat := if lay = 1 then 7 else 6
def lfKeepK (lay : Nat) : List (Reg × Word) :=
  [(.x9, 0x7fc00), (.x7, 1), (.x13, 2), (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6),
   (.x30, 7), (if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))),
   (.x2, BitVec.ofNat 64 0xffbde0)] ++
  (if lay = 0 then [] else [(.x1, BitVec.ofNat 64 M1c), (.x24, BitVec.ofNat 64 M2c), (.x6, 0x10000), (.x27, 0x3fe00)])
def lfK (lay : Nat) : List (Reg × Word) := postLf lay ++ lfKeepK lay
structure LeafOut (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest)
    (u : MachineState) : Prop where
  pc : u.pc = pcOf (stabW lay.val ((route index lay).1 % 2 ^ stabBits lay.val))
  glob : Glob (lfK lay.val) w pk u
  s7 : lay = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index lay).1)
  t5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2
  len : ends.length = chainCount lay
  ends : ∀ j < chainCount lay, DigAt u (lfSlot lay.val j) (ends.getD j 0)
  T0 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 16)) =
    T3.hyperWord lay.val ((route index lay).2 * 2 ^ height lay + (route index lay).1)
  /-- C3: the leaf tweak's high word is witness memory (`wleafHigh`). -/
  T1 : u.getMem (BitVec.ofNat 64 (lfBase lay.val + 24)) = ClaudeWCT.W9.T3M.wleafHigh w lay
  orig : Verify.Orig w (fun o => 7664 ≤ o ∧
    o < ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay) u
  bufferOrig : lay ≠ 0 → Verify.Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 21984) u
theorem LeafOut.hashInput {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {index : Nat} {lay : Layer} {ends : List Digest}
    {u : MachineState} (h : LeafOut w pk index lay ends u) :
    hashInput u = toQ (pad64 (lfIn w lay (route index lay).2 (route index lay).1 ends)) ∧
      (toQ (pad64 (lfIn w lay (route index lay).2 (route index lay).1 ends))).blocks = lfBlocks lay.val := by
  have h10 := h.glob.1 (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11 := h.glob.1 (.x11, BitVec.ofNat 64 (lfBytes lay.val)) (by simp [lfK, postLf, lfBytes])
  have hT0 := h.T0
  have hT1 := h.T1
  have hS := h.ends
  have hn := h.len
  by_cases h0 : lay = 0
  · subst h0
    exact topLeaf_hashInput u _ _ _ _ ends hn h10 h11 hS hT0 hT1
  · have hc := LCtx.chainCount_lower lay h0
    have hv : lay.val ≠ 0 := fun hv => h0 (Fin.ext hv)
    simp only [lfBase, lfBytes, lfSlot, lfBlocks, if_neg hv] at h10 h11 hT0 hT1 hS ⊢
    rw [hc] at hn hS
    have hb : bufferBase lay.val = bufferBias lay.val + 768 := by
      fin_cases lay <;> first | exact absurd rfl h0 | rfl
    have hm : bufferBias lay.val % 16 = 0 := by fin_cases lay <;> decide +kernel
    have hbd : bufferBias lay.val + 1472 < 2 ^ 64 := by fin_cases lay <;> decide +kernel
    rw [hb] at h10 hT0 hT1
    exact lowLeaf_hashInput u lay h0 _ _ _ _ ends (bufferBias lay.val) hm hbd hn h10 h11 hS hT0 hT1
theorem glob_frame {gk gk' : List (Reg × Word)} {w : ClaudeWCT.W9.T3M.WBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (hG : Glob gk w pk s) (hf : Frame s t W)
    (hW : ∀ A, W A → 544 ≤ A ∧ (A < 0x1020 ∨ 0x1060 ≤ A) ∧ A < 2 ^ 23) (hk : ∀ p ∈ gk', t.getReg p.1 = p.2) :
    Glob gk' w pk t := by
  obtain ⟨-, hH, hP, hZ, hh, hD⟩ := hG
  have hn : ∀ A, A < 544 → ¬ W A := fun A hA h => by have := hW A h; omega
  refine ⟨hk, fun j hj4 hj => ?_, ⟨?_, ?_⟩, fun a ha => ?_, ?_, ?_⟩
  · rw [hf.get (by unfold WIT; omega) (fun h => by have := hW _ h; unfold WIT at this; omega)]; exact hH j hj4 hj
  · exact (hf.get (A := 0xA0) (by norm_num) (hn _ (by norm_num))).trans hP.1
  · exact (hf.get (A := 0xA8) (by norm_num) (hn _ (by norm_num))).trans hP.2
  · have ha' : a < 544 := by simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
    rw [hf.get (by omega) (hn _ ha')]; exact hZ a ha
  · unfold PHalf CTRW at *; rw [hf.get (by norm_num) (hn _ (by norm_num))]; exact hh
  · exact hD.congr (fun A hA hB => hf.get (by omega) (fun hw => by
      have := hW A hw
      unfold Verify.TAB at hA
      omega))
theorem land4 (n k : Nat) : n &&& (4 * (2 ^ k - 1)) = 4 * (n / 4 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (4 : Nat) = 2 ^ 2 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h2 : 2 ≤ j
  · simp only [h2, decide_true, Bool.true_and, show j - 2 + 2 = j by omega]
    by_cases hj : j - 2 < k
    · simp [hj]
    · simp [hj]
  · simp [h2]
theorem stabMask_eq (lay : Nat) : stabMask lay = 4 * (2 ^ stabBits lay - 1) := by
  unfold stabMask stabBits; split <;> rfl
theorem tgtLf0_eval (t : MachineState) (leaf : Nat) (hl : leaf < 4096)
    (h31 : t.getReg .x31 = BitVec.ofNat 64 leaf) :
    (tgtLf 0).eval t = pcOf (stabW 0 (leaf % 2 ^ stabBits 0)) := by
  change ((((t.getReg .x31 &&& BitVec.ofNat 64 63) + BitVec.ofNat 64 1117) <<< ((BitVec.ofNat 64 9).toNat % 64)) +
      BitVec.ofNat 64 320) &&& ~~~(1#64) = BitVec.ofNat 64 (0x1000 + 4 * (142032 + 128 * (leaf % 64)))
  have hm : (t.getReg .x31 &&& BitVec.ofNat 64 63) = BitVec.ofNat 64 (leaf % 64) := by
    rw [h31]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_andc _ 63 (by norm_num), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hmod : leaf % 2 ^ 64 = leaf := Nat.mod_eq_of_lt (by omega)
    rw [hmod, show (63 : Nat) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hm, ofNat_add_ofNat]
  have hs : (BitVec.ofNat 64 (leaf % 64 + 1117) <<< ((BitVec.ofNat 64 9).toNat % 64)) + BitVec.ofNat 64 320 =
      BitVec.ofNat 64 (0x1000 + 4 * (142032 + 128 * (leaf % 64))) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, toNat_sll _ 9 (by norm_num), BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hs, even_andNot1' _ (by omega)]
theorem stabBits_le (lay : Layer) : stabBits lay.val ≤ hL lay.val := by fin_cases lay <;> decide +kernel
theorem stabIdx_lt (lay : Nat) : stabIdx lay < 2 ^ 32 := by
  unfold stabIdx
  rcases lay with _ | _ | _ | _ | n <;> simp
/-- Campaign T51: the state at a final tail `ckTail d` (after chain 50), ready for the top leaf hash. -/
structure TopLeafReady (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (ends : List Digest)
    (t : MachineState) : Prop where
  pc : ∃ d, d < 6 ∧ t.pc = pcOf (Nonbinary.ckTail d)
  glob : Glob (leafK 0) w pk t
  keep : KnownOK (lfKeepK 0) t
  s7 : t.getReg .x23 = BitVec.ofNat 64 (dispatchHeap 0 (route index 0).1)
  t5 : t.getReg .x31 = BitVec.ofNat 64 (route index 0).1
  word : t.getReg .x28 = leafWord 0 (route index 0).2 (route index 0).1
  len : ends.length = 51
  ends : ∀ j < 51, DigAt t (slotT j) (ends.getD j 0)
  orig : Verify.Orig w (fun o => 7664 ≤ o ∧
    o < ClaudeWCT.W9.T3M.layerBase 0 + 16 * ClaudeWCT.W9.T3M.pathSlots 0) t
  /-- C3: the top leaf tweak's high word is witness memory. -/
  topHi : t.getMem (BitVec.ofNat 64 25240) = ClaudeWCT.W9.T3M.wleafHigh w 0
theorem lfKeepK_keep : (lfKeepK 0).all (fun p => decide (p.1 ∈ keepLfAll 0)) = true := by decide +kernel
/-- Campaign T51: the final tail (7 steps, no sum check) stores the leaf label and jumps to the top merkle entry. -/
theorem leafT_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (ends : List Digest) (t : MachineState) (ht : TopLeafReady w pk index c ends t) :
    ∃ u, Steps image t 7 7 u ∧ LeafOut w pk index 0 ends u := by
  obtain ⟨d, hd, hp⟩ := ht.pc
  obtain ⟨u, hu⟩ := spec_run (fusedLeafCheck6_at d hd) t hp ht.glob.1 (by simp [specLf]) (by simp)
  have hst := hu.steps
  rw [show (specLf 0).steps = 7 from rfl, show (specLf 0).cycles = 7 from rfl] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf 0) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 25232⟩, .reg .x28)] A := by
    intro A; rw [hu.mem]; simp [specLf, bufferBase]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ 25232 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    simp
    omega
  have hlf := leaf_lt index 0
  refine ⟨?_, ?_, ?_, ?_, ht.len, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.spc (tgtLf 0) (by simp [specLf])]
    exact tgtLf0_eval t _ hlf ht.t5
  · have hGu := hu.glob _ w pk ht.glob (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have hkp : p.1 ∈ keepLfAll 0 := by
        have := List.all_eq_true.mp lfKeepK_keep p hp
        simpa using this
      rw [hkeep _ hkp]
      exact ht.keep p hp
  · intro _
    rw [hkeep .x23 (by simp [keepLfAll]), ht.s7]
  · intro h; exact absurd rfl h
  · intro j hj
    have hj' : j < 51 := hj
    have e := ht.ends j hj'
    simp only [lfSlot, if_pos rfl]
    have hsl : (slotT j = 25216 ∨ 25248 ≤ slotT j) ∧ slotT j ≤ 26032 := by unfold slotT; split_ifs <;> omega
    exact ⟨(hfr (slotT j) (by omega) (by omega)).trans e.1,
      (hfr (slotT j + 8) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase (0 : Layer).val + 16 = 25232 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
    simp only [E.eval]
    exact ht.word
  · rw [show lfBase (0 : Layer).val + 24 = 25240 from rfl, hfr 25240 (by norm_num) (by norm_num)]
    exact ht.topHi
  · exact (hu.orig_const ht.orig).mono (fun o ho => ⟨ho, by
      have hhi : o < 8336 := ho.2
      simp only [lfAllowed, bufferBase, List.getD_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      unfold WIT
      constructor <;> omega⟩)
  · intro h; exact (h rfl).elim
end SigGolfCandidate.T3M
end
end

namespace SigGolfCandidate.T3M.LCtx
open SigGolfCandidate.T3
theorem canonical_decode_lower_sum (lay : Layer) (hlay : lay ≠ 0) (value : Digest) (ds : List Nat)
    (h : canonicalDecode lay value = some ds) : ds.length = 43 ∧ ds.sum = canonicalTarget lay := by
  have hd : decode (1 : Layer) value = some ds := by
    simpa only [canonicalDecode, ClaudeWCT.WCT9.CanonicalPolicy.decode,
      ClaudeWCT.WCT9.CanonicalPolicy.normalLayer, if_neg hlay] using h
  simpa only [canonicalTarget, ClaudeWCT.WCT9.CanonicalPolicy.normalLayer, if_neg hlay] using
    decode_lower_sum (1 : Layer) (by decide) value ds hd
end SigGolfCandidate.T3M.LCtx
end
-- ==== merged from T3M_Verify_TopSource ====
section

namespace SigGolfCandidate.T3M.TopSource
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.WCT9 (topRejectLength topGroupBad topRejectChains topGroupValid topChecksumOk)
theorem chainCount0 : chainCount 0=51 := rfl
theorem length_finRange0 : (List.finRange (chainCount 0)).length=51 := by simp [chainCount0]
/-- Campaign T51: a group is checked at its first chain (r6 groups g0..g8 at chains 0..24, r5 groups q9..q15 at
27..45, the r7 pair at 48), the checksum before chain 50. -/
theorem topGroupBad_iff (a : Digest) (i : Nat) :
    topGroupBad a i=true ↔
      ((i%3=0 ∧ i<50 ∧ topGroupValid a (i/3)=false) ∨ (i=50 ∧ topChecksumOk a=false)) := by
  unfold topGroupBad
  simp only [Bool.or_eq_true, decide_eq_true_eq]

/-- Campaign T51 (no spare bit): the verifier runs exactly the chains before the first bad position. -/
theorem topRejectLength_bad (a : Digest) (j : Nat) (hj : j<51)
    (hgood : ∀ i, i<j → topGroupBad a i=false) (hbad : topGroupBad a j=true) :
    topRejectLength a=j := by
  have hv := a.isLt
  unfold topRejectLength
  rw [if_neg (by simp [encodedBits]; omega)]
  rw [List.findIdx_eq (by rw [length_finRange0]; omega)]
  refine ⟨?_,fun k hk => ?_⟩
  · simpa only [List.getElem_finRange,Fin.cast_mk] using hbad
  · simpa only [List.getElem_finRange,Fin.cast_mk] using hgood k hk

theorem take_mapM {β : Type} (g : Nat → M β) (m : Nat) (hm : m ≤ 51) :
    ((List.finRange (chainCount 0)).take m).mapM (fun i => g i.val)=(List.range' 0 m).mapM g := by
  have e : ((List.finRange (chainCount 0)).take m).map Fin.val=List.range' 0 m := by
    apply List.ext_getElem
    · simp [chainCount0]; omega
    · intro k h1 h2; simp
  rw [← e, List.mapM_map]; rfl

end SigGolfCandidate.T3M.TopSource
end
-- ==== merged from T3M_Verify_Nonbinary_LayerContext ====
section

set_option Elab.async false

-- Top-half selection (formerly Nonbinary/TopSelect.lean, folded here for the 1000-entry limit).
section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem byte7_ult (lo : BitVec 128) :
    BitVec.ult ((extractByte (lo.extractLsb' 64 64) 7).zeroExtend 64) 64#64 = decide (T3.TopChoice.blocked lo) := by
  have hl := lo.isLt
  unfold T3.TopChoice.blocked extractByte
  simp only [BitVec.ult, BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have h1 : lo.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact hl
  rw [Nat.mod_eq_of_lt h1, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h2 : lo.toNat / 2 ^ (64 + 7 * 8) < 2 ^ 8 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact hl
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (lt_trans h2 (by norm_num))]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  norm_num
theorem lb_ge_zero (b : BitVec 8) :
    (!BitVec.slt (b.signExtend 64) (0 : BitVec 64)) = !b.getLsbD 7 := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_signExtend]
  simp [BitVec.msb_eq_getLsbD_last]

end SigGolfCandidate.T3M.Verify.Nonbinary
end


section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
/-- Campaign T51: the dispatch jump of the head lands on `g0Target V`. -/
theorem g0_jump (V : Digest) :
    ((((V.extractLsb' 0 64) <<< ((56#64 : Word).toNat % 64)) >>> ((45#64 : Word).toNat % 64)) +
      18446744073709550872#64) &&& 18446744073709551614#64 = g0Target V := by
  have e1 : (56#64 : Word).toNat % 64 = 56 := rfl
  have e2 : (45#64 : Word).toNat % 64 = 45 := rfl
  have e3 : (18446744073709550872#64 : Word) = BitVec.ofNat 64 (2^64-744) := rfl
  have e4 : (18446744073709551614#64 : Word) = ~~~1#64 := by decide
  rw [e1, e2, e3, e4]; rfl
/-- One 6-word dispatch block of the d6b head (`hi`: the HIGH block at `a2+16`; T51: 5 instructions run, the
trailing `nop` is never reached). -/
theorem prefix_end_spec (s : MachineState) (hi : Bool) (half : Digest) (d q : Nat)
    (hpc : s.pc = pcOf q) (hcode : CodeAt Verify.image (pcOf q) (if hi then dHigh else dLow))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d) (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (hh : DigAt s (d + (if hi then 16 else 0)) half) :
    ∃ t, Steps Verify.image s 5 5 t ∧ t.pc = g0Target half ∧
      t.getReg .x16 = half.extractLsb' 0 64 ∧ t.getReg .x17 = half.extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17,.x14] ∧ Frame s t (fun _ => False) := by
  cases hi with
  | false =>
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hcode hh
    have m0 : s.getMem (s.getReg .x12) = half.extractLsb' 0 64 := by rw [h12]; exact hh.1
    have m8 : s.getMem (s.getReg .x12 + 8#64) = half.extractLsb' 64 64 := by
      rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hh.2
    have es := symRun_sound (dLow_run (pcOf q)) hcode s hpc (by
      simp [dLowBase.res, rv_simp, h12, accessValid_iff, MEMORY_BYTES]; omega)
    refine ⟨_, es, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, dLowBase.res, E.eval, BinOp.eval, m0]
      exact g0_jump half
    · simp only [Result.toState_getReg, dLowBase.res, RegFile.get, E.eval, m0]
    · simpa only [Result.toState_getReg, dLowBase.res, RegFile.get, E.eval, BinOp.eval] using m8
    · intro r hr; cases r <;> simp at hr <;> simp [dLowBase.res, rv_simp] <;> rfl
    · intro A _ _; simp [dLowBase.res, rv_simp]
  | true =>
    simp only [if_true] at hcode hh
    have m0 : s.getMem (s.getReg .x12 + 16#64) = half.extractLsb' 0 64 := by
      rw [h12, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; exact hh.1
    have m8 : s.getMem (s.getReg .x12 + 24#64) = half.extractLsb' 64 64 := by
      rw [h12, show (24#64 : Word) = BitVec.ofNat 64 24 from rfl, ofNat_add_ofNat]
      simpa [Nat.add_assoc] using hh.2
    have es := symRun_sound (dHigh_run (pcOf q)) hcode s hpc (by
      simp [dHighBase.res, rv_simp, h12, accessValid_iff, MEMORY_BYTES]; omega)
    refine ⟨_, es, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, dHighBase.res, E.eval, BinOp.eval, m0]
      exact g0_jump half
    · simpa only [Result.toState_getReg, dHighBase.res, RegFile.get, E.eval, BinOp.eval] using m0
    · simpa only [Result.toState_getReg, dHighBase.res, RegFile.get, E.eval, BinOp.eval] using m8
    · intro r hr; cases r <;> simp at hr <;> simp [dHighBase.res, rv_simp] <;> rfl
    · intro A _ _; simp [dHighBase.res, rv_simp]
/-- Exact cycle cost of the d6b selector before its 6-word dispatch block: hint clear 4, hint set 6 (HIGH, or LOW
forced). -/
def selCost (high : Bool) (_a : BitVec 256) : Nat := if high then 6 else 4
def selMax : Nat := 6
theorem selCost_le (high : Bool) (a : BitVec 256) : selCost high a ≤ selMax := by
  unfold selCost selMax; split_ifs <;> omega
/-- The whole d6b top head (18 words at `h+6`): loads the verifier-read half `TopChoice.read high a` into a6/a7
and dispatches to its first digit group (T51: the g0 cell), in exactly `selCost high a + 5` cycles. -/
theorem prefix_head_spec (s : MachineState) (a : BitVec 256) (high : Bool) (ra d p : Nat) (hra : ra ∈ aVals)
    (hpc : s.pc = pcOf p) (hc : CodeAt Verify.image (pcOf p) (prefixWordsOf ra))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d) (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (h11 : s.getReg .x11 = 64#64) (h4 : s.getReg .x4 = 24704#64)
    (h9 : s.getReg .x2 = BitVec.ofNat 64 0xffbde0) (hmask : s.getMem 0xffbff8#64 = 520192#64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 ra)
    (hhint : (extractByte (s.getMem 25232#64) 0).getLsbD selHintBit = high)
    (hlo : DigAt s d (a.extractLsb' 0 128))
    (hhi : DigAt s (d+16) (a.extractLsb' 128 128)) :
    ∃ t, Steps Verify.image s (selCost high a + 5) (selCost high a + 5) t ∧
      t.pc = g0Target (T3.TopChoice.read high a) ∧
      t.getReg .x16 = (T3.TopChoice.read high a).extractLsb' 0 64 ∧
      t.getReg .x17 = (T3.TopChoice.read high a).extractLsb' 64 64 ∧
      t.getReg .x8 = 14128#64 ∧ t.getReg .x6 = 520192#64 ∧
      RegsExcept s t [.x16,.x17,.x6,.x8,.x14,.x3] ∧ Frame s t (fun _ => False) := by
  have hsub : ∀ (pre seg post : List (BitVec 32)), prefixWordsOf ra = pre ++ seg ++ post →
      CodeAt Verify.image (pcOf (p + pre.length)) seg := by
    intro pre seg post he
    have h := hc
    rw [he] at h
    have h' := CodeAt.drop_prefix (pre := pre) (seg := seg) (post := post) h
    rwa [pcOf, ofNat_add_ofNat, show 0x1000 + 4 * p + 4 * pre.length = 0x1000 + 4 * (p + pre.length) by ring] at h'
  have hc0 : CodeAt Verify.image (pcOf p) (dProWordsOf ra) := by
    simpa using hsub [] (dProWordsOf ra) (dHint ++ dHead ++ dLow ++ dHigh) (by simp [prefixWordsOf])
  have hc2 : CodeAt Verify.image (pcOf (p+2)) dHint := by
    simpa [dProWordsOf] using hsub (dProWordsOf ra) dHint (dHead ++ dLow ++ dHigh) (by simp [prefixWordsOf])
  have hc4 : CodeAt Verify.image (pcOf (p+4)) dHead := by
    simpa [dProWordsOf, dHint] using hsub (dProWordsOf ra ++ dHint) dHead (dLow ++ dHigh) (by simp [prefixWordsOf])
  have hc6 : CodeAt Verify.image (pcOf (p+6)) dLow := by
    simpa [dProWordsOf, dHint, dHead] using
      hsub (dProWordsOf ra ++ dHint ++ dHead) dLow dHigh (by simp [prefixWordsOf])
  have hc12 : CodeAt Verify.image (pcOf (p+12)) dHigh := by
    simpa [dProWordsOf, dHint, dHead, dLow] using
      hsub (dProWordsOf ra ++ dHint ++ dHead ++ dLow) dHigh [] (by simp [prefixWordsOf])
  have hhint : (extractByte (s.getMem 25232#64) 0).getLsbD 7 = high := hhint
  have hal : 15336 ≤ ra ∧ ra ≤ 15528 := by
    simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at hra; omega
  -- `ld t1,232(s1); addi s0,a0,K`
  have hm : s.getMem (s.getReg .x2 + 536#64) = 520192#64 := by rw [h9]; exact hmask
  have e0 := symRun_sound (dPro_run ra hra (pcOf p)) hc0 s hpc (by
    simp [dProRes, dProRegs, dProBase.res, rv_simp, h9, accessValid_iff, MEMORY_BYTES])
  let u := (dProRes ra (pcOf p)).toState s
  have ru : RegsExcept s u [.x6,.x8] := by
    intro r hr; cases r <;> simp at hr <;> simp [u, dProRes, dProRegs, dProBase.res, rv_simp] <;> rfl
  have fu : Frame s u (fun _ => False) := by
    intro A _ _; simp [u, dProRes, dProRegs, dProBase.res, rv_simp]
  have pu : u.pc = pcOf (p+2) := by
    simp [u, dProRes, rv_simp, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  have u6 : u.getReg .x6 = 520192#64 := by
    simp only [u, Result.toState_getReg, dProRes, dProRegs, dProBase.res, RegFile.get, RegFile.set, E.eval]
    exact hm
  have u8 : u.getReg .x8 = 14128#64 := by
    simp only [u, Result.toState_getReg, dProRes, dProRegs, RegFile.get, RegFile.set, E.eval, BinOp.eval, h10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h12u : u.getReg .x12 = BitVec.ofNat 64 d := (ru.get (by decide)).trans h12
  have h4u : u.getReg .x4 = 24704#64 := (ru.get (by decide)).trans h4
  have hmemu : u.getMem 25232#64 = s.getMem 25232#64 := fu.get (A := 25232) (by omega) (by simp)
  -- `lb gp,528(tp); bge gp,zero,LOW`
  have e1 := symRun_sound (dHint_run (pcOf (p+2))) hc2 u pu (by
    simp [dHintRes, dHintBase.res, rv_simp, h4u, accessValid_iff, MEMORY_BYTES])
  let v := (dHintRes (pcOf (p+2))).toState u
  have rv : RegsExcept u v [.x3] := by
    intro r hr; cases r <;> simp_all [v, dHintRes, dHintBase.res, rv_simp] <;> rfl
  have fv : Frame u v (fun _ => False) := by
    intro A _ _; simp [v, dHintRes, dHintBase.res, rv_simp]
  have hhb : hintByte.eval u = (extractByte (s.getMem 25232#64) 0).signExtend 64 := by
    simp only [hintByte, E.eval, UnOp.eval, LoadKind.fromWord, BinOp.eval]
    rw [show (u.getReg Reg.x4 + 528) = 25232#64 by rw [h4u]; rfl, hmemu]
  have hcmp : CmpOp.ge.eval (hintByte.eval u) ((E.c 0).eval u) = !high := by
    simp only [CmpOp.eval, E.eval]; rw [hhb, lb_ge_zero, hhint]
  have pv : v.pc = if high then pcOf (p+4) else pcOf (p+6) := by
    simp only [v, Result.toState_pc, dHintRes]
    simp only [E.eval] at hcmp ⊢
    simp only [hcmp]
    cases high
    · simp [pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
    · simp [pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  have h12v : v.getReg .x12 = BitVec.ofNat 64 d := (rv.get (by decide)).trans h12u
  have h6v : v.getReg .x6 = 520192#64 := (rv.get (by decide)).trans u6
  have h8v : v.getReg .x8 = 14128#64 := (rv.get (by decide)).trans u8
  have fsv : Frame s v (fun _ => False) := (fu.trans fv).mono (by simp)
  have dig : ∀ (x : MachineState) (o : Nat) (half : BitVec 128), Frame s x (fun _ => False) → DigAt s (d+o) half →
      o ≤ 16 → DigAt x (d+o) half := fun x o half hf hh ho =>
    hh.frame hf (by omega) (by simp) (by simp)
  cases high with
  | false =>
    rw [if_neg (by simp)] at pv
    obtain ⟨t, et, pt, t16, t17, rt, ft⟩ := prefix_end_spec v false (a.extractLsb' 0 128) d (p+6) pv
      (by simpa using hc6) h12v hd (by simpa using dig v 0 _ fsv (by simpa using hlo) (by omega))
    have hr : T3.TopChoice.read false a = a.extractLsb' 0 128 := T3.TopChoice.read_false a
    refine ⟨t, by rw [show selCost false a + 5 = 2 + 2 + 5 from rfl]; exact (e0.trans e1).trans et,
      by rw [pt, hr], by rw [t16, hr], by rw [t17, hr],
      by rw [rt.get (by decide), h8v], by rw [rt.get (by decide), h6v],
      ((ru.trans rv).trans rt).mono (by decide), ((fu.trans fv).trans ft).mono (by simp)⟩
  | true =>
    rw [if_pos rfl] at pv
    -- `lbu gp,15(a2); bgeu gp,a1,HIGH`
    have hlo1 : v.getMem (v.getReg .x12 + 8#64) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
      rw [h12v, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat, fsv.get (by omega) (by simp), hlo.2]
    have e2 := symRun_sound (dHead_run (pcOf (p+4))) hc4 v pv (by
      simp [dHeadRes, dHeadBase.res, rv_simp, h12v, accessValid_iff, MEMORY_BYTES]; omega)
    let w := (dHeadRes (pcOf (p+4))).toState v
    have rw' : RegsExcept v w [.x3] := by
      intro r hr; cases r <;> simp_all [w, dHeadRes, dHeadBase.res, rv_simp] <;> rfl
    have fw : Frame v w (fun _ => False) := by
      intro A _ _; simp [w, dHeadRes, dHeadBase.res, rv_simp]
    have hb : headByte.eval v = (extractByte ((a.extractLsb' 0 128).extractLsb' 64 64) 7).zeroExtend 64 := by
      simp only [headByte, E.eval, UnOp.eval, LoadKind.fromWord, BinOp.eval]
      rw [show (v.getReg Reg.x12 + 8) = v.getReg .x12 + 8#64 from rfl, hlo1]
    have h11v : v.getReg .x11 = 64#64 := (rv.get (by decide)).trans ((ru.get (by decide)).trans h11)
    have hcmp : CmpOp.geu.eval (headByte.eval v) ((E.reg .x11).eval v) =
        !decide (T3.TopChoice.blocked (a.extractLsb' 0 128)) := by
      simp only [CmpOp.eval, E.eval]; rw [hb, h11v, byte7_ult]
    have pw : w.pc = if T3.TopChoice.blocked (a.extractLsb' 0 128) then pcOf (p+6) else pcOf (p+12) := by
      simp only [w, Result.toState_pc, dHeadRes]
      simp only [E.eval] at hcmp ⊢
      simp only [hcmp]
      by_cases hbl : T3.TopChoice.blocked (a.extractLsb' 0 128)
      · simp [hbl, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
      · simp [hbl, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
    have h12w : w.getReg .x12 = BitVec.ofNat 64 d := (rw'.get (by decide)).trans h12v
    have h6w : w.getReg .x6 = 520192#64 := (rw'.get (by decide)).trans h6v
    have h8w : w.getReg .x8 = 14128#64 := (rw'.get (by decide)).trans h8v
    have fsw : Frame s w (fun _ => False) := (fsv.trans fw).mono (by simp)
    by_cases hbl : T3.TopChoice.blocked (a.extractLsb' 0 128)
    · rw [if_pos hbl] at pw
      obtain ⟨t, et, pt, t16, t17, rt, ft⟩ := prefix_end_spec w false (a.extractLsb' 0 128) d (p+6) pw
        (by simpa using hc6) h12w hd (by simpa using dig w 0 _ fsw (by simpa using hlo) (by omega))
      have hr : T3.TopChoice.read true a = a.extractLsb' 0 128 := T3.TopChoice.read_blocked true hbl
      refine ⟨t, by rw [show selCost true a + 5 = 2 + 2 + 2 + 5 from rfl]; exact ((e0.trans e1).trans e2).trans et,
        by rw [pt, hr], by rw [t16, hr], by rw [t17, hr],
        by rw [rt.get (by decide), h8w], by rw [rt.get (by decide), h6w],
        (((ru.trans rv).trans rw').trans rt).mono (by decide), (((fu.trans fv).trans fw).trans ft).mono (by simp)⟩
    · rw [if_neg hbl] at pw
      obtain ⟨t, et, pt, t16, t17, rt, ft⟩ := prefix_end_spec w true (a.extractLsb' 128 128) d (p+12) pw
        (by simpa using hc12) h12w hd (by simpa using dig w 16 _ fsw hhi (by omega))
      have hr : T3.TopChoice.read true a = a.extractLsb' 128 128 := by
        simp [T3.TopChoice.read, T3.TopChoice.lowHalf, T3.TopChoice.highHalf, hbl]
      refine ⟨t, by rw [show selCost true a + 5 = 2 + 2 + 2 + 5 from rfl]; exact ((e0.trans e1).trans e2).trans et,
        by rw [pt, hr], by rw [t16, hr], by rw [t17, hr],
        by rw [rt.get (by decide), h8w], by rw [rt.get (by decide), h6w],
        (((ru.trans rv).trans rw').trans rt).mono (by decide), (((fu.trans fv).trans fw).trans ft).mono (by simp)⟩
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
def rejectJumpCode : List (BitVec 32) := [0xea8fa06f]
sym_block rejectJumpBase := symRun { noAlias := true } rejectJumpCode (pcOf 9147) 20
theorem rejectJump_at : CodeAt Verify.image (pcOf 9147) rejectJumpCode := by
  have h := codeAt_from 9147 (by decide +kernel)
  have hp : rejectJumpCode <+: codeFrom 9147 := by decide +kernel
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
def rejectExitCode : List (BitVec 32) := [1049235,1049875]
sym_block rejectExitBase := symRun { noAlias := true } rejectExitCode (pcOf 3429) 20
theorem rejectExit_at : CodeAt Verify.image (pcOf 3429) rejectExitCode := by
  have h := codeAt_from 3429 (by decide +kernel)
  have hp : rejectExitCode <+: codeFrom 3429 := by decide +kernel
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 9147) :
    ∃ t, Steps Verify.image s 3 3 t ∧ fetch Verify.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase rejectJump_at s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 3429 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase rejectExit_at (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt Verify.image (pcOf 3431) [0x00000073] := by
      have h := codeAt_from 3431 (by decide +kernel)
      have hp : [0x00000073] <+: codeFrom 3431 := by decide +kernel
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
    exact h.fetch _ (by simp [rejectExitBase.res, rv_simp, pcOf])
  · simp [rejectExitBase.res, rv_simp]
  · simp [rejectExitBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- Configuration (1)+(2): the selector also writes `gp` (x3) and `a2` (x12); both are dead after the head. -/
def topEntryRegs : List Reg := [.x16,.x17,.x29,.x6,.x8,.x14,.x3,.x12]
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  /-- Campaign T51: the head's dispatch target (the g0 cell of the low byte of `v`). -/
  pc : s.pc = Nonbinary.g0Target v
  ra : s.getReg .x2 = BitVec.ofNat 64 0xffbde0
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = v.extractLsb' 64 64
  s3 : s.getReg .x8 = 14128#64
  mask : s.getReg .x6 = 520192#64
  table : s.getReg .x9 = 0x7fc00#64
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun A => A = 25160)
def topRowA (c : Nat) : Nat := rowA 0 c
theorem prefix_slots : (List.range 128).all (fun c => decide (topRowA c ∈ Nonbinary.aVals) &&
    (Nonbinary.prefixWordsOf (topRowA c)).isPrefixOf (codeFrom (trPc 0 c + 6))) = true := by
  decide +kernel

theorem topRowA_mem (c : Nat) (hc : c < 128) : topRowA c ∈ Nonbinary.aVals := by
  have h := List.all_eq_true.mp prefix_slots c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1
theorem prefix_at (c : Nat) (hc : c < 128) :
    CodeAt image (pcOf (trPc 0 c + 6)) (Nonbinary.prefixWordsOf (topRowA c)) := by
  have hp := trPc_lt 0 c
  have h := codeAt_from (trPc 0 c + 6) (by omega)
  have h2 := List.all_eq_true.mp prefix_slots c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  have hpre : Nonbinary.prefixWordsOf (topRowA c) <+: codeFrom (trPc 0 c + 6) :=
    List.isPrefixOf_iff_prefix.mp h2.2
  refine ⟨?_, ?_, ?_, hpre.trans h.2.2.2⟩
  · unfold pcOf; simp only [BitVec.toNat_ofNat]; omega
  · unfold pcOf; simp only [BitVec.toNat_ofNat]; omega
  · unfold pcOf
    simp only [BitVec.toNat_ofNat, Nonbinary.prefixWordsOf, List.length_append,
      Nonbinary.dProWordsOf, Nonbinary.dHint, Nonbinary.dHead, Nonbinary.dLow, Nonbinary.dHigh,
      List.length_cons, List.length_nil]
    omega
theorem prefix_sub_at (c : Nat) (hc : c < 128) (pre seg post : List (BitVec 32))
    (he : Nonbinary.prefixWordsOf (topRowA c) = pre ++ seg ++ post) :
    CodeAt image (pcOf (trPc 0 c + 6 + pre.length)) seg := by
  have h := prefix_at c hc
  rw [he] at h
  have h' := CodeAt.drop_prefix (pre := pre) (seg := seg) (post := post) h
  rwa [pcOf, ofNat_add_ofNat,
    show 0x1000 + 4 * (trPc 0 c + 6) + 4 * pre.length =
      0x1000 + 4 * (trPc 0 c + 6 + pre.length) by ring] at h'
/-- The witness choice byte (rel 21104, abs 25232) is the low byte of its witness word. -/
theorem extractByte_wword_choice (w : ClaudeWCT.W9.T3M.WBytes) :
    extractByte (wword w (ClaudeWCT.W9.T3M.choiceOff / 8)) 0 = ClaudeWCT.W9.T3M.wchoice w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, wword, ClaudeWCT.W9.T3M.wchoice, ClaudeWCT.W9.T3M.choiceOff, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', Nat.zero_mul, Nat.zero_add]
  simp [hi, show i < 64 by omega]
theorem topTransition (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : BC.EncPre w pk index 0 c t) (a : BitVec 256) :
    ∃ n s, Steps image (writeHash t a) n n s ∧ n ≤ 11 ∧
      n = Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a + 5 ∧
      TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 ∧ topRowA c % 8 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have hdA : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000 := by omega
  have hk : KnownOK (BC.bK 0 c) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 6) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 5) + 4 = pcOf (trPc 0 c + 6)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 5)
  have hglob := Glob_writeHash ht.glob a d h12 (safeDest_hi d (by unfold WLO WIT; omega) hdA.1 (by omega))
  have hv := DigAt.writeHash_lo t a d h12 (by omega)
  have h12s : (writeHash t a).getReg .x12 = BitVec.ofNat 64 d := by rw [writeHash_getReg]; exact h12
  have hD := hglob.2.2.2.2.2
  have h10 : (writeHash t a).getReg .x10 = BitVec.ofNat 64 (topRowA c) :=
    hk (.x10, BitVec.ofNat 64 (rowA 0 c)) (by simp [BC.bK])
  have hra : (writeHash t a).getReg .x2 = BitVec.ofNat 64 0xffbde0 :=
    hk (.x2, BitVec.ofNat 64 0xffbde0) (by simp [BC.bK, T3M.bK, layK])
  have h15 : (writeHash t a).getReg .x9 = 0x7fc00#64 :=
    hk (.x9, 0x7fc00#64) (by simp [BC.bK, T3M.bK, layK])
  have h4 : (writeHash t a).getReg .x4 = 24704#64 :=
    hk (.x4, 24704#64) (by simp [BC.bK, T3M.bK, layK, bufferBias])
  have h11 : (writeHash t a).getReg .x11 = 64#64 :=
    hk (.x11, 64#64) (by simp [BC.bK, T3M.bK, layK])
  have hmask : (writeHash t a).getMem 0xffbff8#64 = 520192#64 := hD.mask
  have hhi := DigAt.writeHash_hi t a d h12 (by omega)
  -- the choice hint byte (witness rel 21104 = abs 25232) is still the original witness byte
  have hhint : (extractByte ((writeHash t a).getMem 25232#64) 0).getLsbD Nonbinary.selHintBit =
      ClaudeWCT.W9.T3M.wtopHigh w := by
    have ho := Orig_writeHash ht.bufferOrig a d h12 (by omega)
    have hw := ho.word ClaudeWCT.W9.T3M.choiceOff (by decide) (by unfold WX; decide)
      ⟨⟨by norm_num [BC.bufferStart, ClaudeWCT.W9.T3M.choiceOff], by norm_num [ClaudeWCT.W9.T3M.choiceOff]⟩,
        Or.inr (by unfold WIT ClaudeWCT.W9.T3M.choiceOff; omega)⟩
    rw [show (25232#64 : Word) = BitVec.ofNat 64 (WIT + ClaudeWCT.W9.T3M.choiceOff) from rfl, hw,
      extractByte_wword_choice]
    rfl
  obtain ⟨z, ez, pz, lo, hi, s3, mask, rz, fz⟩ := Verify.Nonbinary.prefix_head_spec
    (writeHash t a) a (ClaudeWCT.W9.T3M.wtopHigh w) (topRowA c) d (trPc 0 c + 6) ha hpc (prefix_at c hc')
    h12s hdA h11 h4 hra hmask h10 hhint hv hhi
  have hn := Verify.Nonbinary.selCost_le (ClaudeWCT.W9.T3M.wtopHigh w) a
  unfold Verify.Nonbinary.selMax at hn
  refine ⟨_,z,ez,by omega,rfl,⟨pz,?_,lo,hi,s3,mask,?_,?_,?_⟩⟩
  · rw [rz.get (by decide),hra]
  · rw [rz.get (by decide),h15]
  · exact rz.mono (by simp [topEntryRegs])
  · exact fz.mono (by simp)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
/-- Campaign T51: the top context's digits: the 50 data digits of the selected half `v`, then the checksum digit
`min 5 (152 - data sum)` (the decoded checksum whenever it is in range), then 0. -/
def topDig (v : Digest) (i : Nat) : Nat :=
  if i < 50 then coreDigit 0 v i else if i = 50 then min 5 (T3.target 0 - (T3.dataDigits 0 v).sum) else 0
def nctxOf (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 14128, topDig v, p + 8⟩
/-- The context's digits through a symbolic index (a `show` at a literal index makes the unifier evaluate
`min 5 (target 0 - sum)`). -/
theorem nctxOf_dig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).dig i = topDig v i := rfl
theorem nctx_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).DigitsOk := by
  intro i hi
  rw [nctxOf_dig, Nonbinary.NCtx.topMax_eq]
  unfold topDig
  by_cases h50 : i < 50
  · rw [if_pos h50]; exact SigGolfCandidate.T3.Nonbinary.coreDigit_le 0 v i
  · rw [if_neg h50, if_pos (by omega), show i = 50 by omega]
    simp [T3.maxDigit]
theorem nctx_dataSum (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    ((List.range 50).map (nctxOf w index v p).dig).sum = (T3.dataDigits 0 v).sum := by
  have h : (List.range 50).map (nctxOf w index v p).dig = T3.dataDigits 0 v := by
    unfold T3.dataDigits
    show (List.range 50).map _ = (List.range 50).map (coreDigit 0 v)
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.mp hi
    rw [nctxOf_dig]
    simp [topDig, this]
  rw [h]
theorem nctx_ok (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  have ht : (route index 0).2 = 0 := by rw [route_snd]; exact Nat.div_eq_of_lt hidx
  exact ⟨ht, leaf_lt index 0, by norm_num [nctxOf], by norm_num [nctxOf, Verify.WIT], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩
theorem hyperWord_top_prefix (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    T3.hyperWord 0 (index / 2 ^ below 0) = BitVec.ofNat 64 ((nctxOf w index v p).prefix + 385) := by
  have h1 : (route index 0).1 = index / 2 ^ 19 % 2 ^ 12 := route_fst index 0
  have h2 : (route index 0).2 = index / 2 ^ (19 + 12) := route_snd index 0
  unfold T3.hyperWord NCtx.prefix
  simp only [nctxOf, h1, h2, show below 0 = 19 from rfl]
  congr 1
  norm_num
  omega
theorem nctx_known (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s) :
    KnownOK (nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).known s := by
  have hprefix : s.getReg .x28 =
      BitVec.ofNat 64 ((nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).prefix + 385) := by
    rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg, ht.word]
    exact hyperWord_top_prefix w index _ _
  intro p hp
  simp only [NCtx.known, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact hprefix
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK, bufferBias])
theorem topEntry_orig (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s) :
    Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd 0) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  rw [show BC.layerEnd 0 = 11144 from rfl] at hd
  have ho := Orig_writeHash ht.orig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inl (by
      have hp2 := hp.2
      have hle : layerEnd 0 = 11144 := rfl
      rw [hle] at hp2
      unfold WIT at *; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by norm_num [WIT, layerEnd] at *; omega))
theorem topEntry_bufferOrig (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s) :
    Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 21984) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have ho := Orig_writeHash ht.bufferOrig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 21984) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inr (by
      have hp1 := hp.1
      norm_num [BC.bufferStart] at hp1
      unfold WIT; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by norm_num [WIT, BC.bufferStart] at *; omega))
theorem nctx_orig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd 0) s)
    (hb : Verify.Orig w (fun o => BC.bufferStart 0 ≤ o ∧ o < 21984) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨⟨?_, ?_⟩, hD⟩
  · intro i hi k hk
    have hts := NCtx.topSlot_props i hi
    apply origW_of ho _
    all_goals simp only [NCtx.blk, nctxOf]
    all_goals norm_num [WIT, WX, layerEnd] at *
    all_goals omega
  · intro i hi k hk
    have hs := NCtx.slot_props i hi
    apply origW_of hb _
    all_goals norm_num [WIT, WX, BC.bufferStart] at *
    all_goals omega
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
/-! ### Campaign T51: the top chains as the source program (moved here from `Compose`). -/
theorem nctx_block (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p i : Nat) :
    (nctxOf w index v p).blk i - Verify.WIT = ClaudeWCT.W9.T3M.chainBlock 0 i := by
  change 14128 - 1664 + Nonbinary.topSlot i - Verify.WIT = 7664 + 16 * 42 + ClaudeWCT.W9.T3M.chainSlot 0 i
  rw [← NCtx.topSlot_eq]
  unfold Verify.WIT; omega
/-- `bufferSafe_source` from the agreement on digits `j ≤ i` only (a rejected word runs data chains only). -/
theorem bufferSafe_source_le (c : NCtx) (digits : List Nat) (i : Nat) (hi : i < 51)
    (hd : ∀ j, j ≤ i → digits.getD j 0 = c.dig j) :
    c.bufferSafe i ↔ ClaudeWCT.WCT9.safeZeroCopy 0 digits i := by
  unfold NCtx.bufferSafe ClaudeWCT.WCT9.safeZeroCopy
  rw [hd i le_rfl, NCtx.topMax_eq]
  by_cases hz : i = 0
  · simp [hz]
  · rw [hd (i-1) (by omega), NCtx.topMax_eq]
    simp [hz]
theorem bufferVal_source_le (c : NCtx) (digits : List Nat) (hS : c.S3 = 14128) (i : Nat) (hi : i < 51)
    (hd : ∀ j, j ≤ i → digits.getD j 0 = c.dig j) :
    c.bufferVal i = ClaudeWCT.W9.T3M.wvalueFor c.w 0 digits i := by
  unfold NCtx.bufferVal ClaudeWCT.W9.T3M.wvalueFor
  simp only [← bufferSafe_source_le c digits i hi hd, NCtx.bufferSlot_source]
  split
  · rfl
  · unfold NCtx.val ClaudeWCT.W9.T3M.wvalue
    apply congrArg (ClaudeWCT.W9.T3M.wdig c.w)
    have hv : ClaudeWCT.W9.T3M.valueOff 0 i = 48 * (i % 2) := by
      unfold ClaudeWCT.W9.T3M.valueOff; rw [← NCtx.topG_isG, NCtx.topG_lt i hi]
      by_cases h : i % 2 = 0 <;> simp [h] <;> omega
    rw [hv]
    simp only [NCtx.vAt, NCtx.blk, hS, ClaudeWCT.W9.T3M.chainBlock, ClaudeWCT.W9.T3M.layerBase,
      ClaudeWCT.W9.T3M.pathSlots, Matrix.cons_val_zero, Verify.WIT, ← NCtx.topSlot_eq]
    omega
/-- Campaign T51: chain `i` of the top source program for the digit list `ds` (decoded: 50 data digits + checksum;
rejected: the data digits). -/
def srcChain (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ds : List Nat) (i : Nat) : T3.M Digest :=
  ClaudeWCT.W9.T3M.chainPW 0 (route index 0).2 (route index 0).1 i (ds.getD i 0)
    (maxDigit 0 i - ds.getD i 0) (ClaudeWCT.W9.T3M.wchainPads w 0 i).1
    (ClaudeWCT.W9.T3M.wchainPads w 0 i).2 (ClaudeWCT.W9.T3M.wchainHeaderPad w 0 i) (ClaudeWCT.W9.T3M.wvalueFor w 0 ds i)
theorem nctx_chain_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (ds : List Nat)
    (i : Nat) (hi : i < 51) (hds : ∀ j, j ≤ i → ds.getD j 0 = (nctxOf w index v p).dig j) :
    let c := nctxOf w index v p
    ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i - c.dig i) (c.pad0 i) (c.pad1 i)
      (c.padHeader i) (c.bufferVal i) = srcChain w index ds i := by
  have hbuf := bufferVal_source_le (nctxOf w index v p) ds rfl i hi hds
  dsimp only
  unfold srcChain
  rw [← hds i (le_refl _), NCtx.topMax_eq, hbuf]
  have hp0 : (nctxOf w index v p).pad0At i - Verify.WIT =
      ClaudeWCT.W9.T3M.chainBlock 0 i + ClaudeWCT.W9.T3M.pad0Off 0 i := by
    rw [← nctx_block w index v p i]
    unfold NCtx.pad0At ClaudeWCT.W9.T3M.pad0Off; rw [← NCtx.topG_isG, NCtx.topG_lt i hi]
    simp only [NCtx.blk, nctxOf, Verify.WIT]
    by_cases h : i % 2 = 0 <;> simp [h] <;> omega
  have hp1 : (nctxOf w index v p).pad1At i - Verify.WIT =
      ClaudeWCT.W9.T3M.chainBlock 0 i + ClaudeWCT.W9.T3M.pad1Off 0 i := by
    rw [← nctx_block w index v p i]
    unfold NCtx.pad1At ClaudeWCT.W9.T3M.pad1Off; rw [← NCtx.topG_isG, NCtx.topG_lt i hi]
    simp only [NCtx.blk, nctxOf, Verify.WIT]
    by_cases h : i % 2 = 0 <;> simp [h] <;> omega
  unfold NCtx.pad0 NCtx.pad1 NCtx.padHeader
  rw [nctx_block, hp0, hp1]
  rfl
/-- Campaign T51: before a top rejection only data chains (`i < 50`) run, with their data digits. -/
theorem topRejectChains_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (m : Nat) (hm : m ≤ 50)
    (hL : ClaudeWCT.WCT9.topRejectLength v = m) :
    ClaudeWCT.WCT9.topRejectChains (ClaudeWCT.W9.T3M.topChainP w (route index 0).2 (route index 0).1 (dataDigits 0 v)) v =
      (List.range' 0 m).mapM (srcChain w index (dataDigits 0 v)) := by
  unfold ClaudeWCT.WCT9.topRejectChains
  rw [hL]
  refine (TopSource.take_mapM (fun n => ClaudeWCT.W9.T3M.chainPW 0 (route index 0).2 (route index 0).1 n
    (ClaudeWCT.WCT9.topRunDigit v n) (maxDigit 0 n - ClaudeWCT.WCT9.topRunDigit v n)
    (ClaudeWCT.W9.T3M.wchainPads w 0 n).1 (ClaudeWCT.W9.T3M.wchainPads w 0 n).2
    (ClaudeWCT.W9.T3M.wchainHeaderPad w 0 n) (ClaudeWCT.W9.T3M.wvalueFor w 0 (dataDigits 0 v) n)) m (by omega)).trans ?_
  apply mapM_congr'
  intro n hn
  have hn' := List.mem_range'_1.mp hn
  unfold srcChain ClaudeWCT.WCT9.topRunDigit
  rw [if_pos (by omega)]
/-- The context's data digits are the word's data digits (the reject path's agreement). -/
theorem nctx_data_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p j : Nat) (hj : j < 50) :
    (dataDigits 0 v).getD j 0 = (nctxOf w index v p).dig j := by
  rw [nctxOf_dig, ClaudeWCT.WCT9.dataDigits_top_getD v hj]
  unfold topDig; rw [if_pos hj]
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topChainRegs : List Reg := [.x10,.x12,.x25,.x3,.x14,.x15,.x24,.x29,.x18]
/-- Campaign T51: the top chains write chain 0's terminal 32 bytes at `[25200, 25232)` (c0hi: the high half is
`end_0` at 25216, the junk low half on the dead L1 leaf-buffer tail), the ends of chains 1..50 from 25248 on, and the
chain blocks. The leaf tweak `[25232, 25248)` is never written. -/
def topChainWrites (A : Nat) : Prop := (25200 ≤ A ∧ A < 25232) ∨ (25248 ≤ A ∧ A < 26064) ∨ (12464 ≤ A ∧ A < 15288)
/-- Campaign T51: the top leaf's known registers (`leafK 0` keeps `t0 = 0` but not main's `s2 = 0xFFF`: the g0 body
loads `s2 = 856064`). -/
theorem topLeafK_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s0 s : MachineState)
    (a : BitVec 256) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hr : RegsExcept s0 s topChainRegs) (_h15 : s.getReg .x9 = 0x7fc00#64) : KnownOK (leafK 0) s := by
  intro p hp
  simp only [leafK, gkL, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals rw [hr.get (by simp [topChainRegs])]
  all_goals try exact he.mask
  all_goals rw [he.regs.get (by simp [topEntryRegs]),writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
/-- Digit constants and leaf globals survive both the top entry and all chains. -/
theorem topLeafKeepK_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat)
    (t s0 s : MachineState) (a : BitVec 256) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hr : RegsExcept s0 s topChainRegs) : KnownOK (lfKeepK 0) s := by
  intro p hp
  simp [lfKeepK] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [hr.get (by simp [topChainRegs])]
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact he.table
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
/-- Campaign T51: at the final tail `ckTail d50` after the 51 top chains, the top leaf is ready: 51 ends at
`slotT j`, and the tweak high word is witness memory as found. -/
theorem topLeafReady_of (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s0 s : MachineState) (a : BitVec 256) (ends : List Digest) (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (hp : s.pc = pcOf (Nonbinary.ckTail
      ((nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).dig 50)))
    (hr : RegsExcept s0 s topChainRegs) (hf : Frame s0 s topChainWrites) (h15 : s.getReg .x9 = 0x7fc00#64)
    (hlen : ends.length = 51) (hend : ∀j<51, DigAt s (slotT j) (ends.getD j 0)) :
    TopLeafReady w pk index c ends s := by
  have hk := topLeafK_of w pk index c t s0 s a ht he hr h15
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 ∧ topRowA c % 8 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d,h12,hd⟩ := ht.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  have hg := Glob_writeHash ht.glob a d h12 (safeDest_hi d (by unfold WLO WIT; omega) (by omega) (by omega))
  have hfr : Frame (writeHash t a) s (fun A => A = 25160 ∨ topChainWrites A) :=
    he.frame.trans hf
  have hglob : Glob (leafK 0) w pk s := glob_frame hg hfr (by
    intro A h
    unfold topChainWrites at h
    rcases h with h | h | h | h <;> omega) hk
  have hreg : ∀ r, r ∉ topChainRegs → r ∉ topEntryRegs → s.getReg r = t.getReg r := fun r h1 h2 => by
    rw [hr.get h1, he.regs.get h2, writeHash_getReg]
  have hy : (nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).dig 50 < 6 := by
    rw [nctxOf_dig]
    unfold topDig
    rw [if_neg (by omega), if_pos rfl]
    omega
  refine ⟨⟨_,hy,hp⟩,hglob,?_,?_,?_,?_,hlen,hend,?_,?_⟩
  · exact topLeafKeepK_of w pk index c t s0 s a ht he hr
  · rw [hreg .x23 (by decide +kernel) (by decide +kernel)]
    exact ht.s7 0 rfl (by decide)
  · rw [hreg .x31 (by decide +kernel) (by decide +kernel)]
    exact (ht.t5 0 rfl).2 rfl
  · rw [hreg .x28 (by decide +kernel) (by decide +kernel), ht.word]
    exact hyperWord_top_prefix w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) |>.trans (by
      congr 1
      simp only [Nonbinary.NCtx.prefix, nctxOf, show T3.height 0 = 12 from rfl, Fin.val_zero]
      omega)
  · have ho := topEntry_orig w pk index c hc t s0 a ht he
    apply (ho.mono (fun o h => ⟨h.1, by
      norm_num [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots, layerEnd] at *; omega⟩)).frame
    intro j hj hp
    exact hf.get (by unfold WIT WX at *;omega) (by
      norm_num [ClaudeWCT.W9.T3M.layerBase, ClaudeWCT.W9.T3M.pathSlots] at hp
      unfold topChainWrites WIT
      omega)
  · -- C3: the top leaf tweak's high word is witness memory
    have h1 : s.getMem (BitVec.ofNat 64 25240) = t.getMem (BitVec.ofNat 64 25240) := by
      rw [hf.get (by omega) (by unfold topChainWrites; omega), he.frame.get (by omega) (by omega),
        writeHash_frame t a d 25240 h12 (by omega) (by omega) (Or.inr (by omega))]
    have hlb0 : ClaudeWCT.W9.T3M.leafBufferBase 0 = 21088 := rfl
    have hhi := ht.bufferOrig.hi 21104 (by decide) (by unfold WX; decide) ⟨by decide, by decide⟩
    unfold ClaudeWCT.W9.T3M.wleafHigh; rw [hlb0]
    exact h1.trans hhi
end SigGolfCandidate.T3M
end
end
-- ==== merged from T3M_Verify_MerkleRuns ====
section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def mkKnownKeep (known : List (Reg × Word)) (keep : List Reg) : List (Reg × Word) :=
  known.filter fun p => keep.contains p.1
def mkUnknownKeep (known : List (Reg × Word)) (keep : List Reg) : List Reg :=
  keep.filter fun r => !(known.any fun p => p.1 == r)
def mkSpecB (allow : List Nat) (rel : List Reg) (gk known : List (Reg × Word))
    (stops : List Nat) (n : Nat) (dirs : List Dir) (sp : Spec)
    (obl : List Oblig) (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  specB allow rel gk (runAt known stops n dirs) sp obl
    (post ++ mkKnownKeep known keep) (mkUnknownKeep known keep)
def mkNch (lay : Nat) : Nat := if lay = 0 then 2 else 1
def mkLo (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 6 else 0
def mkBits (lay ci : Nat) : Nat := if lay = 0 then 6 else hL lay
def mkTab (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 133840 else stabIdx lay
def mkTabW (lay ci sh : Nat) : Nat := if lay = 0 ∧ ci = 1 then 15718 + 256 * sh else stabW lay sh
def mkShp (lay ci sh : Nat) : Nat :=
  if lay = 3 then 133764 + 128 * sh else if lay = 2 then 141956 + 128 * sh
  else if lay = 1 then 1028 + 1024 * sh else if ci = 0 then 142032 + 128 * sh else 133840 + 128 * sh
/-- C2: every lower fold writes its packed tweak word from an immediate (`addi gp,t3,K; sd gp,16(a0)`), so it costs
like the old register-heap levels; the top tree keeps register heaps on its last three levels only. -/
def mkReg (lay l : Nat) : Bool := decide (lay ≠ 0 ∨ hL lay ≤ l + 3)
/-- Words of the level-`l` block (its ecall included). C4 top: one label store per level (`srli gp,s7,5+l; sd gp,16(a0)`
in the lower copy, `addi gp,zero,heap; sd gp,16(a0)` or `sd REG,16(a0)` in the upper copy); the last level (11) counts
a virtual `addi a2` (`mkMove 0 11 = 0`). -/
def mkWords (lay l : Nat) : Nat :=
  (if l = 0 then (if lay = 0 then 5 else 9) else (if lay = 0 then 4 else 5)) + (if mkReg lay l then 0 else 1)
def mkOff (lay ci : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci kk + mkWords lay (mkLo lay ci + kk)
/-- C4: every layer (the top included) places its windows by the plan (`plan 0` = the two-line top plan). -/
def mkBo (lay leaf l : Nat) : Nat := mkBase lay + 16 * plan lay leaf l
def mkBlk (lay leaf l : Nat) : Nat := 0x1020 + mkBo lay leaf l
/-- Position of the value a level reads as its current input (left slot for bit 0, right slot for bit 1). -/
def mkVal (lay leaf l b : Nat) : Nat := mkBlk lay leaf l + 48 * b
/-- Hash destination (`a2`) feeding level `l`: the value position, except that a left child (C2, and C4 on the top:
HIGH half) is written 16 bytes earlier so that its high half lands in the left slot. -/
def mkCur (lay leaf l b : Nat) : Nat := mkVal lay leaf l b + 16 * b - 16
/-- Representative leaf of chunk pattern `sh` (C4: the top's upper copies are indexed by `leaf / 64`). -/
def mkLeafOf (lay ci sh : Nat) : Nat := sh * 2 ^ mkLo lay ci
/-- C4: the top root is the low half of the last fold's answer, written where node 11's input was delivered. -/
def mkDst (lay leaf : Nat) : Nat := if lay = 0 then mkCur 0 leaf 11 (leaf / 2048 % 2) else 256
def mkMove (lay level : Nat) : Nat := if lay = 0 ∧ level = 11 then 0 else 1
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)
def mkK (lay : Nat) : List (Reg × Word) :=
  gkL lay ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x7, 1), (.x13, 2),
    (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x5, 0)] ++
    (if lay = 0 then [] else [(.x2, BitVec.ofNat 64 0xffbde0)])
def mkKc (lay : Nat) : List (Reg × Word) :=
  gkL lay ++ [(if lay = 0 then (.x8, BitVec.ofNat 64 s3v) else (.x22, BitVec.ofNat 64 (s6v lay))), (.x7, 1), (.x13, 2),
    (.x19, 3), (.x20, 4), (.x21, 5), (.x26, 6), (.x30, 7), (.x5, 0)]
def mkKeep : List Reg := [.x4, .x1, .x2, .x16, .x17, .x8, .x9, .x24, .x23, .x6, .x25, .x27, .x29, .x31]
def mkEntSpec (lay ci sh : Nat) : Spec := let st := if lay = 0 ∧ ci = 1 then 2 else 1; ⟨[], [], mkShp lay ci sh + 1, true, st, [], none, st⟩
def mkEntPost (lay ci sh : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x12, BitVec.ofNat 64 (mkCur lay (mkLeafOf lay ci sh) (mkLo lay ci) (sh % 2)))]
def mkEntKeep : List Reg := mkKeep ++ [.x10, .x11, .x14, .x4, .x28]
def mkEntK (lay ci : Nat) : List (Reg × Word) :=
  mkKc lay ++ (if lay = 0 ∧ ci = 1 then [(.x10, BitVec.ofNat 64 (mkBlk 0 0 5))] else [])
def mkEntCheck (lay ci sh : Nat) : Bool :=
  mkSpecB [] [] (gkL lay) (mkEntK lay ci) [] (mkTabW lay ci sh) [] (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def mkHeapE (lay ci sh l : Nat) : E :=
  if lay = 0 ∧ ci = 0 then .bin .srl (.reg .x23) (kw (l + 5)) else kw (mkHeap lay ci sh l)
def t3E (l' : Nat) : E := .bin .or (.bin .sll (.reg .x31) (kw 16)) (.ld (kw (hdrA l')))
def mkHdrE (lay l : Nat) : E := if lay = 0 then kw 64 else if l = 0 then t3E (lay - 1) else .reg .x28
/-- C2 lower fold constant `K heap = mkK7 + heap` (= `WCT9.lowerK`). -/
def mkK7 : Nat := 1407
/-- C2: lower levels write only the packed tweak word `hyperWord + mkK7 + heap`; its high word is witness memory.
C4: a top level writes only its one-word label, the heap. -/
def mkLabE (lay ci sh l : Nat) : E :=
  if lay = 0 then mkHeapE lay ci sh l else addC (mkHdrE lay l) (BitVec.ofNat 64 (mkK7 + mkHeap lay ci sh l))
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) l + 16)⟩, mkLabE lay ci sh l)]
def mkLvlRegs (lay l : Nat) : List (Reg × E) := if l = 0 ∧ lay ≠ 0 then [(.x28, t3E (lay - 1))] else []
def mkLvlKeep (lay l : Nat) : List Reg := if l = 0 ∧ lay ≠ 0 then [] else [.x28]
def mkLvlAllow (lay sh l : Nat) : List Nat := [mkBlk lay sh l + 16, mkBlk lay sh l + 24]
def mkDispTgt (sh : Nat) : E :=
  .bin .and (addC (.reg .x23) (BitVec.ofNat 64 1432 - BitVec.ofNat 64 (16 * sh))) (.c (~~~1#64))
def mkBody (lay l : Nat) : Nat :=
  (if l = 0 then (if lay = 0 then 2 else 6) else (if lay = 0 then 1 else 2)) + (if mkReg lay l then 1 else 2)
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkCur lay (mkLeafOf lay ci sh) (mkLo lay ci + kk + 1) (sh / 2 ^ (kk + 1) % 2)
  else if lay = 0 then mkCur lay (mkLeafOf lay ci sh) (mkLo lay ci + kk) (sh / 2 ^ kk % 2) else 256
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk),
    mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk), true,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk), [], none,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk)⟩
def mkLvlSpecD (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk), 0, false,
    mkBody lay (mkLo lay ci + kk) + 1, [], some (mkDispTgt sh),
    mkBody lay (mkLo lay ci + kk) + 1⟩
def mkLvlK (lay l : Nat) : List (Reg × Word) := if l = 0 then mkK lay else mkKc lay ++ [(.x11, 64)]
def mkLvlPostN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) (mkLo lay ci + kk))),
    (.x12, BitVec.ofNat 64 (mkNextA2 lay ci sh kk))]
def mkLvlPostD (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLeafOf lay ci sh) (mkLo lay ci + kk))), (.x7, 1)]
def mkLvlKN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkLvlK lay (mkLo lay ci + kk) ++
    (if lay = 0 then
      [(.x12, BitVec.ofNat 64 (mkCur lay (mkLeafOf lay ci sh) (mkLo lay ci + kk) (sh / 2 ^ kk % 2)))] else [])
def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] (gkL lay)
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) []
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk) (mkKeep ++ (.x14 :: mkLvlKeep lay (mkLo lay ci + kk)))
def mkLvlCheckD (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] (gkL lay)
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [.jmp]
    (mkLvlSpecD lay ci sh kk) [] (mkLvlPostD lay ci sh kk) (mkKeep ++ mkLvlKeep lay (mkLo lay ci + kk))
def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then mkLvlCheckD lay ci sh kk else mkLvlCheckN lay ci sh kk
def mkBlockCheck (lay ci sh : Nat) : Bool :=
  mkEntCheck lay ci sh && (List.range (mkBits lay ci)).all (mkLvlCheck lay ci sh)
def mkChunkCheck (lay ci lo n : Nat) : Bool := (List.range' lo n).all (mkBlockCheck lay ci)
/-- C4: the root compare moved up 6 words (`133868 + 128 c`) and reads the root where upper copy `c` wrote it. -/
def cmpPc (c : Nat) : Nat := 133868 + 128 * c
def cmpDst (c : Nat) : Nat := 11792 + 16 * topRootSlot.getD c 0
def cmpK (c : Nat) : List (Reg × Word) := gkL 0 ++ [(.x12, BitVec.ofNat 64 (cmpDst c))]
def cmpBr1 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c)), .ld (kw 160), d⟩
def cmpBr2 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c + 8)), .ld (kw 168), d⟩
def cmpDelta (c : Nat) : E := .bin .sub (.ld (kw (cmpDst c + 8))) (.ld (kw 168))
def cmpAcc (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, cmpDelta c)], [], cmpPc c + 7, true, 7, [cmpBr1 c false], none, 7⟩
def cmpRej1 (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], cmpPc c + 11, true, 5, [cmpBr1 c true], none, 5⟩
def cmpCheck (c : Nat) : Bool :=
  specB [] [] [] (runAt (cmpK c) [] (cmpPc c) [.br false]) (cmpAcc c) [] [] [] &&
  specB [] [] [] (runAt (cmpK c) [] (cmpPc c) [.br true]) (cmpRej1 c) [] [] []
end SigGolfCandidate.T3M
end
-- ==== merged from T3M_Verify_DirectMerkleChecks ====
section

set_option Elab.async false

section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def mkShp (lay ci sh : Nat) : Nat :=
  T3M.mkShp lay ci sh
def mkEntSpec (lay ci sh : Nat) : Spec :=
  let st := if lay = 0 ∧ ci = 1 then 2 else 1
  ⟨[], [], mkShp lay ci sh + 1, true, st, [], none, st⟩
def mkEntCheck (lay ci sh : Nat) : Bool :=
  mkSpecB [] [] (gkL lay) (mkEntK lay ci) [] (mkTabW lay ci sh) []
    (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  { T3M.mkLvlSpecN lay ci sh kk with
    pc := mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk) }
def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  mkSpecB (mkLvlAllow lay (mkLeafOf lay ci sh) (mkLo lay ci + kk)) [] (gkL lay)
    (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) []
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk)
    (mkKeep ++ (.x14 :: mkLvlKeep lay (mkLo lay ci + kk)))
def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then T3M.mkLvlCheckD lay ci sh kk
  else mkLvlCheckN lay ci sh kk
def childReturn (lay sh : Nat) : Nat :=
  mkShp lay 0 sh + mkOff lay 0 (hL lay - 1) + 2
def mkBlockCheck (lay ci sh : Nat) : Bool :=
  mkEntCheck lay ci sh &&
  (List.range (mkBits lay ci - if lay = 0 then 0 else 1)).all (mkLvlCheck lay ci sh) &&
  (lay == 0 || childReturn lay sh == trPc (lay - 1) sh)
def mkChunkCheck (lay ci lo n : Nat) : Bool :=
  (List.range' lo n).all (mkBlockCheck lay ci)
end SigGolfCandidate.T3M.BC
end
section
namespace SigGolfCandidate.T3M.BC
set_option maxRecDepth 100000
theorem mkChunkCheck_add {lay ci lo left right : Nat}
    (hleft : mkChunkCheck lay ci lo left = true)
    (hright : mkChunkCheck lay ci (lo + left) right = true) :
    mkChunkCheck lay ci lo (left + right) = true := by
  unfold mkChunkCheck at *
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl
private theorem mkCheck_part_3_0_0 : mkChunkCheck 3 0 0 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_4 : mkChunkCheck 3 0 4 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_8 : mkChunkCheck 3 0 8 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_12 : mkChunkCheck 3 0 12 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_16 : mkChunkCheck 3 0 16 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_20 : mkChunkCheck 3 0 20 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_24 : mkChunkCheck 3 0 24 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_28 : mkChunkCheck 3 0 28 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_32 : mkChunkCheck 3 0 32 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_36 : mkChunkCheck 3 0 36 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_40 : mkChunkCheck 3 0 40 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_44 : mkChunkCheck 3 0 44 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_48 : mkChunkCheck 3 0 48 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_52 : mkChunkCheck 3 0 52 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_56 : mkChunkCheck 3 0 56 4 = true := by decide +kernel
private theorem mkCheck_part_3_0_60 : mkChunkCheck 3 0 60 4 = true := by decide +kernel
theorem mkCheck_3 : mkChunkCheck 3 0 0 64 = true := by
  exact @mkChunkCheck_add 3 0 0 4 60 mkCheck_part_3_0_0 (@mkChunkCheck_add 3 0 4 4 56 mkCheck_part_3_0_4 (@mkChunkCheck_add 3 0 8 4 52 mkCheck_part_3_0_8 (@mkChunkCheck_add 3 0 12 4 48 mkCheck_part_3_0_12 (@mkChunkCheck_add 3 0 16 4 44 mkCheck_part_3_0_16 (@mkChunkCheck_add 3 0 20 4 40 mkCheck_part_3_0_20 (@mkChunkCheck_add 3 0 24 4 36 mkCheck_part_3_0_24 (@mkChunkCheck_add 3 0 28 4 32 mkCheck_part_3_0_28 (@mkChunkCheck_add 3 0 32 4 28 mkCheck_part_3_0_32 (@mkChunkCheck_add 3 0 36 4 24 mkCheck_part_3_0_36 (@mkChunkCheck_add 3 0 40 4 20 mkCheck_part_3_0_40 (@mkChunkCheck_add 3 0 44 4 16 mkCheck_part_3_0_44 (@mkChunkCheck_add 3 0 48 4 12 mkCheck_part_3_0_48 (@mkChunkCheck_add 3 0 52 4 8 mkCheck_part_3_0_52 (@mkChunkCheck_add 3 0 56 4 4 mkCheck_part_3_0_56 (mkCheck_part_3_0_60)))))))))))))))
private theorem mkCheck_part_2_0_0 : mkChunkCheck 2 0 0 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_4 : mkChunkCheck 2 0 4 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_8 : mkChunkCheck 2 0 8 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_12 : mkChunkCheck 2 0 12 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_16 : mkChunkCheck 2 0 16 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_20 : mkChunkCheck 2 0 20 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_24 : mkChunkCheck 2 0 24 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_28 : mkChunkCheck 2 0 28 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_32 : mkChunkCheck 2 0 32 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_36 : mkChunkCheck 2 0 36 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_40 : mkChunkCheck 2 0 40 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_44 : mkChunkCheck 2 0 44 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_48 : mkChunkCheck 2 0 48 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_52 : mkChunkCheck 2 0 52 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_56 : mkChunkCheck 2 0 56 4 = true := by decide +kernel
private theorem mkCheck_part_2_0_60 : mkChunkCheck 2 0 60 4 = true := by decide +kernel
theorem mkCheck_2 : mkChunkCheck 2 0 0 64 = true := by
  exact @mkChunkCheck_add 2 0 0 4 60 mkCheck_part_2_0_0 (@mkChunkCheck_add 2 0 4 4 56 mkCheck_part_2_0_4 (@mkChunkCheck_add 2 0 8 4 52 mkCheck_part_2_0_8 (@mkChunkCheck_add 2 0 12 4 48 mkCheck_part_2_0_12 (@mkChunkCheck_add 2 0 16 4 44 mkCheck_part_2_0_16 (@mkChunkCheck_add 2 0 20 4 40 mkCheck_part_2_0_20 (@mkChunkCheck_add 2 0 24 4 36 mkCheck_part_2_0_24 (@mkChunkCheck_add 2 0 28 4 32 mkCheck_part_2_0_28 (@mkChunkCheck_add 2 0 32 4 28 mkCheck_part_2_0_32 (@mkChunkCheck_add 2 0 36 4 24 mkCheck_part_2_0_36 (@mkChunkCheck_add 2 0 40 4 20 mkCheck_part_2_0_40 (@mkChunkCheck_add 2 0 44 4 16 mkCheck_part_2_0_44 (@mkChunkCheck_add 2 0 48 4 12 mkCheck_part_2_0_48 (@mkChunkCheck_add 2 0 52 4 8 mkCheck_part_2_0_52 (@mkChunkCheck_add 2 0 56 4 4 mkCheck_part_2_0_56 (mkCheck_part_2_0_60)))))))))))))))
private theorem mkCheck_part_1_0_0 : mkChunkCheck 1 0 0 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_4 : mkChunkCheck 1 0 4 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_8 : mkChunkCheck 1 0 8 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_12 : mkChunkCheck 1 0 12 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_16 : mkChunkCheck 1 0 16 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_20 : mkChunkCheck 1 0 20 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_24 : mkChunkCheck 1 0 24 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_28 : mkChunkCheck 1 0 28 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_32 : mkChunkCheck 1 0 32 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_36 : mkChunkCheck 1 0 36 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_40 : mkChunkCheck 1 0 40 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_44 : mkChunkCheck 1 0 44 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_48 : mkChunkCheck 1 0 48 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_52 : mkChunkCheck 1 0 52 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_56 : mkChunkCheck 1 0 56 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_60 : mkChunkCheck 1 0 60 4 = true := by decide +kernel
theorem mkCheck_1a : mkChunkCheck 1 0 0 64 = true := by
  exact @mkChunkCheck_add 1 0 0 4 60 mkCheck_part_1_0_0 (@mkChunkCheck_add 1 0 4 4 56 mkCheck_part_1_0_4 (@mkChunkCheck_add 1 0 8 4 52 mkCheck_part_1_0_8 (@mkChunkCheck_add 1 0 12 4 48 mkCheck_part_1_0_12 (@mkChunkCheck_add 1 0 16 4 44 mkCheck_part_1_0_16 (@mkChunkCheck_add 1 0 20 4 40 mkCheck_part_1_0_20 (@mkChunkCheck_add 1 0 24 4 36 mkCheck_part_1_0_24 (@mkChunkCheck_add 1 0 28 4 32 mkCheck_part_1_0_28 (@mkChunkCheck_add 1 0 32 4 28 mkCheck_part_1_0_32 (@mkChunkCheck_add 1 0 36 4 24 mkCheck_part_1_0_36 (@mkChunkCheck_add 1 0 40 4 20 mkCheck_part_1_0_40 (@mkChunkCheck_add 1 0 44 4 16 mkCheck_part_1_0_44 (@mkChunkCheck_add 1 0 48 4 12 mkCheck_part_1_0_48 (@mkChunkCheck_add 1 0 52 4 8 mkCheck_part_1_0_52 (@mkChunkCheck_add 1 0 56 4 4 mkCheck_part_1_0_56 (mkCheck_part_1_0_60)))))))))))))))
private theorem mkCheck_part_1_0_64 : mkChunkCheck 1 0 64 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_68 : mkChunkCheck 1 0 68 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_72 : mkChunkCheck 1 0 72 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_76 : mkChunkCheck 1 0 76 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_80 : mkChunkCheck 1 0 80 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_84 : mkChunkCheck 1 0 84 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_88 : mkChunkCheck 1 0 88 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_92 : mkChunkCheck 1 0 92 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_96 : mkChunkCheck 1 0 96 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_100 : mkChunkCheck 1 0 100 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_104 : mkChunkCheck 1 0 104 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_108 : mkChunkCheck 1 0 108 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_112 : mkChunkCheck 1 0 112 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_116 : mkChunkCheck 1 0 116 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_120 : mkChunkCheck 1 0 120 4 = true := by decide +kernel
private theorem mkCheck_part_1_0_124 : mkChunkCheck 1 0 124 4 = true := by decide +kernel
theorem mkCheck_1b : mkChunkCheck 1 0 64 64 = true := by
  exact @mkChunkCheck_add 1 0 64 4 60 mkCheck_part_1_0_64 (@mkChunkCheck_add 1 0 68 4 56 mkCheck_part_1_0_68 (@mkChunkCheck_add 1 0 72 4 52 mkCheck_part_1_0_72 (@mkChunkCheck_add 1 0 76 4 48 mkCheck_part_1_0_76 (@mkChunkCheck_add 1 0 80 4 44 mkCheck_part_1_0_80 (@mkChunkCheck_add 1 0 84 4 40 mkCheck_part_1_0_84 (@mkChunkCheck_add 1 0 88 4 36 mkCheck_part_1_0_88 (@mkChunkCheck_add 1 0 92 4 32 mkCheck_part_1_0_92 (@mkChunkCheck_add 1 0 96 4 28 mkCheck_part_1_0_96 (@mkChunkCheck_add 1 0 100 4 24 mkCheck_part_1_0_100 (@mkChunkCheck_add 1 0 104 4 20 mkCheck_part_1_0_104 (@mkChunkCheck_add 1 0 108 4 16 mkCheck_part_1_0_108 (@mkChunkCheck_add 1 0 112 4 12 mkCheck_part_1_0_112 (@mkChunkCheck_add 1 0 116 4 8 mkCheck_part_1_0_116 (@mkChunkCheck_add 1 0 120 4 4 mkCheck_part_1_0_120 (mkCheck_part_1_0_124)))))))))))))))
private theorem mkCheck_part_0_0_0 : mkChunkCheck 0 0 0 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_4 : mkChunkCheck 0 0 4 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_8 : mkChunkCheck 0 0 8 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_12 : mkChunkCheck 0 0 12 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_16 : mkChunkCheck 0 0 16 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_20 : mkChunkCheck 0 0 20 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_24 : mkChunkCheck 0 0 24 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_28 : mkChunkCheck 0 0 28 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_32 : mkChunkCheck 0 0 32 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_36 : mkChunkCheck 0 0 36 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_40 : mkChunkCheck 0 0 40 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_44 : mkChunkCheck 0 0 44 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_48 : mkChunkCheck 0 0 48 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_52 : mkChunkCheck 0 0 52 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_56 : mkChunkCheck 0 0 56 4 = true := by decide +kernel
private theorem mkCheck_part_0_0_60 : mkChunkCheck 0 0 60 4 = true := by decide +kernel
theorem mkCheck_00 : mkChunkCheck 0 0 0 64 = true := by
  exact @mkChunkCheck_add 0 0 0 4 60 mkCheck_part_0_0_0 (@mkChunkCheck_add 0 0 4 4 56 mkCheck_part_0_0_4 (@mkChunkCheck_add 0 0 8 4 52 mkCheck_part_0_0_8 (@mkChunkCheck_add 0 0 12 4 48 mkCheck_part_0_0_12 (@mkChunkCheck_add 0 0 16 4 44 mkCheck_part_0_0_16 (@mkChunkCheck_add 0 0 20 4 40 mkCheck_part_0_0_20 (@mkChunkCheck_add 0 0 24 4 36 mkCheck_part_0_0_24 (@mkChunkCheck_add 0 0 28 4 32 mkCheck_part_0_0_28 (@mkChunkCheck_add 0 0 32 4 28 mkCheck_part_0_0_32 (@mkChunkCheck_add 0 0 36 4 24 mkCheck_part_0_0_36 (@mkChunkCheck_add 0 0 40 4 20 mkCheck_part_0_0_40 (@mkChunkCheck_add 0 0 44 4 16 mkCheck_part_0_0_44 (@mkChunkCheck_add 0 0 48 4 12 mkCheck_part_0_0_48 (@mkChunkCheck_add 0 0 52 4 8 mkCheck_part_0_0_52 (@mkChunkCheck_add 0 0 56 4 4 mkCheck_part_0_0_56 (mkCheck_part_0_0_60)))))))))))))))
private theorem mkCheck_part_0_1_0 : mkChunkCheck 0 1 0 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_4 : mkChunkCheck 0 1 4 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_8 : mkChunkCheck 0 1 8 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_12 : mkChunkCheck 0 1 12 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_16 : mkChunkCheck 0 1 16 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_20 : mkChunkCheck 0 1 20 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_24 : mkChunkCheck 0 1 24 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_28 : mkChunkCheck 0 1 28 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_32 : mkChunkCheck 0 1 32 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_36 : mkChunkCheck 0 1 36 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_40 : mkChunkCheck 0 1 40 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_44 : mkChunkCheck 0 1 44 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_48 : mkChunkCheck 0 1 48 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_52 : mkChunkCheck 0 1 52 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_56 : mkChunkCheck 0 1 56 4 = true := by decide +kernel
private theorem mkCheck_part_0_1_60 : mkChunkCheck 0 1 60 4 = true := by decide +kernel
theorem mkCheck_01 : mkChunkCheck 0 1 0 64 = true := by
  exact @mkChunkCheck_add 0 1 0 4 60 mkCheck_part_0_1_0 (@mkChunkCheck_add 0 1 4 4 56 mkCheck_part_0_1_4 (@mkChunkCheck_add 0 1 8 4 52 mkCheck_part_0_1_8 (@mkChunkCheck_add 0 1 12 4 48 mkCheck_part_0_1_12 (@mkChunkCheck_add 0 1 16 4 44 mkCheck_part_0_1_16 (@mkChunkCheck_add 0 1 20 4 40 mkCheck_part_0_1_20 (@mkChunkCheck_add 0 1 24 4 36 mkCheck_part_0_1_24 (@mkChunkCheck_add 0 1 28 4 32 mkCheck_part_0_1_28 (@mkChunkCheck_add 0 1 32 4 28 mkCheck_part_0_1_32 (@mkChunkCheck_add 0 1 36 4 24 mkCheck_part_0_1_36 (@mkChunkCheck_add 0 1 40 4 20 mkCheck_part_0_1_40 (@mkChunkCheck_add 0 1 44 4 16 mkCheck_part_0_1_44 (@mkChunkCheck_add 0 1 48 4 12 mkCheck_part_0_1_48 (@mkChunkCheck_add 0 1 52 4 8 mkCheck_part_0_1_52 (@mkChunkCheck_add 0 1 56 4 4 mkCheck_part_0_1_56 (mkCheck_part_0_1_60)))))))))))))))
end SigGolfCandidate.T3M.BC
end
section
namespace SigGolfCandidate.T3M.BC
theorem mkBlockCheck_at (lay ci sh : Nat) (hlay : lay < 4) (hci : ci < mkNch lay) (hsh : sh < 2 ^ mkBits lay ci) :
    mkBlockCheck lay ci sh = true := by
  have hall : ∀ lo n, mkChunkCheck lay ci lo n = true → lo ≤ sh → sh < lo + n → mkBlockCheck lay ci sh = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h sh (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · have hci' : ci < 2 := by simpa [mkNch] using hci
    interval_cases ci
    · exact hall 0 64 mkCheck_00 (by omega) (by simpa [mkBits] using hsh)
    · exact hall 0 64 mkCheck_01 (by omega) (by simpa [mkBits] using hsh)
  all_goals (have hci0 : ci = 0 := by simp [mkNch] at hci; omega); subst hci0
  · have : sh < 128 := by simpa [mkBits, hL] using hsh
    by_cases h64 : sh < 64
    · exact hall 0 64 mkCheck_1a (by omega) (by omega)
    · exact hall 64 64 mkCheck_1b (by omega) (by omega)
  · exact hall 0 64 mkCheck_2 (by omega) (by simpa [mkBits, hL] using hsh)
  · exact hall 0 64 mkCheck_3 (by omega) (by simpa [mkBits, hL] using hsh)
theorem mkEnt_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) : mkEntCheck lay ci sh = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h; exact h.1.1
theorem mkLvl_of {lay ci sh : Nat} (h : mkBlockCheck lay ci sh = true) (kk : Nat) (hkk : kk < mkBits lay ci - (if lay = 0 then 0 else 1)) :
    mkLvlCheck lay ci sh kk = true := by
  simp only [mkBlockCheck, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.2 kk (List.mem_range.mpr hkk)
end SigGolfCandidate.T3M.BC
end

section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
/-! ### Merkle routes (window plans): what a fold still needs and what each write hits
C4: the top route is checked like the lower ones (its plan has two lines, so all 4096 leaves are checked); a top left
child at window slot 0 writes its junk low half at slot -1 (the end of the FTS area), so the `1 ≤ plan` fact is only
claimed for the lower layers, where slot -1 is the layer below. -/
def mkPS (lay : Nat) : Nat := [42,25,20,20].getD lay 0
def mkSib (lay leaf j : Nat) : Nat := plan lay leaf j + 3 * (1 - leaf / 2 ^ j % 2)
def mkCs (lay leaf j : Nat) : Nat := plan lay leaf j + 3 * (leaf / 2 ^ j % 2)
/-- Slots the fold window of level `j` still needs from the witness: the pad and the sibling. -/
def mkKS (lay leaf k : Nat) : List Nat :=
  ((List.range (hL lay)).filter (fun j => decide (k ≤ j))).flatMap (fun j => [plan lay leaf j + 2, mkSib lay leaf j])
/-- C2: slots whose HIGH word (the fold's witness high tweak word) a fold at level `≥ k` still needs. -/
def mkKH (lay leaf k : Nat) : List Nat :=
  ((List.range (hL lay)).filter (fun j => decide (k ≤ j))).map (fun j => plan lay leaf j + 1)
/-- C2: slots written by the hash that produces the level-`j` input (a left node 16 bytes low). -/
def mkWs (lay leaf j : Nat) : List Nat :=
  if leaf / 2 ^ j % 2 = 0 then [plan lay leaf j - 1, plan lay leaf j] else [plan lay leaf j + 3, plan lay leaf j + 4]
def mkRouteOk (lay leaf : Nat) : Bool :=
  (List.range (hL lay)).all (fun k => decide (plan lay leaf k + 4 ≤ mkPS lay ∧
    (lay ≠ 0 → leaf / 2 ^ k % 2 = 0 → 1 ≤ plan lay leaf k))) &&
  (mkKS lay leaf 0 ++ mkKH lay leaf 0).all (fun s => decide (s + 1 ≤ mkPS lay ∧ s ∉ mkWs lay leaf 0)) &&
  (List.range (hL lay - 1)).all (fun k => (mkKS lay leaf (k + 1) ++ mkKH lay leaf (k + 1)).all (fun s =>
    decide (s ≠ plan lay leaf k + 1 ∧ s ∉ mkWs lay leaf (k + 1))))
def mkLowOk : Bool :=
  (List.range 128).all (mkRouteOk 1) && (List.range 64).all (mkRouteOk 2) && (List.range 64).all (mkRouteOk 3)
set_option maxRecDepth 100000 in
theorem mkLowOk_true : mkLowOk = true := by decide +kernel
def mkTopOk (lo n : Nat) : Bool := (List.range' lo n).all (mkRouteOk 0)
theorem mkTopOk_add {lo left right : Nat} (hleft : mkTopOk lo left = true)
    (hright : mkTopOk (lo + left) right = true) : mkTopOk lo (left + right) = true := by
  unfold mkTopOk at *
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl
set_option maxRecDepth 100000
private def need (p d : Nat) : List Nat := [p + 2, p + 3 * (1-d), p+1]
private def writes (p d : Nat) : List Nat := if d=0 then [p-1,p] else [p+3,p+4]
private def pA (r j : Nat) := (topPlanA.getD r []).getD j 0
private def pB (r j : Nat) := (topPlanB.getD r []).getD j 0
private def bit (r j : Nat) := r / 2^j % 2
private theorem checkA : ∀ r < 64,
    (∀ j < 6, 21 ≤ pA r j ∧ pA r j ≤ 38) ∧
    (∀ i < 6, ∀ j < 6, i ≤ j → ∀ s ∈ need (pA r j) (bit r j), s ∉ writes (pA r i) (bit r i)) ∧
    (∀ i < 6, ∀ j < 6, i < j → ∀ s ∈ need (pA r j) (bit r j), s ≠ pA r i + 1) := by
  have h : ∀ r : Fin 64,
    (∀ j : Fin 6, 21 ≤ pA r j ∧ pA r j ≤ 38) ∧
    (∀ i : Fin 6, ∀ j : Fin 6, i ≤ j → ∀ s ∈ need (pA r j) (bit r j), s ∉ writes (pA r i) (bit r i)) ∧
    (∀ i : Fin 6, ∀ j : Fin 6, i < j → ∀ s ∈ need (pA r j) (bit r j), s ≠ pA r i + 1) := by
    simp only [need, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    decide +kernel
  simpa only [Fin.forall_iff, Fin.mk_le_mk, Fin.mk_lt_mk] using h
private theorem checkB : ∀ r < 64,
    (∀ j < 6, pB r j ≤ 16) ∧
    (∀ i < 6, ∀ j < 6, i ≤ j → ∀ s ∈ need (pB r j) (bit r j), s ∉ writes (pB r i) (bit r i)) ∧
    (∀ i < 6, ∀ j < 6, i < j → ∀ s ∈ need (pB r j) (bit r j), s ≠ pB r i + 1) := by
  have h : ∀ r : Fin 64,
    (∀ j : Fin 6, pB r j ≤ 16) ∧
    (∀ i : Fin 6, ∀ j : Fin 6, i ≤ j → ∀ s ∈ need (pB r j) (bit r j), s ∉ writes (pB r i) (bit r i)) ∧
    (∀ i : Fin 6, ∀ j : Fin 6, i < j → ∀ s ∈ need (pB r j) (bit r j), s ≠ pB r i + 1) := by
    simp only [need, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    decide +kernel
  simpa only [Fin.forall_iff, Fin.mk_le_mk, Fin.mk_lt_mk] using h
private theorem bit_low (r j : Nat) (hj : j < 6) : bit r j = bit (r % 64) j := by
  unfold bit
  interval_cases j <;> norm_num <;> omega
private theorem bit_high (r j : Nat) (hj : j < 6) : bit r (6+j) = bit (r / 64 % 64) j := by
  unfold bit
  interval_cases j <;> norm_num <;> omega
private theorem need_bounds (p d s : Nat) (h : s ∈ need p d) : p ≤ s ∧ s ≤ p+3 := by
  simp only [need, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> omega
private theorem plan_low (r j : Nat) (hj : j<6) : plan 0 r j = pA (r%64) j := by
  simp [plan, topPlan, pA, hj]
private theorem plan_high (r j : Nat) (hj : 6≤j) : plan 0 r j = pB (r/64%64) (j-6) := by
  simp [plan, topPlan, pB, show ¬j<6 by omega]
private theorem bit_high' (r j : Nat) (hj : 6≤j) (hj' : j<12) : bit r j = bit (r/64%64) (j-6) := by
  have h := bit_high r (j-6) (by omega)
  simpa only [show 6+(j-6)=j by omega] using h
private theorem plan_bounds (r j : Nat) (hj : j<12) : plan 0 r j ≤ 38 := by
  by_cases h : j<6
  · rw [plan_low r j h]
    exact ((checkA _ (Nat.mod_lt _ (by decide))).1 j h).2
  · rw [plan_high r j (by omega)]
    have := (checkB (r/64%64) (Nat.mod_lt _ (by decide))).1 (j-6) (by omega)
    omega
private theorem separation (r i j s : Nat) (hi : i<12) (hj : j<12) (hij : i≤j)
    (hs : s∈need (plan 0 r j) (bit r j)) :
    s∉writes (plan 0 r i) (bit r i) ∧ (i<j → s≠plan 0 r i + 1) := by
  by_cases ha : i<6
  · by_cases hb : j<6
    · rw [plan_low r j hb, bit_low r j hb] at hs
      rw [plan_low r i ha, bit_low r i ha]
      exact ⟨(checkA _ (Nat.mod_lt _ (by decide))).2.1 i ha j hb hij s hs,
        fun h => (checkA _ (Nat.mod_lt _ (by decide))).2.2 i ha j hb h s hs⟩
    · have hsmall : s≤19 := by
        have hbnd := (need_bounds _ _ _ hs).2
        rw [plan_high r j (by omega)] at hbnd
        have := (checkB (r/64%64) (Nat.mod_lt _ (by decide))).1 (j-6) (by omega)
        omega
      have hlarge : 21≤plan 0 r i := by
        rw [plan_low r i ha]
        exact ((checkA _ (Nat.mod_lt _ (by decide))).1 i ha).1
      constructor
      · intro hw
        simp only [writes] at hw
        split at hw <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;> omega
      · omega
  · have hb : 6≤j := by omega
    rw [plan_high r j hb, bit_high' r j hb hj] at hs
    rw [plan_high r i (by omega), bit_high' r i (by omega) hi]
    exact ⟨(checkB _ (Nat.mod_lt _ (by decide))).2.1 (i-6) (by omega) (j-6) (by omega) (by omega) s hs,
      fun h => (checkB _ (Nat.mod_lt _ (by decide))).2.2 (i-6) (by omega) (j-6) (by omega) (by omega) s hs⟩
private theorem need_mem (r k s : Nat) (hs : s∈mkKS 0 r k ++ mkKH 0 r k) :
    ∃ j, j<12 ∧ k≤j ∧ s∈need (plan 0 r j) (bit r j) := by
  simp only [List.mem_append, mkKS, mkKH, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range, decide_eq_true_eq] at hs
  rcases hs with ⟨j, ⟨hj, hk⟩, hs⟩ | ⟨j, ⟨hj,hk⟩, hs⟩
  · refine ⟨j, hj, hk, ?_⟩
    simpa only [need, mkSib, bit, List.mem_cons, List.not_mem_nil, or_false] using
      (show s=plan 0 r j+2 ∨ s=mkSib 0 r j ∨ s=plan 0 r j+1 from by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
  · refine ⟨j,hj,hk,?_⟩
    simp only [need, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr hs.symm)
private theorem route_fast (r : Nat) : mkRouteOk 0 r = true := by
  simp only [mkRouteOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro k hk
    refine ⟨?_, by simp⟩
    have h := plan_bounds r k hk
    change plan 0 r k+4 ≤42
    omega
  · intro s hs
    obtain ⟨j,hj,_,hsj⟩ := need_mem r 0 s hs
    constructor
    · have h := (need_bounds _ _ _ hsj).2
      have hp := plan_bounds r j hj
      change s+1≤42
      omega
    · exact (separation r 0 j s (by decide) hj (Nat.zero_le _) hsj).1
  · intro k hk s hs
    obtain ⟨j,hj,hkj,hsj⟩ := need_mem r (k+1) s hs
    exact ⟨(separation r k j s (by change k<12; change k<12-1 at hk; omega)
      hj (by omega) hsj).2 (by omega),
      (separation r (k+1) j s (by omega) hj hkj hsj).1⟩

theorem mkTopOk_all : mkTopOk 0 4096 = true := by
  exact List.all_eq_true.mpr (fun leaf _ => route_fast leaf)
theorem mkTop_route (leaf : Nat) (hleaf : leaf < 4096) : mkRouteOk 0 leaf = true :=
  List.all_eq_true.mp mkTopOk_all leaf (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
end SigGolfCandidate.T3M
end
end
-- ==== merged from T3M_Verify_LayerLower ====
section

set_option Elab.async false
set_option maxRecDepth 100000

section


section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
namespace LCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
def lowP (c : LCtx) : M (List Digest) := (List.range' 0 42).foldlM c.chainF [] >>= fun e => c.chainF e 42
def lowCost (c : LCtx) : Nat := c.chainsCost 0 42 + chainCost 42 c.ck
theorem lower_good (c : LCtx) (hc : c.ok) (hi0 : c.i0 = 0) (hko : c.koff = 0) (hck : c.ck < 8) (hRanks : ∀ j, j < 42 → c.headOK j) {s0 : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (h0 : c.Orig0 s0)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → Verify.GoodQP P t N C Q A (K ends))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Verify.GoodQP P s (N + 1720) (C + c.lowCost) Q (A + c.lowCost) (Verify.ccM c.lowP K) := by
  unfold lowP
  rw [Verify.ccM_bind]
  have H := c.chains_good hc hk h0 (fun _ => hko) 42 (by omega) (fun j _ hj => hRanks j hj) (fun e => Verify.ccM (c.chainF e 42) K)
    (N + 40) (C + chainCost 42 c.ck) (A + chainCost 42 c.ck) Q
    (fun ends t ht => c.ck_good hc hk h0 (fun _ => hko) hck K N C A Q hK ends t ht) 42 0 (by omega) (by omega) [] s hs
  refine H.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
  · unfold lowCost; omega
  · unfold lowCost; omega
/-- The image's projected hash is the spec's `WCT9.halfHash`. -/
theorem vHash_eq_halfHash (high : Bool) (input : List UInt8) :
    Verify.vHash high input = ClaudeWCT.WCT9.halfHash high input := by
  rw [ClaudeWCT.WCT9.halfHash_eq]; unfold Verify.vHash; cases high <;> rfl
/-- C3: on a lower layer (`koff = 0`) the image's chain run is the spec's `chainPW` (chain 0's last step high). -/
theorem rest_chainPW (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (i d : Nat) (v : Digest) :
    c.rest i d v = ClaudeWCT.W9.T3M.chainPW c.lay c.tree c.leaf i d (7 - d) (c.pad0 i) (c.pad1 i) (c.padHeader i) v := by
  unfold LCtx.rest ClaudeWCT.W9.T3M.chainPW
  rw [hko, Nat.add_zero]
  congr 1
  funext v step
  rw [vHash_eq_halfHash, chainInputL_eq _ hlay]
  congr 1
  unfold LCtx.stepHigh ClaudeWCT.WCT9.chainHigh lowerG
  by_cases h6 : step = 6 <;> by_cases h0 : i = 0 <;> simp [h6, h0, hlay]
def coreChain (c : LCtx) (D : List Nat) (i : Nat) : M Digest :=
  ClaudeWCT.W9.T3M.chainPW c.lay c.tree c.leaf i (D.getD i 0) (maxDigit c.lay i - D.getD i 0)
    (ClaudeWCT.W9.T3M.wchainPads c.w c.lay i).1 (ClaudeWCT.W9.T3M.wchainPads c.w c.lay i).2
    (ClaudeWCT.W9.T3M.wchainHeaderPad c.w c.lay i) (ClaudeWCT.W9.T3M.wvalueFor c.w c.lay D i)
theorem fit_chain (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hS6 : c.S6 = Verify.WIT + ClaudeWCT.W9.T3M.layerBase c.lay + 16 * ClaudeWCT.W9.T3M.pathSlots c.lay + 520)
    (i : Nat) (hi : i < 43) :
    c.rest i (c.dig i) (c.bufferVal i) = c.coreChain D i := by
  rw [c.rest_chainPW hlay hko]
  unfold coreChain
  have hw : maxDigit c.lay i = 7 := by simp [maxDigit, hlay]
  rw [← hD i hi, hw, c.bufferVal_eq hlay D hD hS6 i hi]
  have e : c.blk i - Verify.WIT = ClaudeWCT.W9.T3M.chainBlock c.lay i := by
    unfold blk ClaudeWCT.W9.T3M.chainBlock; rw [chainSlot_lower hlay, hS6]; omega
  have hg : ClaudeWCT.WCT9.isG c.lay i = lowerG i := by simp [ClaudeWCT.WCT9.isG, lowerG, hlay]
  unfold pad0 pad1 pad0At pad1At padHeader ClaudeWCT.W9.T3M.wchainPads ClaudeWCT.W9.T3M.wchainHeaderPad
    ClaudeWCT.W9.T3M.pad0Off ClaudeWCT.W9.T3M.pad1Off
  rw [hg, show c.blk i + (if lowerG i then 32 else 0) - Verify.WIT = c.blk i - Verify.WIT + (if lowerG i then 32 else 0)
      by unfold blk; rw [hS6]; unfold Verify.WIT; omega,
    show c.blk i + (if lowerG i then 48 else 32) - Verify.WIT = c.blk i - Verify.WIT + (if lowerG i then 48 else 32)
      by unfold blk; rw [hS6]; unfold Verify.WIT; omega,
    show c.blk i - Verify.WIT + 24 = ClaudeWCT.W9.T3M.chainBlock c.lay i + 16 + 8 by omega, e, wdig_hi]
theorem lowP_eq (c : LCtx) (hlay : c.lay ≠ 0) (hko : c.koff = 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hS6 : c.S6 = Verify.WIT + ClaudeWCT.W9.T3M.layerBase c.lay + 16 * ClaudeWCT.W9.T3M.pathSlots c.lay + 520) :
    c.lowP = (List.finRange 43).mapM fun i => c.coreChain D i.val := by
  rw [finRange_mapM, List.range_eq_range', show (43 : Nat) = 42 + 1 from rfl, List.range'_append_1.symm,
    List.mapM_append]
  unfold lowP
  have hF : (List.range' 0 42).foldlM c.chainF [] = (fun l => [] ++ l) <$> (List.range' 0 42).mapM
      (fun i => c.rest i (c.dig i) (c.bufferVal i)) :=
    foldlM_app_mapM _ 42 0 []
  rw [hF, mapM_congr' (List.range' 0 42) (fun i hi => c.fit_chain hlay hko D hD hS6 i (by
    have := List.mem_range'_1.mp hi; omega))]
  have h42 := c.fit_chain hlay hko D hD hS6 42 (by omega)
  unfold chainF
  rw [h42]
  simp [List.range'_one]
theorem lowCost_accept (c : LCtx) (hck : c.ck < 8) (D : List Nat) (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hl : D.length = 43) (T : Nat) (hT : D.sum = T) : c.lowCost + c.zSum 0 43 + 9 * T + 4*c.savedCopies 0 43 = 2935 := by
  have := c.chainsCost_lower hck T (by rw [c.sum_dig D hD hl, hT])
  unfold lowCost
  omega
end LCtx
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
theorem geomL (lay : Layer) (h : lay ≠ 0) :
    s6v lay.val = 4128 + ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay + 520 ∧
      ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay + 2248 ≤ layerEnd lay.val ∧
      7664 ≤ ClaudeWCT.W9.T3M.layerBase lay ∧ layerEnd lay.val < 18929 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
/-- C2 (FULL): the per-leaf blocks start one word later (entry offset 16). -/
theorem lfS7_pc (lay : Layer) (hlay : lay ≠ 0) (leaf : Nat) (hl : leaf < 2 ^ hL lay.val) :
    (BitVec.ofNat 64 (lfS7 lay.val leaf) + 16) &&& ~~~1#64 = pcOf (stabW lay.val (leaf % 2 ^ stabBits lay.val)) := by
  have e : lfS7 lay.val leaf + 16 = 0x1000 + 4 * stabW lay.val (leaf % 2 ^ stabBits lay.val) := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals
      simp only [lfS7, dispatchHeap, s7Bias, s7Sh, stabW, stabBits, hL] at hl ⊢
      norm_num at hl ⊢
      rw [Nat.mod_eq_of_lt hl]
      omega
  rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat, e, even_andNot1' _ (by omega)]
theorem leafL_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0)
    (hidx : index < 2 ^ 31) (a : BitVec 256) (s0 : MachineState)
    (hk : ∀ p ∈ (lctxOf w index lay a).known, s0.getReg p.1 = p.2) (hck : (lctxOf w index lay a).ck < 8)
    (hG : Glob (chainK lay.val) w pk s0) (hO : Verify.Orig w (fun o => 7664 ≤ o ∧ o < layerEnd lay.val) s0)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (lfS7 lay.val (route index lay).1))
    (h30 : s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (h1 : s0.getReg .x2 = BitVec.ofNat 64 0xffbde0)
    (hBuffer : Verify.Orig w (fun o => BC.bufferStart lay.val ≤ o ∧ o < 21984) s0)
    (ends : List Digest) (t : MachineState)
    (ht : (lctxOf w index lay a).ChainOut s0 43 ends t) :
    ∃ u, Steps image t 4 4 u ∧ LeafOut w pk index lay ends u := by
  set L := lctxOf w index lay a with hLd
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := ht
  have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := hG.1
  have hknown : KnownOK (leafK lay.val) t := by
    intro p hp
    simp only [leafK, gkL_low h0, baseK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ((rfl | rfl) | rfl | rfl) | rfl
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x18 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x7 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
    · rw [hR .x5 (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK, baseK])
    · rw [hR .x4 (by simp [chainRegs])]
      exact hkL (.x4, _) (by simp [chainK])
  have hBias : L.bufferOffset = bufferBias lay.val := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals rfl
  have hBB : bufferBase lay.val = bufferBias lay.val + 768 := by
    fin_cases lay
    · exact absurd rfl hlay
    all_goals rfl
  have hBb : bufferBase lay.val % 8 = 0 ∧ 23056 ≤ bufferBase lay.val ∧ bufferBase lay.val ≤ 25216 := by
    fin_cases lay <;> decide +kernel
  have hBi : 22288 ≤ bufferBias lay.val ∧ bufferBias lay.val ≤ 24704 := by fin_cases lay <;> decide +kernel
  obtain ⟨u, hu⟩ := spec_run (lfSlotCheck_at lay.val L.ck h0 lay.isLt hck) t (by rw [hpc]; rfl) hknown
    (by intro b hb; simp [specLf, h0] at hb) (by simp)
  have hst := hu.steps
  rw [show (specLf lay.val).steps = 4 by simp [specLf, h0],
    show (specLf lay.val).cycles = 4 by simp [specLf, h0]] at hst
  refine ⟨u, hst, ?_⟩
  have hku : KnownOK (postLf lay.val) u := hu.known
  have hkeep := hu.keep
  have hmem : ∀ A, u.getMem A = memEval t [(⟨none, BitVec.ofNat 64 (bufferBase lay.val+16)⟩, .reg .x28)] A := by
    intro A; rw [hu.mem]; simp [specLf, h0]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ bufferBase lay.val+24 → A ≠ bufferBase lay.val+16 → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA _ h2
    rw [hmem]
    apply memEval_frame_ofNat t _ A hA
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    simp; omega
  have htr := tree_lt index lay hidx
  have hlf := leaf_lt index lay
  obtain ⟨hg1, hg2, hg3, hg4⟩ := geomL lay hlay
  have hS6 : L.S6 = s6v lay.val := rfl
  refine ⟨?_, ?_, fun h => absurd h hlay, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.spc (tgtLf lay.val) (by simp [specLf, h0])]
    simp only [tgtLf, if_neg h0, E.eval, BinOp.eval, addC_eval]
    rw [hR .x23 (by simp [chainRegs]), h23]
    exact lfS7_pc lay hlay _ hlf
  · have hGt : Glob baseK w pk t := glob_frame hG hF (fun A hA => by
        replace hA := L.Wr_range (by omega) hA
        unfold LCtx.bufferEnd LCtx.bufferSlot at hA; rw [hS6, hBias] at hA
        have : slotL L.i0 = 768 := rfl
        rw [this] at hA
        simp only [show L.i0 = 0 from rfl, slotL, if_neg (by omega : ¬43=0), if_pos rfl] at hA
        split_ifs at hA <;> rcases hA with hA | hA <;> omega)
      (fun p hp => hknown p (by simp [leafK, gkL_low h0, hp]))
    have hGu := hu.glob _ w pk hGt (RelOK.nil t)
    refine ⟨fun p hp => ?_, hGu.2.1, hGu.2.2.1, hGu.2.2.2.1, hGu.2.2.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hku p hp
    · have h22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) :=
        hk (.x22, BitVec.ofNat 64 L.S6) (by simp [LCtx.known])
      have m6 : ((.x7 : Reg), (1 : Word)) ∈ postLf lay.val := by
        simp [postLf, leafK, h0]
      simp only [lfKeepK, if_neg h0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
      all_goals first
        | exact hku _ m6
        | rw [hkeep _ (by simp [keepLfL]), hR _ (by simp [chainRegs])]; exact h22
        | rw [hkeep _ (by simp [keepLfL]), hR _ (by simp [chainRegs])]; exact h1
        | rw [hkeep _ (by simp [keepLfL]), hR _ (by simp [chainRegs])]; exact hkL (_, _) (by simp [chainK])
  · intro _; rw [hkeep .x31 (by simp [keepLfL]), hR .x31 (by simp [chainRegs]), h30]
  · rw [hlen, LCtx.chainCount_lower lay hlay]; rfl
  · intro j hj
    rw [LCtx.chainCount_lower lay hlay] at hj
    have e := hS j (by rw [hlen]; exact hj)
    have hj0 : slotL (L.i0 + j) = slotL j := by rw [show L.i0 = 0 from rfl, Nat.zero_add]
    simp only [LCtx.bufferSlot, hBias, hj0] at e
    simp only [lfSlot, if_neg h0]
    have hsl : slotL j = 768 ∨ 800 ≤ slotL j := by unfold slotL; split <;> omega
    have hsl' : slotL j < 2 ^ 32 := by unfold slotL; split <;> omega
    exact ⟨(hfr (bufferBias lay.val + slotL j) (by omega) (by omega) (by omega)).trans e.1,
      (hfr (bufferBias lay.val + slotL j + 8) (by omega) (by omega) (by omega)).trans e.2⟩
  · rw [show lfBase lay.val + 16 = bufferBase lay.val+16 from rfl, hmem,
      memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
    simp only [E.eval]
    rw [hR .x28 (by simp [chainRegs]), hk (.x28, BitVec.ofNat 64 L.x28v) (by simp [LCtx.known]), routed_eq,
      show below lay.val = BC.below lay.val from rfl, ← hyperWord_x28v w index lay a]
    rfl
  · -- C3: the leaf tweak's high word is witness memory (no chain or setup write reaches it)
    have hlb : ClaudeWCT.W9.T3M.leafBufferBase lay = bufferBase lay.val - WIT := by
      fin_cases lay
      · exact absurd rfl hlay
      all_goals rfl
    have hbs : BC.bufferStart lay.val = ClaudeWCT.W9.T3M.leafBufferBase lay := by
      fin_cases lay
      · exact absurd rfl hlay
      all_goals rfl
    have hu24 : u.getMem (BitVec.ofNat 64 (bufferBase lay.val + 24)) =
        t.getMem (BitVec.ofNat 64 (bufferBase lay.val + 24)) := by
      rw [hmem]; apply memEval_frame_ofNat t _ _ (by omega)
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl; simp; omega
    have ht24 : t.getMem (BitVec.ofNat 64 (bufferBase lay.val + 24)) =
        s0.getMem (BitVec.ofNat 64 (bufferBase lay.val + 24)) := by
      apply hF.get (by omega)
      intro hw
      have hb0 := L.bufferBound_slot
      have hs0 : L.bufferSlot 0 = bufferBase lay.val := by
        unfold LCtx.bufferSlot; rw [hBias, hBB]; rfl
      have hs1 : L.bufferSlot 1 = L.bufferSlot 0 + 32 := by unfold LCtx.bufferSlot slotL; simp
      have hi0 : L.i0 = 0 := rfl
      replace hw := L.Wr_range (by omega) hw
      rw [hi0] at hw
      have harea := L.bufferArea_slot
      omega
    have hw := (hBuffer.mono (fun o (ho : o = bufferBase lay.val - WIT + 24) => ⟨by rw [ho, ← hlb, ← hbs]; omega,
      by rw [ho]; unfold WIT; omega⟩)).hi (bufferBase lay.val - WIT + 16) (by unfold WIT; omega)
      (by unfold WIT WX; omega) (by omega)
    rw [show lfBase lay.val + 24 = bufferBase lay.val+24 from rfl, hu24, ht24,
      show bufferBase lay.val + 24 = WIT + (bufferBase lay.val - WIT + 16) + 8 by unfold WIT; omega, hw]
    unfold ClaudeWCT.W9.T3M.wleafHigh; rw [hlb]
  · have hOt : Verify.Orig w (fun o => 7664 ≤ o ∧
        o < ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay) t :=
      (hO.mono (fun o ho => ⟨ho.1, by omega⟩)).frame (fun j hj hp => hF.get (by unfold WIT WX at *; omega)
        (fun hw => by
          replace hw := L.Wr_range (by omega) hw
          unfold LCtx.bufferEnd LCtx.bufferSlot at hw; rw [hS6, hBias] at hw
          simp only [show L.i0 = 0 from rfl, slotL, if_neg (by omega : ¬43=0), if_pos rfl] at hw
          unfold WIT at hw
          split_ifs at hw <;> rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hOt).mono (fun o ho => ⟨ho, by simp only [lfAllowed, List.mem_cons, List.not_mem_nil, or_false]; unfold WIT; omega⟩)
  · intro hLay
    have hfut : BC.bufferStart lay.val ≤ BC.bufferStart (lay.val-1) ∧
        bufferBase lay.val + 720 ≤ WIT + BC.bufferStart (lay.val-1) ∧
        s6v lay.val - 520 + 2264 ≤ WIT + BC.bufferStart (lay.val-1) := by
      fin_cases lay
      · exact absurd rfl hlay
      all_goals decide +kernel
    have hBt : Verify.Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 21984) t :=
      (hBuffer.mono (fun o ho => ⟨by omega,ho.2⟩)).frame (fun j hj hp =>
        hF.get (by unfold WIT WX at *; omega) (fun hw => by
          replace hw := L.Wr_range (by omega) hw
          unfold LCtx.bufferEnd LCtx.bufferSlot at hw
          rw [hS6,hBias] at hw
          simp only [show L.i0=0 from rfl, slotL, if_neg (by omega : ¬43=0), if_pos rfl] at hw
          unfold WIT at *
          split_ifs at hw <;> rcases hw with hw | hw <;> omega))
    exact (hu.orig_const hBt).mono (fun o ho => ⟨ho, by
      simp only [lfAllowed,List.mem_cons,List.not_mem_nil,or_false]
      unfold WIT at *; omega⟩)
end SigGolfCandidate.T3M
end
end

section

section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route height)
theorem plan_eq : planL1 = ClaudeWCT.W9.T3M.lowerPlanL1 ∧ planL32 = ClaudeWCT.W9.T3M.lowerPlanL32 := ⟨rfl, rfl⟩
set_option maxRecDepth 100000 in
theorem rowA_tab : ∀ lay : Fin 3, ∀ c < 2 ^ hL (lay.val + 1),
    rowA lay.val c = WIT + ClaudeWCT.W9.T3M.merkleBlock (ClaudeWCT.W9.T3M.upLayer lay.castSucc) c
      (height (ClaudeWCT.W9.T3M.upLayer lay.castSucc) - 1) := by decide +kernel
theorem upLayer_val (lay : Layer) (h3 : lay.val ≠ 3) : (ClaudeWCT.W9.T3M.upLayer lay).val = lay.val + 1 := by
  unfold ClaudeWCT.W9.T3M.upLayer; simp only [Fin.val_ofNat]; have := lay.isLt; omega
theorem cpIdx_route (index : Nat) (lay : Layer) (h3 : lay.val ≠ 3) :
    BC.cpIdx index lay.val = (route index (ClaudeWCT.W9.T3M.upLayer lay)).1 := by
  rw [route_fst, upLayer_val lay h3]; unfold BC.cpIdx; rw [if_neg h3]; rfl
theorem rowA_eq (index : Nat) (lay : Layer) (h3 : lay.val ≠ 3) :
    rowA lay.val (BC.cpIdx index lay.val) = WIT + ClaudeWCT.W9.T3M.rowBlock index lay := by
  have hl := leaf_lt index (ClaudeWCT.W9.T3M.upLayer lay)
  rw [upLayer_val lay h3] at hl
  rw [cpIdx_route index lay h3]
  unfold ClaudeWCT.W9.T3M.rowBlock; rw [if_neg h3]
  have := lay.isLt
  obtain ⟨l, hl3⟩ := lay
  have hl3' : l < 3 := by simp at h3; omega
  exact rowA_tab ⟨l, hl3'⟩ _ hl
theorem rowBlock_mod8 (index : Nat) (lay : Layer) : ClaudeWCT.W9.T3M.rowBlock index lay % 8 = 0 := by
  by_cases h3 : lay.val = 3
  · unfold ClaudeWCT.W9.T3M.rowBlock; rw [if_pos h3]
  · have e := rowA_eq index lay h3
    obtain ⟨r16, -⟩ := rowA_facts lay.val (BC.cpIdx index lay.val) (by have := lay.isLt; omega)
      (cpIdx_lt index lay.val lay.isLt)
    unfold WIT at e; omega
theorem hdrA_eq (l : Nat) (hl : l < 4) : hdrA l = hdrAddr l := by
  interval_cases l <;> decide +kernel
theorem hyper_or (lay r : Nat) (hl : lay < 4) (hr : r < 2 ^ 32) :
    BitVec.ofNat 64 (hyperBase lay) ||| BitVec.ofNat 64 (r * 2 ^ 16) = T3.hyperWord lay r := by
  have e1 : BitVec.ofNat 64 (hyperBase lay) =
      BitVec.ofNat 64 ((lay + 193 * 256) * 2 ^ 48) ||| BitVec.ofNat 64 0x201 := by
    rw [ofNat_or_add 0x201 (lay + 193 * 256) 48 (by norm_num)]; unfold hyperBase; apply congrArg (BitVec.ofNat 64); ring
  rw [e1, BitVec.or_assoc, BitVec.or_comm (BitVec.ofNat 64 0x201), ofNat_or_add 0x201 r 16 (by norm_num),
    ofNat_or_add (r * 2 ^ 16 + 0x201) (lay + 193 * 256) 48 (by omega)]
  unfold T3.hyperWord
  rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : lay < 256)]
  apply congrArg (BitVec.ofNat 64)
  ring
theorem rowTweak_lo (lay : Layer) (tree leaf : Nat) :
    dlo (T3.rowTweak lay tree leaf) = T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) :=
  BitVec.extractLsb'_append_eq_right
theorem rowTweak_hi (lay : Layer) (tree leaf : Nat) : dhi (T3.rowTweak lay tree leaf) = 1#64 :=
  BitVec.extractLsb'_append_eq_left
/-- C3 (FULL): the row tweak's high word `hi` is read from memory (a witness pad, honest 1). -/
theorem row_hash (t : MachineState) (A : Nat) (hA8 : A % 8 = 0) (hA : A + 64 < 2 ^ 64) (lay : Layer)
    (tree leaf : Nat) (left right cp : Digest) (hi : BitVec 64) (h10 : t.getReg .x10 = BitVec.ofNat 64 A)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (h0 : DigAt t A left)
    (h2 : t.getMem (BitVec.ofNat 64 (A + 16)) = T3.hyperWord lay.val (tree * 2 ^ height lay + leaf))
    (h3 : t.getMem (BitVec.ofNat 64 (A + 24)) = hi) (h4 : t.getMem (BitVec.ofNat 64 (A + 32)) = dlo cp)
    (h5 : t.getMem (BitVec.ofNat 64 (A + 40)) = dhi cp) (h6 : DigAt t (A + 48) right) :
    hashInput t = toQ (T3.pad64 (blk4 left (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) cp right)) := by
  rw [pad64_blk4]
  apply hashInput_words8 t _ A (blk4_length _ _ _ _) h10 hA8 hA h11
  rw [wordsOf_blk4, show dlo (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) =
      T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) from BitVec.extractLsb'_append_eq_right,
    show dhi (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) = hi from BitVec.extractLsb'_append_eq_left,
    h0.1, h0.2, h2, h3, h4, h5, h6.1,
    show A + 48 + 8 = A + 56 by omega] at *
  all_goals (try rw [h6.2])
  all_goals (try rfl)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route height counterLimit encodingInput pad64)
open ClaudeWCT.WCT9 (LayerMsg)
def CounterEval : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  (ctrE lay.val (cpIdx index lay.val)).eval s = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat
theorem counter_eval : CounterEval := fun w pk index lay msg s hs => by
  by_cases h3 : lay.val = 3
  case neg =>
    cases msg with
    | forest root => exact hs.msg.elim
    | pair left right =>
      have hm := (hs.msg.pair_low h3).2.2.2 4 (Or.inr (Or.inl rfl))
      simp only [ctrE, if_neg h3, E.eval, kw, UnOp.eval, hm]
      rw [counterWord]
      have e := T3M.rowA_eq index lay h3
      have h8 := T3M.rowBlock_mod8 index lay
      unfold ClaudeWCT.W9.T3M.wbcCtr ClaudeWCT.W9.T3M.bcCounterOff
      rw [show 8 * ((rowA lay.val (cpIdx index lay.val) - WIT) / 8 + 4) =
        ClaudeWCT.W9.T3M.rowBlock index lay + 32 by rw [e]; unfold WIT; omega]
  case pos =>
    obtain rfl : lay = 3 := Fin.ext h3
    exact T3M.ctrE_eval w index s hs.glob.2.1
/-- The verify machine's encoding-counter branch compares against its literal `0x400000 = 2^22` (independent of the
scheme's search windows `T3.counterLimit` / `WCT9.searchLimit`). -/
def CounterBranch : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ d, Br.holds s (ctrBr lay.val (cpIdx index lay.val) d) ↔
    d = decide (if lay.val = 3 then (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < 2 ^ 22
      else (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ 2 ^ 22)
theorem counter_branch : CounterBranch := fun w pk index lay msg s hs d => by
  have h64 : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < 2 ^ 64 :=
    lt_of_lt_of_le (ClaudeWCT.W9.T3M.wbcCtr w index lay).isLt (by decide +kernel)
  norm_num at h64
  unfold ctrBr Br.holds
  rw [counter_eval w pk index lay msg s hs]
  by_cases h3 : lay.val = 3 <;>
    simp [h3, CmpOp.eval, E.eval, kw, BitVec.ult, Nat.mod_eq_of_lt h64,
      ← decide_not, eq_comm]
theorem encoding_reject (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState) (_hs : LayerIn w pk index lay.val msg s)
    (hge : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow) :
    ∃ u, Steps image s (rejectSteps lay.val) (rejectSteps lay.val) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1 :=
  absurd hge (ClaudeWCT.WCT9.ctr_not_ge_verifyWindow _)
def PairInputBlock : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (tree leaf : Nat)
  (left right : Digest) (hi : BitVec 64), ClaudeWCT.WCT9.pairEncodingInputH lay tree leaf left right
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) hi =
  blk4 left (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf))
    (ClaudeWCT.W9.T3M.wdig w (ClaudeWCT.W9.T3M.bcCounterOff index lay)) right
theorem pair_input_block : PairInputBlock := fun w index lay tree leaf left right hi => by
  unfold ClaudeWCT.WCT9.pairEncodingInputH blk4
  simp only [List.append_assoc]
  rw [← List.append_assoc (SphincsSecurity.bytesLE 4 (ClaudeWCT.W9.T3M.wbcCtr w index lay)), counterPadBytes]
  rw [show ClaudeWCT.W9.T3M.wbcPad w index lay ++ ClaudeWCT.W9.T3M.wbcCtr w index lay =
    ClaudeWCT.W9.T3M.wdig w (ClaudeWCT.W9.T3M.bcCounterOff index lay) from counterPadExtract w _]
def EncodingRun : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < ClaudeWCT.WCT9.verifyWindow →
  ∃ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] (setupGk lay.val) (specA lay.val (cpIdx index lay.val))
      (bKS lay.val (cpIdx index lay.val)) (keepA lay.val) s t
theorem encoding_run : EncodingRun := fun w pk index lay msg s hs _ => by
  have hcc := (T3M.copy_parts lay.val (cpIdx index lay.val)
    (copyCheck_at lay.val _ lay.isLt (T3M.cpIdx_lt index lay.val lay.isLt))).1
  have hbrs : (specA lay.val (cpIdx index lay.val)).brs = [] := by
    fin_cases lay <;> rfl
  exact spec_run hcc s hs.copy hs.glob.1 (by rw [hbrs]; simp) (by simp)
theorem t3E3_eval (s : MachineState) (index : Nat) (hidx : index < 2 ^ 31)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hm : s.getMem (BitVec.ofNat 64 (TOPLOAD + 32)) = BitVec.ofNat 64 (hyperBase 3)) :
    t3E3.eval s = T3.hyperWord 3 index := by
  simp only [t3E3, E.eval, BinOp.eval, kw, h22]
  rw [show hdrA 3 = TOPLOAD + 32 from rfl, hm, ofNat_shl',
    show (16 : Nat) % 2 ^ 64 % 64 = 16 by norm_num]
  exact hyper_or 3 index (by norm_num) (by omega)
def SetupPost : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] (setupGk lay.val) (specA lay.val (cpIdx index lay.val))
    (bKS lay.val (cpIdx index lay.val)) (keepA lay.val) s t → EncPre w pk index lay.val (cpIdx index lay.val) t
theorem setup_writes_bounds (lay c : Nat) (hl : lay < 4) (hc : c < nCopy lay) :
    ∀ A ∈ allowed lay c, (A < WIT+7664 ∨ WIT+layerEnd lay ≤ A) ∧ A < WIT+bufferStart lay := by
  have H : ((List.range 4).all fun l => (List.range (nCopy l)).all fun c =>
    (allowed l c).all fun A => decide ((A < WIT+7664 ∨ WIT+layerEnd l ≤ A) ∧ A < WIT+bufferStart l)) = true := by
    decide +kernel
  intro A hA
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp H lay
    (List.mem_range.mpr hl)) c (List.mem_range.mpr hc)) A hA)
/-- C4 (D7): the L3 block's run starts without `x18`; its `ld s2,-304(s1)` restores `x18 = 0xFFF` from `d0`. -/
theorem setup_known (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (msg : LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val msg s) (t : MachineState)
    (ht : SpecRes (allowed lay.val (cpIdx index lay.val)) [] (setupGk lay.val) (specA lay.val (cpIdx index lay.val))
      (bKS lay.val (cpIdx index lay.val)) (keepA lay.val) s t) :
    KnownOK (bK lay.val (cpIdx index lay.val)) t := by
  intro p hp
  by_cases h3 : lay.val = 3
  · obtain rfl : lay = 3 := Fin.ext h3
    rcases p with ⟨r, v⟩
    by_cases h18 : r = .x18
    · subst h18
      have hv : v = 0xFFF := by
        simp [bK, T3M.bK, layK, baseK] at hp; exact hp
      subst hv
      rw [ht.regs (.x18, x18E3) (by simp [specA, T3M.specA])]
      exact hs.d0 rfl
    · exact ht.known _ (by
        simp only [bKS, if_pos (show (3 : Layer).val = 3 from rfl)]
        exact List.mem_filter.mpr ⟨hp, by simpa using h18⟩)
  · exact ht.known p (by simp only [bKS, if_neg h3]; exact hp)
theorem setup_post : SetupPost := fun w pk index lay msg s hs t ht => by
  obtain ⟨hlE, htE, -, hs7E⟩ := T3M.route_evals index lay hs.idx s hs.route
  refine ⟨?_, ⟨setup_known w pk index lay msg s hs t ht, (ht.glob _ w pk hs.glob (RelOK.nil s)).2⟩, ?_, ?_, ?_,
    (ht.orig_const hs.orig).mono (fun o ho => ⟨ho, by
      intro hm
      have H := setup_writes_bounds lay.val _ lay.isLt (T3M.cpIdx_lt index lay.val lay.isLt) _ hm
      rcases H.1 with H | H <;> omega⟩), ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 => fin_cases lay <;> exact ht.pc rfl
  case refine_2 =>
    by_cases h3 : lay.val = 3
    · obtain rfl : lay = 3 := Fin.ext h3
      rw [ht.regs (.x28, t3E3) (by simp [specA, T3M.specA])]
      have h22 : s.getReg .x22 = BitVec.ofNat 64 index := by
        simpa [rReg, below] using hs.route
      rw [t3E3_eval s index hs.idx h22 (hs.hdr3 rfl).1, show below (3 : Layer).val = 0 from rfl, pow_zero,
        Nat.div_one]
      try rfl
    · rw [ht.keep .x28 (by fin_cases lay <;> simp_all [keepA])]
      exact hs.word (by have := lay.isLt; omega)
  case refine_3 =>
    intro L hL hl3
    obtain rfl : L = lay := Fin.ext hL
    have h3 : L.val ≠ 3 := by omega
    exact (ht.regs (.x23, s7E L.val) (by fin_cases L <;> simp_all [specA, T3M.specA])).trans hs7E
  case refine_4 =>
    intro L hL
    obtain rfl : L = lay := Fin.ext hL
    refine ⟨fun h0 hl3 => ?_, fun h0 => ?_⟩
    · have h3 : L.val ≠ 3 := by omega
      exact (ht.regs (.x31, treeE L.val) (by fin_cases L <;> simp_all [specA, T3M.specA])).trans htE
    · obtain rfl : L = 0 := Fin.ext h0
      rw [ht.keep .x31 (by simp [keepA])]
      simpa [leafE, E.eval] using hlE
  case refine_5 =>
    intro h3
    obtain rfl : lay = 3 := Fin.ext h3
    have hm (A : Word) : t.getMem A = memEval s (T3M.specA 3 (trPc 3 (cpIdx index 3))).mem A := ht.mem A
    have hf (A : Nat) (hA : A < 2 ^ 64) (h1 : A ≠ 4144) (h3 : A ≠ 4176) (h4 : A ≠ 4184) :
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl <;> simp <;> omega
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega)]
      exact (hs.hdr3 rfl).1
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega)]
      exact (hs.hdr3 rfl).2.1
    · rw [hf _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)
        (by unfold TOPLOAD; omega)]
      exact (hs.hdr3 rfl).2.2 k hk
  case refine_6 =>
    intro h3
    obtain rfl : lay = 3 := Fin.ext h3
    exact (ht.keep .x22 (by simp [keepA])).trans (by simpa [rReg, below] using hs.route)
  case refine_7 =>
    intro hl3
    obtain ⟨d, hd, hdd⟩ := hs.dst hl3
    refine ⟨d, ?_, hdd⟩
    have h3 : lay.val ≠ 3 := by omega
    rw [ht.regs (.x12, .reg .x12) (by fin_cases lay <;> simp_all [specA])]
    simpa [E.eval] using hd
  case refine_8 =>
    exact (ht.orig_const hs.bufferOrig).mono (fun o ho => ⟨ho, by
      intro hm
      have H := (setup_writes_bounds lay.val _ lay.isLt (T3M.cpIdx_lt index lay.val lay.isLt) _ hm).2
      omega⟩)
  case refine_9 =>
    intro h3
    obtain rfl : lay = 3 := Fin.ext h3
    rw [ht.regs (.x12, .reg .x12) (by simp [specA, T3M.specA])]
    simpa [E.eval] using hs.dst3 rfl
def SetupHash : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
  (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ∀ t, SpecRes (allowed lay.val (cpIdx index lay.val)) [] (setupGk lay.val) (specA lay.val (cpIdx index lay.val))
    (bKS lay.val (cpIdx index lay.val)) (keepA lay.val) s t →
  t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
  hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
    (route index lay).2 (route index lay).1 msg
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)
    (ClaudeWCT.W9.T3M.wbcHigh w index lay)))
theorem setup_hash : SetupHash := fun w pk index lay msg s hs t ht => by
  have hpost := setup_post w pk index lay msg s hs t ht
  have hkB := setup_known w pk index lay msg s hs t ht
  have h5 : t.getReg .x5 = 0 := hkB (.x5, 0) (by fin_cases lay <;> simp [bK, T3M.bK, layK, baseK])
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkB (.x11, _) (by fin_cases lay <;> simp [bK, T3M.bK, layK])
  have hrw := T3M.routed_eq index lay
  by_cases h3 : lay.val = 3
  · obtain rfl : lay = 3 := Fin.ext h3
    cases msg with
    | forest root => exact hs.msg.elim
    | pair left right =>
    have hm3 := hs.msg.pair_top
    have h10 : t.getReg .x10 = BitVec.ofNat 64 4128 := hkB (.x10, _) (by simp [bK, T3M.bK])
    have h12d : t.getReg .x12 = BitVec.ofNat 64 4112 ∨ t.getReg .x12 = BitVec.ofNat 64 4176 := hpost.dst3 rfl
    have hm (A : Word) : t.getMem A = memEval s (T3M.specA 3 (trPc 3 (cpIdx index 3))).mem A := ht.mem A
    have hf : ∀ A, A < 2 ^ 64 → A ≠ 4144 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl <;> simp <;> omega
    have hH : WitHdr w s := hs.glob.2.1
    refine ⟨h5, ?_, ?_⟩
    · rcases h12d with h12 | h12
      · exact hashArgs_of t 4128 64 4112 h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)
      · exact hashArgs_of t 4128 64 4176 h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)
    change hashInput t = toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputH 3 (route index 3).2 (route index 3).1 left
      right (ClaudeWCT.W9.T3M.wbcCtr w index 3) (ClaudeWCT.W9.T3M.wbcPad w index 3) (ClaudeWCT.W9.T3M.wbcHigh w index 3)))
    rw [pair_input_block, show ClaudeWCT.W9.T3M.bcCounterOff index 3 = 8 * 4 from rfl]
    apply T3M.row_hash t 4128 (by decide +kernel) (by decide +kernel) 3 _ _ left _ _ _ h10 h11
    · exact ⟨(hf _ (by decide +kernel) (by decide +kernel)).trans hm3.1.1,
        (hf _ (by decide +kernel) (by decide +kernel)).trans hm3.1.2⟩
    · rw [hm]; simp only [T3M.specA, T3M.l3Writes, ↓reduceIte, List.cons_append, List.nil_append]
      rw [memEval_cons_ofNat _ _ _ _ _ (by norm_num) (by norm_num), if_pos rfl]
      rw [t3E3_eval s index hs.idx (by simpa [rReg, below] using hs.route) (hs.hdr3 rfl).1, hrw,
        show T3M.below (3 : Layer).val = 0 from rfl, pow_zero, Nat.div_one]
      try rfl
    · -- C3 (stage 2): word 857 of stage 1 (`sd t2,-152(s0)`) is gone; the high word is the witness word at offset 24
      refine (hf _ (by decide +kernel) (by decide +kernel)).trans ?_
      refine (hm3.2.2 : s.getMem (BitVec.ofNat 64 (4128 + 24)) = wword w 3).trans ?_
      unfold ClaudeWCT.W9.T3M.wbcHigh ClaudeWCT.W9.T3M.rowBlock
      rw [if_pos (show (3 : Layer).val = 3 from rfl)]
      exact (Verify.wdig_hi w 2).symm
    · rw [hf _ (by decide +kernel) (by decide +kernel), Verify.wdig_lo]; exact hH 4 (by decide +kernel) (by decide +kernel)
    · rw [hf _ (by decide +kernel) (by decide +kernel), Verify.wdig_hi]; exact hH 5 (by decide +kernel) (by decide +kernel)
    · -- the merged singleton leaves the right top value at `WIT + 48`; the entry does not copy it
      exact ⟨(hf _ (by decide +kernel) (by decide +kernel)).trans hm3.2.1.1,
        (hf _ (by decide +kernel) (by decide +kernel)).trans hm3.2.1.2⟩
  · cases msg with
    | forest root => exact hs.msg.elim
    | pair left right =>
    have hmsg := hs.msg.pair_low h3
    have hl3 : lay.val < 3 := hmsg.1
    set c := cpIdx index lay.val with hcd
    have hc := T3M.cpIdx_lt index lay.val lay.isLt
    obtain ⟨r16, rlo, rhi, rend⟩ := T3M.rowA_facts lay.val c hl3 hc
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (rowA lay.val c) :=
      hkB (.x10, _) (by rw [bK, if_neg h3]; exact List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨d, h12, hdd⟩ := hpost.dst hl3
    have hm (A : Word) : t.getMem A = memEval s (headerWrites lay.val c) A := by
      simpa [specA, h3] using ht.mem A
    have hrowpad : rowA lay.val c + 64 < 25216 := by
      have H : ((List.range 3).all fun l => (List.range (nCopy l)).all fun c =>
        decide (rowA l c + 64 < 25216)) = true := by decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp H lay.val
        (List.mem_range.mpr hl3)) c (List.mem_range.mpr hc))
    have hf : ∀ q, q < 64 → q ≠ 16 →
        t.getMem (BitVec.ofNat 64 (rowA lay.val c + q)) = s.getMem (BitVec.ofNat 64 (rowA lay.val c + q)) := by
      intro q hq h16
      rw [hm]
      apply memEval_frame_ofNat s _ _ (by omega)
      intro p hp
      simp only [headerWrites, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      simp; omega
    refine ⟨h5, hashArgs_of t (rowA lay.val c) 64 d h10 h11 h12 (by omega) (by decide +kernel) (by omega)
      (by rcases hdd with ⟨hd1, hd2⟩ | rfl <;> omega) (by rcases hdd with ⟨hd1, hd2⟩ | rfl <;> omega), ?_⟩
    change hashInput t = toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputH lay (route index lay).2 (route index lay).1
      left right (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay)
      (ClaudeWCT.W9.T3M.wbcHigh w index lay)))
    rw [pair_input_block]
    have e := T3M.rowA_eq index lay h3
    have h8 := T3M.rowBlock_mod8 index lay
    have hcoff : ClaudeWCT.W9.T3M.bcCounterOff index lay = 8 * ((rowA lay.val c - WIT) / 8 + 4) := by
      unfold ClaudeWCT.W9.T3M.bcCounterOff; rw [e]; unfold WIT at *; omega
    have hm3 := hmsg.2.2.2 3 (Or.inl rfl)
    have hm4 := hmsg.2.2.2 4 (Or.inr (Or.inl rfl))
    have hm5 := hmsg.2.2.2 5 (Or.inr (Or.inr rfl))
    have hhoff : ClaudeWCT.W9.T3M.rowBlock index lay + 16 = 8 * ((rowA lay.val c - WIT) / 8 + 2) := by
      rw [e]; unfold WIT at *; omega
    apply T3M.row_hash t (rowA lay.val c) (by omega) (by omega) lay _ _ left right _ _ h10 h11
    · exact ⟨(hf 0 (by decide +kernel) (by decide +kernel)).trans hmsg.2.1.1,
        (hf 8 (by decide +kernel) (by decide +kernel)).trans hmsg.2.1.2⟩
    · rw [hm]; unfold headerWrites
      rw [memEval_cons_ofNat _ _ _ _ _ (by omega) (by omega), if_pos rfl]
      simp only [E.eval]
      rw [hs.word hl3, show BC.below lay.val = T3M.below lay.val from rfl, ← hrw]
    · -- C2/C3 (FULL): the root window's high word is witness memory (`wbcHigh`)
      rw [hf 24 (by decide +kernel) (by decide +kernel)]
      unfold ClaudeWCT.W9.T3M.wbcHigh; rw [hhoff]
      have h3' : s.getMem (BitVec.ofNat 64 (rowA lay.val c + 24)) = wword w ((rowA lay.val c - WIT) / 8 + 2 + 1) := by
        simpa using hm3
      rw [h3']; exact (Verify.wdig_hi w _).symm
    · rw [hf 32 (by decide +kernel) (by decide +kernel), hcoff, Verify.wdig_lo]; simpa using hm4
    · rw [hf 40 (by decide +kernel) (by decide +kernel), hcoff, Verify.wdig_hi]; simpa using hm5
    · exact ⟨(hf 48 (by decide +kernel) (by decide +kernel)).trans hmsg.2.2.1.1,
        by rw [show rowA lay.val c + 48 + 8 = rowA lay.val c + 56 by omega,
          hf 56 (by decide +kernel) (by decide +kernel)]; simpa [Nat.add_assoc] using hmsg.2.2.1.2⟩
theorem encoding_setup : EncodingSetup := fun w pk index lay msg s hs => by
  refine ⟨encoding_reject w pk index lay msg s hs, fun hlt => ?_⟩
  obtain ⟨t, ht⟩ := encoding_run w pk index lay msg s hs hlt
  obtain ⟨h5, hv, hin⟩ := setup_hash w pk index lay msg s hs t ht
  exact ⟨t, (by fin_cases lay <;> exact ht.steps), ht.ecall (by fin_cases lay <;> rfl),
    h5, hv, hin, setup_post w pk index lay msg s hs t ht⟩
def EncodingBlocks : Prop := ∀ (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (tree leaf : Nat)
  (msg : LayerMsg) (hi : BitVec 64), (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf msg
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w) hi))).blocks = 1
theorem encoding_blocks : EncodingBlocks := fun w index lay tree leaf msg hi => by
  cases msg with
  | forest root =>
    change (toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputH lay tree leaf root (ClaudeWCT.W9.T3M.wbcRight w)
      (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) hi))).blocks = 1
    rw [pair_input_block]
    exact blocks_blk4 _ _ _ _
  | pair left right =>
    change (toQ (pad64 (ClaudeWCT.WCT9.pairEncodingInputH lay tree leaf left right
      (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) hi))).blocks = 1
    rw [pair_input_block]
    exact blocks_blk4 _ _ _ _
end SigGolfCandidate.T3M.BC
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 width maxDigit shortHash leafHash)
def chainsP (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (tree leaf : Nat) (digits : List Nat) : T3.M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    ClaudeWCT.W9.T3M.chainPW lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (ClaudeWCT.W9.T3M.wchainPads w lay i.val).1 (ClaudeWCT.W9.T3M.wchainPads w lay i.val).2
      (ClaudeWCT.W9.T3M.wchainHeaderPad w lay i.val) (ClaudeWCT.W9.T3M.wvalueFor w lay digits i.val)
theorem lctx_rank_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256)
    (t : Nat) (ht : t < 14) :
    (lctxOf w index lay a).kOf t = SigGolfCandidate.T3.lowerWord (ansD a) / 2 ^ (9 * t) % 512 := by
  rw [LCtx.kOf_eq _ t ht]
  simp only [lctxOf]
  by_cases h7 : t < 7
  · rw [if_pos h7, Nat.mod_eq_of_lt h7, ← ansD_lo]
    rw [lowerWord_eq]
    have h1 := mod_pow_div_mod (ansD a).toNat 64 (9 * t) 9 (by omega)
    have h2 := mod_pow_div_mod (ansD a).toNat 63 (9 * t) 9 (by omega)
    have h3 := div_mod_add_pow ((ansD a).toNat % 2 ^ 63) ((ansD a).toNat / 2 ^ 64 % 2 ^ 63)
      (9 * t) 63 9 (by omega)
    rw [show (2 : Nat) ^ 9 = 512 from rfl] at h1 h2 h3
    rw [h1, h3, h2]
  · rw [if_neg h7, show t % 7 = t - 7 by omega, ← ansD_hi]
    rw [lowerWord_eq]
    rw [show 9 * t = 63 + 9 * (t - 7) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_add_pow _ _ _ _ (le_refl _), Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)), Nat.sub_self,
      Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    have h2 := mod_pow_div_mod ((ansD a).toNat / 2 ^ 64) 63 (9 * (t - 7)) 9 (by omega)
    rw [show (2 : Nat) ^ 9 = 512 from rfl] at h2
    exact h2.symm
theorem lctx_headOK (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256)
    (hgood : ClaudeWCT.WCT9.lowerRankGood (ansD a)) (i : Nat) (hi : i < 42) :
    (lctxOf w index lay a).headOK i := by
  intro _ _
  rw [lctx_rank_eq w index lay a (i / 3) (by omega)]
  exact hgood ⟨i / 3, by omega⟩
def guardedChainsP {β : Type} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer)
    (answer : Digest) (digits : List Nat) (R : List Digest → T3.M (Option β)) : T3.M (Option β) := do
  let some ends ← ClaudeWCT.WCT9.lowerGuardedRun
    (ClaudeWCT.W9.T3M.layerChainP w index lay digits)
    (chainsP w lay (route index lay).2 (route index lay).1 digits) answer | pure none
  R ends
/-- C4: the top fold of the spec (`topFinishP`): the one-word label with the witness high pad and the half by heap
parity (`WCT9.lowerNodeHashP 0`). -/
def merkleP (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j.val
    let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.WCT9.lowerNodeHashP lay.val (route index lay).2
      (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1)) pair.1
      (ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j.val)
      (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j.val) pair.2) value
theorem layerP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (digits : List Nat) :
    ClaudeWCT.W9.T3M.layerP w index 0 digits = chainsP w 0 (route index 0).2 (route index 0).1 digits >>= fun ends =>
      ClaudeWCT.WCT9.leafHashW 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
        (ClaudeWCT.W9.T3M.wleafHigh w 0) ends >>= merkleP w index 0 := by
  unfold ClaudeWCT.W9.T3M.layerP chainsP merkleP
  generalize route index 0 = p
  obtain ⟨leaf, tree⟩ := p
  rfl
def layerHead {β : Type} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (M : ClaudeWCT.WCT9.LayerMsg)
    (R : List Digest → T3.M (Option β)) : T3.M (Option β) :=
  if (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow then pure none else
  ClaudeWCT.WCT9.encodingHash lay (ClaudeWCT.W9.T3M.layerEncodingInputP lay (route index lay).2 (route index lay).1 M
    (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w)
    (ClaudeWCT.W9.T3M.wbcHigh w index lay)) >>= fun answer =>
    match canonicalDecode lay answer with
    | none => pure none
    | some digits => guardedChainsP w index lay answer digits R
def stB (lay : Nat) : Nat := if lay = 0 then 122 else bSt lay+4
def cyB (lay : Nat) : Nat := if lay = 0 then 68 else bCy lay+4
def lfStepsL : Nat := 4
def chainCost0 (lay : Nat) : Nat := if lay = 0 then 1066 else 2935 - 9 * tgtL lay
def chainFuel (lay : Nat) : Nat := if lay = 0 then 2320 else 1720
def layerCost (lay Z : Nat) : Nat := stepsA lay + 8 + cyB lay + lfStepsL + chainCost0 lay - Z
def layerFuel (lay : Nat) : Nat := stepsA lay + 1 + stB lay + chainFuel lay + lfStepsL
def layerCostA (floors : Layer → Nat) (lay : Nat) : Nat :=
  layerCost lay 0 - floors (Fin.ofNat 4 lay)
theorem layerCostA_low (floors : Layer → Nat) (lay : Layer) (h : lay ≠ 0) :
    layerCostA floors lay.val = layerCost lay.val 0 - floors lay := by
  fin_cases lay <;> rfl
/-- Stage 2 (C2 + C3): one head step (L3: the row high-word store; L1/L2: the row high-word store) and one leaf
setup step (the leaf tweak high-word clear) fewer than stage 1 (1182/1175/1175). -/
theorem layerCost_vals : layerCost 3 0 = 1181 ∧ layerCost 2 0 = 1173 ∧ layerCost 1 0 = 1173 := by decide +kernel
theorem layerFuel_vals : layerFuel 3 = 1765 ∧ layerFuel 2 = 1757 ∧ layerFuel 1 = 1757 := by decide +kernel
theorem ckOf_lt (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256) (ds : List Nat)
    (hds : canonicalDecode lay (ansD a) = some ds) : ckOf lay a < 8 := by
  rw [canonical_decode_lower_v6 lay hlay] at hds
  split_ifs at hds with h1 h2
  unfold ckOf; rw [tgtL_eq]; exact h2
theorem s6v_chainBlock (lay : Layer) (h : lay ≠ 0) :
    s6v lay.val = Verify.WIT + ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay + 520 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals decide +kernel
theorem lctx_prefix_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256)
    (hlay : lay ≠ 0) (ds : List Nat) (hds : canonicalDecode lay (ansD a) = some ds) (n : Nat) (hn : n ≤ 42) :
    (List.range' 0 n).foldlM (lctxOf w index lay a).chainF [] =
      (List.range n).mapM (ClaudeWCT.W9.T3M.layerChainP w index lay ds) := by
  set L := lctxOf w index lay a
  have hD := lctx_digits w index lay a hlay ds hds
  have hF : (List.range' 0 n).foldlM L.chainF [] = (fun xs => [] ++ xs) <$>
      (List.range' 0 n).mapM (fun i => L.rest i (L.dig i) (L.bufferVal i)) := foldlM_app_mapM _ n 0 []
  rw [hF]
  simp only [List.nil_append, id_map']
  rw [List.range_eq_range']
  apply mapM_congr'
  intro i hi
  have hi' : i < 43 := by have := List.mem_range'_1.mp hi; omega
  have hc : i < chainCount lay := by rw [LCtx.chainCount_lower lay hlay]; omega
  rw [L.fit_chain hlay rfl ds hD (s6v_chainBlock lay hlay) i hi']
  unfold LCtx.coreChain ClaudeWCT.W9.T3M.layerChainP
  rw [Nat.mod_eq_of_lt hc]
  rfl
theorem chainCount_top : chainCount (0 : Layer) = 51 := by decide +kernel
theorem layerCost_low (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (a : BitVec 256)
    (ds : List Nat) (hds : canonicalDecode lay (ansD a) = some ds) :
    stepsA lay.val + 8 + (bCy lay.val+4) + (lctxOf w index lay a).lowCost + lfStepsL =
      layerCost lay.val ((lctxOf w index lay a).zSum 0 43 + 4*(lctxOf w index lay a).savedCopies 0 43) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hD := lctx_digits w index lay a hlay ds hds
  have hsum := LCtx.canonical_decode_lower_sum lay hlay _ ds hds
  have hck : (lctxOf w index lay a).ck < 8 := ckOf_lt lay hlay a ds hds
  have hacc := (lctxOf w index lay a).lowCost_accept hck ds hD hsum.1 (canonicalTarget lay) hsum.2
  rw [← tgtL_eq] at hacc
  simp only [layerCost, cyB, chainCost0, if_neg h0]
  omega
theorem count_range'_eq (f : Nat → Nat) (P : Nat → Prop) [DecidablePred P] (hf : ∀ j, f j = if P j then 1 else 0) :
    ∀ n a, ((List.range' a n).map f).sum = ((List.range' a n).filter fun j => decide (P j)).length := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [List.range'_succ, List.map_cons, List.sum_cons, List.filter_cons, ih (a + 1), hf a]
    by_cases h : P a <;> simp [h] <;> omega
theorem zSum_eq_wordCredit (c : LCtx) (lay : Layer) (hlay : lay ≠ 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) : c.zSum 0 43 = ClaudeWCT.WCT9.wordCredit lay D := by
  have hn := LCtx.chainCount_lower lay hlay
  have hw : ∀ i, maxDigit lay i = 7 := fun i => by simp [maxDigit, hlay]
  unfold LCtx.zSum ClaudeWCT.WCT9.wordCredit
  rw [hn, List.range_eq_range', count_range'_eq _ (fun j => c.dig j = 6) (fun j => by simp [LCtx.zc])]
  congr 1
  apply List.filter_congr
  intro j hj
  have hj' := (List.mem_range'_1.mp hj).2
  rw [hw j, hD j (by omega)]
  simp only [decide_eq_decide]
  omega
theorem savedCopies_eq (c : LCtx) (hlay : c.lay ≠ 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0) :
    c.savedCopies 0 43 = ClaudeWCT.WCT9.savedCopies c.lay D := by
  unfold LCtx.savedCopies ClaudeWCT.WCT9.savedCopies
  rw [LCtx.chainCount_lower c.lay hlay, List.range_eq_range',
    count_range'_eq _ (fun j => c.bufferSafe j) (fun j => by simp [LCtx.savedCopy])]
  congr 1
  apply List.filter_congr
  intro j hj
  rw [decide_eq_decide]
  exact c.bufferSafe_iff hlay D hD j (by have := List.mem_range'_1.mp hj; omega)
open SphincsSecurity (bytesLE bytesLE_length) in
theorem encQ_of_row (lay : Layer) (a : Digest) (tr lf : Nat) (hi : BitVec 64) (rest : List UInt8)
    (hl : (bytesLE 16 a ++ bytesLE 16 (hi ++ T3.hyperWord lay.val (tr * 2 ^ height lay + lf)) ++ rest).length ≤ 64) :
    EncQ lay.val (toQ (pad64 (bytesLE 16 a ++ bytesLE 16 (hi ++ T3.hyperWord lay.val (tr * 2 ^ height lay + lf)) ++
      rest))) := by
  unfold EncQ
  refine ⟨pad64 (bytesLE 16 a ++ bytesLE 16 (hi ++ T3.hyperWord lay.val (tr * 2 ^ height lay + lf)) ++ rest), ?_, rfl,
    ⟨tr * 2 ^ height lay + lf, hi, ?_⟩⟩
  · simp only [pad64, List.length_append, List.length_replicate, bytesLE_length] at hl ⊢
    omega
  · unfold pad64
    rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 a),
      List.take_left' (bytesLE_length 16 _)]
    try rfl
open SphincsSecurity (bytesLE bytesLE_length) in
theorem encQ_layer (lay : Layer) (tree leaf : Nat) (M : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32) (pad : BitVec 96)
    (padR : Digest) (hi : BitVec 64) :
    EncQ lay.val (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf M c pad padR hi))) := by
  cases M with
  | forest root =>
    change EncQ lay.val (toQ (pad64 (bytesLE 16 root ++
      bytesLE 16 (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) ++
      bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 padR)))
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 root)]
    exact encQ_of_row lay root tree leaf hi _ (by simp only [List.length_append, bytesLE_length]; omega)
  | pair left right =>
    change EncQ lay.val (toQ (pad64 (bytesLE 16 left ++
      bytesLE 16 (hi ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) ++
      bytesLE 4 c ++ bytesLE 12 pad ++ bytesLE 16 right)))
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 left)]
    exact encQ_of_row lay left tree leaf hi _ (by simp only [List.length_append, bytesLE_length]; omega)
/-- Configuration (1)+(2): the hash hypothesis `HashOkBy floors high` is path-aware; a LOW selection costs `bCy`
(4 less than HIGH) and earns the `pathBonus` 4, so the accepted cost stays `layerCost - floors`. -/
theorem layer_good_low (floors : Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (high : Bool) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (M : ClaudeWCT.WCT9.LayerMsg)
    (s : MachineState) (hs : LayerIn w pk index lay.val M s) {β : Type} (R : List Digest → T3.M (Option β))
    (K : Option β → OracleComp HashSpec Obs) (hK0 : K none = pure (false, 0)) (N C A : Nat) (Q : Prop)
    (hR : ∀ ends u, LeafOut w pk index lay ends u → GoodQP (HashOkBy floors high) u N C Q A (ccM (R ends) K)) :
    GoodQP (HashOkBy floors high) s (N + layerFuel lay.val) (C + layerCost lay.val 0) Q (A + layerCostA floors lay.val)
      (ccM (layerHead w index lay M R) K) := by
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hlf : lfStepsL = 4 := rfl
  have hidx := hs.idx
  have hA := BC.encoding_setup w pk index lay M s hs
  have hT : 9 * tgtL lay.val ≤ 2935 := by fin_cases lay <;> decide +kernel
  have hF : floors lay + 9 * tgtL lay.val ≤ 2935 := by
    have hb := hbound lay
    have ht : tgtL lay.val ≤ 201 := by fin_cases lay <;> decide +kernel
    omega
  have hfuel : layerFuel lay.val = stepsA lay.val + 1 + (bSt lay.val+4) + 1720 + lfStepsL := by
    simp [layerFuel, stB, chainFuel, h0]
  have hcost : layerCost lay.val 0 = stepsA lay.val + 8 + (bCy lay.val+4) + lfStepsL + (2935 - 9 * tgtL lay.val) := by
    simp only [layerCost, cyB, chainCost0, if_neg h0]; omega
  have hcostA : layerCostA floors lay.val = stepsA lay.val + 8 + (bCy lay.val+4) + lfStepsL +
      (2935 - 9 * tgtL lay.val - floors lay) := by
    rw [layerCostA_low floors lay hlay, hcost]; omega
  have hbS : 25 ≤ (bSt lay.val+4) := by unfold bSt; split_ifs <;> omega
  have hbC : 28 ≤ (bCy lay.val+4) := by unfold bCy; split_ifs <;> omega
  have hrej : BC.rejectSteps lay.val ≤ stepsA lay.val + 21 := by
    unfold BC.rejectSteps; split_ifs <;> omega
  unfold layerHead
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow
  · rw [if_pos hctr, ccM_pure, hK0]
    obtain ⟨u, hst, hf, h5, h10⟩ := hA.1 hctr
    exact GoodQP.stepsQ hst (GoodQP.reject (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, hpre⟩ := hA.2 (by omega)
    have hblk := BC.encoding_blocks w index lay (route index lay).2 (route index lay).1 M
      (ClaudeWCT.W9.T3M.wbcHigh w index lay)
    have hq := encQ_layer lay (route index lay).2 (route index lay).1 M (ClaudeWCT.W9.T3M.wbcCtr w index lay)
      (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w) (ClaudeWCT.W9.T3M.wbcHigh w index lay)
    have H : ∀ a : BitVec 256, GoodQP (fun hash => hash (toQ (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 M (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay)
        (ClaudeWCT.W9.T3M.wbcRight w) (ClaudeWCT.W9.T3M.wbcHigh w index lay)))) = a ∧
          HashOkBy floors high hash) (writeHash t a) (N + lfStepsL + 1720 + (bSt lay.val+4))
        (C + lfStepsL + (2935 - 9 * tgtL lay.val) + (bCy lay.val+4))
        Q (A + lfStepsL + (2935 - 9 * tgtL lay.val - floors lay) + (bCy lay.val+4))
        (ccM (match canonicalDecode lay (ansD (selectedView a)) with
          | none => pure none
          | some digits => guardedChainsP w index lay (ansD (selectedView a)) digits R) K) := by
      intro a
      have hB := encB_step w pk index lay hlay _ (cpIdx_lt index lay.val lay.isLt) hidx t hpre a
      cases hds : canonicalDecode lay (ansD (selectedView a)) with
      | none =>
        dsimp only
        rw [ccM_pure, hK0]
        obtain ⟨v, k, cy, hst', hrejected, hk, hcy⟩ := hB.1 hds
        have hrej : GoodQP (HashOkBy floors high) v 1 1 Q 0 (pure (false,0)) := by
          rcases hrejected with hf' | ⟨hf',h5',h10'⟩
          · exact (GoodQP.fetch_none (Q := Q) (A := 0) hf').mono (by omega) (by omega) (fun h => ⟨h,by omega⟩)
          · exact GoodQP.reject hf' h5' h10'
        exact (GoodQP.stepsQ hst' hrej (by omega) (by omega)
          (fun hq => ⟨hq, by omega⟩)).pre_mono (fun _ h => h.2)
      | some ds =>
        dsimp only
        obtain ⟨s0, k0, cy0, hst0, hk0, hcy0, hLok, hkn, hO0, hIn, hG0, hOr0, h23, h30, h1, hBuf0⟩ := hB.2 (by rw [hds]; simp)
        set L := lctxOf w index lay (selectedView a) with hLd
        have hD := lctx_digits w index lay (selectedView a) hlay ds hds
        have hsum := LCtx.canonical_decode_lower_sum lay hlay _ ds hds
        have hck : L.ck < 8 := ckOf_lt lay hlay (selectedView a) ds hds
        have hacc := L.lowCost_accept hck ds hD hsum.1 (canonicalTarget lay) hsum.2
        rw [← tgtL_eq] at hacc
        have hcr : L.zSum 0 43 = ClaudeWCT.WCT9.wordCredit lay ds := zSum_eq_wordCredit L lay hlay ds hD
        have hsave : L.savedCopies 0 43 = ClaudeWCT.WCT9.savedCopies lay ds := savedCopies_eq L hlay ds hD
        have hP := L.lowP_eq hlay rfl ds hD (s6v_chainBlock lay hlay)
        by_cases hgood : ClaudeWCT.WCT9.lowerRankGood (ansD (selectedView a))
        · simp only [guardedChainsP, ClaudeWCT.WCT9.lowerGuardedRun_of_good _ _ _ hgood, bind_map_left]
          have hG := L.lower_good hLok rfl rfl hck (lctx_headOK w index lay (selectedView a) hgood) hkn hO0 (fun ends => ccM (R ends) K) (N + lfStepsL) (C + lfStepsL) (A + lfStepsL) Q
            (fun ends t ht => by
              obtain ⟨u, hstu, hu⟩ := leafL_step w pk index lay hlay hidx (selectedView a) s0 hkn hck hG0 hOr0 h23 h30 h1 hBuf0 ends t ht
              exact GoodQP.stepsQ hstu (hR ends u hu) (by unfold lfStepsL; omega) (by unfold lfStepsL; omega)
                (fun hq => ⟨hq, by unfold lfStepsL; omega⟩))
            s0 hIn
          have e : chainsP w lay (route index lay).2 (route index lay).1 ds = L.lowP := by
            rw [hP]; unfold chainsP; rw [LCtx.chainCount_lower lay hlay]; rfl
          rw [ccM_bind, e]
          have body : ∀ k, k ≤ L.zSum 0 43 + 4*L.savedCopies 0 43 + (if T3.lowerSpare (ansD a) then 4 else 0) →
              GoodQP (HashOkBy floors high) (writeHash t a) (N + lfStepsL + 1720 + (bSt lay.val+4))
                (C + lfStepsL + (2935 - 9 * tgtL lay.val) + (bCy lay.val+4))
                Q (A + lfStepsL + (2935 - 9 * tgtL lay.val - k) + (bCy lay.val+4))
                (ccM L.lowP (fun ends => ccM (R ends) K)) := fun k hk =>
            GoodQP.stepsQ hst0 hG (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
          by_cases hcf : floors lay ≤ ClaudeWCT.WCT9.wordCredit lay ds + 4*ClaudeWCT.WCT9.savedCopies lay ds +
              (if T3.lowerSpare (ansD a) then 4 else 0)
          · exact (body _ (by omega)).pre_mono (fun _ h => h.2)
          · refine GoodQP.of_false_pre (body 0 (Nat.zero_le _)) ?_
            rintro hash ⟨hea, hok⟩
            have hh := hok lay _ hq ds (by
              rw [hea, ClaudeWCT.WCT9.verificationAnswer_lower lay hlay, ← selectedView_answer lay hlay]; exact hds)
            rw [hea, ClaudeWCT.WCT9.verificationLow_lower lay hlay] at hh
            apply hcf
            by_cases hsp : T3.lowerSpare (ansD a)
            · simpa [ClaudeWCT.WCT9.dispatchPenalty, ClaudeWCT.WCT9.CanonicalPolicy.pathReward,
                ClaudeWCT.WCT9.CanonicalPolicy.pathBonus, ClaudeWCT.WCT9.CanonicalPolicy.reward, ClaudeWCT.WCT9.lowSelected,
                hlay, hsp] using hh
            · simpa [ClaudeWCT.WCT9.dispatchPenalty, ClaudeWCT.WCT9.CanonicalPolicy.pathReward,
                ClaudeWCT.WCT9.CanonicalPolicy.pathBonus, ClaudeWCT.WCT9.CanonicalPolicy.reward, ClaudeWCT.WCT9.lowSelected,
                hlay, hsp] using hh
        · have hj := ClaudeWCT.WCT9.lowerFirstBad_lt (ansD (selectedView a)) hgood
          have hbad : L.kOf (ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) <
              rankFloor (ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) := by
            rw [lctx_rank_eq w index lay (selectedView a) _ hj]
            exact ClaudeWCT.WCT9.lowerFirstBad_bad (ansD (selectedView a)) hgood
          have hranks : ∀ i, i < 3 * ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a)) → L.headOK i := by
            intro i hi _ _
            rw [lctx_rank_eq w index lay (selectedView a) _ (by omega)]
            exact ClaudeWCT.WCT9.lowerFirstBad_before (ansD (selectedView a)) hgood (i / 3) (by omega)
          have hpref := L.chains_prefix_fault (P := HashOkBy floors high) hLok rfl rfl hkn hO0 _ hj hbad hranks s0 hIn
          have hpcost := L.chainsCost_prefix_le (3 * ClaudeWCT.WCT9.lowerFirstBad (ansD (selectedView a))) (by omega)
          have hle : L.chainsCost 0 42 ≤ L.lowCost := by unfold LCtx.lowCost; omega
          simp only [guardedChainsP, ClaudeWCT.WCT9.lowerGuardedRun, if_neg hgood, bind_assoc, pure_bind,
            ccM_bind, ccM_pure, hK0]
          rw [← lctx_prefix_eq w index lay (selectedView a) hlay ds hds _ (by omega)]
          exact (GoodQP.stepsQ hst0 hpref (by omega) (by omega) (fun hf => hf.elim)).pre_mono
            (fun _ h => h.2)
    have := GoodQP.encodingHash_bind_pre (f := fun answer => match canonicalDecode lay answer with
      | none => pure none
      | some digits => guardedChainsP w index lay answer digits R) hf h5 hv hin (fun a => by simpa only [selectedView_answer lay hlay] using H a)
    rw [hblk] at this
    exact (GoodQP.steps' hst this (by omega) (by omega) (by omega))
theorem layerIn_of_fts (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (idx : Nat) (left right : Digest) (u : MachineState)
    (hidx : idx < 2 ^ 31) (hglob : Glob [(.x5, 0)] w pk u) (hreg : u.getReg .x22 = BitVec.ofNat 64 idx)
    (hpc : u.pc = pcOf 854) (hleft : DigAt u WIT left) (hright : DigAt u (WIT + 48) right)
    (hwit : Verify.Orig w (fun o => (24 ≤ o ∧ o < 48) ∨ (7664 ≤ o ∧ o < 21984)) u)
    (hbase8 : u.getReg .x8 = BitVec.ofNat 64 (WIT + 80)) (ha1 : u.getReg .x11 = 64)
    (hs10 : u.getReg .x26 = 6) (hOne : u.getReg .x7 = 1) (hTwo : u.getReg .x13 = 2) (hSeven : u.getReg .x30 = 7)
    (hThree : u.getReg .x19 = 3) (hFour : u.getReg .x20 = 4) (hFive : u.getReg .x21 = 5)
    (hCoord : u.getReg .x6 = 0x10000)
    (hbase : u.getReg .x2 = BitVec.ofNat 64 0xffbde0)
    (htop : ∀ k, k < 5 → u.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) =
      BitVec.ofNat 64 (topWords.getD k 0))
    (htop8 : u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21328)
    (ha2 : u.getReg .x12 = BitVec.ofNat 64 4112 ∨ u.getReg .x12 = BitVec.ofNat 64 4176)
    (hd0 : u.getMem (BitVec.ofNat 64 (TOPB9 - 304)) = 0xFFF) :
    ∃ t, Steps image u 0 0 t ∧ LayerIn w pk idx 3 (.pair left right) t := by
  have hpk : preK 3 = [(.x5, 0)] ++ [(.x8, BitVec.ofNat 64 4208), (.x11, 64), (.x26, 6), (.x7, 1), (.x13, 2), (.x30, 7),
      (.x2, BitVec.ofNat 64 0xffbde0), (.x19, 3), (.x20, 4), (.x21, 5), (.x6, 0x10000)] := rfl
  have hk : ∀ p ∈ preK 3, u.getReg p.1 = p.2 := by
    intro p hp
    rw [hpk] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hglob.1 _ (by simp)
    · exact hbase8
    · exact ha1
    · exact hs10
    · exact hOne
    · exact hTwo
    · exact hSeven
    · exact hbase
    · exact hThree
    · exact hFour
    · exact hFive
    · exact hCoord
  refine ⟨u, Steps.refl u, ⟨by norm_num, hidx, hpc, ⟨hk, hglob.2⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ha2, fun _ => hd0⟩⟩
  · rw [show rReg 3 = .x22 from rfl, show BC.below 3 = 0 from rfl, pow_zero, Nat.div_one, hreg]
  · intro h
    exact absurd h (by decide +kernel)
  · exact ⟨hleft, hright, hwit.word 24 (by decide) (by unfold WX; decide) (Or.inl ⟨le_refl _, by decide⟩)⟩
  · exact hwit.mono (fun o ho => Or.inr ⟨ho.1, lt_of_lt_of_le ho.2 (by decide +kernel)⟩)
  · intro _
    exact ⟨(htop 4 (by decide +kernel)).trans (by decide +kernel), htop8, htop⟩
  · intro h
    exact absurd h (by decide +kernel)
  · exact hwit.mono (fun o ho => Or.inr ⟨by have hh : 18928 ≤ o := ho.1; omega,ho.2⟩)
theorem tree_next (index : Nat) (L : Layer) (h : L ≠ 0) : (route index L).2 = index / 2 ^ below (L.val - 1) := by
  rw [route_snd]
  fin_cases L
  · exact absurd rfl h
  all_goals rfl
theorem layerEnd_prev (L : Layer) (h : L ≠ 0) : layerEnd (L.val - 1) = ClaudeWCT.W9.T3M.layerBase L := by
  fin_cases L
  · exact absurd rfl h
  all_goals decide +kernel
end SigGolfCandidate.T3M
end
end
end
-- ==== merged from T3M_Verify_MerkleSem ====
section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount pad64 shortHash leafHash header)
theorem mkSpec_run {allow : List Nat} {rel : List Reg} {gk known post : List (Reg × Word)}
    {stops : List Nat} {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : mkSpecB allow rel gk known stops n dirs sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, SpecRes allow rel gk sp post keep s t := by
  obtain ⟨t, ht⟩ := spec_run h s hpc hk hbr hob
  refine ⟨t, { ht with known := ?_, keep := ?_ }⟩
  · intro p hp
    exact ht.known p (List.mem_append_left _ hp)
  · intro r hr
    by_cases he : ∃ p ∈ known, p.1 = r
    · obtain ⟨p, hp, er⟩ := he
      have hpk : p ∈ mkKnownKeep known keep := by simp [mkKnownKeep, hp, er, hr]
      have ht' := ht.known p (List.mem_append_right _ hpk)
      rw [← er]
      exact ht'.trans (hk p hp).symm
    · have hany : known.any (fun p => p.1 == r) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp h
        exact he ⟨p, hp, by simpa using hpr⟩
      exact ht.keep r (by simp [mkUnknownKeep, hr, hany])
/-- Heap of the fold at level `j` of the path of `index` in layer `lay`. -/
abbrev mkHp (index : Nat) (lay : Layer) (j : Nat) : Nat := 2 ^ (height lay - j - 1) + (route index lay).1 / 2 ^ (j + 1)
/-- C2: the witness high tweak word of a lower fold window (bytes 24..32 of the window, `wmerkleHigh`). -/
def mkHw (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) : BitVec 64 :=
  (ClaudeWCT.W9.T3M.wdig w (mkBo lay.val leaf j + 16)).extractLsb' 64 64
/-- The fold tweak: the one-word label `merkleWord` (C2 lower: `lowerNodeWord`; C4 top: `topNodeWord heap`) with the
witness high word. -/
def mkTw (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (j : Nat) : BitVec 128 :=
  mkHw w lay (route index lay).1 j ++ ClaudeWCT.WCT9.merkleWord lay.val (route index lay).2 (mkHp index lay j)
def mkIn (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : List UInt8 :=
  let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j
  let pair := if (route index lay).1 / 2 ^ j % 2 = 0 then (value, other) else (other, value)
  blk4 pair.1 (mkTw w index lay j) (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j) pair.2
/-- One fold of the image: C2 lower folds keep the half `lowerHigh lay heap` (HIGH for even heaps). -/
def mkStep (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) : T3.M Digest :=
  Verify.vHash (ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay j)) (mkIn w index lay value j)
theorem mkFinRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem mkStep_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    mkStep w index lay value j = Verify.vHash (ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay j)) (mkIn w index lay value j) := rfl
theorem mkIn_length (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (mkIn w index lay value j).length = 64 := blk4_length _ _ _ _
theorem mkIn_blocks (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) (j : Nat) :
    (toQ (pad64 (mkIn w index lay value j))).blocks = 1 := blocks_blk4 _ _ _ _
def mkCi (lay k : Nat) : Nat := if lay = 0 ∧ 6 ≤ k then 1 else 0
def mkSh (lay ci leaf : Nat) : Nat := leaf / 2 ^ mkLo lay ci % 2 ^ mkBits lay ci
def mkEc (lay leaf k : Nat) : Nat :=
  BC.mkShp lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) + mkOff lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) + 1
def mkFin (lay leaf : Nat) : Nat :=
  BC.mkShp lay (mkNch lay - 1) (mkSh lay (mkNch lay - 1) leaf) + mkOff lay (mkNch lay - 1) (mkBits lay (mkNch lay - 1)) + (if lay = 0 then 0 else 1)
def mkLvlSt (lay k : Nat) : Nat := mkBody lay k + mkMove lay k + (if lay = 0 ∧ k = 5 then 2 else 0)
theorem mk_facts (lay k : Nat) (hlay : lay < 4) (hk : k < hL lay) :
    mkCi lay k < mkNch lay ∧ mkLo lay (mkCi lay k) ≤ k ∧ k - mkLo lay (mkCi lay k) < mkBits lay (mkCi lay k) ∧
    mkIsDisp lay (mkCi lay k) (k - mkLo lay (mkCi lay k)) = decide (lay = 0 ∧ k = 5) ∧
    (k + 1 < hL lay → ¬ (lay = 0 ∧ k = 5) → mkCi lay (k + 1) = mkCi lay k ∧
      k + 1 - mkLo lay (mkCi lay k) = k - mkLo lay (mkCi lay k) + 1 ∧
      k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
    (k + 1 = hL lay → mkCi lay k = mkNch lay - 1 ∧ ¬ (k - mkLo lay (mkCi lay k) + 1 < mkBits lay (mkCi lay k)) ∧
      k - mkLo lay (mkCi lay k) + 1 = mkBits lay (mkCi lay k)) := by
  interval_cases lay
  · change k < 12 at hk; interval_cases k <;> decide +kernel
  · change k < 7 at hk; interval_cases k <;> decide +kernel
  · change k < 6 at hk; interval_cases k <;> decide +kernel
  · change k < 6 at hk; interval_cases k <;> decide +kernel
theorem mk_disp_facts : mkCi 0 5 = 0 ∧ mkLo 0 0 = 0 ∧ mkCi 0 6 = 1 ∧ mkLo 0 1 = 6 ∧ mkBits 0 0 = 6 ∧ mkBits 0 1 = 6 ∧
    mkNch 0 = 2 := by decide +kernel
theorem mkLvlSt_ne (lay k : Nat) (h : ¬ (lay = 0 ∧ k = 5)) : mkLvlSt lay k = mkBody lay k + mkMove lay k := by
  simp [mkLvlSt, h]
theorem mkBlk_bit (E b n k : Nat) (hk : k < n) : E / 2 ^ b % 2 ^ n / 2 ^ k % 2 = E / 2 ^ (b + k) % 2 := by
  have h1 : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), Nat.div_div_eq_div_mul,
    ← Nat.pow_add]
theorem mkSh_bit (lay ci leaf kk : Nat) (hkk : kk < mkBits lay ci) :
    mkSh lay ci leaf / 2 ^ kk % 2 = leaf / 2 ^ (mkLo lay ci + kk) % 2 := mkBlk_bit _ _ _ _ hkk
theorem mkSh_lt (lay ci leaf : Nat) : mkSh lay ci leaf < 2 ^ mkBits lay ci := Nat.mod_lt _ (Nat.two_pow_pos _)
theorem mkBit_lt (x k : Nat) : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide +kernel)
theorem mkBase_eq (lay : Layer) : mkBase lay.val = ClaudeWCT.W9.T3M.layerBase lay := by fin_cases lay <;> rfl
theorem mkPS_eq (lay : Layer) : mkPS lay.val = ClaudeWCT.W9.T3M.pathSlots lay := by fin_cases lay <;> rfl
theorem mkBase_ge (lay : Nat) (hlay : lay < 4) : 7664 ≤ mkBase lay ∧ mkBase lay % 8 = 0 := by
  interval_cases lay <;> decide +kernel
theorem mkBo_low (lay leaf k : Nat) (_h0 : lay ≠ 0) : mkBo lay leaf k = mkBase lay + 16 * plan lay leaf k := rfl
theorem mkBo_plan (lay leaf k : Nat) : mkBo lay leaf k = mkBase lay + 16 * plan lay leaf k := rfl
theorem topPlanA_eq : topPlanA = ClaudeWCT.W9.T3M.topPlanA := rfl
theorem topPlanB_eq : topPlanB = ClaudeWCT.W9.T3M.topPlanB := rfl
theorem topPlan_eq (leaf j : Nat) : topPlan leaf j = ClaudeWCT.W9.T3M.topPlanSlot leaf j := by
  unfold topPlan ClaudeWCT.W9.T3M.topPlanSlot; rw [topPlanA_eq, topPlanB_eq]
theorem mkBo_eq (lay : Layer) (leaf k : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    mkBo lay.val leaf k = ClaudeWCT.W9.T3M.merkleBlock lay leaf k := by
  unfold ClaudeWCT.W9.T3M.merkleBlock
  rw [← mkBase_eq]
  by_cases h0 : lay.val = 0
  · rw [if_pos h0, mkBo_plan]; unfold plan; rw [if_pos h0, topPlan_eq]
  · rw [if_neg h0, mkBo_low _ _ _ h0]
    congr 2
    unfold plan ClaudeWCT.W9.T3M.lowerPlan
    rw [if_neg h0]
    fin_cases lay
    · exact absurd rfl h0
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 128 by simpa using hleaf), planL1, ClaudeWCT.W9.T3M.lowerPlanL1]
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 64 by simpa using hleaf), planL32, ClaudeWCT.W9.T3M.lowerPlanL32]
    · simp only [hL, List.getD_cons_succ, List.getD_cons_zero] at hleaf
      simp [Nat.mod_eq_of_lt (show leaf < 64 by simpa using hleaf), planL32, ClaudeWCT.W9.T3M.lowerPlanL32]
theorem mkCi_ok (lay k : Nat) : lay = 0 ∨ mkCi lay k = 0 := by
  by_cases h : lay = 0
  · exact Or.inl h
  · exact Or.inr (by simp [mkCi, h])
/-- C4: the chunk's representative leaf (`mkLeafOf`) has the window of `leaf` on every level of the chunk. -/
theorem mkPlan_sh (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    plan lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = plan lay leaf k := by
  by_cases hl : lay = 0
  · subst hl
    have hl4 : leaf < 4096 := by simpa [hL] using hleaf
    have hk12 : k < 12 := by simpa [hL] using hk
    unfold plan topPlan; rw [if_pos rfl, if_pos rfl]
    by_cases h6 : k < 6
    · have hc : mkCi 0 k = 0 := by simp [mkCi]; omega
      rw [hc, if_pos h6, if_pos h6]
      congr 2
      simp only [mkLeafOf, mkSh, mkLo, mkBits]; norm_num
    · have hc : mkCi 0 k = 1 := by simp [mkCi]; omega
      rw [hc, if_neg h6, if_neg h6]
      congr 2
      simp only [mkLeafOf, mkSh, mkLo, mkBits]; norm_num
  · have hc : mkCi lay k = 0 := by simp [mkCi, hl]
    rw [hc]
    have : mkSh lay 0 leaf = leaf := by
      simp only [mkSh, mkLo, mkBits, hl, false_and, if_false, Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt hleaf
    simp only [mkLeafOf, mkLo, hl, false_and, if_false, Nat.pow_zero, Nat.mul_one, this]
theorem mkBo_sh (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBo lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = mkBo lay leaf k := by
  rw [mkBo_plan, mkBo_plan, mkPlan_sh _ _ _ hlay hleaf hk]
theorem mkBlk_sh (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBlk lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k = mkBlk lay leaf k := by
  unfold mkBlk; rw [mkBo_sh _ _ _ hlay hleaf hk]
theorem mkCur_sh (lay leaf k b : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkCur lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) k b = mkCur lay leaf k b := by
  unfold mkCur mkVal; rw [mkBlk_sh _ _ _ hlay hleaf hk]
theorem mkCur_next (lay leaf k b : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk1 : k + 1 < hL lay)
    (hc : mkCi lay (k + 1) = mkCi lay k) :
    mkCur lay (mkLeafOf lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf)) (k + 1) b = mkCur lay leaf (k + 1) b := by
  rw [← hc]; exact mkCur_sh lay leaf (k + 1) b hlay hleaf hk1
/-- C4: every line-A row places window 5 at slot 21 (the upper copies start from it). -/
theorem mkPlan_top5 (x : Nat) : plan 0 x 5 = 21 := by
  have h : (List.range 64).all (fun r => (topPlanA.getD r []).getD 5 0 == 21) = true := by decide +kernel
  have := List.all_eq_true.mp h (x % 64) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simp only [beq_iff_eq] at this
  unfold plan topPlan
  rw [if_pos rfl, if_pos (show (5 : Nat) < 6 by decide)]
  exact this
/-- Route facts of every layer (C4: the top too, checked leaf by leaf in `DirectMerkleChecks`). -/
theorem route_facts (lay leaf : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) :
    (∀ k < hL lay, plan lay leaf k + 4 ≤ mkPS lay ∧ (lay ≠ 0 → leaf / 2 ^ k % 2 = 0 → 1 ≤ plan lay leaf k)) ∧
    (∀ s ∈ mkKS lay leaf 0 ++ mkKH lay leaf 0, s + 1 ≤ mkPS lay ∧ s ∉ mkWs lay leaf 0) ∧
    (∀ k, k + 1 < hL lay → ∀ s ∈ mkKS lay leaf (k + 1) ++ mkKH lay leaf (k + 1),
      s ≠ plan lay leaf k + 1 ∧ s ∉ mkWs lay leaf (k + 1)) := by
  have h : mkRouteOk lay leaf = true := by
    have hA := mkLowOk_true
    simp only [mkLowOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hA
    interval_cases lay
    · exact mkTop_route leaf (by simpa [hL] using hleaf)
    · exact hA.1.1 leaf (by simpa [hL] using hleaf)
    · exact hA.1.2 leaf (by simpa [hL] using hleaf)
    · exact hA.2 leaf (by simpa [hL] using hleaf)
  simp only [mkRouteOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, fun k hk s hs => h.2 k (by omega) s hs⟩
/-- Membership in the write slots, as arithmetic. -/
theorem mkWs_not (lay leaf j s : Nat) (h : s ∉ mkWs lay leaf j) :
    (leaf / 2 ^ j % 2 = 0 → s ≠ plan lay leaf j - 1 ∧ s ≠ plan lay leaf j) ∧
    (leaf / 2 ^ j % 2 = 1 → s ≠ plan lay leaf j + 3 ∧ s ≠ plan lay leaf j + 4) := by
  unfold mkWs at h
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [if_pos hb] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    omega
  · rw [if_neg (by omega)] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    omega
theorem mkKH_mem (lay leaf k j : Nat) (hj : j < hL lay) (hkj : k ≤ j) : plan lay leaf j + 1 ∈ mkKH lay leaf k := by
  simp only [mkKH, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨j, ⟨hj, hkj⟩, rfl⟩
theorem mkKH_succ (lay leaf k s : Nat) (h : s ∈ mkKH lay leaf (k + 1)) : s ∈ mkKH lay leaf k := by
  simp only [mkKH, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at h ⊢
  obtain ⟨j, ⟨hj, hkj⟩, hs⟩ := h
  exact ⟨j, ⟨hj, by omega⟩, hs⟩
theorem mkKS_mem (lay leaf k j s : Nat) (hj : j < hL lay) (hkj : k ≤ j)
    (hs : s = plan lay leaf j + 2 ∨ s = mkSib lay leaf j) : s ∈ mkKS lay leaf k := by
  simp only [mkKS, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons,
    List.not_mem_nil, or_false]
  exact ⟨j, ⟨hj, hkj⟩, hs⟩
theorem mkKS_succ (lay leaf k s : Nat) (h : s ∈ mkKS lay leaf (k + 1)) : s ∈ mkKS lay leaf k := by
  simp only [mkKS, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq] at h ⊢
  obtain ⟨j, ⟨hj, hkj⟩, hs⟩ := h
  exact ⟨j, ⟨hj, by omega⟩, hs⟩
theorem mkBo_facts (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkBo lay leaf k % 8 = 0 ∧ 7664 ≤ mkBo lay leaf k ∧ mkBo lay leaf k + 80 ≤ 16856 ∧ mkBase lay ≤ mkBo lay leaf k ∧
      mkBo lay leaf k + 64 ≤ mkBase lay + 16 * mkPS lay := by
  have hp := ((route_facts lay leaf hlay hleaf).1 k hk).1
  rw [mkBo_plan]
  interval_cases lay <;> simp only [mkBase, mkPS, List.getD_cons_succ, List.getD_cons_zero] at hp ⊢ <;> omega
theorem mkPow_add_div (h k x : Nat) (hk : k < h) :
    (2 ^ h + x) / 2 ^ (k + 1) = 2 ^ (h - k - 1) + x / 2 ^ (k + 1) := by
  have : 2 ^ h = 2 ^ (k + 1) * 2 ^ (h - k - 1) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_add_div (Nat.two_pow_pos _)]
theorem mkDiv64_mul_div (leaf k : Nat) (hk : 6 ≤ k) : leaf / 64 * 64 / 2 ^ (k + 1) = leaf / 2 ^ (k + 1) := by
  have e : 2 ^ (k + 1) = 64 * 2 ^ (k - 5) := by
    rw [show (64 : Nat) = 2 ^ 6 by rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_comm 64 (2 ^ (k - 5)), Nat.mul_div_mul_right _ _ (by decide +kernel : 0 < 64), Nat.div_div_eq_div_mul,
    Nat.mul_comm 64]
theorem mkHeap_eq (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (hci : ¬ (lay = 0 ∧ mkCi lay k = 0)) :
    mkHeap lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k = 2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1) := by
  unfold mkHeap
  by_cases h0 : lay = 0
  · subst h0
    have hk6 : 6 ≤ k := by
      by_contra hk6; exact hci ⟨rfl, by simp [mkCi]; omega⟩
    have hci1 : mkCi 0 k = 1 := by simp [mkCi]; omega
    rw [hci1]
    have hl : leaf < 4096 := by simpa [hL] using hleaf
    have hsh : mkSh 0 1 leaf = leaf / 64 := by
      simp only [mkSh, mkLo, mkBits]; norm_num; omega
    rw [hsh, show mkLo 0 1 = 6 by rfl, show hL 0 = 12 by rfl, show (2 : Nat) ^ 6 = 64 by rfl,
      mkPow_add_div 12 k _ (by simpa [hL] using hk), mkDiv64_mul_div leaf k hk6]
  · have hci0 : mkCi lay k = 0 := by simp [mkCi, h0]
    rw [hci0]
    have hsh : mkSh lay 0 leaf = leaf := by
      simp only [mkSh, mkLo, mkBits, h0, false_and, if_false, Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt hleaf
    rw [hsh, show mkLo lay 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.mul_one, mkPow_add_div _ k _ hk]
theorem mkHeapE_eval (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay)
    (s : MachineState) (h23 : lay = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay leaf)) :
    (mkHeapE lay (mkCi lay k) (mkSh lay (mkCi lay k) leaf) k).eval s =
      BitVec.ofNat 64 (2 ^ (hL lay - k - 1) + leaf / 2 ^ (k + 1)) := by
  have hh : hL lay ≤ 12 := by interval_cases lay <;> decide +kernel
  have hpow : 2 ^ hL lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide +kernel) hh
  unfold mkHeapE
  split_ifs with hc
  · have h0 : lay = 0 := hc.1
    have hd : dispatchHeap lay leaf = 16 * (2 ^ hL lay + leaf) := by
      simp [dispatchHeap, s7Bias, hL, h0]
    apply BitVec.eq_of_toNat_eq
    simp only [E.eval, BinOp.eval, kw, h23 h0, hd]
    have h1 : 2 ^ (hL lay - k - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide +kernel) (by omega)
    have h2 : leaf / 2 ^ (k + 1) ≤ leaf := Nat.div_le_self _ _
    have hdiv : 16 * (2 ^ hL lay + leaf) / 2 ^ (k + 5) = (2 ^ hL lay + leaf) / 2 ^ (k + 1) := by
      rw [show (k + 5 : Nat) = 4 + (k + 1) by omega, Nat.pow_add, show (2 : Nat) ^ 4 = 16 by rfl,
        ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
    rw [toNat_srl _ _ (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 16 * (2 ^ hL lay + leaf) < 2 ^ 64 by omega), hdiv, mkPow_add_div _ k _ hk]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [E.eval, kw]
    rw [mkHeap_eq lay leaf k hlay hleaf hk hc]
/-- Witness words still needed at level `k` and above (lower layers): below the layer, the pad and sibling slots
(`mkKS`), and C2's high tweak words (upper half of the `mkKH` slots). -/
def mkPL (lay leaf k o : Nat) : Prop :=
  (7664 ≤ o ∧ o < mkBase lay) ∨ (mkBase lay ≤ o ∧ (o - mkBase lay) / 16 ∈ mkKS lay leaf k) ∨
    (mkBase lay ≤ o ∧ (o - mkBase lay) % 16 = 8 ∧ (o - mkBase lay) / 16 ∈ mkKH lay leaf k)
/-- C4: the top uses the plan predicate of the lower layers (its region below, `[7664, mkBase 0)`, is empty). -/
def mkP (lay leaf k _b : Nat) (o : Nat) : Prop := mkPL lay leaf k o
theorem mkP_low (lay leaf k b o : Nat) (_h0 : lay ≠ 0) : mkP lay leaf k b o ↔ mkPL lay leaf k o := Iff.rfl
theorem mkP_eq (lay leaf k b o : Nat) : mkP lay leaf k b o ↔ mkPL lay leaf k o := Iff.rfl
theorem mkPL_slot (lay leaf k o j : Nat) (hj : j < hL lay) (hkj : k ≤ j) (hb : mkBase lay ≤ o)
    (hs : (o - mkBase lay) / 16 = plan lay leaf j + 2 ∨ (o - mkBase lay) / 16 = mkSib lay leaf j) : mkPL lay leaf k o :=
  Or.inr (Or.inl ⟨hb, mkKS_mem lay leaf k j _ hj hkj hs⟩)
theorem mkPL_hi (lay leaf k o j : Nat) (hj : j < hL lay) (hkj : k ≤ j) (hb : mkBase lay ≤ o)
    (h8 : (o - mkBase lay) % 16 = 8) (hs : (o - mkBase lay) / 16 = plan lay leaf j + 1) : mkPL lay leaf k o :=
  Or.inr (Or.inr ⟨hb, h8, hs ▸ mkKH_mem lay leaf k j hj hkj⟩)
theorem mkCur_low (lay leaf l b : Nat) (_h0 : lay ≠ 0) : mkCur lay leaf l b = mkBlk lay leaf l + 48 * b + 16 * b - 16 := rfl
theorem mkCur_eq (lay leaf l b : Nat) : mkCur lay leaf l b = mkBlk lay leaf l + 48 * b + 16 * b - 16 := rfl
theorem mkP_rd (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk : k < hL lay) :
    mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 32) ∧ mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 40) ∧
    mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 48 * (1 - leaf / 2 ^ k % 2)) ∧
    mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 48 * (1 - leaf / 2 ^ k % 2) + 8) ∧
    mkP lay leaf k (leaf / 2 ^ k % 2) (mkBo lay leaf k + 24) := by
  have hb := mkBit_lt leaf k
  obtain ⟨hB16, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay leaf k hlay hleaf hk
  simp only [mkP_eq]
  rw [mkBo_plan] at hBase ⊢
  exact ⟨mkPL_slot _ _ _ _ k hk le_rfl (by omega) (Or.inl (by omega)),
    mkPL_slot _ _ _ _ k hk le_rfl (by omega) (Or.inl (by omega)),
    mkPL_slot _ _ _ _ k hk le_rfl (by omega) (Or.inr (by unfold mkSib; omega)),
    mkPL_slot _ _ _ _ k hk le_rfl (by omega) (Or.inr (by unfold mkSib; omega)),
    mkPL_hi _ _ _ _ k hk le_rfl (by omega) (by omega) (by omega)⟩
theorem mkP_step (lay leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hk1 : k + 1 < hL lay) (o : Nat)
    (h8 : o % 8 = 0) (ho : mkP lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) o) :
    (mkP lay leaf k (leaf / 2 ^ k % 2) o ∧ o ≠ mkBo lay leaf k + 16 ∧ o ≠ mkBo lay leaf k + 24) ∧
      (0x1020 + o + 8 ≤ mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) ∨
        mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) + 32 ≤ 0x1020 + o) := by
  have hb := mkBit_lt leaf k
  have hb' := mkBit_lt leaf (k + 1)
  obtain ⟨hB16, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay leaf k hlay hleaf (by omega)
  obtain ⟨hB16', hBlo', hBhi', hBase', hBtop'⟩ := mkBo_facts lay leaf (k + 1) hlay hleaf hk1
  have hg := mkBase_ge lay hlay
  · rw [mkP_eq] at ho; rw [mkP_eq]
    obtain ⟨hF1, -, hF⟩ := route_facts lay leaf hlay hleaf
    rw [mkCur_eq]
    unfold mkBlk
    rw [mkBo_plan] at hBase hBase' ⊢
    rw [mkBo_plan]
    rcases ho with ho | ⟨hge, hs⟩ | ⟨hge, h16, hs⟩
    · have h0 : lay ≠ 0 := by intro h; subst h; have : mkBase 0 = 7664 := rfl; omega
      have hp1 := (hF1 (k + 1) hk1).2 h0
      exact ⟨⟨Or.inl ho, by omega, by omega⟩, Or.inl (by omega)⟩
    · obtain ⟨n1, n2⟩ := hF k hk1 _ (List.mem_append_left _ hs)
      have hw := mkWs_not lay leaf (k + 1) _ n2
      exact ⟨⟨Or.inr (Or.inl ⟨hge, mkKS_succ _ _ _ _ hs⟩), by omega, by omega⟩, by omega⟩
    · obtain ⟨n1, n2⟩ := hF k hk1 _ (List.mem_append_right _ hs)
      have hw := mkWs_not lay leaf (k + 1) _ n2
      exact ⟨⟨Or.inr (Or.inr ⟨hge, h16, mkKH_succ _ _ _ _ hs⟩), by omega, by omega⟩, by omega⟩
theorem mkP_leaf (lay leaf : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (o : Nat) (h8 : o % 8 = 0)
    (ho : mkP lay leaf 0 (leaf / 2 ^ 0 % 2) o) :
    (7664 ≤ o ∧ o < mkBase lay + 16 * mkPS lay) ∧
      (0x1020 + o + 8 ≤ mkCur lay leaf 0 (leaf / 2 ^ 0 % 2) ∨ mkCur lay leaf 0 (leaf / 2 ^ 0 % 2) + 32 ≤ 0x1020 + o) := by
  have hhL : 0 < hL lay := by interval_cases lay <;> decide +kernel
  have hb := mkBit_lt leaf 0
  obtain ⟨hB16, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay leaf 0 hlay hleaf hhL
  have hg := mkBase_ge lay hlay
  · rw [mkP_eq] at ho
    obtain ⟨hF1, hF, -⟩ := route_facts lay leaf hlay hleaf
    rw [mkCur_eq]
    unfold mkBlk
    rw [mkBo_plan] at hBase ⊢
    rcases ho with ho | ⟨hge, hs⟩ | ⟨hge, h16, hs⟩
    · have h0 : lay ≠ 0 := by intro h; subst h; have : mkBase 0 = 7664 := rfl; omega
      have hp1 := (hF1 0 hhL).2 h0
      exact ⟨⟨ho.1, by omega⟩, Or.inl (by omega)⟩
    · obtain ⟨n1, n2⟩ := hF _ (List.mem_append_left _ hs)
      have hw := mkWs_not lay leaf 0 _ n2
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · obtain ⟨n1, n2⟩ := hF _ (List.mem_append_right _ hs)
      have hw := mkWs_not lay leaf 0 _ n2
      exact ⟨⟨by omega, by omega⟩, by omega⟩
theorem Verify.Orig.mono8 {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P P' : Nat → Prop} (h : Orig w P s)
    (hP : ∀ o, o % 8 = 0 → P' o → P o) : Orig w P' s :=
  fun j h1 h2 => h j h1 (hP _ (Nat.mul_mod_right 8 j) h2)
def mkW0 (lay tree : Nat) : Word := if lay = 0 then 64#64 else T3.hyperWord (lay - 1) tree
structure MAfter (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (k : Nat) (v : Digest)
    (s : MachineState) : Prop where
  pc : s.pc = pcOf (mkEc lay leaf k + 1)
  glob : Glob (gkL lay) w pk s
  known : KnownOK (mkLvlK lay k) s
  keep : ∀ r ∈ mkKeep, s.getReg r = u.getReg r
  /-- The level-`k` input sits at its value slot (C2: a lower left node was written 16 bytes low). -/
  node : DigAt s (mkVal lay leaf k (leaf / 2 ^ k % 2)) v
  orig : Orig w (mkP lay leaf k (leaf / 2 ^ k % 2)) s
  dstReg : s.getReg .x12 = BitVec.ofNat 64 (mkCur lay leaf k (leaf / 2 ^ k % 2))
  x28 : k ≠ 0 → lay ≠ 0 → s.getReg .x28 = T3.hyperWord (lay - 1) (u.getReg .x31).toNat
  bufferOrig : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 21984) s
structure MkEnd (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (root : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf (mkFin lay leaf + 1)
  glob : Glob (gkL lay) w pk t
  known : KnownOK (mkKc lay ++ [(.x11, 64)]) t
  keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r
  root : DigAt t (mkDst lay leaf) root
  orig : Orig w (fun o => 7664 ≤ o ∧ o < mkBase lay) t
  dstReg : t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay leaf (hL lay - 1))
def mkHashInputOf (a b : Word) (f : Word → BitVec 8) : Query :=
  ⟨b.toNat / 64 - 1, BitVec.ofNat (8 * (64 * (b.toNat / 64 - 1 + 1))) ((List.range (64 * (b.toNat / 64 - 1 + 1))).foldl
    (fun acc i => acc + (f (a + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0)⟩
theorem mkHashInput_eq_of (s : MachineState) : hashInput s = mkHashInputOf (s.getReg .x10) (s.getReg .x11) s.getByte := rfl
theorem mkHashInput_congr {s t : MachineState} (h10 : t.getReg .x10 = s.getReg .x10)
    (h11 : t.getReg .x11 = s.getReg .x11) (hm : ∀ A, t.getMem A = s.getMem A) : hashInput t = hashInput s := by
  have hb : t.getByte = s.getByte := funext fun a => by simp only [MachineState.getByte, hm]
  rw [mkHashInput_eq_of, mkHashInput_eq_of, h10, h11, hb]
theorem mkK_sub (lay : Nat) (l : List (Reg × Word)) : ∀ p ∈ mkK lay, p ∈ mkK lay ++ l :=
  fun p hp => List.mem_append_left _ hp
theorem mkKeep_sub (l : List Reg) : ∀ r ∈ mkKeep, r ∈ mkKeep ++ l := fun r hr => List.mem_append_left _ hr
theorem mkKc_mkK (lay : Nat) : ∀ p ∈ mkKc lay, p ∈ mkK lay := by
  intro p hp; unfold mkK; unfold mkKc at hp; exact List.mem_append_left _ hp
theorem mkK_cases (lay : Nat) (p : Reg × Word) (hp : p ∈ mkK lay) :
    p ∈ mkKc lay ∨ p = (.x2, BitVec.ofNat 64 0xffbde0) := by
  unfold mkK at hp; unfold mkKc
  rcases List.mem_append.mp hp with h | h
  · exact Or.inl h
  · right; split_ifs at h with h0 <;> simp_all
/-- C2 + C4: a fold writes only its one-word label (`mkLabE`) at window + 16. -/
theorem lvlMem_read (lay ci sh l : Nat) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64)
    (hB : mkBlk lay (mkLeafOf lay ci sh) l + 24 < 2 ^ 64) :
    memEval s (mkLvlMem lay ci sh l) (BitVec.ofNat 64 A) =
      if A = mkBlk lay (mkLeafOf lay ci sh) l + 16 then (mkLabE lay ci sh l).eval s
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold mkLvlMem
  rw [memEval_cons_ofNat _ _ _ _ _ hA (by omega), memEval_nil]
theorem lvlMem_frame (lay ci sh l : Nat) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64)
    (hB : mkBlk lay (mkLeafOf lay ci sh) l + 24 < 2 ^ 64) (h16 : A ≠ mkBlk lay (mkLeafOf lay ci sh) l + 16) :
    memEval s (mkLvlMem lay ci sh l) (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  rw [lvlMem_read _ _ _ _ s A hA hB, if_neg h16]
theorem mk_buffer_ge (lay o : Nat) (hlay : lay < 4)
    (ho : BC.bufferStart (lay-1) ≤ o ∧ o < 21984) : 18928 ≤ o := by
  interval_cases lay <;> simp [BC.bufferStart] at ho <;> omega

theorem mk_buffer_writeHash {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState}
    (lay : Nat) (hlay : lay < 4)
    (hO : Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 21984) s)
    (a : BitVec 256) (d : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d + 32 ≤ WIT + 18928) :
    Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 21984) (writeHash s a) := by
  apply (Orig_writeHash hO a d h12 (by unfold WIT at hd; omega)).mono
  intro o ho
  exact ⟨ho, Or.inr (by have := mk_buffer_ge lay o hlay ho; omega)⟩

theorem lvl_bufferOrig {w : ClaudeWCT.W9.T3M.WBytes} (lay : Layer) (leaf k : Nat)
    (hleaf : leaf < 2 ^ hL lay.val) (hk : k < hL lay.val) (s t : MachineState)
    (hO : lay.val ≠ 0 → Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 21984) s)
    (hmem : ∀ A, t.getMem A =
      memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) leaf) k) A) :
    lay.val ≠ 0 → Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 21984) t := by
  intro h0
  apply (hO h0).frame
  intro j hj ho
  have hmin := mk_buffer_ge lay.val (8*j) lay.isLt ho
  obtain ⟨_, _, hhi, _, _⟩ := mkBo_facts lay.val leaf k lay.isLt hleaf hk
  have he := mkBlk_sh lay.val leaf k lay.isLt hleaf hk
  rw [hmem, lvlMem_frame _ _ _ _ s (WIT+8*j) (by unfold WIT WX at *; omega)
    (by rw [he]; unfold mkBlk; omega) (by rw [he]; unfold WIT mkBlk; omega)]

theorem t3E_eval (l' tree : Nat) (hl : l' < 4) (htr : tree < 2 ^ 32) (s : MachineState)
    (h31 : s.getReg .x31 = BitVec.ofNat 64 tree) (hD : DataOK s) :
    (t3E l').eval s = T3.hyperWord l' tree := by
  simp only [t3E, E.eval, BinOp.eval, kw, h31]
  rw [hdrA_eq l' hl, hD.header l' hl, ofNat_shl', show (16 : Nat) % 2 ^ 64 % 64 = 16 by norm_num, BitVec.or_comm]
  exact hyper_or l' tree hl htr
theorem mkHdrE_eval (lay l tree : Nat) (hlay : lay < 4) (htr : tree < 2 ^ 32) (s : MachineState)
    (h31 : lay ≠ 0 → l = 0 → s.getReg .x31 = BitVec.ofNat 64 tree) (hD : DataOK s)
    (h28 : lay ≠ 0 → l ≠ 0 → s.getReg .x28 = T3.hyperWord (lay - 1) tree) :
    (mkHdrE lay l).eval s = mkW0 lay tree := by
  unfold mkHdrE mkW0
  by_cases hl0 : lay = 0
  · simp [hl0, kw, E.eval]
  · rw [if_neg hl0, if_neg hl0]
    by_cases hl : l = 0
    · rw [if_pos hl]; exact t3E_eval _ _ (by omega) htr s (h31 hl0 hl) hD
    · rw [if_neg hl]; exact h28 hl0 hl
theorem wpath_eq (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    ClaudeWCT.W9.T3M.wpath w lay leaf j =
      ClaudeWCT.W9.T3M.wdig w (mkBo lay.val leaf j + sibOff (leaf / 2 ^ j % 2)) := by
  unfold ClaudeWCT.W9.T3M.wpath; rw [mkBo_eq lay leaf j hleaf]
theorem wpad_eq (w : ClaudeWCT.W9.T3M.WBytes) (lay : Layer) (leaf j : Nat) (hleaf : leaf < 2 ^ hL lay.val) :
    ClaudeWCT.W9.T3M.wmerklePad w lay leaf j = ClaudeWCT.W9.T3M.wdig w (mkBo lay.val leaf j + 32) := by
  unfold ClaudeWCT.W9.T3M.wmerklePad; rw [mkBo_eq lay leaf j hleaf]
theorem mkTw_lo (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (k : Nat) :
    dlo (mkTw w index lay k) = ClaudeWCT.WCT9.merkleWord lay.val (route index lay).2 (mkHp index lay k) := by
  unfold mkTw; exact BitVec.extractLsb'_append_eq_right
theorem mkTw_hi (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (k : Nat) :
    dhi (mkTw w index lay k) = mkHw w lay (route index lay).1 k := by
  unfold mkTw; exact BitVec.extractLsb'_append_eq_left
theorem lvl_input (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1))
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s t : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s)
    (hmem : ∀ A, t.getMem A =
      memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) :
    hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧
      Orig w (fun o => mkP lay.val (route index lay).1 k ((route index lay).1 / 2 ^ k % 2) o ∧
        o ≠ mkBo lay.val (route index lay).1 k + 16 ∧ o ≠ mkBo lay.val (route index lay).1 k + 24) t := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have htree : (route index lay).2 < 2 ^ 32 := tree_lt index lay hidx
  obtain ⟨hB16, hBlo, hBhi, hBase, -⟩ := mkBo_facts lay.val (route index lay).1 k hlay hleaf hk
  have hsh : mkBlk lay.val (mkLeafOf lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)) k =
      mkBlk lay.val (route index lay).1 k := mkBlk_sh _ _ _ hlay hleaf hk
  have hfr : ∀ A, A < 2 ^ 64 →
      A ≠ mkBlk lay.val (route index lay).1 k + 16 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h2
    rw [hmem, lvlMem_frame _ _ _ _ s A hA (by rw [hsh]; unfold mkBlk; omega) (by rw [hsh]; exact h2)]
  have h23 : lay.val = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) :=
    fun h => (hs.keep .x23 (by simp [mkKeep])).trans (hs7 h)
  have hO := hs.orig
  obtain ⟨rp0, rp1, rs0, rs1, rhi⟩ := mkP_rd lay.val (route index lay).1 k hlay hleaf hk
  have hT1 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 24)) = dhi (mkTw w index lay k) := by
    rw [mkTw_hi, hfr _ (by unfold mkBlk; omega) (by omega)]
    have := hO.hi (mkBo lay.val (route index lay).1 k + 16) (by omega) (by unfold WX; omega)
      (by rw [show mkBo lay.val (route index lay).1 k + 16 + 8 = mkBo lay.val (route index lay).1 k + 24 by omega]
          exact rhi)
    rw [show WIT + (mkBo lay.val (route index lay).1 k + 16) + 8 = mkBlk lay.val (route index lay).1 k + 24 by
      unfold WIT mkBlk; omega] at this
    rw [this]; rfl
  have hT0 : t.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 16)) = dlo (mkTw w index lay k) := by
    rw [mkTw_lo, hmem, lvlMem_read _ _ _ _ s _ (by unfold mkBlk; omega) (by rw [hsh]; unfold mkBlk; omega), hsh,
      if_pos rfl]
    by_cases h0 : lay.val = 0
    · have hev := mkHeapE_eval lay.val (route index lay).1 k hlay hleaf hk s h23
      rw [hL_eq] at hev
      have hp1 : 1 ≤ mkHp index lay k ∧ mkHp index lay k < 4096 := by
        have hk12 : k < 12 := by rw [h0] at hk; simpa [hL] using hk
        have hl4 : (route index lay).1 < 4096 := by rw [h0] at hleaf; simpa [hL] using hleaf
        have hh : height lay = 12 := by rw [← hL_eq, h0]; rfl
        unfold mkHp; rw [hh]
        have e1 : 1 ≤ 2 ^ (12 - k - 1) := Nat.one_le_two_pow
        have e2 : 2 ^ (12 - k - 1) * 2 ^ (k + 1) = 4096 := by
          rw [← Nat.pow_add, show 12 - k - 1 + (k + 1) = 12 by omega]
        have e3 : (route index lay).1 / 2 ^ (k + 1) < 2 ^ (12 - k - 1) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), e2]; exact hl4
        have e4 : 2 ^ (12 - k - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
        generalize (route index lay).1 / 2 ^ (k + 1) = q at e3 ⊢
        generalize 2 ^ (12 - k - 1) = p at e1 e3 e4 ⊢
        omega
      unfold mkLabE
      rw [if_pos h0, hev, ClaudeWCT.WCT9.merkleWord, if_pos h0, T3.topNodeWord_eq hp1.1 hp1.2]
    · have hh := mkHdrE_eval lay.val k _ hlay htree s
        (fun h0 _ => (hs.keep .x31 (by simp [mkKeep])).trans (ht5 h0)) hs.glob.2.2.2.2.2
        (fun h0 hk0 => by rw [hs.x28 hk0 h0, ht5 h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      unfold mkLabE
      rw [if_neg h0, addC_eval, hh, mkHeap_eq lay.val (route index lay).1 k hlay hleaf hk (by omega), hL_eq,
        ClaudeWCT.WCT9.merkleWord_lower h0]
      simp only [mkW0, if_neg h0]
      unfold ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
      rfl
  have hlen := mkIn_length w index lay v k
  refine ⟨?_, ?_⟩
  · rw [pad64_of_aligned _ (by rw [hlen])]
    apply hashInput_words8 t _ (mkBlk lay.val (route index lay).1 k) hlen h10 (by unfold mkBlk; omega)
      (by unfold mkBlk; omega) h11
    have hpad := hO.dig (mkBo lay.val (route index lay).1 k + 32) (by omega) (by unfold WX; omega) rp0 rp1
    have e32 : WIT + (mkBo lay.val (route index lay).1 k + 32) = mkBlk lay.val (route index lay).1 k + 32 := by
      unfold WIT mkBlk; omega
    rw [e32, show mkBlk lay.val (route index lay).1 k + 32 + 8 = mkBlk lay.val (route index lay).1 k + 40 by omega] at hpad
    have f32 := hfr (mkBlk lay.val (route index lay).1 k + 32) (by unfold mkBlk; omega) (by omega)
    have f40 := hfr (mkBlk lay.val (route index lay).1 k + 40) (by unfold mkBlk; omega) (by omega)
    have f0 := hfr (mkBlk lay.val (route index lay).1 k) (by unfold mkBlk; omega) (by omega)
    have f8 := hfr (mkBlk lay.val (route index lay).1 k + 8) (by unfold mkBlk; omega) (by omega)
    have f48 := hfr (mkBlk lay.val (route index lay).1 k + 48) (by unfold mkBlk; omega) (by omega)
    have f56 := hfr (mkBlk lay.val (route index lay).1 k + 56) (by unfold mkBlk; omega) (by omega)
    have hnode := hs.node
    unfold mkIn
    rw [wpath_eq w lay _ _ hleaf, wpad_eq w lay _ _ hleaf]
    rcases (show (route index lay).1 / 2 ^ k % 2 = 0 ∨ (route index lay).1 / 2 ^ k % 2 = 1 by omega) with hb | hb
    · rw [hb] at hnode hO rs0 rs1
      simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide +kernel, if_false]
      have hsib := hO.dig (mkBo lay.val (route index lay).1 k + 48) (by omega) (by unfold WX; omega)
        (by simpa using rs0) (by simpa using rs1)
      have e48 : WIT + (mkBo lay.val (route index lay).1 k + 48) = mkBlk lay.val (route index lay).1 k + 48 := by
        unfold WIT mkBlk; omega
      rw [e48, show mkBlk lay.val (route index lay).1 k + 48 + 8 = mkBlk lay.val (route index lay).1 k + 56 by omega] at hsib
      have hn0 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k)) = v.extractLsb' 0 64 := by
        have := hnode.1; simpa [mkVal] using this
      have hn8 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 8)) = v.extractLsb' 64 64 := by
        have := hnode.2; simpa [mkVal] using this
      rw [wordsOf_blk4, f0, f8, hT0, hT1, f32, f40, f48, f56, hn0, hn8, hpad.1, hpad.2, hsib.1, hsib.2]
    · rw [hb] at hnode hO rs0 rs1
      simp only [hb, show (1 : Nat) ≠ 0 by decide +kernel, if_false, sibOff, if_true, Nat.add_zero]
      have hsib := hO.dig (mkBo lay.val (route index lay).1 k) (by omega) (by unfold WX; omega)
        (by simpa using rs0) (by simpa using rs1)
      have e0 : WIT + mkBo lay.val (route index lay).1 k = mkBlk lay.val (route index lay).1 k := by unfold WIT mkBlk; omega
      rw [e0] at hsib
      have hn48 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 48)) = v.extractLsb' 0 64 := by
        have := hnode.1; simpa [mkVal] using this
      have hn56 : s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 56)) = v.extractLsb' 64 64 := by
        have := hnode.2; simpa [mkVal, Nat.add_assoc] using this
      rw [wordsOf_blk4, f0, f8, hT0, hT1, f32, f40, f48, f56, hn48, hn56, hpad.1, hpad.2, hsib.1, hsib.2]
  · intro j hj ⟨h1, h2, h3⟩
    rw [hfr _ (by unfold WIT WX at *; omega) (by unfold WIT mkBlk; omega)]
    exact hO j hj h1
/-- C4: the top root answer address, as the compare reads it (`cmpDst`, from `topRootSlot`). -/
theorem mkDst_cmp_all : (List.range 64).all (fun c => mkCur 0 (c * 64) 11 (c / 32 % 2) == cmpDst c) = true := by
  decide +kernel
theorem mkDst_cmp (leaf : Nat) (hleaf : leaf < 4096) : cmpDst (mkSh 0 1 leaf) = mkDst 0 leaf := by
  have hsh : mkSh 0 1 leaf = leaf / 64 := by simp only [mkSh, mkLo, mkBits]; norm_num; omega
  have h := List.all_eq_true.mp mkDst_cmp_all (leaf / 64) (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq] at h
  have e0 : leaf / 64 * 64 / 64 % 64 = leaf / 64 % 64 := by omega
  have e1 : plan 0 leaf 11 = plan 0 (leaf / 64 * 64) 11 := by simp [plan, topPlan, e0]
  have e2 : leaf / 2048 % 2 = leaf / 64 / 32 % 2 := by omega
  rw [hsh, ← h]
  unfold mkDst mkCur mkVal mkBlk mkBo
  rw [if_pos rfl, e1, e2]
theorem mkDst_bound (lay leaf : Nat) (hleaf : lay = 0 → leaf < 4096) :
    mkDst lay leaf % 8 = 0 ∧ mkDst lay leaf + 32 ≤ 2^23 ∧ (lay = 0 → WLO ≤ mkDst lay leaf) := by
  by_cases h : lay = 0
  · subst h
    have hl := hleaf rfl
    have hb := mkBit_lt leaf 11
    obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts 0 leaf 11 (by decide) (by simpa [hL] using hl) (by decide)
    unfold mkDst mkCur mkVal mkBlk WLO WIT
    rw [if_pos rfl]
    refine ⟨by omega, by omega, fun _ => by omega⟩
  · unfold mkDst; rw [if_neg h]; exact ⟨by decide, by decide, fun h' => absurd h' h⟩
theorem safeDest_dst (lay leaf : Nat) (hlay : lay < 4) (hleaf : lay = 0 → leaf < 4096) :
    safeDest (mkDst lay leaf) = true := by
  by_cases h : lay = 0
  · obtain ⟨h8, h23, hlo⟩ := mkDst_bound lay leaf hleaf
    exact safeDest_hi _ (hlo h) h8 h23
  · simp [mkDst,h,safeDest,pSlots,CTRW,WIT,MEMORY_BYTES]
    intro x hx; right; omega
theorem mkMove_next (lay k : Nat) (hk : k+1 < hL lay) : mkMove lay k = 1 := by
  by_cases h : lay = 0
  · subst lay
    have : k < 11 := by change k+1<12 at hk; omega
    simp [mkMove]; omega
  · simp [mkMove,h]
theorem mkMove_last (lay k : Nat) (hk : k+1 = hL lay) :
    mkMove lay k = if lay = 0 then 0 else 1 := by
  by_cases h : lay = 0
  · subst lay
    have : k = 11 := by change k+1=12 at hk; omega
    simp [mkMove,this]
  · simp [mkMove,h]
/-- C2: the level-`j` input of a lower path keeps the HIGH half iff it is a left child. -/
def mkHB (_lay leaf j : Nat) : Bool := decide (leaf / 2 ^ j % 2 = 0)
theorem mk_node_at (lay leaf j : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hj : j < hL lay)
    (t : MachineState) (a : BitVec 256)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay leaf j (leaf / 2 ^ j % 2))) :
    DigAt (writeHash t a) (mkVal lay leaf j (leaf / 2 ^ j % 2)) (Verify.vHalf (mkHB lay leaf j) a) := by
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay leaf j hlay hleaf hj
  have hb := mkBit_lt leaf j
  · rw [mkCur_eq] at h12
    rcases (show leaf / 2 ^ j % 2 = 0 ∨ leaf / 2 ^ j % 2 = 1 by omega) with hb0 | hb1
    · have e : mkHB lay leaf j = true := by simp [mkHB, hb0]
      rw [e, Verify.vHalf_true]
      rw [hb0] at h12 ⊢
      have h := DigAt.writeHash_hi t a _ h12 (by unfold mkBlk; omega)
      rwa [show mkBlk lay leaf j + 48 * 0 + 16 * 0 - 16 + 16 = mkVal lay leaf j 0 by unfold mkVal mkBlk; omega] at h
    · have e : mkHB lay leaf j = false := by simp [mkHB, hb1]
      rw [e, Verify.vHalf_false]
      rw [hb1] at h12 ⊢
      have h := DigAt.writeHash_lo t a _ h12 (by unfold mkBlk; omega)
      rwa [show mkBlk lay leaf j + 48 * 1 + 16 * 1 - 16 = mkVal lay leaf j 1 by unfold mkVal mkBlk; omega] at h
theorem mkCur_bounds (lay leaf j b : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hj : j < hL lay)
    (hb : b < 2) :
    WLO ≤ mkCur lay leaf j b ∧ mkCur lay leaf j b % 8 = 0 ∧ mkCur lay leaf j b + 32 ≤ 0x1020 + 16856 := by
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay leaf j hlay hleaf hj
  unfold mkCur mkVal mkBlk WLO WIT
  omega
theorem lvl_after (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (hlay : lay < 4)
    (hleaf : leaf < 2 ^ hL lay) (k : Nat) (hk : k < hL lay) (t : MachineState)
    (hglob : Glob (gkL lay) w pk t) (hknown : KnownOK (mkKc lay ++ [(.x11, 64)]) t)
    (hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r)
    (h28 : lay ≠ 0 → t.getReg .x28 = T3.hyperWord (lay - 1) (u.getReg .x31).toNat)
    (horig : Orig w (fun o => mkP lay leaf k (leaf / 2 ^ k % 2) o ∧ o ≠ mkBo lay leaf k + 16 ∧
      o ≠ mkBo lay leaf k + 24) t)
    (hbuffer : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 21984) t)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay leaf k)) (a : BitVec 256) :
    (k + 1 < hL lay → t.pc = pcOf (mkEc lay leaf (k + 1)) →
      t.getReg .x12 = BitVec.ofNat 64 (mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2)) →
      MAfter w pk lay leaf u (k + 1) (Verify.vHalf (mkHB lay leaf (k + 1)) a) (writeHash t a)) ∧
    (lay = 0 → k + 1 = hL lay → t.pc = pcOf (mkFin lay leaf) → t.getReg .x12 = BitVec.ofNat 64 (mkDst lay leaf) →
      MkEnd w pk lay leaf u (a.extractLsb' 0 128) (writeHash t a)) := by
  refine ⟨fun hk1 hpc h12 => ?_, fun hl0 hk1 hpc h12 => ?_⟩
  · obtain ⟨hB16', hBlo', hBhi', -, -⟩ := mkBo_facts lay leaf (k + 1) hlay hleaf hk1
    have hb := mkBit_lt leaf (k + 1)
    obtain ⟨hcw, hc8, hc32⟩ := mkCur_bounds lay leaf (k + 1) _ hlay hleaf hk1 hb
    have hd : mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) + 32 < 2 ^ 64 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_hi _ hcw hc8 (by omega))
    · intro p hp
      rw [writeHash_getReg]
      exact hknown p (by simpa [mkLvlK] using hp)
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · exact mk_node_at lay leaf (k + 1) hlay hleaf hk1 t a h12
    · have hw2 := Orig_writeHash horig a _ h12 hd
      refine hw2.mono8 (fun o h8 ho => ?_)
      obtain ⟨hA, hB⟩ := mkP_step lay leaf k hlay hleaf hk1 o h8 ho
      exact ⟨hA, by unfold WIT; omega⟩
    · rw [writeHash_getReg]; exact h12
    · intro _ h0; rw [writeHash_getReg]; exact h28 h0
    · intro h0
      exact mk_buffer_writeHash lay hlay (hbuffer h0) a _ h12
        (by unfold WIT; omega)
  · subst hl0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [writeHash_pc, hpc, pcOf_add4]
    · exact Glob_writeHash hglob a _ h12 (safeDest_dst 0 leaf hlay (fun _ => by simpa [hL] using hleaf))
    · intro p hp; rw [writeHash_getReg]; exact hknown p hp
    · intro r hr; rw [writeHash_getReg]; exact hkeep r hr
    · exact DigAt.writeHash_lo t a _ h12
        (by have := (mkDst_bound 0 leaf (fun _ => by simpa [hL] using hleaf)).2.1; omega)
    · intro j _ hj
      have h1 := hj.1
      have h2 := hj.2
      simp only [mkBase, List.getD_cons_zero] at h2
      omega
    · rw [writeHash_getReg]; exact h12
    · rw [writeHash_getReg, h10, show k = hL 0 - 1 by omega]
theorem dispTgt_eval (leaf : Nat) (hleaf : leaf < 4096) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 (16 * (2 ^ hL 0 + leaf))) :
    (mkDispTgt (mkSh 0 0 leaf)).eval s = pcOf (mkTabW 0 1 (mkSh 0 1 leaf)) := by
  have hsh0 : mkSh 0 0 leaf = leaf % 64 := by simp only [mkSh, mkLo, mkBits]; norm_num
  have hsh1 : mkSh 0 1 leaf = leaf / 64 := by simp only [mkSh, mkLo, mkBits]; norm_num; omega
  rw [hsh0, hsh1]
  unfold mkDispTgt
  simp only [E.eval, BinOp.eval, addC_eval, h23, show hL 0 = 12 from rfl, mkTabW, Nat.reduceEqDiff, and_self, if_true, pcOf]
  have hm : BitVec.ofNat 64 (16 * (2 ^ 12 + leaf)) + (BitVec.ofNat 64 1432 - BitVec.ofNat 64 (16 * (leaf % 64))) =
      BitVec.ofNat 64 (0x1000 + 4 * (15718 + 256 * (leaf / 64))) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hm, even_andNot1' _ (by omega)]
theorem lfK_mkK (lay : Nat) : ∀ p ∈ mkK lay, p ∈ lfK lay := by
  intro p hp
  by_cases h0 : lay = 0
  · subst h0
    simp only [mkK, gkL, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    repeat' first | subst p | rcases hp with hp | hp
    all_goals simp [lfK, postLf, leafK, lfKeepK, gkL]
  · simp only [mkK, gkL_low h0, h0, if_false, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    repeat' first | subst p | rcases hp with hp | hp
    all_goals simp [lfK, postLf, leafK, lfKeepK, h0, gkL_low h0, baseK]
theorem lvl_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1))
    (hx6 : lay.val = 0 → u.getReg .x6 = 520192)
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (k : Nat) (hk : k < hL lay.val) (hlive : k < hL lay.val - (if lay.val = 0 then 0 else 1)) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) :
    ∃ t, Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (mkIn w index lay v k)) ∧
      ∀ a : BitVec 256,
        (k + 1 < hL lay.val →
          MAfter w pk lay.val (route index lay).1 u (k + 1) (Verify.vHalf (mkHB lay.val (route index lay).1 (k + 1)) a)
            (writeHash t a)) ∧
        (k + 1 = hL lay.val → MkEnd w pk lay.val (route index lay).1 u (a.extractLsb' 0 128) (writeHash t a)) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hci, hlo, hkk, hdisp, hnext, hlast⟩ := mk_facts lay.val k hlay hk
  obtain ⟨hB8, hBlo, hBhi, hBase, -⟩ := mkBo_facts lay.val (route index lay).1 k hlay hleaf hk
  have hlk : mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) = k := by omega
  have hblk := BC.mkBlockCheck_at lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) hlay hci
    (mkSh_lt _ _ _)
  have hliveChunk : k - mkLo lay.val (mkCi lay.val k) <
      mkBits lay.val (mkCi lay.val k) - (if lay.val = 0 then 0 else 1) := by
    by_cases h0 : lay.val = 0
    · simpa [h0] using hkk
    · simpa [mkCi, mkLo, mkBits, h0] using hlive
  have hlvl := BC.mkLvl_of hblk _ hliveChunk
  have hpc0 : s.pc = pcOf (BC.mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
      mkOff lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) + 2) := by rw [hs.pc]; rfl
  have hkn0 : KnownOK (mkLvlK lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) s := by
    rw [hlk]; exact hs.known
  have hknAddr : KnownOK (mkLvlKN lay.val (mkCi lay.val k)
      (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))) s := by
    intro p hp
    simp only [mkLvlKN, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hkn0 p hp
    · split_ifs at hp with h0
      · simp only [List.mem_singleton] at hp
        subst p
        dsimp only
        rw [mkSh_bit _ _ _ _ hkk, hlk, mkCur_sh _ _ _ _ hlay hleaf hk]
        exact hs.dstReg
      · simp at hp
  have h23 : lay.val = 0 → s.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) :=
    fun h => (hs.keep .x23 (by simp [mkKeep])).trans (hs7 h)
  by_cases hd : lay.val = 0 ∧ k = 5
  ·
    obtain ⟨hl0, hk5⟩ := hd
    have hdt : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = true := by
      rw [hdisp]; simp [hl0, hk5]
    have hD : mkLvlCheckD lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [BC.mkLvlCheck, hdt, if_true] at hlvl; exact hlvl
    obtain ⟨t1, ht1⟩ := mkSpec_run hD s (by simpa [BC.mkShp, hl0] using hpc0) hknAddr (by simp [mkLvlSpecD]) (by simp)
    have hleaf0 : (route index lay).1 < 4096 := by rw [hl0] at hleaf; simpa [hL] using hleaf
    have hpc1 : t1.pc = pcOf (mkTabW 0 1 (mkSh 0 1 (route index lay).1)) := by
      rw [ht1.spc (mkDispTgt (mkSh 0 0 (route index lay).1)) (by simp [mkLvlSpecD, hl0, hk5, mkCi]),
        dispTgt_eval _ hleaf0 s (by simpa [dispatchHeap, s7Bias, hL, hl0] using h23 hl0)]
    have hkn1 : KnownOK (mkEntK 0 1) t1 := by
      intro p hp
      simp only [mkEntK, Nat.reduceEqDiff, and_self, if_true, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact ht1.known p (List.mem_append_left _ (by rw [hl0]; exact hp))
      · exact ht1.known (.x10, BitVec.ofNat 64 (mkBlk 0 0 5))
          (by simp [mkLvlPostD, hl0, hk5, mkCi, mkLo, mkBlk, mkBo, mkPlan_top5])
    have hent := BC.mkEnt_of (BC.mkBlockCheck_at 0 1 (mkSh 0 1 (route index lay).1) (by decide +kernel) (by decide +kernel) (mkSh_lt _ _ _))
    obtain ⟨t, ht⟩ := mkSpec_run hent t1 hpc1 hkn1 (by simp [BC.mkEntSpec]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t := by
      have := ht1.steps.trans ht.steps
      simp only [mkLvlSpecD, BC.mkEntSpec, Nat.reduceEqDiff, and_self, if_true, hlk] at this
      rw [show mkLvlSt lay.val k = mkBody lay.val k + 1 + 2 by simp [mkLvlSt,hl0,hk5,mkMove]]
      exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A
      rw [ht.mem]
      show memEval t1 [] A = _
      rw [memEval_nil, ht1.mem]
      show memEval s (mkLvlMem _ _ _ (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)))) A = _
      rw [hlk]
    have hkt1 : KnownOK (mkLvlPostD lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
      (k - mkLo lay.val (mkCi lay.val k))) t1 := ht1.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k) := by
      rw [ht.keep .x10 (by simp [mkEntKeep])]
      have := hkt1 (.x10, BitVec.ofNat 64 (mkBlk lay.val
        (mkLeafOf lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1))
        (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostD])
      rw [this, hlk, mkBlk_sh _ _ _ hlay hleaf hk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
      rw [ht.keep .x11 (by simp [mkEntKeep])]
      exact hkt1 (.x11, 64) (by simp [mkLvlPostD])
    have hkt : KnownOK (mkEntPost 0 1 (mkSh 0 1 (route index lay).1)) t := ht.known
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val (route index lay).1 (k + 1) ((route index lay).1 / 2 ^ (k + 1) % 2)) := by
      have hb : mkSh 0 1 (route index lay).1 % 2 = (route index lay).1 / 64 % 2 := by
        have := mkSh_bit 0 1 (route index lay).1 0 (by decide +kernel)
        rw [show mkLo 0 1 = 6 from rfl] at this
        simpa using this
      have hc6 := mkCur_sh 0 (route index lay).1 6 ((route index lay).1 / 64 % 2) (by decide)
        (by rw [hl0] at hleaf; exact hleaf) (by decide)
      rw [show mkCi 0 6 = 1 from rfl] at hc6
      rw [hkt (.x12, BitVec.ofNat 64 (mkCur 0 (mkLeafOf 0 1 (mkSh 0 1 (route index lay).1)) (mkLo 0 1)
        (mkSh 0 1 (route index lay).1 % 2))) (by simp [mkEntPost]),
        hl0, hk5, show mkLo 0 1 = 6 from rfl, hb, hc6]
      rfl
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob (gkL lay.val) w pk t := by
      rw [hl0]; exact ht.glob _ _ _ (ht1.glob _ _ _ hs.glob (RelOK.nil s)) (RelOK.nil t1)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by rw [← hl0]; simp [mkEntPost, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr
      rw [ht.keep r (mkKeep_sub _ r hr), ht1.keep r (mkKeep_sub _ r hr)]; exact hs.keep r hr
    have h28 : lay.val ≠ 0 → t.getReg .x28 = T3.hyperWord (lay.val - 1) (u.getReg .x31).toNat :=
      fun h => absurd hl0 h
    have hk6 : k + 1 < hL lay.val := by rw [hl0, hk5]; decide +kernel
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 h12 (by unfold mkBlk; omega) (by decide +kernel) (by unfold mkBlk; omega)
        (mkCur_bounds lay.val (route index lay).1 (k + 1) ((route index lay).1 / 2 ^ (k + 1) % 2) hlay hleaf hk6
          (mkBit_lt _ _)).2.1
        (by have := (mkCur_bounds lay.val (route index lay).1 (k + 1) ((route index lay).1 / 2 ^ (k + 1) % 2) hlay
              hleaf hk6 (mkBit_lt _ _)).2.2
            omega), hinp, fun a => ?_⟩
    obtain ⟨hA1, -⟩ := lvl_after w pk lay.val (route index lay).1 u hlay hleaf k hk t hglob hknown hkeep h28 horig (lvl_bufferOrig lay _ k hleaf hk s t hs.bufferOrig hmem) h10 a
    refine ⟨fun _ => hA1 hk6 ?_ h12, fun h => absurd h (by omega)⟩
    rw [ht.pc rfl]
    simp only [BC.mkEntSpec, mkEc, hl0, hk5, show mkCi 0 6 = 1 from rfl, show mkLo 0 1 = 6 from rfl]
    rfl
  ·
    have hdf : mkIsDisp lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k)) = false := by
      rw [hdisp]; exact decide_eq_false hd
    have hN : BC.mkLvlCheckN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k)) = true := by
      simp only [BC.mkLvlCheck, hdf, Bool.false_eq_true, if_false] at hlvl; exact hlvl
    have hknN := hknAddr
    obtain ⟨t, ht⟩ := mkSpec_run hN s hpc0 hknN (by simp [BC.mkLvlSpecN, mkLvlSpecN]) (by simp)
    have hst : Steps image s (mkLvlSt lay.val k) (mkLvlSt lay.val k) t := by
      have := ht.steps
      simp only [BC.mkLvlSpecN, mkLvlSpecN, hlk] at this
      rw [mkLvlSt_ne _ _ hd]; exact this
    have hmem : ∀ A, t.getMem A =
        memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) k) A := by
      intro A; rw [ht.mem]; simp only [BC.mkLvlSpecN, mkLvlSpecN, hlk]
    have hkt : KnownOK (mkLvlPostN lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1)
        (k - mkLo lay.val (mkCi lay.val k))) t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k) := by
      have := hkt (.x10, BitVec.ofNat 64 (mkBlk lay.val
        (mkLeafOf lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1))
        (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))))) (by simp [mkLvlPostN])
      rw [this, hlk, mkBlk_sh _ _ _ hlay hleaf hk]
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [mkLvlPostN])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k))) :=
      hkt (.x12, BitVec.ofNat 64 (mkNextA2 lay.val (mkCi lay.val k)
        (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k)))) (by simp [mkLvlPostN])
    obtain ⟨hinp, horig⟩ := lvl_input w pk index lay u hidx hs7 ht5 k hk v s t hs hmem h10 h11
    have hglob : Glob (gkL lay.val) w pk t := ht.glob _ _ _ hs.glob (RelOK.nil s)
    have hknown : KnownOK (mkKc lay.val ++ [(.x11, 64)]) t := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hkt p (by simp [mkLvlPostN, hp])
      · simp only [List.mem_singleton] at hp; subst hp; exact h11
    have hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r := by
      intro r hr; rw [ht.keep r (mkKeep_sub _ r hr)]; exact hs.keep r hr
    have h28 : lay.val ≠ 0 → t.getReg .x28 = T3.hyperWord (lay.val - 1) (u.getReg .x31).toNat := by
      intro hl0
      by_cases hk0 : k = 0
      · have hreg : mkLvlRegs lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) =
            [(.x28, t3E (lay.val - 1))] := by
          rw [hlk, hk0]; simp [mkLvlRegs, hl0]
        have hr : t.getReg .x28 = (t3E (lay.val - 1)).eval s :=
          ht.regs (.x28, t3E (lay.val - 1)) (by simp only [BC.mkLvlSpecN, mkLvlSpecN]; rw [hreg]; exact List.mem_singleton.mpr rfl)
        have htr := tree_lt index lay hidx
        rw [hr, ht5 hl0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact t3E_eval _ _ (by omega) htr s ((hs.keep .x31 (by simp [mkKeep])).trans (ht5 hl0)) hs.glob.2.2.2.2.2
      · have hkp : Reg.x28 ∈ mkLvlKeep lay.val (mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k))) := by
          rw [hlk]; simp [mkLvlKeep, hk0]
        rw [ht.keep .x28 (List.mem_append_right _ (List.mem_cons_of_mem _ hkp))]
        exact hs.x28 hk0 hl0
    have hpcT : t.pc = pcOf (BC.mkShp lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) (route index lay).1) +
        mkOff lay.val (mkCi lay.val k) (k - mkLo lay.val (mkCi lay.val k) + 1) + mkMove lay.val k) := by
      have h := ht.pc rfl
      simpa only [BC.mkLvlSpecN, mkLvlSpecN,hlk] using h
    have hdst : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧ d % 8 = 0 ∧ d + 32 ≤ 2 ^ 24 := by
      by_cases hk1 : k + 1 < hL lay.val
      · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
        refine ⟨_, h12, ?_⟩
        have := mkBo_facts lay.val (route index lay).1 (k + 1) hlay hleaf hk1
        simp only [mkNextA2, if_pos hn3]
        rw [show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega,
          mkCur_next _ _ _ _ hlay hleaf hk1 hn1]
        have := mkCur_bounds lay.val (route index lay).1 (k + 1) _ hlay hleaf hk1
          (mkBit_lt (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k) + 1))
        omega
      · have hk1' : k + 1 = hL lay.val := by omega
        obtain ⟨-, hn2, -⟩ := hlast hk1'
        refine ⟨_, h12, ?_⟩
        simp only [mkNextA2, if_neg hn2]
        split
        · rw [hlk, mkCur_sh _ _ _ _ hlay hleaf hk]
          have := mkCur_bounds lay.val (route index lay).1 k _ hlay hleaf hk
            (mkBit_lt (mkSh lay.val (mkCi lay.val k) (route index lay).1) (k - mkLo lay.val (mkCi lay.val k)))
          omega
        · omega
    obtain ⟨d, hd12, hd8, hd32⟩ := hdst
    refine ⟨t, hst, ht.ecall rfl, hknown (.x5, 0) (by simp [mkKc, baseK]),
      hashArgs_of t _ 64 _ h10 h11 hd12 (by unfold mkBlk; omega) (by decide +kernel) (by unfold mkBlk; omega) hd8 hd32,
      hinp, fun a => ?_⟩
    obtain ⟨hA1, hA2⟩ := lvl_after w pk lay.val (route index lay).1 u hlay hleaf k hk t hglob hknown hkeep h28 horig (lvl_bufferOrig lay _ k hleaf hk s t hs.bufferOrig hmem) h10 a
    refine ⟨fun hk1 => hA1 hk1 ?_ ?_, fun hk1 => hA2 (by by_contra h0; rw [if_neg h0] at hlive; omega) hk1 ?_ ?_⟩
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [hpcT,mkMove_next _ _ hk1]; unfold mkEc; rw [hn1, hn2]
    · obtain ⟨hn1, hn2, hn3⟩ := hnext hk1 hd
      rw [h12]; simp only [mkNextA2, if_pos hn3]
      rw [mkSh_bit _ _ _ _ hn3, show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k)) + 1 = k + 1 by omega,
        show mkLo lay.val (mkCi lay.val k) + (k - mkLo lay.val (mkCi lay.val k) + 1) = k + 1 by omega,
        mkCur_next _ _ _ _ hlay hleaf hk1 hn1]
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [hpcT,mkMove_last _ _ hk1]; unfold mkFin; rw [← hl1, hl3]
    · obtain ⟨hl1, hl2, hl3⟩ := hlast hk1
      rw [h12]; simp only [mkNextA2, if_neg hl2]
      by_cases h0 : lay.val = 0
      · have hk11 : k = 11 := by rw [h0] at hk1; simp [hL] at hk1; omega
        subst hk11
        rw [if_pos h0, mkSh_bit _ _ _ _ hkk, hlk, mkCur_sh _ _ _ _ hlay hleaf hk]
        unfold mkDst; rw [if_pos h0, h0]; rfl
      · simp [h0,mkDst]
/-- C2: the half a fold keeps is its output node's side (`2 ^ (h-k-1)` is even below the root). -/
theorem mkHi_eq (index : Nat) (lay : Layer) (k : Nat) (hk1 : k + 1 < hL lay.val) :
    ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay k) = mkHB lay.val (route index lay).1 (k + 1) := by
  have hl := lay.isLt
  have hpar : (2 ^ (height lay - k - 1) + (route index lay).1 / 2 ^ (k + 1)) % 2 =
      (route index lay).1 / 2 ^ (k + 1) % 2 := by
    rw [← hL_eq]
    obtain ⟨m, hm⟩ : ∃ m, hL lay.val - k - 1 = m + 1 := ⟨hL lay.val - k - 2, by omega⟩
    rw [hm, pow_succ]; omega
  unfold mkHp mkHB ClaudeWCT.WCT9.lowerHigh
  rw [hpar]
  simp [hl]
theorem mkHi_leaf (lay : Layer) (leaf : Nat) :
    ClaudeWCT.WCT9.lowerHigh lay.val leaf = mkHB lay.val leaf 0 := by
  have hl := lay.isLt
  unfold mkHB ClaudeWCT.WCT9.lowerHigh
  simp [hl]
def mkStop (lay : Nat) : Nat := hL lay - (if lay = 0 then 0 else 1)
def MkStop (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState)
    (v : Digest) (s : MachineState) : Prop :=
  if lay = 0 then MkEnd w pk lay leaf u v s else MAfter w pk lay leaf u (mkStop lay) v s
def mkCycR (lay : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay k + 8 + mkCycR lay (k + 1) n
def mkFuelR (lay : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => mkLvlSt lay k + 1 + mkFuelR lay (k + 1) n
theorem merkle_rest (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState) (hidx : index < 2 ^ 31)
    (hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1))
    (hx6 : lay.val = 0 → u.getReg .x6 = 520192)
    (ht5 : lay.val ≠ 0 → u.getReg .x31 = BitVec.ofNat 64 (route index lay).2)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → GoodQP P t N C Q A (K root)) :
    ∀ n k v s, k + n = mkStop lay.val → k < hL lay.val → MAfter w pk lay.val (route index lay).1 u k v s →
      GoodQP P s (N + mkFuelR lay.val k n) (C + mkCycR lay.val k n) Q (A + mkCycR lay.val k n)
        (ccM ((List.range' k n).foldlM (mkStep w index lay) v) K) := by
  intro n
  induction n with
  | zero =>
    intro k v s hkn hk hs
    have h0 : lay.val ≠ 0 := by intro h; simp [mkStop, h] at hkn; rw [h] at hk; omega
    simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
    apply hK v s
    simpa [MkStop, h0, ← hkn] using hs
  | succ m ih =>
    intro k v s hkn hk hs
    have hlive : k < hL lay.val - (if lay.val = 0 then 0 else 1) := by change k < mkStop lay.val; omega
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step w pk index lay u hidx hs7 hx6 ht5 k hk hlive v s hs
    rw [List.range'_succ, List.foldlM_cons, mkStep_eq]
    have H : ∀ a : BitVec 256, GoodQP P (writeHash t a) (N + mkFuelR lay.val (k + 1) m) (C + mkCycR lay.val (k + 1) m) Q
        (A + mkCycR lay.val (k + 1) m)
        (ccM ((fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v')
          (Verify.vHalf (ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay k)) a)) K) := by
      intro a
      by_cases he : k + 1 = hL lay.val
      · have hm : m = 0 := by unfold mkStop at hkn; split_ifs at hkn <;> omega
        subst m
        have h0 : lay.val = 0 := by unfold mkStop at hkn; split_ifs at hkn <;> omega
        have e : ClaudeWCT.WCT9.lowerHigh lay.val (mkHp index lay k) = false := by
          have hl4 := leaf_lt index lay
          have h1 : mkHp index lay k = 1 := by
            unfold mkHp
            rw [← hL_eq, ← he]
            rw [← he] at hl4
            simp [Nat.div_eq_of_lt hl4]
          rw [h1]; exact ClaudeWCT.WCT9.lowerHigh_one _
        rw [e, Verify.vHalf_false]
        simp only [List.range'_zero, List.foldlM_nil, ccM_pure, mkFuelR, mkCycR, Nat.add_zero]
        apply hK
        simpa [MkStop, h0] using (hpost a).2 he
      · rw [mkHi_eq index lay k (by omega)]
        exact ih (k + 1) _ _ (by omega) (by omega) ((hpost a).1 (by omega))
    have hg := GoodQP.vHash_bind _ (f := fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') hf h5 hv hin H
    rw [mkIn_blocks] at hg
    simp only [mkFuelR, mkCycR]
    exact GoodQP.stepsQ hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
def merklePrefix (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.range (mkStop lay.val)).foldlM (mkStep w index lay) value
def mkFuel (lay : Nat) : Nat := 2 + mkFuelR lay 0 (mkStop lay)
def mkCyc (lay : Nat) : Nat := 1 + 8 * lfBlocks lay + mkCycR lay 0 (mkStop lay)
/-- C4: the top path is 12 instructions shorter (one label store per fold): 268 -> 256 cycles, 73 -> 61 fuel.
Campaign T51: the top leaf has 13 blocks (832 B), one fewer than #938: 248 cycles. -/
theorem mkCyc_vals : mkCyc 0 = 248 ∧ mkCyc 1 = 165 ∧ mkCyc 2 = 153 ∧ mkCyc 3 = 153 := by decide +kernel
theorem mkFuel_vals : mkFuel 0 = 61 ∧ mkFuel 1 = 36 ∧ mkFuel 2 = 31 ∧ mkFuel 3 = 31 := by decide +kernel
theorem mkBits_stabBits (lay : Nat) (hlay : lay < 4) : mkBits lay 0 = stabBits lay := by
  interval_cases lay <;> decide +kernel
theorem merkle_good (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState)
    (hidx : index < 2 ^ 31) (hu : LeafOut w pk index lay ends u)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → GoodQP P t N C Q A (K root)) :
    GoodQP P u (N + mkFuel lay.val) (C + mkCyc lay.val) Q (A + mkCyc lay.val)
      (ccM (ClaudeWCT.WCT9.leafHashW lay (route index lay).2 (route index lay).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
        (ClaudeWCT.W9.T3M.wleafHigh w lay) ends >>= merklePrefix w index lay) K) := by
  have hlay := lay.isLt
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  have hkU : KnownOK (lfK lay.val) u := hu.glob.1
  have hknown : KnownOK (mkKc lay.val) u := fun p hp => hkU p (lfK_mkK _ p (mkKc_mkK _ p hp))
  have hhL : 0 < hL lay.val := by interval_cases lay.val <;> decide +kernel
  have hent := BC.mkEnt_of (BC.mkBlockCheck_at lay.val 0 (mkSh lay.val 0 (route index lay).1) hlay
    (by unfold mkNch; split <;> omega) (mkSh_lt _ _ _))
  have hpc : u.pc = pcOf (mkTabW lay.val 0 (mkSh lay.val 0 (route index lay).1)) := by
    rw [hu.pc]
    have e2 : mkSh lay.val 0 (route index lay).1 = (route index lay).1 % 2 ^ stabBits lay.val := by
      simp only [mkSh, show mkLo lay.val 0 = 0 by simp [mkLo], Nat.pow_zero, Nat.div_one, mkBits_stabBits _ hlay]
    rw [e2]; simp [mkTabW]
  have hEntKnown : KnownOK (mkEntK lay.val 0) u := by
    simpa [mkEntK] using hknown
  obtain ⟨t, ht⟩ := mkSpec_run hent u hpc hEntKnown (by simp [BC.mkEntSpec]) (by simp)
  have hmem : ∀ A, t.getMem A = u.getMem A := fun A => by rw [ht.mem]; rfl
  have h10u : u.getReg .x10 = BitVec.ofNat 64 (lfBase lay.val) :=
    hkU (.x10, BitVec.ofNat 64 (lfBase lay.val)) (by simp [lfK, postLf, lfBase])
  have h11u : u.getReg .x11 = BitVec.ofNat 64 (lfBytes lay.val) :=
    hkU (.x11, BitVec.ofNat 64 (if lay.val = 0 then 832 else 704)) (by simp [lfK, postLf])
  have h10 : t.getReg .x10 = u.getReg .x10 := ht.keep .x10 (by simp [mkEntKeep])
  have h11 : t.getReg .x11 = u.getReg .x11 := ht.keep .x11 (by simp [mkEntKeep])
  have hkt : KnownOK (mkEntPost lay.val 0 (mkSh lay.val 0 (route index lay).1)) t := ht.known
  have hb0 : mkSh lay.val 0 (route index lay).1 % 2 = (route index lay).1 / 2 ^ 0 % 2 := by
    have := mkSh_bit lay.val 0 (route index lay).1 0 (by unfold mkBits; split <;> [decide; (interval_cases lay.val <;> decide +kernel)])
    simpa [mkLo] using this
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (mkCur lay.val (route index lay).1 0 ((route index lay).1 / 2 ^ 0 % 2)) := by
    have hc0 := mkCur_sh lay.val (route index lay).1 0 ((route index lay).1 / 2 ^ 0 % 2) hlay hleaf
      (by interval_cases lay.val <;> decide +kernel)
    rw [show mkCi lay.val 0 = 0 by simp [mkCi]] at hc0
    rw [hkt (.x12, BitVec.ofNat 64 (mkCur lay.val (mkLeafOf lay.val 0 (mkSh lay.val 0 (route index lay).1)) (mkLo lay.val 0)
      (mkSh lay.val 0 (route index lay).1 % 2)))
      (by simp [mkEntPost]), hb0, show mkLo lay.val 0 = 0 by simp [mkLo], hc0]
  obtain ⟨hB8, hBlo, hBhi, hBase, hBtop⟩ := mkBo_facts lay.val (route index lay).1 0 hlay hleaf hhL
  have hb := mkBit_lt (route index lay).1 0
  obtain ⟨hcw, hc8, hc32⟩ := mkCur_bounds lay.val (route index lay).1 0 _ hlay hleaf hhL hb
  have hd : mkCur lay.val (route index lay).1 0 ((route index lay).1 / 2 ^ 0 % 2) + 32 < 2 ^ 64 := by omega
  have hin : hashInput t = toQ (pad64 (lfIn w lay (route index lay).2 (route index lay).1 ends)) := by
    rw [mkHashInput_congr h10 h11 hmem]; exact hu.hashInput.1
  have hv : hashArgumentsValid t = true := by
    refine hashArgs_of t (lfBase lay.val) (lfBytes lay.val) _ (h10.trans h10u) (h11.trans h11u) h12
      (by fin_cases lay <;> decide +kernel) (by fin_cases lay <;> decide +kernel) (by fin_cases lay <;> decide +kernel)
      hc8 (by omega)
  have hG : Glob (gkL lay.val) w pk t := ht.glob _ _ _ hu.glob (RelOK.nil u)
  have H : ∀ a : BitVec 256, GoodQP P (writeHash t a) (N + mkFuelR lay.val 0 (mkStop lay.val))
      (C + mkCycR lay.val 0 (mkStop lay.val)) Q (A + mkCycR lay.val 0 (mkStop lay.val))
      (ccM (merklePrefix w index lay (Verify.vHalf (ClaudeWCT.WCT9.lowerHigh lay.val (route index lay).1) a)) K) := by
    intro a
    rw [mkHi_leaf]
    have hA : MAfter w pk lay.val (route index lay).1 u 0 (Verify.vHalf (mkHB lay.val (route index lay).1 0) a)
        (writeHash t a) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h, ?_⟩
      · rw [writeHash_pc, ht.pc rfl, pcOf_add4]
        simp only [BC.mkEntSpec, mkEc, show mkCi lay.val 0 = 0 by simp [mkCi], show mkLo lay.val 0 = 0 by simp [mkLo]]
        rfl
      · exact Glob_writeHash hG a _ h12 (safeDest_hi _ hcw hc8 (by omega))
      · intro p hp
        rw [writeHash_getReg]
        have hp' : p ∈ mkK lay.val := by simpa [mkLvlK] using hp
        rcases mkK_cases _ p hp' with hp'' | hp''
        · exact hkt p (List.mem_append_left _ hp'')
        ·
          rw [ht.keep p.1 (by rw [hp'']; simp [mkEntKeep, mkKeep])]
          exact hkU p (lfK_mkK _ p hp')
      · intro r hr; rw [writeHash_getReg]; exact ht.keep r (mkKeep_sub _ r hr)
      · exact mk_node_at lay.val (route index lay).1 0 hlay hleaf hhL t a h12
      · have hO : Orig w (fun o => 7664 ≤ o ∧
            o < ClaudeWCT.W9.T3M.layerBase lay + 16 * ClaudeWCT.W9.T3M.pathSlots lay) t :=
          hu.orig.frame (fun j _ _ => hmem _)
        have hw2 := Orig_writeHash hO a _ h12 hd
        refine hw2.mono8 (fun o h8 ho => ?_)
        obtain ⟨⟨h1, h2⟩, h3⟩ := mkP_leaf lay.val (route index lay).1 hlay hleaf o h8 ho
        exact ⟨⟨h1, by rw [← mkBase_eq, ← mkPS_eq]; exact h2⟩, by unfold WIT; omega⟩
      · rw [writeHash_getReg]; exact h12
      · intro h0
        have h0' : lay ≠ 0 := by intro he; apply h0; rw [he]; rfl
        have hbuf := (hu.bufferOrig h0').frame (fun j _ _ => hmem _)
        exact mk_buffer_writeHash lay.val hlay hbuf a _ h12
          (by unfold WIT; omega)
    rw [merklePrefix, List.range_eq_range']
    have hs7 : lay.val = 0 → u.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) := by
      intro h
      rw [hu.s7 (Fin.ext h), h]
    have hx6 : lay.val = 0 → u.getReg .x6 = 520192 := by
      intro h
      exact hkU (.x6, 520192) (by simp [lfK, postLf, leafK, h])
    exact merkle_rest w pk index lay u hidx hs7 hx6 hu.t5 K N C A Q hK (mkStop lay.val) 0 _ _ (by omega) hhL hA
  have h5 : t.getReg .x5 = 0 := hkt (.x5, 0) (by simp [mkEntPost, mkKc, baseK])
  have hg := GoodQP.vHash_bind _ (f := merklePrefix w index lay) (K := K) (ht.ecall rfl) h5 hv hin H
  rw [hu.hashInput.2] at hg
  rw [show ClaudeWCT.WCT9.leafHashW lay (route index lay).2 (route index lay).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
      (ClaudeWCT.W9.T3M.wleafHigh w lay) ends = Verify.vHash (ClaudeWCT.WCT9.lowerHigh lay.val (route index lay).1)
        (lfIn w lay (route index lay).2 (route index lay).1 ends) from (LCtx.vHash_eq_halfHash _ _).symm]
  have hst := ht.steps
  simp only [BC.mkEntSpec, Nat.reduceEqDiff, and_false, if_false] at hst
  exact GoodQP.stepsQ hst hg (by unfold mkFuel; omega) (by unfold mkCyc; omega) (fun q => ⟨q, by unfold mkCyc; omega⟩)
open ClaudeWCT.WCT9 (LayerMsg)
def mkMessage (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (v : Digest) : LayerMsg :=
  if lay.val = 0 then .forest v else
  let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 (height lay - 1)
  if (route index lay).1 / 2 ^ (height lay - 1) % 2 = 0 then .pair v other else .pair other v
def merkleMsg (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (v : Digest) : T3.M LayerMsg :=
  merklePrefix w index lay v >>= fun root => pure (mkMessage w index lay root)
theorem layerPairP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0) (digits : List Nat) :
    (ClaudeWCT.W9.T3M.layerPairP w index lay digits >>= fun p => pure (LayerMsg.pair p.1 p.2)) =
      (chainsP w lay (route index lay).2 (route index lay).1 digits >>= fun ends =>
        ClaudeWCT.WCT9.leafHashW lay (route index lay).2 (route index lay).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
          (ClaudeWCT.W9.T3M.wleafHigh w lay) ends >>= merkleMsg w index lay) := by
  have hleaf := leaf_lt index lay
  have hfun : (fun x (j : Fin (height lay - 1)) => mkStep w index lay x j.val) = (fun value j =>
      let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 j.val
      let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
      ClaudeWCT.WCT9.lowerNodeHashP lay.val (route index lay).2
        (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1)) pair.1
        (ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j.val)
        (ClaudeWCT.W9.T3M.wmerklePad w lay (route index lay).1 j.val) pair.2) := by
    funext x j
    have hw : mkHw w lay (route index lay).1 j.val = ClaudeWCT.W9.T3M.wmerkleHigh w lay (route index lay).1 j.val := by
      unfold mkHw ClaudeWCT.W9.T3M.wmerkleHigh; rw [mkBo_eq lay _ j.val hleaf]
    unfold mkStep mkIn mkTw
    rw [LCtx.vHash_eq_halfHash, hw]
    dsimp only
    split_ifs <;> rfl
  unfold ClaudeWCT.W9.T3M.layerPairP chainsP merkleMsg merklePrefix
  rw [mkStop, if_neg h0, hL_eq, ← mkFinRange_map_val]
  simp only [List.foldlM_map]
  rw [hfun]
  unfold mkMessage
  generalize route index lay = pair
  rcases pair with ⟨leaf, tree⟩
  simp only [bind_assoc, pure_bind]
  congr 1
  funext ends
  congr 1
  funext v
  congr 1
  funext root
  simp only [h0, if_false]
  split_ifs <;> rfl
/-- C4: the top fold of the spec (`lowerNodeHashP 0` with the witness high pad) is the image's `mkStep`. -/
theorem merkleP_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (value : Digest) :
    merkleP w index 0 value = (List.range (height 0)).foldlM (mkStep w index 0) value := by
  have hleaf := leaf_lt index 0
  rw [← mkFinRange_map_val, List.foldlM_map]
  unfold merkleP
  congr 1
  funext x j
  have hw : mkHw w 0 (route index 0).1 j.val = ClaudeWCT.W9.T3M.wmerkleHigh w 0 (route index 0).1 j.val := by
    unfold mkHw ClaudeWCT.W9.T3M.wmerkleHigh; rw [mkBo_eq 0 _ j.val hleaf]
  unfold mkStep mkIn mkTw
  rw [LCtx.vHash_eq_halfHash, hw]
  dsimp only
  split_ifs <;> rfl
theorem merkleMsg_top (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) :
    merkleMsg w index 0 v = merkleP w index 0 v >>= fun root => pure (LayerMsg.forest root) := by
  rw [merkleP_eq]
  rfl
theorem layerLoop_succ (w : ClaudeWCT.W9.T3M.WBytes) (index n : Nat) (hn : n < 4) (hn0 : n ≠ 0) (msg : LayerMsg) :
    BC.layerLoop w index (n + 1) msg =
      layerHead w index (Fin.ofNat 4 n) msg (fun ends =>
        ClaudeWCT.WCT9.leafHashW (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
          (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w (Fin.ofNat 4 n)) ends >>=
          fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n) := by
  change ClaudeWCT.W9.T3M.layersCanonicalBC w index (n + 1) msg = _
  rw [ClaudeWCT.W9.T3M.layersCanonicalBC, layerHead]
  dsimp only
  simp only [hn0, ↓reduceIte]
  have hlay0 : (Fin.ofNat 4 n : Layer) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_ofNat, Nat.mod_eq_of_lt hn] at this
    exact hn0 this
  rw [ClaudeWCT.WCT9.verificationHash_lower _ hlay0]
  split_ifs with hc
  · rfl
  · congr 1
    funext answer
    simp only [canonicalDecode]
    cases ClaudeWCT.WCT9.CanonicalPolicy.decode (Fin.ofNat 4 n) answer with
    | none => rfl
    | some digits =>
      unfold guardedChainsP ClaudeWCT.W9.T3M.layerGuardedPairP ClaudeWCT.WCT9.lowerGuardedRun
      by_cases hgood : ClaudeWCT.WCT9.lowerRankGood answer
      · simp only [if_pos hgood, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        have hv : (Fin.ofNat 4 n : Layer).val ≠ 0 := by simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hn] using hn0
        have h := congrArg (fun p => p >>= BC.layerLoop w index n) (layerPairP_eq w index (Fin.ofNat 4 n) hv digits)
        cases n with
        | zero => contradiction
        | succ m => simpa only [bind_assoc, pure_bind, BC.layerLoop] using h
      · simp only [if_neg hgood, bind_assoc, pure_bind]
theorem layerLoop_one (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (msg : LayerMsg) :
    BC.layerLoop w index 1 msg =
      if (ClaudeWCT.W9.T3M.wbcCtr w index 0).toNat ≥ ClaudeWCT.WCT9.verifyWindow then pure none else
      ClaudeWCT.WCT9.verificationHash 0 (ClaudeWCT.W9.T3M.wtopHigh w)
        (ClaudeWCT.W9.T3M.layerEncodingInputP 0 (route index 0).2 (route index 0).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w index 0) (ClaudeWCT.W9.T3M.wbcPad w index 0) (ClaudeWCT.W9.T3M.wbcRight w)
        (ClaudeWCT.W9.T3M.wbcHigh w index 0)) >>=
        ClaudeWCT.W9.T3M.topLayerP w index := by
  change ClaudeWCT.W9.T3M.layersCanonicalBC w index 1 msg = _
  rw [ClaudeWCT.W9.T3M.layersCanonicalBC]
  rfl
set_option maxRecDepth 10000
theorem mAfter_pair (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) :
    let other := ClaudeWCT.W9.T3M.wpath w lay (route index lay).1 k
    let pair := if (route index lay).1 / 2 ^ k % 2 = 0 then (v, other) else (other, v)
    DigAt s (mkBlk lay.val (route index lay).1 k) pair.1 ∧ DigAt s (mkBlk lay.val (route index lay).1 k + 48) pair.2 := by
  dsimp only
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay.val (route index lay).1 k lay.isLt hleaf hk
  obtain ⟨-, -, rs0, rs1, -⟩ := mkP_rd lay.val (route index lay).1 k lay.isLt hleaf hk
  have hb := mkBit_lt (route index lay).1 k
  have hO := hs.orig
  have hnode := hs.node
  rw [wpath_eq w lay _ _ hleaf]
  rcases (show (route index lay).1 / 2 ^ k % 2 = 0 ∨ (route index lay).1 / 2 ^ k % 2 = 1 by omega) with hb | hb
  · rw [hb] at hnode hO rs0 rs1
    simp only [hb, if_true, sibOff, show (0 : Nat) ≠ 1 by decide +kernel, if_false]
    have hsib := hO.dig (mkBo lay.val (route index lay).1 k + 48) (by omega) (by unfold WX; omega)
      (by simpa using rs0) (by simpa using rs1)
    exact ⟨by simpa [mkVal] using hnode, by simpa [DigAt, dlo, dhi, WIT, mkBlk, Nat.add_assoc] using hsib⟩
  · rw [hb] at hnode hO rs0 rs1
    simp only [hb, show (1 : Nat) ≠ 0 by decide +kernel, if_false, sibOff, if_true, Nat.add_zero]
    have hsib := hO.dig (mkBo lay.val (route index lay).1 k) (by omega) (by unfold WX; omega)
      (by simpa using rs0) (by simpa using rs1)
    exact ⟨by simpa [DigAt, dlo, dhi, WIT, mkBlk] using hsib, by simpa [mkVal] using hnode⟩
theorem mAfter_pad (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (u : MachineState)
    (k : Nat) (hk : k < hL lay.val) (v : Digest) (s : MachineState)
    (hs : MAfter w pk lay.val (route index lay).1 u k v s) (j : Nat) (hj : (lay.val ≠ 0 ∧ j = 3) ∨ j = 4 ∨ j = 5) :
    s.getMem (BitVec.ofNat 64 (mkBlk lay.val (route index lay).1 k + 8 * j)) =
      wword w ((mkBlk lay.val (route index lay).1 k - WIT) / 8 + j) := by
  have hleaf : (route index lay).1 < 2 ^ hL lay.val := leaf_lt index lay
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay.val (route index lay).1 k lay.isLt hleaf hk
  obtain ⟨rp0, rp1, -, -, rhi⟩ := mkP_rd lay.val (route index lay).1 k lay.isLt hleaf hk
  have hm : 8 * (mkBo lay.val (route index lay).1 k / 8 + j) = mkBo lay.val (route index lay).1 k + 8 * j := by omega
  have h := hs.orig (mkBo lay.val (route index lay).1 k / 8 + j) (by unfold WX; omega) (by
    rw [hm]
    rcases hj with ⟨h0, rfl⟩ | rfl | rfl
    · simpa using rhi
    · simpa using rp0
    · simpa using rp1)
  simpa only [mkBlk, WIT, Nat.add_sub_cancel_left, hm, Nat.add_assoc] using h
theorem rowA_mk (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0) :
    rowA (lay.val - 1) (BC.cpIdx index (lay.val - 1)) = mkBlk lay.val (route index lay).1 (mkStop lay.val) := by
  have hcp : BC.cpIdx index (lay.val - 1) = (route index lay).1 := by
    rw [route_fst]; unfold BC.cpIdx; rw [if_neg (by have := lay.isLt; omega), show lay.val - 1 + 1 = lay.val by omega]
    rfl
  rw [hcp]; unfold rowA mkBlk
  rw [mkBo_low _ _ _ h0, show lay.val - 1 + 1 = lay.val by omega, mkStop, if_neg h0]
  omega
theorem mkStop_msg (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (h0 : lay.val ≠ 0)
    (u : MachineState) (v : Digest) (s : MachineState)
    (hs : MkStop w pk lay.val (route index lay).1 u v s) :
    BC.MsgAt w index (lay.val - 1) (mkMessage w index lay v) s := by
  have hS : mkStop lay.val = height lay - 1 := by rw [mkStop, if_neg h0, hL_eq]
  have hk : mkStop lay.val < hL lay.val := by fin_cases lay <;> first | contradiction | decide
  have ha : MAfter w pk lay.val (route index lay).1 u (mkStop lay.val) v s := by
    simpa [MkStop, h0] using hs
  have hp := mAfter_pair w pk index lay u _ hk v s ha
  have hpad := mAfter_pad w pk index lay u _ hk v s ha
  rw [← rowA_mk index lay h0] at hp hpad
  rw [hS] at hp
  have hlt : lay.val - 1 < 3 := by omega
  unfold mkMessage
  rw [if_neg h0]
  have h3 : lay.val - 1 ≠ 3 := by omega
  have hpad' : ∀ j, j = 3 ∨ j = 4 ∨ j = 5 → s.getMem (BitVec.ofNat 64 (rowA (lay.val - 1) (BC.cpIdx index (lay.val - 1)) + 8 * j)) =
      wword w ((rowA (lay.val - 1) (BC.cpIdx index (lay.val - 1)) - WIT) / 8 + j) := fun j hj =>
    hpad j (by rcases hj with h | h | h
               · exact Or.inl ⟨h0, h⟩
               · exact Or.inr (Or.inl h)
               · exact Or.inr (Or.inr h))
  split_ifs with hb
  · simp only [hb, if_true] at hp
    simp only [BC.MsgAt, if_neg h3]
    exact ⟨hlt, hp.1, hp.2, hpad'⟩
  · simp only [hb, if_false] at hp
    simp only [BC.MsgAt, if_neg h3]
    exact ⟨hlt, hp.1, hp.2, hpad'⟩
theorem mkStop_known_next (n : Nat) (hn : n < 4) (hn0 : n ≠ 0) (u t : MachineState)
    (hu : KnownOK (lfK n) u) (ht : KnownOK (mkLvlK n (mkStop n)) t)
    (keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r) : KnownOK (BC.preK (n - 1)) t := by
  intro p hp
  interval_cases n
  · contradiction
  all_goals
    simp only [BC.preK, preK, baseK] at hp
    dsimp at hp
    simp only [List.mem_append, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨hp, hf⟩ | hp
    all_goals
      repeat' first | subst p | rcases hp with hp | hp
      all_goals first
      | exact ht _ (by decide +kernel)
      | (rw [keep _ (by decide +kernel)]; exact hu _ (by decide +kernel))
      | contradiction
theorem mkStop_pc (n leaf : Nat) (hn : n < 4) (h0 : n ≠ 0) (hleaf : leaf < 2 ^ hL n) :
    mkEc n leaf (mkStop n) + 1 = trPc (n - 1) leaf := by
  have hbits : mkBits n 0 = hL n := by simp [mkBits, h0]
  have hc := BC.mkBlockCheck_at n 0 leaf hn (by simp [mkNch, h0]) (by rwa [hbits])
  simp only [BC.mkBlockCheck, Bool.and_eq_true] at hc
  have hr : BC.childReturn n leaf = trPc (n - 1) leaf := by simpa [h0] using hc.2
  rw [← hr]
  simp only [mkEc, mkCi, h0, false_and, if_false, mkSh, mkLo, Nat.pow_zero, Nat.div_one,
    hbits, Nat.mod_eq_of_lt hleaf, mkStop, BC.childReturn, Nat.sub_zero]
theorem mkStop_next_lower (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (h0 : lay.val ≠ 0) (ends : List Digest) (u : MachineState)
    (hu : LeafOut w pk index lay ends u) (v : Digest) (t : MachineState)
    (ht : MkStop w pk lay.val (route index lay).1 u v t) :
    LayerIn w pk index (lay.val - 1) (mkMessage w index lay v) t := by
  have ha : MAfter w pk lay.val (route index lay).1 u (mkStop lay.val) v t := by
    simpa [MkStop, h0] using ht
  have hleaf := leaf_lt index lay
  have hL0 : lay ≠ 0 := by intro h; apply h0; rw [h]; rfl
  have hk0 : mkStop lay.val ≠ 0 := by fin_cases lay <;> first | contradiction | decide
  have hcp : BC.cpIdx index (lay.val - 1) = (route index lay).1 := by
    rw [route_fst]; unfold BC.cpIdx; rw [if_neg (by have := lay.isLt; omega), show lay.val - 1 + 1 = lay.val by omega]
    rfl
  have he : BC.below (lay.val - 1) = below (lay.val - 1) := by
    fin_cases lay <;> rfl
  refine ⟨by omega, hidx, ?_, ⟨mkStop_known_next _ lay.isLt h0 u t hu.glob.1 ha.known ha.keep, ha.glob.2⟩, ?_, ?_,
    mkStop_msg w pk index lay h0 u v t ht, ?_, fun h => absurd h (by have := lay.isLt; omega), ?_, ha.bufferOrig h0,
    fun h => absurd h (by have := lay.isLt; omega), fun h => absurd h (by have := lay.isLt; omega)⟩
  · rw [ha.pc, mkStop_pc _ _ lay.isLt h0 hleaf, hcp]
    simp only [setupPc, if_neg (show lay.val - 1 ≠ 3 by have := lay.isLt; omega)]
  · rw [show rReg (lay.val - 1) = .x31 by simp [rReg]; omega,
      ha.keep .x31 (by simp [mkKeep]), hu.t5 h0, tree_next index lay hL0, he]
  · intro _
    have htr := tree_lt index lay hidx
    rw [ha.x28 hk0 h0, hu.t5 h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), tree_next index lay hL0, he]
  · have hle : BC.layerEnd (lay.val - 1) = mkBase lay.val := by
      fin_cases lay <;> first | contradiction | rfl
    refine ha.orig.mono (fun o ho => ?_)
    rw [mkP_low _ _ _ _ _ h0]
    exact Or.inl ⟨ho.1, by rw [← hle]; exact ho.2⟩
  · intro _
    refine ⟨_, ha.dstReg, ?_⟩
    have hb := mkBit_lt (route index lay).1 (mkStop lay.val)
    have hk : mkStop lay.val < hL lay.val := by fin_cases lay <;> first | contradiction | decide
    have hle : BC.layerEnd (lay.val - 1) = mkBase lay.val := by
      fin_cases lay <;> first | contradiction | rfl
    have hp1 := ((route_facts lay.val (route index lay).1 lay.isLt hleaf).1 (mkStop lay.val) hk).2 h0
    rw [rowA_mk index lay h0, mkCur_low _ _ _ _ h0, hle]
    unfold mkBlk WIT; rw [mkBo_low _ _ _ h0]
    omega
end SigGolfCandidate.T3M
end
end
-- ==== merged from T3M_Verify_Compose ====
section

set_option Elab.async false

section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit dataDigits maxDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem nctx_prefix_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (ds : List Nat)
    (m : Nat) (hm : m ≤ 51) (hds : ∀ j, j < m → ds.getD j 0 = (nctxOf w index v p).dig j) :
    (List.range' 0 m).foldlM (nctxOf w index v p).chainF [] =
      (List.range' 0 m).mapM (srcChain w index ds) := by
  unfold NCtx.chainF
  rw [foldlM_app_mapM]
  simp only [List.nil_append, id_map']
  apply mapM_congr'
  intro i hi
  have hi' := List.mem_range'_1.mp hi
  exact nctx_chain_eq w index v p ds i (by omega) (fun j hj => hds j (by omega))
theorem chainsP_top_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ds : List Nat) :
    chainsP w 0 (route index 0).2 (route index 0).1 ds =
      (List.range' 0 51).mapM (srcChain w index ds) := by
  unfold chainsP
  rw [← TopSource.take_mapM (srcChain w index ds) 51 (le_refl _)]
  rw [show (List.finRange (T3.chainCount 0)).take 51 = List.finRange (T3.chainCount 0) by
    rw [List.take_of_length_le]; simp [TopSource.chainCount0]]
  rfl
theorem nctx_fit6 (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).Fit6 v := fun i hi => by
  rw [nctxOf_dig]; simp [topDig, hi]
/-- Campaign T51: a valid g0 field takes the head's dispatch to group 0's cell. -/
theorem nctx_group0 (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hv0 : Nonbinary.NCtx.gValid v 0) :
    (nctxOf w index v p).GroupIn s 0 [] s :=
  ⟨⟨fun _ _ => rfl, Frame.refl s _, by simp⟩, rfl,
    ((nctxOf w index v p).g0_group (nctx_fit6 w index v p) s he.pc).1 hv0⟩
/-- Campaign T51: an invalid g0 field faults at the head's dispatch. -/
theorem nctx_group0_bad (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (u s : MachineState)
    (he : TopEntry u v p s) (hv0 : ¬ Nonbinary.NCtx.gValid v 0) : fetch vimage s = none :=
  ((nctxOf w index v p).g0_group (nctx_fit6 w index v p) s he.pc).2 hv0
/-- Campaign T51: chain 50's digit is the checksum whenever it is in range. -/
theorem nctx_ck (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    (nctxOf w index v p).CkOk := by
  intro ds hds h1 h2
  rw [nctx_dataSum] at hds
  have ht : T3.target 0 = 152 := rfl
  rw [nctxOf_dig]
  unfold topDig
  rw [if_neg (by omega), if_pos rfl, ht, hds]
  unfold Nonbinary.topT at h1 h2 ⊢
  omega
theorem top_chain_frame (c : NCtx) (hc : c.S3 = 14128) {s t : MachineState}
    (hf : Frame s t (c.Wr 51)) : Frame s t topChainWrites := by
  apply hf.mono
  intro A _ hA
  unfold NCtx.Wr NCtx.bufferEnd Nonbinary.slot at hA
  rw [hc] at hA
  unfold topChainWrites
  split_ifs at hA <;> omega
end SigGolfCandidate.T3M
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c) ∧ KnownOK (cmpK c) t ∧ DigAt t (cmpDst c) root
  pk : PkOK pk t
theorem cmpBr1_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c)) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
theorem cmpBr2_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]
set_option maxRecDepth 100000
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel
theorem cmpCheck_at (c : Nat) (hc : c < 64) : cmpCheck c = true :=
  List.all_eq_true.mp cmpCheck_all c (List.mem_range.mpr hc)
theorem cmp_good {P : Hash → Prop} (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQP P t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc, hknown, hroot⟩ := h.copy
  have hck := cmpCheck_at c hc
  simp only [cmpCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 (cmpDst c)) = root.extractLsb' 0 64 := hroot.1
  have hr8 : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = root.extractLsb' 64 64 := hroot.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds c t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := spec_run hA t hpc hknown (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta c) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := GoodQP.halt (P := P) (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQP.stepsQ hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := spec_run hR1 t hpc hknown (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact GoodQP.stepsQ hu.steps (GoodQP.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route)
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height pad64 shortHash leafHash)
def kFin (pk : Digest) : Option Digest → OracleComp HashSpec Obs := fun x =>
  ccM (match x with
    | some r => pure (r == pk)
    | _ => pure false) Kb
theorem kFin_none (pk : Digest) : kFin pk none = pure (false, 0) := by simp [kFin, Kb]
theorem kFin_some (pk r : Digest) : kFin pk (some r) = pure (r == pk, 0) := by simp [kFin, Kb]
open ClaudeWCT.WCT9 (LayerMsg)
def RestIn (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index n : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  if n = 0 then match msg with
    | .forest root => CmpIn pk root s
    | .pair _ _ => False
  else LayerIn w pk index (n - 1) msg s
theorem mkEnd_top (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (u : MachineState) (root : Digest)
    (t : MachineState) (ht : MkEnd w pk 0 (route index 0).1 u root t) : CmpIn pk root t := by
  have hl4 : (route index 0).1 < 4096 := by simpa [hL] using leaf_lt index 0
  have hpc : t.pc = pcOf (cmpPc (mkSh 0 1 (route index 0).1)) := by
    rw [ht.pc]
    congr 1
    simp [mkFin, cmpPc, show mkNch 0 - 1 = 1 from rfl, show mkBits 0 1 = 6 from rfl,
      show mkOff 0 1 6 = 27 from rfl, BC.mkShp, mkShp]
    omega
  refine ⟨⟨mkSh 0 1 (route index 0).1, mkSh_lt _ _ _, ?_, ?_, ?_⟩, ht.glob.2.2.1⟩
  · exact hpc
  · intro p hp
    simp only [cmpK, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ht.glob.1 p hp
    · rw [ht.dstReg, mkDst_cmp _ hl4]
  · rw [mkDst_cmp _ hl4]; exact ht.root
theorem mkStop_next (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31)
    (lay : Layer) (ends : List Digest) (u : MachineState) (hu : LeafOut w pk index lay ends u)
    (v : Digest) (t : MachineState) (ht : MkStop w pk lay.val (route index lay).1 u v t) :
    RestIn w pk index lay.val (mkMessage w index lay v) t := by
  by_cases h0 : lay.val = 0
  · have hz : lay = 0 := Fin.ext h0
    subst lay
    exact mkEnd_top w pk index u v t ht
  · simpa [RestIn, h0] using mkStop_next_lower w pk index hidx lay h0 ends u hu v t ht
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput route coreDigit dataDigits)
open Nonbinary (NCtx)
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem chainsCost_mono (c : NCtx) (m : Nat) (hm : m ≤ 51) : c.chainsCost 0 m ≤ c.chainsCost 0 51 := by
  have := Nonbinary.NCtx.chainsCost_add' c 0 m (51-m)
  rw [show m+(51-m)=51 by omega] at this
  omega
/-- Path-aware top accounting contract: the selector cost plus the verifier-side top path bonus is at most the
worst-case selector cost `selMax = 6`. d6b: hint clear (`verificationLow 0 high _ = !high`) costs 4 and earns the
top bonus 2; hint set costs 6 (HIGH, or LOW forced) and earns nothing. -/
theorem top_sel_bonus_le (high : Bool) (a : BitVec 256) :
    Verify.Nonbinary.selCost high a +
      ClaudeWCT.WCT9.CanonicalPolicy.pathBonus 0 (ClaudeWCT.WCT9.verificationLow 0 high a) ≤ 6 := by
  unfold Verify.Nonbinary.selCost
  cases high <;> simp [ClaudeWCT.WCT9.CanonicalPolicy.pathBonus, ClaudeWCT.WCT9.verificationLow] <;>
    split_ifs <;> omega
/-- Campaign T51: the verifier's group check is the spec's `topGroupValid`. -/
theorem topGroupValid_iff (v : Digest) (q : Nat) :
    ClaudeWCT.WCT9.topGroupValid v q = true ↔ Nonbinary.NCtx.gValid v q := by
  unfold ClaudeWCT.WCT9.topGroupValid Nonbinary.NCtx.gValid
  split_ifs <;> simp
/-- Campaign T51: the first invalid group. -/
theorem first_invalid (V : Digest) (h : ¬ ∀ q, q < 17 → Nonbinary.NCtx.gValid V q) :
    ∃ j, j < 17 ∧ (∀ q, q < j → Nonbinary.NCtx.gValid V q) ∧ ¬ Nonbinary.NCtx.gValid V j := by
  classical
  have hex : ∃ j, j < 17 ∧ ¬ Nonbinary.NCtx.gValid V j := by
    by_contra hn; push Not at hn; exact h (fun q hq => hn q hq)
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun q hq => ?_, (Nat.find_spec hex).2⟩
  have := Nat.find_min hex hq
  push Not at this
  exact this (by have := (Nat.find_spec hex).1; omega)
theorem topGroupBad_before (v : Digest) (j : Nat) (hval : ∀ q, q < j → Nonbinary.NCtx.gValid v q) (i : Nat)
    (hi : i < 3 * j) (hi50 : i < 50) : ClaudeWCT.WCT9.topGroupBad v i = false := by
  cases h : ClaudeWCT.WCT9.topGroupBad v i
  · rfl
  · rw [TopSource.topGroupBad_iff] at h
    rcases h with ⟨-, -, hg⟩ | ⟨h50, -⟩
    · have := (topGroupValid_iff v (i/3)).mpr (hval (i/3) (by omega))
      rw [hg] at this; cases this
    · omega
/-- Campaign T51: the first invalid group `j` (16 = the r7 pair at chain 48) stops the verifier after `3 j` chains. -/
theorem topRejectLength_group (v : Digest) (j : Nat) (hj : j < 17)
    (hval : ∀ q, q < j → Nonbinary.NCtx.gValid v q) (hbad : ¬ Nonbinary.NCtx.gValid v j) :
    ClaudeWCT.WCT9.topRejectLength v = 3 * j := by
  apply TopSource.topRejectLength_bad v (3*j) (by omega)
  · intro i hi
    exact topGroupBad_before v j hval i hi (by omega)
  · rw [TopSource.topGroupBad_iff]
    left
    refine ⟨by omega, by omega, ?_⟩
    rw [show 3 * j / 3 = j by omega]
    cases h : ClaudeWCT.WCT9.topGroupValid v j
    · rfl
    · exact absurd ((topGroupValid_iff v j).mp h) hbad
/-- Campaign T51: all 17 groups valid but the checksum out of range: the verifier runs the 50 data chains. -/
theorem topRejectLength_ck (v : Digest) (hval : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q)
    (hout : ¬ ((dataDigits 0 v).sum ≤ T3.target 0 ∧ T3.target 0 - (dataDigits 0 v).sum < 6)) :
    ClaudeWCT.WCT9.topRejectLength v = 50 := by
  apply TopSource.topRejectLength_bad v 50 (by omega)
  · intro i hi
    exact topGroupBad_before v 17 hval i (by omega) hi
  · rw [TopSource.topGroupBad_iff]
    right
    refine ⟨rfl, ?_⟩
    unfold ClaudeWCT.WCT9.topChecksumOk
    simp only [decide_eq_false_iff_not]
    exact hout
/-- Campaign T51: a decoded word's digits (data digits, then the checksum) are the chain context's digits. -/
theorem nctx_top_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat)
    (hs2 : T3.target 0 - (dataDigits 0 v).sum < 6) :
    ∀ j, j < 51 → (dataDigits 0 v ++ [T3.target 0 - (dataDigits 0 v).sum]).getD j 0 = (nctxOf w index v p).dig j := by
  intro j hj
  have hl := ClaudeWCT.WCT9.dataDigits_top_length v
  by_cases h50 : j < 50
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact h50)]
    exact nctx_data_digits w index v p j h50
  · have hj50 : j = 50 := by omega
    subst hj50
    rw [nctxOf_dig, List.getD_append_right _ _ _ _ (by rw [hl]), hl]
    unfold topDig
    rw [if_neg (by omega), if_pos rfl]
    simp only [Nat.sub_self, List.getD_cons_zero]
    omega
/-- Campaign T51: the verify data words (masks, gate) survive the top entry. -/
theorem topEntry_data (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s0 : MachineState) (a : BitVec 256) (hpre : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0) :
    DataOK s0 := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 15272 ≤ topRowA c ∧ topRowA c ≤ 15528 ∧ topRowA c % 8 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := hpre.dst (by decide +kernel)
  change (d + 16 = topRowA c ∧ WIT + BC.layerEnd 0 + 16 ≤ topRowA c) ∨ d = topRowA c + 48 at hd
  exact (Glob_writeHash hpre.glob a d h12
    (safeDest_hi d (by unfold WLO WIT; omega) (by omega) (by omega))).2.2.2.2.2.congr
    (fun A hlo hA => he.frame.get (by omega) (by unfold TAB at hlo; omega))
/-- Campaign T51: after the 51 top chains: the top leaf (7 cycles), the 12 folds and the root compare. -/
theorem top_leaf_tail (floors : T3.Layer → Nat) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat)
    (hc : c < nCopy 0) (hidx : index < 2 ^ 31) (t s0 : MachineState) (a : BitVec 256)
    (hpre : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c) s0)
    (Q : Prop) (hQ : Q) (ends : List Digest) (z : MachineState)
    (hz : (nctxOf w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a) (trPc 0 c)).TopOut s0 ends z) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) z 77 263 Q 263
      (ccM (ClaudeWCT.WCT9.leafHashW 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
        (ClaudeWCT.W9.T3M.wleafHigh w 0) ends >>= merkleP w index 0)
        (fun r => kFin pk (some r))) := by
  obtain ⟨hr, hfz, hlen, hend, hpc, -⟩ := hz
  have hregs : RegsExcept s0 z topChainRegs := by
    intro r hrn
    have h24 : r ≠ .x24 := by intro hh; subst hh; exact hrn (by decide +kernel)
    have h29 : r ≠ .x29 := by intro hh; subst hh; exact hrn (by decide +kernel)
    have h18 : r ≠ .x18 := by intro hh; subst hh; exact hrn (by decide +kernel)
    exact hr r (fun hh => hrn ((by decide +kernel : chainRegs ⊆ topChainRegs) hh)) h24 h29 h18
  have hframe : Frame s0 z topChainWrites := top_chain_frame _ rfl hfz
  have h15 : z.getReg .x9 = 0x7fc00#64 := by
    rw [hregs.get (by decide +kernel)]; exact he.table
  have hready := topLeafReady_of w pk index c hc t s0 z a ends hpre he hpc hregs hframe h15 hlen
    (fun j hj => by have h := hend j (by omega); exact h)
  obtain ⟨u, st, hu⟩ := leafT_step w pk index c hc hidx ends z hready
  have hm := merkle_good (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) w pk index 0 ends u hidx hu
    (fun r => kFin pk (some r)) 9 8 8 Q
    (fun root t ht => by
      rw [kFin_some]
      exact cmp_good pk root t (mkEnd_top w pk index u root t (by simpa [MkStop] using ht)) Q hQ)
  have hmP : merkleP w index 0 = merklePrefix w index 0 := by
    funext x; rw [merkleP_eq]; rfl
  rw [hmP]
  have := GoodQP.steps st hm
  refine this.mono ?_ ?_ (fun h => ⟨h, ?_⟩) <;> simp [mkFuel_vals, mkCyc_vals]
/-- Campaign T51 top layer after its encoding hash: selector + head (`selCost + 5`), the 16 groups, the r7 pair and
the checksum chain (`chainsCost 0 51 + 78`), leaf/folds/compare (263): accepted cost
`chainsCost 0 51 + 346 + selCost <= 1322 - floor` by the cost law (970 + penalty) and the policy's floor. -/
theorem top_after_hash (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0) (hidx : index < 2 ^ 31)
    (t : MachineState) (hpre : BC.EncPre w pk index 0 c t) (Q : Prop) (hQ : Q) (q : Query) (hq : EncQ 0 q)
    (a : BitVec 256) :
    GoodQP (fun hash => hash q = a ∧ HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w) hash) (writeHash t a) 2372 2693 Q
      (1322 - floors 0)
      (ccM (ClaudeWCT.W9.T3M.topLayerP w index (T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a)) (kFin pk)) := by
  have hfloor := hbound 0
  obtain ⟨n0, s0, st0, hn0, hn0e, he⟩ := topTransition w pk index c hc t hpre a
  set v := T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a with hvdef
  have hsel := top_sel_bonus_le (ClaudeWCT.W9.T3M.wtopHigh w) a
  set L := nctxOf w index v (trPc 0 c) with hLdef
  have hLok : L.ok := nctx_ok w index v c hidx
  have hkn : ∀ p ∈ L.known, s0.getReg p.1 = p.2 := nctx_known w pk index c t s0 a hpre he
  have hD := topEntry_data w pk index c hc t s0 a hpre he
  have hO := nctx_orig w index v (trPc 0 c) s0 (topEntry_orig w pk index c hc t s0 a hpre he)
    (topEntry_bufferOrig w pk index c hc t s0 a hpre he) hD
  have hds := nctx_digits w index v (trPc 0 c)
  have hf := nctx_fit6 w index v (trPc 0 c)
  have hEnc : Nonbinary.NCtx.Encoded0 v s0 := ⟨he.lo, he.hi, he.mask⟩
  have hmask : s0.getMem 0xffbdf0#64 = 65280#64 := hD.mask6
  have hck := nctx_ck w index v (trPc 0 c)
  have hcc : L.chainsCost 0 51 ≤ 2341 := L.chainsCost_any hds
  cases hdec : T3.decode 0 v with
  | some ds =>
    obtain ⟨-, hrv, ⟨hs1, hs2⟩, rfl⟩ := ClaudeWCT.WCT9.decode_top_some hdec
    have hval : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q := (Nonbinary.NCtx.topRanksValid_iff v).mp hrv
    have hin : Nonbinary.topT - 5 ≤ ((List.range 50).map L.dig).sum ∧
        ((List.range 50).map L.dig).sum ≤ Nonbinary.topT := by
      rw [hLdef, nctx_dataSum]
      have ht : T3.target 0 = 152 := rfl
      unfold Nonbinary.topT; omega
    have hdig := nctx_top_digits w index v (trPc 0 c) hs2
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode w index hdec, ccM_map, layerP_eq, ccM_bind, chainsP_top_eq,
      ← nctx_prefix_eq w index v (trPc 0 c) _ 51 (le_refl _) (fun j hj => hdig j hj)]
    have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hval 0 (by omega))
    have body : GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) (writeHash t a) 2372 2693 Q
        (L.chainsCost 0 51 + 346 + Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a)
        (ccM ((List.range' 0 51).foldlM L.chainF [])
          (fun ends => ccM (ClaudeWCT.WCT9.leafHashW 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
            (ClaudeWCT.W9.T3M.wleafHigh w 0) ends >>= merkleP w index 0)
            (fun r => kFin pk (some r)))) := by
      have H := L.top_full (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hck hkn hO hEnc hf hmask hval hin
        (fun ends => ccM (ClaudeWCT.WCT9.leafHashW 0 (route index 0).2 (route index 0).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
            (ClaudeWCT.W9.T3M.wleafHigh w 0) ends >>= merkleP w index 0)
          (fun r => kFin pk (some r))) 77 263 263 Q
        (fun ends z hz => top_leaf_tail floors w pk index c hc hidx t s0 a hpre he Q hQ ends z hz)
        s0 hg0
      have H2 := GoodQP.steps st0 H
      refine H2.mono ?_ ?_ (fun h => ⟨h, ?_⟩) <;> omega
    by_cases hcr : L.chainsCost 0 51 + Verify.Nonbinary.selCost (ClaudeWCT.W9.T3M.wtopHigh w) a ≤ 976 - floors 0
    · exact (body.mono (le_refl _) (le_refl _) (fun h => ⟨h, by omega⟩)).pre_mono (fun _ h => h.2)
    · refine GoodQP.of_false_pre body ?_
      rintro hash ⟨hea, hok⟩
      have h7 := hok 0 q hq (dataDigits 0 v ++ [T3.target 0 - (dataDigits 0 v).sum]) (by rw [hea]; exact hdec)
      simp only [ClaudeWCT.WCT9.CanonicalPolicy.pathReward, ClaudeWCT.WCT9.CanonicalPolicy.reward, hea] at h7
      rw [ClaudeWCT.WCT9.wordCredit_top hdec] at h7
      have hbalance := L.chainsCost_accepted hds v _ hdec (fun i hi => hdig i hi)
      exact hcr (by omega)
  | none =>
    refine GoodQP.pre_mono (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) ?_ (fun _ h => h.2)
    refine Nonbinary.NCtx.goodQ_vacuous (A := 0) ?_ Q (1322 - floors 0)
    rw [ClaudeWCT.W9.T3M.topLayerP_of_decode_none w index hdec, ccM_map]
    simp only [kFin_none]
    have hv' : v.toNat < 2 ^ T3.encodedBits 0 := by simpa [T3.encodedBits] using v.isLt
    by_cases hall : ∀ q, q < 17 → Nonbinary.NCtx.gValid v q
    · have hout : ¬ ((dataDigits 0 v).sum ≤ T3.target 0 ∧ T3.target 0 - (dataDigits 0 v).sum < 6) := by
        intro h
        rw [ClaudeWCT.WCT9.decode_top_of hv' ((Nonbinary.NCtx.topRanksValid_iff v).mpr hall) h.1 h.2] at hdec
        cases hdec
      rw [topRejectChains_eq w index v 50 (le_refl _) (topRejectLength_ck v hall hout),
        ← nctx_prefix_eq w index v (trPc 0 c) _ 50 (by omega)
          (fun j hj => nctx_data_digits w index v (trPc 0 c) j hj)]
      have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hall 0 (by omega))
      have hout' : ¬ (Nonbinary.topT - 5 ≤ ((List.range 50).map L.dig).sum ∧
          ((List.range 50).map L.dig).sum ≤ Nonbinary.topT) := by
        rw [hLdef, nctx_dataSum]
        have ht : T3.target 0 = 152 := rfl
        unfold Nonbinary.topT; omega
      have H := L.top_bad_ck (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hkn hO hEnc hf hmask hall
        hout' (fun _ => pure (false, 0)) (fun _ => rfl) False 0 s0 hg0
      have hm := chainsCost_mono L 50 (by omega)
      have hov := Nonbinary.NCtx.ov_le 16 (le_refl _)
      exact (GoodQP.steps st0 H).mono (by omega) (by omega) (fun h => h.elim)
    · obtain ⟨j, hj, hjmin, hjbad⟩ := first_invalid v hall
      by_cases hj0 : j = 0
      · subst hj0
        rw [topRejectChains_eq w index v 0 (by omega) (by rw [topRejectLength_group v 0 (by omega) hjmin hjbad])]
        simp only [List.range'_zero, List.mapM_nil, ccM_pure]
        have hf0 := nctx_group0_bad w index v (trPc 0 c) _ s0 he hjbad
        exact (GoodQP.steps st0 (Nonbinary.NCtx.goodQ_fault (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w))
          (Q := False) (A := 0) hf0)).mono (by omega) (by omega) (fun h => h.elim)
      · rw [topRejectChains_eq w index v (3 * j) (by omega) (topRejectLength_group v j hj hjmin hjbad),
          ← nctx_prefix_eq w index v (trPc 0 c) _ (3 * j) (by omega)
            (fun i hi => nctx_data_digits w index v (trPc 0 c) i (by omega))]
        have hg0 := nctx_group0 w index v (trPc 0 c) _ s0 he (hjmin 0 (by omega))
        have H := L.top_bad_group (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) hLok hds hkn hO hEnc hf hmask
          j (by omega) (by omega) hjmin hjbad (fun _ => pure (false, 0)) (fun _ => rfl) False 0 s0 hg0
        have hm := chainsCost_mono L (3 * j) (by omega)
        have hov := Nonbinary.NCtx.ov_le j (by omega)
        exact (GoodQP.steps st0 H).mono (by omega) (by omega) (fun h => h.elim)
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
variable {floors : SigGolfCandidate.T3.Layer → Nat}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route leafHash)
open ClaudeWCT.WCT9 (LayerMsg)
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
/-- Stage 2 (C2 + C3, as #866): top head 5 steps (row high-word pad), top leaf without the 16-byte pad stores and the
leaf tweak high-word store. Configuration (1)+(2): target 146 (accepted chains 936 -> 927) and the e7b
top-half selector (worst path 7 instead of 4, the honest LOW path's 3 cycles are credited by the top path bonus):
1292 -> 1286, fuel/cycles +3. d6b head (img-v4/v6): HIGH path 6 instead of 7, top bonus 2: 1286 -> 1285. -/
def topFuel : Nat := 5 + 1 + 2372
def topCyc : Nat := 5 + 8 + 2693
def topCycA (floors : T3.Layer → Nat) : Nat := 5 + 8 + (1322 - floors 0)
theorem top_layer_good (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q)
    (M : LayerMsg) (s : MachineState) (hs : LayerIn w pk index 0 M s) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) s topFuel topCyc Q (topCycA floors)
      (ccM (BC.layerLoop w index 1 M) (kFin pk)) := by
  rw [layerLoop_one]
  have hA := BC.encoding_setup w pk index 0 M s hs
  have hsA : stepsA (0 : Layer).val = 5 := rfl
  by_cases hctr : (ClaudeWCT.W9.T3M.wbcCtr w index 0).toNat ≥ ClaudeWCT.WCT9.verifyWindow
  · exact absurd hctr (ClaudeWCT.WCT9.ctr_not_ge_verifyWindow _)
  · rw [if_neg hctr]
    obtain ⟨t, hst, hf, h5, hv, hin, hpre⟩ := hA.2 (by omega)
    set c := BC.cpIdx index (0 : Layer).val with hcdef
    have hc : c < nCopy 0 := by
      have h := BC.nCopy_eq
      have : c < 128 := by
        show (if (0 : Nat) = 3 then 0 else index / 2 ^ below (0 + 1) % 2 ^ hL (0 + 1)) < 128
        rw [if_neg (by decide +kernel)]
        exact lt_of_lt_of_le (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel)
      omega
    rw [hsA] at hst
    have hblk := BC.encoding_blocks w index 0 (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcHigh w index 0)
    have hq := encQ_layer 0 (route index 0).2 (route index 0).1 M (ClaudeWCT.W9.T3M.wbcCtr w index 0)
      (ClaudeWCT.W9.T3M.wbcPad w index 0) (ClaudeWCT.W9.T3M.wbcRight w) (ClaudeWCT.W9.T3M.wbcHigh w index 0)
    have := GoodQP.verificationHash_bind_pre (lay := 0) (high := ClaudeWCT.W9.T3M.wtopHigh w)
      (f := ClaudeWCT.W9.T3M.topLayerP w index) hf h5 hv hin
      (fun a => by
        rw [show ClaudeWCT.WCT9.verificationAnswer 0 (ClaudeWCT.W9.T3M.wtopHigh w) a =
          T3.TopChoice.read (ClaudeWCT.W9.T3M.wtopHigh w) a from rfl]
        exact top_after_hash floors hbound w pk index c hc hidx t hpre Q hQ _ hq a)
    rw [hblk] at this
    exact (GoodQP.steps' hst this (by simp [topFuel]) (by simp [topCyc]) (by simp [topCycA]; omega))
def lCyc : Nat → Nat
  | 0 => 8
  | 1 => topCyc
  | n + 2 => layerCost (n + 1) 0 + mkCyc (n + 1) + lCyc (n + 1)
def lCycA (floors : T3.Layer → Nat) : Nat → Nat
  | 0 => 8
  | 1 => topCycA floors
  | n + 2 => layerCostA floors (n + 1) + mkCyc (n + 1) + lCycA floors (n + 1)
def lFuel : Nat → Nat
  | 0 => 9
  | 1 => topFuel
  | n + 2 => layerFuel (n + 1) + mkFuel (n + 1) + lFuel (n + 1)
theorem lCyc_4 : lCyc 4 = 6704 := by decide +kernel
/-- Stage 2: floor-free constant 5303 (stage 1: 5334; C2 −13, C3 −7). Configuration (1)+(2): 5297 (top −9 + 3); d6b 5296. -/
theorem lCycA_4 (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) :
    lCycA floors 4 = 5333 - ((List.finRange 4).map floors).sum := by
  have h0 := hbound 0
  have h1 := hbound 1
  have h2 := hbound 2
  have h3 := hbound 3
  change (1181 - floors 3) + 153 + ((1173 - floors 2) + 153 +
    ((1173 - floors 1) + 165 + (5 + 8 + (1322 - floors 0)))) =
      5333 - (floors 0 + (floors 1 + (floors 2 + (floors 3 + 0))))
  omega
theorem lFuel_4 : lFuel 4 = 7755 := by decide +kernel
theorem layers_good (floors : T3.Layer → Nat) (hbound : ∀ lay, floors lay ≤ 301) (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (hidx : index < 2 ^ 31) (Q : Prop) (hQ : Q) :
    ∀ n, n ≤ 4 → ∀ msg s, RestIn w pk index n msg s →
      GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) s (lFuel n) (lCyc n) Q (lCycA floors n)
        (ccM (BC.layerLoop w index n msg) (kFin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ msg s hs
    cases msg with
    | forest root =>
      simp only [BC.layerLoop, ccM_pure, kFin_some]
      exact cmp_good pk root s hs Q hQ
    | pair left right => exact False.elim hs
  | succ n ih =>
    intro hn msg s hs
    have hs' : LayerIn w pk index n msg s := by simpa [RestIn] using hs
    by_cases hn0 : n = 0
    · subst hn0
      exact top_layer_good floors hbound w pk index hidx Q hQ msg s hs'
    have hv : (Fin.ofNat 4 n : Layer).val = n := by simp [Fin.val_ofNat, Nat.mod_eq_of_lt (show n < 4 by omega)]
    have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := fun h => hn0 (by rw [← hv, h]; rfl)
    rw [layerLoop_succ w index n (by omega) hn0 msg]
    have hg := layer_good_low floors hbound (ClaudeWCT.W9.T3M.wtopHigh w) w pk index (Fin.ofNat 4 n) hlay msg s (by rwa [hv])
      (fun ends => ClaudeWCT.WCT9.leafHashW (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1
          (ClaudeWCT.W9.T3M.wtopLeafPad w) (ClaudeWCT.W9.T3M.wleafHigh w (Fin.ofNat 4 n)) ends >>=
        fun v => merkleMsg w index (Fin.ofNat 4 n) v >>= BC.layerLoop w index n)
      (kFin pk) (kFin_none pk) (lFuel n + mkFuel n) (lCyc n + mkCyc n) (lCycA floors n + mkCyc n) Q
      (fun ends u hu => by
        have hm := merkle_good (P := HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) w pk index (Fin.ofNat 4 n) ends u hidx hu
          (fun v => ccM (BC.layerLoop w index n (mkMessage w index (Fin.ofNat 4 n) v)) (kFin pk))
          (lFuel n) (lCyc n) (lCycA floors n) Q
          (fun v t ht => ih (by omega) _ t (by
            have h := mkStop_next w pk index hidx (Fin.ofNat 4 n) ends u hu v t ht
            rw [hv] at h
            exact h))
        simp only [ccM_bind, merkleMsg, ccM_pure, hv] at hm ⊢
        exact hm)
    rw [hv] at hg
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 + 1 = m + 2 from rfl]
    exact hg.mono (by simp only [lFuel]; omega) (by simp only [lCyc]; omega)
      (fun q => ⟨q, by simp only [lCycA]; omega⟩)
theorem after_good (floors : T3.Layer → Nat) (hcredit : CreditFloors floors) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (Q : Prop) (hQ : Q) (a : HashOutput)
    (top : Digest × Digest) (u : MachineState)
    (h : FtsOut ⟨pk, w, a⟩ top u) :
    GoodQP (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) u 8050 8050 Q 5264
      (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb) := by
  have hidx : ClaudeWCT.WCT9.digestIndex a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  obtain ⟨t, hst, hL3⟩ := layerIn_of_fts w pk _ top.1 top.2 u hidx h.glob h.idx h.pc h.left h.right h.wit h.base h.a1
    h.s10 h.heapOne h.heapTwo h.heapSeven h.heapThree h.heapFour h.heapFive h.coordStep h.topBase h.top h.top8 h.a2 h.d0
  have hg := layers_good floors hcredit.1 w pk _ hidx Q hQ 4 le_rfl (.pair top.1 top.2) t (by simpa [RestIn] using hL3)
  have e : ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb =
      ccM (BC.layerLoop w (ClaudeWCT.WCT9.digestIndex a) 4 (.pair top.1 top.2)) (kFin pk) := by
    unfold afterFts
    rw [ccM_bind]
    rfl
  rw [e]
  rw [lFuel_4, lCyc_4, lCycA_4 floors hcredit.1] at hg
  have htotal := hcredit.2
  exact GoodQP.stepsQ hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
theorem after_good_budget : AfterGoodBudget 5264 :=
  fun floors hcredit pk w Q hQ a top u h => after_good floors hcredit pk w Q hQ a top u h
end SigGolfCandidate.T3M
end
end
-- ==== merged from T3M_Verify_Init ====
section

set_option Elab.async false

set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
def leNat8 : List (BitVec 8) → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * leNat8 l
theorem shl_or (X y k : Nat) (hX : X < 2 ^ k) : X ||| y * 2 ^ k = X + 2 ^ k * y := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hX]; ring
theorem zext_shl_toNat (b : BitVec 8) (k : Nat) (hk : k ≤ 56) :
    ((b.zeroExtend 64 : Word) <<< (BitVec.ofNat 64 k)).toNat = b.toNat * 2 ^ k := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega)]
  apply Nat.mod_eq_of_lt
  calc b.toNat * 2 ^ k < 2 ^ 8 * 2 ^ k := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
    _ = 2 ^ (8 + k) := by rw [Nat.pow_add]
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide +kernel) (by omega)
theorem leNat8_lt : ∀ l : List (BitVec 8), leNat8 l < 256 ^ l.length
  | [] => by simp [leNat8]
  | b :: l => by
    have := leNat8_lt l
    have hb := b.isLt
    simp only [leNat8, List.length_cons, pow_succ]
    have : b.toNat < 256 := by simpa using hb
    nlinarith
theorem bytesToWordLE8_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]).toNat =
      leNat8 [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [bytesToWordLE, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    BitVec.toNat_or, leNat8]
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, show (16 : Word) = BitVec.ofNat 64 16 from rfl,
    show (24 : Word) = BitVec.ofNat 64 24 from rfl, show (32 : Word) = BitVec.ofNat 64 32 from rfl,
    show (40 : Word) = BitVec.ofNat 64 40 from rfl, show (48 : Word) = BitVec.ofNat 64 48 from rfl,
    show (56 : Word) = BitVec.ofNat 64 56 from rfl]
  rw [zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel),
    zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel),
    zext_shl_toNat _ _ (by decide +kernel)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := b4.isLt; have := b5.isLt; have := b6.isLt; have := b7.isLt
  generalize b0.toNat = x0 at *; generalize b1.toNat = x1 at *; generalize b2.toNat = x2 at *
  generalize b3.toNat = x3 at *; generalize b4.toNat = x4 at *; generalize b5.toNat = x5 at *
  generalize b6.toNat = x6 at *; generalize b7.toNat = x7 at *
  rw [Nat.mod_eq_of_lt (show x0 < 2 ^ 64 by omega), shl_or x0 x1 8 (by omega),
    shl_or _ x2 16 (by omega), shl_or _ x3 24 (by omega), shl_or _ x4 32 (by omega),
    shl_or _ x5 40 (by omega), shl_or _ x6 48 (by omega), shl_or _ x7 56 (by omega)]
  norm_num
  omega
theorem bytesToWordLE8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7] =
      BitVec.ofNat 64 (leNat8 [b0, b1, b2, b3, b4, b5, b6, b7]) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := leNat8_lt [b0, b1, b2, b3, b4, b5, b6, b7]
  simp only [List.length_cons, List.length_nil] at hlt
  rw [bytesToWordLE8_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num at hlt ⊢; exact hlt)]
theorem bytesToWordLE_len8 (l : List (BitVec 8)) (hl : l.length = 8) :
    bytesToWordLE l = BitVec.ofNat 64 (leNat8 l) := by
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact bytesToWordLE8 b0 b1 b2 b3 b4 b5 b6 b7
theorem length_bytes {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]
theorem leNat8_slice {n : Nat} (x : Bytes n) : ∀ k a, a + k ≤ n →
    leNat8 (((bytes x).drop a).take k) = x.toNat / 2 ^ (8 * a) % 2 ^ (8 * k) := by
  intro k
  induction k with
  | zero => intro a _; simp only [List.take_zero, leNat8, Nat.mul_zero, pow_zero, Nat.mod_one]
  | succ k ih =>
    intro a h
    have ha : a < (bytes x).length := by rw [length_bytes]; omega
    rw [List.drop_eq_getElem_cons ha, List.take_succ_cons, leNat8, ih (a + 1) (by omega)]
    have hb : ((bytes x)[a]'ha).toNat = x.toNat / 2 ^ (8 * a) % 2 ^ 8 := by
      simp only [bytes, List.getElem_map, List.getElem_range, BitVec.extractLsb'_toNat,
        Nat.shiftRight_eq_div_pow]
    rw [hb, show 8 * (a + 1) = 8 * a + 8 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show 8 * (k + 1) = 8 + 8 * k by ring, Nat.pow_add 2 8 (8 * k), Nat.mod_mul]
theorem bytes_word {n : Nat} (x : Bytes n) (j : Nat) (h : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  rw [bytesToWordLE_len8 _ (by simp [length_bytes]; omega), leNat8_slice x 8 (8 * j) h]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * j) = 64 * j by ring, show 8 * 8 = 64 by rfl, Nat.mod_mod]
theorem bytesToWordLE_len4 (l : List (BitVec 8)) (hl : l.length = 4) :
    bytesToWordLE l = BitVec.ofNat 64 (leNat8 l) := by
  match l, hl with
  | [b0, b1, b2, b3], _ =>
    have e : bytesToWordLE [b0, b1, b2, b3] = bytesToWordLE [b0, b1, b2, b3, 0, 0, 0, 0] := rfl
    rw [e, bytesToWordLE8]
    simp [leNat8]
/-- The last, half-filled word of a buffer whose length is 4 mod 8: the loader zero-pads it. -/
theorem bytes_word_tail {n : Nat} (x : Bytes n) (j : Nat) (h : 8 * j + 4 = n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  have hd : ((bytes x).drop (8 * j)).length = 4 := by
    rw [List.length_drop, length_bytes]; omega
  have ht : ((bytes x).drop (8 * j)).take 8 = ((bytes x).drop (8 * j)).take 4 := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  rw [ht, bytesToWordLE_len4 _ (by rw [List.length_take, hd]; rfl), leNat8_slice x 4 (8 * j) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * j) = 64 * j by ring]
  have hx : x.toNat / 2 ^ (64 * j) < 2 ^ (8 * 4) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    calc x.toNat < 2 ^ (8 * n) := x.isLt
      _ = 2 ^ (8 * 4 + 64 * j) := by congr 1; omega
  rw [Nat.mod_eq_of_lt hx]
theorem bytes_word_lt {n : Nat} (x : Bytes n) (j : Nat) (hn : n % 8 = 4) (h : 8 * j < n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  rcases Nat.lt_or_ge (8 * j + 8) (n + 1) with h1 | h1
  · exact bytes_word x j (by omega)
  · exact bytes_word_tail x j (by omega)
theorem extractByte_or8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)
theorem extractByte_bytesToWordLE (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8 _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0)]
def VERIFY_DATA : Nat := 0xffbde0
def MSGADDR : Nat := 26144
structure InitOK (m : T3.Message) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) : Prop where
  known : KnownOK k0 s
  pc : s.pc = pcOf 0
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (MSGADDR + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0xA0 ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  sp : s.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
theorem verifyData_length : (submission.image .verify).data.length = 16928 := Images.verifyData_length
theorem dataBase_verify : dataBase (submission.image .verify) = VERIFY_DATA := by
  unfold dataBase; rw [verifyData_length]; decide +kernel
theorem verifyData_mask :
    bytesToWordLE ((((submission.image .verify).data).drop 536).take 8) = 520192#64 := by
  decide +kernel
theorem verifyData_header (lay : Nat) (hl : lay < 4) :
    bytesToWordLE ((((submission.image .verify).data).drop (424 + 8 * ((lay + 1) % 4))).take 8) =
      BitVec.ofNat 64 (hyperBase lay) := by
  interval_cases lay <;> decide +kernel
theorem verifyData_buffer3 :
    bytesToWordLE ((((submission.image .verify).data).drop 360).take 8) = 22288#64 := by
  decide +kernel
/-- Campaign T51: verify data word 16 is the r6 field mask 0xFF00. -/
theorem verifyData_mask6 :
    bytesToWordLE ((((submission.image .verify).data).drop 16).take 8) = 65280#64 := by
  decide +kernel
theorem verifyData_initialMask :
    bytesToWordLE ((((submission.image .verify).data).take 8)) = 0xfff#64 := by
  decide +kernel
set_option maxRecDepth 200000 in
theorem init_ok (m : Legacy.Message) (pk : PublicKey) (w : Bytes 22012) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : InitOK m pk w s := by
  unfold initialState at h
  simp only [submission_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have hl : inputBuffers submission.sizes submission.layout .verify (m, pk, w) =
      [(MSGADDR, bytes m), (0xA0, bytes pk), (0x1020, bytes w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil]
  have lm : (bytes m).length = 32 := length_bytes m
  have lp : (bytes pk).length = 16 := length_bytes pk
  have lw : (bytes w).length = 22012 := length_bytes w
  have lD := verifyData_length
  have eD := dataBase_verify
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set s0 := blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase (submission.image .verify)))
    (submission.image .verify).data
  set s1 := s0.writeBytesAsWords (BitVec.ofNat 64 MSGADDR) (bytes m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x1020) (bytes w)
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getMem A =
      s3.getMem A := fun A => by simp [MachineState.setReg, MachineState.getMem]
  have g0 : ∀ A, A < 2 ^ 64 → s0.getMem (BitVec.ofNat 64 A) =
      if VERIFY_DATA ≤ A ∧ A < VERIFY_DATA + 8 * ((16928 + 7) / 8) ∧ (A - VERIFY_DATA) % 8 = 0 then
        bytesToWordLE ((((submission.image .verify).data).drop (A - VERIFY_DATA)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords (submission.image .verify).data blank (dataBase (submission.image .verify)) A
      (by rw [lD, eD]; unfold VERIFY_DATA; omega) hA, lD, eD]; rfl
  have g0z : ∀ A, A < VERIFY_DATA → s0.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA
    rw [g0 A (by unfold VERIFY_DATA at hA; omega), if_neg (by omega)]
  have g1 : ∀ A, A < 2 ^ 64 → s1.getMem (BitVec.ofNat 64 A) =
      if MSGADDR ≤ A ∧ A < MSGADDR + 8 * ((32 + 7) / 8) ∧ (A - MSGADDR) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - MSGADDR)).take 8) else s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s0 MSGADDR A (by rw [lm]; unfold MSGADDR; omega) hA, lm]
  have g2 : ∀ A, A < 2 ^ 64 → s2.getMem (BitVec.ofNat 64 A) =
      if 0xA0 ≤ A ∧ A < 0xA0 + 8 * ((16 + 7) / 8) ∧ (A - 0xA0) % 8 = 0 then
        bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8) else s1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s1 0xA0 A (by rw [lp]; omega) hA, lp]
  have g3 : ∀ A, A < 2 ^ 64 → s3.getMem (BitVec.ofNat 64 A) =
      if 0x1020 ≤ A ∧ A < 0x1020 + 8 * ((22012 + 7) / 8) ∧ (A - 0x1020) % 8 = 0 then
        bytesToWordLE (((bytes w).drop (A - 0x1020)).take 8) else s2.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s2 0x1020 A (by rw [lw]; omega) hA, lw]
  have gb : ∀ A, VERIFY_DATA ≤ A → A < 2 ^ 24 →
      (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getByte
        (BitVec.ofNat 64 A) = (submission.image .verify).data.getD (A - VERIFY_DATA) 0 := by
    intro A hA hA'
    rw [T3M.getByte_eq_word _ _ (by omega), gm,
      g3 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g2 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g1 _ (by omega), if_neg (by unfold VERIFY_DATA MSGADDR at *; omega),
      g0 _ (by omega), if_pos (by unfold VERIFY_DATA at *; omega),
      extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide +kernel))]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      if_pos (Nat.mod_lt A (show 0 < 8 by decide +kernel))]
    have hidx : A / 8 * 8 - VERIFY_DATA + A % 8 = A - VERIFY_DATA := by
      unfold VERIFY_DATA at hA ⊢
      omega
    rw [hidx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hr1 : ∀ (st : MachineState) (base : Word) (l : List (BitVec 8)),
        (st.writeBytesAsWords base l).regs = st.regs := by
      intro st base l
      induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length)
        generalizing st base with
      | hwf => exact (measure List.length).wf
      | h l ih =>
        match l with
        | [] => simp
        | b :: bs =>
          unfold MachineState.writeBytesAsWords
          rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
          rfl
    have hr : s3.regs = blank.regs := by simp only [s3, s2, s1, s0, hr1]
    simp only [k0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [MachineState.setReg, MachineState.getReg, hr, blank]
  · have hp1 : ∀ (st : MachineState) (base : Word) (l : List (BitVec 8)),
        (st.writeBytesAsWords base l).pc = st.pc := by
      intro st base l
      induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length)
        generalizing st base with
      | hwf => exact (measure List.length).wf
      | h l ih =>
        match l with
        | [] => simp
        | b :: bs =>
          unfold MachineState.writeBytesAsWords
          rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
          rfl
    simp only [MachineState.pc_setReg, s3, s2, s1, s0, hp1, blank]
    rfl
  · intro k hk
    unfold MSGADDR
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_pos (by unfold MSGADDR; omega), show 26144 + 8 * k - MSGADDR = 8 * k by unfold MSGADDR; omega,
      bytes_word m k (by omega)]
  · refine ⟨?_, ?_⟩
    · show (s3.setReg .x2 _).getMem (BitVec.ofNat 64 0xA0) = _
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_pos (by omega),
        show (0xA0 : Nat) - 0xA0 = 8 * 0 by rfl, bytes_word pk 0 (by omega)]
    · show (s3.setReg .x2 _).getMem (BitVec.ofNat 64 0xA8) = _
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_pos (by omega),
        show (0xA8 : Nat) - 0xA0 = 8 * 1 by rfl, bytes_word pk 1 (by omega)]
  · intro j hj
    unfold WX at hj
    rw [gm, g3 _ (by unfold WIT; omega), if_pos (by unfold WIT; omega),
      show WIT + 8 * j - 0x1020 = 8 * j by unfold WIT; omega, bytes_word_lt w j (by norm_num) (by omega)]
    rfl
  · intro A hA hz
    unfold WIT at hA
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_neg (by unfold MSGADDR; omega), g0z A (by unfold VERIFY_DATA; omega)]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [gm, g3 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE; omega),
        g2 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE; omega),
        g1 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE MSGADDR; omega),
        g0 _ (by unfold TOPBASE; omega), if_pos (by unfold TOPBASE VERIFY_DATA; omega),
        show TOPBASE - 8 - VERIFY_DATA = 536 by unfold TOPBASE VERIFY_DATA; omega,
        verifyData_mask]
    · intro lay hl
      have hb := hdrAddr_bounds lay
      unfold TOPBASE at hb
      rw [gm, g3 _ (by omega), if_neg (by omega),
        g2 _ (by omega), if_neg (by omega),
        g1 _ (by omega), if_neg (by unfold MSGADDR; omega),
        g0 _ (by omega), if_pos (by unfold hdrAddr TOPBASE VERIFY_DATA; omega),
        show hdrAddr lay - VERIFY_DATA = 424 + 8 * ((lay + 1) % 4) by unfold hdrAddr TOPBASE VERIFY_DATA; omega,
        verifyData_header lay hl]
    · rw [gm, g3 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9; omega),
        g2 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9; omega),
        g1 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9 MSGADDR; omega),
        g0 _ (by unfold TOPB9; omega), if_pos (by unfold TOPB9 VERIFY_DATA; omega),
        show TOPB9 + 56 - VERIFY_DATA = 360 by unfold TOPB9 VERIFY_DATA; omega,
        verifyData_buffer3]
    · rw [gm, g3 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9; omega),
        g2 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9; omega),
        g1 _ (by unfold TOPB9; omega), if_neg (by unfold TOPB9 MSGADDR; omega),
        g0 _ (by unfold TOPB9; omega), if_pos (by unfold TOPB9 VERIFY_DATA; omega),
        show TOPB9 - 288 - VERIFY_DATA = 16 by unfold TOPB9 VERIFY_DATA; omega,
        verifyData_mask6]
  · simp [MachineState.setReg, MachineState.getReg]
    exact congrArg (BitVec.ofNat 64) eD
end SigGolfCandidate.T3M.Verify
end
-- ==== merged from W9Fin_V7_Final ====
section

set_option Elab.async false

section



namespace W9Fin.V7
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
abbrev WB := ClaudeWCT.W9.T3M.WBytes
def digestQ (m : SigGolfCandidate.T3.Message) (w : WB) : Query :=
  toQ (pad64 (digestInput (ClaudeWCT.W9.T3M.wrho w) m (ClaudeWCT.W9.T3M.wdc w)))
def ftsAcceptCost (overhead : Nat) (a : HashOutput) : Nat :=
  overhead + ClaudeWCT.WCT9.jointCost a
def FtsGoodByCost (GatePre : Digest → WB → HashOutput → MachineState → Prop)
    (FtsOut : Digest → WB → HashOutput → Digest × Digest → MachineState → Prop)
    (acceptCost : HashOutput → Nat) : Prop :=
  ∀ (pk : Digest) (w : WB) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs),
    GatePre pk w a u →
    K none = pure (false, 0) →
    (∀ top t, FtsOut pk w a top t → GoodQ t N C Q A (K (some top))) →
    GoodQ u (N + 2023) (C + 2023) Q (A + acceptCost a)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none) K)
def afterFts (pk : Digest) (w : WB) (index : Nat) (r : Option (Digest × Digest)) : SigGolfCandidate.T3.M Bool :=
  match r with
  | some top => do
      let __x ← ClaudeWCT.W9.T3M.layersBC w index 4 (.pair top.1 top.2)
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false
def AfterGoodBudget (FtsOut : Digest → WB → HashOutput → Digest × Digest → MachineState → Prop)
    (acceptCycles : Nat) : Prop :=
  ∀ (pk : Digest) (w : WB) (Q : Prop), Q →
    ∀ (a : HashOutput) (top : Digest × Digest) (u : MachineState),
      FtsOut pk w a top u →
      GoodQ u 8050 8050 Q acceptCycles (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb)
def PrefixGood (GatePre : Digest → WB → HashOutput → MachineState → Prop) : Prop :=
  ∀ (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22012) (s : MachineState),
    initialState submission .verify (m, pk, w) = some s →
    ∀ (P : Hash → Prop) (N C A : Nat) (Q : Prop) (K : Option HashOutput → OracleComp HashSpec Obs),
      K none = pure (false, 0) →
      (∀ a u, (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow → GatePre pk w a u →
        GoodQP (fun hash => hash (digestQ m w) = a ∧ P hash) u N C Q A (K (some a))) →
      GoodQP P s (N + 10) (C + 11) Q (A + 11) (ccM (ClaudeWCT.W9.T3M.digestP m w) K)
end W9Fin.V7
end

section




set_option linter.unusedSimpArgs false
namespace W9Fin.V7
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
theorem GoodQP.mono' {P : Hash → Prop} {s : MachineState} {N C A N' C' A' : Nat} {Q : Prop}
    {X : OracleComp HashSpec Obs} (h : GoodQP P s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hA : A ≤ A') :
    GoodQP P s N' C' Q A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs hp => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs hp
  exact ⟨hq, by omega⟩
theorem GoodQP.reject {P : Hash → Prop} {s : MachineState} {Q : Prop} {A : Nat}
    (hf : fetch image s = some (.base .ECALL)) (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) :
    GoodQP P s 1 1 Q A (pure (false, 0)) := by
  have h := GoodQ.reject (Q := Q) (A := A) hf h5 h10
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  refine ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2.1, fun hs _ => ?_⟩⟩
  have e := congrArg (evalWithAnswerFn hash) h1
  rw [evalWithAnswerFn_map, evalWithAnswerFn_pure] at e
  simp only [obs, Prod.mk.injEq] at e
  exact absurd (decide_eq_true hs) (by rw [e.1]; decide)
theorem GoodQP.publicHash_bind_pre {P : Hash → Prop} {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : HashOutput → SigGolfCandidate.T3.M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQP (fun hash => hash (toQ (pad64 input)) = a ∧ P hash) (writeHash s a) N C Q A
      (ccM (f a) K)) :
    GoodQP P s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (SigGolfCandidate.T3.publicHash input >>= f) K) := by
  have := GoodQP.query_pre (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]
def Bank (u : MachineState) : Prop :=
  W9Drv.ForestData u ∧ W9Drv.HeaderBank u ∧ W9Drv.SharedGate.SetupMask u ∧
    u.getMem (BitVec.ofNat 64 VERIFY_DATA) = BitVec.ofNat 64 0xfff ∧
    u.getMem (BitVec.ofNat 64 (VERIFY_DATA + 8)) = BitVec.ofNat 64 26112
theorem Bank.congr {s t : MachineState} (h : Bank s)
    (hm : ∀ A, VERIFY_DATA ≤ A → A < VERIFY_DATA + 472 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : Bank t := by
  obtain ⟨⟨f0, f1, f2⟩, ⟨htop, htop8⟩, ⟨mpad, mc, mj, mk, mg, md0, ma, ms⟩, d0, d8⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ⟨fun k hk => ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact f0
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact f1
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact f2
  · rw [hm _ (by unfold TOPLOAD VERIFY_DATA; omega) (by unfold TOPLOAD VERIFY_DATA; omega)]
    exact htop k hk
  · rw [hm _ (by unfold TOPLOAD VERIFY_DATA; omega) (by unfold TOPLOAD VERIFY_DATA; omega)]
    exact htop8
  · rw [hm _ (by unfold W9Drv.stackBase7 W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.stackBase7 W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact mpad
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact mc
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact mj
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact mk
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact mg
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact md0
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact ma
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact ms
  · rw [hm _ (le_refl _) (by unfold VERIFY_DATA; omega)]
    exact d0
  · rw [hm _ (by omega) (by omega)]
    exact d8
theorem init_word (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22012) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) (j : Nat) (hj : j < 2116) :
    s.getMem (BitVec.ofNat 64 (VERIFY_DATA + 8 * j)) =
      bytesToWordLE (((submission.image .verify).data.drop (8 * j)).take 8) := by
  unfold initialState at h
  simp only [submission_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have hl : inputBuffers submission.sizes submission.layout .verify (m, pk, w) =
      [(26144, bytes m), (0xA0, bytes pk), (0x1020, bytes w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil]
  have lm : (bytes m).length = 32 := length_bytes m
  have lp : (bytes pk).length = 16 := length_bytes pk
  have lw : (bytes w).length = 22012 := length_bytes w
  have lD := verifyData_length
  have eD := dataBase_verify
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set s0 := blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase (submission.image .verify)))
    (submission.image .verify).data
  set s1 := s0.writeBytesAsWords (BitVec.ofNat 64 26144) (bytes m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x1020) (bytes w)
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getMem A =
      s3.getMem A := fun A => by simp [MachineState.setReg, MachineState.getMem]
  have g0 : ∀ A, A < 2 ^ 64 → s0.getMem (BitVec.ofNat 64 A) =
      if VERIFY_DATA ≤ A ∧ A < VERIFY_DATA + 8 * ((16928 + 7) / 8) ∧ (A - VERIFY_DATA) % 8 = 0 then
        bytesToWordLE ((((submission.image .verify).data).drop (A - VERIFY_DATA)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords (submission.image .verify).data blank (dataBase (submission.image .verify)) A
      (by rw [lD, eD]; unfold VERIFY_DATA; omega) hA, lD, eD]; rfl
  have g1 : ∀ A, A < 2 ^ 64 → s1.getMem (BitVec.ofNat 64 A) =
      if 26144 ≤ A ∧ A < 26144 + 8 * ((32 + 7) / 8) ∧ (A - 26144) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 26144)).take 8) else s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s0 26144 A (by rw [lm]; omega) hA, lm]
  have g2 : ∀ A, A < 2 ^ 64 → s2.getMem (BitVec.ofNat 64 A) =
      if 0xA0 ≤ A ∧ A < 0xA0 + 8 * ((16 + 7) / 8) ∧ (A - 0xA0) % 8 = 0 then
        bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8) else s1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s1 0xA0 A (by rw [lp]; omega) hA, lp]
  have g3 : ∀ A, A < 2 ^ 64 → s3.getMem (BitVec.ofNat 64 A) =
      if 0x1020 ≤ A ∧ A < 0x1020 + 8 * ((22012 + 7) / 8) ∧ (A - 0x1020) % 8 = 0 then
        bytesToWordLE (((bytes w).drop (A - 0x1020)).take 8) else s2.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s2 0x1020 A (by rw [lw]; omega) hA, lw]
  rw [gm, g3 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g2 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g1 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g0 _ (by unfold VERIFY_DATA; omega), if_pos (by unfold VERIFY_DATA; omega),
    show VERIFY_DATA + 8 * j - VERIFY_DATA = 8 * j by omega]
set_option maxRecDepth 200000 in
theorem init_bank (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22012) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : Bank s := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨fun k hk => ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [show W9Drv.dataBase7 + 16 = VERIFY_DATA + 8 * 2 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 2 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 24 = VERIFY_DATA + 8 * 3 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 3 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 32 = VERIFY_DATA + 8 * 4 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 4 (by omega)]
    decide +kernel
  · rw [show TOPLOAD + 8 * k = VERIFY_DATA + 8 * (49 + k) by unfold TOPLOAD VERIFY_DATA; omega,
      init_word m pk w s h (49 + k) (by omega)]
    interval_cases k <;> decide +kernel
  · rw [show TOPLOAD - 8 = VERIFY_DATA + 8 * 48 by unfold TOPLOAD VERIFY_DATA; omega,
      init_word m pk w s h 48 (by omega)]
    decide +kernel
  · rw [show W9Drv.stackBase7 + 48 = VERIFY_DATA + 8 * 6 by unfold W9Drv.stackBase7 W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 6 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 368 = VERIFY_DATA + 8 * 46 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 46 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 376 = VERIFY_DATA + 8 * 47 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 47 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 464 = VERIFY_DATA + 8 * 58 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 58 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 352 = VERIFY_DATA + 8 * 44 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 44 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 = VERIFY_DATA + 8 * 0 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 0 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 56 = VERIFY_DATA + 8 * 7 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 7 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 64 = VERIFY_DATA + 8 * 8 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 8 (by omega)]
    decide +kernel
  · rw [show VERIFY_DATA = VERIFY_DATA + 8 * 0 by rfl, init_word m pk w s h 0 (by omega)]
    decide +kernel
  · rw [show VERIFY_DATA + 8 = VERIFY_DATA + 8 * 1 by rfl, init_word m pk w s h 1 (by omega)]
    decide +kernel
theorem extract_top_word {n : Nat} (w : BitVec (8 * n)) (j : Nat) (h : 8 * n ≤ 64 * j + 32) :
    w.extractLsb' (64 * j) 64 = BitVec.ofNat 64 (w.extractLsb' (64 * j) 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hw : w.toNat / 2 ^ (64 * j) < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    exact lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (lt_trans hw (by norm_num))]
theorem wword_dc (w : WB) : wword w 2751 = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wdc w).toNat := by
  unfold wword ClaudeWCT.W9.T3M.wdc ClaudeWCT.W9.T3M.wle32 ClaudeWCT.W9.T3M.dcOff
  exact extract_top_word w 2751 (by norm_num)
theorem wdc_eq_of_lt (w : WB) (h : (ClaudeWCT.W9.T3M.wdcWord w).toNat < 2 ^ 32) :
    (ClaudeWCT.W9.T3M.wdc w).toNat = (ClaudeWCT.W9.T3M.wdcWord w).toNat := by
  simp only [ClaudeWCT.W9.T3M.wdc, ClaudeWCT.W9.T3M.wle32, ClaudeWCT.W9.T3M.wdcWord, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow] at h ⊢
  rw [← Nat.mod_mod_of_dvd (w.toNat / 2 ^ (8 * ClaudeWCT.W9.T3M.dcOff)) (show 2 ^ 32 ∣ 2 ^ 64 by norm_num),
    Nat.mod_eq_of_lt h]
theorem digest_words (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    wordsOf (digestInput rho m c) =
      [dlo rho, dhi rho, 0, BitVec.ofNat 64 c.toNat,
        m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64, m.extractLsb' 192 64] :=
  wordsOf_digestInput rho m c
abbrev cw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def kSp : List (Reg × Word) := k0 ++ [(.x2, BitVec.ofNat 64 VERIFY_DATA)]
def ldSpec : Spec :=
  ⟨[(.x10, .ld (cw (VERIFY_DATA + 8)))], [], 1, false, 1, [], none, 1⟩
def kLd : List (Reg × Word) := kSp.filter fun p => p.1 ≠ .x10
theorem ldCheck : specB [] [] [] (runAt kSp [1] 0 []) ldSpec [] kLd [] = true := by
  decide +kernel
def kPro : List (Reg × Word) :=
  kSp.map fun p => if p.1 = .x10 then (.x10, 26112) else p
structure ProInit (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState) : Prop where
  known : KnownOK kPro s
  pc : s.pc = pcOf 1
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (MSGADDR + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0xA0 ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  sp : s.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
theorem kSp_ok {m : SigGolfCandidate.T3.Message} {pk : Digest} {w : WB} {s : MachineState} (hs : InitOK m pk w s) :
    KnownOK kSp s := by
  intro p hp
  simp only [kSp, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact hs.known p hp
  · exact hs.sp
theorem ld_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) :
    ∃ s1, Steps image s 1 1 s1 ∧ ProInit m pk w s1 ∧ Bank s1 := by
  obtain ⟨s1, h1⟩ := spec_run ldCheck s hs.pc (kSp_ok hs) (by simp [ldSpec]) (by simp)
  have hm : ∀ A, s1.getMem A = s.getMem A := fun A => h1.mem A
  have h10 : s1.getReg .x10 = 26112 := by
    rw [h1.regs (.x10, .ld (cw (VERIFY_DATA + 8))) (by simp [ldSpec])]
    exact hb.2.2.2.2
  have hknown : KnownOK kPro s1 := by
    intro p hp
    simp only [kPro, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    split
    · rename_i heq
      simpa only [heq] using h10
    · rename_i hne
      exact h1.known q (List.mem_filter.mpr ⟨hq, by simp only [decide_eq_true_eq]; exact hne⟩)
  refine ⟨s1, h1.steps, ⟨hknown, h1.pc rfl, fun k hk => (hm _).trans (hs.msg k hk),
    ⟨(hm _).trans hs.pk.1, (hm _).trans hs.pk.2⟩, fun j hj => (hm _).trans (hs.wit j hj),
    fun A hA hz => (hm _).trans (hs.zero A hA hz), hs.data.congr (fun A _ _ => hm _),
    h1.known (.x2, BitVec.ofNat 64 VERIFY_DATA) (by decide +kernel)⟩, hb.congr (fun A _ _ => hm _)⟩
def rejectPc : Nat := 33511
def rejSpec (steps : Nat) (brs : List Br) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], rejectPc, true, steps, brs, none, steps⟩
def proSpec : Spec :=
  ⟨[(.x11, cw 64)], [(⟨none, BitVec.ofNat 64 26128⟩, cw 0)], 3, true, 2, [], none, 2⟩
def proPost : List (Reg × Word) :=
  (kPro.filter fun p => p.1 ≠ .x3 ∧ p.1 ≠ .x4 ∧ p.1 ≠ .x11) ++ [(.x11, 64)]
theorem proCheck : specB [26128] [] [] (runAt kPro [] 1 []) proSpec [] proPost [] = true := by
  decide +kernel
structure DgPre (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (t : MachineState) : Prop where
  pc : t.pc = pcOf 3
  known : KnownOK proPost t
  wit : Orig w (fun o => o ≠ 22000) t
  zw : t.getMem (BitVec.ofNat 64 26128) = 0
  msg : ∀ k, k < 4 → t.getMem (BitVec.ofNat 64 (MSGADDR + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk t
  zero : ∀ A, A < WIT → (A < 0xA0 ∨ 0xB0 ≤ A) → t.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK t
  sp : t.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
  bank : Bank t
structure DgOut (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (a : HashOutput) (u : MachineState) :
    Prop where
  pc : u.pc = pcOf 4
  known : KnownOK proPost u
  wit : Orig w (fun o => o ≠ 22000) u
  digest : W9Drv.DigestAt a u
  pk : PkOK pk u
  zero : ∀ A, A < WIT → 32 ≤ A → (A < 0xA0 ∨ 0xB0 ≤ A) → u.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK u
  sp : u.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
  bank : Bank u
theorem digest_tail (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : ProInit m pk w s) (hb : Bank s) :
    ((ClaudeWCT.W9.T3M.wdc w).toNat ≥ ClaudeWCT.WCT9.digestVerifyWindow → ∃ u, Steps image s 6 6 u ∧
        fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow → ∃ t, Steps image s 2 2 t ∧
        fetch image t = some (.base .ECALL) ∧ hashArgumentsValid t = true ∧
        hashInput t = toQ (pad64 (digestInput (ClaudeWCT.W9.T3M.wrho w) m (ClaudeWCT.W9.T3M.wdc w))) ∧
        DgPre m pk w t) := by
  constructor
  · intro hge
    exact False.elim ((Nat.not_le.mpr (ClaudeWCT.W9.T3M.wdc w).isLt) hge)
  · intro hlt
    obtain ⟨t, ht⟩ := spec_run proCheck s hs.pc hs.known (by simp [proSpec]) (by simp)
    have hm : ∀ A, t.getMem A = memEval s proSpec.mem A := ht.mem
    have hkt : KnownOK proPost t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 26112 := hkt (.x10, 26112) (by decide +kernel)
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by decide +kernel)
    have h12 : t.getReg .x12 = BitVec.ofNat 64 0 := hkt (.x12, 0) (by decide +kernel)
    have frame : ∀ A, A < 2 ^ 64 → A ≠ 26128 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [proSpec, List.mem_singleton] at hp
      subst hp
      exact ⟨rfl, by simpa using fun h => h1 (by omega)⟩
    have hz : t.getMem (BitVec.ofNat 64 26128) = 0 := by
      rw [hm]; simp [proSpec, memEval, Addr.eval, E.eval]
    refine ⟨t, ht.steps, ht.ecall rfl, ?_, ?_, ?_⟩
    · exact hashArgs_of t 26112 64 0 h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · have hl := digestInput_length (ClaudeWCT.W9.T3M.wrho w) m (ClaudeWCT.W9.T3M.wdc w)
      rw [pad64_digestInput]
      apply hashInput_words8 t _ 26112 hl h10 (by decide +kernel) (by decide +kernel) h11
      rw [digest_words]
      have e0 : t.getMem (BitVec.ofNat 64 26112) = dlo (ClaudeWCT.W9.T3M.wrho w) := by
        rw [frame _ (by omega) (by omega), show (26112 : Nat) = WIT + 8 * 2748 by unfold WIT; omega,
          hs.wit 2748 (by unfold WX; omega)]
        exact (SigGolfCandidate.T3M.Verify.wdig_lo w 2748).symm
      have e1 : t.getMem (BitVec.ofNat 64 (26112 + 8)) = dhi (ClaudeWCT.W9.T3M.wrho w) := by
        rw [frame _ (by omega) (by omega), show (26112 + 8 : Nat) = WIT + 8 * 2749 by unfold WIT; omega,
          hs.wit 2749 (by unfold WX; omega)]
        exact (SigGolfCandidate.T3M.Verify.wdig_hi w 2748).symm
      have e3 : t.getMem (BitVec.ofNat 64 (26112 + 24)) = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wdc w).toNat := by
        rw [frame _ (by omega) (by omega), show (26112 + 24 : Nat) = WIT + 8 * 2751 by unfold WIT; omega,
          hs.wit 2751 (by unfold WX; omega), wword_dc]
      have em : ∀ k, k < 4 → t.getMem (BitVec.ofNat 64 (26112 + 32 + 8 * k)) = m.extractLsb' (64 * k) 64 := by
        intro k hk
        rw [frame _ (by omega) (by omega), show 26112 + 32 + 8 * k = MSGADDR + 8 * k by unfold MSGADDR; omega,
          hs.msg k hk]
      rw [e0, e1, show 26112 + 16 = 26128 by rfl, hz, e3, show 26112 + 32 = 26112 + 32 + 8 * 0 by rfl,
        em 0 (by omega), show 26112 + 40 = 26112 + 32 + 8 * 1 by rfl, em 1 (by omega),
        show 26112 + 48 = 26112 + 32 + 8 * 2 by rfl, em 2 (by omega), show 26112 + 56 = 26112 + 32 + 8 * 3 by rfl,
        em 3 (by omega)]
    · refine ⟨ht.pc rfl, hkt, ?_, hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj hp
        rw [frame _ (by unfold WIT WX at *; omega) (by unfold WIT; omega)]
        exact hs.wit j hj
      · intro k hk
        rw [frame _ (by unfold MSGADDR; omega) (by unfold MSGADDR; omega)]
        exact hs.msg k hk
      · exact ⟨(frame 0xA0 (by omega) (by omega)).trans hs.pk.1, (frame 0xA8 (by omega) (by omega)).trans hs.pk.2⟩
      · intro A hA hz'
        unfold WIT at hA
        rw [frame A (by omega) (by omega)]
        exact hs.zero A (by unfold WIT; omega) hz'
      · apply hs.data.congr
        intro A hA hEnd
        exact frame A (by omega) (by unfold TAB at hA; omega)
      · exact hkt (.x2, BitVec.ofNat 64 VERIFY_DATA) (by decide +kernel)
      · exact hb.congr (fun A hA _ => frame A (by unfold VERIFY_DATA at *; omega)
          (by unfold VERIFY_DATA at hA; omega))
theorem digest_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) :
    ((ClaudeWCT.W9.T3M.wdc w).toNat ≥ ClaudeWCT.WCT9.digestVerifyWindow → ∃ u, Steps image s 7 7 u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow → ∃ t, Steps image s 3 3 t ∧
      fetch image t = some (.base .ECALL) ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (pad64 (digestInput (ClaudeWCT.W9.T3M.wrho w) m (ClaudeWCT.W9.T3M.wdc w))) ∧
      DgPre m pk w t) := by
  obtain ⟨s0, st, hs0, hb0⟩ := ld_step m pk w s hs hb
  obtain ⟨hr, ha⟩ := digest_tail m pk w s0 hs0 hb0
  constructor
  · intro h
    obtain ⟨u, stu, hf, h5, h10⟩ := hr h
    exact ⟨u, st.trans stu, hf, h5, h10⟩
  · intro h
    obtain ⟨t, stt, hf, hv, hin, hp⟩ := ha h
    exact ⟨t, st.trans stt, hf, hv, hin, hp⟩
theorem digest_out (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (t : MachineState)
    (ht : DgPre m pk w t) (a : HashOutput) : DgOut m pk w a (writeHash t a) := by
  have h12 : t.getReg .x12 = BitVec.ofNat 64 0 := ht.known (.x12, 0) (by decide +kernel)
  refine ⟨?_, ht.known.writeHash a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, ht.pc]; rfl
  · intro j hj hp
    rw [writeHash_frame t a 0 _ h12 (by unfold WIT WX at *; omega) (by omega) (Or.inr (by unfold WIT; omega))]
    exact ht.wit j hj hp
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact writeHash_at0 t a 0 h12 (by omega)
    · exact writeHash_at8 t a 0 h12 (by omega)
    · exact writeHash_at16 t a 0 h12 (by omega)
    · exact writeHash_at24 t a 0 h12 (by omega)
  · exact ⟨(writeHash_frame t a 0 0xA0 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.1,
       (writeHash_frame t a 0 0xA8 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.2⟩
  · intro A hA h32 hz
    unfold WIT at hA
    rw [writeHash_frame t a 0 A h12 (by omega) (by omega) (Or.inr (by omega))]
    exact ht.zero A (by unfold WIT; omega) hz
  · apply ht.data.congr
    intro A hA hEnd
    exact writeHash_frame t a 0 A h12 (by omega) (by omega) (Or.inr (by unfold TAB at hA; omega))
  · rw [writeHash_getReg]; exact ht.sp
  · exact ht.bank.congr (fun A hA _ => writeHash_frame t a 0 A h12 (by unfold VERIFY_DATA at *; omega) (by omega)
      (Or.inr (by unfold VERIFY_DATA at hA; omega)))
theorem digestP_good (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) {P : Hash → Prop} {N C A : Nat} {Q : Prop} (hN : 1 ≤ N)
    (K : Option HashOutput → OracleComp HashSpec Obs) (hK : K none = pure (false, 0))
    (hcont : ∀ a u, (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow → DgOut m pk w a u →
      GoodQP (fun hash => hash (digestQ m w) = a ∧ P hash) u N C Q A (K (some a))) :
    GoodQP P s (N + 5) (C + 11) Q (A + 11) (ccM (ClaudeWCT.W9.T3M.digestP m w) K) := by
  obtain ⟨hrej, hacc⟩ := digest_step m pk w s hs hb
  unfold ClaudeWCT.W9.T3M.digestP
  by_cases hdc : (ClaudeWCT.W9.T3M.wdc w).toNat ≥ ClaudeWCT.WCT9.digestVerifyWindow
  · exact False.elim ((Nat.not_le.mpr (ClaudeWCT.W9.T3M.wdc w).isLt) hdc)
  · rw [if_neg hdc, ccM_map]
    obtain ⟨t, hst, hf, hv, hin, hpre⟩ := hacc (by omega)
    unfold SigGolfCandidate.T3.digest
    have h5 : t.getReg .x5 = 0 := hpre.known (.x5, 0) (by decide +kernel)
    have := GoodQP.publicHash_bind_pre (P := P) (f := pure) (K := fun a => K (some a)) hf h5 hv hin (fun a => by
      rw [ccM_pure]; exact hcont a _ (by omega) (digest_out m pk w t hpre a))
    rw [bind_pure, blocks_digestInput] at this
    exact GoodQP.steps' hst this (by omega) (by omega) (by omega)
theorem gatePre_of_dgOut (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (a : HashOutput)
    (u : MachineState) (hu : DgOut m pk w a u) :
    W9Drv.SharedGate.Pre pk w a u := by
  have h5 : u.getReg .x5 = 0 := hu.known (.x5, 0) (by decide +kernel)
  have hglob : Glob [(.x5, 0)] w pk u := by
    refine ⟨?_, fun j hj hj' => hu.wit j (by unfold WX; omega) (by omega), hu.pk, ?_, ?_, hu.data⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact h5
    · intro A hA
      simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl <;> exact hu.zero _ (by unfold WIT; omega) (by omega) (by omega)
    · show (u.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hu.zero CTRW (by unfold CTRW WIT; omega) (by unfold CTRW; omega) (by unfold CTRW; omega)]
      rfl
  exact ⟨hu.pc, hglob, hu.known (.x11, 64) (by decide +kernel),
    hu.bank.1, hu.digest, hu.bank.2.1, fun j hj hp => hu.wit j hj (by omega), hu.bank.2.2.1, hu.sp⟩
theorem prefixGood : PrefixGood W9Drv.SharedGate.Pre := by
  intro m pk w s hs P N C A Q K hK hcont
  have h := digestP_good m pk w s (init_ok m pk w s hs) (init_bank m pk w s hs) (P := P) (N := N + 1)
    (C := C) (A := A) (Q := Q) (by omega) K hK (fun a u hdc hu =>
      GoodQP.mono' (hcont a u hdc (gatePre_of_dgOut m pk w a u hu)) (by omega) le_rfl le_rfl)
  exact GoodQP.mono' h (by omega) (by omega) (by omega)
end W9Fin.V7
end

section



namespace W9Fin.V7
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
theorem digestP_eval (hash : Hash) (m : SigGolfCandidate.T3.Message) (w : WB)
    (hdc : (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow) :
    evalWithAnswerFn hash (mrealize 0 (ClaudeWCT.W9.T3M.digestP m w)) = some (hash (digestQ m w)) := by
  unfold ClaudeWCT.W9.T3M.digestP
  rw [if_neg (by omega), mrealize_map]
  unfold SigGolfCandidate.T3.digest
  rw [mrealize_publicHash, evalWithAnswerFn_map, eval_liftQ]
  rfl
theorem capOk_of_pre {hash : Hash} {m : SigGolfCandidate.Legacy.Message} {w : Bytes 22012} {a : HashOutput}
    (hdc : (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow) (hq : hash (digestQ m w) = a)
    (hcap : ClaudeWCT.W9.T3M.Final.DigestCapOk hash m w) : ClaudeWCT.WCT9.capOk a = true :=
  hcap a ((digestP_eval hash m w hdc).trans (congrArg some hq))
theorem jointCost_le_of_capOk {a : HashOutput} (h : ClaudeWCT.WCT9.capOk a = true) :
    ClaudeWCT.WCT9.jointCost a ≤ 789 := by
  unfold ClaudeWCT.WCT9.capOk ClaudeWCT.WCT9.jointCap at h
  exact of_decide_eq_true h
structure Inputs (GatePre : Digest → WB → HashOutput → MachineState → Prop)
    (FtsOut : Digest → WB → HashOutput → Digest × Digest → MachineState → Prop) (ovh aG : Nat) : Prop where
  prefixGood : PrefixGood GatePre
  fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh)
  after : AfterGoodBudget FtsOut aG
  hnum : 11 + aG + ovh + 789 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound
section
variable {GatePre : Digest → WB → HashOutput → MachineState → Prop}
  {FtsOut : Digest → WB → HashOutput → Digest × Digest → MachineState → Prop} {ovh aG : Nat}
def afterDigest (pk : Digest) (w : WB) (N : HashOutput) : SigGolfCandidate.T3.M Bool :=
  (if ClaudeWCT.W9.T3M.gateOk N then ClaudeWCT.W9.T3M.wctP w N else pure none) >>=
    afterFts pk w (ClaudeWCT.WCT9.digestIndex N)
theorem verifyP_eq (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) :
    ClaudeWCT.W9.T3M.verifyP m pk w = (ClaudeWCT.W9.T3M.digestP m w >>= fun o => match o with
      | some N => afterDigest pk w N
      | none => pure false) := by
  unfold ClaudeWCT.W9.T3M.verifyP afterDigest
  congr 1; funext o
  rcases o with _ | N
  · rfl
  · cases hg : ClaudeWCT.W9.T3M.gateOk N
    · simp only [hg, Bool.not_false, if_true, if_false, Bool.false_eq_true, pure_bind, afterFts]
    · simp only [hg, Bool.not_true, if_true, if_false, Bool.false_eq_true]
      rfl
abbrev Pre (m : SigGolfCandidate.Legacy.Message) (w : Bytes 22012) (hash : Hash) : Prop :=
  HashOk hash ∧ ClaudeWCT.W9.T3M.Final.DigestCapOk hash m w
theorem afterDigest_good (fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh))
    (after : AfterGoodBudget FtsOut aG)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22012) (a : HashOutput) (u : MachineState)
    (hdc : (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow) (hu : GatePre pk w a u) :
    GoodQP (fun hash => hash (digestQ m w) = a ∧ Pre m w hash) u (8050 + 2023) (8050 + 2023) True
      (aG + (ovh + 789)) (ccM (afterDigest pk w a) Kb) := by
  have h := fts pk w a u 8050 8050 aG True (fun r => ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) r) Kb) hu
    (by simp only [afterFts, ccM_pure, Kb])
    (fun top t ht => after pk w True trivial a top t ht)
  have e : ccM (afterDigest pk w a) Kb =
      ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none)
        (fun r => ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) r) Kb) := by
    unfold afterDigest
    rw [ccM_bind]
  rw [e]
  by_cases hcap : ClaudeWCT.WCT9.capOk a = true
  · have hj := jointCost_le_of_capOk hcap
    have h' : GoodQ u (8050 + 2023) (8050 + 2023) True (aG + (ovh + 789))
        (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none)
          (fun r => ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) r) Kb)) :=
      h.mono (le_refl _) (le_refl _) (fun hq => ⟨hq, by simp only [ftsAcceptCost]; omega⟩)
    exact (GoodQ.toP h').pre_mono (fun hash hp => hp.2.1)
  · exact GoodQP.of_false h (fun hash hp => hcap (capOk_of_pre hdc hp.1 hp.2.2))
def fuelBound : Nat := 10 + (8050 + 2023)
def cycleBoundAll : Nat := 11 + (8050 + 2023)
theorem fuelBound_eq : fuelBound = 10083 := rfl
theorem cycleBoundAll_eq : cycleBoundAll = 10084 := rfl
theorem fuelBound_le : fuelBound ≤ CYCLE_LIMIT := by rw [fuelBound_eq]; unfold CYCLE_LIMIT; norm_num
theorem verify_good (prefixGood : PrefixGood GatePre)
    (fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh))
    (after : AfterGoodBudget FtsOut aG)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22012) (s : MachineState)
    (hs : initialState submission .verify (m, pk, w) = some s) :
    GoodQP (Pre m w) s fuelBound cycleBoundAll True (aG + (ovh + 789) + 11)
      (ccM (ClaudeWCT.W9.T3M.verifyP m pk w) Kb) := by
  rw [verifyP_eq, ccM_bind]
  exact prefixGood m pk w s hs (Pre m w) (8050 + 2023) (8050 + 2023) (aG + (ovh + 789)) True
    (fun o => ccM (match o with
      | some N => afterDigest pk w N
      | none => pure false) Kb) (by simp only [ccM_pure, Kb])
    (fun a u hdc hu => afterDigest_good fts after m pk w a u hdc hu)
set_option maxRecDepth 100000 in
theorem init_mk (sI eI : Riscv.Image) (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22012) :
    initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) =
      initialState submission .verify (m, pk, w) :=
  rfl
theorem mk_verify (sI eI : Riscv.Image) :
    (⟨sI, eI, Images.verifyImage⟩ : ClaudeWCT.W9.T3M.Images).verify = Images.verifyImage := rfl
theorem init_exists (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22012) :
    ∃ s, initialState submission .verify (m, pk, w) = some s := by
  unfold initialState
  simp only [submission_admissible.2 .verify, if_true]
  exact ⟨_, rfl⟩
theorem verify_refines_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyRefines I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).1
  rw [ccM_Kb] at hg
  rw [run_eq _ .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, Functor.map_map]
  change _ = (fun p => (if p.1 then some () else none, p.2)) <$>
    countCalls (mrealize 0 (ClaudeWCT.W9.T3M.verifyP m pk w))
  rw [← hg, Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT Verify.image s) ?_
  funext e
  simp only [toRunResult, obs]
  by_cases h : e.exit = .success
  · simp only [h, decide_true, if_true]; rfl
  · simp only [h, decide_false, if_false, Bool.false_eq_true]; rfl
theorem verify_terminates_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyTerminates I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro hash m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, mk_verify]
  simp only [toRunResult]
  refine ⟨?_, lt_of_le_of_lt hg.2.1 (by rw [cycleBoundAll_eq]; unfold CYCLE_LIMIT; norm_num)⟩
  simpa using hg.1
set_option maxRecDepth 100000 in
theorem verify_accept_cycles_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro hash m pk w hok hcap h
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, mk_verify] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT Images.verifyImage s)).exit = .success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  have h1 := (hg.2.2 hsucc ⟨hok, hcap⟩).2
  have h2 : aG + (ovh + 789) + 11 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound := by have := H.hnum; omega
  exact le_trans h1 h2
theorem verify_inputs_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I :=
  ⟨verify_refines_of I hI H, verify_terminates_of I hI H, verify_accept_cycles_of I hI H⟩
end
def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
theorem I0_verify : I0.verify = Images.verifyImage := rfl
theorem verify_inputs {GatePre : Digest → WB → HashOutput → MachineState → Prop}
    {FtsOut : Digest → WB → HashOutput → Digest × Digest → MachineState → Prop} {ovh aG : Nat}
    (H : Inputs GatePre FtsOut ovh aG) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs_of I0 I0_verify H
end W9Fin.V7
end

section


namespace W9Fin.V7
theorem verify_inputs_x {FtsOut : SigGolfCandidate.T3.Digest → ClaudeWCT.W9.T3M.WBytes →
      SigGolfCandidate.T3.HashOutput → SigGolfCandidate.T3.Digest × SigGolfCandidate.T3.Digest →
      RiscvZkvm.Rv64.MachineState → Prop}
    {ovh aG : Nat}
    (fts : FtsGoodByCost W9Drv.SharedGate.Pre FtsOut (ftsAcceptCost ovh))
    (after : AfterGoodBudget FtsOut aG)
    (hnum : 11 + aG + ovh + 789 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs ⟨prefixGood, fts, after, hnum⟩
end W9Fin.V7
end

namespace W9Fin.V7.Canonical
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Verifier composition is independent of the chosen honest-run predicate. -/
def FtsGoodByCost
    (GatePre : Digest → WB → HashOutput → MachineState → Prop)
    (FtsOut : Digest → WB → HashOutput → Digest × Digest → MachineState → Prop)
    (ftsProgram : WB → HashOutput → M (Option (Digest × Digest)))
    (acceptCost : HashOutput → Nat) (P : Hash → Prop) : Prop :=
  ∀ (pk : Digest) (w : WB) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option (Digest × Digest) → OracleComp HashSpec Obs),
    GatePre pk w a u → K none = pure (false, 0) →
    (∀ top t, FtsOut pk w a top t → GoodQP P t N C Q A (K (some top))) →
    GoodQP P u (N+2023) (C+2023) Q (A+acceptCost a) (ccM (ftsProgram w a) K)

def AfterGoodBudget
    (FtsOut : Digest → WB → HashOutput → Digest × Digest → MachineState → Prop)
    (afterProgram : Digest → WB → Nat → Option (Digest × Digest) → M Bool)
    (acceptCycles : Nat) (P : WB → Hash → Prop) : Prop :=
  ∀ (pk : Digest) (w : WB) (Q : Prop), Q →
    ∀ (a : HashOutput) (top : Digest × Digest) (u : MachineState),
      FtsOut pk w a top u → GoodQP (P w) u 8050 8050 Q acceptCycles
        (ccM (afterProgram pk w (ClaudeWCT.WCT9.digestIndex a) (some top)) Kb)

section
variable {GatePre : Digest → WB → HashOutput → MachineState → Prop}
  {FtsOut : Digest → WB → HashOutput → Digest × Digest → MachineState → Prop}
  {ftsProgram : WB → HashOutput → M (Option (Digest × Digest))}
  {afterProgram : Digest → WB → Nat → Option (Digest × Digest) → M Bool}
  {cost : HashOutput → Nat} {P : WB → Hash → Prop} {ovh aG cap : Nat}

def afterDigest (ftsProgram : WB → HashOutput → M (Option (Digest × Digest)))
    (afterProgram : Digest → WB → Nat → Option (Digest × Digest) → M Bool)
    (pk : Digest) (w : WB) (a : HashOutput) : M Bool :=
  ftsProgram w a >>= afterProgram pk w (ClaudeWCT.WCT9.digestIndex a)

def verifyP (ftsProgram : WB → HashOutput → M (Option (Digest × Digest)))
    (afterProgram : Digest → WB → Nat → Option (Digest × Digest) → M Bool)
    (m : SigGolfCandidate.Legacy.Message) (pk : Digest) (w : WB) : M Bool := do
  match ← ClaudeWCT.W9.T3M.digestP m w with
  | some a => afterDigest ftsProgram afterProgram pk w a
  | none => pure false

abbrev Pre (P : Hash → Prop) (cost : HashOutput → Nat) (cap : Nat)
    (m : SigGolfCandidate.Legacy.Message) (w : WB) (hash : Hash) : Prop :=
  P hash ∧ cost (hash (digestQ m w)) ≤ cap

theorem afterDigest_good
    (fts : ∀ w : WB, FtsGoodByCost GatePre FtsOut ftsProgram (fun a => ovh + cost a) (P w))
    (after : AfterGoodBudget FtsOut afterProgram aG P)
    (hnone : ∀ pk w i, afterProgram pk w i none = pure false)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : WB) (a : HashOutput) (u : MachineState)
    (hu : GatePre pk w a u) :
    GoodQP (fun hash => hash (digestQ m w) = a ∧ Pre (P w) cost cap m w hash)
      u (8050+2023) (8050+2023) True (aG+(ovh+cap))
      (ccM (afterDigest ftsProgram afterProgram pk w a) Kb) := by
  have h := fts w pk w a u 8050 8050 aG True
    (fun r => ccM (afterProgram pk w (ClaudeWCT.WCT9.digestIndex a) r) Kb) hu
    (by rw [hnone]; simp only [ccM_pure, Kb])
    (fun top t ht => after pk w True trivial a top t ht)
  intro F hF
  obtain ⟨he, hb⟩ := h F hF
  refine ⟨?_, fun hash => ⟨(hb hash).1, (hb hash).2.1, ?_⟩⟩
  · simpa only [afterDigest, ccM_bind] using he
  · intro hsucc hp
    obtain ⟨hq, ha⟩ := (hb hash).2.2 hsucc hp.2.1
    have hc : cost a ≤ cap := by rw [← hp.1]; exact hp.2.2
    dsimp only at ha
    exact ⟨hq, by omega⟩

theorem verify_good
    (hprefix : W9Fin.V7.PrefixGood GatePre)
    (fts : ∀ w : WB, FtsGoodByCost GatePre FtsOut ftsProgram (fun a => ovh + cost a) (P w))
    (after : AfterGoodBudget FtsOut afterProgram aG P)
    (hnone : ∀ pk w i, afterProgram pk w i none = pure false)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : WB) (s : MachineState)
    (hs : initialState submission .verify (m,pk,w) = some s) :
    GoodQP (Pre (P w) cost cap m w) s 10083 10084 True (aG+(ovh+cap)+11)
      (ccM (verifyP ftsProgram afterProgram m pk w) Kb) := by
  unfold verifyP
  rw [ccM_bind]
  exact hprefix m pk w s hs (Pre (P w) cost cap m w) (8050+2023) (8050+2023)
    (aG+(ovh+cap)) True
    (fun o => ccM (match o with
      | some a => afterDigest ftsProgram afterProgram pk w a
      | none => pure false) Kb)
    (by simp only [ccM_pure, Kb])
    (fun a u _ hu => afterDigest_good fts after hnone m pk w a u hu)

theorem verify_good_6997
    (hprefix : W9Fin.V7.PrefixGood GatePre)
    (fts : ∀ w : WB, FtsGoodByCost GatePre FtsOut ftsProgram (fun a => 869 + cost a) (P w))
    (after : AfterGoodBudget FtsOut afterProgram 5264 P)
    (hnone : ∀ pk w i, afterProgram pk w i none = pure false)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : WB) (s : MachineState)
    (hs : initialState submission .verify (m,pk,w) = some s) :
    GoodQP (Pre (P w) cost 777 m w) s 10083 10084 True 6921
      (ccM (verifyP ftsProgram afterProgram m pk w) Kb) :=
  verify_good hprefix fts after hnone m pk w s hs
end
end W9Fin.V7.Canonical


namespace W9Drv.SharedCoord
open W9Machine
/-- The installed shared FTS trace and its exact accepting cost, for any
honest-run predicate needed by the following WOTS layers. -/
theorem fts_good {P : SigGolfCandidate.Legacy.Hash → Prop} :
    FtsGoodByCost ftsAcceptCost (P := P) :=
  fts_good_of SharedGate.gCheck_linked SharedGate.gSetup_linked SharedDispatch.linked
    (fun k => N600.allGood_layout (P := P) (SharedLayout.layout k) rfl (fun _ => rfl))
    sharedChildGood
end W9Drv.SharedCoord

namespace W9Fin.V7.Canonical
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def installedFts (w : WB) (answer : HashOutput) : SigGolfCandidate.T3.M (Option (Digest × Digest)) :=
  if W9Drv.SharedGate.gateOk answer then W9Drv.SharedCoord.ftsN w answer else pure none

def installedOut (pk : Digest) (w : WB) (answer : HashOutput)
    (top : Digest × Digest) (state : MachineState) : Prop :=
  SigGolfCandidate.T3M.Verify.FtsOut ⟨pk, w, answer⟩ top state

theorem goodQP_frozen {P : Hash → Prop} {s : MachineState} {N C A : Nat} {Q : Prop}
    {X : OracleComp HashSpec Obs} :
    W9Machine.GoodQFor (P := P) W9Machine.Frozen.image s N C Q A X ↔ GoodQP P s N C Q A X := by
  rw [W9Machine.Frozen.image_eq]
  rfl

theorem fts_installed {P : Hash → Prop} :
    FtsGoodByCost W9Drv.SharedGate.Pre installedOut installedFts
      (fun answer => 869 + SigGolfCandidate.Research.SharedForest.jointAccountingCost answer) P := by
  intro pk w answer state N C A Q K hstate hnone hnext
  have h := W9Drv.SharedCoord.fts_good (P := P) pk w answer state N C A Q K hstate hnone
    (fun top next hnextState => goodQP_frozen.mpr (hnext top next hnextState))
  exact goodQP_frozen.mp h

theorem after_installed (floors : SigGolfCandidate.T3.Layer → Nat) (hcredit : CreditFloors floors) :
    AfterGoodBudget installedOut SigGolfCandidate.T3M.Verify.afterFts 5264
      (fun w => HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) :=
  fun pk w Q hQ answer top state hstate =>
    SigGolfCandidate.T3M.after_good_budget floors hcredit pk w Q hQ answer top state hstate

theorem installed_verify_good (floors : SigGolfCandidate.T3.Layer → Nat) (hcredit : CreditFloors floors)
    (message : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (witness : WB) (state : MachineState)
    (hstate : initialState submission .verify (message, pk, witness) = some state) :
    GoodQP (Pre (HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh witness))
      SigGolfCandidate.Research.SharedForest.jointAccountingCost 777 message witness)
      state 10083 10084 True 6921
      (ccM (verifyP installedFts SigGolfCandidate.T3M.Verify.afterFts message pk witness) Kb) :=
  verify_good_6997 (P := fun w => HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w)) W9Fin.V7.prefixGood
    (fun _ => fts_installed) (after_installed floors hcredit)
    (fun _ _ _ => rfl) message pk witness state hstate
end W9Fin.V7.Canonical


namespace W9Fin.V7.Canonical
open OracleComp SigGolfCandidate.T3

theorem paired_ftsStep_eq (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput)
    (state : Option (List (Digest × Digest))) (coord : Fin 9) :
    ClaudeWCT.W9.T3M.Paired.ftsStep w output state coord =
      W9Drv.SharedCoord.stepN w output state coord := by
  unfold ClaudeWCT.W9.T3M.Paired.ftsStep W9Drv.SharedCoord.stepN W9Drv.SharedCoord.coordN
  rw [show W9Machine.N600.embed = ClaudeWCT.WCT9.embed from W9Machine.N600.embed_eq_c1]
  rfl

theorem paired_ftsP_eq (w : ClaudeWCT.W9.T3M.WBytes) (output : HashOutput) :
    ClaudeWCT.W9.T3M.Paired.ftsP w output = installedFts w output := by
  unfold ClaudeWCT.W9.T3M.Paired.ftsP installedFts W9Drv.SharedGate.gateOk
  have hs : ClaudeWCT.W9.T3M.Paired.ftsStep w output = W9Drv.SharedCoord.stepN w output :=
    funext (fun state => funext (fun coord => paired_ftsStep_eq w output state coord))
  rw [hs]
  unfold W9Drv.SharedCoord.ftsN
  cases h : decide (output.toNat / 2^242 % 16384 < 791) <;>
    try simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rfl

theorem paired_verifyP_eq (message : SigGolfCandidate.Legacy.Message) (pk : Digest)
    (w : ClaudeWCT.W9.T3M.WBytes) :
    ClaudeWCT.W9.T3M.Paired.verifyP message pk w =
      verifyP installedFts SigGolfCandidate.T3M.Verify.afterFts message pk w := by
  unfold ClaudeWCT.W9.T3M.Paired.verifyP verifyP
  apply bind_congr
  intro output
  cases output with
  | none => rfl
  | some output =>
    dsimp only
    rw [paired_ftsP_eq]
    unfold afterDigest
    apply bind_congr
    intro pair
    cases pair <;> rfl

end W9Fin.V7.Canonical

namespace W9Fin.V7.Canonical.Runtime
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open ClaudeWCT.W9.T3M.Final.Paired (DigestCapOk VerifyRefines VerifyTerminates VerifyAcceptCycles)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev pairedSubmission := ClaudeWCT.W9.T3M.Paired.submission

def Inputs : Prop := ∀ (floors : SigGolfCandidate.T3.Layer→Nat), CreditFloors floors →
  ∀ (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22012) (s : MachineState),
  initialState SigGolfCandidate.T3M.submission .verify (m,pk,w)=some s →
  GoodQP (fun hash => HashOkBy floors (ClaudeWCT.W9.T3M.wtopHigh w) hash ∧ DigestCapOk hash m w) s 10083 10084 True 6921
    (ccM (ClaudeWCT.W9.T3M.Paired.verifyP m pk w) Kb)

theorem init_paired (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify=Images.verifyImage)
    (had : (pairedSubmission I).Admissible) (m : SigGolfCandidate.Legacy.Message)
    (pk : PublicKey) (w : Bytes 22012) :
    initialState (pairedSubmission I) .verify (m,pk,w)=
      initialState SigGolfCandidate.T3M.submission .verify (m,pk,w) := by
  unfold initialState
  rw [if_pos (had.2 .verify),if_pos (SigGolfCandidate.T3M.submission_admissible.2 .verify)]
  simp only [pairedSubmission,ClaudeWCT.W9.T3M.Paired.submission_verify,
    SigGolfCandidate.T3M.submission_verify,hI]
  rfl

theorem fixed_credit : CreditFloors (fun _ => 20) := by
  unfold CreditFloors
  constructor
  · intro lay;norm_num
  · decide

theorem verify_refines_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify=Images.verifyImage)
    (had : (pairedSubmission I).Admissible) (H : Inputs) : VerifyRefines I := by
  intro m pk w
  obtain ⟨s,hs⟩ := W9Fin.V7.init_exists m pk w
  have hs' := (init_paired I hI had m pk w).trans hs
  have hg := (H _ fixed_credit m pk w s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT; norm_num)).1
  rw [ccM_Kb] at hg
  rw [run_eq _ .verify _ s hs',ClaudeWCT.W9.T3M.Paired.submission_verify,hI,Functor.map_map]
  change _ = (fun p => (if p.1 then some () else none,p.2)) <$>
    countCalls (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP m pk w))
  rw [←hg,Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT Verify.image s) ?_
  funext e
  simp only [toRunResult,obs]
  by_cases h : e.exit=.success
  · simp only [h,decide_true,if_true];rfl
  · simp only [h,decide_false,if_false,Bool.false_eq_true];rfl

theorem verify_terminates_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify=Images.verifyImage)
    (had : (pairedSubmission I).Admissible) (H : Inputs) : VerifyTerminates I := by
  intro hash m pk w
  obtain ⟨s,hs⟩ := W9Fin.V7.init_exists m pk w
  have hs' := (init_paired I hI had m pk w).trans hs
  have hg := (H _ fixed_credit m pk w s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT; norm_num)).2 hash
  rw [runWith_eq _ hash .verify _ s hs',ClaudeWCT.W9.T3M.Paired.submission_verify,hI]
  simp only [toRunResult]
  refine ⟨?_,lt_of_le_of_lt hg.2.1 (by unfold CYCLE_LIMIT; norm_num)⟩
  simpa using hg.1

theorem verify_accept_cycles_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify=Images.verifyImage)
    (had : (pairedSubmission I).Admissible) (H : Inputs) : VerifyAcceptCycles I := by
  intro floors hcredit hash m pk w hok hcap h
  obtain ⟨s,hs⟩ := W9Fin.V7.init_exists m pk w
  have hs' := (init_paired I hI had m pk w).trans hs
  have hg := (H floors hcredit m pk w s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT; norm_num)).2 hash
  rw [runWith_eq _ hash .verify _ s hs',ClaudeWCT.W9.T3M.Paired.submission_verify,hI] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT Images.verifyImage s)).exit=.success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  exact (hg.2.2 hsucc ⟨hok,hcap⟩).2

theorem verify_inputs_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify=Images.verifyImage)
    (had : (pairedSubmission I).Admissible) (H : Inputs) :
    VerifyRefines I ∧ VerifyTerminates I ∧ VerifyAcceptCycles I :=
  ⟨verify_refines_of I hI had H,verify_terminates_of I hI had H,verify_accept_cycles_of I hI had H⟩
end W9Fin.V7.Canonical.Runtime

namespace W9Fin.V7.Canonical.Runtime
open SigGolfCandidate.Legacy SigGolfCandidate.T3M.Verify

theorem installed_inputs : Inputs := by
  intro floors hcredit message pk witness state hstate
  have h := W9Fin.V7.Canonical.installed_verify_good floors hcredit message pk witness state hstate
  rw [←W9Fin.V7.Canonical.paired_verifyP_eq] at h
  exact h

theorem installed_verify_inputs (I : ClaudeWCT.W9.T3M.Images)
    (hI : I.verify=SigGolfCandidate.T3M.Images.verifyImage)
    (had : (pairedSubmission I).Admissible) :
    ClaudeWCT.W9.T3M.Final.Paired.VerifyRefines I ∧
    ClaudeWCT.W9.T3M.Final.Paired.VerifyTerminates I ∧
    ClaudeWCT.W9.T3M.Final.Paired.VerifyAcceptCycles I :=
  verify_inputs_of I hI had installed_inputs
end W9Fin.V7.Canonical.Runtime
end
