import SigGolfCandidate.Merge009
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge068
import SigGolfCandidate.Merge112
import SigGolfCandidate.Merge120

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
theorem chk_rung (c : LCtx) (i m : Nat) (hi : i ≤ 42) (hm : c.dig i ≤ m) (hm6 : m ≤ 6) (hm1 : 1 ≤ m)
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
    have e : triBase t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) + 2 + 2 * (m - 1) =
        triBase t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) + 2 * m := by omega
    rw [hr]
    rw [e] at this
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
  c.chk_rung i m hi (by omega) hm6 hm1 (fun _ => hm) hck
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
theorem startPc_lt (c : LCtx) (i : Nat) (hi : i ≤ 42) (hck : i = 42 → c.ck < 8) (hRank : c.headOK i) : c.startPc i < 257214 := by
  by_cases h42 : i=42
  · subst i; simp only [startPc, if_true]; rw [ckSlot_lt8 _ (hck rfl)]; omega
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
    (hm : m ≤ 6) (hck : i = 42 → c.ck < 8) : c.rungPc i m + landOff m < 257214 := by
  have hd6 : c.dig i<7 := by omega
  have he : c.endPc i<257214 := by
    by_cases h42 : i=42
    · subst i
      have hlen := partLen_le c.ck
      have hc8 := hck rfl
      simp only [endPc,if_true]
      rw [ckSlot_lt8 _ hc8]
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
    (hm : m ≤ 6) (hck : i = 42 → c.ck < 8) : c.rungPc i m < 257214 := by
  have := c.rungPc_land_lt i m hi hdm hm hck
  omega
def ChainNext (c : LCtx) (s0 : MachineState) (j : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  if j ≤ 42 then c.ChainIn s0 j acc s else c.ChainOut s0 43 acc s
/-- Exit dispatch cost of chain `i`. M0 (A0, P2c): chain 41's checksum dispatch is `slli a4,t4,11; jalr -720(a4)` (2). -/
def xCost (i : Nat) : Nat :=
  if i = 42 then 0 else if i % 3 = 2 then (if i = 2 ∨ i = 23 ∨ i = 41 then 2 else 3) else 0
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
  have hrc : ∀ m, c.dig i ≤ m → m ≤ 6 → c.rungPc i m < 257214 := fun m hd hm => c.rungPc_lt i m hi.2 hd hm hck
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
  have hsp := c.startPc_lt i hi.2 hck hRank
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
    have hrp := c.rungPc_lt i (c.dig i) hi.2 (le_refl _) (by omega) hck
    by_cases hl : i % 3 = 0 ∧ i ≠ 42
    · obtain ⟨h0', h42⟩ := hl
      have hruns := c.chk_headJ i (by omega) h0' hd hRank
      obtain ⟨t, hst, hP⟩ := c.headJ_step hc hk h0 i hi hd hsp
        (c.rungPc_land_lt i (c.dig i) hi.2 (le_refl _) (by omega) hck) hruns.1 hruns.2 acc s hs
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
        (c.startPc_lt 0 hi.2 hck hRank) hr acc hs
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
theorem cbase_sum43 : ((List.range' 0 43).map cbase).sum = 2934 := by decide +kernel
theorem cbase_sum_top : ((List.range' 33 9).map cbase).sum = 614 := by decide +kernel
def zSum (c : LCtx) (i k : Nat) : Nat := ((List.range' i k).map fun j => zc j (c.dig j)).sum
theorem chainsCost_lower (c : LCtx) (hck : c.ck < 8) (T : Nat) (hT : ((List.range' 0 43).map c.dig).sum = T) :
    c.chainsCost 0 42 + chainCost 42 c.ck + 9 * T + c.zSum 0 43 + 4*c.savedCopies 0 43 = 2934 := by
  have h := c.chainsCost_add hck 43 0 (le_refl _)
  rw [hT, cbase_sum43] at h
  have e : c.chainsCost 0 43 = c.chainsCost 0 42 + chainCost 42 c.ck := by
    unfold chainsCost
    rw [show (43 : Nat) = 42 + 1 from rfl, List.range'_concat, List.map_append, List.sum_append]
    simp [dig42,bufferCost_ck]
  unfold zSum
  omega
theorem chainsCost_top (c : LCtx) (hck : c.ck < 8) (S : Nat) (hS : ((List.range' 33 9).map c.dig).sum = S) :
    c.chainsCost 33 9 + 9 * S + c.zSum 33 9 + 4*c.savedCopies 33 9 = 614 := by
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
  | n + 1, msg => ClaudeWCT.W9.T3M.layersCanonicalBCW w index (n + 1) msg
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
        [.br (decide (lay = 3)), .jmp])
        (specBl lay (trPc lay c)) BC.oblB (postBlC lay (trPc lay c)) (keepB lay) = true) := by
  unfold BC.copyCheck BC.setupCheck at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, fun h0 => ?_⟩
  rw [if_neg h0] at h
  simp only [Bool.and_eq_true] at h
  tauto
theorem copy_parts_hi (lay c : Nat) (h : BC.copyCheck lay c = true) (h0 : lay ≠ 0) :
    specB [] [] baseK (runAt (BC.bKB lay c) [] (trPc lay c + stepsA lay + 1)
      [.br (decide (lay ≠ 3)), .br true, .jmp]) (specBlHi lay (trPc lay c)) BC.oblBHi
      (postBlC lay (trPc lay c)) (keepB lay) = true := by
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
-- M0 (A0, P2c): `ckBr_iff` removed (the lower heads have no window branch).
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
-- M0 (A0, P2c): `ckHiBr_iff` removed (the lower heads have no window branch).
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
    (h29 : s.getReg .x29 = 201#64 - BitVec.ofNat 64 (ckOf lay a)) :
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
    (∃ s0, Steps image (writeHash t a) (bSt lay.val) (bCy lay.val) s0 ∧
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
  have hS := lowSumS1_lt (ansD a)
  · have hs : lowerSpare (ansD a) := hsp
    obtain ⟨h6, h7⟩ := (spare_iff a).mp hs
    obtain ⟨s0, hs0⟩ := spec_run hB u hpcu hkuB (by
      intro b hb; simp only [specBl, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      exact (spareBr_iff hans lay.val false).mpr (by rw [decide_eq_false (not_not_intro hs)])) hobl
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
    have e29 : ((t4E lay.val).eval u) = 201#64 - BitVec.ofNat 64 (ckOf lay a) := by
      have hT : tgtL lay.val = 201 := by fin_cases lay <;> first | exact absurd rfl hlay | rfl
      apply BitVec.eq_of_toNat_eq
      simp only [t4E]
      rw [sumE_eval hans hs lay.val hm1 hm2, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      unfold ckOf; rw [hT]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, rfl,
        by simp [hL, lctxOf], tree_actual_lt index lay hidx, ?_, ?_, ?_⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v, Verify.WIT]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; unfold ckOf; omega
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
    (∃ s0, Steps image (writeHash t a) (bSt lay.val+4) (bCy lay.val+4) s0 ∧
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
  have hS := lowSumS1_lt (ansD b)
  · have hs : lowerSpare (ansD b) := hsp
    obtain ⟨h6, h7⟩ := (spare_iff b).mp hs
    obtain ⟨s0, hs0⟩ := spec_run hB u hpcu hkuB (by
      intro b hb; simp only [specBlHi, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
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
    have e29 : ((t4HiE lay.val).eval u) = 201#64 - BitVec.ofNat 64 (ckOf lay b) := by
      have hT : tgtL lay.val = 201 := by fin_cases lay <;> first | exact absurd rfl hlay | rfl
      apply BitVec.eq_of_toNat_eq
      simp only [t4HiE]
      rw [sumHiE_eval hans hs lay.val hm1 hm2, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      unfold ckOf; rw [hT]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, rfl,
        by simp [hL, lctxOf], tree_actual_lt index lay hidx, ?_, ?_, ?_⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v, Verify.WIT]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; unfold ckOf; omega
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
    (ClaudeWCT.W9.T3M.lowerDataDecode (ansD (selectedView a)) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        (fetch image v = none ∨ (fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1)) ∧ k ≤ 27 ∧ cy ≤ 30) ∧
    (ClaudeWCT.W9.T3M.lowerDataDecode (ansD (selectedView a)) ≠ none → ∃ s0 k cy, Steps image (writeHash t a) k cy s0 ∧ k ≤ bSt lay.val+4 ∧
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
      simp [ClaudeWCT.W9.T3M.lowerDataDecode, hlo] at hn
    · intro _
      obtain ⟨s0,hst,hrest⟩ := H
      exact ⟨s0,bSt lay.val,bCy lay.val,hst,by omega,by simp [hlo],hrest⟩
  · simp only [selectedView, if_neg hlo]
    by_cases hhi : lowerSpare (ansD (highView a))
    · have H := encB_step_hi w pk index lay hlay c hc hidx t ht a hlo hhi
      constructor
      · intro hn
        simp [ClaudeWCT.W9.T3M.lowerDataDecode, hhi] at hn
      · intro _
        obtain ⟨s0,hst,hrest⟩ := H
        exact ⟨s0,bSt lay.val+4,bCy lay.val+4,hst,le_refl _,by simp [hlo],hrest⟩
    · constructor
      · intro _
        obtain ⟨v,hst,hf⟩ := encB_step_trap w pk index lay hlay c hc t ht a hlo hhi
        exact ⟨v,8,8,hst,Or.inl hf,by omega,by omega⟩
      · intro hn
        exact (hn (by simp [ClaudeWCT.W9.T3M.lowerDataDecode, hhi])).elim

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
