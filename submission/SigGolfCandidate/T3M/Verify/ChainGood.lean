import SigGolfCandidate.T3M.Verify.ChainSem
import SigGolfCandidate.T3M.Verify.ChainCheckAll

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
      (hSlot i (c.dig i))) ∧
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
    vrun (c.startPc i) 7 = some (copyNB .x22 (offL i) (slotL i) (c.endPc i)) := by
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
      some (headRVB .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i) := by
  have hp := c.part_at i hi hnl hck (fun h => by have := h.1; omega)
  unfold partOK at hp
  simp only [partOK, Bool.false_eq_true, ite_false] at hp
  rw [if_neg (by omega), Bool.and_eq_true] at hp
  exact rOK_eq hp.1
theorem chk_copyF (c : LCtx) (i : Nat) (hi : i ≤ 42) (hnl : i % 3 ≠ 0 ∨ i = 42) (hck : i = 42 → c.ck < 8)
    (hd : c.dig i = 7) (hNS : ¬c.bufferSafe i) :
    vrun (c.startPc i) 4 = some (copyFHB .x22 (offL i) (slotL i) (c.startPc i)) := by
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
      (chainInputP c.lay c.tree c.leaf (i + c.koff) step (c.pad0 i) (c.pad1 i) (c.padHeader i) v)) v
theorem rest_succ (c : LCtx) (i m : Nat) (h : m ≤ 6) (v : Digest) :
    c.rest i m v =
      Verify.vHash (stepHigh i m) (chainInputP c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) (c.padHeader i) v) >>=
        c.rest i (m + 1) := by
  unfold rest
  rw [show 7 - m = (7 - (m + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]
theorem rest_7 (c : LCtx) (i : Nat) (v : Digest) : c.rest i 7 v = pure v := rfl
theorem chainInputP_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest) :
    pad64 (chainInputP lay tree leaf i step p0 p1 headerPad v) = chainInputP lay tree leaf i step p0 p1 headerPad v :=
  pad64_of_aligned _ (by rw [chainInputP_length])
theorem chainInputP_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest) :
    (toQ (chainInputP lay tree leaf i step p0 p1 headerPad v)).blocks = 1 := by
  rw [blocks_toQ ⟨by rw [chainInputP_length]; omega, by rw [chainInputP_length]⟩, chainInputP_length]
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
      rw [stepHigh_lt i m (by omega), Verify.vHalf_false]
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
      obtain ⟨t,ht,he⟩ := c.buffer_skip_jump h0 0 hi hSafe
        (c.startPc_lt 0 hi.2 hc.2.2.2.2.2.2.1 hRank) hr acc hs
      obtain ⟨u,hu,hn⟩ := c.end_next hc hk 0 hi hck _ _ he
      have H := Verify.GoodQP.stepsQ ht (Verify.GoodQP.stepsQ hu (hK _ _ hn)
        (le_refl _) (le_refl _) (fun h=>⟨h,le_refl _⟩))
        (show N+xCost 0+1≤N+40 by simp [xCost])
        (show C+xCost 0+1≤C+c.bufferCost 0 by simp [bufferCost,hSafe,chainCost,h7,zc,xCost])
        (fun h=>⟨h,show A+xCost 0+1≤A+c.bufferCost 0 by simp [bufferCost,hSafe,chainCost,h7,zc,xCost]⟩)
      exact H
    · have he := c.buffer_skip_inline h0 i hi hSafe (c.bufferSafe_pc i hi.2 hz hSafe) acc hs
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
    hD i hi, hD (i-1) (by omega), ne_eq, hlay, not_false_eq_true, true_and, if_false]
theorem bufferSlot_eq (c : LCtx) (hlay : c.lay ≠ 0) (i : Nat) :
    c.bufferSlot i = 0x520 + ClaudeWCT.W9.T3M.leafBufferSlot c.lay i := by
  unfold bufferSlot bufferOffset slotL ClaudeWCT.W9.T3M.leafBufferSlot
  rw [if_neg hlay]
  split_ifs <;> omega
theorem bufferVal_eq (c : LCtx) (hlay : c.lay ≠ 0) (D : List Nat)
    (hD : ∀ i < 43, c.dig i = D.getD i 0)
    (hS6 : c.S6 = 0x520 + ClaudeWCT.W9.T3M.chainBlock c.lay 42 + 1024)
    (i : Nat) (hi : i < 43) :
    c.bufferVal i = ClaudeWCT.W9.T3M.wvalueFor c.w c.lay D i := by
  have hn : chainCount c.lay = 43 := by
    have H : ∀ l : Layer, l ≠ 0 → chainCount l = 43 := by decide +kernel
    exact H c.lay hlay
  have hb : c.blk i - 0x520 = ClaudeWCT.W9.T3M.chainBlock c.lay i := by
    unfold blk ClaudeWCT.W9.T3M.chainBlock at *
    rw [hS6]; rw [hn] at *; simp only at *; omega
  unfold bufferVal ClaudeWCT.W9.T3M.wvalueFor
  simp only [c.bufferSafe_iff hlay D hD i hi]
  split_ifs
  · rw [c.bufferSlot_eq hlay i, Nat.add_sub_cancel_left]
  · simp only [val, ClaudeWCT.W9.T3M.wvalue, hb]
end LCtx
end SigGolfCandidate.T3M
