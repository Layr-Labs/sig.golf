import SigGolfCandidate.T3M.Verify.DirectMerkleChecks

/-! Campaign S1 Merkle window plans.

Window `j` of a path (witness offset `mkBo`) holds the left input (bytes 0..16), the one-word label (16..24, written
by the fold's code), the witness high word (24..32), the pad (32..48) and the right input (48..64). The fold of
window `j` still needs the sibling, the high word and the pad (`mkNeedW`) when it runs. Writes: the label of every
fold, and the 32-byte hash write of every node: a left node (bit 0) is the HIGH half of its answer, written 16 bytes
below its slot, a right node is written at its slot (`mkWo`). `route_facts`: no write hits a word a later fold
needs, writes stay above the layers below (`mkBase`), windows lie inside the path area. Lower layers are checked leaf
by leaf; the top path line by line (line A: levels 0..5 by `leaf % 64`, line B: levels 6..11 by `leaf / 64 % 64`),
every line-A write lying above every line-B word. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

def mkCi (lay k : Nat) : Nat := if lay = 0 ∧ 6 ≤ k then 1 else 0
def mkSh (lay ci leaf : Nat) : Nat := leaf / 2 ^ mkLo lay ci % 2 ^ mkBits lay ci
theorem mkBlk_bit (E b n k : Nat) (hk : k < n) : E / 2 ^ b % 2 ^ n / 2 ^ k % 2 = E / 2 ^ (b + k) % 2 := by
  have h1 : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), Nat.div_div_eq_div_mul,
    ← Nat.pow_add]
theorem mkSh_bit (lay ci leaf kk : Nat) (hkk : kk < mkBits lay ci) :
    mkSh lay ci leaf / 2 ^ kk % 2 = leaf / 2 ^ (mkLo lay ci + kk) % 2 := mkBlk_bit _ _ _ _ hkk
theorem mkSh_lt (lay ci leaf : Nat) : mkSh lay ci leaf < 2 ^ mkBits lay ci := Nat.mod_lt _ (Nat.two_pow_pos _)
theorem mkBit_lt (x k : Nat) : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide +kernel)
theorem mkBit_lt' (x k : Nat) : mkBit x k < 2 := mkBit_lt x k
theorem mkLeafOf_bit (lay ci leaf k : Nat) (hk1 : mkLo lay ci ≤ k) (hk2 : k - mkLo lay ci < mkBits lay ci) :
    mkBit (mkLeafOf lay ci (mkSh lay ci leaf)) k = mkBit leaf k := by
  unfold mkBit mkLeafOf
  have e : 2 ^ k = 2 ^ mkLo lay ci * 2 ^ (k - mkLo lay ci) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _), mkSh_bit _ _ _ _ hk2,
    show mkLo lay ci + (k - mkLo lay ci) = k by omega, ← e]
theorem mkBo_top (leaf k : Nat) : mkBo 0 leaf k = 8256 + ClaudeWCT.W9.T3M.topPlan leaf k := by
  unfold mkBo mkPath; rw [if_pos rfl]; rfl
theorem mkBo_low (lay leaf k : Nat) (h0 : lay ≠ 0) : mkBo lay leaf k = mkBase lay + 16 * plan lay leaf k := by
  unfold mkBo mkPath; rw [if_neg h0]
/-- The chunk's representative leaf has the window plan of `leaf` on the chunk's levels. -/
theorem mkLeafOf_bo (lay ci leaf k : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) (hci : ci < mkNch lay)
    (hk1 : mkLo lay ci ≤ k) (hk2 : k - mkLo lay ci < mkBits lay ci) :
    mkBo lay (mkLeafOf lay ci (mkSh lay ci leaf)) k = mkBo lay leaf k := by
  by_cases h0 : lay = 0
  · subst h0
    have hl : leaf < 4096 := by simpa [hL] using hleaf
    have hci' : ci < 2 := by simpa [mkNch] using hci
    rw [mkBo_top, mkBo_top]
    congr 1
    unfold ClaudeWCT.W9.T3M.topPlan
    interval_cases ci
    · have hk : k < 6 := by simpa [mkLo, mkBits] using hk2
      have hs : mkLeafOf 0 0 (mkSh 0 0 leaf) = leaf % 64 := by simp [mkLeafOf, mkSh, mkLo, mkBits]
      rw [hs, if_pos hk, if_pos hk, Nat.mod_mod]
    · have hk : 6 ≤ k := by simpa [mkLo] using hk1
      have hs : mkLeafOf 0 1 (mkSh 0 1 leaf) = leaf / 64 % 64 * 64 := by simp [mkLeafOf, mkSh, mkLo, mkBits]
      rw [hs, if_neg (show ¬ k < 6 by omega), if_neg (show ¬ k < 6 by omega),
        Nat.mul_div_cancel _ (by norm_num : 0 < 64), Nat.mod_mod]
  · have hc : ci = 0 := by simp [mkNch, h0] at hci; omega
    subst hc
    have hs : mkSh lay 0 leaf = leaf := by
      simp only [mkSh, mkLo, mkBits, h0, false_and, if_false, Nat.pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt hleaf
    simp [mkLeafOf, mkLo, hs, h0]
def mkPS (lay : Nat) : Nat := [49,23,20,20].getD lay 0
theorem mkBase_ge (lay : Nat) (hlay : lay < 4) : 8256 ≤ mkBase lay ∧ mkBase lay % 16 = 0 := by
  interval_cases lay <;> decide +kernel
/-- Witness offset of the 32-byte hash write of the level-`l` node (left: 16 below its slot). -/
def mkWo (lay leaf l : Nat) : Nat := mkBo lay leaf l + 64 * mkBit leaf l - 16
/-- Witness offset of the sibling of the level-`l` node. -/
def mkSibO (lay leaf l : Nat) : Nat := mkBo lay leaf l + 48 * (1 - mkBit leaf l)
/-- The witness words the fold of window `j` reads: sibling, high word, pad. -/
def mkNeedW (lay leaf j : Nat) : List Nat :=
  [mkSibO lay leaf j, mkSibO lay leaf j + 8, mkBo lay leaf j + 24, mkBo lay leaf j + 32, mkBo lay leaf j + 40]
def mkDis (x o : Nat) : Bool := decide (o + 8 ≤ x ∨ x + 32 ≤ o)
def mkWrOk (lay leaf k j : Nat) : Bool :=
  (mkNeedW lay leaf j).all fun o => o != mkBo lay leaf k + 16 && mkDis (mkWo lay leaf (k + 1)) o
def mkLvlOk (lay leaf j : Nat) : Bool :=
  decide (mkPath lay leaf j % 16 = 0 ∧ mkPath lay leaf j + 64 ≤ 16 * mkPS lay) &&
    (lay == 0 || decide (mkBase lay ≤ mkWo lay leaf j)) && (mkNeedW lay leaf j).all (mkDis (mkWo lay leaf 0))
def mkRouteOk (lay leaf : Nat) : Bool :=
  (List.range (hL lay)).all (mkLvlOk lay leaf) &&
    (List.range (hL lay - 1)).all fun k => (List.range' (k + 1) (hL lay - k - 1)).all (mkWrOk lay leaf k)
def mkLowOk (lay lo n : Nat) : Bool := (List.range' lo n).all (mkRouteOk lay)
theorem mkLowOk_1a : mkLowOk 1 0 64 = true := by decide +kernel
theorem mkLowOk_1b : mkLowOk 1 64 64 = true := by decide +kernel
theorem mkLowOk_2 : mkLowOk 2 0 64 = true := by decide +kernel
theorem mkLowOk_3 : mkLowOk 3 0 64 = true := by decide +kernel
/-- Line-A writes start at region offset 400, line-B words end at 384. -/
def mkSplit : Nat := 8256 + 384
def mkTopA (sh : Nat) : Bool :=
  (List.range 6).all (mkLvlOk 0 (mkLeafOf 0 0 sh)) &&
    ((List.range 5).all fun k => (List.range' (k + 1) (5 - k)).all (mkWrOk 0 (mkLeafOf 0 0 sh) k)) &&
    (List.range 6).all fun k => decide (mkSplit ≤ mkBo 0 (mkLeafOf 0 0 sh) k + 16 ∧ mkSplit ≤ mkWo 0 (mkLeafOf 0 0 sh) k)
def mkTopB (sh : Nat) : Bool :=
  ((List.range' 6 6).all fun j => decide (mkPath 0 (mkLeafOf 0 1 sh) j % 16 = 0 ∧
      mkPath 0 (mkLeafOf 0 1 sh) j + 64 ≤ 16 * mkPS 0) &&
    (mkNeedW 0 (mkLeafOf 0 1 sh) j).all fun o => decide (o + 8 ≤ mkSplit)) &&
  (List.range' 5 6).all fun k => (List.range' (k + 1) (11 - k)).all fun j =>
    (mkNeedW 0 (mkLeafOf 0 1 sh) j).all fun o =>
      (k == 5 || o != mkBo 0 (mkLeafOf 0 1 sh) k + 16) && mkDis (mkWo 0 (mkLeafOf 0 1 sh) (k + 1)) o
theorem mkTopA_all : (List.range 64).all mkTopA = true := by decide +kernel
theorem mkTopB_all : (List.range 64).all mkTopB = true := by decide +kernel

/-- Facts of a checked route. -/
def RouteF (lay leaf : Nat) : Prop :=
  (∀ j < hL lay, mkPath lay leaf j % 16 = 0 ∧ mkPath lay leaf j + 64 ≤ 16 * mkPS lay) ∧
  (lay ≠ 0 → ∀ j < hL lay, mkBase lay ≤ mkWo lay leaf j) ∧
  (∀ j < hL lay, ∀ o ∈ mkNeedW lay leaf j, mkDis (mkWo lay leaf 0) o = true) ∧
  (∀ k j, k < j → j < hL lay → ∀ o ∈ mkNeedW lay leaf j,
    o ≠ mkBo lay leaf k + 16 ∧ mkDis (mkWo lay leaf (k + 1)) o = true)
theorem routeF_of (lay leaf : Nat) (h : mkRouteOk lay leaf = true) : RouteF lay leaf := by
  simp only [mkRouteOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_range'_1] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj => ?_, fun h0 j hj => ?_, fun j hj o ho => ?_, fun k j hkj hj o ho => ?_⟩
  · have := h1 j hj
    simp only [mkLvlOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  · have := h1 j hj
    simp only [mkLvlOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, h0, false_or] at this
    exact this.1.2
  · have := h1 j hj
    simp only [mkLvlOk, Bool.and_eq_true, List.all_eq_true] at this
    exact this.2 o ho
  · have := h2 k (by omega) j ⟨by omega, by omega⟩
    simp only [mkWrOk, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this o ho
theorem mkNeedW_congr {lay leaf leaf' j : Nat} (hb : mkBo lay leaf' j = mkBo lay leaf j)
    (hc : mkBit leaf' j = mkBit leaf j) : mkNeedW lay leaf' j = mkNeedW lay leaf j := by
  unfold mkNeedW mkSibO; rw [hb, hc]
theorem mkWo_congr {lay leaf leaf' j : Nat} (hb : mkBo lay leaf' j = mkBo lay leaf j)
    (hc : mkBit leaf' j = mkBit leaf j) : mkWo lay leaf' j = mkWo lay leaf j := by
  unfold mkWo; rw [hb, hc]
theorem mkPath_congr {lay leaf leaf' j : Nat} (hb : mkBo lay leaf' j = mkBo lay leaf j) :
    mkPath lay leaf' j = mkPath lay leaf j := by
  unfold mkBo at hb; omega
theorem routeF_top (leaf : Nat) (hleaf : leaf < 4096) : RouteF 0 leaf := by
  have hl : leaf < 2 ^ hL 0 := hleaf
  have hA := List.all_eq_true.mp mkTopA_all (mkSh 0 0 leaf) (List.mem_range.mpr (mkSh_lt 0 0 leaf))
  have hB := List.all_eq_true.mp mkTopB_all (mkSh 0 1 leaf) (List.mem_range.mpr (mkSh_lt 0 1 leaf))
  -- lifts
  have eA : ∀ j < 6, mkBo 0 (mkLeafOf 0 0 (mkSh 0 0 leaf)) j = mkBo 0 leaf j ∧
      mkBit (mkLeafOf 0 0 (mkSh 0 0 leaf)) j = mkBit leaf j := fun j hj =>
    ⟨mkLeafOf_bo 0 0 leaf j (by decide) hl (by decide) (by simp [mkLo]) (by simp [mkLo, mkBits]; omega),
      mkLeafOf_bit 0 0 leaf j (by simp [mkLo]) (by simp [mkLo, mkBits]; omega)⟩
  have eB : ∀ j, 6 ≤ j → j < 12 → mkBo 0 (mkLeafOf 0 1 (mkSh 0 1 leaf)) j = mkBo 0 leaf j ∧
      mkBit (mkLeafOf 0 1 (mkSh 0 1 leaf)) j = mkBit leaf j := fun j hj1 hj2 =>
    ⟨mkLeafOf_bo 0 1 leaf j (by decide) hl (by decide) (by simp [mkLo]; omega) (by simp [mkLo, mkBits]; omega),
      mkLeafOf_bit 0 1 leaf j (by simp [mkLo]; omega) (by simp [mkLo, mkBits]; omega)⟩
  simp only [mkTopA, mkTopB, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_range'_1,
    decide_eq_true_eq] at hA hB
  obtain ⟨⟨hA1, hA2⟩, hA3⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  -- line A writes are high, line B words low
  have wA : ∀ k < 6, mkSplit ≤ mkBo 0 leaf k + 16 ∧ mkSplit ≤ mkWo 0 leaf k := by
    intro k hk
    have := hA3 k hk
    rw [(eA k hk).1, mkWo_congr (eA k hk).1 (eA k hk).2] at this
    exact this
  have nB : ∀ j, 6 ≤ j → j < 12 → ∀ o ∈ mkNeedW 0 leaf j, o + 8 ≤ mkSplit := by
    intro j hj1 hj2 o ho
    have := (hB1 j ⟨hj1, by omega⟩).2
    rw [mkNeedW_congr (eB j hj1 hj2).1 (eB j hj1 hj2).2] at this
    exact this o ho
  have lvA : ∀ j < 6, mkLvlOk 0 leaf j = true := by
    intro j hj
    have := hA1 j hj
    unfold mkLvlOk at this ⊢
    rw [mkPath_congr (eA j hj).1, mkWo_congr (eA j hj).1 (eA j hj).2, mkNeedW_congr (eA j hj).1 (eA j hj).2,
      mkWo_congr (eA 0 (by omega)).1 (eA 0 (by omega)).2] at this
    exact this
  refine ⟨fun j hj => ?_, fun h0 => absurd rfl h0, fun j hj o ho => ?_, fun k j hkj hj o ho => ?_⟩
  · change j < 12 at hj
    by_cases hj6 : j < 6
    · have := lvA j hj6
      simp only [mkLvlOk, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1
    · have := (hB1 j ⟨by omega, by omega⟩).1
      rw [mkPath_congr (eB j (by omega) hj).1] at this
      exact this
  · change j < 12 at hj
    by_cases hj6 : j < 6
    · have := lvA j hj6
      simp only [mkLvlOk, Bool.and_eq_true, List.all_eq_true] at this
      exact this.2 o ho
    · have h1 := nB j (by omega) hj o ho
      have h2 := (wA 0 (by omega)).2
      simp only [mkDis, decide_eq_true_eq]; omega
  · change j < 12 at hj
    by_cases hj6 : j < 6
    · have := hA2 k (by omega) j ⟨by omega, by omega⟩
      simp only [mkWrOk, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
      rw [mkNeedW_congr (eA j hj6).1 (eA j hj6).2, (eA k (by omega)).1,
        mkWo_congr (eA (k + 1) (by omega)).1 (eA (k + 1) (by omega)).2] at this
      exact this o ho
    · have h1 := nB j (by omega) hj o ho
      by_cases hk5 : k < 5
      · have h2 := wA k (by omega)
        have h3 := wA (k + 1) (by omega)
        refine ⟨by omega, ?_⟩
        simp only [mkDis, decide_eq_true_eq]; omega
      · have := hB2 k ⟨by omega, by omega⟩ j ⟨by omega, by omega⟩
        rw [mkNeedW_congr (eB j (by omega) hj).1 (eB j (by omega) hj).2,
          mkWo_congr (eB (k + 1) (by omega) (by omega)).1 (eB (k + 1) (by omega) (by omega)).2] at this
        have hh := this o ho
        simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hh
        refine ⟨?_, hh.2⟩
        by_cases hk : k = 5
        · subst hk; have h2 := wA 5 (by omega); omega
        · have := hh.1.resolve_left hk
          rwa [(eB k (by omega) (by omega)).1] at this
theorem route_facts (lay leaf : Nat) (hlay : lay < 4) (hleaf : leaf < 2 ^ hL lay) : RouteF lay leaf := by
  have hall : ∀ l lo n, mkLowOk l lo n = true → lo ≤ leaf → leaf < lo + n → RouteF l leaf :=
    fun l lo n h h1 h2 => routeF_of l leaf (List.all_eq_true.mp h leaf (List.mem_range'_1.mpr ⟨h1, h2⟩))
  interval_cases lay
  · exact routeF_top leaf hleaf
  · have : leaf < 128 := hleaf
    by_cases h64 : leaf < 64
    · exact hall 1 0 64 mkLowOk_1a (by omega) (by omega)
    · exact hall 1 64 64 mkLowOk_1b (by omega) (by omega)
  · exact hall 2 0 64 mkLowOk_2 (by omega) hleaf
  · exact hall 3 0 64 mkLowOk_3 (by omega) hleaf
theorem mkTop5_all : (List.range 64).all (fun sh => mkWo 0 (mkLeafOf 0 0 sh) 5 == 8704) = true := by decide +kernel
/-- Line A always writes node 5 at region offset 448 (the second half's base `mkP5`). -/
theorem mkWo_top5 (leaf : Nat) (hleaf : leaf < 4096) : mkWo 0 leaf 5 = 8704 := by
  have h := List.all_eq_true.mp mkTop5_all (mkSh 0 0 leaf) (List.mem_range.mpr (mkSh_lt 0 0 leaf))
  have hb := mkLeafOf_bo 0 0 leaf 5 (by decide) (show leaf < 2 ^ hL 0 from hleaf) (by decide) (by simp [mkLo])
    (by simp [mkLo, mkBits])
  have hc := mkLeafOf_bit 0 0 leaf 5 (by simp [mkLo]) (by simp [mkLo, mkBits])
  rw [mkWo_congr hb hc] at h
  simpa using h
end SigGolfCandidate.T3M
