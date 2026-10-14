import SigGolfCandidate.T3M.Verify.DirectMerkleChecks
import SigGolfCandidate.T3M.Verify.LayerLower
import SigGolfCandidate.T3M.Verify.Arith

variable {choiceHint : BitVec 64}

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
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
theorem mkBase_ge (lay : Nat) (hlay : lay < 4) : 8256 ≤ mkBase lay ∧ mkBase lay % 16 = 0 := by
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
/-- C4: every line-A row places window 5 at slot 25 (the upper copies start from it). -/
theorem mkPlan_top5 (x : Nat) : plan 0 x 5 = 25 := by
  have h : (List.range 64).all (fun r => (topPlanA.getD r []).getD 5 0 == 25) = true := by decide +kernel
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
    mkBo lay leaf k % 16 = 0 ∧ 8256 ≤ mkBo lay leaf k ∧ mkBo lay leaf k + 80 ≤ 19200 ∧ mkBase lay ≤ mkBo lay leaf k ∧
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
  (8256 ≤ o ∧ o < mkBase lay) ∨ (mkBase lay ≤ o ∧ (o - mkBase lay) / 16 ∈ mkKS lay leaf k) ∨
    (mkBase lay ≤ o ∧ (o - mkBase lay) % 16 = 8 ∧ (o - mkBase lay) / 16 ∈ mkKH lay leaf k)
/-- C4: the top uses the plan predicate of the lower layers (its region below, `[8256, mkBase 0)`, is empty). -/
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
      (0x4c0 + o + 8 ≤ mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) ∨
        mkCur lay leaf (k + 1) (leaf / 2 ^ (k + 1) % 2) + 32 ≤ 0x4c0 + o) := by
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
    · have h0 : lay ≠ 0 := by intro h; subst h; have : mkBase 0 = 8256 := rfl; omega
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
    (8256 ≤ o ∧ o < mkBase lay + 16 * mkPS lay) ∧
      (0x4c0 + o + 8 ≤ mkCur lay leaf 0 (leaf / 2 ^ 0 % 2) ∨ mkCur lay leaf 0 (leaf / 2 ^ 0 % 2) + 32 ≤ 0x4c0 + o) := by
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
    · have h0 : lay ≠ 0 := by intro h; subst h; have : mkBase 0 = 8256 := rfl; omega
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
  glob : Glob baseK w pk s
  known : KnownOK (mkLvlK lay k) s
  keep : ∀ r ∈ mkKeep, s.getReg r = u.getReg r
  /-- The level-`k` input sits at its value slot (C2: a lower left node was written 16 bytes low). -/
  node : DigAt s (mkVal lay leaf k (leaf / 2 ^ k % 2)) v
  orig : Orig w (mkP lay leaf k (leaf / 2 ^ k % 2)) s
  dstReg : s.getReg .x12 = BitVec.ofNat 64 (mkCur lay leaf k (leaf / 2 ^ k % 2))
  x28 : k ≠ 0 → lay ≠ 0 → s.getReg .x28 = T3.hyperWord (lay - 1) (u.getReg .x31).toNat
  bufferOrig : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24896) s
structure MkEnd (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (root : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf (mkFin lay leaf + 1)
  glob : Glob baseK w pk t
  known : KnownOK (mkKc lay ++ [(.x11, 64)]) t
  keep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r
  root : DigAt t (mkDst lay leaf) root
  orig : Orig w (fun o => 8256 ≤ o ∧ o < mkBase lay) t
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
    p ∈ mkKc lay ∨ p = (.x9, BitVec.ofNat 64 TOPB9) := by
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
    (ho : BC.bufferStart (lay-1) ≤ o ∧ o < 24896) : 21776 ≤ o := by
  interval_cases lay <;> simp [BC.bufferStart] at ho <;> omega

theorem mk_buffer_writeHash {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState}
    (lay : Nat) (hlay : lay < 4)
    (hO : Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24896) s)
    (a : BitVec 256) (d : Nat) (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d + 32 ≤ WIT + 21776) :
    Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24896) (writeHash s a) := by
  apply (Orig_writeHash hO a d h12 (by unfold WIT at hd; omega)).mono
  intro o ho
  exact ⟨ho, Or.inr (by have := mk_buffer_ge lay o hlay ho; omega)⟩

theorem lvl_bufferOrig {w : ClaudeWCT.W9.T3M.WBytes} (lay : Layer) (leaf k : Nat)
    (hleaf : leaf < 2 ^ hL lay.val) (hk : k < hL lay.val) (s t : MachineState)
    (hO : lay.val ≠ 0 → Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 24896) s)
    (hmem : ∀ A, t.getMem A =
      memEval s (mkLvlMem lay.val (mkCi lay.val k) (mkSh lay.val (mkCi lay.val k) leaf) k) A) :
    lay.val ≠ 0 → Orig w (fun o => BC.bufferStart (lay.val-1) ≤ o ∧ o < 24896) t := by
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
    WLO ≤ mkCur lay leaf j b ∧ mkCur lay leaf j b % 8 = 0 ∧ mkCur lay leaf j b + 32 ≤ 0x4c0 + 19200 := by
  obtain ⟨hB16, hBlo, hBhi, -, -⟩ := mkBo_facts lay leaf j hlay hleaf hj
  unfold mkCur mkVal mkBlk WLO WIT
  omega
theorem lvl_after (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (lay leaf : Nat) (u : MachineState) (hlay : lay < 4)
    (hleaf : leaf < 2 ^ hL lay) (k : Nat) (hk : k < hL lay) (t : MachineState)
    (hglob : Glob baseK w pk t) (hknown : KnownOK (mkKc lay ++ [(.x11, 64)]) t)
    (hkeep : ∀ r ∈ mkKeep, t.getReg r = u.getReg r)
    (h28 : lay ≠ 0 → t.getReg .x28 = T3.hyperWord (lay - 1) (u.getReg .x31).toNat)
    (horig : Orig w (fun o => mkP lay leaf k (leaf / 2 ^ k % 2) o ∧ o ≠ mkBo lay leaf k + 16 ∧
      o ≠ mkBo lay leaf k + 24) t)
    (hbuffer : lay ≠ 0 → Orig w (fun o => BC.bufferStart (lay-1) ≤ o ∧ o < 24896) t)
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
    simp only [mkK, if_pos, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    repeat' first | subst p | rcases hp with hp | hp
    all_goals simp [lfK, postLf, leafK, lfKeepK, baseK]
  · simp only [mkK, h0, if_false, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    repeat' first | subst p | rcases hp with hp | hp
    all_goals simp [lfK, postLf, leafK, lfKeepK, h0, baseK]
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
    have hglob : Glob baseK w pk t := ht.glob _ _ _ (ht1.glob _ _ _ hs.glob (RelOK.nil s)) (RelOK.nil t1)
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
    have hglob : Glob baseK w pk t := ht.glob _ _ _ hs.glob (RelOK.nil s)
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
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → GoodQ (choiceHint := choiceHint) t N C Q A (K root)) :
    ∀ n k v s, k + n = mkStop lay.val → k < hL lay.val → MAfter w pk lay.val (route index lay).1 u k v s →
      GoodQ (choiceHint := choiceHint) s (N + mkFuelR lay.val k n) (C + mkCycR lay.val k n) Q (A + mkCycR lay.val k n)
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
    have H : ∀ a : BitVec 256, GoodQ (choiceHint := choiceHint) (writeHash t a) (N + mkFuelR lay.val (k + 1) m) (C + mkCycR lay.val (k + 1) m) Q
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
    have hg := GoodQ.vHash_bind _ (f := fun v' => (List.range' (k + 1) m).foldlM (mkStep w index lay) v') hf h5 hv hin H
    rw [mkIn_blocks] at hg
    simp only [mkFuelR, mkCycR]
    exact GoodQ.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
def merklePrefix (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (value : Digest) : T3.M Digest :=
  (List.range (mkStop lay.val)).foldlM (mkStep w index lay) value
def mkFuel (lay : Nat) : Nat := 2 + mkFuelR lay 0 (mkStop lay)
def mkCyc (lay : Nat) : Nat := 1 + 8 * lfBlocks lay + mkCycR lay 0 (mkStop lay)
/-- C4: the top path is 12 instructions shorter (one label store per fold): 268 -> 256 cycles, 73 -> 61 fuel. -/
theorem mkCyc_vals : mkCyc 0 = 256 ∧ mkCyc 1 = 165 ∧ mkCyc 2 = 153 ∧ mkCyc 3 = 153 := by decide +kernel
theorem mkFuel_vals : mkFuel 0 = 61 ∧ mkFuel 1 = 36 ∧ mkFuel 2 = 31 ∧ mkFuel 3 = 31 := by decide +kernel
theorem mkBits_stabBits (lay : Nat) (hlay : lay < 4) : mkBits lay 0 = stabBits lay := by
  interval_cases lay <;> decide +kernel
theorem merkle_good (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (ends : List Digest) (u : MachineState)
    (hidx : index < 2 ^ 31) (hu : LeafOut w pk index lay ends u)
    (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ root t, MkStop w pk lay.val (route index lay).1 u root t → GoodQ (choiceHint := choiceHint) t N C Q A (K root)) :
    GoodQ (choiceHint := choiceHint) u (N + mkFuel lay.val) (C + mkCyc lay.val) Q (A + mkCyc lay.val)
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
    hkU (.x11, BitVec.ofNat 64 (if lay.val = 0 then 896 else 704)) (by simp [lfK, postLf])
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
  have hG : Glob baseK w pk t := ht.glob _ _ _ hu.glob (RelOK.nil u)
  have H : ∀ a : BitVec 256, GoodQ (choiceHint := choiceHint) (writeHash t a) (N + mkFuelR lay.val 0 (mkStop lay.val))
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
      · have hO : Orig w (fun o => 8256 ≤ o ∧
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
  have hg := GoodQ.vHash_bind _ (f := merklePrefix w index lay) (K := K) (ht.ecall rfl) h5 hv hin H
  rw [hu.hashInput.2] at hg
  rw [show ClaudeWCT.WCT9.leafHashW lay (route index lay).2 (route index lay).1 (ClaudeWCT.W9.T3M.wtopLeafPad w)
      (ClaudeWCT.W9.T3M.wleafHigh w lay) ends = Verify.vHash (ClaudeWCT.WCT9.lowerHigh lay.val (route index lay).1)
        (lfIn w lay (route index lay).2 (route index lay).1 ends) from (LCtx.vHash_eq_halfHash _ _).symm]
  have hst := ht.steps
  simp only [BC.mkEntSpec, Nat.reduceEqDiff, and_false, if_false] at hst
  exact GoodQ.steps' hst hg (by unfold mkFuel; omega) (by unfold mkCyc; omega) (fun q => ⟨q, by unfold mkCyc; omega⟩)
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
  change ClaudeWCT.W9.T3M.layersBC w index (n + 1) msg = _
  rw [ClaudeWCT.W9.T3M.layersBC, layerHead]
  dsimp only
  simp only [hn0, ↓reduceIte]
  have hl : (Fin.ofNat 4 n : Layer) ≠ 0 := by
    intro he
    apply hn0
    simpa [Fin.val_ofNat, Nat.mod_eq_of_lt hn] using congrArg Fin.val he
  rw [ClaudeWCT.WCT9.verificationHash_lower _ hl]
  split_ifs with hc
  · rfl
  · congr 1
    funext answer
    cases T3.decode (Fin.ofNat 4 n) answer with
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
      ClaudeWCT.WCT9.verificationHash 0 (ClaudeWCT.W9.T3M.wtopHint w) (ClaudeWCT.W9.T3M.layerEncodingInputP 0 (route index 0).2 (route index 0).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w index 0) (ClaudeWCT.W9.T3M.wbcPad w index 0) (ClaudeWCT.W9.T3M.wbcRight w)
        (ClaudeWCT.W9.T3M.wbcHigh w index 0)) >>=
        ClaudeWCT.W9.T3M.topLayerP w index := by
  change ClaudeWCT.W9.T3M.layersBC w index 1 msg = _
  rw [ClaudeWCT.W9.T3M.layersBC]
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
