import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactRun
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Wit
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ComposeBack
import SigGolfCandidate.ClaudeWCT.W9.T3M.Submission
import SigGolfCandidate.T3M.Submission

section



namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap_const window_full zeros wordsOf)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (headerBytes regionBytes merkleBytes authSibOff authByte headerBytes_length
  regionBytes_length merkleBytes_length region_merkle merkleBytes_sib authByte_none window_map_range)
open ClaudeWCT.W9.Machine.Expand (witListV6 wctBytesV6 wctBytesV6_length witListV6_length witListV5 wctBytesV5 regionBytesV5 merkleBytesV5 merkleBytesV5_length regionBytesV6 regionBytesV6_length
  regionBytesV5_length wctBytesV5_length witListV5_length region_merkleV5 merkleBytesV5_window wordsOf_getD)
set_option linter.unusedSimpArgs false
theorem window_window (L : List UInt8) (o m a n : Nat) (h : a + n ≤ m) :
    window (window L o m) a n = window L (o + a) n := by
  unfold window
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
section
variable (N : HashOutput) (w : WCT9.Witness)
theorem witList_head (o : Nat) (h : o + 8 ≤ 64) : window (witListV6 N w) o 8 = window (witListV5 N w) o 8 := by
  unfold witListV6 witListV5
  simp only [List.append_assoc]
  rw [window_append_left _ _ _ _ (by rw [headerBytes_length]; omega),
    window_append_left _ _ _ _ (by rw [headerBytes_length]; omega)]
theorem witList_tail (o : Nat) (h : 8128 ≤ o) :
    window (witListV6 N w) o 8 = window (witListV5 N w) (o + 1152) 8 := by
  unfold witListV6 witListV5
  simp only [List.append_assoc]
  rw [window_append_right (headerBytes w) _ _ _ (by rw [headerBytes_length]; omega),
    window_append_right (headerBytes w) _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    window_append_right (wctBytesV6 N w.signature) _ _ _ (by rw [wctBytesV6_length]; omega),
    window_append_right (wctBytesV5 N w.signature) _ _ _ (by rw [wctBytesV5_length]; omega), wctBytesV6_length,
    wctBytesV5_length,
    show o + 1152 - 64 - 9216 = o - 64 - 8064 by omega]
theorem witList_region (k : Nat) (hk : k < 9) (j : Nat) (hj : j + 8 ≤ 896) :
    window (witListV6 N w) (64 + 896 * k + j) 8 =
      window (regionBytesV6 (WCT9.child N ⟨k, hk⟩).val (w.signature.openings ⟨k, hk⟩)) j 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_right _ _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    window_append_left _ _ _ _ (by rw [wctBytesV6_length]; omega),
    show 64 + 896 * k + j - 64 = 896 * k + j by omega]
  unfold wctBytesV6
  rw [window_flatMap_const _ _ 896 (fun k => regionBytesV6_length _ _) k (by simp; omega) j 8 hj]
  simp
theorem witListV5_region (k : Nat) (hk : k < 9) (j : Nat) (hj : j + 8 ≤ 1024) :
    window (witListV5 N w) (64 + 1024 * k + j) 8 =
      window (regionBytesV5 (WCT9.child N ⟨k, hk⟩).val (w.signature.openings ⟨k, hk⟩)) j 8 := by
  unfold witListV5
  simp only [List.append_assoc]
  rw [window_append_right _ _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    window_append_left _ _ _ _ (by rw [wctBytesV5_length]; omega),
    show 64 + 1024 * k + j - 64 = 1024 * k + j by omega]
  unfold wctBytesV5
  rw [window_flatMap_const _ _ 1024 (fun k => regionBytesV5_length _ _) k (by simp; omega) j 8 hj]
  simp
end
section
variable (c : Nat) (op : WCT9.Opening)
theorem region_tail (o : Nat) (h0 : 320 ≤ o) (h : o + 8 ≤ 896) :
    window (regionBytesV6 c op) o 8 = window (regionBytesV5 c op) (o + 128) 8 := by
  unfold regionBytesV6 regionBytes regionBytesV5
  simp only [List.append_assoc]
  rw [window_append_right (merkleBytes c op) _ _ _ (by rw [merkleBytes_length]; omega),
    window_append_right (merkleBytesV5 c op) _ _ _ (by rw [merkleBytesV5_length]; omega), merkleBytes_length,
    merkleBytesV5_length,
    show o + 128 - 448 = o - 320 by omega, zeros, zeros, zeros, List.replicate_append_replicate]
  rfl
theorem region_v6_left (o : Nat) (h : o + 8 ≤ 832) :
    window (regionBytesV6 c op) o 8 = window (regionBytes c op) o 8 := by
  unfold regionBytesV6
  rw [window_append_left _ _ _ _ (by rw [regionBytes_length]; omega)]
theorem merkleV5_sib (l : Fin 7) : window (merkleBytesV5 c op) (srcOff c l.val) 16 = bytesLE 16 (op.path l) := by
  unfold srcOff
  have hb : c / 2 ^ l.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [merkleBytesV5_window c op l _ (by omega)]
  by_cases h1 : c / 2 ^ l.val % 2 = 1
  · rw [if_pos h1, h1, show 48 * (1 - 1) = 0 from rfl,
      window_append_left _ _ _ _ (by simp [bytesLE_length]), window_full _ _ (bytesLE_length _ _)]
  · rw [if_neg h1, show 48 * (1 - c / 2 ^ l.val % 2) = 48 by omega,
      window_append_right _ _ _ _ (by simp [zeros]), show 48 - (zeros 48).length = 0 by simp [zeros],
      window_full _ _ (bytesLE_length _ _)]
theorem sib_window (hc : c < 128) (l : Nat) (hl : l < 7) (a : Nat) (ha : a + 8 ≤ 16) :
    window (merkleBytes c op) (authSibOff c l + a) 8 = window (merkleBytesV5 c op) (srcOff c l + a) 8 := by
  rw [← window_window _ _ 16 _ _ ha, ← window_window _ _ 16 _ _ ha,
    merkleBytes_sib hc op ⟨l, hl⟩, merkleV5_sib c op ⟨l, hl⟩]
theorem merkle_none (hc : c < 128) (j : Nat) (hj : j < 40) (h : sibSrc c j = none) :
    window (merkleBytes c op) (8 * j) 8 = zeros 8 := by
  have hn : ∀ l < 7, authSibOff c l ≠ 8 * j ∧ authSibOff c l + 8 ≠ 8 * j := by
    intro l hl
    unfold sibSrc sibLev at h
    rw [Option.map_eq_none_iff] at h
    have := find_none h l hl
    simp only [decide_eq_false_iff_not, not_or] at this
    exact this
  unfold merkleBytes
  rw [window_map_range _ _ _ _ (by omega)]
  rw [List.map_congr_left (fun i hi => authByte_none op (fun l => by
    have hi' := List.mem_range.mp hi
    have h16 := authSibOff_ok c hc l.val l.isLt
    have := hn l.val l.isLt
    omega))]
  simp [zeros, List.map_const']
end
theorem compact_words (N : HashOutput) (w : WCT9.Witness) (i : Nat) (hi : i < 2729) :
    (wordsOf (witListV6 N w)).getD i 0 =
      finalWord (fun B => (wordsOf (witListV5 N w)).getD ((B - 0x800) / 8) 0)
        (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) i := by
  have hW := witListV6_length N w
  have hV := witListV5_length N w
  rw [wordsOf_getD _ 2729 (by omega) i hi]
  unfold finalWord
  by_cases h8 : i < 8
  · rw [if_pos h8]
    beta_reduce
    rw [show (0x800 + 8 * i - 0x800) / 8 = i by omega, wordsOf_getD _ 2873 (by omega) i (by omega),
      witList_head N w _ (by omega)]
  rw [if_neg h8]
  by_cases ht : 1016 ≤ i
  · rw [if_neg (show ¬ i < 1016 by omega)]
    beta_reduce
    rw [show (0x800 + 8 * (i + 144) - 0x800) / 8 = i + 144 by omega,
      wordsOf_getD _ 2873 (by omega) (i + 144) (by omega), witList_tail N w _ (by omega),
      show 8 * i + 1152 = 8 * (i + 144) by ring]
  rw [if_pos (show i < 1016 by omega)]
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 112 ∧ i = 8 + 112 * k + j :=
    ⟨(i - 8) / 112, (i - 8) % 112, Nat.mod_lt _ (by norm_num), by omega⟩
  have hk : k < 9 := by omega
  have hcl : N.toNat / 2 ^ WCT9.childBase k % 128 < 128 := Nat.mod_lt _ (by norm_num)
  rw [show (8 + 112 * k + j - 8) / 112 = k by omega, show (8 + 112 * k + j - 8) % 112 = j by omega,
    show 8 * (8 + 112 * k + j) = 64 + 896 * k + 8 * j by ring, witList_region N w k hk (8 * j) (by omega)]
  have hcv : (WCT9.child N ⟨k, hk⟩).val = N.toNat / 2 ^ WCT9.childBase k % 128 := rfl
  rw [hcv]
  by_cases hj40 : j < 40
  · rw [if_pos hj40, region_v6_left _ _ _ (by omega), region_merkle _ _ _ _ (by omega)]
    cases h : sibSrc (N.toNat / 2 ^ WCT9.childBase k % 128) j with
    | none =>
      rw [merkle_none _ _ hcl j hj40 h]
      rfl
    | some o =>
      have ho := sibSrc_lt h
      simp only
      rw [show (0x840 + 1024 * k + o - 0x800) / 8 = 8 + 128 * k + o / 8 by omega,
        wordsOf_getD _ 2873 (by omega) _ (by omega),
        show 8 * (8 + 128 * k + o / 8) = 64 + 1024 * k + o by omega, witListV5_region N w k hk o (by omega), hcv,
        region_merkleV5 _ _ _ _ (by omega)]
      unfold sibSrc at h
      cases hl : sibLev (N.toNat / 2 ^ WCT9.childBase k % 128) j with
      | none => rw [hl] at h; simp at h
      | some l =>
        rw [hl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        unfold sibLev at hl
        obtain ⟨hl7, hp⟩ := find_some hl
        simp only [decide_eq_true_eq] at hp
        by_cases h0 : authSibOff (N.toNat / 2 ^ WCT9.childBase k % 128) l = 8 * j
        · rw [if_pos h0] at h
          subst h
          have := sib_window _ (w.signature.openings ⟨k, hk⟩) hcl l hl7 0 (by norm_num)
          rw [Nat.add_zero, Nat.add_zero, h0] at this
          rw [this]
        · rw [if_neg h0] at h
          subst h
          have := sib_window _ (w.signature.openings ⟨k, hk⟩) hcl l hl7 8 (by norm_num)
          rw [show authSibOff (N.toNat / 2 ^ WCT9.childBase k % 128) l + 8 = 8 * j by omega] at this
          rw [this]
  · rw [if_neg hj40, region_tail _ _ _ (by omega) (by omega)]
    beta_reduce
    rw [show (0x840 + 1024 * k + 448 + 8 * (j - 40) - 0x800) / 8 = 8 + 128 * k + (j + 16) by omega,
      wordsOf_getD _ 2873 (by omega) _ (by omega),
      show 8 * (8 + 128 * k + (j + 16)) = 64 + 1024 * k + (8 * j + 128) by ring,
      witListV5_region N w k hk _ (by omega), hcv]
end ClaudeWCT.W9.Machine.Expand.Compact
end

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
theorem lvSrc_val (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    SNAP2 + 8136 ≤ lvSrc lay j ∧ lvSrc lay j ≤ SNAP2 + 8136 + 64 * 171 ∧ (lvSrc lay j - SNAP2) % 8 = 0 := by
  have hS : SNAP2 = 0x300000 := rfl
  unfold lvSrc
  split_ifs <;> omega
theorem pathOut_congr (M M' : Nat → Word) (lay r p : Nat)
    (h : ∀ j < lvH lay, M (lvSrc lay j - SNAP2 + WIT + (p - 16 * plan lay r j)) =
      M' (lvSrc lay j - SNAP2 + WIT + (p - 16 * plan lay r j))) :
    pathOut M lay r p = pathOut M' lay r p := by
  unfold pathOut
  split
  · rename_i j hj
    exact h j (List.mem_range.mp (List.mem_of_find?_eq_some hj))
  · rfl
theorem out2_congr (M M' : Nat → Word) (h : ∀ x < 8 * 2729, x % 8 = 0 → M (WIT + x) = M' (WIT + x))
    (idx o : Nat) (ho : o % 8 = 0) : out2 M idx o = out2 M' idx o := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  have e : ∀ A, WIT ≤ A → A - WIT < 8 * 2729 → (A - WIT) % 8 = 0 → M A = M' A := fun A h1 h2 h3 => by
    have := h (A - WIT) h2 h3
    rwa [show WIT + (A - WIT) = A by omega] at this
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  have hz : (zoneLay o = 1 ∧ o < 14768) ∨ (zoneLay o = 2 ∧ 14768 ≤ o ∧ o < 17824) ∨
      (zoneLay o = 3 ∧ 17824 ≤ o) := by
    unfold zoneLay; split_ifs <;> omega
  have hzl : 1 ≤ zoneLay o ∧ zoneLay o < 4 := by omega
  have hpt : pathTop (zoneLay o) ≤ 368 := by unfold pathTop; split_ifs <;> omega
  have hch : chSrc (zoneLay o) - SNAP2 + (o - (chDst (zoneLay o) - WIT)) + 8 ≤ 8 * 2729 ∨ ¬ o < 20880 := by
    unfold chSrc
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> simp only [hz] at * <;> norm_num <;> omega
  have hch8 : (chSrc (zoneLay o) - SNAP2 + (o - (chDst (zoneLay o) - WIT))) % 8 = 0 := by
    unfold chSrc
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> simp only [hz] at * <;> norm_num <;> omega
  have hdl : (lvDst (zoneLay o) - WIT) % 8 = 0 := by
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> omega
  have hcs : SNAP2 ≤ chSrc (zoneLay o) := by unfold chSrc; omega
  unfold out2
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  · exact e _ (by omega) (by omega) (by omega)
  · rcases Nat.le_total ((o - 64) / 816) 8 with hq | hq
    · rw [Nat.min_eq_left hq]
      exact e _ (by omega) (by omega) (by omega)
    · rw [Nat.min_eq_right hq]
      exact e _ (by omega) (by omega) (by omega)
  · exact e _ (by omega) (by omega) (by omega)
  · apply pathOut_congr
    intro j hj
    obtain ⟨s1, s2, s3⟩ := lvSrc_val (zoneLay o) j hzl
    exact e _ (by omega) (by omega) (by omega)
  · exact e _ (by omega) (by omega) (by omega)
  · exact e _ (by omega) (by omega) (by omega)
  · exact e _ (by omega) (by omega) (by omega)
  · rfl
  · rw [e _ (by omega) (by omega) (by omega)]
theorem index_shr (N : SigGolfCandidate.T3.HashOutput) :
    N.extractLsb' 0 64 >>> 33 = BitVec.ofNat 64 (WCT9.digestIndex N) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero,
    BitVec.toNat_ofNat]
  unfold WCT9.digestIndex
  rw [Nat.mod_eq_of_lt (show N.toNat / 2 ^ 33 % 2 ^ 31 < 2 ^ 64 by omega)]
  rw [show (2 : Nat) ^ 64 = 2 ^ 33 * 2 ^ 31 by norm_num, Nat.mod_mul_right_div_self]
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section




namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (OutAt)
set_option linter.unusedSimpArgs false
structure CompactPre (N : HashOutput) (w : WCT9.Witness) (s : MachineState) : Prop where
  pc : s.pc = pcOf 351
  wit : s.readWords (BitVec.ofNat 64 0x800) 2873 = wordsOf (witListV5 N w)
  dig : OutAt s 0x60 N
  plan : PlanAt s
  lplan : Compact2.LPlanAt s
def compactC : Nat := 66005
def CompactGood (im : Image) : Prop :=
  NewCodeAt im → CodeAt im (pcOf 351) [compactJal] → ∀ N w s, CompactPre N w s →
    ∃ t, Steps im s compactC compactC t ∧ t.pc = pcOf 42718 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧
      t.readWords (BitVec.ofNat 64 0x800) 2614 = wordsOf (ClaudeWCT.W9.T3M.witList N w)
namespace Compact
sym_block cJal := symRun { noAlias := true } [compactJal] (pcOf 351) 10
theorem jal_spec {im : Image} (hJ : CodeAt im (pcOf 351) [compactJal]) (s : MachineState) (hpc : s.pc = pcOf 351) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 41108 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound cJal hJ s hpc (by simp [cJal.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, cJal.res, E.eval]
  · c_regs cJal.res
  · intro A _ _; simp [cJal.res, rv_simp]
theorem finalWord_congr (M M' : Nat → Word) (cs : Nat → Nat)
    (h : ∀ i' < 2873, M (0x800 + 8 * i') = M' (0x800 + 8 * i')) (i : Nat) (hi : i < 2729) :
    finalWord M cs i = finalWord M' cs i := by
  unfold finalWord
  split
  · exact h i (by omega)
  · split
    · split
      · cases hs : sibSrc (cs ((i - 8) / 112)) ((i - 8) % 112) with
        | none => rfl
        | some o =>
          have := sibSrc_lt hs
          simp only
          rw [show 0x840 + 1024 * ((i - 8) / 112) + o = 0x800 + 8 * (8 + 128 * ((i - 8) / 112) + o / 8) by omega]
          exact h _ (by omega)
      · rw [show 0x840 + 1024 * ((i - 8) / 112) + 448 + 8 * ((i - 8) % 112 - 40) =
          0x800 + 8 * (8 + 128 * ((i - 8) / 112) + 56 + ((i - 8) % 112 - 40)) by omega]
        exact h _ (by omega)
    · exact h _ (by omega)
end Compact
theorem compactGood_holds (im : Image) : CompactGood im := by
  intro hc hJ N w s hpre
  have hPL : PLAN = 0xff9a00 := rfl
  have hLP : Compact2.LPLAN = 0xff9400 := rfl
  obtain ⟨u, su, pu, ru, fu⟩ := Compact.jal_spec hJ s hpre.pc
  have hNu : OutAt u 0x60 N := fun j hj => by rw [fu _ (by omega) (fun h => h)]; exact hpre.dig j hj
  have hpu : PlanAt u := fun j hj => by rw [fu _ (by omega) (fun h => h)]; exact hpre.plan j hj
  obtain ⟨v, sv, pv, rv, mv, fv⟩ := Compact.run_spec hc N u pu hNu hpu
  have hix : v.getMem (BitVec.ofNat 64 0x60) >>> 33 = BitVec.ofNat 64 (WCT9.digestIndex N) := by
    rw [fv 0x60 (by norm_num) (Or.inl (by norm_num))]
    have h0 := hNu 0 (by norm_num)
    rw [show (0x60 : Nat) + 8 * 0 = 0x60 from rfl] at h0
    rw [h0]
    exact Compact2.index_shr N
  have hlv : Compact2.LPlanAt v := fun k hk => by
    rw [fv _ (by omega) (Or.inr (by omega)), fu _ (by omega) (fun h => h)]
    exact hpre.lplan k hk
  obtain ⟨t, st, pt, t5, t10, mt⟩ := Compact2.run2_spec hc v pv (WCT9.digestIndex N) (WCT9.digestIndex_lt N) hix hlv
  refine ⟨t, ((su.trans sv).trans st).of_eq (by unfold compactC; norm_num) (by unfold compactC; norm_num), pt, t5,
    t10, ?_⟩
  have hW5 : ∀ i' < 2873, s.getMem (BitVec.ofNat 64 (0x800 + 8 * i')) = (wordsOf (witListV5 N w)).getD i' 0 := by
    intro i' hi'
    rw [← hpre.wit, VLib.readWords_ofNat s 0x800 2873 (by norm_num)]
    simp [List.getD_eq_getElem?_getD, hi']
  have hv6 : ∀ x < 8 * 2729, x % 8 = 0 →
      v.getMem (BitVec.ofNat 64 (Compact2.WIT + x)) = Compact2.v6M N w (Compact2.WIT + x) := by
    intro x hx h8
    obtain ⟨i, rfl⟩ : ∃ i, x = 8 * i := ⟨x / 8, by omega⟩
    rw [show Compact2.WIT = 0x800 from rfl, mv i (by omega)]
    unfold Compact2.v6M
    rw [show (0x800 + 8 * i - Compact2.WIT) / 8 = i by unfold Compact2.WIT; omega,
      Compact.compact_words N w i (by omega)]
    apply Compact.finalWord_congr _ _ _ (fun i' hi' => ?_) i (by omega)
    rw [fu _ (by omega) (fun h => h), hW5 i' hi', show (0x800 + 8 * i' - 0x800) / 8 = i' by omega]
  have hl : (wordsOf (ClaudeWCT.W9.T3M.witList N w)).length = 2614 :=
    length_wordsOf 2614 _ (by rw [ClaudeWCT.W9.T3M.witList_length_eq])
  rw [← hl]
  refine readWords_ext t _ 0x800 (fun i hi => ?_)
  rw [hl] at hi
  rw [mt _ (by omega), show 0x800 + 8 * i = Compact2.WIT + 8 * i from rfl,
    Compact2.run2_zone _ _ _ (by omega) (by omega), Compact2.compact2_words N w i hi]
  exact Compact2.out2_congr _ _ hv6 _ _ (by omega)
end ClaudeWCT.W9.Machine.Expand
end

section










section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (KernAt)
open SigGolfCandidate.T3M.Expand (LInv LPost lcost)
def BackSpec (im : Image) : Prop :=
  (∀ (sk : BitVec 256) (sig : WCT9.Signature) (index : Nat) (root : Digest) (s : MachineState),
    LInv sig index 4 (.forest root) s →
      TBSim im sk s (lcost 4) (WCT9.expandLayersBC sig index 4 (.forest root)) (LPost s sig index 4)) ∧
  CodeAt im (pcOf 342) compareCode ∧ KernAt im 354
def ExpandComposeSpec : Prop :=
  ∀ imgs : Phase → Image, (imgs .expand).Valid (w9Sub imgs).sizes (w9Sub imgs).layout →
    NewCodeAt (imgs .expand) → FrontAt (imgs .expand) → ExpandDataOK (imgs .expand) → BackSpec (imgs .expand) →
    ExpandRefinesW imgs ∧ ExpandTerminatesW imgs
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Layer height chainCount route)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK KernAt NODE NOUT EOUT DIGITS)
open SigGolfCandidate.T3M.Expand (IDXV LInv LPost lcost lP lD lk lWC lWM LW LZero SigLayersAt HalfAt
  RlWit entryOf lval lpath sideOff CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (ltable ltable_lo ltable_disj rlWit_range)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests sigDigests_sigDec sigDigests_layValue sigDigests_layPath)
set_option linter.unusedSimpArgs false
theorem dword_of_halves (w : BitVec 64) :
    w = BitVec.ofNat 64 ((w.extractLsb' 0 32).toNat + 2 ^ 32 * (w.extractLsb' 32 32).toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  have h1 : w.toNat / 2 ^ 32 % 2 ^ 32 = w.toNat / 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  omega
def ExpQW : Option (HashOutput × WCT9.Witness) → MachineState → Prop
  | none, t => FailedAt 354 t ∨ FailedAt 41062 t
  | some (N, w), t => t.pc = pcOf 42718 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 0 ∧
      t.readWords (BitVec.ofNat 64 0x800) 2614 = wordsOf (ClaudeWCT.W9.T3M.witList N w)
def expCostW : Nat := 37 + newCost + (lcost 4 + 9 + compactC)
theorem lcost_four : lcost 4 ≤ 3011803496 := by decide
theorem expCostW_le : expCostW ≤ 3431400667 := by
  have h := lcost_four
  unfold expCostW newCost compactC
  generalize lcost 4 = L at h ⊢
  omega
theorem expCostW_lt : expCostW + 1 < CYCLE_LIMIT := by
  have h := lcost_four
  unfold expCostW newCost compactC CYCLE_LIMIT
  generalize lcost 4 = L at h ⊢
  omega
theorem hookAt_of_front {im : Image} (hF : FrontAt im) : HookAt im :=
  codeAt_appR (n := 0) (a := SigGolfCandidate.T3M.Expand.seg_0) hF.1 (by decide)
theorem lP_eq (lay : Layer) : lP lay = 0x7000 + 2192 + 16 * (ClaudeWCT.W9.T3M.layIdx lay - 118) ∧ 118 ≤ ClaudeWCT.W9.T3M.layIdx lay ∧
    ClaudeWCT.W9.T3M.layIdx lay + chainCount lay + height lay ≤ 332 := by
  fin_cases lay <;> decide
def FrontW (A : Nat) : Prop :=
  A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 ∨
    A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8
theorem lD_cases (lay : Layer) : lD lay = 0x3ce8 ∨ lD lay = 0x4968 ∨ lD lay = 0x55a8 ∨ lD lay = 0x820 := by
  fin_cases lay <;> simp [lD]
theorem lk_zero (lay : Layer) : lk lay = 0 := by fin_cases lay <;> rfl
theorem lD_above (lay : Layer) (h : lay.val ≠ 0) : lD (Fin.ofNat 4 (lay.val - 1)) = lBase lay + 32 := by
  fin_cases lay <;> simp_all [lD, lBase] <;> rfl
theorem fin_ofNat_pred (lay : Layer) : (Fin.ofNat 4 (lay.val - 1) : Layer).val = lay.val - 1 := by
  fin_cases lay <;> rfl
theorem region_bounds (lay : Layer) : 0x2c48 ≤ lBase lay ∧ lBase lay + 64 * (height lay + chainCount lay) ≤ 0x61C8 := by
  fin_cases lay <;> decide
theorem lD_in_region (lay lay' : Layer) (A : Nat) (h1 : lBase lay ≤ A) (h2 : A < lBase lay + 64 * (height lay + chainCount lay))
    (he : A = lD lay') : A = lBase lay + 32 := by
  subst he
  fin_cases lay <;> fin_cases lay' <;> simp_all [lD, lBase, height, chainCount] <;> omega
theorem rlWit_region (lay lay' : Layer) (leaf A : Nat) (h1 : lBase lay ≤ A)
    (h2 : A < lBase lay + 64 * (height lay + chainCount lay)) (hne : lay' ≠ lay)
    (h : RlWit lay' leaf (lWC lay') (lWM lay') A) : False := by
  have hr := rlWit_range h
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  obtain ⟨hWM', hWC'⟩ := lBase_eq lay'
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  rcases ltable_disj lay' lay hne with hd | hd <;> omega
theorem halves_lo (x z y : BitVec 32) (hy : y = 0) (hxz : x = z) :
    BitVec.ofNat 64 (x.toNat + 2 ^ 32 * y.toNat) = BitVec.ofNat 64 z.toNat := by
  subst hy hxz; simp
section run
variable {sk : BitVec 256}
theorem expandW_tbsim {im : Image} (hc : NewCodeAt im) (hF : FrontAt im) (hd : ExpandDataOK im)
    (hB : BackSpec im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    TBSim im sk (w9init im m pk σ) expCostW (ClaudeWCT.W9.T3M.expandN m pk (sigDec σ)) ExpQW := by
  set sig := sigDec σ with hsig
  set s0 := w9init im m pk σ with hs0
  obtain ⟨t1, st1, hpre, hmz, w800, w808, f1⟩ := front_pre30 hF hd m pk σ
  have hz0 : ∀ A, A < Compact2.LPLAN → (A < 0x7000 ∨ 0x7000 + 5312 ≤ A) → (A < 0xA0 ∨ 0xB0 ≤ A) →
      (A < 0x59B0 ∨ 0x59D0 ≤ A) → s0.getMem (BitVec.ofNat 64 A) = 0 := fun A hA h1 h2 h3 =>
    w9init_zero hd m pk σ A hA ⟨h1, h2, by omega⟩
  have hz0' : ∀ A, A < Compact2.LPLAN → (A < 0x7000 ∨ 0x7000 + 5312 ≤ A) → (A < 0xA0 ∨ 0xB0 ≤ A) →
      ¬ (0x59B0 ≤ A ∧ A < 0x59D0 ∧ (A - 0x59B0) % 8 = 0) → s0.getMem (BitVec.ofNat 64 A) = 0 :=
    fun A hA h1 h2 h3 => w9init_zero hd m pk σ A hA ⟨h1, h2, h3⟩
  unfold Compact2.LPLAN at hz0 hz0'
  rw [expandN_split]
  have hCC : compactC = 66005 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  refine (TBSim.steps st1 (TBSim.bind (W₂ := lcost 4 + 9 + compactC)
    (newCode_tb hc (hookAt_of_front hF) sk m sig t1 hpre) (fun r t7 h7 => ?_))).mono
    (by unfold expCostW; omega) (fun _ _ h => h)
  rcases r with _ | ⟨counter, N, root⟩
  · exact (TBSim.pure (Q := ExpQW) (a := none) (Or.inr h7.1)).mono (by omega) (fun _ _ h => h)
  have P := h7.1
  have hi7 := h7.2 rfl
  simp only [NewPost] at P
  set index := WCT9.digestIndex N with hindex
  have hi : index < 2 ^ 31 := WCT9.digestIndex_lt N
  have F7 : Frame s0 t7 (fun A => FrontW A ∨ NewW A) := f1.trans P.frame
  have g7 : ∀ A, A < 2 ^ 64 → ¬ FrontW A → ¬ NewW A → t7.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => F7 A hA (fun h => h.elim h1 h2)
  have nFW : ∀ A, (A < 0x800 ∨ 0x810 ≤ A) → (A < DIG ∨ DIG + 64 ≤ A) → (A < 0x59B0 ∨ 0x59D0 ≤ A) → ¬ FrontW A := by
    intro A h1 h2 h3 h; unfold FrontW at h; simp only [DIG] at h h2; omega
  have nNW : ∀ A, A ≠ 0x810 → (A < 0x60 ∨ 0x80 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) → (A < 0x400 ∨ 0x550 ≤ A) →
      (A < 0x840 ∨ 0x2c48 ≤ A) → (A < 0x7890 ∨ 0x85f0 ≤ A) → (A < DIG + 16 ∨ DIG + 32 ≤ A) →
      (A < NBUF ∨ NBUF + 32 ≤ A) → A ≠ IDXV → A ≠ ENC → A ≠ ENC + 8 → ¬ NewW A := by
    intro A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h
    unfold NewW at h; simp only [DIG, NBUF, IDXV, ENC] at h h7 h8 h9 h10 h11; omega
  have z7 : ∀ A, A < 0x7000 → (A < 0x60 ∨ 0x80 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) → (A < 0x400 ∨ 0x550 ≤ A) →
      (A < 0x800 ∨ 0x818 ≤ A) → (A < 0x840 ∨ 0x2c48 ≤ A) → (A < 0xA0 ∨ 0xB0 ≤ A) → (A < 0x59B0 ∨ 0x59D0 ≤ A) →
      t7.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A h0 h1 h2 h3 h4 h4' h5 h6
    rw [g7 A (by omega) (nFW _ (by omega) (by simp only [DIG]; omega) h6)
      (nNW _ (by omega) h1 h2 h3 h4' (by omega) (by simp only [DIG]; omega) (by simp only [NBUF]; omega)
        (by simp only [IDXV]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)),
      hz0 _ (by omega) (by omega) h5 h6]
  have z7h : ∀ A, 0x20000 ≤ A → A < 0x30000 → A ≠ ENC → A ≠ ENC + 8 → (A < DIG ∨ DIG + 64 ≤ A) →
      (A < NBUF ∨ NBUF + 32 ≤ A) → A ≠ IDXV → t7.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A h0 h1 h2 h3 h4 h5 h6
    rw [g7 A (by omega) (nFW _ (by omega) h4 (by omega))
      (nNW _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [DIG] at h4 ⊢; omega)
        h5 h6 h2 h3),
      hz0 _ (by omega) (by omega) (by omega) (by omega)]
  have hL : LInv sig index 4 (.forest root) t7 := by
    refine ⟨by rw [P.pc]; rfl, le_refl _, P.x5, hi, P.idx, P.enc, fun _ => ?_, fun h => absurd h (by decide),
      ⟨0, by norm_num, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [SigGolfCandidate.T3M.Search.BC.right]
      refine ⟨?_, ?_⟩
      · rw [z7h _ (by simp only [ENC]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)
          (by simp only [ENC]; omega) (by simp only [DIG, ENC]; omega) (by simp only [NBUF, ENC]; omega)
          (by simp only [IDXV, ENC]; omega)]; decide
      · rw [z7h _ (by simp only [ENC]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)
          (by simp only [ENC]; omega) (by simp only [DIG, ENC]; omega) (by simp only [NBUF, ENC]; omega)
          (by simp only [IDXV, ENC]; omega)]; decide
    · rw [z7h _ (by simp only [ENC]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)
        (by simp only [ENC]; omega) (by simp only [DIG, ENC]; omega) (by simp only [NBUF, ENC]; omega)
        (by simp only [IDXV, ENC]; omega)]; rfl
    · intro lay
      obtain ⟨hP, h127, hlen⟩ := lP_eq lay
      refine ⟨fun i hi' => ?_, fun j hj => ?_⟩
      · have hd := P.layers (ClaudeWCT.W9.T3M.layIdx lay - 118 + i) (by omega)
        rw [show 118 + (ClaudeWCT.W9.T3M.layIdx lay - 118 + i) = ClaudeWCT.W9.T3M.layIdx lay + i by omega,
          sigDigests_layValue sig lay i hi',
          show 0x7000 + 2192 + 16 * (ClaudeWCT.W9.T3M.layIdx lay - 118 + i) = lP lay + 16 * i by rw [hP]; ring] at hd
        exact hd
      · have hd := P.layers (ClaudeWCT.W9.T3M.layIdx lay - 118 + (chainCount lay + j)) (by omega)
        rw [show 118 + (ClaudeWCT.W9.T3M.layIdx lay - 118 + (chainCount lay + j)) =
            ClaudeWCT.W9.T3M.layIdx lay + (chainCount lay + j) by omega,
          sigDigests_layPath sig lay j hj,
          show 0x7000 + 2192 + 16 * (ClaudeWCT.W9.T3M.layIdx lay - 118 + (chainCount lay + j)) =
            lP lay + 16 * chainCount lay + 16 * j by rw [hP]; ring] at hd
        exact hd
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [z7h _ (by simp only [CHAIN, Search.NODE, LEAFPK, ENC]; omega)
          (by simp only [CHAIN, Search.NODE, LEAFPK, ENC]; omega) (by simp only [CHAIN, Search.NODE, LEAFPK, ENC]; omega)
          (by simp only [CHAIN, Search.NODE, LEAFPK, ENC]; omega)
          (by simp only [CHAIN, Search.NODE, LEAFPK, ENC, DIG]; omega)
          (by simp only [CHAIN, Search.NODE, LEAFPK, ENC, NBUF]; omega)
          (by simp only [CHAIN, Search.NODE, LEAFPK, ENC, IDXV]; omega)]
    · apply (w9init_table hd m pk σ).frame F7
      intro i hi h
      rcases h with h | h
      · unfold FrontW at h; simp only [TOP_DATA, DIG] at h; omega
      · unfold NewW at h; simp only [TOP_DATA, DIG, NBUF, IDXV, ENC] at h; omega
    · apply (w9init_cf hd m pk σ).frame F7
      intro i hi hi' h
      rcases h with h | h
      · unfold FrontW at h; simp only [TOP_DATA, DIG] at h; omega
      · unfold NewW at h; simp only [TOP_DATA, DIG, NBUF, IDXV, ENC] at h; omega
  simp only [tailProg]
  refine (TBSim.bind (W₂ := 9 + compactC) (hB.1 sk sig index root t7 hL) (fun r8 t8 h8 => ?_)).mono
    (by omega) (fun _ _ h => h)
  rcases r8 with _ | ⟨root', counters⟩
  · exact (TBSim.pure (Q := ExpQW) (a := none) (Or.inl h8)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p8, x5_8, e8, hlen8, hout8, hhf8, r8, f8⟩ := h8
  have g87 : ∀ A, A < 2 ^ 64 → ¬ LW index 4 A → t8.getMem (BitVec.ofNat 64 A) = t7.getMem (BitVec.ofNat 64 A) :=
    fun A hA h => f8.get hA h
  have nLW : ∀ A, A < 0x2c48 → A ≠ 0x820 → ¬ LW index 4 A := by
    intro A hA h8 h
    rcases h with h | h | ⟨lay, _, h | h⟩
    · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch, SigGolfCandidate.T3M.Expand.RlScratch, CHAIN, Search.NODE,
        Search.NOUT, LEAFPK, ENC] at h; omega
    · rcases lD_cases lay with e | e | e | e <;> omega
    · have := rlWit_range h; have := ltable_lo lay; omega
  have hpk : ∀ j < 2, t8.getMem (BitVec.ofNat 64 (0xA0 + 8 * j)) = pk.extractLsb' (64 * j) 64 := by
    intro j hj
    rw [g87 _ (by omega) (nLW _ (by omega) (by omega)), g7 _ (by omega)
      (nFW _ (by omega) (by simp only [DIG]; omega) (by omega))
      (nNW _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [DIG]; omega)
        (by simp only [NBUF]; omega) (by simp only [IDXV]; omega) (by simp only [ENC]; omega)
        (by simp only [ENC]; omega))]
    exact w9init_pk hd m pk σ j hj
  obtain ⟨t9, st9, p9, x28, x29, r9, f9⟩ := c342W hB.2.1 t8 p8
  have hlo : (t8.getMem (BitVec.ofNat 64 ENC) = t8.getMem (BitVec.ofNat 64 0xA0)) ↔
      root'.extractLsb' 0 64 = pk.extractLsb' 0 64 := by
    rw [e8.1, show (0xA0 : Nat) = 0xA0 + 8 * 0 from rfl, hpk 0 (by decide)]
  have hhi : (t9.getMem (BitVec.ofNat 64 (ENC + 8)) = t9.getMem (BitVec.ofNat 64 0xA8)) ↔
      root'.extractLsb' 64 64 = pk.extractLsb' 64 64 := by
    rw [f9.get (by decide) (by simp), f9.get (by decide) (by simp), e8.2,
      show (0xA8 : Nat) = 0xA0 + 8 * 1 from rfl, hpk 1 (by decide)]
  have hsplit : root' = pk ↔ root'.extractLsb' 0 64 = pk.extractLsb' 0 64 ∧
      root'.extractLsb' 64 64 = pk.extractLsb' 64 64 := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases h : i < 64
      · have := congrArg (fun x => x.getLsbD i) h0
        simpa [BitVec.getLsbD_extractLsb', h] using this
      · have := congrArg (fun x => x.getLsbD (i - 64)) h1
        simp [BitVec.getLsbD_extractLsb', show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega] at this
        simpa using this
  by_cases heq : root' = pk
  · simp only [heq, ne_eq, not_true_eq_false, ↓reduceIte]
    have h1 := (hsplit.mp heq)
    rw [if_pos (hlo.mpr h1.1)] at p9
    obtain ⟨t10, st10, p10, r10, f10⟩ := c348W hB.2.1 t9 p9 x28 x29
    rw [if_pos (hhi.mpr h1.2)] at p10
    set w : WCT9.Witness := ⟨sig, counter, fun lay => counters.getD lay.val 0⟩ with hw
    have f810 : Frame t8 t10 (fun _ => False) := (f9.trans f10).mono (fun _ _ h => by rcases h with h | h <;> exact h)
    have nLWp : ∀ A, 0xff0000 ≤ A → ¬ LW index 4 A := by
      intro A hA h
      rcases h with h | h | ⟨lay, _, h | h⟩
      · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
      · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch, SigGolfCandidate.T3M.Expand.RlScratch, CHAIN,
          Search.NODE, Search.NOUT, LEAFPK, ENC] at h; omega
      · have := ltable lay; omega
      · have := rlWit_range h; have := ltable lay; omega
    have hdig : OutAt t10 0x60 N := fun j hj => by
      rw [f810.get (by omega) (fun h => h), g87 _ (by omega) (nLW _ (by omega) (by omega))]
      exact P.dig j hj
    have hplan : PlanAt t10 := fun j hj => by
      rw [f810.get (by omega) (fun h => h), g87 _ (by omega) (nLWp _ (by omega)),
        P.frame _ (by omega) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega)]
      exact hpre.plan j hj
    have hlplan : Compact2.LPlanAt t10 := fun j hj => by
      have hLP : Compact2.LPLAN = 0xff9400 := rfl
      rw [f810.get (by omega) (fun h => h), g87 _ (by omega) (nLWp _ (by omega)),
        P.frame _ (by omega) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega),
        f1.get (by omega) (by simp only [DIG]; omega)]
      exact w9init_lplan hd m pk σ j hj
    have hwit8 : t8.readWords (BitVec.ofNat 64 0x800) 2873 = wordsOf (witListV5 N w) := by
      have halves : ∀ D lo hi, (t8.getMem (BitVec.ofNat 64 D)).extractLsb' 0 32 = lo →
          (t8.getMem (BitVec.ofNat 64 D)).extractLsb' 32 32 = hi →
          t8.getMem (BitVec.ofNat 64 D) = BitVec.ofNat 64 (lo.toNat + 2 ^ 32 * hi.toNat) := by
        intro D lo hi h1 h2
        rw [dword_of_halves (t8.getMem (BitVec.ofNat 64 D)), h1, h2]
      have hhf1 : ∀ D, (D = 0x3ce8 ∨ D = 0x4968 ∨ D = 0x55a8 ∨ D = 0x820) →
          (t8.getMem (BitVec.ofNat 64 D)).extractLsb' 32 32 = (t7.getMem (BitVec.ofNat 64 D)).extractLsb' 32 32 := by
        intro D hD
        have := hhf8 D 1 (by rcases hD with h | h | h | h <;> simp [h]) (by decide)
          (fun lay _ h => by rw [lk_zero] at h; exact absurd h.2 (by decide))
        simpa using this
      have r0 : t8.getMem (BitVec.ofNat 64 0x800) = sig.rho.extractLsb' 0 64 := by
        rw [g87 _ (by decide) (nLW _ (by decide) (by decide)),
          P.frame _ (by decide) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega)]
        exact w800
      have r8' : t8.getMem (BitVec.ofNat 64 0x808) = sig.rho.extractLsb' 64 64 := by
        rw [g87 _ (by decide) (nLW _ (by decide) (by decide)),
          P.frame _ (by decide) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega)]
        exact w808
      have c810 : t8.getMem (BitVec.ofNat 64 0x810) = BitVec.ofNat 64 counter.toNat := by
        rw [g87 _ (by decide) (nLW _ (by decide) (by decide))]
        have hhi0 : (t7.getMem (BitVec.ofNat 64 0x810)).extractLsb' 32 32 = 0 := by
          rw [hi7, show t1.getMem (BitVec.ofNat 64 0x810) = s0.getMem (BitVec.ofNat 64 0x810) from
            f1.get (by decide) (by simp only [DIG]; omega), hz0 _ (by decide) (by decide) (by decide)
            (by decide)]
          rfl
        rw [dword_of_halves (t7.getMem (BitVec.ofNat 64 0x810)), P.dc, hhi0]
        simp
      have c818 : t8.getMem (BitVec.ofNat 64 0x818) = 0 := by
        rw [g87 _ (by decide) (nLW _ (by decide) (by decide))]
        exact z7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have c820 : t8.getMem (BitVec.ofNat 64 0x820) = BitVec.ofNat 64 (counters.getD 3 0).toNat := by
        have hlo3 := (hout8 3 (by decide)).1
        simp only [HalfAt, show lD (3 : Layer) = 0x820 from rfl, show lk (3 : Layer) = 0 from rfl, Nat.mul_zero] at hlo3
        have hhi3 := hhf1 0x820 (by simp)
        rw [z7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hhi3
        rw [halves 0x820 _ _ hlo3 hhi3]
        simp
      have hz8 : ∀ A, 0x828 ≤ A → A < 0x840 → t8.getMem (BitVec.ofNat 64 A) = 0 := by
        intro A h1 h2
        rw [g87 A (by omega) (nLW A (by omega) (by omega))]
        exact z7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hh : t8.readWords (BitVec.ofNat 64 0x800) 8 = wordsOf (ClaudeWCT.W9.T3M.headerBytes w) := by
        rw [headerW_words, readWords_eight, r0, show 0x800 + 8 = 0x808 from rfl, r8',
          show 0x800 + 16 = 0x810 from rfl, c810, show 0x800 + 24 = 0x818 from rfl, c818,
          show 0x800 + 32 = 0x820 from rfl, c820, hz8 (0x800 + 40) (by decide) (by decide),
          hz8 (0x800 + 48) (by decide) (by decide), hz8 (0x800 + 56) (by decide) (by decide)]
        rfl
      have hplaced8 : Placed N sig t8 := fun k i hk hi' => by
        rw [g87 _ (by unfold regBase; omega) (nLW _ (by unfold regBase; omega) (by unfold regBase; omega))]
        exact P.placed k i hk hi'
      have hwct : t8.readWords (BitVec.ofNat 64 0x840) 1152 = wordsOf (wctBytesV5 N w.signature) :=
        placed_words hplaced8
      have hgap : t8.readWords (BitVec.ofNat 64 0x2c40) 1 = List.replicate 1 0 := by
        apply readWords_zero t8 0x2c40 1 (by decide)
        intro j hj
        rw [g87 _ (by omega) (nLW _ (by omega) (by omega))]
        exact P.gap _ (by omega) (by omega)
      have g8L : ∀ A, 0x2c48 ≤ A → A < 0x61C8 → ¬ LW index 4 A → t8.getMem (BitVec.ofNat 64 A) = 0 := by
        intro A h1 h2 hn
        rw [g87 A (by omega) hn]
        by_cases hm : 0x59B0 ≤ A ∧ A < 0x59D0 ∧ (A - 0x59B0) % 8 = 0
        · rw [P.frame A (by omega) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega)]
          exact hmz A (by omega) (by omega)
        · rw [g7 A (by omega) (by unfold FrontW; simp only [DIG]; omega)
            (nNW _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [DIG]; omega)
              (by simp only [NBUF]; omega) (by simp only [IDXV]; omega) (by simp only [ENC]; omega)
              (by simp only [ENC]; omega))]
          exact hz0' _ (by omega) (by omega) (by omega) hm
      have hlay : ∀ lay : Layer, t8.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
          wordsOf (layerRegionV6 N w lay) := by
        intro lay
        have hout := hout8 lay (by omega)
        have hrb := region_bounds lay
        have hv : ∀ i (h : i < chainCount lay), DigAt t8 (lWC lay - 64 * i + 48) ((sig.layers lay).values ⟨i, h⟩) := by
          intro i h
          have e : lval (WCT9.toT3Signature sig) lay i = (sig.layers lay).values ⟨i, h⟩ := by
            unfold lval; rw [dif_pos h]; rfl
          rw [← e]; exact hout.2.1 i h
        have hp : ∀ j (h : j < height lay), DigAt t8 (lWM lay - 64 * j + sideOff (route index lay).1 j)
            ((sig.layers lay).path ⟨j, h⟩) := by
          intro j h
          have e : lpath (WCT9.toT3Signature sig) lay j = (sig.layers lay).path ⟨j, h⟩ := by
            unfold lpath; rw [dif_pos h]; rfl
          rw [← e]; exact hout.2.2 j h
        unfold layerRegionV6
        split
        · rename_i h0
          refine layer_words t8 lay _ _ hv hp (fun A h1 h2 hn => g8L A (by omega) (by omega) ?_)
          rintro (h | h | ⟨lay', _, h | h⟩)
          · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
          · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch, SigGolfCandidate.T3M.Expand.RlScratch, CHAIN,
              Search.NODE, Search.NOUT, LEAFPK, ENC] at h; omega
          · have e1 := lD_in_region lay lay' A h1 h2 h
            have hl0 : lay = 0 := Fin.ext h0
            rw [hl0, show lBase (0 : Layer) = 0x2c48 from rfl] at e1
            rcases lD_cases lay' with e | e | e | e <;> omega
          · by_cases he : lay' = lay
            · subst he; exact hn h
            · exact rlWit_region lay lay' _ A h1 h2 he h
        · rename_i h0
          refine layerBC_words t8 lay _ _ _ hv hp ?_ (fun A h1 h2 hn hne => g8L A (by omega) (by omega) ?_)
          ·
            have hD := lD_above lay h0
            have hlo := (hout8 (Fin.ofNat 4 (lay.val - 1)) (by rw [fin_ofNat_pred]; omega)).1
            simp only [HalfAt, lk_zero, Nat.mul_zero, hD] at hlo
            have hhi1 := hhf1 (lBase lay + 32) (by rw [← hD]; exact lD_cases _)
            have hcase := lD_cases (Fin.ofNat 4 (lay.val - 1))
            rw [hD] at hcase
            rw [z7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] at hhi1
            rw [halves _ _ _ hlo hhi1]
            exact halves_lo _ _ _ (by decide) rfl
          · rintro (h | h | ⟨lay', _, h | h⟩)
            · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
            · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch, SigGolfCandidate.T3M.Expand.RlScratch, CHAIN,
                Search.NODE, Search.NOUT, LEAFPK, ENC] at h; omega
            · exact hne (lD_in_region lay lay' A h1 h2 h)
            · by_cases he : lay' = lay
              · subst he; exact hn h
              · exact rlWit_region lay lay' _ A h1 h2 he h
      exact witListW_words t8 N w hh hwct hgap hlay
    have hwit : t10.readWords (BitVec.ofNat 64 0x800) 2873 = wordsOf (witListV5 N w) := by
      rw [frame_readWords f810 0x800 2873 (by decide) (fun _ _ h => h)]; exact hwit8
    obtain ⟨t11, st11, p11, x5_11, x10_11, hw11⟩ :=
      compactGood_holds im hc (codeAt_351W hB.2.1) N w t10 ⟨p10, hwit, hdig, hplan, hlplan⟩
    exact (TBSim.steps (st9.trans (st10.trans st11)) (TBSim.pure (Q := ExpQW) (a := some (N, w))
      ⟨p11, x5_11, x10_11, hw11⟩)).mono (by omega) (fun _ _ h => h)
  · simp only [ne_eq, heq, not_false_eq_true, ↓reduceIte]
    by_cases h0 : root'.extractLsb' 0 64 = pk.extractLsb' 0 64
    · rw [if_pos (hlo.mpr h0)] at p9
      obtain ⟨t10, st10, p10, r10, f10⟩ := c348W hB.2.1 t9 p9 x28 x29
      have h1 : ¬ root'.extractLsb' 64 64 = pk.extractLsb' 64 64 := fun h => heq (hsplit.mpr ⟨h0, h⟩)
      rw [if_neg (fun h => h1 (hhi.mp h))] at p10
      obtain ⟨t11, st11, p11, x5_11, x10_11, _⟩ := Search.cs0_spec hB.2.2 t10 p10
      exact (TBSim.steps (st9.trans (st10.trans st11)) (TBSim.pure (Q := ExpQW) (a := none)
        (Or.inl ⟨p11, x5_11, x10_11⟩))).mono (by omega) (fun _ _ h => h)
    · rw [if_neg (fun h => h0 (hlo.mp h))] at p9
      obtain ⟨t10, st10, p10, x5_10, x10_10, _⟩ := Search.cs0_spec hB.2.2 t9 p9
      exact (TBSim.steps (st9.trans st10) (TBSim.pure (Q := ExpQW) (a := none)
        (Or.inl ⟨p10, x5_10, x10_10⟩))).mono (by omega) (fun _ _ h => h)
end run
theorem readBuffer_foldl_mod (t : MachineState) (A n : Nat) : ∀ m, n ≤ m →
    (List.range m).foldl
        (fun acc i => acc + (t.getByte (BitVec.ofNat 64 (A + i))).toNat * 2 ^ (8 * i)) 0 % 2 ^ (8 * n) =
      (List.range n).foldl
        (fun acc i => acc + (t.getByte (BitVec.ofNat 64 (A + i))).toNat * 2 ^ (8 * i)) 0 % 2 ^ (8 * n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega : 8 * n ≤ 8 * m)) _),
      Nat.add_zero, Nat.mod_mod, ih]
/-- Reading a buffer prefix: the first `n` bytes of a longer read. -/
theorem readBuffer_trunc (t : MachineState) (A n m : Nat) (h : n ≤ m) :
    readBuffer t A n = BitVec.ofNat (8 * n) (readBuffer t A m).toNat := by
  unfold readBuffer
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 * n ≤ 8 * m)), readBuffer_foldl_mod t A n m h]
/-- Expand still writes 2614 whole words; the 20908-byte witness is their prefix (the 4 bytes
after the 32-bit digest counter are zero and lie outside the witness). -/
theorem expqW_output {imgs : Phase → Image} {N : HashOutput} {w : WCT9.Witness} {t : MachineState}
    (h : t.readWords (BitVec.ofNat 64 0x800) 2614 = wordsOf (ClaudeWCT.W9.T3M.witList N w)) :
    readOutput (w9Sub imgs).sizes (w9Sub imgs).layout .expand t = ClaudeWCT.W9.T3M.witEnc N w := by
  show readBuffer t 0x800 20908 =
    BitVec.ofNat (8 * 20908) (SigGolfCandidate.T3.readLE (ClaudeWCT.W9.T3M.witList N w))
  rw [readBuffer_trunc t 0x800 20908 (8 * 2614) (by omega),
    readBuffer_of_words t 0x800 2614 (ClaudeWCT.W9.T3M.witList N w) (by decide) (by decide)
      (ClaudeWCT.W9.T3M.witList_length_eq N w) h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
theorem codeAt_42718 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf 42718) [0x00000073] :=
  codeAt_of_window hc (by decide) (by decide +kernel)
theorem expqW_halt (imgs : Phase → Image) (hc : NewCodeAt (imgs .expand)) (hB : BackSpec (imgs .expand))
    (a : Option (HashOutput × WCT9.Witness)) (t : MachineState) (h : ExpQW a t) :
    fetch ((w9Sub imgs).image .expand) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
      (a.map fun x => ClaudeWCT.W9.T3M.witEnc x.1 x.2) =
        (if t.getReg .x10 = 0 then some (readOutput (w9Sub imgs).sizes (w9Sub imgs).layout .expand t) else none) := by
  rcases a with _ | ⟨N, w⟩
  · rcases h with ⟨p, x5, x10⟩ | ⟨p, x5, x10⟩
    · refine ⟨((Search.codeAt_k_2 hB.2.2).fetch t p).trans rfl, x5, ?_⟩
      rw [x10]; rfl
    · refine ⟨((codeAt_41064 hc).fetch t p).trans rfl, x5, ?_⟩
      rw [x10]; rfl
  · obtain ⟨p, x5, x10, hw⟩ := h
    refine ⟨((codeAt_42718 hc).fetch t p).trans rfl, x5, ?_⟩
    rw [x10, if_pos (show (0#64 : BitVec 64) = 0 from rfl), expqW_output hw]; rfl
set_option maxRecDepth 10000 in
theorem expandComposeSpec_holds : ExpandComposeSpec := by
  intro imgs hv hc hF hd hB
  have hsim : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 5312),
      Sim ((w9Sub imgs).image .expand) (w9init (imgs .expand) m pk σ) expCostW
        (mrealize 0 (ClaudeWCT.W9.T3M.expandN m pk (sigDec σ))) ExpQW :=
    fun m pk σ => expandW_tbsim (sk := 0) hc hF hd hB m pk σ
  refine ⟨fun m pk σ => ?_, fun hash m pk σ => ?_⟩
  · exact Sim.run_eq (w9Sub imgs) .expand (m, pk, σ) (initialState_w9 imgs hv m pk σ) (hsim m pk σ)
      (Nat.lt_of_succ_lt expCostW_lt) _ (expqW_halt imgs hc hB)
  · obtain ⟨h1, h2⟩ := Sim.runWith (w9Sub imgs) .expand (m, pk, σ) (initialState_w9 imgs hv m pk σ)
      (hsim m pk σ) expCostW_lt (fun a t h => ⟨(expqW_halt imgs hc hB a t h).1, (expqW_halt imgs hc hB a t h).2.1⟩) hash
    exact ⟨h1, lt_of_le_of_lt h2 expCostW_lt⟩
end ClaudeWCT.W9.Machine.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT.W9.Machine.Expand (BackSpec compareCode)
theorem wct_compareCode : CodeAt image (pcOf 342) compareCode := by
  apply codeAt_slice
  · decide +kernel
  · decide +kernel
theorem wct_backSpec : BackSpec Images.expandImage := by
  exact ⟨fun sk sig index value s h => layers_tbsim 4 (.forest value) s h, wct_compareCode, Search.kernAt_expand⟩
set_option maxRecDepth 100000 in
theorem wct_prefixData : Images.expandPrefixData =
    ClaudeWCT.W9.Machine.Expand.lplanBytes ++ ClaudeWCT.W9.Machine.Expand.planBytes ++
      ClaudeWCT.W9.Machine.Expand.expCostBytes ++ ClaudeWCT.W9.Machine.Expand.hdrBankBytes := by
  unfold Images.expandPrefixData ClaudeWCT.W9.Machine.Expand.lplanBytes ClaudeWCT.W9.Machine.Expand.planBytes
    ClaudeWCT.W9.Machine.Expand.expCostBytes ClaudeWCT.W9.Machine.Expand.hdrBankBytes
  rw [← List.flatten_append, ← List.flatten_append, ← List.flatten_append]
  rfl
theorem wct_expandData : Images.expandImage.data =
    ClaudeWCT.W9.Machine.Expand.lplanBytes ++ ClaudeWCT.W9.Machine.Expand.planBytes ++
      ClaudeWCT.W9.Machine.Expand.expCostBytes ++ ClaudeWCT.W9.Machine.Expand.hdrBankBytes ++
        Images.expandLegacyData := by
  change Images.expandPrefixData ++ Images.expandLegacyData = _
  rw [wct_prefixData]
theorem wct_front0 : CodeAt Images.expandImage (pcOf 0) (seg_0 ++ [ClaudeWCT.W9.Machine.Expand.hookWord]) := by
  apply codeAt_slice
  · decide +kernel
  · decide +kernel
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT.W9.Machine.Expand (NewCodeAt expChunks expChunks_len_le)
set_option maxRecDepth 100000
private def chunks : List (List (BitVec 32)) :=
  [Images.expandCode_0, Images.expandCode_1, Images.expandCode_2, Images.expandCode_3, Images.expandCode_4, Images.expandCode_5, Images.expandCode_6, Images.expandCode_7, Images.expandCode_8, Images.expandCode_9, Images.expandCode_10, Images.expandCode_11, Images.expandCode_12, Images.expandCode_13, Images.expandCode_14, Images.expandCode_15, Images.expandCode_16, Images.expandCode_17, Images.expandCode_18, Images.expandCode_19, Images.expandCode_20, Images.expandCode_21, Images.expandCode_22, Images.expandCode_23, Images.expandCode_24, Images.expandCode_25, Images.expandCode_26, Images.expandCode_27, Images.expandCode_28, Images.expandCode_29, Images.expandCode_30, Images.expandCode_31, Images.expandCode_32, Images.expandCode_33, Images.expandCode_34, Images.expandCode_35, Images.expandCode_36, Images.expandCode_37, Images.expandCode_38, Images.expandCode_39, Images.expandCode_40, Images.expandCode_41, Images.expandCode_42, Images.expandCode_43, Images.expandCode_44, Images.expandCode_45, Images.expandCode_46, Images.expandCode_47, Images.expandCode_48, Images.expandCode_49, Images.expandCode_50, Images.expandCode_51, Images.expandCode_52, Images.expandCode_53, Images.expandCode_54, Images.expandCode_55, Images.expandCode_56, Images.expandCode_57, Images.expandCode_58, Images.expandCode_59, Images.expandCode_60, Images.expandCode_61, Images.expandCode_62, Images.expandCode_63, Images.expandCode_64, Images.expandCode_65, Images.expandCode_66, Images.expandCode_67, Images.expandCode_68, Images.expandCode_69, Images.expandCode_70, Images.expandCode_71, Images.expandCode_72, Images.expandCode_73, Images.expandCode_74, Images.expandCode_75, Images.expandCode_76, Images.expandCode_77, Images.expandCode_78, Images.expandCode_79, Images.expandCode_80, Images.expandCode_81, Images.expandCode_82, Images.expandCode_83, Images.expandCode_84, Images.expandCode_85, Images.expandCode_86, Images.expandCode_87, Images.expandCode_88, Images.expandCode_89, Images.expandCode_90, Images.expandCode_91, Images.expandCode_92, Images.expandCode_93, Images.expandCode_94, Images.expandCode_95, Images.expandCode_96, Images.expandCode_97, Images.expandCode_98, Images.expandCode_99, Images.expandCode_100, Images.expandCode_101, Images.expandCode_102, Images.expandCode_103, Images.expandCode_104, Images.expandCode_105, Images.expandCode_106, Images.expandCode_107, Images.expandCode_108, Images.expandCode_109, Images.expandCode_110, Images.expandCode_111, Images.expandCode_112, Images.expandCode_113, Images.expandCode_114, Images.expandCode_115, Images.expandCode_116, Images.expandCode_117, Images.expandCode_118, Images.expandCode_119, Images.expandCode_120, Images.expandCode_121, Images.expandCode_122, Images.expandCode_123, Images.expandCode_124, Images.expandCode_125, Images.expandCode_126, Images.expandCode_127, Images.expandCode_128, Images.expandCode_129, Images.expandCode_130, Images.expandCode_131, Images.expandCode_132, Images.expandCode_133, Images.expandCode_134, Images.expandCode_135, Images.expandCode_136, Images.expandCode_137, Images.expandCode_138, Images.expandCode_139, Images.expandCode_140, Images.expandCode_141, Images.expandCode_142, Images.expandCode_143, Images.expandCode_144, Images.expandCode_145, Images.expandCode_146, Images.expandCode_147, Images.expandCode_148, Images.expandCode_149, Images.expandCode_150, Images.expandCode_151, Images.expandCode_152, Images.expandCode_153, Images.expandCode_154, Images.expandCode_155, Images.expandCode_156, Images.expandCode_157, Images.expandCode_158, Images.expandCode_159, Images.expandCode_160, Images.expandCode_161, Images.expandCode_162, Images.expandCode_163, Images.expandCode_164, Images.expandCode_165, Images.expandCode_166, Images.expandCode_167]
private theorem chunks_ok : (chunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel
private theorem chunks_length : chunks.length = 168 := by rfl
private theorem chunks_new : expChunks = chunks.drop 4 := rfl
private theorem code_chunks : Images.expandCode = chunks.flatten := by
  change chunks.foldl (· ++ ·) [] = chunks.flatten
  rw [ClaudeWCT.W9.Machine.VLib.foldl_append_flatten, List.nil_append]
theorem wct_chunk_prefix {α : Type} (cs : List (List α)) (k : Nat) :
    cs.getD k [] <+: (cs.drop k).flatten := by
  induction cs generalizing k with
  | nil => simp
  | cons c cs ih =>
    cases k with
    | zero => exact ⟨cs.flatten, rfl⟩
    | succ k => simpa using ih k
theorem wct_newCodeAt : NewCodeAt Images.expandImage := by
  intro c hc
  have hlen := expChunks_len_le c hc
  have hp : expChunks.getD c [] <+: Images.expandCode.drop (256 * (c + 4)) := by
    rw [code_chunks, ClaudeWCT.W9.Machine.VLib.drop_chunks 256 chunks (c + 4) chunks_ok (by rw [chunks_length]; omega)]
    have hh := wct_chunk_prefix (chunks.drop 4) c
    rw [List.drop_drop] at hh
    rw [chunks_new]
    simpa [Nat.add_comm] using hh
  apply codeAt_slice (by omega)
  change List.take (expChunks.getD c []).length (Images.expandCode.drop (256 * (c + 4))) = _
  obtain ⟨rest, hrest⟩ := hp
  rw [← hrest, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
theorem wct_frontAt : ClaudeWCT.W9.Machine.Expand.FrontAt Images.expandImage :=
  ⟨wct_front0, ClaudeWCT.W9.Machine.Expand.codeAt_of_window wct_newCodeAt
    (by simp [ClaudeWCT.W9.Machine.Expand.zeroBlk]) (by decide +kernel)⟩
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000 in
theorem expChunks_full : ∀ c, c < 163 → (expChunks.getD c []).length = 256 := by decide +kernel
set_option maxRecDepth 100000 in
theorem expChunks_flatten_length : expChunks.flatten.length = 41753 := by decide +kernel
theorem drop_flatten_chunks : ∀ (L : List (List (BitVec 32))) (c : Nat), (∀ i, i < c → (L.getD i []).length = 256) →
    c ≤ L.length → L.flatten.drop (256 * c) = (L.drop c).flatten
  | L, 0, _, _ => by simp
  | [], c + 1, _, h => by simp at h
  | a :: L, c + 1, h, hl => by
    have ha : a.length = 256 := by simpa using h 0 (by omega)
    rw [List.flatten_cons, List.drop_append, List.drop_eq_nil_of_le (by rw [ha]; omega), List.nil_append, ha,
      show 256 * (c + 1) - 256 = 256 * c by ring_nf; omega,
      drop_flatten_chunks L c (fun i hi => by simpa using h (i + 1) (by omega)) (by simp at hl; omega)]
    rfl
theorem newCodeAt_of_drop {im : Image} (h : im.code.drop 1024 = expChunks.flatten) : NewCodeAt im := by
  intro c hc
  have hpc : (pcOf (256 * (c + 4))).toNat = 0x1000 + 4 * (256 * (c + 4)) := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen := expChunks_len_le c hc
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * (256 * (c + 4)) - 0x1000) / 4 = 1024 + 256 * c by omega, ← List.drop_drop, h,
    drop_flatten_chunks expChunks c (fun i hi => expChunks_full i (by omega)) (by rw [expChunks_length]; omega)]
  rw [List.drop_eq_getElem_cons (by rw [expChunks_length]; omega), List.flatten_cons,
    ← List.getD_eq_getElem _ [] (by rw [expChunks_length]; omega)]
  exact List.prefix_append _ _
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.ExpandLink
open SigGolfCandidate.T3M
def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
theorem v7_valid : I0.expand.Valid (ClaudeWCT.W9.T3M.submission I0).sizes (ClaudeWCT.W9.T3M.submission I0).layout :=
  submission_expand_valid
theorem v7_dataOK : ClaudeWCT.W9.Machine.Expand.ExpandDataOK I0.expand := Expand.wct_expandData
theorem expand_W_v7 :
    ClaudeWCT.W9.Machine.Expand.ExpandRefinesW (ClaudeWCT.W9.T3M.submission I0).image ∧
      ClaudeWCT.W9.Machine.Expand.ExpandTerminatesW (ClaudeWCT.W9.T3M.submission I0).image :=
  ClaudeWCT.W9.Machine.Expand.expandComposeSpec_holds _ v7_valid Expand.wct_newCodeAt Expand.wct_frontAt
    v7_dataOK Expand.wct_backSpec
end ClaudeWCT.W9.Machine.ExpandLink
end
end
