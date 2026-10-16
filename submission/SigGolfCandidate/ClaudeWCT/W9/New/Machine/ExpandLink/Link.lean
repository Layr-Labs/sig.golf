import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactRun
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Wit
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ComposeBack
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.H2Search
import SigGolfCandidate.ClaudeWCT.W9.T3M.Submission
import SigGolfCandidate.T3M.Submission
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending

set_option Elab.async false
set_option maxRecDepth 100000

section



namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap_const window_full window_zeros
  zeros wordsOf)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (regionBytes merkleBytes chainBytes leafBytes topBlockBytes authSibOff merkleBytes_length
  chainBytes_length region_merkle region_top merkleBytes_sib topBlock_sib authByte5_none window_map_range zeros_len)
open ClaudeWCT.W9.Machine.Expand (witListV6 wctBytesV6 wctBytesV6_length witListV6_length witListV5 wctBytesV5
  regionBytesV5 merkleBytesV5 merkleBytesV5_length regionBytesV6 regionBytesV6_length regionBytesV5_length
  wctBytesV5_length witListV5_length region_merkleV5 region_tailV5 merkleBytesV5_window wordsOf_getD headerBytesV5
  headerBytesV5_length)
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
  rw [window_append_left _ _ _ _ (by rw [headerBytesV5_length]; omega),
    window_append_left _ _ _ _ (by rw [headerBytesV5_length]; omega)]
theorem witList_tail (o : Nat) (h : 8128 ≤ o) :
    window (witListV6 N w) o 8 = window (witListV5 N w) (o + 1152) 8 := by
  unfold witListV6 witListV5
  simp only [List.append_assoc]
  rw [window_append_right (headerBytesV5 w) _ _ _ (by rw [headerBytesV5_length]; omega),
    window_append_right (headerBytesV5 w) _ _ _ (by rw [headerBytesV5_length]; omega), headerBytesV5_length,
    window_append_right (wctBytesV6 N w.signature) _ _ _ (by rw [wctBytesV6_length]; omega),
    window_append_right (wctBytesV5 N w.signature) _ _ _ (by rw [wctBytesV5_length]; omega), wctBytesV6_length,
    wctBytesV5_length,
    show o + 1152 - 64 - 9216 = o - 64 - 8064 by omega]
theorem witList_region (k : Nat) (hk : k < 9) (j : Nat) (hj : j + 8 ≤ 896) :
    window (witListV6 N w) (64 + 896 * k + j) 8 =
      window (regionBytesV6 (WCT9.child N ⟨k, hk⟩).val (w.signature.openings ⟨k, hk⟩)) j 8 := by
  unfold witListV6
  simp only [List.append_assoc]
  rw [window_append_right _ _ _ _ (by rw [headerBytesV5_length]; omega), headerBytesV5_length,
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
  rw [window_append_right _ _ _ _ (by rw [headerBytesV5_length]; omega), headerBytesV5_length,
    window_append_left _ _ _ _ (by rw [wctBytesV5_length]; omega),
    show 64 + 1024 * k + j - 64 = 1024 * k + j by omega]
  unfold wctBytesV5
  rw [window_flatMap_const _ _ 1024 (fun k => regionBytesV5_length _ _) k (by simp; omega) j 8 hj]
  simp
end
section
variable (c : Nat) (op : WCT9.Opening)
/-- The staging region and the scratch region share the chain/leaf block (512 bytes). -/
def midBlock : List UInt8 := chainBytes op ++ zeros 48 ++ leafBytes op (zeros 16) ++ zeros 16
theorem midBlock_length : (midBlock op).length = 512 := by
  unfold midBlock
  rw [List.length_append, List.length_append, List.length_append, chainBytes_length,
    ClaudeWCT.W9.T3M.leafBytes_length _ _ (zeros_len 16), zeros_len, zeros_len]
theorem v6_mid : regionBytesV6 c op = merkleBytes c op ++ (midBlock op ++ topBlockBytes c op (zeros 16)) := by
  simp only [regionBytesV6, regionBytes, midBlock, List.append_assoc]
theorem v5_mid : regionBytesV5 c op = merkleBytesV5 c op ++ (midBlock op ++ zeros 64) := by
  simp only [regionBytesV5, midBlock, List.append_assoc]
  congr 4
theorem region_tail (o : Nat) (h0 : 320 ≤ o) (h : o + 8 ≤ 832) :
    window (regionBytesV6 c op) o 8 = window (regionBytesV5 c op) (o + 128) 8 := by
  rw [v6_mid, v5_mid, window_append_right (merkleBytes c op) _ _ _ (by rw [merkleBytes_length]; omega),
    merkleBytes_length,
    window_append_right (merkleBytesV5 c op) _ _ _ (by rw [merkleBytesV5_length]; omega), merkleBytesV5_length,
    window_append_left (midBlock op) (topBlockBytes c op (zeros 16)) _ _ (by rw [midBlock_length]; omega),
    window_append_left (midBlock op) (zeros 64) _ _ (by rw [midBlock_length]; omega),
    show o + 128 - 448 = o - 320 by omega]
theorem region_merkle6 (o : Nat) (h : o + 8 ≤ 320) :
    window (regionBytesV6 c op) o 8 = window (merkleBytes c op) o 8 := by
  unfold regionBytesV6
  exact region_merkle _ _ _ _ o 8 h
theorem region_top6 (o : Nat) (h0 : 832 ≤ o) :
    window (regionBytesV6 c op) o 8 = window (topBlockBytes c op (zeros 16)) (o - 832) 8 := by
  unfold regionBytesV6
  exact region_top _ _ _ _ (zeros_len 16) o 8 h0
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
theorem sib_window (hc : c < 128) (l : Nat) (hl : l < 5) (a : Nat) (ha : a + 8 ≤ 16) :
    window (merkleBytes c op) (authSibOff c l + a) 8 = window (merkleBytesV5 c op) (srcOff c l + a) 8 := by
  rw [← window_window _ _ 16 _ _ ha, ← window_window _ _ 16 _ _ ha,
    merkleBytes_sib hc op ⟨l, hl⟩, merkleV5_sib c op ⟨l, by omega⟩]
  rfl
theorem sib5_window (a : Nat) (ha : a + 8 ≤ 16) :
    window (topBlockBytes c op (zeros 16)) (SigGolfCandidate.T3M.sibOff (c / 2 ^ 5 % 2) + a) 8 =
      window (merkleBytesV5 c op) (srcOff c 5 + a) 8 := by
  rw [← window_window _ _ 16 _ _ ha, ← window_window _ _ 16 _ _ ha,
    topBlock_sib _ _ _ (zeros_len 16), merkleV5_sib c op ⟨5, by omega⟩]
  rfl
theorem merkle_none (hc : c < 128) (j : Nat) (hj : j < 40) (h : sibSrc c j = none) :
    window (merkleBytes c op) (8 * j) 8 = zeros 8 := by
  have hn : ∀ l < 6, authSibOff c l ≠ 8 * j ∧ authSibOff c l + 8 ≠ 8 * j := by
    intro l hl
    unfold sibSrc sibLev at h
    rw [Option.map_eq_none_iff] at h
    have := find_none h l hl
    simp only [decide_eq_false_iff_not, not_or] at this
    exact this
  unfold merkleBytes
  rw [window_map_range _ _ _ _ (by omega)]
  rw [List.map_congr_left (fun i hi => authByte5_none op (fun l => by
    have hi' := List.mem_range.mp hi
    have h16 := authSibOff_ok c hc l.val l.isLt
    have := hn l.val (by omega)
    omega))]
  simp [zeros, List.map_const']
/-- Top-block words of the staging region that are not the level-5 sibling are zero. -/
theorem top_zero (o : Nat) (h0 : 832 ≤ o) (h1 : o + 8 ≤ 896) (h8 : o % 8 = 0)
    (hn : o ≠ authSibOff c 5 ∧ o ≠ authSibOff c 5 + 8) : window (regionBytesV6 c op) o 8 = zeros 8 := by
  rw [region_top6 c op o h0]
  rw [authSibOff_five c] at hn
  have hb : c / 2 ^ 5 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold topBlockBytes
  rcases (show c / 2 ^ 5 % 2 = 0 ∨ c / 2 ^ 5 % 2 = 1 by omega) with hb | hb
  · rw [if_neg (show ¬ c / 2 ^ 5 % 2 = 1 by omega), if_pos hb,
      window_append_left _ _ _ _ (by simp only [List.length_append, zeros_len]; omega)]
    simp only [zeros, List.replicate_append_replicate]
    exact window_zeros _ _ _ (by omega)
  · rw [if_pos hb, if_neg (show ¬ c / 2 ^ 5 % 2 = 0 by omega), List.append_assoc, List.append_assoc,
      window_append_right _ _ _ _ (by rw [bytesLE_length]; omega), bytesLE_length]
    simp only [zeros, List.replicate_append_replicate]
    exact window_zeros _ _ _ (by omega)
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
  cases h : sibSrc (N.toNat / 2 ^ WCT9.childBase k % 128) j with
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
      obtain ⟨hl6, hp⟩ := find_some hl
      simp only [decide_eq_true_eq] at hp
      by_cases h5 : l < 5
      · have hb := authSibOff_ok _ hcl l h5
        rw [region_merkle6 _ _ _ (by omega)]
        by_cases h0 : authSibOff (N.toNat / 2 ^ WCT9.childBase k % 128) l = 8 * j
        · rw [if_pos h0] at h
          subst h
          have := sib_window _ (w.signature.openings ⟨k, hk⟩) hcl l h5 0 (by norm_num)
          rw [Nat.add_zero, Nat.add_zero, h0] at this
          rw [this]
        · rw [if_neg h0] at h
          subst h
          have := sib_window _ (w.signature.openings ⟨k, hk⟩) hcl l h5 8 (by norm_num)
          rw [show authSibOff (N.toNat / 2 ^ WCT9.childBase k % 128) l + 8 = 8 * j by omega] at this
          rw [this]
      · obtain rfl : l = 5 := by omega
        have h5' := authSibOff_five (N.toNat / 2 ^ WCT9.childBase k % 128)
        have hso : SigGolfCandidate.T3M.sibOff ((N.toNat / 2 ^ WCT9.childBase k % 128) / 2 ^ 5 % 2) =
            48 * (1 - (N.toNat / 2 ^ WCT9.childBase k % 128) / 2 ^ 5 % 2) := by
          unfold SigGolfCandidate.T3M.sibOff
          have : (N.toNat / 2 ^ WCT9.childBase k % 128) / 2 ^ 5 % 2 < 2 := Nat.mod_lt _ (by norm_num)
          split <;> omega
        rw [region_top6 _ _ _ (by omega)]
        by_cases h0 : authSibOff (N.toNat / 2 ^ WCT9.childBase k % 128) 5 = 8 * j
        · rw [if_pos h0] at h
          subst h
          have := sib5_window (N.toNat / 2 ^ WCT9.childBase k % 128) (w.signature.openings ⟨k, hk⟩) 0 (by norm_num)
          rw [Nat.add_zero, Nat.add_zero, hso, show 48 * (1 - (N.toNat / 2 ^ WCT9.childBase k % 128) / 2 ^ 5 % 2) =
            8 * j - 832 by omega] at this
          rw [this]
        · rw [if_neg h0] at h
          subst h
          have := sib5_window (N.toNat / 2 ^ WCT9.childBase k % 128) (w.signature.openings ⟨k, hk⟩) 8 (by norm_num)
          rw [hso, show 48 * (1 - (N.toNat / 2 ^ WCT9.childBase k % 128) / 2 ^ 5 % 2) + 8 = 8 * j - 832 by omega]
            at this
          rw [this]
  | none =>
    simp only
    by_cases hj40 : j < 40
    · rw [if_pos hj40, region_merkle6 _ _ _ (by omega), merkle_none _ _ hcl j hj40 h]
      rfl
    rw [if_neg hj40]
    beta_reduce
    rw [show (0x840 + 1024 * k + 448 + 8 * (j - 40) - 0x800) / 8 = 8 + 128 * k + (j + 16) by omega,
      wordsOf_getD _ 2873 (by omega) _ (by omega),
      show 8 * (8 + 128 * k + (j + 16)) = 64 + 1024 * k + (8 * j + 128) by ring,
      witListV5_region N w k hk _ (by omega), hcv]
    by_cases h104 : j < 104
    · rw [region_tail _ _ _ (by omega) (by omega)]
    · have hn : ∀ l < 6, authSibOff (N.toNat / 2 ^ WCT9.childBase k % 128) l ≠ 8 * j ∧
          authSibOff (N.toNat / 2 ^ WCT9.childBase k % 128) l + 8 ≠ 8 * j := by
        intro l hl
        unfold sibSrc sibLev at h
        rw [Option.map_eq_none_iff] at h
        have := find_none h l hl
        simp only [decide_eq_false_iff_not, not_or] at this
        exact this
      have h5 := hn 5 (by omega)
      rw [top_zero _ _ (8 * j) (by omega) (by omega) (by omega) ⟨fun e => h5.1 e.symm, fun e => h5.2 e.symm⟩,
        region_tailV5 _ _ _ _ (by omega) (by omega)]
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
  split_ifs
  · rfl
  · split
    · rename_i j hj
      exact h j (List.mem_range.mp (List.mem_of_find?_eq_some hj))
    · rfl
theorem out2old_congr (M M' : Nat → Word) (h : ∀ x < 8 * 2729, x % 8 = 0 → M (WIT + x) = M' (WIT + x))
    (idx o : Nat) (ho : o % 8 = 0) : out2old M idx o = out2old M' idx o := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  have e : ∀ A, WIT ≤ A → A - WIT < 8 * 2729 → (A - WIT) % 8 = 0 → M A = M' A := fun A h1 h2 h3 => by
    have := h (A - WIT) h2 h3
    rwa [show WIT + (A - WIT) = A by omega] at this
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  have hz : (zoneLay o = 1 ∧ o < 14800) ∨ (zoneLay o = 2 ∧ 14800 ≤ o ∧ o < 17872) ∨
      (zoneLay o = 3 ∧ 17872 ≤ o) := by
    unfold zoneLay; split_ifs <;> omega
  have hzl : 1 ≤ zoneLay o ∧ zoneLay o < 4 := by omega
  have hpt : pathTop (zoneLay o) ≤ 400 := by unfold pathTop; split_ifs <;> omega
  have hch : chSrc (zoneLay o) - SNAP2 + (o - (chDst (zoneLay o) - WIT)) + 8 ≤ 8 * 2729 ∨ ¬ o < 20944 := by
    unfold chSrc
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> simp only [hz] at * <;> norm_num <;> omega
  have hch8 : (chSrc (zoneLay o) - SNAP2 + (o - (chDst (zoneLay o) - WIT))) % 8 = 0 := by
    unfold chSrc
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> simp only [hz] at * <;> norm_num <;> omega
  have hdl : (lvDst (zoneLay o) - WIT) % 8 = 0 := by
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> omega
  have hcs : SNAP2 ≤ chSrc (zoneLay o) := by unfold chSrc; omega
  unfold out2old
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
theorem plMem_congr (R R' : Nat → Word) (Q : Nat) (A : Nat) (hA : R A = R' A)
    (hH : ∀ c < Q, R (Compact.holdAt c) = R' (Compact.holdAt c) ∧
      R (Compact.holdAt c + 8) = R' (Compact.holdAt c + 8) ∧ R (Compact.holdAt c + 16) = R' (Compact.holdAt c + 16)) :
    plMem R Q A = plMem R' Q A := by
  induction Q with
  | zero => exact hA
  | succ Q ih =>
    obtain ⟨h0, h8, h16⟩ := hH Q (by omega)
    have hs : hslot R Q = hslot R' Q := by unfold hslot; rw [h16]
    simp only [plMem]
    rw [hs, h0, h8, ih (fun c hc => hH c (by omega))]
/-- The final assembly below offset 8160 reads its input only at the staging words and the hold words. -/
theorem stMem_congr (M M' : Nat → Word) (h : ∀ x < 8 * 2729, x % 8 = 0 → M (WIT + x) = M' (WIT + x))
    (hH : ∀ c < 9, ∀ j < 3, M (Compact.holdAt c + 8 * j) = M' (Compact.holdAt c + 8 * j))
    (o : Nat) (ho : o < 8160) (h8 : o % 8 = 0) : stMem M (WOUT + o) = stMem M' (WOUT + o) := by
  have hW : WIT = 0x800 := rfl
  have hWO : WOUT = 0x520 := rfl
  have hWZ : WZ = 0x4c0 := rfl
  unfold stMem
  apply plMem_congr
  · rw [R_eval M _ (by omega) (by omega) (by omega), R_eval M' _ (by omega) (by omega) (by omega)]
    split_ifs
    · exact h _ (by omega) (by omega)
    · exact h _ (by omega) (by omega)
    · rfl
  · intro c hc
    refine ⟨?_, ?_, ?_⟩
    · rw [show Compact.holdAt c = Compact.holdAt c + 0 from rfl, R_hold M c hc 0 (by omega),
        R_hold M' c hc 0 (by omega)]
      exact hH c hc 0 (by omega)
    · rw [R_hold M c hc 8 (by omega), R_hold M' c hc 8 (by omega)]
      exact hH c hc 1 (by omega)
    · rw [R_hold M c hc 16 (by omega), R_hold M' c hc 16 (by omega)]
      exact hH c hc 2 (by omega)
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
  /-- C4: the top-path plan tables of the post-pass. -/
  toptab : Compact2.TopTabAt s
/-- Nested FTS (r1-1): jump 1 + staging 23576 + final assembly 42535 + leaf buffers 2672 (C2 + C3 FULL: the three
root-level trampolines add 4 steps each to the final assembly, the E6 footer trampoline 4 to the leaf buffers)
+ C4 top-path post-pass 549 (hook 1, gather 159, zeroing 292, table 11, placement 84, finish 2). -/
def compactC : Nat := 69333
def CompactGood (im : Image) : Prop :=
  NewCodeAt im → CodeAt im (pcOf 351) [compactJal] → ∀ N w s, CompactPre N w s →
    ∃ t, Steps im s compactC compactC t ∧ t.pc = pcOf 43763 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧
      -- Witness trim: above the 80-byte header only (the compactor's header words are scratch-shifted).
      ∀ i, 10 ≤ i → i < 3104 →
        t.getMem (BitVec.ofNat 64 (1312 + 8 * i)) = (wordsOf (ClaudeWCT.W9.T3M.witList N w)).getD i 0
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
    · cases hs : sibSrc (cs ((i - 8) / 112)) ((i - 8) % 112) with
      | some o =>
        have := sibSrc_lt hs
        simp only
        rw [show 0x840 + 1024 * ((i - 8) / 112) + o = 0x800 + 8 * (8 + 128 * ((i - 8) / 112) + o / 8) by omega]
        exact h _ (by omega)
      | none =>
        simp only
        split
        · rfl
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
  obtain ⟨v, sv, pv, rv, mv, mhv, fv⟩ := Compact.run_spec (CompactCodeAt.ofNew hc) N u pu hNu hpu
  have hix : v.getMem (BitVec.ofNat 64 0x60) >>> 33 = BitVec.ofNat 64 (WCT9.digestIndex N) := by
    rw [fv 0x60 (by norm_num) (Or.inl (by norm_num)) (by unfold Compact.InHold; omega)]
    have h0 := hNu 0 (by norm_num)
    rw [show (0x60 : Nat) + 8 * 0 = 0x60 from rfl] at h0
    rw [h0]
    exact Compact2.index_shr N
  have hlv : Compact2.LPlanAt v := fun k hk => by
    rw [fv _ (by omega) (Or.inr (by omega)) (by unfold Compact.InHold; omega), fu _ (by omega) (fun h => h)]
    exact hpre.lplan k hk
  have htv : Compact2.TopTabAt v := by
    have hT : Compact2.TOPA = 0xfffb80 ∧ Compact2.TOPB = 0xfffd80 := ⟨rfl, rfl⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [fv _ (by omega) (Or.inr (by omega)) (by unfold Compact.InHold; omega), fu _ (by omega) (fun h => h)]
      exact hpre.toptab.1 k hk
    · rw [fv _ (by omega) (Or.inr (by omega)) (by unfold Compact.InHold; omega), fu _ (by omega) (fun h => h)]
      exact hpre.toptab.2 k hk
  have hW5 : ∀ i' < 2873, s.getMem (BitVec.ofNat 64 (0x800 + 8 * i')) = (wordsOf (witListV5 N w)).getD i' 0 := by
    intro i' hi'
    rw [← hpre.wit, VLib.readWords_ofNat s 0x800 2873 (by norm_num)]
    simp [List.getD_eq_getElem?_getD, hi']
  -- the hold words: coordinate c's top sibling (from its scratch region) and the flag 1 - bit6
  have hvH : ∀ c < 9, ∀ j < 3, v.getMem (BitVec.ofNat 64 (Compact.holdAt c + 8 * j)) =
      Compact2.vM N w (Compact.holdAt c + 8 * j) := by
    intro c hc9 j hj
    rw [mhv c hc9 j hj, Compact2.vM_hold N w c hc9 j hj]
    unfold Compact.holdVal Compact2.holdModel
    rw [dif_pos hc9]
    have hcv : (WCT9.child N ⟨c, hc9⟩).val = N.toNat / 2 ^ WCT9.childBase c % 128 := rfl
    have hso := Compact.srcOff_bound (N.toNat / 2 ^ WCT9.childBase c % 128) 6
    have hsib : ∀ a, (a = 0 ∨ a = 8) → u.getMem (BitVec.ofNat 64
        (0x840 + 1024 * c + Compact.srcOff (N.toNat / 2 ^ WCT9.childBase c % 128) 6 + a)) =
        BitVec.ofNat 64 (SigGolfCandidate.T3.readLE (window (SphincsSecurity.bytesLE 16
          ((w.signature.openings ⟨c, hc9⟩).path 6)) a 8)) := by
      intro a ha8
      have ha : a + 8 ≤ 16 := by omega
      have hal : (Compact.srcOff (N.toNat / 2 ^ WCT9.childBase c % 128) 6 + a) % 8 = 0 := by
        rcases ha8 with rfl | rfl <;> omega
      rw [fu _ (by omega) (fun h => h),
        show 0x840 + 1024 * c + Compact.srcOff (N.toNat / 2 ^ WCT9.childBase c % 128) 6 + a =
          0x800 + 8 * (8 + 128 * c + (Compact.srcOff (N.toNat / 2 ^ WCT9.childBase c % 128) 6 + a) / 8) by omega,
        hW5 _ (by omega), wordsOf_getD _ 2873 (by rw [witListV5_length]) _ (by omega),
        show 8 * (8 + 128 * c + (Compact.srcOff (N.toNat / 2 ^ WCT9.childBase c % 128) 6 + a) / 8) =
          64 + 1024 * c + (Compact.srcOff (N.toNat / 2 ^ WCT9.childBase c % 128) 6 + a) by omega,
        Compact.witListV5_region N w c hc9 _ (by omega), hcv, region_merkleV5 _ _ _ _ (by omega),
        ← Compact.window_window _ _ 16 _ _ ha, Compact.merkleV5_sib _ _ ⟨6, by omega⟩]
      rfl
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · rw [if_pos rfl, if_pos rfl]
      beta_reduce
      have := hsib 0 (Or.inl rfl)
      rw [Nat.add_zero] at this
      exact this
    · rw [if_neg (show ¬ (1 : Nat) = 0 by decide), if_pos rfl, if_neg (show ¬ (1 : Nat) = 0 by decide), if_pos rfl]
      beta_reduce
      exact hsib 8 (Or.inr rfl)
    · rw [if_neg (show ¬ (2 : Nat) = 0 by decide), if_neg (show ¬ (2 : Nat) = 1 by decide),
        if_neg (show ¬ (2 : Nat) = 0 by decide), if_neg (show ¬ (2 : Nat) = 1 by decide), hcv]
  have hfl : ∀ c < 9, ∃ f < 2, v.getMem (BitVec.ofNat 64 (Compact.holdAt c + 16)) = BitVec.ofNat 64 f := by
    intro c hc9
    refine ⟨1 - (WCT9.child N ⟨c, hc9⟩).val / 2 ^ 6 % 2, by omega, ?_⟩
    rw [show Compact.holdAt c + 16 = Compact.holdAt c + 8 * 2 by omega, hvH c hc9 2 (by omega),
      Compact2.vM_hold N w c hc9 2 (by omega)]
    unfold Compact2.holdModel
    rw [dif_pos hc9, if_neg (show ¬ (2 : Nat) = 0 by decide), if_neg (show ¬ (2 : Nat) = 1 by decide)]
  obtain ⟨t, st, pt, mt⟩ := Compact2.run2_spec (CompactCodeAt.ofNew hc) v pv (WCT9.digestIndex N) (WCT9.digestIndex_lt N) hix hlv hfl
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
  have hvM : ∀ x < 8 * 2729, x % 8 = 0 →
      v.getMem (BitVec.ofNat 64 (Compact2.WIT + x)) = Compact2.vM N w (Compact2.WIT + x) := fun x hx h8 => by
    rw [hv6 x hx h8, Compact2.vM_wit N w x hx]
  have hpreWords : ∀ i < 2714, (8 * i < 8160 ∨ 8928 ≤ 8 * i) → t.getMem (BitVec.ofNat 64 (1312 + 8 * i)) =
      (wordsOf (Compact2.preBufferWitList N w)).getD i 0 := by
    intro i hi hnt
    rw [mt _ (by omega), show 1312 + 8 * i = Compact2.WOUT + 8 * i from rfl,
      Compact2.run2_zone _ _ _ (by omega) (by omega), Compact2.compact2_words N w i hi hnt]
    unfold Compact2.out2
    by_cases hl : 8 * i < 8160
    · rw [if_pos hl, if_pos hl]
      exact Compact2.stMem_congr _ _ hvM hvH _ hl (by omega)
    · rw [if_neg hl, if_neg hl]
      exact Compact2.out2old_congr _ _ hv6 _ _ (by omega)
  -- C4: the old-layout top path area (re-placed by the post-pass)
  have hold : ∀ q < 96, t.getMem (BitVec.ofNat 64 (9472 + 8 * q)) =
      BitVec.ofNat 64 (SigGolfCandidate.T3.readLE (window (ClaudeWCT.W9.Machine.Expand.layerRegionV6 N w 0) (8 * q) 8)) := by
    intro q hq
    rw [mt _ (by omega), show 9472 + 8 * q = Compact2.WOUT + (8160 + 8 * q) by unfold Compact2.WOUT; omega,
      Compact2.run2_zone _ _ _ (by omega) (by omega)]
    unfold Compact2.out2
    rw [if_neg (by omega), Compact2.out2old_congr _ _ hv6 _ _ (by omega),
      show 8160 + 8 * q - 736 = 8 * (1020 + q) - 736 by omega,
      Compact2.compact2_top_old N w (1020 + q) (by omega) (by omega), show 8 * (1020 + q) - 8160 = 8 * q by omega]
  have htt : Compact2.TopTabAt t := by
    have hT : Compact2.TOPA = 0xfffb80 ∧ Compact2.TOPB = 0xfffd80 := ⟨rfl, rfl⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [mt _ (by omega), Compact2.run2Mem_out _ _ _ (Or.inr (by unfold Compact2.SNAP2; omega))]
      exact htv.1 k hk
    · rw [mt _ (by omega), Compact2.run2Mem_out _ _ _ (Or.inr (by unfold Compact2.SNAP2; omega))]
      exact htv.2 k hk
  have hleaf : (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2 ^ 19 := by
    have := WCT9.digestIndex_lt N
    have h1 : (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2 ^ 19 % 2 ^ 12 := rfl
    rw [h1]; omega
  have hix52 : t.getMem (BitVec.ofNat 64 96) >>> 52 = BitVec.ofNat 64 (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 := by
    have h96 : t.getMem (BitVec.ofNat 64 96) = v.getMem (BitVec.ofNat 64 0x60) := by
      rw [mt _ (by omega), Compact2.run2Mem_out _ _ _ (Or.inl (by unfold Compact2.WZ; omega))]
    rw [h96, show (52 : Nat) = 33 + 19 from rfl, BitVec.shiftRight_add, hix, hleaf,
      SigGolfCandidate.T3M.ofNat_shr _ _ (by have := WCT9.digestIndex_lt N; omega)]
  have hl4 : (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 < 4096 := by
    rw [hleaf]; have := WCT9.digestIndex_lt N; omega
  obtain ⟨q, sq, pq, q5, q10, mq⟩ := Compact2.Buffer.bufferPost_spec hc t pt _ hl4 hix52 htt
  refine ⟨q, (((su.trans sv).trans st).trans sq).of_eq (by unfold compactC; norm_num)
    (by unfold compactC; norm_num), pq, q5, q10, ?_⟩
  intro i hh hi
  rw [mq (1312 + 8 * i) (by omega) (by unfold Compact2.Buffer.Post.SCR; omega)]
  exact Compact2.postMem_words N w (fun A => t.getMem (BitVec.ofNat 64 A)) hpreWords hold i hi hh

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
  (∀ (sk : BitVec 256) (sig : WCT9.Signature) (index : Nat) (L R : Digest) (s : MachineState),
    LInv sig index 4 (.pair L R) s →
      TBSim im sk s (lcost 4) (WCT9.expandLayersT sig index (WCT9.topSib sig) 4 (.pair L R))
        (LPost s sig index 4 0)) ∧
  CodeAt im (pcOf 342) compareCode ∧ KernAt im 354
def ExpandComposeSpec : Prop :=
  ∀ imgs : Phase → Image, (imgs .expand).Valid (w9Sub imgs).sizes (w9Sub imgs).layout →
    NewCodeAt (imgs .expand) → FrontAt (imgs .expand) → ProAt (imgs .expand) → SrchAt (imgs .expand) →
    ExpandDataOK (imgs .expand) → BackSpec (imgs .expand) → ExpandRefinesW imgs ∧ ExpandTerminatesW imgs
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
  | some (N, w), t => t.pc = pcOf 43763 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 0 ∧
      ∀ i, 10 ≤ i → i < 3104 →
        t.getMem (BitVec.ofNat 64 (1312 + 8 * i)) = (wordsOf (ClaudeWCT.W9.T3M.witList N w)).getD i 0
/-- [h2 lane] prologue 1199 + front 29 + zero block 7, then the layers, the 2^16 search and the compaction. -/
def expCostW : Nat := 1235 + newCost + (lcost 4 + (65535 * 30 + 111 + compactC))
theorem lcost_four : lcost 4 ≤ 3523312730 := by decide
theorem expCostW_le : expCostW ≤ 3944879859 := by
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
set_option maxRecDepth 10000 in
/-- [h2 lane] the H2 expander on the compact signature `b`: prologue (un-shift) -> the record's front and zero block
-> layers (exposing the top level-11 node) -> candidate search -> the record's compaction and witness. -/
theorem expandW_tbsim {im : Image} (hc : NewCodeAt im) (hF : FrontAt im) (hP : ProAt im) (hS : SrchAt im)
    (hd : ExpandDataOK im) (hB : BackSpec im) (m : Message) (pk : PublicKey) (b : Bytes 5310) :
    TBSim im sk (w9init im m pk b) expCostW (ClaudeWCT.W9.T3M.expandN m pk (ClaudeWCT.W9.T3M.sigDecC b)) ExpQW := by
  set σ := sigFull b with hσ
  have hsigσ : sigDec σ = ClaudeWCT.W9.T3M.sigDecC b := sigDec_sigFull b
  have hproj : WCT9.proj (sigDec σ) = sigDec σ := by rw [hsigσ]; exact ClaudeWCT.W9.T3M.proj_sigDecC b
  rw [← hsigσ, expandN_splitS m pk _ hproj]
  set sig := sigDec σ with hsig
  set s0 := w9init im m pk σ with hs0
  obtain ⟨u, stu, pu, ru, m70, m78, mmv, fu⟩ := prologue_spec hP (w9init im m pk b) (w9initC_pc m pk b)
    (fun r hr => w9init_regs0 hd m pk b r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
  have humem := prologue_mem hd m pk b u m70 m78 mmv fu
  obtain ⟨t1, st1, hpre, hmz, w800, w808, f1⟩ := front_pre30' hF hP hd m pk σ u pu
    (by rw [ru]; exact w9init_regs0 hd m pk b .x5 (by decide)) humem
  have hz0 : ∀ A, A < Compact2.LPLAN → (A < 0x7000 ∨ 0x7000 + 5312 ≤ A) → (A < 0xA0 ∨ 0xB0 ≤ A) →
      (A < 0x6620 ∨ 0x6640 ≤ A) → s0.getMem (BitVec.ofNat 64 A) = 0 := fun A hA h1 h2 h3 =>
    w9init_zero hd m pk σ A hA ⟨h1, h2, by omega⟩
  have hz0' : ∀ A, A < Compact2.LPLAN → (A < 0x7000 ∨ 0x7000 + 5312 ≤ A) → (A < 0xA0 ∨ 0xB0 ≤ A) →
      ¬ (0x6620 ≤ A ∧ A < 0x6640 ∧ (A - 0x6620) % 8 = 0) → s0.getMem (BitVec.ofNat 64 A) = 0 :=
    fun A hA h1 h2 h3 => w9init_zero hd m pk σ A hA ⟨h1, h2, h3⟩
  unfold Compact2.LPLAN at hz0 hz0'
  have hCC : compactC = 69333 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  refine (TBSim.steps (stu.trans st1) (TBSim.bind (W₂ := lcost 4 + (65535 * 30 + 111 + compactC))
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
      (A < NBUF ∨ NBUF + 32 ≤ A) → A ≠ IDXV → A ≠ ENC → A ≠ ENC + 8 → (A < ENC + 48 ∨ ENC + 64 ≤ A) →
      ¬ NewW A := by
    intro A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h
    unfold NewW at h; simp only [DIG, NBUF, IDXV, ENC] at h h7 h8 h9 h10 h11 h12; omega
  have z7 : ∀ A, A < 0x6620 → (A < 0x60 ∨ 0x80 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) → (A < 0x400 ∨ 0x550 ≤ A) →
      (A < 0x800 ∨ 0x818 ≤ A) → (A < 0x840 ∨ 0x2c48 ≤ A) → (A < 0xA0 ∨ 0xB0 ≤ A) → (A < 0x59B0 ∨ 0x59D0 ≤ A) →
      t7.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A h0 h1 h2 h3 h4 h4' h5 h6
    rw [g7 A (by omega) (nFW _ (by omega) (by simp only [DIG]; omega) h6)
      (nNW _ (by omega) h1 h2 h3 h4' (by omega) (by simp only [DIG]; omega) (by simp only [NBUF]; omega)
        (by simp only [IDXV]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)
        (by simp only [ENC]; omega)),
      hz0 _ (by omega) (by omega) h5 (by omega)]
  have z7h : ∀ A, 0x20000 ≤ A → A < 0x30000 → A ≠ ENC → A ≠ ENC + 8 → (A < DIG ∨ DIG + 64 ≤ A) →
      (A < NBUF ∨ NBUF + 32 ≤ A) → A ≠ IDXV → (A < ENC + 48 ∨ ENC + 64 ≤ A) → t7.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A h0 h1 h2 h3 h4 h5 h6 h7
    rw [g7 A (by omega) (nFW _ (by omega) h4 (by omega))
      (nNW _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [DIG] at h4 ⊢; omega)
        h5 h6 h2 h3 h7),
      hz0 _ (by omega) (by omega) (by omega) (by omega)]
  have hL : LInv sig index 4 (.pair root.1 root.2) t7 := by
    refine ⟨by rw [P.pc]; rfl, le_refl _, P.x5, hi, P.idx, P.enc, fun _ => P.right, fun h => absurd h (by decide),
      ⟨0, by norm_num, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [z7h _ (by simp only [ENC]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)
        (by simp only [ENC]; omega) (by simp only [DIG, ENC]; omega) (by simp only [NBUF, ENC]; omega)
        (by simp only [IDXV, ENC]; omega) (by simp only [ENC]; omega)]; rfl
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
          (by simp only [CHAIN, Search.NODE, LEAFPK, ENC, IDXV]; omega)
          (by simp only [CHAIN, Search.NODE, LEAFPK, ENC]; omega)]
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
    · apply (w9init_reward hd m pk σ).frame F7
      intro i hi hi' h
      rcases h with h | h
      · unfold FrontW at h; simp only [TOP_DATA, DIG] at h; omega
      · unfold NewW at h; simp only [TOP_DATA, DIG, NBUF, IDXV, ENC] at h; omega
  simp only [tailProgS]
  refine (TBSim.bind (W₂ := 65535 * 30 + 111 + compactC) (hB.1 sk sig index root.1 root.2 t7 hL) (fun r8 t8 h8 => ?_)).mono
    (by omega) (fun _ _ h => h)
  rcases r8 with _ | ⟨v, root', counters⟩
  · exact (TBSim.pure (Q := ExpQW) (a := none) (Or.inl h8)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p8, x5_8, e8, hlen8, hout8, hhf8, r8, f8, _, htop8⟩ := h8
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
        (by simp only [ENC]; omega) (by simp only [ENC]; omega))]
    exact w9init_pk hd m pk σ j hj
  -- [h2 lane] after the layers: the search from word 342, then the witness at the halt
  have nLWX : ¬ LW index 4 0x20550 := by
    intro h
    rcases h with h | h | ⟨lay, _, h | h⟩
    · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch, SigGolfCandidate.T3M.Expand.RlScratch, CHAIN, Search.NODE,
        Search.NOUT, LEAFPK, ENC] at h; omega
    · rcases lD_cases lay with e | e | e | e <;> omega
    · have := rlWit_range h; have := ltable lay; omega
  have hix : t8.getMem (BitVec.ofNat 64 0x20550) = BitVec.ofNat 64 index := by
    rw [g87 _ (by decide) nLWX]; exact hL.idx
  have hsib : WCT9.setTop (WCT9.topSib sig) 0 = WCT9.topSib sig := by
    rw [← WCT9.topSib_fillTop]; exact congrArg WCT9.topSib hproj
  have hblk := topBlk_get sig index v t8 (htop8 (by decide))
  have hpk0 : t8.getMem (BitVec.ofNat 64 0xA0) = lo64 pk := hpk 0 (by decide)
  have hpk1 : t8.getMem (BitVec.ofNat 64 0xA8) = hi64 pk := hpk 1 (by decide)
  set w : WCT9.Witness := ⟨sig, counter, fun lay => counters.getD lay.val 0⟩ with hw
  have nLWp : ∀ A, 0xff0000 ≤ A → ¬ LW index 4 A := by
    intro A hA h
    rcases h with h | h | ⟨lay, _, h | h⟩
    · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch, SigGolfCandidate.T3M.Expand.RlScratch, CHAIN,
        Search.NODE, Search.NOUT, LEAFPK, ENC] at h; omega
    · have := ltable lay; omega
    · have := rlWit_range h; have := ltable lay; omega
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
  have hh : t8.readWords (BitVec.ofNat 64 0x800) 8 = wordsOf (headerBytesV5 w) := by
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
          (by simp only [ENC]; omega) (by simp only [ENC]; omega))]
      exact hz0' _ (by omega) (by omega) (by omega) (by omega)
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
  have hse := search_entry (sk := sk) hS index hi v (WCT9.topSib sig) root' pk hsib t8 p8 x5_8 e8 hpk0 hpk1 hix hblk
  -- [h2 lane] tailProgS's do-notation puts the `if` outside the bind; fold it back under one bind
  have hite : ∀ K : Option Nat → M (Option (HashOutput × WCT9.Witness)),
      (if root' = pk then pure (some 0) >>= K
        else WCT9.searchTop (WCT9.digestIndex N) v (WCT9.topSib sig) pk WCT9.searchFuel 1 >>= K) =
      (if root' = pk then pure (some 0) else
        WCT9.searchTop (WCT9.digestIndex N) v (WCT9.topSib sig) pk WCT9.searchFuel 1) >>= K := by
    intro K; split <;> rfl
  dsimp only
  rw [hite]
  refine (TBSim.bind (W₂ := 11 + compactC) hse (fun oc t9 h9 => ?_)).mono
    (W' := 65535 * 30 + 111 + compactC) (by omega) (fun _ _ h => h)
  rcases oc with _ | c
  · obtain ⟨t10, st10, p10, x5_10, x10_10, _⟩ := Search.cs0_spec hB.2.2 t9 h9
    exact (TBSim.steps st10 (TBSim.pure (Q := ExpQW) (a := none) (Or.inl ⟨p10, x5_10, x10_10⟩))).mono (by omega)
      (fun _ _ h => h)
  obtain ⟨p9, h0, hne⟩ := h9
  set wc : WCT9.Witness := ⟨WCT9.fillTop sig c, counter, fun lay => counters.getD lay.val 0⟩ with hwc
  -- [h2 lane] one frame for both search outcomes: only the hash buffers and the completed sibling word move
  have FU : Frame t8 t9 (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨
      A = 0x2c48 + sOff index) := by
    by_cases hc0 : c = 0
    · exact (h0 hc0).mono (fun _ _ h => h.elim)
    · exact (hne hc0).2.2
  have hdig9 : OutAt t9 0x60 N := fun j hj => by
    rw [FU.get (by omega) (by simp only [NODE, NOUT]; have := sOff_cases index; omega),
      g87 _ (by omega) (nLW _ (by omega) (by omega))]
    exact P.dig j hj
  have hplan9 : PlanAt t9 := fun j hj => by
    rw [FU.get (by omega) (by simp only [NODE, NOUT]; have := sOff_cases index; omega),
      g87 _ (by omega) (nLWp _ (by omega)),
      P.frame _ (by omega) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega)]
    exact hpre.plan j hj
  have hlplan9 : Compact2.LPlanAt t9 := fun j hj => by
    have hLP : Compact2.LPLAN = 0xff9400 := rfl
    rw [FU.get (by omega) (by simp only [NODE, NOUT]; have := sOff_cases index; omega),
      g87 _ (by omega) (nLWp _ (by omega)),
      P.frame _ (by omega) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega),
      f1.get (by omega) (by simp only [DIG]; omega)]
    exact w9init_lplan hd m pk σ j hj
  have htoptab9 : Compact2.TopTabAt t9 := by
    have hT : Compact2.TOPA = 0xfffb80 ∧ Compact2.TOPB = 0xfffd80 := ⟨rfl, rfl⟩
    have ht := w9init_toptab hd m pk σ
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [FU.get (by omega) (by simp only [NODE, NOUT]; have := sOff_cases index; omega),
        g87 _ (by omega) (nLWp _ (by omega)),
        P.frame _ (by omega) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega),
        f1.get (by omega) (by simp only [DIG]; omega)]
      exact ht.1 j hj
    · rw [FU.get (by omega) (by simp only [NODE, NOUT]; have := sOff_cases index; omega),
        g87 _ (by omega) (nLWp _ (by omega)),
        P.frame _ (by omega) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega),
        f1.get (by omega) (by simp only [DIG]; omega)]
      exact ht.2 j hj
  have hwit9 : t9.readWords (BitVec.ofNat 64 0x800) 2873 = wordsOf (witListV5 N wc) := by
    by_cases hc0 : c = 0
    · subst hc0
      rw [frame_readWords (h0 rfl) 0x800 2873 (by decide) (fun _ _ h => h), hwc,
        show WCT9.fillTop sig 0 = sig from hproj]
      exact witListW_words t8 N w hh hwct hgap hlay
    obtain ⟨_, hX, f9⟩ := hne hc0
    have hso := sOff_cases index
    have hsd := sOff_eq index
    have FT : Frame t8 t9 (fun A => (NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨
        A = 0x2c48 + sOff index) := f9
    have hXT : t9.getMem (BitVec.ofNat 64 (0x2c48 + sOff index)) = hi64 (WCT9.setTop (WCT9.topSib sig) c) := hX
    have nW : ∀ A, A < 0x2c48 →
        ¬ ((NODE ≤ A ∧ A < NODE + 64) ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ A = 0x2c48 + sOff index) := by
      intro A hA h; simp only [NODE, NOUT] at h; omega
    refine witListW_words t9 N wc ?_ ?_ ?_ ?_
    · rw [frame_readWords FT 0x800 8 (by decide) (fun i hi => nW _ (by omega))]; exact hh
    · rw [frame_readWords FT 0x840 1152 (by decide) (fun i hi => nW _ (by omega))]; exact hwct
    · rw [frame_readWords FT 0x2c40 1 (by decide) (fun i hi => nW _ (by omega))]; exact hgap
    intro lay
    have hrb := region_bounds lay
    by_cases hl0 : lay.val = 0
    swap
    · -- layers 1..3: untouched by the search, and `fillTop` only changes layer 0
      have hge : 0x3CC8 ≤ lBase lay := by
        clear hrb
        fin_cases lay <;> first | exact absurd rfl hl0 | decide
      rw [frame_readWords FT (lBase lay) _ (by omega) (fun i hi h => by simp only [NODE, NOUT] at h; omega), hlay lay]
      unfold layerRegionV6
      rw [if_neg hl0, if_neg hl0]
      show _ = wordsOf (layerBytesBCV6 lay _ (WCT9.fillLayer lay (sig.layers lay) c) _)
      rw [WCT9.fillLayer_ne _ _ _ hl0]
    have hlay0 : lay = 0 := Fin.ext hl0
    subst hlay0
    have hlb0 : lBase 0 = 0x2c48 := by decide
    have hh0 : height 0 = 12 := by decide
    have hcc0 : chainCount 0 = 54 := by decide
    have hsoe : sOff index = SigGolfCandidate.T3M.Expand.sideOff (route index 0).1 11 + 8 := sOff_eq index
    have hsoe' : sOff index = SigGolfCandidate.T3M.Expand.sideOff (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 11 + 8 := sOff_eq index
    have hout := hout8 0 (by decide)
    have hs11 : SigGolfCandidate.T3M.Expand.sideOff (route index 0).1 11 ≤ 48 := by
      unfold SigGolfCandidate.T3M.Expand.sideOff; split <;> omega
    have hs11' : SigGolfCandidate.T3M.Expand.sideOff (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 11 ≤ 48 := hs11
    unfold layerRegionV6
    rw [if_pos (show (0 : Layer).val = 0 from rfl)]
    refine layer_words t9 0 _ _ (fun i h => ?_) (fun j h => ?_) (fun A h1 h2 hn => ?_)
    · -- chain values: unchanged, above the paths
      have e : lval (WCT9.toT3Signature sig) 0 i = (sig.layers 0).values ⟨i, h⟩ := by
        unfold lval; rw [dif_pos h]; rfl
      have d8 := hout.2.1 i h
      rw [e] at d8
      have hi54 : i < 54 := h
      rw [show lWC (0 : Layer) = 0x3c88 from rfl] at d8 ⊢
      exact ⟨(FT.get (by omega) (by simp only [NODE, NOUT]; omega)).trans d8.1,
        (FT.get (by omega) (by simp only [NODE, NOUT]; omega)).trans d8.2⟩
    · -- paths: level 11 is completed by the search word, the others are unchanged
      have e : lpath (WCT9.toT3Signature sig) 0 j = (sig.layers 0).path ⟨j, h⟩ := by
        unfold lpath; rw [dif_pos h]; rfl
      have d8 := hout.2.2 j h
      rw [e] at d8
      have h12 : j < 12 := h
      have hsj : SigGolfCandidate.T3M.Expand.sideOff (route index 0).1 j ≤ 48 := by
        unfold SigGolfCandidate.T3M.Expand.sideOff; split <;> omega
      have hsj' : SigGolfCandidate.T3M.Expand.sideOff (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 j ≤ 48 := hsj
      rw [show lWM (0 : Layer) = 0x2f08 from rfl] at d8 ⊢
      show DigAt t9 _ ((WCT9.fillLayer 0 (sig.layers 0) c).path ⟨j, h⟩)
      unfold WCT9.fillLayer
      dsimp only
      by_cases hj : j = 11
      · subst hj
        rw [if_pos ⟨rfl, rfl⟩]
        constructor
        · rw [FT.get (by omega) (by simp only [NODE, NOUT]; omega), d8.1]
          exact (lo64_setTop _ c).symm
        · rw [show 0x2f08 - 64 * 11 + SigGolfCandidate.T3M.Expand.sideOff (route index 0).1 11 + 8 =
            0x2c48 + sOff index by omega, hXT]
          rfl
      · rw [if_neg (fun hh => hj hh.2)]
        exact ⟨(FT.get (by omega) (by simp only [NODE, NOUT]; omega)).trans d8.1,
          (FT.get (by omega) (by simp only [NODE, NOUT]; omega)).trans d8.2⟩
    · -- zeros: the only written word in the region is a witness slot
      have h1' : 0x2c48 ≤ A := h1
      have h2' : A < 0x2c48 + 64 * 66 := h2
      have hAX : A ≠ 0x2c48 + sOff index := by
        intro hA
        apply hn
        refine Or.inr ⟨11, by decide, Or.inr ?_⟩
        rw [show lWM (0 : Layer) = 0x2f08 from rfl]
        omega
      rw [FT.get (by omega) (by simp only [NODE, NOUT]; omega)]
      refine g8L A h1' (by omega) ?_
      rintro (h | h | ⟨lay', _, h | h⟩)
      · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
      · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch, SigGolfCandidate.T3M.Expand.RlScratch, CHAIN,
          Search.NODE, Search.NOUT, LEAFPK, ENC] at h; omega
      · have e1 := lD_in_region 0 lay' A h1 h2 h
        rw [show lBase (0 : Layer) = 0x2c48 from rfl] at e1
        rcases lD_cases lay' with e | e | e | e <;> omega
      · by_cases he : lay' = 0
        · subst he; exact hn h
        · exact rlWit_region 0 lay' _ A h1 h2 he h
  obtain ⟨t11, st11, p11, x5_11, x10_11, hw11⟩ :=
    compactGood_holds im hc (codeAt_351W hB.2.1) N wc t9 ⟨p9, hwit9, hdig9, hplan9, hlplan9, htoptab9⟩
  exact (TBSim.steps st11 (TBSim.pure (Q := ExpQW) (a := some (N, wc)) ⟨p11, x5_11, x10_11, hw11⟩)).mono
    (by omega) (fun _ _ h => h)
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
/- Witness trim: archived. After the trim the legacy (5310-byte) compactor no longer leaves the inner header at
the witness base (its counter copy at 1248, LE64(1) at 1240 and bit-6 = 1 top sibling at 1216 are now scratch
below `WIT = 1312`), so the full legacy readout `expqW_output` and the legacy `expandComposeSpec_holds` are no
longer derivable; they were only consumed by the archived 5310-byte bindings below. The paired chain
(`SharedCompactMain.finish_steps`) is unaffected.
/-- Expand writes 3116 whole words from 0x4c0; the 24924-byte witness is their prefix (the 4 bytes
after the 32-bit digest counter are zero and lie outside the witness). -/
theorem expqW_output {imgs : Phase → Image} {N : HashOutput} {w : WCT9.Witness} {t : MachineState}
    (h : t.readWords (BitVec.ofNat 64 0x4c0) 3116 = wordsOf (ClaudeWCT.W9.T3M.witList N w)) :
    readOutput (w9Sub imgs).sizes (w9Sub imgs).layout .expand t = ClaudeWCT.W9.T3M.witEnc N w := by
  show readBuffer t 0x4c0 24924 =
    BitVec.ofNat (8 * 24924) (SigGolfCandidate.T3.readLE (ClaudeWCT.W9.T3M.witList N w))
  rw [readBuffer_trunc t 0x4c0 24924 (8 * 3116) (by omega),
    readBuffer_of_words t 0x4c0 3116 (ClaudeWCT.W9.T3M.witList N w) (by decide) (by decide)
      (ClaudeWCT.W9.T3M.witList_length_eq N w) h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
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
    refine ⟨((Compact2.Buffer.Post.code_ecall hc).fetch t p).trans rfl, x5, ?_⟩
    rw [x10, if_pos (show (0#64 : BitVec 64) = 0 from rfl), expqW_output hw]; rfl
set_option maxRecDepth 10000 in
theorem expandComposeSpec_holds : ExpandComposeSpec := by
  intro imgs hv hc hF hP hS hd hB
  have hsim : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 5310),
      Sim ((w9Sub imgs).image .expand) (w9init (imgs .expand) m pk σ) expCostW
        (mrealize 0 (ClaudeWCT.W9.T3M.expandN m pk (ClaudeWCT.W9.T3M.sigDecC σ))) ExpQW :=
    fun m pk σ => expandW_tbsim (sk := 0) hc hF hP hS hd hB m pk σ
  refine ⟨fun m pk σ => ?_, fun hash m pk σ => ?_⟩
  · exact Sim.run_eq (w9Sub imgs) .expand (m, pk, σ) (initialState_w9 imgs hv m pk σ) (hsim m pk σ)
      (Nat.lt_of_succ_lt expCostW_lt) _ (expqW_halt imgs hc hB)
  · obtain ⟨h1, h2⟩ := Sim.runWith (w9Sub imgs) .expand (m, pk, σ) (initialState_w9 imgs hv m pk σ)
      (hsim m pk σ) expCostW_lt (fun a t h => ⟨(expqW_halt imgs hc hB a t h).1, (expqW_halt imgs hc hB a t h).2.1⟩) hash
    exact ⟨h1, lt_of_le_of_lt h2 expCostW_lt⟩
-/
end ClaudeWCT.W9.Machine.Expand
end
/- Archived concrete 5310-byte image bindings. The paired image is bound below.
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT.W9.Machine.Expand (BackSpec compareCode)
theorem wct_compareCode : CodeAt image (pcOf 342) compareCode := by
  apply codeAt_slice
  · decide +kernel
  · decide +kernel
theorem wct_backSpec : BackSpec Images.expandImage := by
  exact ⟨fun sk sig index L R s h => layers_tbsim 4 (.pair L R) 0 s h, wct_compareCode, Search.kernAt_expand⟩
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
private def chunks : List (List (BitVec 32)) := expandCodeChunks
private theorem chunks_ok : (chunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel
private theorem chunks_length : chunks.length = 173 := by rfl
private theorem chunks_new : expChunks = chunks.drop 4 := rfl
set_option maxHeartbeats 1000000 in
private theorem code_chunks : Images.expandCode = chunks.flatten := by
  exact expandCode_flatten
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
    have hp0 : expChunks.getD c [] <+: chunks.flatten.drop (256 * (c + 4)) := by
      rw [ClaudeWCT.W9.Machine.VLib.drop_chunks 256 chunks (c + 4) chunks_ok (by rw [chunks_length]; omega)]
      have hh := wct_chunk_prefix (chunks.drop 4) c
      rw [List.drop_drop] at hh
      rw [chunks_new]
      simpa [Nat.add_comm] using hh
    have hbase : chunks.flatten <+: Images.expandCode := ⟨[], by simpa using code_chunks.symm⟩
    exact hp0.trans (hbase.drop (256 * (c + 4)))
  apply codeAt_slice (by omega)
  change List.take (expChunks.getD c []).length (Images.expandCode.drop (256 * (c + 4))) = _
  obtain ⟨rest, hrest⟩ := hp
  rw [← hrest, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
/-- [h2 lane] the H2 prologue and search words are in the record's expand image (tail words through the chunk
windows, as the post-pass's final `ecall`). -/
theorem wct_proAt : ClaudeWCT.W9.Machine.Expand.ProAt Images.expandImage := by
  refine ⟨?_, ClaudeWCT.W9.Machine.Expand.codeAt_of_window wct_newCodeAt (by decide) (by decide +kernel), ?_⟩
  · apply codeAt_slice
    · decide +kernel
    · decide +kernel
  · apply codeAt_slice
    · decide +kernel
    · decide +kernel
theorem wct_srchAt : ClaudeWCT.W9.Machine.Expand.SrchAt Images.expandImage := by
  refine ⟨?_, ClaudeWCT.W9.Machine.Expand.codeAt_of_window wct_newCodeAt (by decide) (by decide +kernel)⟩
  apply codeAt_slice
  · decide +kernel
  · decide +kernel
theorem wct_frontAt : ClaudeWCT.W9.Machine.Expand.FrontAt Images.expandImage :=
  ⟨wct_front0, ClaudeWCT.W9.Machine.Expand.codeAt_of_window wct_newCodeAt
    (by simp [ClaudeWCT.W9.Machine.Expand.zeroBlk]) (by decide +kernel)⟩
end SigGolfCandidate.T3M.Expand
end
-/
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000 in
theorem expChunks_full : ∀ c, c < 168 → (expChunks.getD c []).length = 256 := by decide +kernel
set_option maxRecDepth 100000 in
theorem expChunks_flatten_length : expChunks.flatten.length = 43022 := by decide +kernel
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
/- Archived 5310-byte export for the former concrete image.
section
namespace ClaudeWCT.W9.Machine.ExpandLink
open SigGolfCandidate.T3M
def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
theorem v7_valid : I0.expand.Valid (ClaudeWCT.W9.T3M.submission I0).sizes (ClaudeWCT.W9.T3M.submission I0).layout := by
  rw [ClaudeWCT.W9.T3M.submission_sizes, ClaudeWCT.W9.T3M.submission_layout]
  have h := submission_expand_valid
  rw [SigGolfCandidate.T3M.submission_expand, SigGolfCandidate.T3M.submission_sizes,
    SigGolfCandidate.T3M.submission_layout] at h
  dsimp only [I0]
  exact h
theorem v7_dataOK : ClaudeWCT.W9.Machine.Expand.ExpandDataOK I0.expand := Expand.wct_expandData
theorem expand_W_v7 :
    ClaudeWCT.W9.Machine.Expand.ExpandRefinesW (ClaudeWCT.W9.T3M.submission I0).image ∧
      ClaudeWCT.W9.Machine.Expand.ExpandTerminatesW (ClaudeWCT.W9.T3M.submission I0).image := by
  dsimp only [ClaudeWCT.W9.T3M.submission, I0]
  exact ClaudeWCT.W9.Machine.Expand.expandComposeSpec_holds _ v7_valid Expand.wct_newCodeAt Expand.wct_frontAt
    Expand.wct_proAt Expand.wct_srchAt v7_dataOK Expand.wct_backSpec
end ClaudeWCT.W9.Machine.ExpandLink
end
-/
end

namespace ClaudeWCT.W9.Machine.Expand.SharedWitnessOutput
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem words_map (t : MachineState) (A : Nat) : ∀n,
    t.readWords (BitVec.ofNat 64 A) n=(List.range n).map (fun j=>t.getMem (BitVec.ofNat 64 (A+8*j)))
  | 0 => rfl
  | n+1 => by
    rw [readWords_add,words_map t A n,readWords_one,List.range_succ,List.map_append]
    rfl

theorem readBuffer_words (t : MachineState) (A n m : Nat) (b : BitVec (8*n))
    (hal : A%8=0) (haddr : A+8*m<2^64) (hsize : n≤8*m)
    (hw : ∀k,k < m → t.getMem (BitVec.ofNat 64 (A+8*k))=b.extractLsb' (64*k) 64) :
    readBuffer t A n=b := by
  let b' : BitVec (8*(8*m)):=b.setWidth _
  have hw' : t.readWords (BitVec.ofNat 64 A) m=wordsOf (SphincsSecurity.bytesLE (8*m) b') := by
    rw[words_map,wordsOf_bytesLE]
    apply List.map_congr_left
    intro k hk
    rw[show b'.extractLsb' (64*k) 64=b.extractLsb' (64*k) 64 from
      BitVec.extractLsb'_setWidth_of_le (by have h:=List.mem_range.mp hk;omega)]
    exact hw k (List.mem_range.mp hk)
  have h:=readBuffer_of_words t A m (SphincsSecurity.bytesLE (8*m) b') hal haddr
    (by rw[SphincsSecurity.bytesLE_length]) hw'
  rw[readLE_bytesLE] at h
  rw[readBuffer_trunc t A n (8*m) hsize,h]
  apply BitVec.eq_of_toNat_eq
  simp only[BitVec.toNat_ofNat,BitVec.toNat_setWidth,b',Nat.mod_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8*n≤8*(8*m))),
    Nat.mod_eq_of_lt b.isLt]
#print axioms readBuffer_words
end ClaudeWCT.W9.Machine.Expand.SharedWitnessOutput

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

theorem scatter_finish_readout {im : Image} (hc : ∀k:Fin 9,CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) afterCode) (hf : CodeAt im (pcOf 47005) finishCode)
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec.CBytes)
    (s : MachineState) (hp : s.pc=pcOf 45257)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hraw : RawAt s (SharedForest.rawChildFromOutput output)) (hplan : PlanAt s)
    (hmode : s.getMem 417824=1)
    (hc3 : s.getMem 417816=(witness.counters 3).setWidth 64)
    (hz : ∀ (off : Nat), off+8≤8160 → off%8=0 → s.getMem (BitVec.ofNat 64 (1312+off))=0)
    (htail : ∀ (j : Nat), 1020≤j → j<3104 → s.getMem (BitVec.ofNat 64 (1312+8*j))=
      (Paired.witEnc output witness).extractLsb' (8*(8*j)) 64) :
    ∃v,Steps im s 1263 1440 v ∧ v.pc=pcOf 47012 ∧ v.getReg .x5=1 ∧ v.getReg .x10=0 ∧
      readBuffer v 1312 24828=Paired.witEnc output witness ∧ Frame s v ScatterW := by
  obtain ⟨t,st,ht⟩:=scatter_steps hc s _ hraw hplan hp
  obtain ⟨u,tu,up,ur,uf⟩:=after_steps ha t ht.pc
  have hm:t.getMem 417824=1:=
    (ht.frame.get (A:=417824) (by decide) (by unfold ScatterW;omega)).trans hmode
  have up':u.pc=pcOf 47005:=by simpa only [hm,if_neg (show (1:BitVec 64)≠0 by decide)] using up
  obtain ⟨v,uv,vp,vc,vpad,v5,v10,vr,vf⟩:=finish_steps hf u up'
  have hcounter:v.getMem 1344=(witness.counters 3).setWidth 64:=by
    exact vc.trans ((uf.get (A:=417816) (by decide) (by tauto)).trans
      ((ht.frame.get (A:=417816) (by decide) (by unfold ScatterW;omega)).trans hc3))
  have hframe:Frame s v ScatterW:=((ht.frame.trans uf).trans vf).mono (by
    intro A hA hw
    rcases hw with (hw|hw)|hw
    · exact hw
    · exact hw.elim
    · unfold ScatterW;omega)
  -- Stage 2 (C3): the final pass restores the counter word (`off = 32`) and the row-tweak pad (`off = 24`); every
  -- other prefix word is the scatter's original word.
  have hprefix : ∀ (off:Nat), off+8≤8160 → off%8=0 →
      W9Machine.OrigW (Paired.witEnc output witness) v (1312+off) := by
    intro off hb hal
    unfold W9Machine.OrigW
    rw [show 1312+off-0x520=off by omega]
    by_cases h32:off=32
    · subst off
      rw [Paired.counterWord_witEnc]
      exact hcounter
    by_cases h24:off=24
    · subst off
      rw [SharedScatter.witPad24_witEnc]
      exact vpad
    have ho:=ScatterInv.original_prefix_forest output witness b s t hin hforest ht hz off hb hal (Or.inl h32) h24
    unfold W9Machine.OrigW at ho
    rw [show 1312+off-0x520=off by omega] at ho
    rw [vf.get (A:=1312+off) (by omega) (by omega)]
    exact (uf.get (by omega) (by tauto)).trans ho
  refine ⟨v,(st.trans tu).trans uv,vp,v5,v10,?_,hframe⟩
  apply SharedWitnessOutput.readBuffer_words v 1312 24828 3104 _ (by decide) (by decide) (by decide)
  intro j hj
  by_cases h:j<1020
  · have hh:=hprefix (8*j) (by omega) (by omega)
    simpa only [W9Machine.OrigW,show 1312+8*j-0x520=8*j by omega,
      show 8*(8*j)=64*j by omega] using hh
  · have hm':v.getMem (BitVec.ofNat 64 (1312+8*j))=s.getMem (BitVec.ofNat 64 (1312+8*j)):=
      hframe.get (by omega) (by unfold ScatterW;omega)
    exact hm'.trans (by simpa only [show 8*(8*j)=64*j by omega] using htail j (by omega) hj)
#print axioms scatter_finish_readout
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

theorem PlanAt.frame {s t:MachineState} {W:Nat → Prop} (h:PlanAt s) (hf:Frame s t W)
    (hn:∀A,16748424≤A → A<16748600 → ¬W A) : PlanAt t := by
  intro child j hj
  have hm:=Nat.mod_lt child.val (by decide:0<32)
  exact (hf.getByte (by omega) (hn _ (by omega) (by omega))).trans (h child j hj)

theorem rawAt_of_output (s:MachineState) (output:HashOutput) (ho:OutAt s NBUF output) :
    RawAt s (SharedForest.rawChildFromOutput output) := by
  intro k
  convert SharedDispatch.raw_output s output ho k using 1 <;> fin_cases k <;> rfl

theorem clear_scatter_finish {im:Image} (hz:SharedZero.ClearCode im)
    (hc:∀k:Fin 9,CoordinateCode im k.val) (ha:CodeAt im (pcOf 46509) afterCode)
    (hf:CodeAt im (pcOf 47005) finishCode)
    (output:HashOutput) (witness:SharedForest.Witness) (b:SharedCodec.CBytes)
    (s:MachineState) (hp:s.pc=pcOf 46980) (hin:SharedCompact.ForestAt s b)
    (hforest:witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hplan:PlanAt s) (hout:OutAt s 96 output)
    (hc3:s.getMem 1248=(witness.counters 3).setWidth 64)
    (htail:∀ (j:Nat),1020≤j → j<3104 → s.getMem (BitVec.ofNat 64 (1312+8*j))=
      (Paired.witEnc output witness).extractLsb' (8*(8*j)) 64) :
    ∃v,Steps im s 4381 4558 v ∧ v.pc=pcOf 47012 ∧ v.getReg .x5=1 ∧ v.getReg .x10=0 ∧
      readBuffer v 1312 24828=Paired.witEnc output witness := by
  obtain ⟨t,st,tp,tzero,tctr,tmode,tdigest,tr,tf⟩:=SharedZero.final_clear hz s hp
  have tin:SharedCompact.ForestAt t b:=hin.frame tf (by intros A hA hB hw;omega)
  have tplan:PlanAt t:=hplan.frame tf (by intros A hA hB hw;omega)
  have tout:OutAt t NBUF output:=by
    intro k hk
    exact (tdigest k hk).trans (hout k hk)
  obtain ⟨v,tv,vp,v5,v10,vout,vf⟩:=scatter_finish_readout hc ha hf output witness b t tp tin hforest
    (rawAt_of_output t output tout) tplan tmode (tctr.trans hc3)
    (by intro off hb hal;exact tzero _ (by omega) (by omega) (by omega)) (by
      intro j hj hbound
      exact (tf.get (by omega) (by omega)).trans (htail j hj hbound))
  exact ⟨v,st.trans tv,vp,v5,v10,vout⟩
#print axioms PlanAt.frame
#print axioms rawAt_of_output
#print axioms clear_scatter_finish
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer chainCount readLE)
open SigGolfCandidate.T3M (window zeros wordsOf)
open ClaudeWCT.W9.T3M (leafBufferSlot leafBufferBase)
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
theorem bufferMem_main_congr (M M' : Nat → Word) (A : Nat)
    (hlo : 10240 ≤ A) (hhi : A < 26144) (halign : A % 8 = 0)
    (hmem : ∀ B, 10240 ≤ B → B < 23024 → B % 8 = 0 → M B = M' B) :
    Buffer.bufferMem M A = Buffer.bufferMem M' A := by
  have h1240 : A ≠ 1240 := by omega
  by_cases hprefix : A < 22992
  · rw [Buffer.bufferMem, if_neg h1240, if_neg (by omega), if_neg (by omega),
      Buffer.bufferMem, if_neg h1240, if_neg (by omega), if_neg (by omega)]
    exact hmem A hlo (by omega) halign
  by_cases hfooter : 26112 ≤ A
  · rw [Buffer.bufferMem, if_neg h1240, if_pos ⟨hfooter,hhi,halign⟩,
      Buffer.bufferMem, if_neg h1240, if_pos ⟨hfooter,hhi,halign⟩]
    exact hmem (A-3120) (by omega) (by omega) (by omega)
  · have hidx : (A - 22992) / 8 < 390 := by omega
    have h := buffer_address_coverage ⟨(A - 22992) / 8,hidx⟩
    have he : 22992 + 8 * ((A - 22992) / 8) = A := by omega
    simp only [he,List.mem_append] at h
    rcases h with h | h
    · obtain ⟨lay,i,k,hi,hk,rfl⟩ := mem_bufferEndpointAddresses h
      rw [bufferMem_endpoint _ lay i hi k hk,bufferMem_endpoint _ lay i hi k hk]
      have hb : 10240 ≤ 1312 + ClaudeWCT.W9.T3M.chainBlock lay i + 48 + k ∧
          1312 + ClaudeWCT.W9.T3M.chainBlock lay i + 48 + k < 23024 ∧
          (1312 + ClaudeWCT.W9.T3M.chainBlock lay i + 48 + k) % 8 = 0 := by
        fin_cases lay <;> rcases hk with rfl | rfl
        all_goals norm_num [ClaudeWCT.W9.T3M.chainBlock,ClaudeWCT.W9.T3M.layerBase,ClaudeWCT.W9.T3M.pathSlots,chainCount] at hi ⊢ <;> omega
      exact hmem _ hb.1 hb.2.1 hb.2.2
    · rw [bufferMem_zeroAddress _ _ h,bufferMem_zeroAddress _ _ h]

theorem bufferMem_main_words (N : HashOutput) (w : WCT9.Witness) (M : Nat → Word)
    (hmem : ∀ i,1116 ≤ i → i < 2714 → M (1312 + 8*i) = (wordsOf (preBufferWitList N w)).getD i 0)
    (i : Nat) (hlo : 1116 ≤ i) (hi : i < 3104) :
    Buffer.bufferMem M (1312 + 8*i) = (wordsOf (ClaudeWCT.W9.T3M.witList N w)).getD i 0 := by
  have hm : ∀ B, 10240 ≤ B → B < 23024 → B % 8 = 0 → M B = preBufferMem N w B := by
    intro B hB hB' h8
    have hj : (B-1312)/8 < 2714 := by omega
    have he : B = 1312 + 8*((B-1312)/8) := by omega
    have h := hmem _ (by omega) hj
    rw [wordsOf_getD' _ 2714 (preBufferWitList_length N w) _ hj] at h
    unfold preBufferMem
    have hz : 8*((B-1312)/8) = B-1312 := by omega
    rw [hz] at h
    simpa only [Nat.add_sub_of_le (show 1312 ≤ B by omega)] using h
  rw [bufferMem_main_congr M (preBufferMem N w) _ (by omega) (by omega) (by omega) hm,
    bufferMem_serializer N w _ (by omega) (by omega) (by omega),
    wordsOf_getD' _ 3104 (ClaudeWCT.W9.T3M.witList_length_eq N w) i hi]
  unfold serializedMem
  congr 3 <;> omega

#print axioms bufferMem_main_congr
#print axioms bufferMem_main_words
end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
theorem out2old_main_congr (M M' : Nat → Word) (h : ∀ x < 8 * 2729, x % 8 = 0 → (x ≤ 16 ∨ 8136 ≤ x) → M (WIT + x) = M' (WIT + x))
    (idx o : Nat) (hlo : 7424 ≤ o) (ho : o % 8 = 0) : out2old M idx o = out2old M' idx o := by
  have hW : WIT = 0x800 := rfl
  have hS : SNAP2 = 0x300000 := rfl
  have e : ∀ A, WIT ≤ A → A - WIT < 8 * 2729 → (A - WIT) % 8 = 0 → (A - WIT ≤ 16 ∨ 8136 ≤ A - WIT) → M A = M' A := fun A h1 h2 h3 h4 => by
    have := h (A - WIT) h2 h3 h4
    rwa [show WIT + (A - WIT) = A by omega] at this
  obtain ⟨d1, d2, d3, c1, c2, c3⟩ := lay_consts
  have hz : (zoneLay o = 1 ∧ o < 14800) ∨ (zoneLay o = 2 ∧ 14800 ≤ o ∧ o < 17872) ∨
      (zoneLay o = 3 ∧ 17872 ≤ o) := by
    unfold zoneLay; split_ifs <;> omega
  have hzl : 1 ≤ zoneLay o ∧ zoneLay o < 4 := by omega
  have hpt : pathTop (zoneLay o) ≤ 400 := by unfold pathTop; split_ifs <;> omega
  have hch : chSrc (zoneLay o) - SNAP2 + (o - (chDst (zoneLay o) - WIT)) + 8 ≤ 8 * 2729 ∨ ¬ o < 20944 := by
    unfold chSrc
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> simp only [hz] at * <;> norm_num <;> omega
  have hch8 : (chSrc (zoneLay o) - SNAP2 + (o - (chDst (zoneLay o) - WIT))) % 8 = 0 := by
    unfold chSrc
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> simp only [hz] at * <;> norm_num <;> omega
  have hdl : (lvDst (zoneLay o) - WIT) % 8 = 0 := by
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> omega
  have hcs : SNAP2 ≤ chSrc (zoneLay o) := by unfold chSrc; omega
  have hchlo : 8136 ≤ chSrc (zoneLay o) - SNAP2 := by
    unfold chSrc
    rcases hz with ⟨hz, _⟩ | ⟨hz, _, _⟩ | ⟨hz, _⟩ <;> rw [hz] <;> decide
  unfold out2old
  simp only [if_neg (show ¬o<64 by omega),if_neg (show ¬o<7424 by omega)]
  split_ifs with h3 h4 h5 h6 h7 h8 h9
  · exact e _ (by omega) (by omega) (by omega) (by omega)
  · apply pathOut_congr
    intro j hj
    obtain ⟨s1, s2, s3⟩ := lvSrc_val (zoneLay o) j hzl
    exact e _ (by omega) (by omega) (by omega) (by omega)
  · exact e _ (by omega) (by omega) (by omega) (by omega)
  · exact e _ (by omega) (by omega) (by omega) (by omega)
  · exact e _ (by omega) (by omega) (by omega) (by omega)
  · rfl
  · rw [e _ (by omega) (by omega) (by omega) (by omega)]

#print axioms out2old_main_congr
end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem stMem_between (M : Nat → Word) (A : Nat)
    (hlo : 26144 ≤ A) (hhi : A < SNAP2) : stMem M A = M A := by
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (Or.inr (by omega))]
  unfold regsMem ctrMem zMem snapMem
  have hs : SNAP2 = 0x300000 := rfl
  have hw : WZ = 1216 := rfl
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

theorem run2Mem_between (M : Nat → Word) (idx A : Nat)
    (hlo : 26144 ≤ A) (hhi : A < SNAP2) : run2Mem M idx A = M A := by
  have hw : WIT = 2048 := rfl
  obtain ⟨d1,d2,d3,c1,c2,c3⟩ := lay_consts
  unfold run2Mem tailMem
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
    layMem_out _ 3 (by omega) idx A (Or.inr (by omega)),
    layMem_out _ 2 (by omega) idx A (Or.inr (by omega)),
    layMem_out _ 1 (by omega) idx A (Or.inr (by omega))]
  unfold topMem
  rw [if_neg (by omega),stMem_between M A hlo hhi]

theorem bufferMem_between (M : Nat → Word) (A : Nat) (hlo : 26144 ≤ A) :
    Buffer.bufferMem M A = M A := by
  unfold Buffer.bufferMem
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]

theorem plMem_counter (M : Nat → Word) (Q : Nat) (hQ : Q ≤ 9) : plMem M Q 1248 = M 1248 := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    have hm:=Nat.min_le_right (M (Compact.holdAt Q + 16)).toNat 1
    have hb : 896*Q ≤ 8384 := by omega
    unfold plMem hslot hdst
    rw [if_neg (by omega),if_neg (by omega)]
    exact ih (by omega)

theorem stMem_counter (M : Nat → Word) : stMem M 1248 = M (WIT+32) := by
  unfold stMem
  rw [plMem_counter _ 9 le_rfl]
  unfold regsMem ctrMem
  rw [if_neg (by norm_num),if_pos (by norm_num)]
  unfold zMem snapMem WZ SNAP2 WIT
  norm_num

theorem run2Mem_counter (M : Nat → Word) (idx : Nat) : run2Mem M idx 1248 = M (WIT+32) := by
  have hw : WIT = 2048 := rfl
  unfold run2Mem tailMem
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),lays_low _ idx _ (by omega)]
  unfold topMem
  rw [if_neg (by omega),stMem_counter]

theorem bufferMem_counter (M : Nat → Word) : Buffer.bufferMem M 1248 = M 1248 := by rfl

#print axioms run2Mem_between
#print axioms run2Mem_counter
end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem stMem_keep (M : Nat → Word) (A : Nat)
    (hA : A < 1216 ∨ 26144 ≤ A) (hSnap : A < SNAP2 ∨ SNAP2+8*2729 ≤ A) : stMem M A = M A := by
  unfold stMem
  rw [plMem_out _ 9 le_rfl A (by omega)]
  unfold regsMem ctrMem zMem snapMem
  have hs : SNAP2 = 0x300000 := rfl
  have hw : WZ = 1216 := rfl
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

theorem run2Mem_keep (M : Nat → Word) (idx A : Nat)
    (hA : A < 1216 ∨ 26144 ≤ A) (hSnap : A < SNAP2 ∨ SNAP2+8*2729 ≤ A) : run2Mem M idx A = M A := by
  have hw : WIT = 2048 := rfl
  obtain ⟨d1,d2,d3,c1,c2,c3⟩ := lay_consts
  unfold run2Mem tailMem
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
    layMem_out _ 3 (by omega) idx A (by omega),
    layMem_out _ 2 (by omega) idx A (by omega),
    layMem_out _ 1 (by omega) idx A (by omega)]
  unfold topMem
  rw [if_neg (by omega),stMem_keep M A hA hSnap]

theorem bufferMem_keep (M : Nat → Word) (A : Nat) (hA : A < 1216 ∨ 26144 ≤ A) :
    Buffer.bufferMem M A = M A := by
  unfold Buffer.bufferMem
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]

#print axioms run2Mem_keep
end ClaudeWCT.W9.Machine.Expand.Compact2

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 1000000

theorem finalWord_main_congr (M M' : Nat → Word) (cs : Nat → Nat)
    (h : ∀ i < 2873, (i ≤ 4 ∨ 1161 ≤ i) → M (0x800+8*i)=M' (0x800+8*i))
    (i : Nat) (hi : i < 2729) (hmain : i ≤ 4 ∨ 1017 ≤ i) :
    finalWord M cs i=finalWord M' cs i := by
  rcases hmain with hsmall | hlarge
  · simp only [finalWord,if_pos (show i<8 by omega)]
    exact h i (by omega) (Or.inl hsmall)
  · simp only [finalWord,if_neg (show ¬i<8 by omega),if_neg (show ¬i<1016 by omega)]
    exact h (i+144) (by omega) (Or.inr (by omega))
#print axioms finalWord_main_congr
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

def Protected (A : Nat) : Prop :=
  (A < 1216 ∨ 26144 ≤ A) ∧
  (((A < Compact.SNAP ∨ Compact.SNAP+9216 ≤ A) ∧
    (A < Compact2.SNAP2 ∨ Compact2.SNAP2+8*2729 ≤ A) ∧ ¬Compact.InHold 9 A) ∧
    ¬ (Compact2.Buffer.Post.SCR ≤ A ∧ A < Compact2.Buffer.Post.SCR+192))

theorem compact_main_steps {im : Image} (hc : CompactCodeAt im)
    (N : HashOutput) (w : WCT9.Witness) (s : MachineState) (hpc : s.pc = pcOf 41108)
    (hN : OutAt s 96 N) (hp : PlanAt s) (hlp : Compact2.LPlanAt s) (htp : Compact2.TopTabAt s)
    (hmain : ∀ i < 2873, (i ≤ 4  ∨  1161 ≤ i)  →  s.getMem (BitVec.ofNat 64 (2048+8*i))=(wordsOf (witListV5 N w)).getD i 0) :
    ∃ t, Steps im s 69330 69330 t  ∧  t.pc = pcOf 43761  ∧
      (∀ i,1020 ≤ i  →  i < 3104  →  t.getMem (BitVec.ofNat 64 (1312+8*i))=(wordsOf (ClaudeWCT.W9.T3M.witList N w)).getD i 0)  ∧ 
      t.getMem (BitVec.ofNat 64 1248)=s.getMem (BitVec.ofNat 64 2080)  ∧ 
      (∀ A < 2^64, Protected A  →  t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) := by
  obtain ⟨v,sv,pv,rv,mv,mhv,fv⟩ := Compact.run_spec_framed hc N s hpc hN hp
  have hix : v.getMem (BitVec.ofNat 64 96) >>> 33 = BitVec.ofNat 64 (WCT9.digestIndex N) := by
    rw [fv 96 (by norm_num) (Or.inl (by norm_num)) (Or.inl (by decide)) (by unfold Compact.InHold;omega)]
    have h0:=hN 0 (by norm_num)
    rw [Nat.mul_zero,Nat.add_zero] at h0
    rw [h0]
    exact Compact2.index_shr N
  have hlv : Compact2.LPlanAt v := by
    intro k hk
    rw [fv _ (by unfold Compact2.LPLAN;omega) (Or.inr (by unfold Compact2.LPLAN;omega))
      (Or.inr (by unfold Compact2.LPLAN Compact.SNAP;omega)) (by unfold Compact2.LPLAN Compact.InHold;omega)]
    exact hlp k hk
  have hfl : ∀ c < 9, ∃f < 2, v.getMem (BitVec.ofNat 64 (Compact.holdAt c+16))=BitVec.ofNat 64 f := by
    intro c hc9
    refine ⟨1-(N.toNat/2^WCT9.childBase c%128)/2^6%2,by omega,?_⟩
    rw [show Compact.holdAt c+16 = Compact.holdAt c+8*2 by omega,mhv c hc9 2 (by omega)]
    simp only [Compact.holdVal,if_neg (by decide : ¬(2:Nat)=0),if_neg (by decide : ¬(2:Nat)=1)]
  obtain ⟨u,su,pu,mu⟩ := Compact2.run2_spec hc v pv (WCT9.digestIndex N) (WCT9.digestIndex_lt N) hix hlv hfl
  have hv6 : ∀ x < 8*2729,x%8 = 0  →  (x ≤ 16  ∨  8136 ≤ x)  → 
      v.getMem (BitVec.ofNat 64 (Compact2.WIT+x))=Compact2.v6M N w (Compact2.WIT+x) := by
    intro x hx h8 hzone
    obtain ⟨i,rfl⟩ : ∃i,x = 8*i := ⟨x/8,by omega⟩
    rw [show Compact2.WIT = 2048 from rfl,mv i (by omega)]
    unfold Compact2.v6M
    rw [show (2048+8*i-Compact2.WIT)/8 = i by unfold Compact2.WIT;omega,Compact.compact_words N w i (by omega)]
    apply Compact.finalWord_main_congr _ _ _ (fun j hj hm => ?_) i (by omega) (by omega)
    rw [hmain j hj hm,show (2048+8*j-2048)/8 = j by omega]
  have hpre : ∀ i,1116 ≤ i  →  i < 2714  →  u.getMem (BitVec.ofNat 64 (1312+8*i))=(wordsOf (Compact2.preBufferWitList N w)).getD i 0 := by
    intro i hi hi'
    rw [mu _ (by omega),show 1312+8*i = Compact2.WOUT+8*i from rfl,
      Compact2.run2_zone _ _ _ (by omega) (by omega),Compact2.compact2_words N w i hi' (by omega)]
    unfold Compact2.out2
    rw [if_neg (by omega),if_neg (by omega)]
    exact Compact2.out2old_main_congr _ _ hv6 _ _ (by omega) (by omega)
  have hold : ∀ q < 96, u.getMem (BitVec.ofNat 64 (9472 + 8*q)) =
      BitVec.ofNat 64 (SigGolfCandidate.T3.readLE (window (layerRegionV6 N w 0) (8*q) 8)) := by
    intro q hq
    rw [mu _ (by omega), show 9472+8*q = Compact2.WOUT+(8160+8*q) by unfold Compact2.WOUT; omega,
      Compact2.run2_zone _ _ _ (by omega) (by omega)]
    unfold Compact2.out2
    rw [if_neg (by omega), Compact2.out2old_main_congr _ _ hv6 _ _ (by omega) (by omega),
      show 8160+8*q-736 = 8*(1020+q)-736 by omega,
      Compact2.compact2_top_old N w (1020+q) (by omega) (by omega), show 8*(1020+q)-8160=8*q by omega]
  obtain ⟨t,st,pt,mt⟩ := Compact2.Buffer.buffer_prefix_spec hc u pu
  dsimp only [Compact2.Buffer.MemEq] at mt
  have beforeKeep : ∀ A < 2^64, Protected A → t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hkeep
    rw [mt A hA,Compact2.bufferMem_keep _ A hkeep.1,mu A hA,Compact2.run2Mem_keep _ _ A hkeep.1 hkeep.2.1.2.1]
    exact fv A hA (by rcases hkeep.1 with h | h <;> omega) hkeep.2.1.1 hkeep.2.1.2.2
  have htab : Compact2.TopTabAt t := by
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [beforeKeep _ (by unfold Compact2.TOPA;omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.TOPA Compact2.Buffer.Post.SCR;omega)]
      exact htp.1 k hk
    · rw [beforeKeep _ (by unfold Compact2.TOPB;omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.TOPB Compact2.Buffer.Post.SCR;omega)]
      exact htp.2 k hk
  have hleaf : (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 = WCT9.digestIndex N / 2^19 := by
    have := WCT9.digestIndex_lt N
    change WCT9.digestIndex N / 2^19 % 2^12 = _
    omega
  have hl : (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 < 4096 := by
    rw [hleaf];have := WCT9.digestIndex_lt N;omega
  have hix52 : t.getMem (BitVec.ofNat 64 96) >>> 52 = BitVec.ofNat 64 (SigGolfCandidate.T3.route (WCT9.digestIndex N) 0).1 := by
    rw [beforeKeep 96 (by decide) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;decide)]
    rw [hN 0 (by decide), show (52:Nat)=33+19 from rfl, BitVec.shiftRight_add, Compact2.index_shr, hleaf,
      SigGolfCandidate.T3M.ofNat_shr _ _ (by have := WCT9.digestIndex_lt N;omega)]
  obtain ⟨q,tq,pq,mq⟩ := Compact2.Buffer.Post.post_prefix_spec hc t pt _ hl hix52 htab
  refine ⟨q,(((sv.trans su).trans st).trans tq).of_eq (by norm_num) (by norm_num),pq,?_,?_,?_⟩
  · intro i hi hi'
    rw [mq _ (by omega) (by unfold Compact2.Buffer.Post.SCR;omega)]
    rw [Compact2.Buffer.Post.ppPlace_congr _ _ mt _ hl 12 le_rfl _ (by omega)]
    by_cases hnt : 1116 ≤ i
    · rw [Compact2.Buffer.Post.ppPlace_out _ _ hl 12 le_rfl _ (by omega)]
      exact Compact2.bufferMem_main_words N w _ hpre i hnt hi'
    · rw [show 1312+8*i=9472+8*(i-1020) by omega,
        Compact2.postMem_top N w _ hold (i-1020) (by omega),
        Compact2.wordsOf_getD' _ 3104 (ClaudeWCT.W9.T3M.witList_length_eq N w) i hi',
        show 8160+8*(i-1020)=8*i by omega]
  · rw [mq _ (by decide) (by unfold Compact2.Buffer.Post.SCR;decide),
      Compact2.Buffer.Post.ppPlace_out _ _ hl 12 le_rfl _ (by decide),
      mt _ (by norm_num),Compact2.bufferMem_counter,mu _ (by norm_num),Compact2.run2Mem_counter,
      show Compact2.WIT+32=2048+8*4 from rfl,mv 4 (by norm_num)]
    simp only [Compact.finalWord,if_pos (by decide : (4:Nat)<8)]
  · intro A hA hkeep
    rw [mq A hA hkeep.2.2, Compact2.Buffer.Post.ppPlace_out _ _ hl 12 le_rfl _ (by rcases hkeep.1 with h|h <;> omega)]
    exact beforeKeep A hA hkeep
#print axioms compact_main_steps
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer height chainCount)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem readWords_getD (t : MachineState) : ∀ (n a i : Nat), i<n →
    (t.readWords (BitVec.ofNat 64 a) n).getD i 0=t.getMem (BitVec.ofNat 64 (a+8*i))
  | 0,_,_,h => by omega
  | n+1,a,i,h => by
    have e : BitVec.ofNat 64 a+8=BitVec.ofNat 64 (a+8) := by
      apply BitVec.eq_of_toNat_eq;simp
    rw [MachineState.readWords_succ,e]
    cases i with
    | zero => simp
    | succ i =>
      rw [List.getD_cons_succ,readWords_getD t n (a+8) i (by omega)]
      congr 2;omega

theorem main_words_of_regions (t : MachineState) (N : HashOutput) (w : WCT9.Witness)
    (hh : t.readWords (BitVec.ofNat 64 2048) 8=wordsOf (headerBytesV5 w))
    (hlay : ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
      wordsOf (layerRegionV6 N w lay)) :
    ∀i,i<2873 → (i ≤ 4 ∨ 1161 ≤ i) →
      t.getMem (BitVec.ofNat 64 (2048+8*i))=(wordsOf (witListV5 N w)).getD i 0 := by
  have hf : (List.finRange 4).flatMap (layerRegionV6 N w)=
      layerRegionV6 N w 0++layerRegionV6 N w 1++layerRegionV6 N w 2++layerRegionV6 N w 3 := by
    simp only [List.finRange_succ,List.finRange_zero,List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,List.append_nil,List.append_assoc]
    rfl
  have hlenh : (wordsOf (headerBytesV5 w)).length=8 := length_wordsOf 8 _ (headerBytesV5_length w)
  have hlenf : (wordsOf (wctBytesV5 N w.signature)).length=1152 := length_wordsOf 1152 _ (wctBytesV5_length N w.signature)
  have htail : t.readWords (BitVec.ofNat 64 11336) 1712=
      wordsOf ((List.finRange 4).flatMap (layerRegionV6 N w)) := by
    rw [hf]
    simp only [List.append_assoc]
    rw [wordsOf_append _ _ (by rw[layerRegionV6_length];decide),
      wordsOf_append _ _ (by rw[layerRegionV6_length];decide),
      wordsOf_append _ _ (by rw[layerRegionV6_length];decide),←hlay 0,←hlay 1,←hlay 2,←hlay 3]
    simp only [lBase,height,chainCount]
    rw [show (1712:Nat)=528+(400+(392+392)) by rfl,readWords_add,readWords_add,readWords_add]
    rfl
  have hwords : wordsOf (witListV5 N w)=wordsOf (headerBytesV5 w)++wordsOf (wctBytesV5 N w.signature)++
      [0]++wordsOf ((List.finRange 4).flatMap (layerRegionV6 N w)) := by
    unfold witListV5
    rw [wordsOf_append _ _ (by simp only[List.length_append,headerBytesV5_length,wctBytesV5_length,zeros,List.length_replicate]),
      wordsOf_append _ _ (by simp only[List.length_append,headerBytesV5_length,wctBytesV5_length]),
      wordsOf_append _ _ (by rw[headerBytesV5_length])]
    have hz : wordsOf (zeros 8)=[0] := by
      rw [show zeros 8=List.replicate (8*1) 0 by rfl,wordsOf_replicate_zero];rfl
    rw [hz]
  intro i hi hz
  rw [hwords]
  rcases hz with hz|hz
  · have hm:=congrArg (fun l:List Word=>l.getD i 0) hh
    rw [readWords_getD _ _ _ _ (by omega)] at hm
    rw [hm]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_append,hlenh,hlenf,List.length_cons,List.length_nil,
      if_pos (show i<8 by omega),if_pos (show i<8+1152 by omega),if_pos (show i<8+1152+1 by omega)]
  · have hm:=congrArg (fun l:List Word=>l.getD (i-1161) 0) htail
    rw [readWords_getD _ _ _ _ (by omega),show 11336+8*(i-1161)=2048+8*i by omega] at hm
    rw [hm]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_append,hlenh,hlenf,List.length_cons,List.length_nil,
      if_neg (show ¬i<8+1152+1 by omega)]
#print axioms main_words_of_regions
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem legacy_word (N : HashOutput) (w : WCT9.Witness) (i : Nat) (hi : i<3104) :
    (wordsOf (witList N w)).getD i 0=(witEnc N w).extractLsb' (8*(8*i)) 64 := by
  rw [wordsOf_getD _ 3104 (witList_length_eq N w) i hi]
  unfold ClaudeWCT.W9.T3M.witEnc
  rw [show (64:Nat)=8*8 by rfl,extract_readLE_lt _ 24828 (witList_readLE_lt N w) (8*i) 8]
  rfl
#print axioms legacy_word
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem finish_steps {im : Image} (hcompact : CompactCodeAt im)
    (hz : SharedZero.ClearCode im) (hc : ∀k:Fin 9,SharedScatter.CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) SharedScatter.afterCode)
    (hf : CodeAt im (pcOf 47005) SharedScatter.finishCode)
    (hj : CodeAt im (pcOf 43761) [0x24c0306f])
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec.CBytes)
    (s : MachineState) (hpc : s.pc=pcOf 41108)
    (hout : OutAt s 96 output) (hp : PlanAt s) (hlp : Compact2.LPlanAt s) (htp : Compact2.TopTabAt s)
    (hmain : ∀i,i<2873 → (i ≤ 4 ∨ 1161 ≤ i) → s.getMem (BitVec.ofNat 64 (2048+8*i))=
      (wordsOf (witListV5 output (Paired.mainWitness witness))).getD i 0)
    (hc3 : s.getMem 2080=(witness.counters 3).setWidth 64)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hplan : SharedScatter.PlanAt s) :
    ∃v,Steps im s 73712 73889 v ∧ v.pc=pcOf 47012 ∧ v.getReg .x5=1 ∧ v.getReg .x10=0 ∧
      readBuffer v 1312 24828=Paired.witEnc output witness := by
  obtain ⟨t,st,pt,main,ctr,keep⟩:=compact_main_steps hcompact output (Paired.mainWitness witness) s hpc hout hp hlp htp hmain
  have tin : SharedCompact.ForestAt t b := by
    intro k hk
    have old:=hin k hk
    exact ⟨(keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans old.1,
      (keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans old.2⟩
  have tout : OutAt t 96 output := by
    intro k hk
    exact (keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans (hout k hk)
  have tplan : SharedScatter.PlanAt t := by
    intro child j hj
    have hm:=Nat.mod_lt child.val (by decide : 0<32)
    have hh:=hplan child j hj
    rw [getByte_eq_word _ _ (by omega)] at hh ⊢
    rw [keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)]
    exact hh
  have ttail : ∀j,1020 ≤ j → j<3104 → t.getMem (BitVec.ofNat 64 (1312+8*j))=
      (Paired.witEnc output witness).extractLsb' (8*(8*j)) 64 := by
    intro j hj hj'
    rw [main j hj hj',legacy_word output (Paired.mainWitness witness) j hj',
      Paired.word_witEnc_tail output witness (8*j) (by omega)]
  obtain ⟨imm,hd,ho⟩:=jalTo_sound (show jalTo (0x24c0306f#32) 43761=some 46980 by decide)
  have jump:=jal_x0_step hj hd ho t pt
  obtain ⟨v,tv,pv,v5,v10,vout⟩:=SharedScatter.clear_scatter_finish hz hc ha hf output witness b
    (t.setPC (pcOf 46980)) rfl tin hforest tplan tout (ctr.trans hc3) ttail
  exact ⟨v,((st.trans jump).trans tv).of_eq (by norm_num) (by norm_num),pv,v5,v10,vout⟩
#print axioms finish_steps
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit lval lpath CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame HalfAt ltable rlWit_range)
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem region_not_written (index : Nat) (lay : Layer) (A : Nat)
    (hlo : lBase lay ≤ A) (hhi : A<lBase lay+64*(height lay+chainCount lay))
    (hW : ¬RlWit lay (route index lay).1 (lWC lay) (lWM lay) A)
    (hctr : A≠lBase lay+32) : ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  intro h
  rcases h with h|h|⟨lay',_,h|h|h⟩
  · unfold Search.CsW Search.DigW at h
    have hb:=region_bounds lay
    simp only [ENC,EOUT,DIGITS] at h;omega
  · have hb:=region_bounds lay
    simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,Search.NODE,Search.NOUT,LEAFPK,ENC] at h;omega
  · exact hctr (lD_in_region lay lay' A hlo hhi h)
  · by_cases he:lay'=lay
    · subst he;exact hW h
    · exact rlWit_region lay lay' _ A hlo hhi he h
  · have hb:=region_bounds lay
    have hc:=h.2.1
    omega

theorem layer_regions (N : HashOutput) (w : WCT9.Witness) (s t : MachineState)
    (hout : ∀lay:Layer,LayerOut t w.signature (WCT9.digestIndex N) lay (w.counters lay))
    (hhalf : HalfFrame s t 4)
    (hframe : Frame s t (SigGolfCandidate.T3M.Expand.SharedLayers.LW (WCT9.digestIndex N) 4))
    (hz : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0) :
    ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
      wordsOf (layerRegionV6 N w lay) := by
  intro lay
  have hrb:=region_bounds lay
  have hv : ∀i (h:i<chainCount lay),DigAt t (lWC lay-64*i+48) ((w.signature.layers lay).values ⟨i,h⟩) := by
    intro i hi
    simpa only [lval,dif_pos hi,WCT9.toT3Signature] using (hout lay).2.1 i hi
  have hp : ∀j (h:j<height lay),DigAt t (lWM lay-64*j+SigGolfCandidate.T3M.Expand.sideOff (route (WCT9.digestIndex N) lay).1 j)
      ((w.signature.layers lay).path ⟨j,h⟩) := by
    intro j hj
    simpa only [lpath,dif_pos hj,WCT9.toT3Signature] using (hout lay).2.2 j hj
  have zero (A : Nat) (hlo : lBase lay ≤ A) (hhi : A<lBase lay+64*(height lay+chainCount lay))
      (hn : ¬RlWit lay (route (WCT9.digestIndex N) lay).1 (lWC lay) (lWM lay) A)
      (hc : A≠lBase lay+32) : t.getMem (BitVec.ofNat 64 A)=0 := by
    rw [hframe.get (by omega) (region_not_written _ lay A hlo hhi hn hc)]
    exact hz A (by omega) (by omega)
  unfold layerRegionV6
  split
  · rename_i h0
    refine layer_words t lay _ _ hv hp (fun A h1 h2 hn=>?_)
    by_cases he:A=lBase lay+32
    · have e:lay=0:=Fin.ext h0
      subst e
      rw [hframe.get (by omega) ?_]
      · exact hz A (by omega) (by omega)
      · rintro (h|h|⟨l,_,h|h|h⟩)
        · simp only [Search.CsW,Search.DigW,ENC,EOUT,DIGITS] at h;norm_num [lBase] at he;omega
        · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,CHAIN,Search.NODE,Search.NOUT,LEAFPK,ENC] at h;norm_num [lBase] at he;omega
        · have hd:=lD_cases l;norm_num [lBase] at he;omega
        · by_cases hl:l=0
          · subst hl;exact hn h
          · exact rlWit_region 0 l _ A h1 h2 hl h
        · have hc:=h.2.1;norm_num [lBase] at he;omega
    · exact zero A h1 h2 hn he
  · rename_i h0
    refine layerBC_words t lay _ _ _ hv hp ?_ zero
    let prev : Layer := Fin.ofNat 4 (lay.val-1)
    have hd : lD prev=lBase lay+32:=lD_above lay h0
    have hlo:=(hout prev).1
    simp only [HalfAt,lk_zero,Nat.mul_zero,hd] at hlo
    have hhi:=hhalf (lBase lay+32) 1 (by rw [←hd];rcases lD_cases prev with h|h|h|h <;> simp[h]) (by decide)
      (by intro l hl he;rw[lk_zero] at he;exact absurd he.2 (by decide))
    simp only [Nat.mul_one] at hhi
    rw [hz _ (by omega) (by fin_cases lay <;> simp_all [lBase,height,chainCount]) ] at hhi
    rw [dword_of_halves (t.getMem (BitVec.ofNat 64 (lBase lay+32))),hlo,hhi]
    simp [prev]
#print axioms layer_regions
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit lval lpath sideOff)
open SigGolfCandidate.T3M.Expand.BC (LayerOut)
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem regions_fillTop (N : HashOutput) (w : WCT9.Witness) (s t : MachineState) (c : Nat)
    (hproj : WCT9.fillTop w.signature 0=w.signature)
    (hregions : ∀lay:Layer,s.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
      wordsOf (layerRegionV6 N w lay))
    (hout : LayerOut s w.signature (WCT9.digestIndex N) 0 (w.counters 0))
    (hz : ∀A,0x2c48 ≤ A → A<0x2c48+64*66 →
      ¬RlWit 0 (route (WCT9.digestIndex N) 0).1 (lWC 0) (lWM 0) A → s.getMem (BitVec.ofNat 64 A)=0)
    (hzero : c=0 → Frame s t (fun _=>False))
    (hwritten : c≠0 → t.getMem (BitVec.ofNat 64 (0x2c48+sOff (WCT9.digestIndex N)))=
      hi64 (WCT9.setTop (WCT9.topSib w.signature) c))
    (hf : Frame s t (fun A=>(NODE ≤ A ∧ A<NODE+64) ∨ (NOUT ≤ A ∧ A<NOUT+32) ∨ A=0x2c48+sOff (WCT9.digestIndex N))) :
    ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
      wordsOf (layerRegionV6 N {w with signature:=WCT9.fillTop w.signature c} lay) := by
  intro lay
  by_cases hc:c=0
  · subst hc
    rw [frame_readWords (hzero rfl) _ _ (by have:=region_bounds lay;omega) (by simp),hregions lay,hproj]
  have hso:=sOff_cases (WCT9.digestIndex N)
  have hrb:=region_bounds lay
  by_cases hl0:lay.val=0
  swap
  · have hge : 0x3cc8 ≤ lBase lay := by fin_cases lay <;> first | exact absurd rfl hl0 | decide
    rw [frame_readWords hf _ _ (by omega) (by intro i hi h;simp only [NODE,NOUT] at h;omega),hregions lay]
    unfold layerRegionV6
    rw [if_neg hl0,if_neg hl0]
    change _=wordsOf (layerBytesBCV6 lay _ (WCT9.fillLayer lay (w.signature.layers lay) c) _)
    rw [WCT9.fillLayer_ne _ _ _ hl0]
  have h0:lay=0:=Fin.ext hl0
  subst h0
  have hsoe:=sOff_eq (WCT9.digestIndex N)
  unfold layerRegionV6
  rw [if_pos (show (0:Layer).val=0 by rfl)]
  refine layer_words t 0 _ _ (fun i hi=>?_) (fun j hj=>?_) (fun A h1 h2 hn=>?_)
  · have d:=hout.2.1 i hi
    simp only [lval,dif_pos hi,WCT9.toT3Signature] at d
    have hi54:i<54:=hi
    change DigAt t (0x3c88-64*i+48) ((w.signature.layers 0).values ⟨i,hi⟩)
    exact ⟨(hf.get (by omega) (by simp only [NODE,NOUT];omega)).trans d.1,
      (hf.get (by omega) (by simp only [NODE,NOUT];omega)).trans d.2⟩
  · have d:=hout.2.2 j hj
    simp only [lpath,dif_pos hj,WCT9.toT3Signature] at d
    have h12:j<12:=hj
    have hs : sideOff (route (WCT9.digestIndex N) 0).1 j ≤ 48 := by unfold sideOff;split <;> omega
    rw [show lWM (0:Layer)=0x2f08 by rfl] at d ⊢
    change DigAt t _ ((WCT9.fillLayer 0 (w.signature.layers 0) c).path ⟨j,hj⟩)
    unfold WCT9.fillLayer
    dsimp only
    by_cases hj11:j=11
    · subst hj11
      rw [if_pos ⟨rfl,rfl⟩]
      constructor
      · rw [hf.get (by omega) (by simp only [NODE,NOUT];omega),d.1]
        exact (lo64_setTop _ c).symm
      · rw [show 0x2f08-64*11+sideOff (route (WCT9.digestIndex N) 0).1 11+8=0x2c48+sOff (WCT9.digestIndex N) by omega,
          hwritten hc]
        rfl
    · rw [if_neg (fun h=>hj11 h.2)]
      exact ⟨(hf.get (by omega) (by simp only [NODE,NOUT];omega)).trans d.1,
        (hf.get (by omega) (by simp only [NODE,NOUT];omega)).trans d.2⟩
  · have h1':0x2c48 ≤ A:=h1
    have h2':A<0x2c48+64*66:=h2
    have hne:A≠0x2c48+sOff (WCT9.digestIndex N) := by
      intro he
      apply hn
      refine Or.inr ⟨11,by decide,Or.inr ?_⟩
      rw [show lWM (0:Layer)=0x2f08 by rfl]
      omega
    rw [hf.get (by omega) (by simp only [NODE,NOUT];omega)]
    exact hz A h1' h2' hn
#print axioms regions_fillTop
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit lval lpath CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame HalfAt ltable rlWit_range)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layer_not_low (index A : Nat) (ha : A<0x2c48) (hc : A≠0x820) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hD|hD|hD|hD <;> omega
  · have:=rlWit_range h;have:=SigGolfCandidate.T3M.Expand.BC.ltable_lo lay;omega
  · have:=h.2.1;omega

theorem layer_not_high (index A : Nat) (ha : 0xff0000 ≤ A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hD|hD|hD|hD <;> omega
  · have:=rlWit_range h;have:=ltable lay;omega
  · have:=h.2.2;omega

theorem layer_header (N : HashOutput) (w : WCT9.Witness) (s t : MachineState)
    (hout : LayerOut t w.signature (WCT9.digestIndex N) 3 (w.counters 3))
    (hhalf : HalfFrame s t 4)
    (hframe : Frame s t (SigGolfCandidate.T3M.Expand.SharedLayers.LW (WCT9.digestIndex N) 4))
    (hr : DigAt s 2048 w.signature.rho)
    (hc : s.getMem 2064=BitVec.ofNat 64 w.digestCounter.toNat)
    (hz : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0) :
    t.readWords (BitVec.ofNat 64 2048) 8=wordsOf (headerBytesV5 w) ∧
      t.getMem 2080=BitVec.ofNat 64 (w.counters 3).toNat := by
  have ctr : t.getMem 2080=BitVec.ofNat 64 (w.counters 3).toNat := by
    have hlo:=hout.1
    change (t.getMem 2080).extractLsb' 0 32=w.counters 3 at hlo
    have hhi:=hhalf 2080 1 (by simp) (by decide) (by intro lay hl h;rw [lk_zero] at h;omega)
    rw [hz 4 (by decide) (by decide)] at hhi
    have hh : (t.getMem 2080).extractLsb' 32 32=0:=hhi
    rw [dword_of_halves (t.getMem 2080),hlo,hh]
    simp
  have r0:= (hframe.get (by decide) (layer_not_low _ 2048 (by decide) (by decide))).trans hr.1
  have r1:= (hframe.get (by decide) (layer_not_low _ 2056 (by decide) (by decide))).trans hr.2
  have dc:= (hframe.get (by decide) (layer_not_low _ 2064 (by decide) (by decide))).trans hc
  have zero (i:Nat) (hi:3 ≤ i) (hi':i<8) (hne:i≠4) : t.getMem (BitVec.ofNat 64 (2048+8*i))=0 := by
    rw [hframe.get (by omega) (layer_not_low _ _ (by omega) (by omega))]
    exact hz i hi hi'
  have ctr' : t.getMem (BitVec.ofNat 64 (2048+32))=BitVec.ofNat 64 (w.counters 3).toNat:=ctr
  refine ⟨?_,ctr⟩
  rw [headerW_words,readWords_eight,r0,r1,dc,zero 3 (by decide) (by decide) (by decide),
    ctr',
    zero 5 (by decide) (by decide) (by decide),zero 6 (by decide) (by decide) (by decide),
    zero 7 (by decide) (by decide) (by decide)]

#print axioms layer_header
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT OutAt)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (ltable rlWit_range)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

def Keep (A : Nat) : Prop := A<256 ∨ A=0x20550 ∨ (0x7000 ≤ A ∧ A<0x7760) ∨ 0xff0000 ≤ A

structure Stable (output : HashOutput) (b : SharedCodec.CBytes) (pk : Digest) (s : MachineState) : Prop where
  digest : OutAt s 96 output
  forest : SharedCompact.ForestAt s b
  plan : PlanAt s
  lplan : Compact2.LPlanAt s
  toptab : Compact2.TopTabAt s
  scatterPlan : SharedScatter.PlanAt s
  pk : DigAt s 0xA0 pk
  index : s.getMem (0x20550#64)=BitVec.ofNat 64 (WCT9.digestIndex output)
  threshold1 : ∀r,r<48 → s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (WCT9.CanonicalPolicy.threshold 1 r)
  threshold2 : ∀r,r<35 → s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (WCT9.CanonicalPolicy.threshold 2 r)

theorem Stable.frame {output : HashOutput} {b : SharedCodec.CBytes} {pk : Digest} {s t : MachineState}
    {W : Nat → Prop} (h : Stable output b pk s) (hf : Frame s t W)
    (hn : ∀A,Keep A → ¬W A) : Stable output b pk t := by
  have word (A:Nat) (ha:A<2^64) (hk:Keep A) : t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := hf.get ha (hn A hk)
  have byte (A:Nat) (ha:A<2^64) (hk:0xff0000 ≤ A) : t.getByte (BitVec.ofNat 64 A)=s.getByte (BitVec.ofNat 64 A) :=
    hf.getByte ha (hn _ (Or.inr (Or.inr (Or.inr (by omega)))))
  constructor
  · intro k hk;rw [word _ (by omega) (Or.inl (by omega))];exact h.digest k hk
  · intro k hk
    have d:=h.forest k hk
    exact ⟨(word _ (by omega) (Or.inr (Or.inr (Or.inl (by omega))))).trans d.1,
      (word _ (by omega) (Or.inr (Or.inr (Or.inl (by omega))))).trans d.2⟩
  · intro k hk;rw [word _ (by unfold PLAN;omega) (Or.inr (Or.inr (Or.inr (by unfold PLAN;omega))))];exact h.plan k hk
  · intro k hk;rw [word _ (by unfold Compact2.LPLAN;omega) (Or.inr (Or.inr (Or.inr (by unfold Compact2.LPLAN;omega))))];exact h.lplan k hk
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [word _ (by unfold Compact2.TOPA;omega) (by unfold Keep Compact2.TOPA;omega)];exact h.toptab.1 k hk
    · rw [word _ (by unfold Compact2.TOPB;omega) (by unfold Keep Compact2.TOPB;omega)];exact h.toptab.2 k hk
  · intro child j hj;rw [byte _ (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by omega)];exact h.scatterPlan child j hj
  · exact ⟨(word _ (by decide) (Or.inl (by decide))).trans h.pk.1,(word _ (by decide) (Or.inl (by decide))).trans h.pk.2⟩
  · exact (word _ (by decide) (Or.inr (Or.inl rfl))).trans h.index
  · intro r hr;rw [byte _ (by omega) (by omega)];exact h.threshold1 r hr
  · intro r hr;rw [byte _ (by omega) (by omega)];exact h.threshold2 r hr

theorem layer_keep (index A : Nat) (hk : Keep A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rcases hk with hk|rfl|hk|hk
  · exact layer_not_low index A (by omega) (by omega)
  · rintro (h|h|⟨lay,_,h|h|h⟩)
    · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
    · rcases lD_cases lay with hD|hD|hD|hD <;> omega
    · have:=rlWit_range h;have:=ltable lay;omega
    · have:=h.2.1;omega
  · rintro (h|h|⟨lay,_,h|h|h⟩)
    · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
    · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
    · rcases lD_cases lay with hD|hD|hD|hD <;> omega
    · have:=rlWit_range h;have:=ltable lay;omega
    · have:=h.2.1;omega
  · exact layer_not_high index A hk

def H2Writes (index A : Nat) : Prop := (NODE ≤ A ∧ A<NODE+64) ∨ (NOUT ≤ A ∧ A<NOUT+32) ∨ A=0x2c48+sOff index

theorem h2_keep (index A : Nat) (hk : Keep A) : ¬H2Writes index A := by
  have:=sOff_cases index
  unfold Keep at hk
  unfold H2Writes
  simp only [NODE,NOUT]
  omega
#print axioms Stable.frame
#print axioms layer_keep
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M height chainCount route)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit)
open SigGolfCandidate.T3M.Expand.BC (LayerOut)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def topProgram (output : HashOutput) (w : SharedForest.Witness) (folded root pk : Digest) :
    M (Option (HashOutput × SharedForest.Witness)) :=
  (if root=pk then pure (some 0) else WCT9.searchTop (WCT9.digestIndex output) folded (WCT9.topSib (SharedForest.mainSignature w.signature)) pk WCT9.searchFuel 1) >>= fun c=>
  pure (c.map fun c=>(output,{w with signature:=SharedForest.fillTopSignature w.signature c}))

def Done (r : Option (HashOutput × SharedForest.Witness)) (s : MachineState) : Prop :=
  match r with
  | none => s.pc=pcOf 354
  | some (output,w) => s.pc=pcOf 47012 ∧ s.getReg .x5=1 ∧ s.getReg .x10=0 ∧
      readBuffer s 1312 24828=Paired.witEnc output w

structure TopReady (output : HashOutput) (w : SharedForest.Witness) (b : SharedCodec.CBytes)
    (folded root pk : Digest) (s : MachineState) : Prop where
  pc : s.pc=pcOf 42795
  x5 : s.getReg .x5=0
  root : DigAt s ENC root
  stable : Stable output b pk s
  indexLt : WCT9.digestIndex output<2^31
  top : ∀i,i<8 → s.getMem (BitVec.ofNat 64 (NODE+8*i))=
    (blkW (WCT9.digestIndex output) folded (WCT9.topSib (SharedForest.mainSignature w.signature))).getD i 0
  proj : WCT9.fillTop (SharedForest.mainSignature w.signature) 0=SharedForest.mainSignature w.signature
  header : s.readWords 2048 8=wordsOf (headerBytesV5 (Paired.mainWitness w))
  regions : ∀lay:Layer,s.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
    wordsOf (layerRegionV6 output (Paired.mainWitness w) lay)
  layer : LayerOut s (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) 0 (w.counters 0)
  zero : ∀A,0x2c48 ≤ A → A<0x2c48+64*66 →
    ¬RlWit 0 (route (WCT9.digestIndex output) 0).1 (lWC 0) (lWM 0) A → s.getMem (BitVec.ofNat 64 A)=0
  ctr3 : s.getMem 2080=(w.counters 3).setWidth 64
  forest : w.signature.forest=(SharedCodec.sigDecC b).forest

theorem top_good {im : Image} {sk : BitVec 256} (hsearch : SrchCoreAt im)
    (hcompact : CompactCodeAt im) (hz : SharedZero.ClearCode im)
    (hc : ∀k:Fin 9,SharedScatter.CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) SharedScatter.afterCode)
    (hf : CodeAt im (pcOf 47005) SharedScatter.finishCode)
    (hj : CodeAt im (pcOf 43761) [0x24c0306f])
    (hentry : CodeAt im (pcOf 351) [0x4d52706f])
    {output : HashOutput} {w : SharedForest.Witness} {b : SharedCodec.CBytes} {folded root pk : Digest} {s : MachineState}
    (h : TopReady output w b folded root pk s) :
    TBSim im sk s 2040040 (topProgram output w folded root pk) Done := by
  have hsib : WCT9.setTop (WCT9.topSib (SharedForest.mainSignature w.signature)) 0=
      WCT9.topSib (SharedForest.mainSignature w.signature) := by
    rw [←WCT9.topSib_fillTop,h.proj]
  have call:=search_entry_core (sk:=sk) hsearch (WCT9.digestIndex output) h.indexLt folded
    (WCT9.topSib (SharedForest.mainSignature w.signature)) root pk hsib s h.pc h.x5 h.root
    h.stable.pk.1 h.stable.pk.2 h.stable.index h.top
  unfold topProgram
  refine (TBSim.bind (W₂:=73890) call (fun result t ht=>?_)).mono (W':=2040040) (by norm_num) (fun _ _ h=>h)
  cases result with
  | none => exact (TBSim.pure (Q:=Done) (a:=none) ht).mono (by omega) (fun _ _ h=>h)
  | some c =>
    obtain ⟨tp,tzero,tnonzero⟩:=ht
    have frame : Frame s t (H2Writes (WCT9.digestIndex output)) := by
      by_cases hz:c=0
      · exact (tzero hz).mono (by simp)
      · exact (tnonzero hz).2.2
    have stable:=h.stable.frame frame (h2_keep (WCT9.digestIndex output))
    let w' : SharedForest.Witness:={w with signature:=SharedForest.fillTopSignature w.signature c}
    have regs : ∀lay:Layer,t.readWords (BitVec.ofNat 64 (lBase lay)) (8*(height lay+chainCount lay))=
        wordsOf (layerRegionV6 output (Paired.mainWitness w') lay) := by
      exact regions_fillTop output (Paired.mainWitness w) s t c h.proj h.regions h.layer h.zero
        tzero (fun hc=>(tnonzero hc).2.1) frame
    have head : t.readWords 2048 8=wordsOf (headerBytesV5 (Paired.mainWitness w')) := by
      change t.readWords (BitVec.ofNat 64 2048) 8=_
      rw [frame_readWords frame 2048 8 (by decide) (by
        intro i hi hw;unfold H2Writes at hw;simp only [NODE,NOUT] at hw
        have:=sOff_cases (WCT9.digestIndex output);omega)]
      exact h.header
    have ctr : t.getMem 2080=(w'.counters 3).setWidth 64 := by
      change t.getMem (BitVec.ofNat 64 2080)=_
      rw [frame.get (A:=2080) (by decide) (by unfold H2Writes;simp only [NODE,NOUT];have:=sOff_cases (WCT9.digestIndex output);omega)]
      exact h.ctr3
    have fields:=main_words_of_regions t output (Paired.mainWitness w') head regs
    obtain ⟨imm,hd,ho⟩:=jalTo_sound (show jalTo (0x4d52706f#32) 351=some 41108 by decide)
    have jump:=jal_x0_step hentry hd ho t tp
    obtain ⟨v,tv,vp,v5,v10,vout⟩:=finish_steps hcompact hz hc ha hf hj output w' b
      (t.setPC (pcOf 41108)) rfl stable.digest stable.plan stable.lplan stable.toptab fields ctr stable.forest
      h.forest stable.scatterPlan
    exact TBSim.steps (jump.trans tv) (TBSim.pure ⟨vp,v5,v10,vout⟩)
#print axioms top_good
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (HashOutput)

def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage,Images.expandImage,Images.verifyImage⟩

def pairedExpandCost : Nat := 4050000000

def PairedExpPost : Option (HashOutput × SigGolfCandidate.Research.SharedForest.Witness) → MachineState → Prop
  | none,t => (t.pc=pcOf 356 ∨ t.pc=pcOf 45231) ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧
      fetch Images.expandImage t=some (.base .ECALL)
  | some (output,w),t => t.pc=pcOf 47012 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t 1312 24828=ClaudeWCT.W9.T3M.Paired.witEnc output w ∧
      fetch Images.expandImage t=some (.base .ECALL)
end ClaudeWCT.W9.Machine.ExpandLink

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit CHAIN LEAFPK TopBlkG)
open SigGolfCandidate.T3M.Expand.BC (LayerOut HalfFrame ltable rlWit_range)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem top_not_written (index A : Nat) (ha : 0x2c48 ≤ A) (hb : A<0x2c48+64*66)
    (hn : ¬RlWit 0 (route index 0).1 (lWC 0) (lWM 0) A) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hd|hd|hd|hd <;> omega
  · by_cases he:lay=0
    · subst he;exact hn h
    · exact rlWit_region 0 lay _ A ha hb he h
  · have:=h.2.1;omega

theorem ready_of_layers {output : HashOutput} {w : SharedForest.Witness} {b : SharedCodec.CBytes}
    {pk folded root : Digest} {s t u : MachineState}
    (hi : WCT9.digestIndex output<2^31)
    (stable : Stable output b pk s)
    (hr : DigAt s 2048 w.signature.rho)
    (hdc : s.getMem 2064=BitVec.ofNat 64 w.digestCounter.toNat)
    (hzhead : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0)
    (hzregions : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hproj : WCT9.fillTop (SharedForest.mainSignature w.signature) 0=SharedForest.mainSignature w.signature)
    (hforest : w.signature.forest=(SharedCodec.sigDecC b).forest)
    (hout : ∀lay:Layer,LayerOut t (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) lay (w.counters lay))
    (hhalf : HalfFrame s t 4)
    (hframe : Frame s t (SigGolfCandidate.T3M.Expand.SharedLayers.LW (WCT9.digestIndex output) 4))
    (hroot : DigAt t ENC root)
    (hblk : TopBlkG (WCT9.toT3Signature (SharedForest.mainSignature w.signature)) (WCT9.digestIndex output) 0 folded t)
    (hu : Frame t u (fun _=>False)) (up : u.pc=pcOf 42795) (u5 : u.getReg .x5=0) :
    TopReady output w b folded root pk u := by
  have mem (A:Nat) (ha:A<2^64) : u.getMem (BitVec.ofNat 64 A)=t.getMem (BitVec.ofNat 64 A):=hu.get ha (by simp)
  have rs:=layer_regions output (Paired.mainWitness w) s t hout hhalf hframe hzregions
  have hs:=layer_header output (Paired.mainWitness w) s t (hout 3) hhalf hframe hr hdc hzhead
  constructor
  · exact up
  · exact u5
  · exact ⟨(mem _ (by unfold ENC;omega)).trans hroot.1,(mem _ (by unfold ENC;omega)).trans hroot.2⟩
  · exact (stable.frame hframe (layer_keep _)).frame hu (by simp)
  · exact hi
  · intro i hi
    rw [mem _ (by unfold NODE;omega)]
    exact topBlk_get (SharedForest.mainSignature w.signature) (WCT9.digestIndex output) folded t hblk i hi
  · exact hproj
  · change u.readWords (BitVec.ofNat 64 2048) 8=_
    rw [frame_readWords hu 2048 8 (by decide) (by simp)]
    exact hs.1
  · intro lay
    rw [frame_readWords hu _ _ (by have:=region_bounds lay;omega) (by simp)]
    exact rs lay
  · rcases hout 0 with ⟨ctr,values,paths⟩
    refine ⟨?_,?_,?_⟩
    · unfold SigGolfCandidate.T3M.Expand.BC.HalfAt at ctr ⊢
      rw [mem _ (by rw [show lD (0:Layer)=0x3ce8 by rfl];omega)]
      exact ctr
    · intro i hi
      exact ⟨(mem _ (by have:=ltable (0:Layer);omega)).trans (values i hi).1,
        (mem _ (by have:=ltable (0:Layer);omega)).trans (values i hi).2⟩
    · intro j hj
      have hh:SigGolfCandidate.T3M.Expand.sideOff (route (WCT9.digestIndex output) 0).1 j ≤ 48 := by
        unfold SigGolfCandidate.T3M.Expand.sideOff;split <;> omega
      exact ⟨(mem _ (by have:=ltable (0:Layer);omega)).trans (paths j hj).1,
        (mem _ (by have:=ltable (0:Layer);omega)).trans (paths j hj).2⟩
  · intro A ha hb hn
    rw [mem _ (by omega),hframe.get (by omega) (top_not_written _ A ha hb hn)]
    exact hzregions A ha (by omega)
  · change u.getMem (BitVec.ofNat 64 2080)=_
    rw [mem _ (by decide)]
    change t.getMem 2080=_
    exact hs.2.trans (BitVec.ofNat_toNat 64 (w.counters 3))
  · exact hforest
#print axioms ready_of_layers
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Expand (w9init)
open ClaudeWCT.W9.T3M.Final.Paired (ExpandRefines ExpandTerminates)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev PairedExpandSimulation : Prop := ∀(sk : SecretKey)(message : Message)(pk : PublicKey)(b : Bytes 5248),
  TBSim Images.expandImage sk (w9init Images.expandImage message pk b) pairedExpandCost
    (ClaudeWCT.W9.T3M.Paired.expandN message pk (ClaudeWCT.W9.T3M.SharedCodec.sigDecC b)) PairedExpPost

theorem pairedExpandCost_lt : pairedExpandCost+1<CYCLE_LIMIT := by decide +kernel

theorem paired_expand_initial (message : Message) (pk : PublicKey) (b : Bytes 5248) :
    initialState SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)=
      some (w9init Images.expandImage message pk b) := by
  unfold initialState
  rw [if_pos SigGolfCandidate.T3M.Paired.submission_expand_valid]
  simp only [inputBuffers,List.foldl_cons,List.foldl_nil]
  rfl

theorem paired_expPost_halt {o : Option (SigGolfCandidate.T3.HashOutput × SigGolfCandidate.Research.SharedForest.Witness)}
    {t : MachineState} (h : PairedExpPost o t) :
    fetch Images.expandImage t=some (.base .ECALL) ∧ t.getReg .x5=1 := by
  cases o with
  | none=>exact ⟨h.2.2.2,h.2.1⟩
  | some x=>exact ⟨h.2.2.2.2,h.2.1⟩

theorem paired_expPost_readout {o : Option (SigGolfCandidate.T3.HashOutput × SigGolfCandidate.Research.SharedForest.Witness)}
    {t : MachineState} (h : PairedExpPost o t) :
    o.map (fun x=>ClaudeWCT.W9.T3M.Paired.witEnc x.1 x.2)=
      if t.getReg .x10=0 then some (readOutput SigGolfCandidate.T3M.Paired.submission.sizes
        SigGolfCandidate.T3M.Paired.submission.layout .expand t) else none := by
  cases o with
  | none=>rw [if_neg (by rw [h.2.2.1];decide)];rfl
  | some x=>
    rw [if_pos h.2.2.1]
    exact congrArg some h.2.2.2.1.symm

theorem paired_expand_refines_of (H : PairedExpandSimulation) : ExpandRefines I0 := by
  intro message pk b
  apply Sim.run_eq SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)
    (paired_expand_initial message pk b) (H 0 message pk b) (Nat.lt_of_succ_lt pairedExpandCost_lt)
    (fun o=>o.map (fun x=>ClaudeWCT.W9.T3M.Paired.witEnc x.1 x.2))
  intro o t ht
  exact ⟨(paired_expPost_halt ht).1,(paired_expPost_halt ht).2,paired_expPost_readout ht⟩

theorem paired_expand_terminates_of (H : PairedExpandSimulation) : ExpandTerminates I0 := by
  intro hash message pk b
  obtain ⟨hf,hc⟩:=Sim.runWith SigGolfCandidate.T3M.Paired.submission .expand (message,pk,b)
    (paired_expand_initial message pk b) (H 0 message pk b) pairedExpandCost_lt
    (fun _ _ h=>paired_expPost_halt h) hash
  exact ⟨hf,lt_of_le_of_lt hc pairedExpandCost_lt⟩

theorem paired_expand_pending_of (H : PairedExpandSimulation) : ExpandRefines I0 ∧ ExpandTerminates I0 :=
  ⟨paired_expand_refines_of H,paired_expand_terminates_of H⟩
end ClaudeWCT.W9.Machine.ExpandLink

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M height chainCount route)
open SigGolfCandidate.T3M.Search (ENC NODE NOUT)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

structure LayersReady (output : HashOutput) (sig : SharedForest.Signature) (b : SharedCodec.CBytes)
    (counter : BitVec 32) (forest : Digest × Digest) (pk : Digest) (s : MachineState) : Prop where
  inv : SigGolfCandidate.T3M.Expand.SharedLayers.LInv (SharedForest.mainSignature sig) sig.policyHints
    (WCT9.digestIndex output) 4 (.pair forest.1 forest.2) s
  stable : Stable output b pk s
  rho : DigAt s 2048 sig.rho
  dc : s.getMem 2064=BitVec.ofNat 64 counter.toNat
  headerZero : ∀i,3 ≤ i → i<8 → s.getMem (BitVec.ofNat 64 (2048+8*i))=0
  regionZero : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : WCT9.fillTop (SharedForest.mainSignature sig) 0=SharedForest.mainSignature sig
  forestEq : sig.forest=(SharedCodec.sigDecC b).forest

def recoverProgram (output : HashOutput) (sig : SharedForest.Signature) (counter : BitVec 32)
    (forest : Digest × Digest) (pk : Digest) : M (Option (HashOutput × SharedForest.Witness)) :=
  SharedForest.recoverHintedLayers sig (WCT9.digestIndex output) (WCT9.topSib (SharedForest.mainSignature sig))
    4 (.pair forest.1 forest.2) >>= fun result=>
  match result with
  | none => pure none
  | some r => if SharedForest.policyHintsValid sig.policyHints r.digits then
      topProgram output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0⟩ r.foldedTop r.root pk
    else pure none

def SuffixDone (im : Image) (r : Option (HashOutput × SharedForest.Witness)) (s : MachineState) : Prop :=
  match r with
  | none => s.pc=pcOf 354 ∨ (s.pc=pcOf 356 ∧ s.getReg .x5=1 ∧ s.getReg .x10=1 ∧ fetch im s=some (.base .ECALL))
  | some p => Done (some p) s

theorem layers_good {sk : BitVec 256} {output : HashOutput} {sig : SharedForest.Signature}
    {b : SharedCodec.CBytes} {counter : BitVec 32} {forest : Digest × Digest} {pk : Digest} {s : MachineState}
    (h : LayersReady output sig b counter forest pk s) :
    TBSim Images.expandImage sk s 3620040100 (recoverProgram output sig counter forest pk) (SuffixDone Images.expandImage) := by
  have call:=SigGolfCandidate.T3M.Expand.SharedLayers.installed_recover_good (sk:=sk) (vin:=0) h.inv
  unfold recoverProgram
  refine TBSim.bind (W₂:=2040100) call (fun result t ht=>?_)
  cases result with
  | none => exact (TBSim.pure (Q:=SuffixDone Images.expandImage) (a:=none) (Or.inr ht)).mono (by omega) (fun _ _ h=>h)
  | some r =>
    dsimp only
    obtain ⟨tp,t5,troot,clen,dlen,fields,credits,half,regs,frame,_,top,hints,floors⟩:=ht
    have stable:=h.stable.frame frame (layer_keep _)
    have jump:=SharedControl.validate_step t tp
    let u:=t.setPC (pcOf 46929)
    obtain ⟨v,n,c,hn,hc,uv,vp,vr,vf⟩:=SharedValidate.validate_source_steps SharedValidate.installed_code
      u rfl sig.policyHints r.digits h.inv.hintsLt dlen (fun lay=>floors lay lay.isLt) hints
      (fun lay=>credits lay lay.isLt) SharedValidate.threshold1_lt SharedValidate.threshold2_lt
      stable.threshold1 stable.threshold2
    have tf : Frame t v (fun _=>False):=vf
    by_cases valid:SharedForest.policyHintsValid sig.policyHints r.digits=true
    · rw [if_pos valid] at vp ⊢
      have v5:v.getReg .x5=0 := (vr.get (by decide)).trans t5
      have ready:TopReady output ⟨sig,counter,fun lay=>r.counters.getD lay.val 0⟩ b r.foldedTop r.root pk v :=
        ready_of_layers h.inv.hidx h.stable h.rho h.dc h.headerZero h.regionZero h.proj h.forestEq
          (fun lay=>fields lay lay.isLt) half frame troot (top (by decide)) tf vp v5
      have result:=top_good (sk:=sk) SharedControl.installed_srchCore installed_compact SharedZero.installed_code
        SharedScatter.installed_coordinates SharedScatter.installed_after SharedScatter.installed_finish
        SharedControl.scatter_code SharedControl.compact_code ready
      exact (TBSim.steps (jump.trans uv) result).mono (by omega) (by
        intro rv st hp
        cases rv with
        | none => exact Or.inl hp
        | some p => exact hp)
    · rw [if_neg valid] at vp ⊢
      exact (TBSim.steps (jump.trans uv) (TBSim.pure (Q:=SuffixDone Images.expandImage) (a:=none) (Or.inl vp))).mono
        (by omega) (fun _ _ h=>h)
#print axioms layers_good
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest M)
open SigGolfCandidate.T3M.Search (ENC NODE TOP_DATA)
open SigGolfCandidate.T3M.Expand (CHAIN)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

structure ForestMemory (output : HashOutput) (b : SharedCodec.CBytes) (counter : BitVec 32) (pk : Digest) (s : MachineState) : Prop where
  stable : Stable output b pk s
  inflated : SharedCompact.InflatedAt s b
  hintsLt : (SharedCodec.sigDecC b).policyHints.toNat<5832
  hints : s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat
  dc : s.getMem 0x66008=BitVec.ofNat 64 counter.toNat
  c32 : ∃x<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x
  zero : SigGolfCandidate.T3M.Expand.BC.LZero s
  table : Search.TableOK s
  cf : Search.CfTableOK 0 s
  reward : Search.Reward.RewardTablesOK s
  regionZero : ∀A,0x2c48 ≤ A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : WCT9.fillTop (SharedForest.mainSignature (SharedCodec.sigDecC b)) 0=SharedForest.mainSignature (SharedCodec.sigDecC b)

theorem ForestMemory.frame {output : HashOutput} {b : SharedCodec.CBytes} {counter : BitVec 32} {pk : Digest}
    {s t : MachineState} (h : ForestMemory output b counter pk s)
    (hf : Frame s t (fun A=>1200 ≤ A ∧ A<9472)) : ForestMemory output b counter pk t := by
  have mem (A:Nat) (ha:A<2^64) (hn:¬(1200 ≤ A ∧ A<9472)) := hf.get ha hn
  constructor
  · exact h.stable.frame hf (by intro A hk;unfold Keep at hk;omega)
  · exact h.inflated.frame hf (by intro A ha hb;omega)
  · exact h.hintsLt
  · change t.getMem (BitVec.ofNat 64 0x66000)=_
    rw [mem _ (by decide) (by decide)]
    exact h.hints
  · change t.getMem (BitVec.ofNat 64 0x66008)=_
    rw [mem _ (by decide) (by decide)]
    exact h.dc
  · obtain ⟨x,hx,hm⟩:=h.c32
    exact ⟨x,hx,(mem _ (by unfold ENC;omega) (by unfold ENC;omega)).trans hm⟩
  · exact ⟨(mem _ (by unfold CHAIN;omega) (by unfold CHAIN;omega)).trans h.zero.c0,
      (mem _ (by unfold CHAIN;omega) (by unfold CHAIN;omega)).trans h.zero.c8,
      (mem _ (by unfold CHAIN;omega) (by unfold CHAIN;omega)).trans h.zero.c32,
      (mem _ (by unfold CHAIN;omega) (by unfold CHAIN;omega)).trans h.zero.c40,
      (mem _ (by unfold NODE;omega) (by unfold NODE;omega)).trans h.zero.n32,
      (mem _ (by unfold NODE;omega) (by unfold NODE;omega)).trans h.zero.n40,
      (mem _ (by unfold ENC;omega) (by unfold ENC;omega)).trans h.zero.e40⟩
  · exact h.table.frame hf (by intro i hi;unfold TOP_DATA;omega)
  · exact h.cf.frame hf (by intro i hi hj;unfold TOP_DATA;omega)
  · exact h.reward.frame hf (by intro i hi hj;unfold TOP_DATA;omega)
  · intro A ha hb;rw [mem _ (by omega) (by omega)];exact h.regionZero A ha hb
  · exact h.proj

theorem handoff_ready {output : HashOutput} {b : SharedCodec.CBytes} {counter : BitVec 32} {pk : Digest}
    {pair : Digest × Digest} {s t : MachineState}
    (h : ForestMemory output b counter pk s) (hi:WCT9.digestIndex output<2^31)
    (hp:t.pc=pcOf 249) (h5:t.getReg .x5=0)
    (hL:DigAt s 1312 pair.1) (hR:DigAt s 1360 pair.2)
    (hroots:∀o,(o=0 ∨ o=8 ∨ o=48 ∨ o=56) → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (1312+o)))
    (hrho:∀i,i<2 → t.getMem (BitVec.ofNat 64 (2048+8*i))=s.getMem (BitVec.ofNat 64 (0x7000+8*i)))
    (hdc:t.getMem 2064=s.getMem 0x66008)
    (hzero:∀i,3 ≤ i → i<8 → t.getMem (BitVec.ofNat 64 (2048+8*i))=0)
    (hmove:∀i,i<428 → t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i)))
    (hf:Frame s t SharedHandoff.Writes) :
    LayersReady output (SharedCodec.sigDecC b) b counter pair pk t := by
  constructor
  · exact SharedHandoff.layer_inv hp h5 hi h.stable.index h.inflated hL hR hroots hmove hf h.c32 h.zero h.table h.cf h.reward h.hintsLt h.hints
  · exact h.stable.frame hf (by intro A hk;unfold Keep at hk;unfold SharedHandoff.Writes;omega)
  · have d:=h.inflated 0 (by decide)
    change DigAt s 0x7000 (SharedCodec.sigDecC b).rho at d
    exact ⟨(hrho 0 (by decide)).trans d.1,(hrho 1 (by decide)).trans d.2⟩
  · exact hdc.trans h.dc
  · exact hzero
  · intro A ha hb
    rw [hf.get (by omega) (by unfold SharedHandoff.Writes;omega)]
    exact h.regionZero A ha hb
  · exact h.proj
  · rfl
#print axioms ForestMemory.frame
#print axioms handoff_ready
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

def forestProgram (output : HashOutput) (b : SharedCodec.CBytes) (counter : BitVec 32) (pk : Digest) :
    M (Option (HashOutput × SharedForest.Witness)) :=
  SharedForest.recoverForest (WCT9.digestIndex output) (SharedForest.forestSelectionFromOutput output)
    (SharedForest.forestWordsFromOutput output) (SharedCodec.sigDecC b).forest >>= fun pair=>
  recoverProgram output (SharedCodec.sigDecC b) counter pair pk

theorem forest_suffix_good {sk : BitVec 256} {output : HashOutput} {b : SharedCodec.CBytes}
    {counter : BitVec 32} {pk : Digest} {s : MachineState}
    (hi : WCT9.digestIndex output<2^31) (hm : ForestMemory output b counter pk s)
    (hI : SharedForestRun.Inv (Paired.witEnc output ⟨SharedCodec.sigDecC b,counter,fun _=>0⟩)
      (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s 0
      (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCodec.sigDecC b,counter,fun _=>0⟩)) s) :
    TBSim Images.expandImage sk s 3620044721 (forestProgram output b counter pk) (SuffixDone Images.expandImage) := by
  have call:=SharedForestRun.installed_forest_good sk output ⟨SharedCodec.sigDecC b,counter,fun _=>0⟩
    (WCT9.digestIndex output) hi s hI
  unfold forestProgram
  refine TBSim.bind (W₂:=3620042705) call (fun pair t ht=>?_)
  obtain ⟨tp,left,right,frame,fields⟩:=ht
  have memory:=hm.frame frame
  obtain ⟨u,tu,up,u2,u5,roots,rho,dc,zeros,moved,regs,fr⟩:=SharedHandoff.steps SharedHandoff.installed_code t tp
  have ready:=handoff_ready memory hi up u5 left right roots rho dc zeros moved fr
  exact TBSim.steps tu (layers_good ready)
#print axioms forest_suffix_good
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp SigGolfCandidate.T3 SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

theorem expandN_source (message : Message) (pk : Digest) (b : SharedCodec.CBytes)
    (hfill : SharedForest.fillTopSignature (SharedCodec.sigDecC b) 0=SharedCodec.sigDecC b) :
    Paired.expandN message pk (SharedCodec.sigDecC b)=
      if (SharedCodec.sigDecC b).policyHints.toNat ≥ 5832 then pure none else
        SharedForest.sharedDigestSearch (SharedCodec.sigDecC b).rho message 0 (2^21) >>= fun result=>
          match result with
          | none => pure none
          | some (counter,output)=>forestProgram output b counter pk := by
  unfold Paired.expandN
  rw [hfill]
  by_cases bad:(SharedCodec.sigDecC b).policyHints.toNat ≥ 5832
  · simp only [bad,ite_true]
  rw [if_neg bad,if_neg bad]
  apply congrArg (fun k=>SharedForest.sharedDigestSearch (SharedCodec.sigDecC b).rho message 0 (2^21) >>= k)
  funext result
  cases result with
  | none => rfl
  | some pair =>
    rcases pair with ⟨counter,output⟩
    unfold forestProgram recoverProgram
    apply congrArg (fun k=>SharedForest.recoverForest (WCT9.digestIndex output)
      (SharedForest.forestSelectionFromOutput output) (SharedForest.forestWordsFromOutput output)
      (SharedCodec.sigDecC b).forest >>= k)
    funext forest
    apply congrArg (fun k=>SharedForest.recoverHintedLayers (SharedCodec.sigDecC b) (WCT9.digestIndex output)
      (WCT9.topSib (SharedForest.mainSignature (SharedCodec.sigDecC b))) 4 (.pair forest.1 forest.2) >>= k)
    funext layers
    cases layers with
    | none => rfl
    | some layers =>
      dsimp only
      by_cases valid:SharedForest.policyHintsValid (SharedCodec.sigDecC b).policyHints layers.digits=true
      · simp only [valid,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
        unfold topProgram
        by_cases root:layers.root=pk
        · simp only [root,ite_true,pure_bind,Option.map_some,hfill]
        · simp only [root,ite_false]
          apply congrArg (fun k=>WCT9.searchTop (WCT9.digestIndex output) layers.foldedTop
            (WCT9.topSib (SharedForest.mainSignature (SharedCodec.sigDecC b))) pk WCT9.searchFuel 1 >>= k)
          funext c
          cases c <;> rfl
      · have vf : SharedForest.policyHintsValid (SharedCodec.sigDecC b).policyHints layers.digits=false :=
          Bool.eq_false_iff.mpr valid
        simp only [vf,Bool.not_false,Bool.false_eq_true,ite_true,ite_false]
#print axioms expandN_source
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M.Search (ENC)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research

structure InitialMemory (b : SharedCodec.CBytes) (pk : Digest) (s : MachineState) : Prop where
  plan : ClaudeWCT.W9.Machine.Expand.PlanAt s
  lplan : Compact2.LPlanAt s
  toptab : Compact2.TopTabAt s
  scatterPlan : SharedScatter.PlanAt s
  pk : DigAt s 0xA0 pk
  threshold1 : ∀r,r<48 → s.getByte (BitVec.ofNat 64 (16749456+r))=
    BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 1 r)
  threshold2 : ∀r,r<35 → s.getByte (BitVec.ofNat 64 (16749520+r))=
    BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 2 r)
  c32 : ∃x<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x
  zero : SigGolfCandidate.T3M.Expand.BC.LZero s
  table : Search.TableOK s
  cf : Search.CfTableOK 0 s
  reward : Search.Reward.RewardTablesOK s
  regionZero : ∀A,0x2c48≤A → A<0x61c8 → s.getMem (BitVec.ofNat 64 A)=0
  proj : ClaudeWCT.WCT9.fillTop (SharedForest.mainSignature (SharedCodec.sigDecC b)) 0=
    SharedForest.mainSignature (SharedCodec.sigDecC b)

theorem initial_memory (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    InitialMemory b pk (w9init Images.expandImage m pk b) := by
  have hp := SharedInit.initial_plans m pk b
  have ht := SharedInit.initial_tables m pk b
  have hf := SharedInit.initial_thresholds m pk b
  exact ⟨hp.1,hp.2,SharedInit.initial_toptab m pk b,(SharedInit.initial_data m pk b).plans,
    SharedInit.public_key_of_length Images.expandData_length m pk b,hf.1,hf.2,
    SharedInit.counter_of_length Images.expandData_length m pk b,
    SharedInit.layer_zero_of_length Images.expandData_length m pk b,
    ht.1,ht.2.1,ht.2.2,SharedInit.region_zero_of_length Images.expandData_length m pk b,
    SharedHandoff.main_projection b⟩

#print axioms initial_memory
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem halt_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) :
    CodeAt im (pcOf 47012) [0x73] := by
  exact SharedCounterHooks.code_slice (off:=1956) hc (by decide +kernel) (by decide +kernel)

theorem installed_halt : CodeAt Images.expandImage (pcOf 47012) [0x73] :=
  halt_of_driver codeAt_expand_shared_driver

theorem suffix_done {sk : BitVec 256} {r : Option (HashOutput × SharedForest.Witness)} {s : MachineState}
    (h : SuffixDone Images.expandImage r s) :
    TBSim Images.expandImage sk s 2 (pure r) ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost := by
  cases r with
  | none =>
    rcases h with hp|⟨hp,h5,h10,hfetch⟩
    · obtain ⟨t,st,tp,t5,t10,tfetch⟩:=Search.cs0_spec SharedSearchCode.installed_searchKernel s hp
      exact TBSim.steps st (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost) (a:=none)
        ⟨Or.inl tp,t5,t10,tfetch⟩)
    · exact (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost) (a:=none)
        ⟨Or.inl hp,h5,h10,hfetch⟩).mono (by omega) (fun _ _ h=>h)
  | some p =>
    obtain ⟨hp,h5,h10,hbytes⟩:=h
    have fetch:= (installed_halt.fetch s hp).trans rfl
    exact (TBSim.pure (Q:=ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost) (a:=some p)
      ⟨hp,h5,h10,hbytes,fetch⟩).mono (by omega) (fun _ _ h=>h)

theorem forest_suffix_halted {sk : BitVec 256} {output : HashOutput} {b : SharedCodec.CBytes}
    {counter : BitVec 32} {pk : Digest} {s : MachineState}
    (hi : WCT9.digestIndex output<2^31) (hm : ForestMemory output b counter pk s)
    (hI : SharedForestRun.Inv (Paired.witEnc output ⟨SharedCodec.sigDecC b,counter,fun _=>0⟩)
      (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s 0
      (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCodec.sigDecC b,counter,fun _=>0⟩)) s) :
    TBSim Images.expandImage sk s 3620044723 (forestProgram output b counter pk)
      ClaudeWCT.W9.Machine.ExpandLink.PairedExpPost := by
  simpa only [bind_pure] using
    (TBSim.bind (W₂:=2) (forest_suffix_good hi hm hI) (fun _ _ h=>suffix_done h))
#print axioms suffix_done
#print axioms forest_suffix_halted
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (ENC NODE TOP_DATA NBUF OutAt)
open SigGolfCandidate.T3M.Expand (CHAIN)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def ClearWrites (A:Nat) : Prop := A=0x66020 ∨ A=0x66008 ∨ A=0x66010 ∨ A=0x20550 ∨ (96≤A ∧ A<128) ∨ (1216≤A ∧ A<9472)

theorem memory_after_clear {s0 s t:MachineState} {output:HashOutput} {b:SharedCodec.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<5832)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output)
    (hctr:t.getMem 0x66008=BitVec.ofNat 64 counter.toNat)
    (hindex:t.getMem 0x20550=s.getMem 0x20160 >>> 33)
    (hdigest:∀i,i<4 → t.getMem (BitVec.ofNat 64 (96+8*i))=s.getMem (BitVec.ofNat 64 (NBUF+8*i)))
    (hf:Frame s t ClearWrites) : ForestMemory output b counter pk t := by
  have word (A:Nat) (ha:A<2^64) (hS:¬SharedFront.SearchWrites A) (hC:¬ClearWrites A) :
      t.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A) :=
    (hf.get ha hC).trans (hs.get ha hS)
  have highWord (A:Nat) (ha:A<2^64) (hA:0xff0000≤A) :
      t.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A) := by
    apply word A ha
    · unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes
      simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF];omega
    · unfold ClearWrites;omega
  have highByte (A:Nat) (ha:A<2^64) (hA:0xff0000≤A) :
      t.getByte (BitVec.ofNat 64 A)=s0.getByte (BitVec.ofNat 64 A) := by
    apply (hs.trans hf).getByte ha
    rintro (h|h)
    · unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes at h
      simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF] at h;omega
    · unfold ClearWrites at h;omega
  have inflated:SharedCompact.InflatedAt t b:=hin.frame hf (by intro A ha hb;unfold ClearWrites;omega)
  constructor
  · constructor
    · intro i hi;exact (hdigest i hi).trans (hout i hi)
    · exact inflated.forest
    · intro i hi;rw[highWord _ (by unfold PLAN;omega) (by unfold PLAN;omega)];exact initial.plan i hi
    · intro i hi;rw[highWord _ (by unfold Compact2.LPLAN;omega) (by unfold Compact2.LPLAN;omega)];exact initial.lplan i hi
    · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [highWord _ (by unfold Compact2.TOPA;omega) (by unfold Compact2.TOPA;omega)];exact initial.toptab.1 k hk
      · rw [highWord _ (by unfold Compact2.TOPB;omega) (by unfold Compact2.TOPB;omega)];exact initial.toptab.2 k hk
    · intro child j hj
      rw[highByte _ (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by omega)]
      exact initial.scatterPlan child j hj
    · constructor
      · exact (word 160 (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.pk.1
      · exact (word 168 (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.pk.2
    · change t.getMem (0x20550:Word)=_
      rw[hindex]
      have ho:s.getMem (0x20160:Word)=output.extractLsb' 0 64:=hout 0 (by decide)
      rw[ho];exact Compact2.index_shr output
    · intro r hr;rw[highByte _ (by omega) (by omega)];exact initial.threshold1 r hr
    · intro r hr;rw[highByte _ (by omega) (by omega)];exact initial.threshold2 r hr
  · exact inflated
  · exact hh
  · exact (hf.get (A:=0x66000) (by decide) (by unfold ClearWrites;decide)).trans hhmem
  · exact hctr
  · obtain ⟨x,hx,hm⟩:=initial.c32
    exact ⟨x,hx,(word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans hm⟩
  · exact ⟨(word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.c0,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.c8,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.c32,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.c40,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.n32,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.n40,
      (word _ (by decide) (by unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes;decide) (by unfold ClearWrites;decide)).trans initial.zero.e40⟩
  · intro i hi;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.table i hi
  · intro i hi hj;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.cf i hi hj
  · intro i hi hj;rw[highByte _ (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega)];exact initial.reward i hi hj
  · intro A ha hb
    rw[hf.get (by omega) (by unfold ClearWrites;omega)]
    by_cases hz:A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8
    · exact hsetup A hz
    · rw[hs.get (by omega) (by
        unfold SharedFront.SearchWrites SharedFront.Work SharedFront.Writes SharedCompact.policyAddress ClaudeWCT.W9.Machine.Sign.SharedDigest.writes
        simp only [SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF];omega)]
      exact initial.regionZero A ha hb
  · exact initial.proj
#print axioms memory_after_clear
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem cleared_front {s0 s:MachineState} {output:HashOutput} {b:SharedCodec.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<5832)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output) (h19:s.getReg .x19=BitVec.ofNat 64 counter.toNat)
    (h17:s.getReg .x17=0x20160) (hp:s.pc=pcOf 45226) :
    ∃t,Steps Images.expandImage s 3119 3119 t ∧ t.pc=pcOf 45257 ∧
      (∀ (off:Nat),off+8≤8160 → off%8=0 → t.getMem (BitVec.ofNat 64 (1312+off))=0) ∧
      t.getMem 417824=0 ∧ t.getMem 0x66010=BitVec.ofNat 64 (WCT9.digestIndex output) ∧
      OutAt t NBUF output ∧ ForestMemory output b counter pk t := by
  have jump:=ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary.expand_steps ClaudeWCT.W9.Machine.Expand.SharedDigestCode.installed_success s hp
  let u:=s.setPC (pcOf 45232)
  obtain ⟨t,ut,tp,zeros,mode,ctr,index,idx,digest,regs,frame⟩:=
    SharedZero.accepted_clear SharedZero.installed_code u rfl h17
  have memory:ForestMemory output b counter pk t:=
    memory_after_clear initial hin hh hhmem hs hsetup hout (ctr.trans h19) idx digest frame
  refine ⟨t,jump.trans ut,tp,?_,mode,?_,?_,memory⟩
  · intro off hb ha;exact zeros (1312+off) (by omega) (by omega) (by omega)
  · rw[index]
    have ho:u.getMem (0x20160:Word)=output.extractLsb' 0 64:=hout 0 (by decide)
    rw[ho];exact Compact2.index_shr output
  · intro i hi
    exact (frame.get (by unfold NBUF;omega) (by simp only [ClearWrites,NBUF];omega)).trans (hout i hi)
#print axioms cleared_front
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

theorem accepted_front {s0 s:MachineState} {output:HashOutput} {b:SharedCodec.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<5832)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output) (h19:s.getReg .x19=BitVec.ofNat 64 counter.toNat)
    (h17:s.getReg .x17=0x20160) (hp:s.pc=pcOf 45226)
    (hrank:∀k:Fin 9,SharedForest.rawForestRank output k.val<563) :
    ∃t,Steps Images.expandImage s 4375 4552 t ∧ ForestMemory output b counter pk t ∧
      SharedForestRun.Inv (Paired.witEnc output ⟨SharedCodec.sigDecC b,counter,fun _=>0⟩)
        (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
        (fun k=>SharedForest.forestRank output k.val) t 0
        (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCodec.sigDecC b,counter,fun _=>0⟩)) t := by
  obtain ⟨u,su,up,uz,um,ui,uo,uf⟩:=cleared_front initial hin hh hhmem hs hsetup hout h19 h17 hp
  have fields:=SharedForestRun.fields_of_output u output (WCT9.digestIndex output) ui uo hrank
  obtain ⟨t,ut,ht,hframe⟩:=SharedScatter.scatter_forest_pre SharedScatter.installed_coordinates SharedScatter.installed_after
    output ⟨SharedCodec.sigDecC b,counter,fun _=>0⟩ b (WCT9.digestIndex output) u up uf.inflated rfl
    fields uf.stable.scatterPlan um uz rfl
  exact ⟨t,su.trans ut,uf.frame hframe,ht⟩
#print axioms accepted_front
end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.Expand.SharedCompactMain
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.ExpandLink (PairedExpPost)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem initial_pc (message : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    (w9init Images.expandImage message pk b).pc=pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg,MachineState.pc_writeBytesAsWords,MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords,MachineState.pc_writeBytesAsWords]
  rfl

theorem initial_x5 (message : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    (w9init Images.expandImage message pk b).getReg .x5=0 := by
  unfold w9init
  rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
  simp only [MachineState.getReg_writeBytesAsWords]
  rfl

theorem initial_prepared (message : Message) (pk : PublicKey) (b : SharedCodec.CBytes)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<5832) :
    ∃t,Steps Images.expandImage (w9init Images.expandImage message pk b) 3249 3249 t ∧
      SharedFront.Prepared (w9init Images.expandImage message pk b) message b t := by
  exact SharedFront.prepare SharedCompact.installed_entry_codeAt SharedCompact.installed_adapter_codeAt
    SharedFront.installed_tail SharedFront.installed_zero SharedFront.installed_jump
    _ message b (initial_pc message pk b) (initial_x5 message pk b)
    (SharedInit.signatureWord Images.expandData_length SharedInit.installed_dataBase message pk b)
    (SharedInit.msgWord Images.expandData_length SharedInit.installed_dataBase message pk b)
    (SharedInit.initial_data message pk b) hh

theorem invalid_initial {sk : BitVec 256} (message : Message) (pk : PublicKey) (b : SharedCodec.CBytes)
    (hh:5832≤(SharedCodec.sigDecC b).policyHints.toNat) :
    TBSim Images.expandImage sk (w9init Images.expandImage message pk b) 17 (pure none) PairedExpPost := by
  obtain ⟨t,st,tp,regs,frame⟩:=SharedCompact.invalid_front SharedCompact.installed_entry_codeAt
    SharedCompact.installed_adapter_codeAt.tail SharedCompact.installed_adapter_codeAt.guard
    SharedFront.installed_invalid _ (initial_pc message pk b) _ hh
    (BitVec.isLt (SharedCodec.sigDecC b).policyHints)
    (SharedCompact.hints_of_signature _ b
      (SharedInit.signatureWord Images.expandData_length SharedInit.installed_dataBase message pk b))
  exact TBSim.steps st (suffix_done (r:=none) (Or.inl tp))

theorem searched_continue {sk : BitVec 256} {s0 s : MachineState} {pk : Digest} {b : SharedCodec.CBytes}
    (initial : InitialMemory b pk s0) (hh:(SharedCodec.sigDecC b).policyHints.toNat<5832)
    {r : Option (BitVec 32 × HashOutput)} (hs : SharedFront.Searched s0 b r s) :
    TBSim Images.expandImage sk s 3620049275
      (match r with | none=>pure none | some (counter,output)=>forestProgram output b counter pk) PairedExpPost := by
  cases r with
  | none =>
    obtain ⟨t,st,tp,t5,t10,regs,frame⟩:=Sign.SharedDigestBoundary.failure_steps true
      SharedDigestCode.installed_failure s hs.result
    have pc:t.pc=pcOf 45231:=tp
    have hf:fetch Images.expandImage t=some (.base .ECALL):=
      (SharedDigestCode.installed_failure_ecall.fetch t pc).trans rfl
    exact (TBSim.steps st (TBSim.pure (Q:=PairedExpPost) (a:=none)
      ⟨Or.inr pc,t5,t10,hf⟩)).mono (by omega) (fun _ _ h=>h)
  | some result =>
    rcases result with ⟨counter,output⟩
    obtain ⟨hp,h19,hc,ha,hout⟩:=hs.result
    have hrank:=((SharedForest.accepted_conditions output ha).2.1)
    obtain ⟨t,st,memory,inv⟩:=accepted_front initial hs.inflated hh hs.hints hs.frame hs.setupZero hout h19
      hs.resultR17 hp hrank
    exact TBSim.steps st (forest_suffix_halted (WCT9.digestIndex_lt output) memory inv)

end ClaudeWCT.W9.Machine.Expand.SharedCompactMain

namespace ClaudeWCT.W9.Machine.ExpandLink
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem paired_expand_tbsim : PairedExpandSimulation := by
  intro sk message pk b
  rw [expandN_source message pk b (SharedHandoff.decoded_projection b)]
  by_cases bad:5832≤(SharedCodec.sigDecC b).policyHints.toNat
  · rw [if_pos bad]
    exact (invalid_initial message pk b bad).mono (by decide) (fun _ _ h=>h)
  · rw [if_neg bad]
    have hh:(SharedCodec.sigDecC b).policyHints.toNat<5832:=by omega
    obtain ⟨t,st,ready⟩:=initial_prepared message pk b hh
    have search:=SharedFront.search_prepared (sk:=sk) SharedDigestCode.installed_look ready
    have continuation:=TBSim.bind (W₂:=3620049275) search
      (fun _ _ h=>searched_continue (initial_memory message pk b) hh h)
    exact (TBSim.steps st continuation).mono (by decide) (fun _ _ h=>h)

theorem paired_expand_pending : Final.Paired.ExpandRefines I0 ∧ Final.Paired.ExpandTerminates I0 :=
  paired_expand_pending_of paired_expand_tbsim
#print axioms paired_expand_tbsim
#print axioms paired_expand_pending
end ClaudeWCT.W9.Machine.ExpandLink
