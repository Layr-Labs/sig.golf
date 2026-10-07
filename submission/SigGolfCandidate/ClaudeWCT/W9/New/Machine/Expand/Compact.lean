import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactCoord
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ComposeBack

section

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
open ClaudeWCT.W9.T3M (authSibOff)
set_option linter.unusedSimpArgs false
def allMem (M : Nat → Word) (cs : Nat → Nat) (K : Nat) (A : Nat) : Word :=
  if 0x840 ≤ A ∧ A < 0x840 + 896 * K then
    coordMem M (cs ((A - 0x840) / 896)) (SNAP + 1024 * ((A - 0x840) / 896)) (0x840 + 896 * ((A - 0x840) / 896)) A
  else M A
def finalWord (M : Nat → Word) (cs : Nat → Nat) (i : Nat) : Word :=
  if i < 8 then M (0x800 + 8 * i)
  else if i < 1016 then
    if (i - 8) % 112 < 40 then
      match sibSrc (cs ((i - 8) / 112)) ((i - 8) % 112) with
      | some o => M (0x840 + 1024 * ((i - 8) / 112) + o)
      | none => 0
    else M (0x840 + 1024 * ((i - 8) / 112) + 448 + 8 * ((i - 8) % 112 - 40))
  else M (0x800 + 8 * (i + 144))
theorem sibSrc_lt {c j o : Nat} (h : sibSrc c j = some o) : o + 8 ≤ 448 ∧ o % 8 = 0 := by
  unfold sibSrc at h
  cases hl : sibLev c j with
  | none => rw [hl] at h; simp at h
  | some l =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have := srcOff_bound c l
    split at h <;> omega
theorem coordMem_congr (M M' : Nat → Word) (c S D A : Nat) (hS : ∀ o < 1024, M (S + o) = M' (S + o))
    (hA : M A = M' A) : coordMem M c S D A = coordMem M' c S D A := by
  unfold coordMem
  split
  · split
    · cases h : sibSrc c ((A - D) / 8) with
      | none => rfl
      | some o => exact hS o (by have := sibSrc_lt h; omega)
    · rw [Nat.add_assoc]; exact hS _ (by omega)
  · exact hA
theorem coordMem_out (M : Nat → Word) (c S D A : Nat) (h : A < D ∨ D + 896 ≤ A) : coordMem M c S D A = M A := by
  unfold coordMem; rw [if_neg (by omega)]
theorem allMem_succ (M : Nat → Word) (cs : Nat → Nat) (K : Nat) (hK : K < 9) (A : Nat) :
    coordMem (allMem M cs K) (cs K) (SNAP + 1024 * K) (0x840 + 896 * K) A = allMem M cs (K + 1) A := by
  have hSN : SNAP = 0x200000 := rfl
  by_cases hA : 0x840 + 896 * K ≤ A ∧ A < 0x840 + 896 * K + 896
  · have hk : (A - 0x840) / 896 = K := by omega
    have e : allMem M cs (K + 1) A = coordMem M (cs K) (SNAP + 1024 * K) (0x840 + 896 * K) A := by
      unfold allMem; rw [if_pos (by omega), hk]
    rw [e]
    apply coordMem_congr
    · intro o ho; unfold allMem; rw [if_neg (by omega)]
    · unfold allMem; rw [if_neg (by omega)]
  · rw [coordMem_out _ _ _ _ _ (by omega)]
    unfold allMem
    by_cases h2 : 0x840 ≤ A ∧ A < 0x840 + 896 * K
    · rw [if_pos h2, if_pos (show 0x840 ≤ A ∧ A < 0x840 + 896 * (K + 1) by omega)]
    · rw [if_neg h2, if_neg (show ¬ (0x840 ≤ A ∧ A < 0x840 + 896 * (K + 1)) by omega)]
theorem allMem_mid (M : Nat → Word) (cs : Nat → Nat) (k j : Nat) (hk : k < 9) (hj : j < 112) :
    allMem M cs 9 (0x840 + 896 * k + 8 * j) =
      if j < 40 then (match sibSrc (cs k) j with | some o => M (SNAP + 1024 * k + o) | none => 0)
      else M (SNAP + 1024 * k + 448 + 8 * (j - 40)) := by
  unfold allMem
  rw [if_pos (by omega), show (0x840 + 896 * k + 8 * j - 0x840) / 896 = k by omega]
  unfold coordMem
  rw [if_pos (by omega), show 0x840 + 896 * k + 8 * j - (0x840 + 896 * k) = 8 * j by omega,
    show 8 * j / 8 = j by omega]
  by_cases h : j < 40
  · rw [if_pos (show 8 * j < 320 by omega), if_pos h]
    rfl
  · rw [if_neg (show ¬ 8 * j < 320 by omega), if_neg h, show 8 * j - 320 = 8 * (j - 40) by omega]
section
variable {im : Image} (hc : NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem coords_spec (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf (coordAt 0)) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) (h8 : s.getReg .x8 = BitVec.ofNat 64 SNAP) (h9 : s.getReg .x9 = BitVec.ofNat 64 0x840)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN) :
    ∀ K ≤ 9, ∃ t, Steps im s (705 * K) (705 * K) t ∧ t.pc = pcOf (coordAt K) ∧
      t.getReg .x8 = BitVec.ofNat 64 (SNAP + 1024 * K) ∧ t.getReg .x9 = BitVec.ofNat 64 (0x840 + 896 * K) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        allMem (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K A := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  have hSN : SNAP = 0x200000 := rfl
  intro K hK
  induction K with
  | zero =>
    refine ⟨s, Steps.refl s, hpc, by simpa using h8, by simpa using h9, RegsExcept.refl s _, fun A hA => ?_⟩
    unfold allMem; rw [if_neg (by omega)]
  | succ K ih =>
    obtain ⟨t, st, pt, t8, t9, rt, mt⟩ := ih (by omega)
    have hNt : OutAt t 0x60 N := fun j hj => by
      rw [mt _ (by omega)]; unfold allMem; rw [if_neg (by omega)]; exact hN j hj
    have hpt : PlanAt t := fun j hj => by
      rw [mt _ (by omega)]; unfold allMem; rw [if_neg (by omega)]; exact hp j hj
    obtain ⟨t', st', pt', t8', t9', rt', mt'⟩ := coord_spec hc K (by omega) t pt N hNt hpt (SNAP + 1024 * K)
      (0x840 + 896 * K) t8 t9 (by rw [rt.get (by decide), h18]) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), ?_, ?_, ?_, (rt.trans rt').mono (by decide),
      fun A hA => ?_⟩
    · rw [pt', show coordAt K + 111 = coordAt (K + 1) by unfold coordAt; ring]
    · rw [t8', show SNAP + 1024 * K + 1024 = SNAP + 1024 * (K + 1) by ring]
    · rw [t9', show 0x840 + 896 * K + 896 = 0x840 + 896 * (K + 1) by ring]
    · have e := coordMem_congr (fun B => t.getMem (BitVec.ofNat 64 B))
        (allMem (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K)
        (N.toNat / 2 ^ WCT9.childBase K % 128) (SNAP + 1024 * K) (0x840 + 896 * K) A
        (fun o ho => mt _ (by omega)) (mt A hA)
      rw [mt' A hA, e]
      exact allMem_succ _ _ K (by omega) A
set_option maxRecDepth 20000 in
theorem run_spec (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf 41108) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) :
    ∃ t, Steps im s 23559 23559 t ∧ t.pc = pcOf 42129 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧
      ∀ i < 2729, t.getMem (BitVec.ofNat 64 (0x800 + 8 * i)) =
        finalWord (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) i := by
  have hMB : MEMORY_BYTES = 16777216 := rfl
  have hPL : PLAN = 0xff9a00 := rfl
  have hSN : SNAP = 0x200000 := rfl
  obtain ⟨u1, s1, p1, a10, a11, a12, a1, g1, f1⟩ := start_spec hc s hpc
  obtain ⟨u2, s2, p2, g2, m2⟩ := copy_spec hc u1 p1 0x840 SNAP 1152 41115 a10 a11 a12 a1 (by norm_num)
    (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (Or.inr (by omega))
  obtain ⟨u3, s3, p3, b8, b9, b18, g3, f3⟩ := regs_spec hc u2 p2
  have hM3 : ∀ A < 2 ^ 64, u3.getMem (BitVec.ofNat 64 A) = copied u1 0x840 SNAP 1152 A := fun A hA => by
    rw [f3 A hA (fun h => h), m2 A hA]
  have hlo : ∀ A < SNAP, u3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [hM3 A (by omega)]; unfold copied; rw [if_neg (by omega), f1 A (by omega) (fun h => h)]
  have hsn : ∀ o, o < 9216 → o % 8 = 0 →
      u3.getMem (BitVec.ofNat 64 (SNAP + o)) = s.getMem (BitVec.ofNat 64 (0x840 + o)) := fun o ho ho' => by
    rw [hM3 _ (by omega)]; unfold copied
    rw [if_pos (by omega), f1 _ (by omega) (fun h => h), show SNAP + o - SNAP = o by omega]
  have hN3 : OutAt u3 0x60 N := fun j hj => by rw [hlo _ (by omega)]; exact hN j hj
  have hp3 : PlanAt u3 := fun j hj => by
    rw [hM3 _ (by omega)]; unfold copied
    rw [if_neg (by omega), f1 _ (by omega) (fun h => h)]; exact hp j hj
  obtain ⟨u4, s4, p4, c8, c9, g4, m4⟩ := coords_spec hc N u3 p3 hN3 hp3 b8 b9 b18 9 le_rfl
  obtain ⟨u5, s5, p5, d10, d11, d12, d1, g5, f5⟩ := final_spec hc u4 (by rw [p4]; rfl)
  obtain ⟨u6, s6, p6, g6, m6⟩ := copy_spec hc u5 p5 (0x800 + 9280) (0x800 + 8128) 1713 42127 d10 d11 d12 d1
    (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num) (by omega) (Or.inl (by norm_num))
  obtain ⟨u7, s7, p7, e5, e10, _, g7, f7⟩ := halt_spec hc u6 p6
  refine ⟨u7, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).of_eq (by norm_num)
    (by norm_num), p7, e5, e10, fun i hi => ?_⟩
  have h4 : ∀ A < 2 ^ 64, u5.getMem (BitVec.ofNat 64 A) =
      allMem (fun B => u3.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) 9 A :=
    fun A hA => by rw [f5 A hA (fun h => h), m4 A hA]
  rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
  unfold copied finalWord
  by_cases ht : 1016 ≤ i
  · rw [if_pos (show 0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0 by omega), if_neg (show ¬ i < 8 by omega),
      if_neg (show ¬ i < 1016 by omega), h4 _ (by omega)]
    unfold allMem
    rw [if_neg (by omega)]
    beta_reduce
    rw [hlo _ (by omega),
      show 0x800 + 9280 + (0x800 + 8 * i - (0x800 + 8128)) = 0x800 + 8 * (i + 144) by omega]
  · rw [if_neg (show ¬ (0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0) by omega), h4 _ (by omega)]
    by_cases h8 : i < 8
    · rw [if_pos h8]
      unfold allMem
      rw [if_neg (by omega)]
      beta_reduce
      rw [hlo _ (by omega)]
    · rw [if_neg h8, if_pos (show i < 1016 by omega)]
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 112 ∧ i = 8 + 112 * k + j :=
        ⟨(i - 8) / 112, (i - 8) % 112, Nat.mod_lt _ (by norm_num), by omega⟩
      have hk : k < 9 := by omega
      rw [show (8 + 112 * k + j - 8) / 112 = k by omega, show (8 + 112 * k + j - 8) % 112 = j by omega,
        show 0x800 + 8 * (8 + 112 * k + j) = 0x840 + 896 * k + 8 * j by ring, allMem_mid _ _ k j hk hj]
      by_cases hj40 : j < 40
      · rw [if_pos hj40, if_pos hj40]
        cases h : sibSrc (N.toNat / 2 ^ WCT9.childBase k % 128) j with
        | none => rfl
        | some o =>
          have := sibSrc_lt h
          simp only
          rw [show SNAP + 1024 * k + o = SNAP + (1024 * k + o) by ring, hsn _ (by omega) (by omega),
            Nat.add_assoc]
      · rw [if_neg hj40, if_neg hj40,
          show SNAP + 1024 * k + 448 + 8 * (j - 40) = SNAP + (1024 * k + 448 + 8 * (j - 40)) by ring,
          hsn _ (by omega) (by omega)]
        congr 2
        ring
end
end ClaudeWCT.W9.Machine.Expand.Compact
end

section



namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (HashOutput readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap_const window_full zeros wordsOf)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (witList headerBytes wctBytes regionBytes merkleBytes authSibOff authByte headerBytes_length
  wctBytes_length regionBytes_length merkleBytes_length region_merkle merkleBytes_sib authByte_none window_map_range
  witList_length_eq)
open ClaudeWCT.W9.Machine.Expand (witListV5 wctBytesV5 regionBytesV5 merkleBytesV5 merkleBytesV5_length
  regionBytesV5_length wctBytesV5_length witListV5_length region_merkleV5 merkleBytesV5_window wordsOf_getD)
set_option linter.unusedSimpArgs false
theorem window_window (L : List UInt8) (o m a n : Nat) (h : a + n ≤ m) :
    window (window L o m) a n = window L (o + a) n := by
  unfold window
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
section
variable (N : HashOutput) (w : WCT9.Witness)
theorem witList_head (o : Nat) (h : o + 8 ≤ 64) : window (witList N w) o 8 = window (witListV5 N w) o 8 := by
  unfold witList witListV5
  simp only [List.append_assoc]
  rw [window_append_left _ _ _ _ (by rw [headerBytes_length]; omega),
    window_append_left _ _ _ _ (by rw [headerBytes_length]; omega)]
theorem witList_tail (o : Nat) (h : 8128 ≤ o) :
    window (witList N w) o 8 = window (witListV5 N w) (o + 1152) 8 := by
  unfold witList witListV5
  simp only [List.append_assoc]
  rw [window_append_right (headerBytes w) _ _ _ (by rw [headerBytes_length]; omega),
    window_append_right (headerBytes w) _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    window_append_right (wctBytes N w.signature) _ _ _ (by rw [wctBytes_length]; omega),
    window_append_right (wctBytesV5 N w.signature) _ _ _ (by rw [wctBytesV5_length]; omega), wctBytes_length,
    wctBytesV5_length,
    show o + 1152 - 64 - 9216 = o - 64 - 8064 by omega]
theorem witList_region (k : Nat) (hk : k < 9) (j : Nat) (hj : j + 8 ≤ 896) :
    window (witList N w) (64 + 896 * k + j) 8 =
      window (regionBytes (WCT9.child N ⟨k, hk⟩).val (w.signature.openings ⟨k, hk⟩)) j 8 := by
  unfold witList
  simp only [List.append_assoc]
  rw [window_append_right _ _ _ _ (by rw [headerBytes_length]; omega), headerBytes_length,
    window_append_left _ _ _ _ (by rw [wctBytes_length]; omega),
    show 64 + 896 * k + j - 64 = 896 * k + j by omega]
  unfold wctBytes
  rw [window_flatMap_const _ _ 896 (fun k => regionBytes_length _ _) k (by simp; omega) j 8 hj]
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
    window (regionBytes c op) o 8 = window (regionBytesV5 c op) (o + 128) 8 := by
  unfold regionBytes regionBytesV5
  simp only [List.append_assoc]
  rw [window_append_right (merkleBytes c op) _ _ _ (by rw [merkleBytes_length]; omega),
    window_append_right (merkleBytesV5 c op) _ _ _ (by rw [merkleBytesV5_length]; omega), merkleBytes_length,
    merkleBytesV5_length,
    show o + 128 - 448 = o - 320 by omega]
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
    (wordsOf (witList N w)).getD i 0 =
      finalWord (fun B => (wordsOf (witListV5 N w)).getD ((B - 0x800) / 8) 0)
        (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) i := by
  have hW := witList_length_eq N w
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
  · rw [if_pos hj40, region_merkle _ _ _ _ (by omega)]
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
def compactC : Nat := 23560
def CompactGood (im : Image) : Prop :=
  NewCodeAt im → CodeAt im (pcOf 351) [compactJal] → ∀ N w s, CompactPre N w s →
    ∃ t, Steps im s compactC compactC t ∧ t.pc = pcOf 42129 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧
      t.readWords (BitVec.ofNat 64 0x800) 2729 = wordsOf (ClaudeWCT.W9.T3M.witList N w)
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
  obtain ⟨u, su, pu, ru, fu⟩ := Compact.jal_spec hJ s hpre.pc
  have hNu : OutAt u 0x60 N := fun j hj => by rw [fu _ (by omega) (fun h => h)]; exact hpre.dig j hj
  have hpu : PlanAt u := fun j hj => by rw [fu _ (by omega) (fun h => h)]; exact hpre.plan j hj
  obtain ⟨t, st, pt, t5, t10, mt⟩ := Compact.run_spec hc N u pu hNu hpu
  refine ⟨t, (su.trans st).of_eq (by unfold compactC; norm_num) (by unfold compactC; norm_num), pt, t5, t10, ?_⟩
  have hW5 : ∀ i' < 2873, s.getMem (BitVec.ofNat 64 (0x800 + 8 * i')) = (wordsOf (witListV5 N w)).getD i' 0 := by
    intro i' hi'
    rw [← hpre.wit, VLib.readWords_ofNat s 0x800 2873 (by norm_num)]
    simp [List.getD_eq_getElem?_getD, hi']
  have hl : (wordsOf (ClaudeWCT.W9.T3M.witList N w)).length = 2729 :=
    length_wordsOf 2729 _ (by rw [ClaudeWCT.W9.T3M.witList_length_eq])
  rw [← hl]
  refine readWords_ext t _ 0x800 (fun i hi => ?_)
  rw [hl] at hi
  rw [mt i hi, Compact.compact_words N w i hi]
  apply Compact.finalWord_congr _ _ _ (fun i' hi' => ?_) i hi
  rw [fu _ (by omega) (fun h => h), hW5 i' hi', show (0x800 + 8 * i' - 0x800) / 8 = i' by omega]
end ClaudeWCT.W9.Machine.Expand
end
