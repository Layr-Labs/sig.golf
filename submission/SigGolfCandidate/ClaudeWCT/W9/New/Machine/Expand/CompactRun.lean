import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactCoord

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
open ClaudeWCT.W9.T3M (authSibOff)
set_option linter.unusedSimpArgs false
/-- Hold word `j` (0, 1: top sibling; 2: flag `1 - bit6`) of coordinate `k`, read from the snapshot. -/
def holdW (M : Nat → Word) (cs : Nat → Nat) (k j : Nat) : Word :=
  if j = 0 then M (SNAP + 1024 * k + srcOff (cs k) 6)
  else if j = 1 then M (SNAP + 1024 * k + srcOff (cs k) 6 + 8)
  else BitVec.ofNat 64 (1 - cs k / 2 ^ 6 % 2)
/-- The written hold words of the first `K` coordinates. -/
abbrev InHold (K A : Nat) : Prop :=
  0x380000 ≤ A ∧ A < 0x380000 + 32 * K ∧ (A - 0x380000) % 8 = 0 ∧ (A - 0x380000) % 32 < 24
def allMem (M : Nat → Word) (cs : Nat → Nat) (K : Nat) (A : Nat) : Word :=
  if 0x840 ≤ A ∧ A < 0x840 + 896 * K then
    coordMem M (cs ((A - 0x840) / 896)) (SNAP + 1024 * ((A - 0x840) / 896)) (0x840 + 896 * ((A - 0x840) / 896)) A
  else if InHold K A then holdW M cs ((A - 0x380000) / 32) ((A - 0x380000) % 32 / 8)
  else M A
def finalWord (M : Nat → Word) (cs : Nat → Nat) (i : Nat) : Word :=
  if i < 8 then M (0x800 + 8 * i)
  else if i < 1016 then
    match sibSrc (cs ((i - 8) / 112)) ((i - 8) % 112) with
    | some o => M (0x840 + 1024 * ((i - 8) / 112) + o)
    | none => if (i - 8) % 112 < 40 then 0 else M (0x840 + 1024 * ((i - 8) / 112) + 448 + 8 * ((i - 8) % 112 - 40))
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
  · cases h : sibSrc c ((A - D) / 8) with
    | some o => exact hS o (by have := sibSrc_lt h; omega)
    | none =>
      simp only
      split
      · rfl
      · rw [Nat.add_assoc]; exact hS _ (by omega)
  · exact hA
theorem coordMem_out (M : Nat → Word) (c S D A : Nat) (h : A < D ∨ D + 896 ≤ A) : coordMem M c S D A = M A := by
  unfold coordMem; rw [if_neg (by omega)]
theorem holdMem_congr (M M' : Nat → Word) (c S k A : Nat) (r r' : Word)
    (h1 : M (S + srcOff c 6) = M' (S + srcOff c 6)) (h2 : M (S + srcOff c 6 + 8) = M' (S + srcOff c 6 + 8))
    (hr : r = r') : holdMem M c S k A r = holdMem M' c S k A r' := by
  unfold holdMem; rw [h1, h2, hr]
theorem allMem_succ (M : Nat → Word) (cs : Nat → Nat) (K : Nat) (hK : K < 9) (A : Nat) :
    holdMem (allMem M cs K) (cs K) (SNAP + 1024 * K) K A
      (coordMem (allMem M cs K) (cs K) (SNAP + 1024 * K) (0x840 + 896 * K) A) = allMem M cs (K + 1) A := by
  have hSN : SNAP = 0x200000 := rfl
  have hso := srcOff_bound (cs K) 6
  have hS : ∀ X, SNAP + 1024 * K ≤ X → X < SNAP + 1024 * K + 1024 → allMem M cs K X = M X := by
    intro X h1 h2; unfold allMem InHold; rw [if_neg (by omega), if_neg (by omega)]
  have hH : holdAt K = 0x380000 + 32 * K := rfl
  unfold holdMem
  by_cases h16 : A = holdAt K + 16
  · rw [if_pos h16]
    unfold allMem InHold
    rw [if_neg (by omega), if_pos (by omega), show (A - 0x380000) / 32 = K by omega,
      show (A - 0x380000) % 32 / 8 = 2 by omega]
    rfl
  rw [if_neg h16]
  by_cases h8 : A = holdAt K + 8
  · rw [if_pos h8, hS _ (by omega) (by omega)]
    unfold allMem InHold
    rw [if_neg (by omega), if_pos (by omega), show (A - 0x380000) / 32 = K by omega,
      show (A - 0x380000) % 32 / 8 = 1 by omega]
    rfl
  rw [if_neg h8]
  by_cases h0 : A = holdAt K
  · rw [if_pos h0, hS _ (by omega) (by omega)]
    unfold allMem InHold
    rw [if_neg (by omega), if_pos (by omega), show (A - 0x380000) / 32 = K by omega,
      show (A - 0x380000) % 32 / 8 = 0 by omega]
    rfl
  rw [if_neg h0]
  by_cases hA : 0x840 + 896 * K ≤ A ∧ A < 0x840 + 896 * K + 896
  · have hk : (A - 0x840) / 896 = K := by omega
    have e : allMem M cs (K + 1) A = coordMem M (cs K) (SNAP + 1024 * K) (0x840 + 896 * K) A := by
      unfold allMem; rw [if_pos (by omega), hk]
    rw [e]
    apply coordMem_congr
    · intro o ho; unfold allMem InHold; rw [if_neg (by omega), if_neg (by omega)]
    · unfold allMem InHold; rw [if_neg (by omega), if_neg (by omega)]
  · rw [coordMem_out _ _ _ _ _ (by omega)]
    unfold allMem
    by_cases h2 : 0x840 ≤ A ∧ A < 0x840 + 896 * K
    · rw [if_pos h2, if_pos (show 0x840 ≤ A ∧ A < 0x840 + 896 * (K + 1) by omega)]
    · rw [if_neg h2, if_neg (show ¬ (0x840 ≤ A ∧ A < 0x840 + 896 * (K + 1)) by omega)]
      by_cases h3 : InHold K A
      · rw [if_pos h3, if_pos (by unfold InHold at h3 ⊢; omega)]
      · rw [if_neg h3, if_neg (by unfold InHold at h3 ⊢; omega)]
theorem allMem_mid (M : Nat → Word) (cs : Nat → Nat) (k j : Nat) (hk : k < 9) (hj : j < 112) :
    allMem M cs 9 (0x840 + 896 * k + 8 * j) =
      match sibSrc (cs k) j with
      | some o => M (SNAP + 1024 * k + o)
      | none => if j < 40 then 0 else M (SNAP + 1024 * k + 448 + 8 * (j - 40)) := by
  unfold allMem
  rw [if_pos (by omega), show (0x840 + 896 * k + 8 * j - 0x840) / 896 = k by omega]
  unfold coordMem
  rw [if_pos (by omega), show 0x840 + 896 * k + 8 * j - (0x840 + 896 * k) = 8 * j by omega,
    show 8 * j / 8 = j by omega]
  cases sibSrc (cs k) j with
  | some o => rfl
  | none =>
    simp only
    by_cases h : j < 40
    · rw [if_pos (show 8 * j < 320 by omega), if_pos h]
    · rw [if_neg (show ¬ 8 * j < 320 by omega), if_neg h, show 8 * j - 320 = 8 * (j - 40) by omega]
/-- Hold word `j` of coordinate `k` in terms of the first-pass scratch regions at `0x840`. -/
def holdVal (M : Nat → Word) (cs : Nat → Nat) (k j : Nat) : Word :=
  if j = 0 then M (0x840 + 1024 * k + srcOff (cs k) 6)
  else if j = 1 then M (0x840 + 1024 * k + srcOff (cs k) 6 + 8)
  else BitVec.ofNat 64 (1 - cs k / 2 ^ 6 % 2)
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem coords_spec (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf (coordAt 0)) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) (h8 : s.getReg .x8 = BitVec.ofNat 64 SNAP) (h9 : s.getReg .x9 = BitVec.ofNat 64 0x840)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 PLAN) :
    ∀ K ≤ 9, ∃ t, Steps im s (707 * K) (707 * K) t ∧ t.pc = pcOf (coordAt K) ∧
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
    unfold allMem InHold; rw [if_neg (by omega), if_neg (by omega)]
  | succ K ih =>
    obtain ⟨t, st, pt, t8, t9, rt, mt⟩ := ih (by omega)
    have hNt : OutAt t 0x60 N := fun j hj => by
      rw [mt _ (by omega)]; unfold allMem InHold; rw [if_neg (by omega), if_neg (by omega)]; exact hN j hj
    have hpt : PlanAt t := fun j hj => by
      rw [mt _ (by omega)]; unfold allMem InHold; rw [if_neg (by omega), if_neg (by omega)]; exact hp j hj
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
      have hso := srcOff_bound (N.toNat / 2 ^ WCT9.childBase K % 128) 6
      rw [mt' A hA, holdMem_congr _ (allMem (fun B => s.getMem (BitVec.ofNat 64 B))
        (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) K) _ _ _ _ _ _ (mt _ (by omega)) (mt _ (by omega)) e]
      exact allMem_succ _ _ K (by omega) A
set_option maxRecDepth 20000 in
theorem run_spec (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf 41108) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) :
    ∃ t, Steps im s 23576 23576 t ∧ t.pc = pcOf 42142 ∧ RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12,
        .x13, .x18, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      (∀ i < 2729, t.getMem (BitVec.ofNat 64 (0x800 + 8 * i)) =
        finalWord (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) i) ∧
      (∀ k < 9, ∀ j < 3, t.getMem (BitVec.ofNat 64 (holdAt k + 8 * j)) =
        holdVal (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) k j) ∧
      ∀ A < 2 ^ 64, (A < 0x800 ∨ 0x200000 + 9216 ≤ A) → ¬ InHold 9 A →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
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
  obtain ⟨u7, s7, p7, g7, f7⟩ := halt_spec hc u6 p6
  have h4 : ∀ A < 2 ^ 64, u5.getMem (BitVec.ofNat 64 A) =
      allMem (fun B => u3.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) 9 A :=
    fun A hA => by rw [f5 A hA (fun h => h), m4 A hA]
  refine ⟨u7, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).of_eq (by norm_num)
    (by norm_num), p7, (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).mono (by decide)),
    fun i hi => ?_, fun k hk j hj => ?_, fun A hA hA' hH => ?_⟩
  rotate_left
  · have hH : holdAt k = 0x380000 + 32 * k := rfl
    have hso := srcOff_bound (N.toNat / 2 ^ WCT9.childBase k % 128) 6
    rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
    unfold copied
    rw [if_neg (by omega), h4 _ (by omega)]
    unfold allMem
    rw [if_neg (by omega), if_pos (by unfold InHold; omega),
      show (holdAt k + 8 * j - 0x380000) / 32 = k by omega, show (holdAt k + 8 * j - 0x380000) % 32 / 8 = j by omega]
    unfold holdW holdVal
    beta_reduce
    split_ifs
    · rw [show SNAP + 1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 =
          SNAP + (1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6) by omega,
        hsn _ (by omega) (by omega)]
      congr 2; omega
    · rw [show SNAP + 1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 + 8 =
          SNAP + (1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 + 8) by omega,
        hsn _ (by omega) (by omega)]
      congr 2; omega
    · rfl
  · rw [f7 A hA (fun h => h), m6 A hA]
    unfold copied
    rw [if_neg (by omega), h4 A hA]
    unfold allMem
    rw [if_neg (by omega), if_neg hH]
    beta_reduce
    rw [hM3 A hA]
    unfold copied
    rw [if_neg (by omega), f1 A hA (fun h => h)]
  rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
  unfold copied finalWord
  by_cases ht : 1016 ≤ i
  · rw [if_pos (show 0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0 by omega), if_neg (show ¬ i < 8 by omega),
      if_neg (show ¬ i < 1016 by omega), h4 _ (by omega)]
    unfold allMem
    rw [if_neg (by omega), if_neg (by omega)]
    beta_reduce
    rw [hlo _ (by omega),
      show 0x800 + 9280 + (0x800 + 8 * i - (0x800 + 8128)) = 0x800 + 8 * (i + 144) by omega]
  · rw [if_neg (show ¬ (0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0) by omega), h4 _ (by omega)]
    by_cases h8 : i < 8
    · rw [if_pos h8]
      unfold allMem
      rw [if_neg (by omega), if_neg (by omega)]
      beta_reduce
      rw [hlo _ (by omega)]
    · rw [if_neg h8, if_pos (show i < 1016 by omega)]
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 112 ∧ i = 8 + 112 * k + j :=
        ⟨(i - 8) / 112, (i - 8) % 112, Nat.mod_lt _ (by norm_num), by omega⟩
      have hk : k < 9 := by omega
      rw [show (8 + 112 * k + j - 8) / 112 = k by omega, show (8 + 112 * k + j - 8) % 112 = j by omega,
        show 0x800 + 8 * (8 + 112 * k + j) = 0x840 + 896 * k + 8 * j by ring, allMem_mid _ _ k j hk hj]
      cases h : sibSrc (N.toNat / 2 ^ WCT9.childBase k % 128) j with
      | some o =>
        have := sibSrc_lt h
        simp only
        rw [show SNAP + 1024 * k + o = SNAP + (1024 * k + o) by ring, hsn _ (by omega) (by omega),
          Nat.add_assoc]
      | none =>
        simp only
        by_cases hj40 : j < 40
        · rw [if_pos hj40, if_pos hj40]
        · rw [if_neg hj40, if_neg hj40,
            show SNAP + 1024 * k + 448 + 8 * (j - 40) = SNAP + (1024 * k + 448 + 8 * (j - 40)) by ring,
            hsn _ (by omega) (by omega)]
          congr 2
          ring
end
end ClaudeWCT.W9.Machine.Expand.Compact


namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M.Search (OutAt)
open ClaudeWCT.W9.Machine.Expand (PLAN PlanAt)
open ClaudeWCT.W9.T3M (authSibOff)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
section
variable {im : Image} (hc : CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
theorem run_spec_framed (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf 41108) (hN : OutAt s 0x60 N)
    (hp : PlanAt s) :
    ∃ t, Steps im s 23576 23576 t ∧ t.pc = pcOf 42142 ∧ RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x10, .x11, .x12,
        .x13, .x18, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      (∀ i < 2729, t.getMem (BitVec.ofNat 64 (0x800 + 8 * i)) =
        finalWord (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) i) ∧
      (∀ k < 9, ∀ j < 3, t.getMem (BitVec.ofNat 64 (holdAt k + 8 * j)) =
        holdVal (fun B => s.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) k j) ∧
      ∀ A < 2 ^ 64, (A < 0x800 ∨ 0x800 + 8 * 2729 ≤ A) →
        (A < SNAP ∨ SNAP + 9216 ≤ A) → ¬ InHold 9 A →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
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
  obtain ⟨u7, s7, p7, g7, f7⟩ := halt_spec hc u6 p6
  have h4 : ∀ A < 2 ^ 64, u5.getMem (BitVec.ofNat 64 A) =
      allMem (fun B => u3.getMem (BitVec.ofNat 64 B)) (fun k => N.toNat / 2 ^ WCT9.childBase k % 128) 9 A :=
    fun A hA => by rw [f5 A hA (fun h => h), m4 A hA]
  refine ⟨u7, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).of_eq (by norm_num)
    (by norm_num), p7, (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).mono (by decide)),
    fun i hi => ?_, fun k hk j hj => ?_, fun A hA hA' hSnap hH => ?_⟩
  rotate_left
  · have hH : holdAt k = 0x380000 + 32 * k := rfl
    have hso := srcOff_bound (N.toNat / 2 ^ WCT9.childBase k % 128) 6
    rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
    unfold copied
    rw [if_neg (by omega), h4 _ (by omega)]
    unfold allMem
    rw [if_neg (by omega), if_pos (by unfold InHold; omega),
      show (holdAt k + 8 * j - 0x380000) / 32 = k by omega, show (holdAt k + 8 * j - 0x380000) % 32 / 8 = j by omega]
    unfold holdW holdVal
    beta_reduce
    split_ifs
    · rw [show SNAP + 1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 =
          SNAP + (1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6) by omega,
        hsn _ (by omega) (by omega)]
      congr 2; omega
    · rw [show SNAP + 1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 + 8 =
          SNAP + (1024 * k + srcOff (N.toNat / 2 ^ WCT9.childBase k % 128) 6 + 8) by omega,
        hsn _ (by omega) (by omega)]
      congr 2; omega
    · rfl
  · rw [f7 A hA (fun h => h), m6 A hA]
    unfold copied
    rw [if_neg (by omega), h4 A hA]
    unfold allMem
    rw [if_neg (by omega), if_neg hH]
    beta_reduce
    rw [hM3 A hA]
    unfold copied
    rw [if_neg (by omega), f1 A hA (fun h => h)]
  rw [f7 _ (by omega) (fun h => h), m6 _ (by omega)]
  unfold copied finalWord
  by_cases ht : 1016 ≤ i
  · rw [if_pos (show 0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0 by omega), if_neg (show ¬ i < 8 by omega),
      if_neg (show ¬ i < 1016 by omega), h4 _ (by omega)]
    unfold allMem
    rw [if_neg (by omega), if_neg (by omega)]
    beta_reduce
    rw [hlo _ (by omega),
      show 0x800 + 9280 + (0x800 + 8 * i - (0x800 + 8128)) = 0x800 + 8 * (i + 144) by omega]
  · rw [if_neg (show ¬ (0x800 + 8128 ≤ 0x800 + 8 * i ∧ 0x800 + 8 * i < 0x800 + 8128 + 8 * 1713 ∧
        (0x800 + 8 * i - (0x800 + 8128)) % 8 = 0) by omega), h4 _ (by omega)]
    by_cases h8 : i < 8
    · rw [if_pos h8]
      unfold allMem
      rw [if_neg (by omega), if_neg (by omega)]
      beta_reduce
      rw [hlo _ (by omega)]
    · rw [if_neg h8, if_pos (show i < 1016 by omega)]
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 112 ∧ i = 8 + 112 * k + j :=
        ⟨(i - 8) / 112, (i - 8) % 112, Nat.mod_lt _ (by norm_num), by omega⟩
      have hk : k < 9 := by omega
      rw [show (8 + 112 * k + j - 8) / 112 = k by omega, show (8 + 112 * k + j - 8) % 112 = j by omega,
        show 0x800 + 8 * (8 + 112 * k + j) = 0x840 + 896 * k + 8 * j by ring, allMem_mid _ _ k j hk hj]
      cases h : sibSrc (N.toNat / 2 ^ WCT9.childBase k % 128) j with
      | some o =>
        have := sibSrc_lt h
        simp only
        rw [show SNAP + 1024 * k + o = SNAP + (1024 * k + o) by ring, hsn _ (by omega) (by omega),
          Nat.add_assoc]
      | none =>
        simp only
        by_cases hj40 : j < 40
        · rw [if_pos hj40, if_pos hj40]
        · rw [if_neg hj40, if_neg hj40,
            show SNAP + 1024 * k + 448 + 8 * (j - 40) = SNAP + (1024 * k + 448 + 8 * (j - 40)) by ring,
            hsn _ (by omega) (by omega)]
          congr 2
          ring
end
end ClaudeWCT.W9.Machine.Expand.Compact
