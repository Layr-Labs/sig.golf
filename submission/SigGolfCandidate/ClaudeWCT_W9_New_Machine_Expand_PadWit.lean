import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PadWriter
import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Honest

/-! # The pad writer fills the top node nonces of the witness (`Paired.witEnc` → `Paired.witEncN`)

Witness base `0x1020 = 4128` (T3M/Submission Paired layout, 22,012 bytes); the pad writer's `t5 = 0x2e10 = 4128 + 7664`
(start of the top-layer block). Its jump-table offsets are exactly the nonce pads: `offR r i = 16 · topPlanA[r][i] + 32`
(`i < 5`), the fixed `368 = 16 · 21 + 32` (`topPlanA[r][5] = 21`), `offR (64 + r) i = 16 · topPlanB[r][i] + 32`, so
nonce `j` is stored at `4128 + noncePos output j` (`noncePos = merkleBlock 0 leaf j + 32`).

Section 1 is a copy (own namespace) of the `PairedNonce` read-back lemmas of r3m `Witness/HonestN.lean` (absent from
this tree's `Witness/Honest.lean`). -/

namespace ClaudeWCT.W9.Machine.Expand.PadWit
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem topPlanA_bounds : ∀ r, r < 64 → ∀ j, j < 6 →
    21 ≤ (topPlanA.getD r []).getD j 0 ∧ (topPlanA.getD r []).getD j 0 ≤ 38 := by decide
theorem topPlanB_bounds : ∀ r, r < 64 → ∀ k, k < 5 → (topPlanB.getD r []).getD k 0 ≤ 16 := by decide
theorem topPlanA_inj : ∀ r, r < 64 → ∀ j, j < 6 → ∀ j', j' < 6 →
    (topPlanA.getD r []).getD j 0 = (topPlanA.getD r []).getD j' 0 → j = j' := by decide
theorem topPlanB_inj : ∀ r, r < 64 → ∀ k, k < 5 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 = (topPlanB.getD r []).getD k' 0 → k = k' := by decide

theorem slot_bound (leaf j : Nat) (hj : j < 11) :
    (j < 6 → 21 ≤ topPlanSlot leaf j) ∧ topPlanSlot leaf j ≤ 38 ∧ (6 ≤ j → topPlanSlot leaf j ≤ 16) := by
  unfold topPlanSlot
  by_cases h6 : j < 6
  · rw [if_pos h6]
    have := topPlanA_bounds (leaf % 64) (Nat.mod_lt _ (by decide)) j h6
    exact ⟨fun _ => this.1, this.2, fun h => absurd h (by omega)⟩
  · rw [if_neg h6]
    have := topPlanB_bounds (leaf / 64 % 64) (Nat.mod_lt _ (by decide)) (j - 6) (by omega)
    exact ⟨fun h => absurd h h6, by omega, fun _ => this⟩

theorem slot_inj (leaf j j' : Nat) (hj : j < 11) (hj' : j' < 11) (h : topPlanSlot leaf j = topPlanSlot leaf j') :
    j = j' := by
  have b := slot_bound leaf j hj
  have b' := slot_bound leaf j' hj'
  by_cases h6 : j < 6 <;> by_cases h6' : j' < 6
  · unfold topPlanSlot at h; rw [if_pos h6, if_pos h6'] at h
    exact topPlanA_inj _ (Nat.mod_lt _ (by decide)) j h6 j' h6' h
  · have := b.1 h6; have := b'.2.2 (by omega); omega
  · have := b'.1 h6'; have := b.2.2 (by omega); omega
  · unfold topPlanSlot at h; rw [if_neg h6, if_neg h6'] at h
    have := topPlanB_inj _ (Nat.mod_lt _ (by decide)) (j - 6) (by omega) (j' - 6) (by omega) h
    omega

theorem noncePos_eq (output : HashOutput) (j : Nat) :
    noncePos output j = 7664 + 16 * topPlanSlot (route (WCT9.digestIndex output) 0).1 j + 32 := by
  unfold noncePos merkleBlock
  rw [if_pos (show (0 : Layer).val = 0 from rfl)]
  rfl

theorem noncePos_bounds (output : HashOutput) (j : Nat) (hj : j < 11) :
    7696 ≤ noncePos output j ∧ noncePos output j + 16 ≤ 8320 := by
  have := (slot_bound (route (WCT9.digestIndex output) 0).1 j hj).2.1
  rw [noncePos_eq]; omega

theorem noncePos_disjoint (output : HashOutput) (j j' : Nat) (hj : j < 11) (hj' : j' < 11) (hne : j ≠ j') :
    noncePos output j + 16 ≤ noncePos output j' ∨ noncePos output j' + 16 ≤ noncePos output j := by
  have := slot_inj (route (WCT9.digestIndex output) 0).1 j j' hj hj'
  rw [noncePos_eq, noncePos_eq]
  omega

theorem nonceByte_free (output : HashOutput) (nonces : List Nat) (i : Nat) (b : UInt8)
    (h : ∀ j, j < 11 → i < noncePos output j ∨ noncePos output j + 8 ≤ i) : nonceByte output nonces i b = b := by
  unfold nonceByte
  rw [List.find?_eq_none.mpr]
  intro j hj
  have := h j (List.mem_range.mp hj)
  simp only [decide_eq_true_eq, not_and, not_lt]
  omega

theorem nonceByte_in (output : HashOutput) (nonces : List Nat) (j : Nat) (hj : j < 11) (i : Nat) (b : UInt8)
    (hi : noncePos output j ≤ i ∧ i < noncePos output j + 8) :
    nonceByte output nonces i b = (nonceWord nonces j).getD (i - noncePos output j) 0 := by
  unfold nonceByte
  cases hf : (List.range 11).find? (fun j => decide (noncePos output j ≤ i ∧ i < noncePos output j + 8)) with
  | none =>
      have := List.find?_eq_none.mp hf j (List.mem_range.mpr hj)
      simp only [decide_eq_true_eq] at this
      exact absurd hi this
  | some j' =>
      have hp := List.find?_some hf
      have hm := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      simp only [decide_eq_true_eq] at hp
      have : j' = j := by
        by_contra hne
        have := noncePos_disjoint output j' j hm hj hne
        omega
      subst this
      rfl

theorem witListN_length (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    (witListN output w).length = 22016 := by
  rw [witListN, List.length_mapIdx, Paired.witList_length, witListBase_length]

theorem witListN_getElem? (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (n : Nat) :
    (witListN output w)[n]? = (Paired.witList output w)[n]?.map (nonceByte output w.topNonces n) := by
  rw [witListN, List.getElem?_mapIdx]

/-- Windows avoiding every nonce pad are those of the nonce-free encoding. -/
theorem witListN_window_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k : Nat) (h : ∀ i, off ≤ i → i < off + k → ∀ j, j < 11 → i < noncePos output j ∨ noncePos output j + 8 ≤ i) :
    ((witListN output w).drop off).take k = ((Paired.witList output w).drop off).take k := by
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop, witListN_getElem?]
  split_ifs with hn
  · cases (Paired.witList output w)[off + n]? with
    | none => rfl
    | some b => simp only [Option.map_some]; rw [nonceByte_free _ _ _ _ (h (off + n) (by omega) (by omega))]
  · rfl

theorem witEncN_extract_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k : Nat) (hk : off + k ≤ 22012)
    (h : ∀ i, off ≤ i → i < off + k → ∀ j, j < 11 → i < noncePos output j ∨ noncePos output j + 8 ≤ i) :
    (witEncN output w).extractLsb' (8 * off) (8 * k) = (Paired.witEnc output w).extractLsb' (8 * off) (8 * k) := by
  unfold witEncN Paired.witEnc
  rw [extract_readLE _ 22012 _ _ hk, extract_readLE _ 22012 _ _ hk, witListN_window_free output w off k h]

/-- Outside the nonce pads area `[7696, 8320)` the nonce-carrying encoding is the former one. -/
theorem witEncN_extract_outside (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k : Nat) (hk : off + k ≤ 22012) (h : off + k ≤ 7696 ∨ 8320 ≤ off) :
    (witEncN output w).extractLsb' (8 * off) (8 * k) = (Paired.witEnc output w).extractLsb' (8 * off) (8 * k) := by
  apply witEncN_extract_free output w off k hk
  intro i hi1 hi2 j hj
  have := noncePos_bounds output j hj
  omega

theorem witListN_nonce_window (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j : Nat) (hj : j < 11) :
    ((witListN output w).drop (noncePos output j)).take 8 = nonceWord w.topNonces j := by
  have hb := noncePos_bounds output j hj
  have hl : (nonceWord w.topNonces j).length = 8 := by simp [nonceWord, SphincsSecurity.bytesLE_length]
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_take, List.getElem?_drop, witListN_getElem?]
  split_ifs with hn
  · have hlt : noncePos output j + n < (Paired.witList output w).length := by
      rw [Paired.witList_length, witListBase_length]; omega
    rw [List.getElem?_eq_getElem hlt, Option.map_some,
      nonceByte_in output w.topNonces j hj _ _ ⟨by omega, by omega⟩, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [List.getElem?_eq_none (by omega)]

/-- The low word of the level-`j` pad is the nonce. -/
theorem witEncN_nonce_lo (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j : Nat) (hj : j < 11) :
    (witEncN output w).extractLsb' (8 * noncePos output j) (8 * 8) = BitVec.ofNat 64 (w.topNonces.getD j 0) := by
  have hb := noncePos_bounds output j hj
  unfold witEncN
  rw [extract_readLE _ 22012 _ _ (by omega), witListN_nonce_window output w j hj, nonceWord,
    SigGolfCandidate.T3M.readLE_bytesLE]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]


/-! ### Section 2: the pad writer's offsets are the nonce pads -/
open RiscvZkvm.Rv64 ClaudeWCT.W9.Machine.Expand.PadWriter

theorem offA_slot : ∀ r, r < 64 → ∀ i, i < 5 → offR r i = 16 * (topPlanA.getD r []).getD i 0 + 32 := by
  decide +kernel
theorem slotA5 : ∀ r, r < 64 → (topPlanA.getD r []).getD 5 0 = 21 := by decide +kernel
theorem offB_slot : ∀ r, r < 64 → ∀ i, i < 5 → offR (64 + r) i = 16 * (topPlanB.getD r []).getD i 0 + 32 := by
  decide +kernel

/-- Absolute address of nonce `j` in the witness buffer (base `0x1020`). -/
abbrev nonceSlot (output : HashOutput) (j : Nat) : Nat := 4128 + noncePos output j

theorem noncePos_mod8 (output : HashOutput) (j : Nat) : noncePos output j % 8 = 0 := by
  rw [noncePos_eq]; omega

/-- Iterated single-dword updates, first list element applied first. -/
def updF (M : Word → Word) (l : List (Nat × Word)) : Word → Word := l.foldl (fun M p => upd M p.1 p.2) M

theorem updF_out (l : List (Nat × Word)) : ∀ (M : Word → Word) (A : Word), (∀ p ∈ l, A ≠ BitVec.ofNat 64 p.1) →
    updF M l A = M A := by
  induction l with
  | nil => intro M A _; rfl
  | cons p l ih =>
    intro M A h
    show updF (upd M p.1 p.2) l A = M A
    rw [ih _ A (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    unfold upd
    rw [if_neg (h p List.mem_cons_self)]

theorem updF_in (l : List (Nat × Word)) : ∀ (M : Word → Word) (a : Nat) (v : Word), (∀ p ∈ l, p.1 < 2 ^ 64) →
    (l.map Prod.fst).Nodup → (a, v) ∈ l → updF M l (BitVec.ofNat 64 a) = v := by
  induction l with
  | nil => intro M a v _ _ h; cases h
  | cons p l ih =>
    intro M a v hb hn hm
    show updF (upd M p.1 p.2) l (BitVec.ofNat 64 a) = v
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hm with he | he
    · subst he
      rw [updF_out l _ _ (fun q hq e => ?_)]
      · unfold upd; rw [if_pos rfl]
      · apply hn.1
        have h1 := hb q (List.mem_cons_of_mem _ hq)
        have h2 := hb (a, v) List.mem_cons_self
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
        exact List.mem_map.mpr ⟨q, hq, this.symm⟩
    · exact ih _ a v (fun q hq => hb q (List.mem_cons_of_mem _ hq)) hn.2 he

/-- The nonce stores of the pad writer, in program order. -/
def padList (M : Word → Word) (output : HashOutput) : List (Nat × Word) :=
  (List.range 11).map fun j => (nonceSlot output j, M (nonceAddr j))

/-- With the saved leaf word at `0x66758` being the digest leaf (mod 4096), the pad writer stores nonce `j` at
`0x1020 + noncePos output j`. -/
theorem padMem_eq (M : Word → Word) (output : HashOutput)
    (hleaf : leafW M % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096) :
    padMem M = updF M (padList M output) := by
  have hA : leafW M % 64 = (route (WCT9.digestIndex output) 0).1 % 64 := by omega
  have hB : leafW M / 64 % 64 = (route (WCT9.digestIndex output) 0).1 / 64 % 64 := by omega
  have eA : ∀ i, i < 5 → offA (leafW M % 64) i + 11792 = nonceSlot output i := by
    intro i hi
    rw [nonceSlot, noncePos_eq, topPlanSlot, if_pos (by omega), offA, hA,
      offA_slot _ (Nat.mod_lt _ (by decide)) i hi]
    omega
  have e5 : 11792 + 368 = nonceSlot output 5 := by
    rw [nonceSlot, noncePos_eq, topPlanSlot, if_pos (by omega), slotA5 _ (Nat.mod_lt _ (by decide))]
  have eB : ∀ i, i < 5 → offB (leafW M / 64 % 64) i + 11792 = nonceSlot output (6 + i) := by
    intro i hi
    rw [nonceSlot, noncePos_eq, topPlanSlot, if_neg (by omega), show 6 + i - 6 = i by omega, offB, hB,
      offB_slot _ (Nat.mod_lt _ (by decide)) i hi]
    omega
  have a0 : offA (leafW M % 64) 0 + 11792 = nonceSlot output 0 := eA 0 (by decide)
  have a1 : offA (leafW M % 64) 1 + 11792 = nonceSlot output 1 := eA 1 (by decide)
  have a2 : offA (leafW M % 64) 2 + 11792 = nonceSlot output 2 := eA 2 (by decide)
  have a3 : offA (leafW M % 64) 3 + 11792 = nonceSlot output 3 := eA 3 (by decide)
  have a4 : offA (leafW M % 64) 4 + 11792 = nonceSlot output 4 := eA 4 (by decide)
  have b0 : offB (leafW M / 64 % 64) 0 + 11792 = nonceSlot output 6 := eB 0 (by decide)
  have b1 : offB (leafW M / 64 % 64) 1 + 11792 = nonceSlot output 7 := eB 1 (by decide)
  have b2 : offB (leafW M / 64 % 64) 2 + 11792 = nonceSlot output 8 := eB 2 (by decide)
  have b3 : offB (leafW M / 64 % 64) 3 + 11792 = nonceSlot output 9 := eB 3 (by decide)
  have b4 : offB (leafW M / 64 % 64) 4 + 11792 = nonceSlot output 10 := eB 4 (by decide)
  simp only [padMem]
  rw [a0, a1, a2, a3, a4, e5, b0, b1, b2, b3, b4]
  rfl

theorem padList_bound (M : Word → Word) (output : HashOutput) : ∀ p ∈ padList M output, p.1 < 2 ^ 64 := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  have := noncePos_bounds output j (List.mem_range.mp hj)
  show 4128 + noncePos output j < 2 ^ 64
  omega

theorem padList_nodup (M : Word → Word) (output : HashOutput) : ((padList M output).map Prod.fst).Nodup := by
  rw [padList, List.map_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro x hx y hy e
  by_contra hne
  have := noncePos_disjoint output x y (List.mem_range.mp hx) (List.mem_range.mp hy) hne
  simp only [Function.comp, nonceSlot] at e
  omega

/-- Nonce `j` lands at `0x1020 + noncePos output j`. -/
theorem padMem_nonce (M : Word → Word) (output : HashOutput)
    (hleaf : leafW M % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096) (j : Nat) (hj : j < 11) :
    padMem M (BitVec.ofNat 64 (4128 + noncePos output j)) = M (nonceAddr j) := by
  rw [padMem_eq M output hleaf]
  exact updF_in _ M _ _ (padList_bound M output) (padList_nodup M output)
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- Every other dword is unchanged. -/
theorem padMem_other (M : Word → Word) (output : HashOutput)
    (hleaf : leafW M % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096) (A : Word)
    (hA : ∀ j, j < 11 → A ≠ BitVec.ofNat 64 (4128 + noncePos output j)) : padMem M A = M A := by
  rw [padMem_eq M output hleaf]
  apply updF_out
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  exact hA j (List.mem_range.mp hj)

/-! ### Section 3: dword read-back of `witEncN` -/

theorem witEncN_getLsbD_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (i : Nat)
    (hw : ∀ j, j < 11 → i / 8 < noncePos output j ∨ noncePos output j + 8 ≤ i / 8) :
    (witEncN output w).getLsbD i = (Paired.witEnc output w).getLsbD i := by
  by_cases hlt : i < 8 * 22012
  · have e : ∀ x : WBytes, x.getLsbD i = (x.extractLsb' (8 * (i / 8)) (8 * 1)).getLsbD (i % 8) := by
      intro x
      rw [BitVec.getLsbD_extractLsb']
      simp [show i % 8 < 8 * 1 by omega, show 8 * (i / 8) + i % 8 = i by omega]
    rw [e (witEncN output w), e (Paired.witEnc output w), witEncN_extract_free output w (i / 8) 1 (by omega) (by
      intro i' hi1 hi2 j hj
      have := hw j hj
      omega)]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

theorem extract_word_eq {w : Nat} (x y : BitVec w) (k : Nat)
    (h : ∀ b, b < 64 → x.getLsbD (64 * k + b) = y.getLsbD (64 * k + b)) :
    x.extractLsb' (64 * k) 64 = y.extractLsb' (64 * k) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', h b hb]

/-- A dword of the witness buffer that is not a nonce pad is the nonce-free encoding's. -/
theorem witEncN_word_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (k : Nat)
    (hk : ∀ j, j < 11 → 8 * k ≠ noncePos output j) :
    (witEncN output w).extractLsb' (64 * k) 64 = (Paired.witEnc output w).extractLsb' (64 * k) 64 :=
  extract_word_eq _ _ k fun b hb => witEncN_getLsbD_free output w _ fun j hj => by
    have h1 := hk j hj
    have h2 := noncePos_mod8 output j
    omega

/-- The nonce dwords. -/
theorem witEncN_word_nonce (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (j : Nat)
    (hj : j < 11) (k : Nat) (hk : 8 * k = noncePos output j) :
    (witEncN output w).extractLsb' (64 * k) 64 = BitVec.ofNat 64 (w.topNonces.getD j 0) := by
  rw [show 64 * k = 8 * noncePos output j by omega]
  exact witEncN_nonce_lo output w j hj

/-! ### Section 4: the pad writer turns `witEnc` into `witEncN` -/

/-- Word-level: if the 2752 dwords at `0x1020` hold `Paired.witEnc output w`, the leaf word at `0x66758` is the
digest leaf (mod 4096) and `mem[0x66700 + 8 j] = w.topNonces[j]` (`j < 11`, mod `2^64`), then after the pad writer
the 2752 dwords hold `Paired.witEncN output w`. -/
theorem padMem_witEncN (M : Word → Word) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hleaf : leafW M % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096)
    (hn : ∀ j, j < 11 → M (nonceAddr j) = BitVec.ofNat 64 (w.topNonces.getD j 0))
    (hbuf : ∀ k, k < 2752 → M (BitVec.ofNat 64 (4128 + 8 * k)) = (Paired.witEnc output w).extractLsb' (64 * k) 64) :
    ∀ k, k < 2752 → padMem M (BitVec.ofNat 64 (4128 + 8 * k)) = (witEncN output w).extractLsb' (64 * k) 64 := by
  intro k hk
  by_cases h : ∃ j, j < 11 ∧ 8 * k = noncePos output j
  · obtain ⟨j, hj, e⟩ := h
    rw [e, padMem_nonce M output hleaf j hj, hn j hj, witEncN_word_nonce output w j hj k e]
  · rw [padMem_other M output hleaf _ (fun j hj he => ?_), hbuf k hk, witEncN_word_free output w k
      (fun j hj e => h ⟨j, hj, e⟩)]
    apply h
    refine ⟨j, hj, ?_⟩
    have hb := noncePos_bounds output j hj
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega

section machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
/-- Machine-level (from the post-pass hook `54174: jal 44961`): 68 steps to the `ecall` at 45016 with `a0 = 0`; the
witness dwords become `Paired.witEncN output w`; only the eleven nonce slots `0x1020 + noncePos output j` change. -/
theorem pad_hook_witEncN (s : MachineState) (hpc : s.pc = pcOf 54174) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hleaf : (s.getMem (BitVec.ofNat 64 0x66758)).toNat % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096)
    (hn : ∀ j, j < 11 → s.getMem (nonceAddr j) = BitVec.ofNat 64 (w.topNonces.getD j 0))
    (hbuf : ∀ k, k < 2752 → s.getMem (BitVec.ofNat 64 (4128 + 8 * k)) =
      (Paired.witEnc output w).extractLsb' (64 * k) 64) :
    ∃ t, Steps Images.expandImage s 68 68 t ∧
      t.pc = pcOf 45016 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29, .x30] ∧
      (∀ k, k < 2752 → t.getMem (BitVec.ofNat 64 (4128 + 8 * k)) = (witEncN output w).extractLsb' (64 * k) 64) ∧
      (∀ A, (∀ j, j < 11 → A ≠ BitVec.ofNat 64 (4128 + noncePos output j)) → t.getMem A = s.getMem A) := by
  obtain ⟨t, st, tp, t10, rt, mt⟩ := pad_hook s hpc
  refine ⟨t, st, tp, t10, rt, fun k hk => ?_, fun A hA => ?_⟩
  · rw [mt]; exact padMem_witEncN s.getMem output w hleaf hn hbuf k hk
  · rw [mt]; exact padMem_other s.getMem output hleaf A hA

end machine

#print axioms padMem_witEncN
#print axioms pad_hook_witEncN
end ClaudeWCT.W9.Machine.Expand.PadWit
