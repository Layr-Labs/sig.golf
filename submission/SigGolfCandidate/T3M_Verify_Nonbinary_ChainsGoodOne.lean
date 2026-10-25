import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsGoodChecks
import SigGolfCandidate.T3M_Verify_Nonbinary_ChainsDispatchArith

set_option maxRecDepth 20000
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
theorem map_slot_ite (P : Prop) [Decidable P] (a : Nat) :
    (if P then some a else none).map slotOffset = (if P then some (slotOffset a) else none) := by
  split <;> rfl
theorem rungR_keeps (d : Nat) (sl : Option Nat) (p : Nat) : Keeps (rungR d sl p) [.x12] :=
  T3M.rungRB_keeps d (sl.map slotOffset) p
theorem copyN_keeps (rb : Reg) (o : Word) (sl tgt : Nat) (g : Bool := false) : Keeps (copyN rb o sl tgt g) [.x3,.x14] :=
  T3M.copyNB_keeps rb o (slotOffset sl) tgt g
theorem copyFH_keeps (rb : Reg) (o : Word) (sl p : Nat) (g : Bool := false) : Keeps (copyFH rb o sl p g) [.x3,.x14] :=
  T3M.copyFHB_keeps rb o (slotOffset sl) p g
theorem headRH_keeps (rb : Reg) (o : Word) (d : Nat) (sl : Option Nat) (p i : Nat) (g : Bool := false) :
    Keeps (headRH rb o d sl p i g) [.x10,.x12,.x25] :=
  T3M.headRHB_keeps rb o d (sl.map slotOffset) p i g
def copyMem (rb : Reg) (o : Word) (sl : Nat) (g : Bool := false) : SymMem := T3M.copyMemB rb o (slotOffset sl) g
theorem tailR_keeps (slot : Option Nat) (p : Nat) : Keeps (tailR slot p) [.x12] := by
  intro x hx
  simp only [tailR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem bufferAdd_eval {s : MachineState} (h4 : s.getReg .x4=24704) (i : Nat) :
    (addC (.reg .x4) (BitVec.ofNat 64 (slotOffset (slot i)))).eval s = BitVec.ofNat 64 (slot i) := by
  rw [addC_eval]; simp only [E.eval,h4]
  rw [show (24704 : Word)=BitVec.ofNat 64 24704 from rfl,ofNat_add_ofNat]
  rw [show 24704+slotOffset (slot i)=slot i by unfold slotOffset slot; split <;> omega]
/-- T51: the terminal step's destination `termSlot i` (chain 0: `slot 0 - 16`). -/
theorem termAdd_eval {s : MachineState} (h4 : s.getReg .x4=24704) (i : Nat) :
    (addC (.reg .x4) (BitVec.ofNat 64 (slotOffset (termSlot i)))).eval s = BitVec.ofNat 64 (termSlot i) := by
  rw [addC_eval]; simp only [E.eval,h4]
  rw [show (24704 : Word)=BitVec.ofNat 64 24704 from rfl,ofNat_add_ofNat]
  rw [show 24704+slotOffset (termSlot i)=termSlot i by unfold slotOffset termSlot slot; split_ifs <;> omega]
theorem bufferAddr_eval {s : MachineState} (h4 : s.getReg .x4=24704) (i k : Nat) :
    (⟨some (.reg .x4),BitVec.ofNat 64 (slotOffset (slot i)+k)⟩ : Addr).eval s = BitVec.ofNat 64 (slot i+k) := by
  simp only [Addr.eval,E.eval,h4]
  rw [show (24704 : Word)=BitVec.ofNat 64 24704 from rfl,ofNat_add_ofNat]
  congr 1; unfold slotOffset slot; split <;> omega
theorem prehash_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : i < 51) (hm : m ≤ last i) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputL 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i)) ∧
      ∀ a : BitVec 256,
        (m < last i → c.StepInv s0 i acc (m + 1) (Verify.vHalf (topHigh i m) a) (writeHash t a)) ∧
        (m = last i → c.EndInv s0 i (acc ++ [Verify.vHalf (topHigh i m) a]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi
  have ho := c.oAt_props hc i hi
  have hva := c.vAt_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide +kernel)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide +kernel)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · have hts := termSlot_props i hi
    apply hashArgs_const t (c.blk i) 64 (if m = last i then termSlot i else c.oAt i) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm2 => ?_, fun hm2 => ?_⟩
    · have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.oAt i) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; exact h)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.oAt i ≤ A ∧ A < c.oAt i + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      have hhdr : c.oAt i + 32 ≤ c.blk i + 16 ∨ c.blk i + 32 ≤ c.oAt i := by unfold oAt; omega
      have hnew : DigAt (writeHash t a) (c.vAt i) (Verify.vHalf (topHigh i m) a) := by
        have hth : topHigh i m = topG i := by unfold topHigh; simp [show m + 1 < topMax i by omega]
        rw [hth]
        cases hg : topG i
        · rw [(c.oAt_F hc i hi hg).symm, Verify.vHalf_false]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
        · rw [(c.oAt_G hc i hi hg).symm, Verify.vHalf_true]
          exact DigAt.writeHash_hi t a _ d12 (by omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        ⟨?_, ?_, ?_⟩, hnew,
        by rw [getReg_writeHash]; exact h10, fun _ => by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slot_props j (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16]
        exact (c.w0_low i m hi (by omega)).1
      · rw [fget _ (by omega) (by omega), h16]
        exact (c.w0_low i m hi (by omega)).2
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    · subst hm2
      have hts := termSlot_props i hi
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (termSlot i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        rcases h with h | h
        · exact c.WrIn_next hc i A hi h
        · exact c.Wr_hash i A (by omega) h.1 h.2)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen], ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slot_props j (by omega)
          have hi0 : 0 < i := by omega
          have hmono : slot j + 16 ≤ termSlot i := by
            rw [hts.2.2.2.2 hi0]; unfold slot; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
          by_cases hi0 : i = 0
          · subst hi0
            have hth : topHigh 0 (last 0) = true := by unfold topHigh; simp [topG]
            rw [hth, Verify.vHalf_true, ← hts.2.2.2.1 rfl]
            exact DigAt.writeHash_hi t a _ d12 (by omega)
          · have hth : topHigh i (last i) = false := by
              unfold topHigh; simp [show ¬ (last i + 1 < topMax i) by omega, hi0]
            rw [hth, Verify.vHalf_false, ← hts.2.2.2.2 (by omega)]
            exact DigAt.writeHash_lo t a _ d12 (by omega)
      · have hd3 : c.dig i < topMax i := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end hds i hi hd3, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
theorem rung_piece (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i < 51) (hm : m ≤ last i) (hp : p < 257181)
    (hrun : vrun p 3 = some (rungR m (if m = last i then some (termSlot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (termSlot i)) ∧ (m < last i → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = last i then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have h4 : s.getReg .x4 = 24704 := (hR _ (by decide +kernel)).trans (hk (.x4,24704) (by simp [known]))
  set r := rungR m (if m = last i then some (termSlot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 17⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (17 : Word) = BitVec.ofNat 64 17 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB])
  have hn : r.steps = (if m = last i then 2 else 1) ∧ r.cycles = (if m = last i then 2 else 1) := by
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = last i then some (termSlot i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 1 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR i m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide +kernel)]; exact termAdd_eval h4 i
  · rw [Result.toState_getReg]
    simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB, if_neg (show m ≠ last i by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have hp := c.prefix_props
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1
    unfold w0
    omega
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR, map_slot_ite, Option.map_some, Option.map_none, T3M.rungRB]
    by_cases h2 : m = last i <;> simp [h2, E.eval]
theorem tail_piece (i m p : Nat) (hp : p < 257181)
    (hrun : vrun p 2 = some (tailR (if m = last i then some (termSlot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (h4 : s.getReg .x4=24704) :
    ∃ t, Steps vimage s (if m = last i then 1 else 0) (if m = last i then 1 else 0) t ∧
      fetch vimage t = some (.base .ECALL) ∧ (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (termSlot i)) ∧ (m ≠ last i → t.getReg .x12 = s.getReg .x12) ∧
      Frame s t (fun _ => False) ∧ t.pc = pcOf (p + (if m = last i then 1 else 0)) := by
  set r := tailR (if m = last i then some (termSlot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by simp [hr, tailR]
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, tailR])
  have hn : r.steps = (if m = last i then 1 else 0) ∧ r.cycles = (if m = last i then 1 else 0) := by
    simp only [hr, tailR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := tailR_keeps (if m = last i then some (termSlot i) else none) p
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_,
    fun A hA _ => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide +kernel)]; exact termAdd_eval h4 i
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_neg h2]
    rw [RegFile.init_get_eval]
  · rw [Result.toState_getMem]; simp [hr, tailR, memEval]
  · rw [Result.toState_pc]; simp only [hr, tailR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]
theorem rung_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : i < 51) (hm : m ≤ last i) (hp : c.rungPc i m < 257181)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = last i then some (termSlot i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hva := c.vAt_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi hm hp hrun s hpc hR h10 hH
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide +kernel)]; exact h10
  · by_cases h2 : m = last i
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), h12 (by omega), if_neg h2]
  · rw [hpc']
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem kAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 51) (k : Nat) (hk : k ≤ 80) : (kAt .x8 (off i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h19]
  exact c.base_off hc i hi k hk
theorem lAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 51) (k : Nat) (hk : k ≤ 80) :
    (lAt .x8 (off i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h19]
  rw [c.base_off hc i hi k hk]
theorem header_load (c : NCtx) {s : MachineState} (i d : Nat)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (c.prefix + 385)) :
    (hLoad i d).eval s = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * d) := by
  simp only [hLoad, addC_eval, E.eval, h28]
  have e : BitVec.ofNat 64 (c.prefix + 385) = BitVec.ofNat 64 c.prefix + BitVec.ofNat 64 385 := by
    rw [ofNat_add_ofNat]
  rw [e, show ∀ x y z : Word, x + z + (y - z) = x + y from fun x y z => by bv_omega, ofNat_add_ofNat]
  congr 1
  unfold w0
  omega
theorem padHeader_at {c : NCtx} {s0 s : MachineState} (hc : c.ok) (h0 : c.Orig0 s0)
    {i : Nat} (hi : i < 51) (hF : Frame s0 s (c.Wr i)) :
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = c.padHeader i := by
  have hb := c.blk_props hc i hi
  have ho := orig_frame hF h0 hc hi (k := 3) (by omega) (c.notWr_block hc hi (by omega) (by omega))
  change s.getMem (BitVec.ofNat 64 (c.blk i + 24)) =
    c.w.extractLsb' (8 * (c.blk i + 24 - Verify.WIT)) 64 at ho
  rw [ho, padHeader, wdig_hi]
  rw [show c.blk i + 24 - Verify.WIT = c.blk i - Verify.WIT + 16 + 8 by omega]
theorem vAt_gVal (c : NCtx) (i : Nat) (hi : i < 51) : c.vAt i = c.blk i + gVal (topG i) := by
  rw [topG_lt i hi]; unfold vAt gVal; by_cases h : i % 2 = 0 <;> simp [h] <;> omega
theorem copy_mem (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3) (h4 : s.getReg .x4=24704) (i : Nat)
    (hi : i < 51) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMem .x8 (off i) (slot i) (topG i)) (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.vAt i + 8))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.vAt i)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := slot_props i hi
  have hg : gVal (topG i) ≤ 48 := by unfold gVal; split <;> omega
  unfold copyMem T3M.copyMemB
  rw [memEval_two s _ _ _ _ (slot i + 8) (slot i) A (bufferAddr_eval h4 i 8) (by simpa using bufferAddr_eval h4 i 0) (by omega) (by omega) hA,
    c.lAt_eval hc h19 i hi (gVal (topG i) + 8) (by omega), c.lAt_eval hc h19 i hi (gVal (topG i)) (by omega),
    c.vAt_gVal i hi,
    show c.blk i + gVal (topG i) + 8 = c.blk i + (gVal (topG i) + 8) by ring]
theorem copy_obl (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3)
    (h4 : s.getReg .x4=24704) (i : Nat) (hi : i < 51) :
    ∀ o ∈ T3M.copyOblB .x8 (off i) (slotOffset (slot i)) (topG i), o.holds s := by
  have hb := c.blk_props hc i hi
  have hs := slot_props i hi
  have hva := c.vAt_props hc i hi
  have ev := c.vAt_gVal i hi
  have hg : gVal (topG i) ≤ 48 := by unfold gVal; split <;> omega
  simp only [T3M.copyOblB,T3M.copyObl,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro o (rfl | rfl | rfl | rfl)
  · show accessValid _ 8=true
    rw [bufferAddr_eval h4 i 8]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid _ 8=true
    have he := bufferAddr_eval h4 i 0
    simp only [Nat.add_zero] at he
    rw [he]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x8 (off i) (gVal (topG i) + 8)).eval s) 8=true
    rw [c.kAt_eval hc h19 i hi (gVal (topG i) + 8) (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x8 (off i) (gVal (topG i))).eval s) 8=true
    rw [c.kAt_eval hc h19 i hi (gVal (topG i)) (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
theorem copy_post (c : NCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : i < 51) (acc : List Digest) (hlen : acc.length = i) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))
    (h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3) (h4 : s.getReg .x4=24704)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      memEval s (copyMem .x8 (off i) (slot i) (topG i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (slot j) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi
  have hs := slot_props i hi
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.vAt i + 8))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.vAt i)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h19 h4 i hi A hA)
  have hfr : Frame s t (fun A => A = slot i + 8 ∨ A = slot i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    rcases h with h | h
    · exact c.Wr_mono i A h
    · exact c.Wr_copy i A (by omega) (by omega)
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := slot_props j (by omega)
      have hmono : slot j + 16 ≤ slot i := by unfold slot; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2
theorem copyN_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51)
    (hp0 : c.startPc i < 257181)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x8 (off i) (slot i) (c.endPc i) (topG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  set r := copyN .x8 (off i) (slot i) (c.endPc i) (topG i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyN, T3M.copyNB] using c.copy_obl hc h19 h4 i hi)
  have hkeep := copyN_keeps .x8 (off i) (slot i) (c.endPc i) (topG i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19 h4
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; rfl
theorem copyFH_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hp0 : c.startPc i < 257181)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x8 (off i) (slot i) (c.startPc i) (topG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  set r := copyFH .x8 (off i) (slot i) (c.startPc i) (topG i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyFH, T3M.copyFHB] using c.copy_obl hc h19 h4 i hi)
  have hkeep := copyFH_keeps .x8 (off i) (slot i) (c.startPc i) (topG i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19 h4
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, T3M.copyFHB, E.eval]; rw [hend]
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
theorem headJD_keeps (rb : Reg) (o : Word) (tgt i d : Nat) (g : Bool := false) :
    Keeps (headJD rb o tgt i d g) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJD]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headJDTerm_keeps (rb : Reg) (o : Word) (tgt i d : Nat) :
    Keeps (headJDTerm rb o tgt i d) [.x10, .x25] := by
  intro x hx
  simp only [headJDTerm]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem headJ_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 257181) (hp1 : c.rungPc i (c.dig i) + 1 < 257181)
    {f n : Nat} {st : Stop}
    (hrun1 : vrun (c.startPc i) f =
      some {headJD .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) (topG i) with stop := st, steps := n, cycles := n})
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (termSlot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s n n t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide +kernel))
  set r := {headJD .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) (topG i) with stop := st, steps := n, cycles := n}
    with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJD, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJD_keeps .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) (topG i)
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  have t12 : t1.getReg .x12 = BitVec.ofNat 64 (c.oAt i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel), addC_eval, a0e]
    exact c.oAt_eval hc i hi _ rfl
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJD]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, -, h12b, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1 ((hR1 _ (by decide +kernel)).trans (hk (.x4,24704) (by simp [known])))
  have hsteps : r.steps = n ∧ r.cycles = n := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hn : c.dig i ≠ last i := by omega
  rw [if_neg hn] at hst2
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hva := c.vAt_props hc i hi
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega)]
    exact padHeader_at hc h0 hi hF
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide +kernel)]; exact t10
  · rw [h12b hn, t12, if_neg hn]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)
theorem headJTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 257181) (hp1 : c.rungPc i (c.dig i) + 1 < 257181)
    {f n : Nat} {st : Stop}
    (hrun1 : vrun (c.startPc i) f =
      some {headJDTerm .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with stop := st, steps := n, cycles := n})
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (termSlot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (n + 1) (n + 1) t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide +kernel))
  set r := {headJDTerm .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with stop := st, steps := n, cycles := n}
    with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJDTerm, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJDTerm_keeps .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJDTerm]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel), a0e]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJDTerm]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, -, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1 ((hR1 _ (by decide +kernel)).trans (hk (.x4,24704) (by simp [known])))
  have hsteps : r.steps = n ∧ r.cycles = n := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  rw [if_pos hd] at hst2
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hva := c.vAt_props hc i hi
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega)]
    exact padHeader_at hc h0 hi hF
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide +kernel)]; exact t10
  · rw [h12a hd, if_pos hd]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
theorem headRHT_keeps (rb : Reg) (o : Word) (d sl p i : Nat) :
    Keeps (headRHT rb o d sl p i) [.x10, .x12, .x25] :=
  headRH_keeps rb o d (some sl) p i
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem headR_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 257181) (hrp : c.rungPc i (c.dig i) = c.startPc i + 3)
    (hrun : vrun (c.startPc i) 8 = some (headRH .x8 (off i) (c.dig i) none (c.startPc i) i (topG i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide +kernel))
  set r := headRH .x8 (off i) (c.dig i) none (c.startPc i) i (topG i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRH, Option.map_none, T3M.headRHB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRH, Option.map_none, T3M.headRHB])
  have hn : r.steps = 4 ∧ r.cycles = 4 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRH_keeps .x8 (off i) (c.dig i) none (c.startPc i) i (topG i)
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else if A = c.blk i + 24 then c.padHeader i else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRH, Option.map_none, T3M.headRHB]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
    have hpad := padHeader_at hc h0 hi hF
    split_ifs <;> simp_all
  have hpad0 := padHeader_at hc h0 hi hF
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
    split_ifs with h24
    · rw [h24]; exact hpad0.symm
    · rfl
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hva := c.vAt_props hc i hi
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRH, Option.map_none, T3M.headRHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_getReg]; simp only [hr, headRH, Option.map_none, T3M.headRHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel)]
    simp only [h2, if_false]
    rw [addC_eval, a0e]
    exact c.oAt_eval hc i hi _ rfl
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_pc]; simp only [hr, headRH, Option.map_none, T3M.headRHB, hrp]
    simp [h2, E.eval]
theorem headRTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 51) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 257181) (hrp : c.rungPc i (c.dig i) = c.startPc i + 2)
    (hrun : vrun (c.startPc i) 8 =
      some (headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i)) (hi0 : i ≠ 0)
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  have hts : termSlot i = slot i := by unfold termSlot; rw [if_neg hi0]
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide +kernel)
  have h4 : s.getReg .x4 = 24704 := kr _ _ (by simp [known]) (by decide +kernel)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide +kernel))
  set r := headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRHT, headRH, Option.map_some, T3M.headRHB])
  have hn : r.steps = 4 ∧ r.cycles = 4 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRHT_keeps .x8 (off i) (c.dig i) (slot i) (c.startPc i) i
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else if A = c.blk i + 24 then c.padHeader i else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
    have hpad := padHeader_at hc h0 hi hF
    split_ifs <;> simp_all
  have hpad0 := padHeader_at hc h0 hi hF
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
    split_ifs with h24
    · rw [h24]; exact hpad0.symm
    · rfl
  have hv0 : DigAt s (c.vAt i) (c.val i) := val_at hc h0 hi hF
  have hva := c.vAt_props hc i hi
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide +kernel))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB]
    rw [RegFile.get_set_ne _ _ (by decide +kernel), RegFile.get_set_self _ _ (by decide +kernel)]
    simpa only [hd,if_true,hts] using bufferAdd_eval h4 i
  · rw [Result.toState_pc]; simp only [hr, headRHT, headRH, Option.map_some, T3M.headRHB, hrp]
    simp [hd, E.eval]
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 800000
theorem baseTab_all : (baseTab.all fun x => decide (x<256000))=true := by decide +kernel
theorem body6Tab_all : (body6Tab.all fun x => decide (x<256000))=true := by decide +kernel
theorem body7Tab_all : (body7Tab.all fun x => decide (x<256000))=true := by decide +kernel
theorem getD_lt256 (l : List Nat) (n : Nat) (h : (l.all fun x => decide (x<256000))=true) : l.getD n 0<256000 := by
  rw [List.getD_eq_getElem?_getD]
  cases hn : l[n]? with
  | none => simp
  | some x => simpa using List.all_eq_true.mp h x (List.mem_of_getElem? hn)
theorem base_lt (q dB dC : Nat) : base q dB dC<256000 := by
  unfold base body6
  split_ifs
  · exact getD_lt256 _ _ body6Tab_all
  · exact getD_lt256 _ _ baseTab_all
  · exact getD_lt256 _ _ body7Tab_all
  · exact getD_lt256 _ _ baseTab_all
theorem mx_bounds (q : Nat) : 3≤ mx q ∧ mx q≤7 := by unfold mx; split_ifs <;> omega
theorem partLen_ge (q d : Nat) : 4 ≤ partLen q d := by
  have hm := mx_bounds q
  unfold partLen
  split_ifs <;> omega
theorem partLen_rung (q d : Nat) (hd : d < mx q) : 2*(mx q-d)+3 ≤ partLen q d := by
  unfold partLen
  split_ifs <;> omega
theorem partLen_le (q d : Nat) : partLen q d≤18 := by
  have hm := mx_bounds q
  unfold partLen
  split_ifs <;> omega
theorem kdig_le (q k j : Nat) : kdig q k j ≤ mx q := by
  have := mx_bounds q
  unfold kdig; have := Nat.mod_lt (k/(mx q+1)^j) (show 0 < mx q+1 by omega); omega
theorem inl_q (q k : Nat) (h : rowInl q k=true) : q<16 := rowInl_lt q k h
/-- Inline rows are #938's r5 rows (groups 9..15). -/
theorem leadPc_top_bounds (q k : Nat) (h9 : 9 ≤ q) (hq : q<16) (hk : k<125) :
    leadPc q k ≤ 129600 ∧ 64 ≤ leadPc q k := by
  have hu := entOff_le q (by omega)
  have hl := entOff_ge q
  unfold leadPc leadOff entW cellW
  rw [if_neg (by omega), if_pos hq]
  split_ifs <;> omega
/-- T51: every group cell (r6 rank < 216, r5 rank < 125, r7 rank < 49) sits below word 226812 (the checksum chain 50
starts at its arm `ckArm`, not at a group cell). -/
theorem leadPc_le (q k : Nat) (hq : q<17) (hk : k<nRank q) : leadPc q k ≤ 226811 := by
  by_cases h9 : q<9
  · have hk6 : k<216 := by unfold nRank mx at hk; rw [if_neg (by omega), if_pos h9] at hk; norm_num at hk; exact hk
    unfold leadPc leadOff entW cellW cell6 rawOf6 r6Off r6B
    rw [if_pos h9]
    split_ifs <;> omega
  · by_cases h16 : q=16
    · subst h16
      have hk7 : k<49 := by unfold nRank at hk; simpa using hk
      unfold leadPc leadOff entW cellW entOff
      simp only [show ¬ (16:Nat)<9 by omega, show ¬ (16:Nat)<16 by omega, if_false, if_true]
      split_ifs <;> omega
    · have hk5 : k<125 := by
        unfold nRank mx at hk; rw [if_neg h16, if_neg h9, if_pos (by omega)] at hk; norm_num at hk; exact hk
      have := leadPc_top_bounds q k (by omega) (by omega) hk5; omega
theorem group_bounds (q k : Nat) (hq : q<17) (hk : k<nRank q) :
    gbase q k+2*mx q+2<257181 ∧ gX q k+4<257181 ∧ leadPc q k<257181 ∧
      (rowInl q k=true → gbase q k+5 ≤ leadPc q k+8) := by
  have hm := mx_bounds q
  have h1 := partLen_le q (kdig q k 1)
  have h2 := partLen_le q (kdig q k 2)
  have hk0 := kdig_le q k 0
  have hl := leadPc_le q k hq hk
  unfold gX gC gB
  cases hn : rowInl q k
  · have hb := base_lt q (kdig q k 1) (kdig q k 2)
    simp only [gbase,hn,Bool.false_eq_true,if_false]
    refine ⟨by omega,by split_ifs <;> omega,by omega,fun h => absurd h (by simp)⟩
  · have hq' := inl_q q k hn
    have h9 := rowInl_ge q k hn
    have hk5 : k<125 := by rw [nRank_rowInl q k hn] at hk; exact hk
    have hl2 := leadPc_top_bounds q k h9 hq' hk5
    simp only [gbase,hn,if_true]
    refine ⟨?_,?_,by omega,fun _ => ?_⟩ <;> split_ifs <;> omega
namespace NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
theorem kOf_bounds (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) : c.kOf q<nRank q :=
  c.kOf_lt_nRank hds q hq
theorem qX_lt (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) : c.qX i+4<257181 :=
  (group_bounds _ _ (by omega) (c.kOf_bounds hds (i/3) (by omega))).2.1
theorem ckArm_room (d : Nat) (hd : d ≤ 7) : ckArm d+partLen 17 d+5<257181 := by
  have := partLen_le 17 d
  unfold ckArm; omega
theorem startPc_50 (c : NCtx) : c.startPc 50=ckArm (c.dig 50) := by simp [startPc]
theorem ck_end_lt (c : NCtx) (hds : c.DigitsOk) : c.startPc 50+partLen 17 (c.dig 50)+5<257181 := by
  have h5 := hds 50 (by omega)
  rw [topMax_50] at h5
  rw [c.startPc_50]; exact ckArm_room (c.dig 50) (by omega)
theorem startPc_room (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<50) : c.startPc i<256150 := by
  have h1 := c.kOf_bounds hds (i/3) (by omega)
  have hl := leadPc_le (i/3) (c.kOf (i/3)) (by omega) h1
  have hb := base_lt (i/3) (kdig (i/3) (c.kOf (i/3)) 1) (kdig (i/3) (c.kOf (i/3)) 2)
  have hm := mx_bounds (i/3)
  have hp := partLen_le (i/3) (kdig (i/3) (c.kOf (i/3)) 1)
  have hbase : gbase (i/3) (c.kOf (i/3))<256050 := by unfold gbase; split_ifs <;> omega
  unfold startPc qB qC gC gB
  rw [if_pos hi]
  split_ifs <;> omega
theorem startPc_lt (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) : c.startPc i<257181 := by
  by_cases h50 : i<50
  · have := c.startPc_room hds i h50; omega
  · have := c.ck_end_lt hds
    rw [show i=50 by omega]; omega
theorem last_50 : last 50=4 := by unfold last; rw [topMax_50]
theorem rungPc_lt (c : NCtx) (hds : c.DigitsOk) (i m : Nat) (hi : i<51) (hm : m≤ last i) :
    c.rungPc i m+2<257181 := by
  by_cases h50 : 50 ≤ i
  · obtain rfl : i=50 := by omega
    have he := c.ck_end_lt hds
    have hd := hds 50 (by omega)
    rw [topMax_50] at hd
    rw [last_50] at hm
    have hr : c.rungPc 50 m=c.startPc 50+(if c.dig 50=last 50 then 2 else 3)+2*(m-c.dig 50) := by
      unfold rungPc; simp
    rw [hr, last_50]
    unfold partLen mx at he
    simp only [show ¬ (17:Nat)<9 by decide, show ¬ (17:Nat)<16 by decide, show ¬ (17:Nat)=16 by decide,
      if_false] at he
    split_ifs at he ⊢ <;> omega
  have hs := c.startPc_room hds i (by omega)
  have h1 := c.kOf_bounds hds (i/3) (by omega)
  obtain ⟨b1,-,-,-⟩ := group_bounds _ _ (by omega) h1
  have hl := last_bounds i
  have hmx := mx_bounds (i/3)
  have hlm : last i+1=mx (i/3) := by unfold last; rw [topMax_mx i (by omega)]; omega
  unfold rungPc qb
  split_ifs <;> omega
theorem inline_rungPc (c : NCtx) (i : Nat) (h0 : ¬ (i%3=0 ∧ i<50)) :
    c.rungPc i (c.dig i)=c.startPc i+(if c.dig i=last i then 2 else 3) := by
  simp [rungPc,h0]
theorem skipA_eq (c : NCtx) (hds : c.DigitsOk) (q : Nat) (hq : q<17) :
    skipA q (c.kOf q)=decide (c.bufferSafe (3*q)) := by
  obtain ⟨k1,-,-⟩ := c.kdig_kOf' hds q hq
  by_cases h0 : q=0
  · subst h0
    simp [skipA,k1,bufferSafe,topMax,and_comm]
  · simp [skipA,h0,bufferSafe,show 3*q≠0 by omega]
theorem inline_max_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : ¬ (i%3=0 ∧ i<50))
    (hd : c.dig i=topMax i) : c.startPc i+4-(if c.bufferSafe i then 4 else 0)=c.endPc i := by
  by_cases h50 : i<50
  · have hn0 : i%3≠0 := fun h => h0 ⟨h,h50⟩
    obtain ⟨-,k2,k3⟩ := c.kdig_kOf' hds (i/3) (by omega)
    have hdm : c.dig i=mx (i/3) := by rw [hd, topMax_mx i h50]
    by_cases h1 : i%3=1
    · have ei : 3*(i/3)+1=i := by omega
      have he := c.skipB_eq hds (i/3) (by omega)
      rw [ei] at he k2
      simp only [startPc,endPc,h50,hn0,h1,if_true,if_false,qB,qC,gC,k2,he,decide_eq_true_eq]
      simp [partLen,hdm]
    · have ei : 3*(i/3)+2=i := by omega
      have h16 : i/3≠16 := by omega
      have he := c.skipC_eq hds (i/3) (by omega)
      have k3 := k3 h16
      rw [ei] at he k3
      simp only [startPc,endPc,h50,hn0,h1,if_true,if_false,qC,qX,gX,k3,he,decide_eq_true_eq,h16]
      simp [partLen,hdm]
  · obtain rfl : i=50 := by omega
    have hd5 : c.dig 50=5 := hd.trans topMax_50
    simp [startPc,endPc,ckTail,partLen,hd5,mx,bufferSafe]
theorem inline_copy_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : ¬ (i%3=0 ∧ i<50))
    (hd : c.dig i=topMax i) (hn : ¬ c.bufferSafe i) : c.startPc i+4=c.endPc i := by
  simpa [hn] using c.inline_max_end hds i hi h0 hd
theorem lead_max_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : i%3=0) (h50 : i<50)
    (hn : rowInl (i/3) (c.kOf (i/3))=true)
    (hd : c.dig i=topMax i) : c.startPc i+4-(if c.bufferSafe i then 4 else 0)=c.endPc i := by
  obtain ⟨k1,-,-⟩ := c.kdig_kOf' hds (i/3) (by omega)
  have ei : 3*(i/3)=i := by omega
  have e0 : c.dig (3*(i/3))=c.dig i := by rw [ei]
  have hm := mx_bounds (i/3)
  have h9 := rowInl_ge (i/3) (c.kOf (i/3)) hn
  have h16 := rowInl_lt (i/3) (c.kOf (i/3)) hn
  have hk := c.kOf_bounds hds (i/3) (by omega)
  have hk5 : c.kOf (i/3)<125 := by rw [nRank_rowInl _ _ hn] at hk; exact hk
  have hs : c.startPc i=leadPc (i/3) (c.kOf (i/3)) := by simp [startPc,h0,h50]
  have he : c.endPc i=gB (i/3) (c.kOf (i/3)) := by simp [endPc,qB,h0,h50]
  have hdm : kdig (i/3) (c.kOf (i/3)) 0=mx (i/3) := by rw [k1,e0,hd,topMax_mx i h50]
  have hg : gbase (i/3) (c.kOf (i/3))=leadPc (i/3) (c.kOf (i/3))+3-2*mx (i/3) := by simp [gbase,hn,hdm]
  have hlo : 64 ≤ leadPc (i/3) (c.kOf (i/3)) := (leadPc_top_bounds _ _ h9 h16 hk5).2
  have hskip := c.skipA_eq hds (i/3) (by omega)
  rw [ei] at hskip
  have hsh : sharedG (i/3)=false := by simp [sharedG]; omega
  rw [hs,he]
  simp only [gB,hg,hskip,decide_eq_true_eq,hsh,Bool.false_eq_true,if_false]
  omega
theorem lead_copy_end (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (h0 : i%3=0) (h50 : i<50)
    (hr : rowInl (i/3) (c.kOf (i/3))=true)
    (hd : c.dig i=topMax i) (hn : ¬ c.bufferSafe i) : c.startPc i+4=c.endPc i := by
  simpa [hn] using c.lead_max_end hds i hi h0 h50 hr hd
/-- T51 (as R6): a buffer-safe chain other than chain 0 is skipped in place (chain 0 is the g0 cell's `jal`). -/
theorem bufferSafe_pc (c : NCtx) (hds : c.DigitsOk) (i : Nat) (hi : i<51) (hs : c.bufferSafe i) (hiz : i≠0) :
    c.startPc i=c.endPc i := by
  have ht : ¬ (i%3=0 ∧ i<50) := by
    rintro ⟨h0,-⟩; rcases hs.2 with hz | hz; exact hiz hz; exact hz.2.1 h0
  simpa [hs] using c.inline_max_end hds i hi ht hs.1
/-- The buffer-safe end-state bookkeeping (registers, frame, slots) before any pc update. -/
theorem buffer_skip_base (c : NCtx) (hc : c.ok) (s0 s : MachineState) (h0 : c.Orig0 s0)
    (i : Nat) (hi : i<51) (hz : c.bufferSafe i) (acc : List T3.Digest) (hB : c.ChainIn s0 i acc s) :
    c.Base s0 (c.Wr (i+1)) (acc++[c.bufferVal i]) s ∧ (acc++[c.bufferVal i]).length=i+1 ∧ True := by
  obtain ⟨⟨hR,hF,hA⟩,hlen,hpc⟩ := hB
  have hb := c.blk_props hc 0 (by decide +kernel)
  refine ⟨⟨hR,hF.mono (fun A _ h => c.Wr_mono i A h),?_⟩,by simp [hlen],trivial⟩
  intro j hj
  rw [List.length_append,List.length_singleton] at hj
  by_cases hl : j<acc.length
  · rw [List.getD_eq_getElem?_getD,List.getElem?_append_left hl,← List.getD_eq_getElem?_getD]
    exact hA j hl
  · have hj' : j=acc.length := by omega
    subst hj'
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (le_refl _),Nat.sub_self,hlen]
    exact bufferVal_at h0.1.2 hi hz (by rw [slot0]; unfold blk at hb; omega) hF
theorem buffer_skip (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (s0 s : MachineState) (h0 : c.Orig0 s0)
    (i : Nat) (hi : i<51) (hz : c.bufferSafe i) (hiz : i≠0) (acc : List T3.Digest) (hB : c.ChainIn s0 i acc s) :
    Steps vimage s 0 0 s ∧ c.EndInv s0 i (acc++[c.bufferVal i]) s := by
  obtain ⟨hb1,hb2,-⟩ := c.buffer_skip_base hc s0 s h0 i hi hz acc hB
  obtain ⟨-,-,hpc⟩ := hB
  refine ⟨Steps.refl _, hb1, hb2, ?_⟩
  rw [hpc,c.bufferSafe_pc hds i hi hz hiz]
/-- T51 (as R6): chain 0 at its largest digit (always buffer-safe) is the g0 cell's single `jal` to chain B. -/
theorem skip0_step (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) (s0 s : MachineState) (h0 : c.Orig0 s0)
    (hz : c.bufferSafe 0) (acc : List T3.Digest) (hB : c.ChainIn s0 0 acc s) :
    ∃ t, Steps vimage s 1 1 t ∧ c.EndInv s0 0 (acc++[c.bufferVal 0]) t := by
  have hsk := c.buffer_skip_base hc s0 s h0 0 (by omega) hz acc hB
  obtain ⟨⟨hR,hF,hA⟩,hlen,hpc⟩ := hB
  have hrun := c.chk_skipJ hds hz.1
  have hp0 := c.startPc_lt hds 0 (by omega)
  have hst := piece_steps45 hrun hp0 s hpc (by simp [T3M.skipJB, SymState.init])
  have hreg : ∀ x, ((T3M.skipJB (c.endPc 0)).toState s).getReg x = s.getReg x := by
    intro x
    rw [Result.toState_getReg]
    change (RegFile.get RegFile.init x).eval s = _
    rw [RegFile.init_get_eval]
  have hmem : ∀ a, ((T3M.skipJB (c.endPc 0)).toState s).getMem a = s.getMem a := by
    intro a; simp [T3M.skipJB, SymState.init, Result.toState_getMem, memEval]
  have hfr : Frame s ((T3M.skipJB (c.endPc 0)).toState s) (fun _ => False) := fun A _ _ => hmem _
  obtain ⟨⟨hR',hF',hA'⟩,hlen',-⟩ := hsk
  refine ⟨_, hst, ⟨⟨fun x hx => (hreg x).trans (hR' x hx), (hF'.trans hfr).mono (fun A _ h => by
    rcases h with h|h; exact h; exact h.elim), fun j hj => ?_⟩, hlen', ?_⟩⟩
  · exact ⟨(hmem _).trans (hA' j hj).1, (hmem _).trans (hA' j hj).2⟩
  · rw [Result.toState_pc]; rfl
end NCtx
end SigGolfCandidate.T3M.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem chainInputL_pad (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) :
    pad64 (chainInputL lay tree leaf i step p0 p1 headerPad v g) = chainInputL lay tree leaf i step p0 p1 headerPad v g :=
  pad64_of_aligned _ (by rw [chainInputL_length])
theorem chainInputL_blocks (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest) (headerPad : Word) (v : Digest)
    (g : Bool) : (toQ (chainInputL lay tree leaf i step p0 p1 headerPad v g)).blocks = 1 := by
  rw [blocks_toQ ⟨by rw [chainInputL_length]; omega, by rw [chainInputL_length]⟩, chainInputL_length]
/-- The image's chain run from step `m` (G chains keep the high half of their interior steps, `topHigh`). -/
def rest (c : NCtx) (i m : Nat) (v : Digest) : M Digest :=
  (List.range' m (topMax i-m)).foldlM
    (fun v step => Verify.vHash (topHigh i step)
      (chainInputL 0 c.tree c.leaf i step (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i))) v
theorem rest_succ (c : NCtx) (i m : Nat) (h : m ≤ last i) (v : Digest) :
    c.rest i m v=Verify.vHash (topHigh i m)
      (chainInputL 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) (c.padHeader i) v (topG i)) >>= c.rest i (m+1) := by
  have hm := topMax_bounds i
  unfold last at h
  unfold rest
  rw [show topMax i-m=(topMax i-(m+1))+1 by omega,List.range'_succ,List.foldlM_cons]
theorem rest_max (c : NCtx) (i : Nat) (v : Digest) : c.rest i (topMax i) v=pure v := by
  simp [rest]
/-- The image's projected hash is the spec's `WCT9.halfHash`. -/
theorem topVHash_eq (high : Bool) (input : List UInt8) :
    Verify.vHash high input = ClaudeWCT.WCT9.halfHash high input := by
  rw [ClaudeWCT.WCT9.halfHash_eq]; unfold Verify.vHash; cases high <;> rfl
/-- The image's top chain run is the spec's `chainPW 0` (G/F pairing, `WCT9.chainHigh 0`). -/
theorem chainPW_rest (c : NCtx) (i d : Nat) (v : Digest) :
    ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i d (topMax i-d) (c.pad0 i) (c.pad1 i) (c.padHeader i) v=c.rest i d v := by
  unfold rest ClaudeWCT.W9.T3M.chainPW
  congr 1
  funext v step
  rw [topVHash_eq, chainInputL_top, topHigh_eq]
def preCost (i m : Nat) : Nat := 8+9*(last i-m)+(if m< last i then 1 else 0)
theorem steps_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<51)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → Verify.GoodQP P t N C Q A (K (acc++[v]))) :
    ∀k m,m+k=last i → c.dig i ≤ m → ∀v s,c.PreHash s0 i acc m v s →
      Verify.GoodQP P s (N+3*(topMax i-m)+5) (C+preCost i m) Q (A+preCost i m)
        (Verify.ccM (c.rest i m v) (fun v => K (acc++[v]))) := by
  have hmax := topMax_bounds i
  have hlast := last_bounds i
  have hlastEq : last i+1=topMax i := by unfold last;omega
  intro k
  induction k with
  | zero =>
      intro m hm hd v s hs
      obtain rfl : m=last i := by omega
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc hds s0 hk h0 i (last i) hi (le_refl _) hd acc v s hs
      rw [rest_succ c i (last i) (le_refl _)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,Verify.GoodQP P (writeHash s a) N C Q A
          (Verify.ccM (c.rest i (last i+1) (Verify.vHalf (topHigh i (last i)) a)) (fun v => K (acc++[v]))) := by
        intro a
        rw [hlastEq,rest_max,Verify.ccM_pure]
        exact hK _ _ ((hpost a).2 rfl)
      have h3 := Verify.GoodQP.vHash_bind (topHigh i (last i)) (f:=c.rest i (last i+1)) (K:=fun v => K (acc++[v]))
        hf h5 hv (by rw [chainInputL_pad];exact hin) H
      rw [chainInputL_pad,chainInputL_blocks] at h3
      exact h3.mono (by omega) (by simp [preCost]) (fun hq => ⟨hq,by simp [preCost]⟩)
  | succ k ih =>
      intro m hm hd v s hs
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc hds s0 hk h0 i m hi (by omega) hd acc v s hs
      rw [rest_succ c i m (by omega)]
      have hf := hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,Verify.GoodQP P (writeHash s a) (N+3*(topMax i-(m+1))+5+2)
          (C+preCost i (m+1)+(if m+1=last i then 2 else 1)) Q
          (A+preCost i (m+1)+(if m+1=last i then 2 else 1))
          (Verify.ccM (c.rest i (m+1) (Verify.vHalf (topHigh i m) a)) (fun v => K (acc++[v]))) := by
        intro a
        have hrun := c.chk_rung hds i (m+1) hi (by omega) (by omega)
        obtain ⟨u,hu,hp⟩ := c.rung_step hc hk i (m+1) hi (by omega)
          (by have := c.rungPc_lt hds i (m+1) hi (by omega); omega) hrun acc _ _
          ((hpost a).1 (by omega))
        have ht := ih (m+1) (by omega) (by omega) _ _ hp
        exact Verify.GoodQP.stepsQ hu ht (by split <;> omega) (by omega) (fun hq => ⟨hq,by omega⟩)
      have h3 := Verify.GoodQP.vHash_bind (topHigh i m) (f:=c.rest i (m+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputL_pad];exact hin) H
      rw [chainInputL_pad,chainInputL_blocks] at h3
      refine h3.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
section
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
variable {P : SigGolfCandidate.Legacy.Hash → Prop}
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem chainCost_positive (c : NCtx) (i d : Nat) (hd : d< topMax i) :
    c.chainCost i d=4+c.tableJump i+preCost i d := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  unfold chainCost preCost
  rw [if_neg (by omega)]
  split_ifs <;> omega
theorem positive_head (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<51)
    (hd : c.dig i< topMax i) (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃t,Steps vimage s (4+c.tableJump i) (4+c.tableJump i) t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  have hl : last i+1=topMax i := by have := topMax_bounds i;unfold last;omega
  have hsp := c.startPc_lt hds i hi
  by_cases htab : i%3=0 ∧ i<50
  · have hrun2 := c.chk_tail hds i htab.2 htab.1 hd
    have hrp : c.rungPc i (c.dig i)+1<257181 := by have := c.rungPc_lt hds i (c.dig i) hi (by omega); omega
    cases hn : rowInl (i/3) (c.kOf (i/3))
    · have hj : c.tableJump i=1 := by simp [tableJump,htab,hn]
      by_cases ht : c.dig i=last i
      · have hrun1 := c.chk_headJTerm hds i htab.2 htab.1 hn ht
        obtain ⟨t,hst,htp⟩ := c.headJTerm_step hc hk h0 i hi ht hsp hrp (st := .jump) (n := 4) hrun1 hrun2 acc s hs
        exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
      · have hrun1 := c.chk_headJ hds i htab.2 htab.1 hn (by omega)
        obtain ⟨t,hst,htp⟩ := c.headJ_step hc hk h0 i hi (by omega) hsp hrp (st := .jump) (n := 5) hrun1 hrun2 acc s hs
        exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
    · have hj : c.tableJump i=0 := by simp [tableJump,htab,hn]
      by_cases ht : c.dig i=last i
      · have hrun1 := c.chk_headJTermF hds i htab.2 htab.1 hn ht
        obtain ⟨t,hst,htp⟩ := c.headJTerm_step hc hk h0 i hi ht hsp hrp (st := .fuel) (n := 3) hrun1 hrun2 acc s hs
        exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
      · have hrun1 := c.chk_headJF hds i htab.2 htab.1 hn (by omega)
        obtain ⟨t,hst,htp⟩ := c.headJ_step hc hk h0 i hi (by omega) hsp hrp (st := .fuel) (n := 4) hrun1 hrun2 acc s hs
        exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
  · have hj : c.tableJump i=0 := by simp [tableJump,htab]
    have hiz : i≠0 := fun h => htab ⟨by omega, by omega⟩
    by_cases ht : c.dig i=last i
    · have hrun := c.chk_headRTerm hds i hi htab ht
      have hr : c.rungPc i (c.dig i)=c.startPc i+2 := by rw [inline_rungPc c i htab,if_pos ht]
      obtain ⟨t,hst,htp⟩ := c.headRTerm_step hc hk h0 i hi ht hsp hr hrun hiz acc s hs
      exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
    · have hrun := c.chk_headR hds i hi htab (by omega)
      have hr : c.rungPc i (c.dig i)=c.startPc i+3 := by rw [inline_rungPc c i htab,if_neg ht]
      obtain ⟨t,hst,htp⟩ := c.headR_step hc hk h0 i hi (by omega) hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by rw [hj]) (by rw [hj]),htp⟩
theorem tableJump_zero (c : NCtx) : c.tableJump 0=1 := by
  simp [tableJump, rowInl, inl]
theorem chain_good (c : NCtx) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<51)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → Verify.GoodQP P t N C Q A (K (acc++[v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    Verify.GoodQP P s (N+40) (C+c.chainCost i (c.dig i)) Q (A+c.chainCost i (c.dig i))
      (Verify.ccM (ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i)
        (c.padHeader i) (c.bufferVal i)) (fun v => K (acc++[v]))) := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  have hd := hds i hi
  have hsp := c.startPc_lt hds i hi
  by_cases hmax : c.dig i=topMax i
  · rw [hmax,Nat.sub_self]
    have hp : ClaudeWCT.W9.T3M.chainPW 0 c.tree c.leaf i (topMax i) 0 (c.pad0 i) (c.pad1 i) (c.padHeader i)
        (c.bufferVal i)=pure (c.bufferVal i) := rfl
    rw [hp,Verify.ccM_pure]
    by_cases hz : c.bufferSafe i
    · by_cases hiz : i=0
      · subst hiz
        obtain ⟨t,hst,ht⟩ := c.skip0_step hc hds s0 s h0 hz acc hs
        exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,c.tableJump_zero])
          (fun hq => ⟨hq,by simp [chainCost,hz,c.tableJump_zero]⟩)
      · have hj : c.tableJump i=0 := by
          have : i%3≠0 := by rcases hz.2 with h|h; exact absurd h hiz; exact h.2.1
          simp [tableJump,this]
        obtain ⟨hst,ht⟩ := c.buffer_skip hc hds s0 s h0 i hi hz hiz acc hs
        exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,hj])
          (fun hq => ⟨hq,by simp [chainCost,hz,hj]⟩)
    rw [bufferVal,if_neg hz]
    by_cases htab : i%3=0 ∧ i<50
    · cases hn : rowInl (i/3) (c.kOf (i/3))
      · have hiz : i≠0 := fun h => hz (by subst h; exact ⟨hmax, Or.inl rfl⟩)
        obtain ⟨t,hst,ht⟩ := c.copyN_step hc hk h0 i hi hsp
          (c.chk_copyJ hds i htab.2 htab.1 hiz hn hmax) acc s hs
        exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,tableJump,htab,hn])
          (fun hq => ⟨hq,by simp [chainCost,hz,tableJump,htab,hn]⟩)
      · have hsA : skipA (i/3) (c.kOf (i/3))=false := by
          rw [c.skipA_eq hds _ (by omega),show 3*(i/3)=i by omega]; simp [hz]
        obtain ⟨t,hst,ht⟩ := c.copyFH_step hc hk h0 i hi hsp
          (c.lead_copy_end hds i hi htab.1 htab.2 hn hmax hz) (c.chk_copyFL hds i htab.2 htab.1 hn hmax hsA) acc s hs
        exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,tableJump,htab,hn])
          (fun hq => ⟨hq,by simp [chainCost,hz,tableJump,htab,hn]⟩)
    · obtain ⟨t,hst,ht⟩ := c.copyFH_step hc hk h0 i hi hsp
        (c.inline_copy_end hds i hi htab hmax hz) (c.chk_copyF hds i hi htab hmax hz) acc s hs
      exact Verify.GoodQP.stepsQ hst (hK _ _ ht) (by omega) (by simp [chainCost,hz,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,hz,tableJump,htab]⟩)
  · have hd' : c.dig i< topMax i := by omega
    rw [c.bufferVal_nonmax i hmax,chainPW_rest]
    have H := c.steps_good hc hds hk h0 i hi acc K N C A Q hK (last i-c.dig i) (c.dig i) (by omega) (le_refl _)
    obtain ⟨t,hst,ht⟩ := c.positive_head hc hds hk h0 i hi hd' acc s hs
    have hj : c.tableJump i≤1 := by unfold tableJump;split <;> omega
    have he := c.chainCost_positive i (c.dig i) hd'
    exact Verify.GoodQP.stepsQ hst (H _ _ ht) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)
end SigGolfCandidate.T3M.Nonbinary.NCtx
end
