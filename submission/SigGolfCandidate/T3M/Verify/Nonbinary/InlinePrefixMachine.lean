import SigGolfCandidate.T3M.Verify.Nonbinary.InlinePrefixWindows
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailJudg
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne

/- Genuine first51 chain execution adapted from attributed ChainsGoodOne.
   Only finite CodeAt windows are supplied; every memory/frame/HASH outcome
   and finite-chain source bind is proved. Original public proofs untouched. -/
namespace SigGolfCandidate.T3M.Nonbinary.NCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Nonbinary SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem prefix_window_steps {p fuel : Nat} {r : Result}
    (hr : vrun p fuel=some r)
    (hw : CodeAt InlineTail.image (pcOf p) ((lcode p).take fuel))
    (s : MachineState) (hp : s.pc=pcOf p) (ho : ∀ o∈r.st.obl,o.holds s) :
    Steps InlineTail.image s r.steps r.cycles (r.toState s) :=
  symRun_prefix_sound hr (le_refl _) hw s hp ((Oblig.all_iff _ _).mpr ho)

theorem prefix_rung_piece (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i < 54) (hm : m ≤ last i) (hp : p < 251927)
    (hrun : vrun p 3 = some (rungR m (if m = last i then some (slot i) else none) p)) (hwin : CodeAt InlineTail.image (pcOf p) ((lcode p).take 3)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps InlineTail.image s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (slot i)) ∧ (m < last i → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = last i then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  set r := rungR m (if m = last i then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 17⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (17 : Word) = BitVec.ofNat 64 17 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := prefix_window_steps hrun hwin s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, rungR])
  have hn : r.steps = (if m = last i then 2 else 1) ∧ r.cycles = (if m = last i then 2 else 1) := by
    simp only [hr, rungR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = last i then some (slot i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 1 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR]
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
    simp only [hr, rungR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ last i by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have hp := c.prefix_props
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1
    unfold w0
    omega
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]

theorem prefix_tail_piece (i m p : Nat) (hp : p < 251927)
    (hrun : vrun p 2 = some (tailR (if m = last i then some (slot i) else none) p)) (hwin : CodeAt InlineTail.image (pcOf p) ((lcode p).take 2)) (s : MachineState)
    (hpc : s.pc = pcOf p) :
    ∃ t, Steps InlineTail.image s (if m = last i then 1 else 0) (if m = last i then 1 else 0) t ∧
      fetch vimage t = some (.base .ECALL) ∧ (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (slot i)) ∧ (m ≠ last i → t.getReg .x12 = s.getReg .x12) ∧
      Frame s t (fun _ => False) ∧ t.pc = pcOf (p + (if m = last i then 1 else 0)) := by
  set r := tailR (if m = last i then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by simp [hr, tailR]
  have hst := prefix_window_steps hrun hwin s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, tailR])
  have hn : r.steps = (if m = last i then 1 else 0) ∧ r.cycles = (if m = last i then 1 else 0) := by
    simp only [hr, tailR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := tailR_keeps (if m = last i then some (slot i) else none) p
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_,
    fun A hA _ => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_neg h2]
    rw [RegFile.init_get_eval]
  · rw [Result.toState_getMem]; simp [hr, tailR, memEval]
  · rw [Result.toState_pc]; simp only [hr, tailR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]

theorem prefix_rung_step (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : i < 54) (hip : i<51) (hm : m ≤ last i) (hp : c.rungPc i m < 251927)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = last i then some (slot i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps InlineTail.image s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.prefix_rung_piece hc hk i m (c.rungPc i m) hi hm hp hrun (hw.rung i hip m hm 3 (by decide)) s hpc hR h10 hH
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h10
  · by_cases h2 : m = last i
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), h12 (by omega), if_neg h2]
  · rw [hpc']

theorem prefix_copyN_step (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hip : i<51)
    (hp0 : c.startPc i < 251927)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x8 (off i) (slot i) (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x8 (off i) (slot i) (c.endPc i) with hr
  have hst := prefix_window_steps hrun (hw.start i hip _ (by decide)) s hpc (by simpa [hr, copyN] using c.copy_obl hc h19 i hi)
  have hkeep := copyN_keeps .x8 (off i) (slot i) (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; rfl

theorem prefix_copyFH_step (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hip : i<51) (hp0 : c.startPc i < 251927)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x8 (off i) (slot i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyFH .x8 (off i) (slot i) (c.startPc i) with hr
  have hst := prefix_window_steps hrun (hw.start i hip _ (by decide)) s hpc (by simpa [hr, copyFH] using c.copy_obl hc h19 i hi)
  have hkeep := copyFH_keeps .x8 (off i) (slot i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, E.eval]; rw [hend]

theorem prefix_headJ_step (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hip : i<51) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 251927) (hp1 : c.rungPc i (c.dig i) + 1 < 251927)
    (hrun1 : vrun (c.startPc i) 7 = some (headJD .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 5 5 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide))
  set r := headJD .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJD, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := prefix_window_steps hrun1 (hw.start i hip _ (by decide)) s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJD_keeps .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  have t12 : t1.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), addC_eval, a0e,
      show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
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
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, -, h12b, hfr2, hpc2⟩ :=
    prefix_tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 (hw.tail i hip (c.dig i) (by omega) 2 (by decide)) t1 hpc1
  have hsteps : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hn : c.dig i ≠ last i := by omega
  rw [if_neg hn] at hst2
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
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
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12b hn, t12, if_neg hn]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)

theorem prefix_headJTerm_step (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hip : i<51) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 251927) (hp1 : c.rungPc i (c.dig i) + 1 < 251927)
    (hrun1 : vrun (c.startPc i) 7 = some (headJDTerm .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 5 5 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide))
  set r := headJDTerm .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJDTerm, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := prefix_window_steps hrun1 (hw.start i hip _ (by decide)) s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJDTerm_keeps .x8 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJDTerm]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), a0e]
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
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, -, hfr2, hpc2⟩ :=
    prefix_tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 (hw.tail i hip (c.dig i) (by omega) 2 (by decide)) t1 hpc1
  have hsteps : r.steps = 4 ∧ r.cycles = 4 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  rw [if_pos hd] at hst2
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
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
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12a hd, if_pos hd]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)

theorem prefix_headR_step (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hip : i<51) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 251927) (hrp : c.rungPc i (c.dig i) = c.startPc i + 3)
    (hrun : vrun (c.startPc i) 8 = some (headRH .x8 (off i) (c.dig i) none (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 4 4 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide))
  set r := headRH .x8 (off i) (c.dig i) none (c.startPc i) i with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := prefix_window_steps hrun (hw.start i hip _ (by decide)) s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRH])
  have hn : r.steps = 4 ∧ r.cycles = 4 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headRH_keeps .x8 (off i) (c.dig i) none (c.startPc i) i
  have a0e : (addC (E.reg .x8) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 8 * c.dig i)
      else if A = c.blk i + 24 then c.padHeader i else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRH]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
    have hpad := padHeader_at hc h0 hi hF
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
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
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    simp only [h2, if_false]
    rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · have h2 : ¬ c.dig i = last i := by omega
    rw [Result.toState_pc]; simp only [hr, headRH, hrp]
    simp [h2, E.eval]

theorem prefix_headRTerm_step (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hip : i<51) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 251927) (hrp : c.rungPc i (c.dig i) = c.startPc i + 2)
    (hrun : vrun (c.startPc i) 8 =
      some (headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 4 4 t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x8 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load i (c.dig i) (kr _ _ (by simp [known]) (by decide))
  set r := headRHT .x8 (off i) (c.dig i) (slot i) (c.startPc i) i with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRHT, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x8 (off i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := prefix_window_steps hrun (hw.start i hip _ (by decide)) s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRHT, headRH])
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
    simp only [hr, headRHT, headRH]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [htable]
    have hpad := padHeader_at hc h0 hi hF
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
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
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRHT, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    simp only [hd, if_true, E.eval]
  · rw [Result.toState_pc]; simp only [hr, headRHT, headRH, hrp]
    simp [hd, E.eval]

theorem prefix_steps_good (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54) (hip : i<51)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec InlineTail.Judg.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → InlineTail.Judg.GoodQ InlineTail.image t N C Q A (K (acc++[v]))) :
    ∀k m,m+k=last i → c.dig i ≤ m → ∀v s,c.PreHash s0 i acc m v s →
      InlineTail.Judg.GoodQ InlineTail.image s (N+3*(topMax i-m)+5) (C+preCost i m) Q (A+preCost i m)
        (InlineTail.Judg.ccM (c.rest i m v) (fun v => K (acc++[v]))) := by
  have hmax := topMax_bounds i
  have hlast := last_bounds i
  have hlastEq : last i+1=topMax i := by unfold last;omega
  intro k
  induction k with
  | zero =>
      intro m hm hd v s hs
      obtain rfl : m=last i := by omega
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc s0 hk h0 i (last i) hi (le_refl _) hd acc v s hs
      rw [rest_succ c i (last i) (le_refl _)]
      have hf := (hw.prehash i hip (last i) (by omega) s hs.2.2.2.2.2.2.2.1).trans hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,InlineTail.Judg.GoodQ InlineTail.image (writeHash s a) N C Q A
          (InlineTail.Judg.ccM (c.rest i (last i+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        rw [hlastEq,rest_max,InlineTail.Judg.ccM_pure]
        exact hK _ _ ((hpost a).2 rfl)
      have h3 := InlineTail.Judg.GoodQ.shortHash_bind (f:=c.rest i (last i+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputP_pad];exact hin) H
      rw [chainInputP_pad,chainInputP_blocks] at h3
      exact h3.mono (by omega) (by simp [preCost]) (fun hq => ⟨hq,by simp [preCost]⟩)
  | succ k ih =>
      intro m hm hd v s hs
      obtain ⟨h5,hv,hin,hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
      rw [rest_succ c i m (by omega)]
      have hf := (hw.prehash i hip m (by omega) s hs.2.2.2.2.2.2.2.1).trans hs.2.2.2.2.2.2.2.2
      have H : ∀a : BitVec 256,InlineTail.Judg.GoodQ InlineTail.image (writeHash s a) (N+3*(topMax i-(m+1))+5+2)
          (C+preCost i (m+1)+(if m+1=last i then 2 else 1)) Q
          (A+preCost i (m+1)+(if m+1=last i then 2 else 1))
          (InlineTail.Judg.ccM (c.rest i (m+1) (a.extractLsb' 0 128)) (fun v => K (acc++[v]))) := by
        intro a
        have hrun := c.chk_rung hds i (m+1) hi (by omega) (by omega) (fun _ => by omega)
        obtain ⟨u,hu,hp⟩ := c.prefix_rung_step hw hc hk i (m+1) hi hip (by omega) (c.rungPc_lt i _ (by omega)) hrun acc _ _
          ((hpost a).1 (by omega))
        have ht := ih (m+1) (by omega) (by omega) _ _ hp
        exact InlineTail.Judg.GoodQ.steps' hu ht (by split <;> omega) (by omega) (fun hq => ⟨hq,by omega⟩)
      have h3 := InlineTail.Judg.GoodQ.shortHash_bind (f:=c.rest i (m+1)) (K:=fun v => K (acc++[v])) hf h5 hv
        (by rw [chainInputP_pad];exact hin) H
      rw [chainInputP_pad,chainInputP_blocks] at h3
      refine h3.mono (by omega) ?_ (fun hq => ⟨hq,?_⟩)
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega
      · unfold preCost
        by_cases he : m+1=last i
        · rw [if_pos he,if_neg (by omega),if_pos (by omega)];omega
        · rw [if_neg he,if_pos (by omega),if_pos (by omega)];omega

theorem prefix_positive_head (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54) (hip : i<51)
    (hd : c.dig i< topMax i) (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃t,Steps InlineTail.image s (4+tableJump i) (4+tableJump i) t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  have hl : last i+1=topMax i := by have := topMax_bounds i;unfold last;omega
  have hsp := c.startPc_lt hds i hi
  by_cases htab : i%3=0
  · have hrun2 := c.chk_tail hds i (c.dig i) hi htab (by omega)
    have hrp : c.rungPc i (c.dig i)+1<251927 := by
      have hb := base_lt (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
      have hl2 := last_bounds i
      unfold rungPc qb
      rw [if_pos htab]
      omega
    by_cases ht : c.dig i=last i
    · have hrun1 := c.chk_headJTerm hds i hi htab ht
      obtain ⟨t,hst,htp⟩ := c.prefix_headJTerm_step hw hc hk h0 i hi hip ht hsp hrp hrun1 hrun2 acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
    · have hrun1 := c.chk_headJ hds i hi htab (by omega)
      obtain ⟨t,hst,htp⟩ := c.prefix_headJ_step hw hc hk h0 i hi hip (by omega) hsp hrp hrun1 hrun2 acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
  · by_cases ht : c.dig i=last i
    · have hrun := c.chk_headRTerm hds i hi htab ht
      have hr : c.rungPc i (c.dig i)=c.startPc i+2 := by rw [inline_rungPc c i htab,if_pos ht]
      obtain ⟨t,hst,htp⟩ := c.prefix_headRTerm_step hw hc hk h0 i hi hip ht hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩
    · have hrun := c.chk_headR hds i hi htab (by omega)
      have hr : c.rungPc i (c.dig i)=c.startPc i+3 := by rw [inline_rungPc c i htab,if_neg ht]
      obtain ⟨t,hst,htp⟩ := c.prefix_headR_step hw hc hk h0 i hi hip (by omega) hsp hr hrun acc s hs
      exact ⟨t,hst.of_eq (by simp [tableJump,htab]) (by simp [tableJump,htab]),htp⟩

theorem prefix_chain_good (c : NCtx) (hw : c.PrefixWindows) (hc : c.ok) (hds : c.DigitsOk) {s0 : MachineState}
    (hk : ∀p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0) (i : Nat) (hi : i<54) (hip : i<51)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec InlineTail.Judg.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀v t,c.EndInv s0 i (acc++[v]) t → InlineTail.Judg.GoodQ InlineTail.image t N C Q A (K (acc++[v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    InlineTail.Judg.GoodQ InlineTail.image s (N+40) (C+chainCost i (c.dig i)) Q (A+chainCost i (c.dig i))
      (InlineTail.Judg.ccM (chainP 0 c.tree c.leaf i (c.dig i) (topMax i-c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i))
        (fun v => K (acc++[v]))) := by
  have hm := topMax_bounds i
  have hl : last i+1=topMax i := by unfold last;omega
  have hd := hds i hi
  have hsp := c.startPc_lt hds i hi
  by_cases hmax : c.dig i=topMax i
  · rw [hmax,Nat.sub_self]
    have hp : chainP 0 c.tree c.leaf i (topMax i) 0 (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i)=pure (c.val i) := rfl
    rw [hp,InlineTail.Judg.ccM_pure]
    by_cases htab : i%3=0
    · obtain ⟨t,hst,ht⟩ := c.prefix_copyN_step hw hc hk h0 i hi hip hsp
        (c.chk_copyJ hds i hi htab hmax) acc s hs
      exact InlineTail.Judg.GoodQ.steps' hst (hK _ _ ht) (by omega) (by simp [chainCost,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,tableJump,htab]⟩)
    · obtain ⟨t,hst,ht⟩ := c.prefix_copyFH_step hw hc hk h0 i hi hip hsp
        (c.inline_copy_end i htab hmax) (c.chk_copyF hds i hi htab hmax) acc s hs
      exact InlineTail.Judg.GoodQ.steps' hst (hK _ _ ht) (by omega) (by simp [chainCost,tableJump,htab])
        (fun hq => ⟨hq,by simp [chainCost,tableJump,htab]⟩)
  · have hd' : c.dig i< topMax i := by omega
    rw [chainP_rest]
    have H := c.prefix_steps_good hw hc hds hk h0 i hi hip acc K N C A Q hK (last i-c.dig i) (c.dig i) (by omega) (le_refl _)
    obtain ⟨t,hst,ht⟩ := c.prefix_positive_head hw hc hds hk h0 i hi hip hd' acc s hs
    have hj : tableJump i≤1 := by unfold tableJump;split <;> omega
    have he := chainCost_positive i (c.dig i) hd'
    exact InlineTail.Judg.GoodQ.steps' hst (H _ _ ht) (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

#print axioms prefix_chain_good
end SigGolfCandidate.T3M.Nonbinary.NCtx
