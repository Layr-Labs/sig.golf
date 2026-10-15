import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.PlaceDefs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Region

section
namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem placeOK_rest : placeOK 39156 = true := by decide +kernel
theorem cOff_nine : cOff 9 = 1716 := by decide +kernel
def fcLookB : Bool :=
  (List.range 9).all fun c =>
    ((fcList c).all fun p => decide (regBase c ≤ p.1 ∧ p.1 < regBase c + 1024)) &&
    (List.range 128).all fun i => decide (lookW (fcList c) (regBase c + 8 * i) = (plSt 0 0 i).map (fun o => some (sigBlk c + o)))
theorem fcLookB_ok : fcLookB = true := by decide +kernel
def plSt0B : Bool := (List.range 128).all fun j => (List.range 128).all fun i => decide (plSt j 0 i = plSt 0 0 i)
theorem plSt0B_ok : plSt0B = true := by decide +kernel
def plStepB : Bool :=
  (List.range 128).all fun j => (List.range 7).all fun L => (List.range 128).all fun i =>
    decide (plSt j (L + 1) i =
      if 8 * i = sibOff L (j / 2 ^ L % 2 = 1) then some (96 + 16 * L)
      else if 8 * i = sibOff L (j / 2 ^ L % 2 = 1) + 8 then some (96 + 16 * L + 8)
      else plSt j L i)
theorem plStepB_ok : plStepB = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
set_option linter.unusedSimpArgs false
theorem placeOK_fc {P c : Nat} (h : placeOK P = true) (hc : c < 9) : fcCheck P c = true := by
  have := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  exact this.1
theorem placeOK_lev {P c l : Nat} (h : placeOK P = true) (hc : c < 9) (hl : l < 7) (d : Bool) :
    levCheck P c l d = true := by
  have := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  have := List.all_eq_true.mp this.2 l (List.mem_range.mpr hl)
  simp only [Bool.and_eq_true] at this
  cases d
  · exact this.2
  · exact this.1
theorem fcLook {c i : Nat} (hc : c < 9) (hi : i < 128) :
    lookW (fcList c) (regBase c + 8 * i) = (plSt 0 0 i).map (fun o => some (sigBlk c + o)) := by
  have := List.all_eq_true.mp fcLookB_ok c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  have := List.all_eq_true.mp this.2 i (List.mem_range.mpr hi)
  simpa using this
theorem fcDst {c : Nat} (hc : c < 9) : ∀ p ∈ fcList c, regBase c ≤ p.1 ∧ p.1 < regBase c + 1024 := by
  have := List.all_eq_true.mp fcLookB_ok c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  intro p hp
  have := List.all_eq_true.mp this.1 p hp
  simpa using this
theorem plSt0 {j i : Nat} (hj : j < 128) (hi : i < 128) : plSt j 0 i = plSt 0 0 i := by
  have := List.all_eq_true.mp plSt0B_ok j (List.mem_range.mpr hj)
  have := List.all_eq_true.mp this i (List.mem_range.mpr hi)
  simpa using this
theorem plStep {j L i : Nat} (hj : j < 128) (hL : L < 7) (hi : i < 128) :
    plSt j (L + 1) i =
      if 8 * i = sibOff L (j / 2 ^ L % 2 = 1) then some (96 + 16 * L)
      else if 8 * i = sibOff L (j / 2 ^ L % 2 = 1) + 8 then some (96 + 16 * L + 8)
      else plSt j L i := by
  have := List.all_eq_true.mp plStepB_ok j (List.mem_range.mpr hj)
  have := List.all_eq_true.mp this L (List.mem_range.mpr hL)
  have := List.all_eq_true.mp this i (List.mem_range.mpr hi)
  simpa using this
theorem plSt_seven (j i : Nat) : plSt j 7 i = wSrc j i := by
  unfold plSt; rw [if_pos (Or.inr (by omega))]
theorem regBase_lt (k : Nat) (hk : k < 9) : regBase k + 1024 ≤ 0x2c40 := by unfold regBase; omega
theorem childBase_split (c : Nat) (hc : c < 9) :
    64 * fW c + fSh c + (if c = 3 ∨ c = 6 then 21 else 0) = WCT9.childBase c := by
  interval_cases c <;> decide
theorem fSh_le (c : Nat) (hc : c < 9) : fSh c + 7 ≤ 64 ∨ ((c = 3 ∨ c = 6) ∧ fSh c = 36) := by
  interval_cases c <;> decide
theorem fW_lt (c : Nat) (hc : c < 9) : fW c < 4 := by
  interval_cases c <;> decide
theorem fSh_zero (c : Nat) (hc : c < 9) (h : fHas c = false) : fSh c = 0 := by
  interval_cases c <;> simp_all [fHas, fSh]
theorem child_bits57 (a : BitVec 256) (w : Nat) :
    ((a.extractLsb' (64 * w) 64 >>> 36) >>> 21).toNat = a.toNat / 2 ^ (64 * w + 57) % 128 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, extractLsb'_256_toNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show (2 : Nat) ^ 64 = 2 ^ (36 + 21) * 2 ^ 7 by norm_num, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rfl
theorem childE_eval {c : Nat} (hc : c < 9) {N : HashOutput} {s : MachineState} (hN : OutAt s NBUF N) :
    (childE c).eval s = BitVec.ofNat 64 (WCT9.child N ⟨c, hc⟩).val := by
  have hw := hN (fW c) (fW_lt c hc)
  simp only [NBUF] at hw
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (WCT9.child N ⟨c, hc⟩).isLt; omega)]
  have e127 : (127 : Word) = 127#64 := rfl
  have hcb := childBase_split c hc
  unfold childE
  split
  · rename_i hh
    split
    · rename_i h36
      have hs : fSh c = 36 := by rcases h36 with rfl | rfl <;> rfl
      simp only [E.eval, BinOp.eval, hw, BitVec.toNat_ofNat, hs]
      rw [show (36 : Nat) % 2 ^ 64 % 64 = 36 from rfl, show (21 : Nat) % 2 ^ 64 % 64 = 21 from rfl, child_bits57]
      unfold WCT9.child
      simp only
      rw [← hcb, if_pos h36, hs]
    · rename_i h36
      simp only [E.eval, BinOp.eval, hw, BitVec.toNat_ofNat]
      have hs : fSh c + 7 ≤ 64 := (fSh_le c hc).resolve_right (fun h => h36 h.1)
      rw [Nat.mod_eq_of_lt (show fSh c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show fSh c < 64 by omega), e127,
        child_bits N (fW c) (fSh c) hs]
      unfold WCT9.child
      simp only
      rw [← hcb, if_neg h36, Nat.add_zero]
  · rename_i hh
    have h0 := fSh_zero c hc (by simpa using hh)
    simp only [E.eval, BinOp.eval, hw]
    have := child_bits N (fW c) 0 (by omega)
    simp only [BitVec.ushiftRight_zero, Nat.add_zero] at this
    rw [e127, this]
    unfold WCT9.child
    simp only
    have h36 : ¬ (c = 3 ∨ c = 6) := by rintro (rfl | rfl) <;> simp [fHas] at hh
    rw [← hcb, h0, if_neg h36]
    rfl
theorem bit_holds (j L : Nat) (hj : j < 128) (hL : L < 7) (s : MachineState) (h24 : s.getReg .x24 = BitVec.ofNat 64 j) :
    Br.holds s ⟨.ne, bitE L, .c 0, decide (j / 2 ^ L % 2 = 1)⟩ := by
  rw [br_ne_zero]
  have hv : (bitE L).eval s = (BitVec.ofNat 64 j >>> L) &&& (1 : Word) := by
    simp only [bitE, E.eval, BinOp.eval, h24, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show L < 64 by omega)]
  rw [hv]
  have e : ((BitVec.ofNat 64 j >>> L) &&& (1 : Word)).toNat = j / 2 ^ L % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (1 : Word).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      pow_one]
  have hb : j / 2 ^ L % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h1 : j / 2 ^ L % 2 = 1
  · rw [decide_eq_true h1]
    simp only [decide_eq_true_eq]
    intro h0
    have := congrArg BitVec.toNat h0
    rw [e, h1] at this
    exact absurd this (by decide)
  · rw [decide_eq_false h1]
    simp only [decide_eq_false_iff_not, not_not]
    apply BitVec.eq_of_toNat_eq
    rw [e]
    show j / 2 ^ L % 2 = 0
    omega
structure PlInv (P : Nat) (N : HashOutput) (s0 : MachineState) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (P + cOff c)
  regs : RegsExcept s0 t [.x6, .x7, .x24, .x25, .x28, .x29]
  done : ∀ k i, (hk : k < c) → (hk9 : k < 9) → i < 128 →
    t.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) =
      match wSrc (WCT9.child N ⟨k, hk9⟩).val i with
      | some o => s0.getMem (BitVec.ofNat 64 (sigBlk k + o))
      | none => 0
  frame : Frame s0 t (fun A => 0x840 ≤ A ∧ A < regBase c)
structure LvInv (P : Nat) (N : HashOutput) (s0 t : MachineState) (c : Nat) (hc : c < 9) (L : Nat)
    (u : MachineState) : Prop where
  pc : u.pc = pcOf (P + lOff c L)
  regs : RegsExcept t u [.x6, .x7, .x24, .x25, .x28, .x29]
  x24 : u.getReg .x24 = BitVec.ofNat 64 (WCT9.child N ⟨c, hc⟩).val
  reg : ∀ i, i < 128 → u.getMem (BitVec.ofNat 64 (regBase c + 8 * i)) =
    match plSt (WCT9.child N ⟨c, hc⟩).val L i with
    | some o => s0.getMem (BitVec.ofNat 64 (sigBlk c + o))
    | none => 0
  frame : Frame t u (fun A => regBase c ≤ A ∧ A < regBase c + 1024)
theorem sigBlk_lt (c : Nat) (hc : c < 9) (o : Nat) (ho : o < 208) : sigBlk c + o < 0x7000 + 16 + 1872 := by
  unfold sigBlk; omega
def RegZero (c : Nat) (t : MachineState) : Prop :=
  ∀ i, i < 128 → t.getMem (BitVec.ofNat 64 (regBase c + 8 * i)) = 0
theorem wSrc_lt (j i : Nat) : ∀ o, wSrc j i = some o → o < 208 := by
  intro o h
  unfold wSrc at h
  split_ifs at h <;> (simp only [Option.some.injEq] at h; omega)
theorem plSt_lt (j L i : Nat) : ∀ o, plSt j L i = some o → o < 208 := by
  intro o h
  unfold plSt at h
  split_ifs at h
  · exact wSrc_lt j i o h
theorem fc_spec {im : Image} (hc : NewCodeAt im) {P : Nat} {N : HashOutput}
    {s0 : MachineState} (c : Nat) (hP : fcCheck P c = true) (hc9 : c < 9) (t : MachineState)
    (hpc : t.pc = pcOf (P + cOff c))
    (hN : OutAt t NBUF N) (hz : RegZero c t)
    (hsig : ∀ o, o < 208 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o))) :
    ∃ u k cy, Steps im t k cy u ∧ cy ≤ 120 ∧ LvInv P N s0 t c hc9 0 u := by
  obtain ⟨r, hr, hb⟩ := check_some hP
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hrun, h24⟩, hbr⟩, hcy⟩ := hb
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun t hpc (by simp) (by rw [hbr]; simp)
  refine ⟨_, _, _, st, hcy, p, rg, ?_, ?_, ?_⟩
  · rw [PRes.toState_getReg, E.beq_eq h24, childE_eval hc9 hN]
  · intro i hi
    have hA : regBase c + 8 * i < 2 ^ 64 := by unfold regBase; omega
    rw [mm _ hA, plSt0 (WCT9.child N ⟨c, hc9⟩).isLt hi]
    have hl := fcLook hc9 hi
    cases hs : plSt 0 0 i with
    | none =>
      rw [hs] at hl
      rw [effMem_none hl]
      exact hz i hi
    | some o =>
      rw [hs] at hl
      rw [effMem_some hl]
      exact hsig o (plSt_lt 0 0 i o hs)
  · intro A hA hn
    rw [mm A hA]
    apply effMem_none
    apply lookW_none_of
    intro p hp he
    have := fcDst hc9 p hp
    exact hn ⟨by omega, by omega⟩
theorem lev_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 t : MachineState} (c : Nat) (hc9 : c < 9) (L : Nat) (hL : L < 7) (u : MachineState)
    (hI : LvInv P N s0 t c hc9 L u)
    (hsig : ∀ o, o < 208 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o))) :
    ∃ v k cy, Steps im u k cy v ∧ cy ≤ 12 ∧ LvInv P N s0 t c hc9 (L + 1) v := by
  set j := (WCT9.child N ⟨c, hc9⟩).val with hjdef
  have hj : j < 128 := (WCT9.child N ⟨c, hc9⟩).isLt
  obtain ⟨r, hr, hb⟩ := check_some (placeOK_lev hP hc9 hL (decide (j / 2 ^ L % 2 = 1)))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hrun, hbr⟩, hcy⟩ := hb
  have hbr' := listBeq_eq (fun _ _ => Br.beq_eq) hbr
  obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun u hI.pc (by simp) (by
    rw [hbr']; intro b hb; simp only [List.mem_singleton] at hb; subst hb
    exact bit_holds j L hj hL u hI.x24)
  have hsrc : ∀ o, o < 208 → u.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o)) := by
    intro o ho
    rw [hI.frame _ (by unfold sigBlk; omega) (by unfold sigBlk regBase; omega), hsig o ho]
  have hlu : lOff c L + 12 = lOff c (L + 1) := by unfold lOff; ring
  refine ⟨_, _, _, st, hcy, by rw [p, Nat.add_assoc, hlu], hI.regs.trans rg |>.mono (by simp), ?_, ?_, ?_⟩
  · rw [rg.get (by simp)]; exact hI.x24
  · intro i hi
    have hA : regBase c + 8 * i < 2 ^ 64 := by unfold regBase; omega
    rw [mm _ hA, plStep hj hL hi]
    unfold levList
    by_cases h1 : 8 * i = sibOff L (decide (j / 2 ^ L % 2 = 1))
    · rw [if_pos h1]
      have : lookW [(regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)) + 8, some (sigBlk c + 96 + 16 * L + 8)),
          (regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)), some (sigBlk c + 96 + 16 * L))] (regBase c + 8 * i) =
          some (some (sigBlk c + 96 + 16 * L)) := by
        rw [lookW_cons, if_neg (by omega), lookW_cons, if_pos (by omega)]
      rw [effMem_some this, show sigBlk c + 96 + 16 * L = sigBlk c + (96 + 16 * L) by ring]
      exact hsrc _ (by omega)
    · rw [if_neg h1]
      by_cases h2 : 8 * i = sibOff L (decide (j / 2 ^ L % 2 = 1)) + 8
      · rw [if_pos h2]
        have : lookW [(regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)) + 8, some (sigBlk c + 96 + 16 * L + 8)),
            (regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)), some (sigBlk c + 96 + 16 * L))] (regBase c + 8 * i) =
            some (some (sigBlk c + 96 + 16 * L + 8)) := by
          rw [lookW_cons, if_pos (by omega)]
        rw [effMem_some this, show sigBlk c + 96 + 16 * L + 8 = sigBlk c + (96 + 16 * L + 8) by ring]
        exact hsrc _ (by omega)
      · rw [if_neg h2]
        have : lookW [(regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)) + 8, some (sigBlk c + 96 + 16 * L + 8)),
            (regBase c + sibOff L (decide (j / 2 ^ L % 2 = 1)), some (sigBlk c + 96 + 16 * L))] (regBase c + 8 * i) =
            none := by
          rw [lookW_cons, if_neg (by omega), lookW_cons, if_neg (by omega)]; rfl
        rw [effMem_none this]
        exact hI.reg i hi
  · have hs : ∀ d : Bool, sibOff L d + 16 ≤ 1024 := fun d => by unfold sibOff; split <;> omega
    have F : Frame u (r.toState u) (fun A => regBase c ≤ A ∧ A < regBase c + 1024) := by
      intro A hA hn
      rw [mm A hA]
      apply effMem_none
      unfold levList
      have := hs (decide (j / 2 ^ L % 2 = 1))
      rw [lookW_cons, if_neg (fun h => hn ⟨by omega, by omega⟩), lookW_cons,
        if_neg (fun h => hn ⟨by omega, by omega⟩)]; rfl
    exact (hI.frame.trans F).mono (fun A _ h => by rcases h with h | h <;> exact h)
theorem levs_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 t : MachineState} (c : Nat) (hc9 : c < 9)
    (hsig : ∀ o, o < 208 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o))) :
    ∀ L, L ≤ 7 → ∀ u, LvInv P N s0 t c hc9 0 u → ∃ v k cy, Steps im u k cy v ∧ cy ≤ 12 * L ∧ LvInv P N s0 t c hc9 L v := by
  intro L
  induction L with
  | zero => intro _ u h; exact ⟨u, 0, 0, Steps.refl u, le_refl _, h⟩
  | succ L ih =>
    intro hL u h0
    obtain ⟨v, k, cy, sv, hcy, hv⟩ := ih (by omega) u h0
    obtain ⟨w, k', cy', sw, hcy', hw⟩ := lev_spec hc hP c hc9 L (by omega) v hv hsig
    exact ⟨w, _, _, sv.trans sw, by rw [Nat.mul_succ]; omega, hw⟩
theorem coordPl_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 : MachineState} (hN : OutAt s0 NBUF N) (hz : ∀ k i, k < 9 → i < 128 → s0.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = 0)
    (c : Nat) (hc9 : c < 9) (t : MachineState) (hI : PlInv P N s0 c t) :
    ∃ u k cy, Steps im t k cy u ∧ cy ≤ 204 ∧ PlInv P N s0 (c + 1) u := by
  have hrb := regBase_lt c hc9
  have hNt : OutAt t NBUF N := fun k hk => by
    rw [hI.frame _ (by simp only [NBUF]; omega) (by simp only [NBUF]; unfold regBase; omega)]; exact hN k hk
  have hzt : RegZero c t := fun i hi => by
    rw [hI.frame _ (by unfold regBase; omega) (by unfold regBase; omega)]
    exact hz c i hc9 hi
  have hsig : ∀ o, o < 208 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o)) :=
    fun o ho => hI.frame _ (by unfold sigBlk; omega) (by unfold sigBlk regBase; omega)
  obtain ⟨u0, k0, c0, s0', hc0, h0⟩ := fc_spec hc c (placeOK_fc hP hc9) hc9 t hI.pc hNt hzt hsig
  obtain ⟨u7, k7, c7, s7, hc7, h7⟩ := levs_spec hc hP c hc9 hsig 7 le_rfl u0 h0
  refine ⟨u7, _, _, s0'.trans s7, by omega, ?_, ?_, ?_, ?_⟩
  · rw [h7.pc]; unfold lOff; simp only [cOff]; try ring_nf
  · exact (hI.regs.trans h7.regs).mono (by simp)
  · intro k i hk hk9 hi
    by_cases hkc : k = c
    · subst hkc
      rw [h7.reg i hi, plSt_seven]
    · have hk' : k < c := by omega
      have hrk := regBase_lt k hk9
      rw [h7.frame _ (by unfold regBase; omega) (by unfold regBase; omega)]
      exact hI.done k i hk' hk9 hi
  · have := (hI.frame.trans h7.frame)
    refine this.mono (fun A _ h => ?_)
    have e : regBase (c + 1) = regBase c + 1024 := by unfold regBase; ring
    rcases h with h | h
    · exact ⟨h.1, by omega⟩
    · exact ⟨by unfold regBase at h; omega, by omega⟩
theorem place_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK P = true) {N : HashOutput}
    {s0 : MachineState} (hpc : s0.pc = pcOf P) (hN : OutAt s0 NBUF N)
    (hz : ∀ k i, k < 9 → i < 128 → s0.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = 0) :
    ∃ u k cy, Steps im s0 k cy u ∧ cy ≤ 9 * 204 ∧ PlInv P N s0 9 u := by
  have gen : ∀ c, c ≤ 9 → ∃ u k cy, Steps im s0 k cy u ∧ cy ≤ 204 * c ∧ PlInv P N s0 c u := by
    intro c
    induction c with
    | zero =>
      intro _
      refine ⟨s0, 0, 0, Steps.refl _, le_refl _, ⟨by rw [hpc]; rfl, RegsExcept.refl _ _,
        fun k i hk => absurd hk (by omega), Frame.refl _ _⟩⟩
    | succ c ih =>
      intro hc9
      obtain ⟨u, k, cy, su, hcy, hu⟩ := ih (by omega)
      obtain ⟨v, k', cy', sv, hcy', hv⟩ := coordPl_spec hc hP hN hz c (by omega) u hu
      exact ⟨v, _, _, su.trans sv, by rw [Nat.mul_succ]; omega, hv⟩
  obtain ⟨u, k, cy, su, hcy, hu⟩ := gen 9 le_rfl
  exact ⟨u, k, cy, su, by omega, hu⟩
end ClaudeWCT.W9.Machine.Expand
end

section
/-! ### C1 (FTS half-swap): the first-pass placement

The first pass (`P = 1435`) jumps from block 0 of coordinate `c` to the trampoline `F_c` at `fcAt c`, which places
the siblings of levels 0..4 at their plan slots `regBase c + Merkle.sibO l j` (plan halfword `authBase j l` from the
table at `PLAN`, row `j % 64`) and returns to the unchanged level-5 block; levels 5 and 6 are the old blocks. -/
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
set_option linter.unusedSimpArgs false
def fcAt (c : Nat) : Nat := 33285 + 91 * c
def rowE : E := .bin .sll (.bin .and (.reg .x24) (.c 63#64)) (.c 4#64)
def hwF (l : Nat) : E :=
  .un (.ld .hu (2 * (l % 4))) (.ld (.bin .add rowE (.c (BitVec.ofNat 64 (PLAN + 8 * (l / 4))))))
def fDst (c : Nat) (d : Bool) : Nat := regBase c + 128 + (if d then 0 else 48)
def fSrc (c l : Nat) : Nat := sigBlk c + 96 + 16 * l
def fLevRes (c l : Nat) (d : Bool) : PRes :=
  ⟨⟨(((RegFile.init.set .x6 (.ld (.c (BitVec.ofNat 64 (fSrc c l))))).set .x7
        (.ld (.c (BitVec.ofNat 64 (fSrc c l + 8))))).set .x28 (.c (BitVec.ofNat 64 (fSrc c l)))).set .x29
        (.bin .add (hwF l) (.c (BitVec.ofNat 64 (fDst c d)))),
      [(⟨some (hwF l), BitVec.ofNat 64 (fDst c d + 8)⟩, .ld (.c (BitVec.ofNat 64 (fSrc c l + 8)))),
        (⟨some (hwF l), BitVec.ofNat 64 (fDst c d)⟩, .ld (.c (BitVec.ofNat 64 (fSrc c l))))],
      [.valid ⟨some (hwF l), BitVec.ofNat 64 (fDst c d + 8)⟩ 8, .valid ⟨some (hwF l), BitVec.ofNat 64 (fDst c d)⟩ 8,
        .align8 rowE, .valid ⟨some rowE, BitVec.ofNat 64 (PLAN + 2 * l)⟩ 2]⟩,
    pcOf (fcAt c + 18 * (l + 1)), false, (if d then 17 else 18), (if d then 17 else 18), [⟨.ne, bitE l, .c 0, d⟩],
    none⟩
def fJmp (P c : Nat) : Option PRes := pathAux pcfg expLook [pcOf (fcAt c)] 30 (pcOf (P + lOff c 0)) [] (σK []) []
def fRet (P c : Nat) : Option PRes :=
  pathAux pcfg expLook [pcOf (P + lOff c 5)] 30 (pcOf (fcAt c + 90)) [] (σK []) []
def fLev (c l : Nat) (d : Bool) : Option PRes :=
  pathAux pcfg expLook [pcOf (fcAt c + 18 * (l + 1))] 30 (pcOf (fcAt c + 18 * l)) [.br d] (σK []) []
def jmpRes (n : Nat) : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf n, false, 1, 1, [], none⟩
def fcOK1 (P c : Nat) : Bool :=
  optBeq (fJmp P c) (jmpRes (fcAt c)) && optBeq (fRet P c) (jmpRes (P + lOff c 5)) &&
    (List.range 5).all fun l => optBeq (fLev c l true) (fLevRes c l true) && optBeq (fLev c l false) (fLevRes c l false)
def placeOK1 (P : Nat) : Bool :=
  (List.range 9).all fun c => fcCheck P c && fcOK1 P c &&
    (levCheck P c 5 true && levCheck P c 5 false && levCheck P c 6 true && levCheck P c 6 false)
set_option maxRecDepth 100000 in
theorem placeOK1_init : placeOK1 1435 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem planHW1_ok : ∀ r < 64, ∀ l < 5,
    LoadKind.hu.fromWord (bytesToWordLE ((planBytes.drop (8 * (2 * r + l / 4))).take 8)) (2 * (l % 4)) =
      BitVec.ofNat 64 (ClaudeWCT.W9.T3M.authBase r l) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem authBase_facts : ∀ j < 128, ∀ l < 5,
    ClaudeWCT.W9.T3M.authBase j l % 16 = 0 ∧ ClaudeWCT.W9.T3M.authBase j l ≤ 256 := by
  decide +kernel
theorem authBase_mod64 (j l : Nat) : ClaudeWCT.W9.T3M.authBase (j % 64) l = ClaudeWCT.W9.T3M.authBase j l := by
  unfold ClaudeWCT.W9.T3M.authBase; rw [Nat.mod_mod_of_dvd _ (by norm_num : 32 ∣ 64)]
set_option maxRecDepth 100000 in
theorem rowE_tab : ∀ j < 128,
    BinOp.eval .sll (BinOp.eval .and (BitVec.ofNat 64 j) 63#64) 4#64 = BitVec.ofNat 64 (16 * (j % 64)) := by
  decide +kernel
theorem rowE_eval {s : MachineState} {j : Nat} (hj : j < 128) (h24 : s.getReg .x24 = BitVec.ofNat 64 j) :
    rowE.eval s = BitVec.ofNat 64 (16 * (j % 64)) := by
  show BinOp.eval .sll (BinOp.eval .and (s.getReg .x24) 63#64) 4#64 = _
  rw [h24]; exact rowE_tab j hj
theorem hwF_eval {s : MachineState} {j : Nat} (hj : j < 128) (h24 : s.getReg .x24 = BitVec.ofNat 64 j)
    (hp : PlanAt s) (l : Nat) (hl : l < 5) :
    (hwF l).eval s = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.authBase j l) := by
  have hr : j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hw : s.getMem (BinOp.eval .add (rowE.eval s) (BitVec.ofNat 64 (PLAN + 8 * (l / 4)))) =
      bytesToWordLE ((planBytes.drop (8 * (2 * (j % 64) + l / 4))).take 8) := by
    rw [rowE_eval hj h24]
    simp only [BinOp.eval, ofNat_add_ofNat]
    rw [show 16 * (j % 64) + (PLAN + 8 * (l / 4)) = PLAN + 8 * (2 * (j % 64) + l / 4) by ring]
    exact hp _ (by omega)
  simp only [hwF, E.eval, UnOp.eval]
  rw [hw, planHW1_ok (j % 64) hr l hl, authBase_mod64]
theorem placeOK1_parts {P c : Nat} (h : placeOK1 P = true) (hc : c < 9) :
    fcCheck P c = true ∧ fcOK1 P c = true ∧ (∀ d, levCheck P c 5 d = true) ∧ (∀ d, levCheck P c 6 d = true) := by
  have := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true] at this
  obtain ⟨⟨h1, h2⟩, ⟨⟨h3, h4⟩, h5⟩, h6⟩ := this
  exact ⟨h1, h2, fun d => by cases d; exact h4; exact h3, fun d => by cases d; exact h6; exact h5⟩
theorem jmp_spec {im : Image} (hc : NewCodeAt im) {stops : List Word} {fuel m n : Nat}
    (h : pathAux pcfg expLook stops fuel (pcOf m) [] (σK []) [] = some (jmpRes n)) (s : MachineState)
    (hpc : s.pc = pcOf m) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf n ∧ (∀ r, t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  obtain ⟨hs, -⟩ := pathRun_sound h (expLook_ok hc) s hpc (by simp) (by simp [jmpRes]) (by simp [jmpRes])
  exact ⟨_, hs, PRes.toState_pc _ s rfl, fun r => by rw [PRes.toState_getReg]; exact RegFile.init_get_eval s r,
    fun A => by rw [PRes.toState_getMem]; rfl⟩
theorem flev_spec {im : Image} (hc : NewCodeAt im) {P c : Nat} (hok : fcOK1 P c = true) (hc9 : c < 9)
    (l : Nat) (hl : l < 5) (s : MachineState) (hpc : s.pc = pcOf (fcAt c + 18 * l)) {j : Nat} (hj : j < 128)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 j) (hp : PlanAt s) :
    ∃ t cy, Steps im s cy cy t ∧ cy ≤ 18 ∧ t.pc = pcOf (fcAt c + 18 * (l + 1)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
        if A = regBase c + Merkle.sibO l j + 8 then s.getMem (BitVec.ofNat 64 (fSrc c l + 8))
        else if A = regBase c + Merkle.sibO l j then s.getMem (BitVec.ofNat 64 (fSrc c l))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hrun : ∀ d, fLev c l d = some (fLevRes c l d) := by
    unfold fcOK1 at hok
    simp only [Bool.and_eq_true] at hok
    have := List.all_eq_true.mp hok.2 l (List.mem_range.mpr hl)
    simp only [Bool.and_eq_true] at this
    intro d; cases d
    · exact optBeq_eq this.2
    · exact optBeq_eq this.1
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hrb : regBase c + 1024 ≤ 0x2c40 := by unfold regBase; omega
  obtain ⟨ha16, ha256⟩ := authBase_facts j hj l hl
  have hdst := hwF_eval hj h24 hp l hl
  have hrow := rowE_eval hj h24
  have hjm : j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  set d := decide (j / 2 ^ l % 2 = 1) with hd
  have hsib : ClaudeWCT.W9.T3M.authBase j l + fDst c d = regBase c + Merkle.sibO l j := by
    have hb : j / 2 ^ l % 2 < 2 := Nat.mod_lt _ (by decide)
    unfold fDst Merkle.sibO Merkle.blkO Merkle.bitAt
    rw [if_pos hl]
    by_cases hbit : j / 2 ^ l % 2 = 1
    · rw [hd, decide_eq_true hbit, if_pos rfl, hbit]; omega
    · rw [hd, decide_eq_false hbit, if_neg (by simp)]; omega
  have hfd : fDst c d ≤ regBase c + 176 := by unfold fDst; split <;> omega
  have hfdv : fDst c d = regBase c + 128 ∨ fDst c d = regBase c + 176 := by unfold fDst; split <;> simp
  have hrbm : regBase c % 64 = 0 := by unfold regBase; omega
  obtain ⟨hs, -⟩ := pathRun_sound (hrun d) (expLook_ok hc) s hpc (by simp) (by
    intro o ho
    simp only [fLevRes, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hdst, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [hM]; rcases hfdv with h | h <;> rw [h] <;> omega
    · simp only [Oblig.holds, Addr.eval, hdst, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      rw [hM]; rcases hfdv with h | h <;> rw [h] <;> omega
    · simp only [Oblig.holds, hrow, BitVec.toNat_ofNat]; omega
    · simp only [Oblig.holds, Addr.eval, hrow, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      unfold PLAN; omega) (by
    intro b hb
    simp only [fLevRes, List.mem_singleton] at hb
    subst hb
    exact bit_holds j l hj (by omega) s h24)
  refine ⟨_, _, hs, by simp only [fLevRes]; split <;> omega, PRes.toState_pc _ s rfl, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h6, h7, h28, h29⟩ := hr
    rw [PRes.toState_getReg]
    simp only [fLevRes]
    rw [RegFile.get_set_ne _ _ h29, RegFile.get_set_ne _ _ h28, RegFile.get_set_ne _ _ h7, RegFile.get_set_ne _ _ h6,
      RegFile.init_get_eval]
  · intro A hA
    rw [PRes.toState_getMem]
    simp only [fLevRes, memEval_cons, memEval_nil, Addr.eval, E.eval, hdst, ofNat_add_ofNat]
    have hbig : ClaudeWCT.W9.T3M.authBase j l + (fDst c d + 8) < 2 ^ 64 := by unfold regBase at hfd; omega
    have hbig' : ClaudeWCT.W9.T3M.authBase j l + fDst c d < 2 ^ 64 := by omega
    rw [show ClaudeWCT.W9.T3M.authBase j l + (fDst c d + 8) = regBase c + Merkle.sibO l j + 8 by omega] at hbig ⊢
    rw [hsib] at hbig' ⊢
    by_cases h1 : A = regBase c + Merkle.sibO l j + 8
    · subst h1; simp [fSrc]
    · rw [if_neg (fun h => h1 ((ofNat_inj hA hbig).mp h)), if_neg h1]
      by_cases h2 : A = regBase c + Merkle.sibO l j
      · subst h2; simp [fSrc]
      · rw [if_neg (fun h => h2 ((ofNat_inj hA hbig').mp h)), if_neg h2]
/-- The first-pass region state after `L` of the 7 sibling placements (levels `0 .. L - 1`). -/
def plSt1 (j L i : Nat) : Option Nat :=
  if 56 ≤ i then wSrc j i
  else match cellLev j (i / 2) with
    | some l => if l < L then some (96 + 16 * l + 8 * (i % 2)) else none
    | none => none
def plSt1B : Bool :=
  (List.range 128).all fun j => (List.range 128).all fun i => decide (plSt1 j 0 i = plSt 0 0 i) &&
    (List.range 7).all fun L => decide (plSt1 j (L + 1) i =
      if 8 * i = Merkle.sibO L j then some (96 + 16 * L)
      else if 8 * i = Merkle.sibO L j + 8 then some (96 + 16 * L + 8)
      else plSt1 j L i)
set_option maxRecDepth 100000 in
theorem plSt1B_ok : plSt1B = true := by decide +kernel
theorem plSt1_zero {j i : Nat} (hj : j < 128) (hi : i < 128) : plSt1 j 0 i = plSt 0 0 i := by
  have := List.all_eq_true.mp plSt1B_ok j (List.mem_range.mpr hj)
  have := List.all_eq_true.mp this i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1
theorem plStep1 {j L i : Nat} (hj : j < 128) (hL : L < 7) (hi : i < 128) :
    plSt1 j (L + 1) i =
      if 8 * i = Merkle.sibO L j then some (96 + 16 * L)
      else if 8 * i = Merkle.sibO L j + 8 then some (96 + 16 * L + 8)
      else plSt1 j L i := by
  have := List.all_eq_true.mp plSt1B_ok j (List.mem_range.mpr hj)
  have := List.all_eq_true.mp this i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  have := List.all_eq_true.mp this.2 L (List.mem_range.mpr hL)
  simpa using this
theorem sibOff_late (L j : Nat) (hL : 5 ≤ L) (hL7 : L < 7) :
    sibOff L (decide (j / 2 ^ L % 2 = 1)) = Merkle.sibO L j := by
  have hb : j / 2 ^ L % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold sibOff Merkle.sibO Merkle.blkO Merkle.bitAt
  rw [if_neg (show ¬ L < 5 by omega)]
  by_cases hbit : j / 2 ^ L % 2 = 1
  · rw [if_pos (show decide (j / 2 ^ L % 2 = 1) = true by simp [hbit]), hbit]
  · rw [if_neg (show ¬ decide (j / 2 ^ L % 2 = 1) = true by simp [hbit])]; omega
structure LvInv1 (N : HashOutput) (s0 t : MachineState) (c : Nat) (hc : c < 9) (L : Nat) (u : MachineState) :
    Prop where
  regs : RegsExcept t u [.x6, .x7, .x24, .x25, .x28, .x29]
  x24 : u.getReg .x24 = BitVec.ofNat 64 (WCT9.child N ⟨c, hc⟩).val
  reg : ∀ i, i < 128 → u.getMem (BitVec.ofNat 64 (regBase c + 8 * i)) =
    match plSt1 (WCT9.child N ⟨c, hc⟩).val L i with
    | some o => s0.getMem (BitVec.ofNat 64 (sigBlk c + o))
    | none => 0
  frame : Frame t u (fun A => regBase c ≤ A ∧ A < regBase c + 1024)
/-- One sibling placement step: the words of sibling `L` land on its slot `regBase c + sibO L j`. -/
theorem LvInv1.step {N : HashOutput} {s0 t : MachineState} {c : Nat} {hc : c < 9} {L : Nat} {u v : MachineState}
    (hI : LvInv1 N s0 t c hc L u) (hL : L < 7)
    (hsig : ∀ o, o < 208 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o)))
    (hr : RegsExcept u v [.x6, .x7, .x28, .x29])
    (hm : ∀ A, A < 2 ^ 64 → v.getMem (BitVec.ofNat 64 A) =
      if A = regBase c + Merkle.sibO L (WCT9.child N ⟨c, hc⟩).val + 8 then
        u.getMem (BitVec.ofNat 64 (sigBlk c + 96 + 16 * L + 8))
      else if A = regBase c + Merkle.sibO L (WCT9.child N ⟨c, hc⟩).val then
        u.getMem (BitVec.ofNat 64 (sigBlk c + 96 + 16 * L))
      else u.getMem (BitVec.ofNat 64 A))
    (hsb : Merkle.sibO L (WCT9.child N ⟨c, hc⟩).val + 16 ≤ 1024) :
    LvInv1 N s0 t c hc (L + 1) v := by
  set j := (WCT9.child N ⟨c, hc⟩).val with hjdef
  have hj : j < 128 := (WCT9.child N ⟨c, hc⟩).isLt
  have hrb : regBase c + 1024 ≤ 0x2c40 := by unfold regBase; omega
  have hsrc : ∀ o, o < 208 → u.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o)) := by
    intro o ho
    rw [hI.frame _ (by unfold sigBlk; omega) (by unfold sigBlk regBase; omega), hsig o ho]
  refine ⟨hI.regs.trans hr |>.mono (by simp), by rw [hr.get (by simp)]; exact hI.x24, fun i hi => ?_, ?_⟩
  · have hA : regBase c + 8 * i < 2 ^ 64 := by unfold regBase; omega
    rw [hm _ hA, plStep1 hj hL hi]
    by_cases h1 : 8 * i = Merkle.sibO L j
    · rw [if_neg (by omega), if_pos (by omega), if_pos h1, show sigBlk c + 96 + 16 * L = sigBlk c + (96 + 16 * L) by ring]
      exact hsrc _ (by omega)
    · rw [if_neg h1]
      by_cases h2 : 8 * i = Merkle.sibO L j + 8
      · rw [if_pos (by omega), if_pos h2,
          show sigBlk c + 96 + 16 * L + 8 = sigBlk c + (96 + 16 * L + 8) by ring]
        exact hsrc _ (by omega)
      · rw [if_neg (by omega), if_neg (by omega), if_neg h2]
        exact hI.reg i hi
  · have F : Frame u v (fun A => regBase c ≤ A ∧ A < regBase c + 1024) := by
      intro A hA hn
      rw [hm A hA, if_neg (fun h => hn ⟨by omega, by omega⟩), if_neg (fun h => hn ⟨by omega, by omega⟩)]
    exact (hI.frame.trans F).mono (fun A _ h => by rcases h with h | h <;> exact h)
structure PlInv1 (P : Nat) (N : HashOutput) (s0 : MachineState) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (P + cOff c)
  regs : RegsExcept s0 t [.x6, .x7, .x24, .x25, .x28, .x29]
  done : ∀ k i, (hk : k < c) → (hk9 : k < 9) → i < 128 →
    t.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) =
      match plSt1 (WCT9.child N ⟨k, hk9⟩).val 7 i with
      | some o => s0.getMem (BitVec.ofNat 64 (sigBlk k + o))
      | none => 0
  frame : Frame s0 t (fun A => 0x840 ≤ A ∧ A < regBase c)
  plan : PlanAt t
theorem sibO_bound (j L : Nat) (hj : j < 128) (hL : L < 7) : Merkle.sibO L j + 16 ≤ 1024 := by
  have := (cellLev_sib_all j hj L hL).2.2; omega
theorem coordPl1_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK1 P = true) {N : HashOutput}
    {s0 : MachineState} (hN : OutAt s0 NBUF N)
    (hz : ∀ k i, k < 9 → i < 128 → s0.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = 0)
    (c : Nat) (hc9 : c < 9) (t : MachineState) (hI : PlInv1 P N s0 c t) :
    ∃ u k cy, Steps im t k cy u ∧ cy ≤ 236 ∧ PlInv1 P N s0 (c + 1) u := by
  obtain ⟨hfc, hok, hl5, hl6⟩ := placeOK1_parts hP hc9
  have hrb := regBase_lt c hc9
  have hNt : OutAt t NBUF N := fun k hk => by
    rw [hI.frame _ (by simp only [NBUF]; omega) (by simp only [NBUF]; unfold regBase; omega)]; exact hN k hk
  have hzt : RegZero c t := fun i hi => by
    rw [hI.frame _ (by unfold regBase; omega) (by unfold regBase; omega)]
    exact hz c i hc9 hi
  have hsig : ∀ o, o < 208 → t.getMem (BitVec.ofNat 64 (sigBlk c + o)) = s0.getMem (BitVec.ofNat 64 (sigBlk c + o)) :=
    fun o ho => hI.frame _ (by unfold sigBlk; omega) (by unfold sigBlk regBase; omega)
  set j := (WCT9.child N ⟨c, hc9⟩).val with hjdef
  have hj : j < 128 := (WCT9.child N ⟨c, hc9⟩).isLt
  -- the unchanged fc block (chain values, leaf slots)
  obtain ⟨u0, k0, c0, s0', hc0, h0⟩ := fc_spec hc c hfc hc9 t hI.pc hNt hzt hsig
  have I0 : LvInv1 N s0 t c hc9 0 u0 :=
    ⟨h0.regs, h0.x24, fun i hi => by rw [h0.reg i hi, plSt0 hj hi, plSt1_zero hj hi], h0.frame⟩
  have hplan : ∀ {u : MachineState}, Frame t u (fun A => regBase c ≤ A ∧ A < regBase c + 1024) → PlanAt u :=
    fun {u} hf k hk => by
      rw [hf _ (by unfold PLAN; omega) (by unfold PLAN; omega)]
      exact hI.plan k hk
  -- the jump to F_c
  have hj1 : fJmp P c = some (jmpRes (fcAt c)) :=
    optBeq_eq (by unfold fcOK1 at hok; simp only [Bool.and_eq_true] at hok; exact hok.1.1)
  obtain ⟨u1, s1, p1, r1, m1⟩ := jmp_spec hc hj1 u0 h0.pc
  have I1 : LvInv1 N s0 t c hc9 0 u1 :=
    ⟨h0.regs.trans (show RegsExcept u0 u1 [] from fun r _ => r1 r) |>.mono (by simp), by rw [r1]; exact I0.x24,
      fun i hi => by rw [m1]; exact I0.reg i hi,
      (I0.frame.trans (show Frame u0 u1 (fun _ => False) from fun A _ _ => m1 _)).mono (fun A _ h => by
        rcases h with h | h; exact h; exact h.elim)⟩
  -- the five plan levels of F_c
  have gen : ∀ l, l ≤ 5 → ∃ v k cy, Steps im u1 k cy v ∧ cy ≤ 18 * l ∧ v.pc = pcOf (fcAt c + 18 * l) ∧
      LvInv1 N s0 t c hc9 l v := by
    intro l
    induction l with
    | zero => intro _; exact ⟨u1, 0, 0, Steps.refl _, le_refl _, by rw [p1, Nat.mul_zero, Nat.add_zero], I1⟩
    | succ l ih =>
      intro hl
      obtain ⟨v, k, cy, sv, hcy, pv, Iv⟩ := ih (by omega)
      obtain ⟨w, cw, sw, hcw, pw, rw', mw⟩ := flev_spec hc hok hc9 l (by omega) v pv hj Iv.x24 (hplan Iv.frame)
      refine ⟨w, _, _, sv.trans sw, by rw [Nat.mul_succ]; omega, pw, Iv.step (by omega) hsig rw' ?_ (sibO_bound j l hj (by omega))⟩
      intro A hA
      rw [mw A hA]
      unfold fSrc; rfl
  obtain ⟨v5, k5, c5, s5, hc5, p5, I5⟩ := gen 5 le_rfl
  -- the return jump
  have hj2 : fRet P c = some (jmpRes (P + lOff c 5)) :=
    optBeq_eq (by unfold fcOK1 at hok; simp only [Bool.and_eq_true] at hok; exact hok.1.2)
  obtain ⟨u6, s6, p6, r6, m6⟩ := jmp_spec hc hj2 v5 p5
  have I6 : LvInv1 N s0 t c hc9 5 u6 :=
    ⟨I5.regs.trans (show RegsExcept v5 u6 [] from fun r _ => r6 r) |>.mono (by simp), by rw [r6]; exact I5.x24,
      fun i hi => by rw [m6]; exact I5.reg i hi,
      (I5.frame.trans (show Frame v5 u6 (fun _ => False) from fun A _ _ => m6 _)).mono (fun A _ h => by
        rcases h with h | h; exact h; exact h.elim)⟩
  -- the unchanged blocks of levels 5 and 6
  have lev : ∀ L, (L = 5 ∨ L = 6) → (∀ d, levCheck P c L d = true) → ∀ u, u.pc = pcOf (P + lOff c L) →
      LvInv1 N s0 t c hc9 L u → ∃ v k cy, Steps im u k cy v ∧ cy ≤ 12 ∧ v.pc = pcOf (P + lOff c (L + 1)) ∧
        LvInv1 N s0 t c hc9 (L + 1) v := by
    intro L hL hlev u hpu hIu
    obtain ⟨r, hr, hb⟩ := check_some (hlev (decide (j / 2 ^ L % 2 = 1)))
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hrun, hbr⟩, hcy⟩ := hb
    have hbr' := listBeq_eq (fun _ _ => Br.beq_eq) hbr
    obtain ⟨st, p, rg, mm⟩ := runB_spec hc hr hrun u hpu (by simp) (by
      rw [hbr']; intro b hb; simp only [List.mem_singleton] at hb; subst hb
      exact bit_holds j L hj (by omega) u hIu.x24)
    have hlu : lOff c L + 12 = lOff c (L + 1) := by unfold lOff; ring
    have hso := sibOff_late L j (by omega) (by omega)
    refine ⟨_, _, _, st, hcy, by rw [p, Nat.add_assoc, hlu], hIu.step (by omega) hsig rg ?_ (sibO_bound j L hj (by omega))⟩
    intro A hA
    rw [mm A hA]
    unfold levList
    rw [hso]
    by_cases h1 : A = regBase c + Merkle.sibO L j + 8
    · rw [if_pos h1, effMem_some (by rw [lookW_cons, if_pos h1.symm])]
    · rw [if_neg h1]
      by_cases h2 : A = regBase c + Merkle.sibO L j
      · rw [if_pos h2, effMem_some (by rw [lookW_cons, if_neg (fun h => h1 h.symm), lookW_cons, if_pos h2.symm])]
      · rw [if_neg h2, effMem_none (by rw [lookW_cons, if_neg (fun h => h1 h.symm), lookW_cons,
          if_neg (fun h => h2 h.symm)]; rfl)]
  have hp6 : u6.pc = pcOf (P + lOff c 5) := p6
  obtain ⟨u7, k7, c7, s7, hc7, p7, I7⟩ := lev 5 (Or.inl rfl) hl5 u6 hp6 I6
  obtain ⟨u8, k8, c8, s8, hc8, p8, I8⟩ := lev 6 (Or.inr rfl) hl6 u7 p7 I7
  refine ⟨u8, _, _, s0'.trans (s1.trans (s5.trans (s6.trans (s7.trans s8)))), by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p8]; unfold lOff; simp only [cOff]; try ring_nf
  · exact (hI.regs.trans I8.regs).mono (by simp)
  · intro k i hk hk9 hi
    by_cases hkc : k = c
    · subst hkc
      exact I8.reg i hi
    · have hk' : k < c := by omega
      have hrk := regBase_lt k hk9
      rw [I8.frame _ (by unfold regBase; omega) (by unfold regBase; omega)]
      exact hI.done k i hk' hk9 hi
  · have := (hI.frame.trans I8.frame)
    refine this.mono (fun A _ h => ?_)
    have e : regBase (c + 1) = regBase c + 1024 := by unfold regBase; ring
    rcases h with h | h
    · exact ⟨h.1, by omega⟩
    · exact ⟨by unfold regBase at h; omega, by omega⟩
  · exact hplan I8.frame
theorem place1_spec {im : Image} (hc : NewCodeAt im) {P : Nat} (hP : placeOK1 P = true) {N : HashOutput}
    {s0 : MachineState} (hpc : s0.pc = pcOf P) (hN : OutAt s0 NBUF N)
    (hz : ∀ k i, k < 9 → i < 128 → s0.getMem (BitVec.ofNat 64 (regBase k + 8 * i)) = 0) (hp : PlanAt s0) :
    ∃ u k cy, Steps im s0 k cy u ∧ cy ≤ 9 * 236 ∧ PlInv1 P N s0 9 u := by
  have gen : ∀ c, c ≤ 9 → ∃ u k cy, Steps im s0 k cy u ∧ cy ≤ 236 * c ∧ PlInv1 P N s0 c u := by
    intro c
    induction c with
    | zero =>
      intro _
      refine ⟨s0, 0, 0, Steps.refl _, le_refl _, ⟨by rw [hpc]; rfl, RegsExcept.refl _ _,
        fun k i hk => absurd hk (by omega), Frame.refl _ _, hp⟩⟩
    | succ c ih =>
      intro hc9
      obtain ⟨u, k, cy, su, hcy, hu⟩ := ih (by omega)
      obtain ⟨v, k', cy', sv, hcy', hv⟩ := coordPl1_spec hc hP hN hz c (by omega) u hu
      exact ⟨v, _, _, su.trans sv, by rw [Nat.mul_succ]; omega, hv⟩
  obtain ⟨u, k, cy, su, hcy, hu⟩ := gen 9 le_rfl
  exact ⟨u, k, cy, su, by omega, hu⟩
end ClaudeWCT.W9.Machine.Expand
end
