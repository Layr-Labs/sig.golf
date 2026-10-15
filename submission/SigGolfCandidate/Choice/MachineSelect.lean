import SigGolfCandidate.Rv
import SigGolfCandidate.T3M.MemBase
import SigGolfCandidate.Choice.Selector

namespace SigGolfCandidate.Choice.MachineSelect
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Byte-load form of the accepted blocked-quarter test. -/
theorem byte_gate (low : BitVec 128) :
    BitVec.ult ((RiscvZkvm.Rv64.extractByte (low.extractLsb' 64 64) 7).zeroExtend 64) 64#64 =
      decide (Selector.group low = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ult, decide_eq_true_eq, Selector.group_zero_iff,
    RiscvZkvm.Rv64.extractByte, BitVec.zeroExtend_eq_setWidth,
    BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hl := low.isLt
  norm_num at *
  omega

-- The low and high loads fall through to separate four-word continuations.
-- p+1 forces low at p+4; otherwise p+3 chooses low or high at p+10.
def head : List (BitVec 32) := [0xf64183, 0xb1e663]
def choose : List (BitVec 32) := [0x52803183, 0x19e63]
def readLow : List (BitVec 32) := [0x863883, 0x63803]
def readHigh : List (BitVec 32) := [0x1863883, 0x1063803]
def words : List (BitVec 32) := head ++ choose ++ readLow ++ readHigh
sym_block headBase := symRun {noAlias := true} head (pcOf 1069) 200
sym_block chooseBase := symRun {noAlias := true} choose (pcOf 1072) 200
sym_block lowBase := symRun {noAlias := true} readLow (pcOf 1074) 200
sym_block highBase := symRun {noAlias := true} readHigh (pcOf 1076) 200

def headRes (p : Word) : Result :=
  {headBase.res with pc := (E.ite .ltu
    (.un (.ld .bu 7) (.ld (.bin .add (.reg .x12) (.c 8)))) (.reg .x11)
    (.c (p + 4 + 12)) (.c (p + 4 + 4)))}
def chooseRes (p : Word) : Result :=
  {chooseBase.res with pc := (E.ite .ne (.ld (.c 1320)) (.c 0)
    (.c (p + 4 + 28)) (.c (p + 4 + 4)))}
def lowRes (p : Word) : Result := {lowBase.res with pc := .c (p + 4 + 4)}
def highRes (p : Word) : Result := {highBase.res with pc := .c (p + 4 + 4)}
theorem head_run (p : Word) :
    symRun {noAlias := true} head p 200 = some (headRes p) := by rfl
theorem choose_run (p : Word) :
    symRun {noAlias := true} choose p 200 = some (chooseRes p) := by rfl
theorem low_run (p : Word) :
    symRun {noAlias := true} readLow p 200 = some (lowRes p) := by rfl
theorem high_run (p : Word) :
    symRun {noAlias := true} readHigh p 200 = some (highRes p) := by rfl

/-- Four selector instructions suffice when forced low; six otherwise.
The two result PCs enter separate copies of the same terminal continuation.
Every 64-bit hint is covered, with no witness-controlled pointer arithmetic. -/
theorem select_spec {image : Image} (s : MachineState) (a : BitVec 256)
    (hint : Word) (d p : Nat)
    (hpc : s.pc = pcOf p)
    (hc0 : CodeAt image (pcOf p) head)
    (hc2 : CodeAt image (pcOf (p+2)) choose)
    (hc4 : CodeAt image (pcOf (p+4)) readLow)
    (hc10 : CodeAt image (pcOf (p+10)) readHigh)
    (h11 : s.getReg .x11 = 64#64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (hh : s.getMem 1320#64 = hint)
    (hlo : DigAt s d (a.extractLsb' 0 128))
    (hhi : DigAt s (d+16) (a.extractLsb' 128 128)) :
    ∃ k t, Steps image s k k t ∧ k ≤ 6 ∧ t.pc =
      (if Selector.group (a.extractLsb' 0 128) = 0 ∨ hint = 0 then pcOf (p+6) else pcOf (p+12)) ∧
      t.getReg .x16 = (Selector.branchRead (Selector.splitEquiv a) hint).extractLsb' 0 64 ∧
      t.getReg .x17 = (Selector.branchRead (Selector.splitEquiv a) hint).extractLsb' 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x3,.x12,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  have hm0 : s.getMem (s.getReg .x12) = (a.extractLsb' 0 128).extractLsb' 0 64 := by
    rw [h12]; exact hlo.1
  have hm1 : s.getMem (s.getReg .x12 + 8#64) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
    rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hlo.2
  have hm2 : s.getMem (s.getReg .x12 + 16#64) = (a.extractLsb' 128 128).extractLsb' 0 64 := by
    rw [h12, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; exact hhi.1
  have hm3 : s.getMem (s.getReg .x12 + 24#64) = (a.extractLsb' 128 128).extractLsb' 64 64 := by
    rw [h12, show (24#64 : Word) = BitVec.ofNat 64 24 from rfl, ofNat_add_ofNat]
    simpa [Nat.add_assoc] using hhi.2
  have ho : ∀ o ∈ headBase.res.st.obl, o.holds s := by
    simp [headBase.res, rv_simp, h12, accessValid_iff, MEMORY_BYTES, hd.1]
    omega
  have es := symRun_sound (head_run (pcOf p)) hc0 s hpc ((Oblig.all_iff _ _).mpr ho)
  let u := (headRes (pcOf p)).toState s
  have ru : RegsExcept s u [.x3] := by
    intro r hr; cases r <;> simp_all [u, headRes, headBase.res, rv_simp] <;> rfl
  have fu : Frame s u (fun _ => False) := by
    intro A _ _; simp [u, headRes, headBase.res, rv_simp]
  have pu : u.pc = if Selector.group (a.extractLsb' 0 128) = 0 then
      pcOf (p+4) else pcOf (p+2) := by
    simp only [u, headRes, headBase.res, rv_simp, hm1, h11, byte_gate]
    by_cases hg : Selector.group (a.extractLsb' 0 128) = 0
    all_goals simp [hg, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  have h12u : u.getReg .x12 = BitVec.ofNat 64 d := (ru.get (by decide)).trans h12
  by_cases hg : Selector.group (a.extractLsb' 0 128) = 0
  · rw [if_pos hg] at pu
    have el := symRun_sound (low_run (pcOf (p+4))) hc4 u pu (by
      simp [lowRes, lowBase.res, rv_simp, h12u, accessValid_iff, MEMORY_BYTES]; omega)
    let t := (lowRes (pcOf (p+4))).toState u
    have rt : RegsExcept u t [.x16,.x17] := by
      intro r hr; cases r <;> simp_all [t, lowRes, lowBase.res, rv_simp] <;> rfl
    have ft : Frame u t (fun _ => False) := by
      intro A _ _; simp [t, lowRes, lowBase.res, rv_simp]
    refine ⟨4,t,es.trans el,by omega,?_,?_,?_,?_,
      (ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · simp [t, lowRes, lowBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.add_assoc, Nat.mul_add, hg]
    · simpa [t, u, lowRes, lowBase.res, headRes, headBase.res, rv_simp,
        Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm0
    · simpa [t, u, lowRes, lowBase.res, headRes, headBase.res, rv_simp,
        Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm1
    · exact (rt.get (by decide)).trans h12u
  · rw [if_neg hg] at pu
    change Selector.group (a.extractLsb' 0 128) ≠ 0#64 at hg
    have ec := symRun_sound (choose_run (pcOf (p+2))) hc2 u pu (by
      simp [chooseRes, chooseBase.res, rv_simp, accessValid_iff, MEMORY_BYTES])
    let v := (chooseRes (pcOf (p+2))).toState u
    have rv : RegsExcept u v [.x3] := by
      intro r hr; cases r <;> simp_all [v, chooseRes, chooseBase.res, rv_simp] <;> rfl
    have fv : Frame u v (fun _ => False) := by
      intro A _ _; simp [v, chooseRes, chooseBase.res, rv_simp]
    have h12v : v.getReg .x12 = BitVec.ofNat 64 d := (rv.get (by decide)).trans h12u
    have pv : v.pc = if hint = 0#64 then pcOf (p+4) else pcOf (p+10) := by
      by_cases hz : hint = 0#64
      all_goals simp [v, u, chooseRes, chooseBase.res, headRes, headBase.res, rv_simp, hh,
        pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc, hz]
    by_cases hz : hint = 0#64
    · rw [if_pos hz] at pv
      have el := symRun_sound (low_run (pcOf (p+4))) hc4 v pv (by
        simp [lowRes, lowBase.res, rv_simp, h12v, accessValid_iff, MEMORY_BYTES]; omega)
      let t := (lowRes (pcOf (p+4))).toState v
      have rt : RegsExcept v t [.x16,.x17] := by
        intro r hr; cases r <;> simp_all [t, lowRes, lowBase.res, rv_simp] <;> rfl
      have ft : Frame v t (fun _ => False) := by
        intro A _ _; simp [t, lowRes, lowBase.res, rv_simp]
      refine ⟨6,t,(es.trans ec).trans el,by omega,?_,?_,?_,?_,
        ((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
      · simp [t, lowRes, lowBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.add_assoc, Nat.mul_add, hg, hz]
      · simpa [t, v, u, lowRes, lowBase.res, chooseRes, chooseBase.res, headRes, headBase.res,
          rv_simp, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg, hz] using hm0
      · simpa [t, v, u, lowRes, lowBase.res, chooseRes, chooseBase.res, headRes, headBase.res,
          rv_simp, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg, hz] using hm1
      · exact (rt.get (by decide)).trans h12v
    · rw [if_neg hz] at pv
      have eh := symRun_sound (high_run (pcOf (p+10))) hc10 v pv (by
        simp [highRes, highBase.res, rv_simp, h12v, accessValid_iff, MEMORY_BYTES]; omega)
      let t := (highRes (pcOf (p+10))).toState v
      have rt : RegsExcept v t [.x16,.x17] := by
        intro r hr; cases r <;> simp_all [t, highRes, highBase.res, rv_simp] <;> rfl
      have ft : Frame v t (fun _ => False) := by
        intro A _ _; simp [t, highRes, highBase.res, rv_simp]
      refine ⟨6,t,(es.trans ec).trans eh,by omega,?_,?_,?_,?_,
        ((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
      · simp [t, highRes, highBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.add_assoc, Nat.mul_add, hg, hz]
      · simpa [t, v, u, highRes, highBase.res, chooseRes, chooseBase.res, headRes, headBase.res,
          rv_simp, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg, hz] using hm2
      · simpa [t, v, u, highRes, highBase.res, chooseRes, chooseBase.res, headRes, headBase.res,
          rv_simp, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg, hz] using hm3
      · exact (rt.get (by decide)).trans h12v

end SigGolfCandidate.Choice.MachineSelect

#print axioms SigGolfCandidate.Choice.MachineSelect.select_spec
