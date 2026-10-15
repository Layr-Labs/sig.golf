import SigGolfCandidate.Rv
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.Choice.Selector

namespace SigGolfCandidate.Choice.MachineSelect
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- The final byte and the existing `a1 = 64` constant recognize the blocked
quarter without loading and shifting the entire high word. -/
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

def head : List (BitVec 32) := [0xf64183, 0xb1e863]
def choose : List (BitVec 32) := [0x52803183, 0x101f193, 0x360633]
def read : List (BitVec 32) := [0x863883, 0x63803]
def words : List (BitVec 32) := head ++ choose ++ read
sym_block headBase := symRun {noAlias := true} head (pcOf 1069) 200
sym_block chooseBase := symRun {noAlias := true} (choose ++ read) (pcOf 1071) 200
sym_block readBase := symRun {noAlias := true} read (pcOf 1074) 200

def headRes (p : Word) : Result :=
  {headBase.res with pc := (E.ite .ltu
    (.un (.ld .bu 7) (.ld (.bin .add (.reg .x12) (.c 8)))) (.reg .x11)
    (.c (p + 4 + 16)) (.c (p + 4 + 4)))}
def chooseRes (p : Word) : Result := {chooseBase.res with pc := .c (p + 4 + 4 + 4 + 4 + 4)}
def readRes (p : Word) : Result := {readBase.res with pc := .c (p + 4 + 4)}
theorem head_run (p : Word) :
    symRun {noAlias := true} head p 200 = some (headRes p) := by rfl
theorem choose_run (p : Word) :
    symRun {noAlias := true} (choose ++ read) p 200 = some (chooseRes p) := by rfl
theorem read_run (p : Word) :
    symRun {noAlias := true} read p 200 = some (readRes p) := by rfl

/-- Exact semantics of the executable selector for every 64-bit witness hint.
The forced-low path takes four instructions; all other paths take seven; `a1 = 64` is the existing hash-length invariant. -/
theorem select_spec {image : Image} (s : MachineState) (a : BitVec 256)
    (hint : Word) (d p : Nat)
    (hpc : s.pc = pcOf p)
    (hc0 : CodeAt image (pcOf p) head)
    (hc2 : CodeAt image (pcOf (p+2)) (choose ++ read))
    (hc5 : CodeAt image (pcOf (p+5)) read)
    (h11 : s.getReg .x11 = 64#64)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (hh : s.getMem 1320#64 = hint)
    (hlo : DigAt s d (a.extractLsb' 0 128))
    (hhi : DigAt s (d+16) (a.extractLsb' 128 128)) :
    ∃ k t, Steps image s k k t ∧ k ≤ 7 ∧ t.pc = pcOf (p+7) ∧
      t.getReg .x16 = (Selector.branchRead (Selector.splitEquiv a) hint).extractLsb' 0 64 ∧
      t.getReg .x17 = (Selector.branchRead (Selector.splitEquiv a) hint).extractLsb' 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 d + Selector.branchOffset (a.extractLsb' 0 128) hint ∧
      RegsExcept s t [.x3,.x12,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  have hm0 : s.getMem (s.getReg .x12) = (a.extractLsb' 0 128).extractLsb' 0 64 := by
    rw [h12]; exact hlo.1
  have hm1 : s.getMem (s.getReg .x12 + 8#64) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
    rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hlo.2
  have hm2 : s.getMem (s.getReg .x12 + 16#64) = (a.extractLsb' 128 128).extractLsb' 0 64 := by
    rw [h12, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; exact hhi.1
  have hm3 : s.getMem (s.getReg .x12 + 16#64 + 8#64) = (a.extractLsb' 128 128).extractLsb' 64 64 := by
    rw [h12, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl,
      show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat, ofNat_add_ofNat]
    exact hhi.2
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
      pcOf (p+5) else pcOf (p+2) := by
    simp only [u, headRes, headBase.res, rv_simp, hm1, h11, byte_gate]
    by_cases hg : Selector.group (a.extractLsb' 0 128) = 0
    all_goals simp [hg, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  have h12u : u.getReg .x12 = BitVec.ofNat 64 d := (ru.get (by decide)).trans h12
  have hhu : u.getMem 1320#64 = hint := by
    simpa [u, headRes, headBase.res, rv_simp] using hh
  by_cases hg : Selector.group (a.extractLsb' 0 128) = 0
  · rw [if_pos hg] at pu
    have ec := symRun_sound (read_run (pcOf (p+5))) hc5 u pu (by
      simp [readRes, readBase.res, rv_simp, h12u, accessValid_iff, MEMORY_BYTES]; omega)
    let t := (readRes (pcOf (p+5))).toState u
    have rt : RegsExcept u t [.x16,.x17] := by
      intro r hr; cases r <;> simp_all [t, readRes, readBase.res, rv_simp] <;> rfl
    have ft : Frame u t (fun _ => False) := by
      intro A _ _; simp [t, readRes, readBase.res, rv_simp]
    refine ⟨4,t,es.trans ec,by omega,?_,?_,?_,?_,
      (ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · simp [t, readRes, readBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.add_assoc, Nat.mul_add]
    · simpa [t, u, readRes, readBase.res, headRes, headBase.res, rv_simp,
        Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm0
    · simpa [t, u, readRes, readBase.res, headRes, headBase.res, rv_simp,
        Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm1
    · rw [rt.get (by decide), h12u]
      simp [Selector.branchOffset, hg]
  · rw [if_neg hg] at pu
    change Selector.group (a.extractLsb' 0 128) ≠ 0#64 at hg
    have hmask : hint &&& 16#64 = 0#64 ∨ hint &&& 16#64 = 16#64 := Selector.mask_cases hint
    have hob : (chooseRes (pcOf (p+2))).obligs u := by
      rcases hmask with hz | hz
      all_goals have hn := congrArg BitVec.toNat hz
      all_goals simp only [BitVec.toNat_and] at hn
      all_goals norm_num at hn
      all_goals simp [Result.obligs, chooseRes, chooseBase.res, rv_simp,
        h12u, hhu, hz, hn, accessValid_iff, MEMORY_BYTES]
      all_goals omega
    have ec := symRun_sound (choose_run (pcOf (p+2))) hc2 u pu hob
    let t := (chooseRes (pcOf (p+2))).toState u
    have rt : RegsExcept u t [.x3,.x12,.x16,.x17] := by
      intro r hr; cases r <;> simp_all [t, chooseRes, chooseBase.res, rv_simp] <;> rfl
    have ft : Frame u t (fun _ => False) := by
      intro A _ _; simp [t, chooseRes, chooseBase.res, rv_simp]
    refine ⟨7,t,es.trans ec,by omega,?_,?_,?_,?_,
      (ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · simp [t, chooseRes, chooseBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.add_assoc, Nat.mul_add]
    · rcases hmask with hz | hz
      · simpa [t, u, chooseRes, chooseBase.res, headRes, headBase.res, rv_simp,
          hh, hz, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm0
      · simpa [t, u, chooseRes, chooseBase.res, headRes, headBase.res, rv_simp,
          hh, hz, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm2
    · rcases hmask with hz | hz
      · simpa [t, u, chooseRes, chooseBase.res, headRes, headBase.res, rv_simp,
          hh, hz, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm1
      · simpa [t, u, chooseRes, chooseBase.res, headRes, headBase.res, rv_simp,
          hh, hz, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm3
    · simp [t, u, chooseRes, chooseBase.res, headRes, headBase.res, rv_simp,
        hh, h12, Selector.branchOffset, hg]

end SigGolfCandidate.Choice.MachineSelect

#print axioms SigGolfCandidate.Choice.MachineSelect.select_spec
