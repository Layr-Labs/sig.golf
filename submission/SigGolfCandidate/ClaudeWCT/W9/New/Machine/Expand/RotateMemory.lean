import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Rotate

namespace ClaudeWCT.W9.Machine.Expand.Rotation
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def rotatedWord (s : MachineState) (i : Nat) : Word :=
  if i < 2725 then s.getMem (BitVec.ofNat 64 (2048 + 8 * (i + 4)))
  else if i = 2725 then s.getMem 2048
  else if i = 2726 then s.getMem 2056
  else if i = 2727 then 0
  else (LoadKind.wu.fromWord (s.getMem 2064) 0) <<< (32 : Word)

theorem tail_mem (s : MachineState) (A : Word) :
    (RTail.res.toState s).getMem A =
      if A = 23872 then s.getReg .x17 <<< (32 : Word)
      else if A = 23864 then 0
      else if A = 23856 then s.getReg .x16
      else if A = 23848 then s.getReg .x15
      else s.getMem A := by
  by_cases h0 : A = 23872
  <;> by_cases h1 : A = 23864
  <;> by_cases h2 : A = 23856
  <;> by_cases h3 : A = 23848
  <;> simp_all [RTail.res, rv_simp, BitVec.shiftLeft_eq']

section
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem rotate_spec (s : MachineState) (hpc : s.pc = pcOf 42144) :
    ∃ t, Steps im s 16368 16368 t ∧ t.pc = pcOf 42161 ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧ fetch im t = some (.base .ECALL) ∧
      ∀ i < 2729, t.getMem (BitVec.ofNat 64 (2048 + 8 * i)) = rotatedWord s i := by
  obtain ⟨u, su, pu, u10, u11, u12, u1, u15, u16, u17, gu, fu⟩ := start_spec hc s hpc
  obtain ⟨v, sv, pv, gv, mv⟩ := Compact.copy_spec hc u pu 2080 2048 2725 42153
    u10 u11 u12 u1 (by norm_num) (by norm_num) (by norm_num) (by norm_num [MEMORY_BYTES])
    (by norm_num) (by norm_num [MEMORY_BYTES]) (Or.inl (by norm_num))
  obtain ⟨st, pt, t5, t10, ht⟩ := tail_spec hc v pv
  refine ⟨RTail.res.toState v, ((su.trans sv).trans st).of_eq (by norm_num) (by norm_num),
    pt, t5, t10, ht, fun i hi => ?_⟩
  have ha : 2048 + 8 * i < 2 ^ 64 := by omega
  have e (b : Nat) (hb : b < 2 ^ 64) :
      BitVec.ofNat 64 (2048 + 8 * i) = BitVec.ofNat 64 b ↔ 2048 + 8 * i = b := by
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h'
    · intro h; rw [h]
  rw [tail_mem]
  change (if BitVec.ofNat 64 (2048 + 8 * i) = BitVec.ofNat 64 23872 then _ else
    if BitVec.ofNat 64 (2048 + 8 * i) = BitVec.ofNat 64 23864 then _ else
    if BitVec.ofNat 64 (2048 + 8 * i) = BitVec.ofNat 64 23856 then _ else
    if BitVec.ofNat 64 (2048 + 8 * i) = BitVec.ofNat 64 23848 then _ else _) = _
  simp only [e 23872 (by norm_num), e 23864 (by norm_num), e 23856 (by norm_num), e 23848 (by norm_num)]
  by_cases hb : i < 2725
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), mv _ ha]
    unfold Compact.copied rotatedWord
    rw [if_pos (by omega), if_pos hb, fu _ (by omega) (fun h => h)]
    apply congrArg s.getMem
    apply congrArg (BitVec.ofNat 64)
    omega
  · have v15 : v.getReg .x15 = s.getMem 2048 := (gv.get (by decide)).trans u15
    have v16 : v.getReg .x16 = s.getMem 2056 := (gv.get (by decide)).trans u16
    have v17 : v.getReg .x17 = LoadKind.wu.fromWord (s.getMem 2064) 0 := (gv.get (by decide)).trans u17
    interval_cases i <;> simp [rotatedWord, v15, v16, v17]
end
#print axioms rotate_spec
end ClaudeWCT.W9.Machine.Expand.Rotation
