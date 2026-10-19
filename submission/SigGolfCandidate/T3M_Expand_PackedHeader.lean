import SigGolfCandidate.T3M_Keygen_PackedRun
set_option Elab.async false

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Keygen.PackedBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen.PackedBlocks
class Code (im : Image) : Prop where
  entry : CodeAt im (pcOf 1032) expand_entry
  layer0 : CodeAt im (pcOf 1247) expand_layer0
  layer1 : CodeAt im (pcOf 1249) expand_layer1
  layer23 : CodeAt im (pcOf 1251) expand_layer23
  inc : CodeAt im (pcOf 1252) expand_inc
  body : CodeAt im (pcOf 1253) expand_body
  store : CodeAt im (pcOf 1038) expand_store
variable {im : Image} [Code im]
theorem steps_expand_entry (s : MachineState) (hpc : s.pc = pcOf 1032) :
    Steps im s 1 1 (run_expand_entry.res.toState s) := by
  exact symRun_sound run_expand_entry (Code.entry (im := im)) s hpc (by simp [run_expand_entry.res, rv_simp])

theorem steps_expand_layer0 (s : MachineState) (hpc : s.pc = pcOf 1247) :
    Steps im s 2 2 (run_expand_layer0.res.toState s) := by
  exact symRun_sound run_expand_layer0 (Code.layer0 (im := im)) s hpc (by simp [run_expand_layer0.res, rv_simp])

theorem steps_expand_layer1 (s : MachineState) (hpc : s.pc = pcOf 1249) :
    Steps im s 2 2 (run_expand_layer1.res.toState s) := by
  exact symRun_sound run_expand_layer1 (Code.layer1 (im := im)) s hpc (by simp [run_expand_layer1.res, rv_simp])

theorem steps_expand_layer23 (s : MachineState) (hpc : s.pc = pcOf 1251) :
    Steps im s 2 2 (run_expand_layer23.res.toState s) := by
  exact symRun_sound run_expand_layer23 (Code.layer23 (im := im)) s hpc (by simp [run_expand_layer23.res, rv_simp])

theorem steps_expand_inc (s : MachineState) (hpc : s.pc = pcOf 1252) :
    Steps im s 1 1 (run_expand_inc.res.toState s) := by
  exact symRun_sound run_expand_inc (Code.inc (im := im)) s hpc (by simp [run_expand_inc.res, rv_simp])

theorem steps_expand_body (s : MachineState) (hpc : s.pc = pcOf 1253) :
    Steps im s 19 19 (run_expand_body.res.toState s) := by
  exact symRun_sound run_expand_body (Code.body (im := im)) s hpc (by simp [run_expand_body.res, rv_simp])

theorem steps_expand_store (s : MachineState) (hpc : s.pc = pcOf 1038) :
    Steps im s 3 3 (run_expand_store.res.toState s) := by
  exact symRun_sound run_expand_store (Code.store (im := im)) s hpc (by simp [run_expand_store.res, rv_simp])
end SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
open SigGolfCandidate.T3M.Keygen.PackedBlocks
variable {im : SigGolfCandidate.Legacy.Riscv.Image} [Code im]
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
/-- Pairing stage 1: expand's chain header store ends at 1040 (1041 is `jal 43764`, the G/F step block); `t3`
holds `CHAIN`. -/
structure ExpHeaderPost (s t : MachineState) (height : Nat) : Prop where
  low : t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = packedAt s height
  high : t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = routedAt s height >>> 32
  x28 : t.getReg .x28 = BitVec.ofNat 64 0x201A0
  regs : RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30]
  frame : Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24)
theorem expand_header_0 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps im s 25 25 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 12 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_body.res.toState s1
  have h2 := steps_expand_body (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_store.res.toState s2
  have h3 := steps_expand_store (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s3, (((h0.trans h1).trans h2).trans h3), ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_1 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps im s 28 28 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 7 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_inc.res.toState s2
  have h3 := steps_expand_inc (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_2 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 6 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_layer23.res.toState s2
  have h3 := steps_expand_layer23 (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_3 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 6 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_layer23.res.toState s2
  have h3 := steps_expand_layer23 (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
