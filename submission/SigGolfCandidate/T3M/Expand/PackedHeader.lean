import SigGolfCandidate.T3M.Keygen.PackedRun

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem expand_header_0 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps Images.expandReferenceImage s 30 30 t ∧ t.pc = pcOf 1046 ∧ HeaderPost s t 12 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_body.res.toState s1
  have h2 := steps_expand_body s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_store.res.toState s2
  have h3 := steps_expand_store s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s3, (((h0.trans h1).trans h2).trans h3), ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_1 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps Images.expandReferenceImage s 33 33 t ∧ t.pc = pcOf 1046 ∧ HeaderPost s t 7 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_inc.res.toState s2
  have h3 := steps_expand_inc s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_2 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps Images.expandReferenceImage s 34 34 t ∧ t.pc = pcOf 1046 ∧ HeaderPost s t 6 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_layer23.res.toState s2
  have h3 := steps_expand_layer23 s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_3 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps Images.expandReferenceImage s 34 34 t ∧ t.pc = pcOf 1046 ∧ HeaderPost s t 6 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_layer23.res.toState s2
  have h3 := steps_expand_layer23 s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
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
    Steps im s 8 8 (run_expand_store.res.toState s) := by
  exact symRun_sound run_expand_store (Code.store (im := im)) s hpc (by simp [run_expand_store.res, rv_simp])
end SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
open SigGolfCandidate.T3M.Keygen.PackedBlocks
variable {im : SigGolfCandidate.Legacy.Riscv.Image} [Code im]
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem expand_header_0 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps im s 30 30 t ∧ t.pc = pcOf 1046 ∧ HeaderPost s t 12 := by
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
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_1 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps im s 33 33 t ∧ t.pc = pcOf 1046 ∧ HeaderPost s t 7 := by
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
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_2 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps im s 34 34 t ∧ t.pc = pcOf 1046 ∧ HeaderPost s t 6 := by
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
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_3 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps im s 34 34 t ∧ t.pc = pcOf 1046 ∧ HeaderPost s t 6 := by
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
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
