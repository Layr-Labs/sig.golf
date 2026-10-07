import SigGolfCandidate.T3M.Keygen.PackedFactories
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Images.Keygen
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Expand

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
local instance (image : Image) (pc : Word) (code : List (BitVec 32)) :
    Decidable (CodeAt image pc code) := by
  unfold CodeAt
  infer_instance
theorem codeAt_keygen_entry : CodeAt Images.keygenImage (pcOf 126) keygen_entry := by decide +kernel
theorem steps_keygen_entry (s : MachineState) (hpc : s.pc = pcOf 126) :
    Steps Images.keygenImage s 1 1 (run_keygen_entry.res.toState s) := by
  exact symRun_sound run_keygen_entry codeAt_keygen_entry s hpc (by simp [run_keygen_entry.res, rv_simp])
theorem codeAt_keygen_layer0 : CodeAt Images.keygenImage (pcOf 587) keygen_layer0 := by decide +kernel
theorem steps_keygen_layer0 (s : MachineState) (hpc : s.pc = pcOf 587) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer0.res.toState s) := by
  exact symRun_sound run_keygen_layer0 codeAt_keygen_layer0 s hpc (by simp [run_keygen_layer0.res, rv_simp])
theorem codeAt_keygen_layer1 : CodeAt Images.keygenImage (pcOf 589) keygen_layer1 := by decide +kernel
theorem steps_keygen_layer1 (s : MachineState) (hpc : s.pc = pcOf 589) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer1.res.toState s) := by
  exact symRun_sound run_keygen_layer1 codeAt_keygen_layer1 s hpc (by simp [run_keygen_layer1.res, rv_simp])
theorem codeAt_keygen_layer23 : CodeAt Images.keygenImage (pcOf 591) keygen_layer23 := by decide +kernel
theorem steps_keygen_layer23 (s : MachineState) (hpc : s.pc = pcOf 591) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer23.res.toState s) := by
  exact symRun_sound run_keygen_layer23 codeAt_keygen_layer23 s hpc (by simp [run_keygen_layer23.res, rv_simp])
theorem codeAt_keygen_inc : CodeAt Images.keygenImage (pcOf 592) keygen_inc := by decide +kernel
theorem steps_keygen_inc (s : MachineState) (hpc : s.pc = pcOf 592) :
    Steps Images.keygenImage s 1 1 (run_keygen_inc.res.toState s) := by
  exact symRun_sound run_keygen_inc codeAt_keygen_inc s hpc (by simp [run_keygen_inc.res, rv_simp])
theorem codeAt_keygen_body : CodeAt Images.keygenImage (pcOf 593) keygen_body := by decide +kernel
theorem steps_keygen_body (s : MachineState) (hpc : s.pc = pcOf 593) :
    Steps Images.keygenImage s 19 19 (run_keygen_body.res.toState s) := by
  exact symRun_sound run_keygen_body codeAt_keygen_body s hpc (by simp [run_keygen_body.res, rv_simp])
theorem codeAt_keygen_store : CodeAt Images.keygenImage (pcOf 132) keygen_store := by decide +kernel
theorem steps_keygen_store (s : MachineState) (hpc : s.pc = pcOf 132) :
    Steps Images.keygenImage s 8 8 (run_keygen_store.res.toState s) := by
  exact symRun_sound run_keygen_store codeAt_keygen_store s hpc (by simp [run_keygen_store.res, rv_simp])
theorem codeAt_sign_entry : CodeAt Images.signImage (pcOf 1022) sign_entry := by decide +kernel
theorem steps_sign_entry (s : MachineState) (hpc : s.pc = pcOf 1022) :
    Steps Images.signImage s 1 1 (run_sign_entry.res.toState s) := by
  exact symRun_sound run_sign_entry codeAt_sign_entry s hpc (by simp [run_sign_entry.res, rv_simp])
theorem codeAt_sign_layer0 : CodeAt Images.signImage (pcOf 1483) sign_layer0 := by decide +kernel
theorem steps_sign_layer0 (s : MachineState) (hpc : s.pc = pcOf 1483) :
    Steps Images.signImage s 2 2 (run_sign_layer0.res.toState s) := by
  exact symRun_sound run_sign_layer0 codeAt_sign_layer0 s hpc (by simp [run_sign_layer0.res, rv_simp])
theorem codeAt_sign_layer1 : CodeAt Images.signImage (pcOf 1485) sign_layer1 := by decide +kernel
theorem steps_sign_layer1 (s : MachineState) (hpc : s.pc = pcOf 1485) :
    Steps Images.signImage s 2 2 (run_sign_layer1.res.toState s) := by
  exact symRun_sound run_sign_layer1 codeAt_sign_layer1 s hpc (by simp [run_sign_layer1.res, rv_simp])
theorem codeAt_sign_layer23 : CodeAt Images.signImage (pcOf 1487) sign_layer23 := by decide +kernel
theorem steps_sign_layer23 (s : MachineState) (hpc : s.pc = pcOf 1487) :
    Steps Images.signImage s 2 2 (run_sign_layer23.res.toState s) := by
  exact symRun_sound run_sign_layer23 codeAt_sign_layer23 s hpc (by simp [run_sign_layer23.res, rv_simp])
theorem codeAt_sign_inc : CodeAt Images.signImage (pcOf 1488) sign_inc := by decide +kernel
theorem steps_sign_inc (s : MachineState) (hpc : s.pc = pcOf 1488) :
    Steps Images.signImage s 1 1 (run_sign_inc.res.toState s) := by
  exact symRun_sound run_sign_inc codeAt_sign_inc s hpc (by simp [run_sign_inc.res, rv_simp])
theorem codeAt_sign_body : CodeAt Images.signImage (pcOf 1489) sign_body := by decide +kernel
theorem steps_sign_body (s : MachineState) (hpc : s.pc = pcOf 1489) :
    Steps Images.signImage s 19 19 (run_sign_body.res.toState s) := by
  exact symRun_sound run_sign_body codeAt_sign_body s hpc (by simp [run_sign_body.res, rv_simp])
theorem codeAt_sign_store : CodeAt Images.signImage (pcOf 1028) sign_store := by decide +kernel
theorem steps_sign_store (s : MachineState) (hpc : s.pc = pcOf 1028) :
    Steps Images.signImage s 8 8 (run_sign_store.res.toState s) := by
  exact symRun_sound run_sign_store codeAt_sign_store s hpc (by simp [run_sign_store.res, rv_simp])
theorem codeAt_expand_entry : CodeAt Images.expandImage (pcOf 1032) expand_entry := by decide +kernel
theorem steps_expand_entry (s : MachineState) (hpc : s.pc = pcOf 1032) :
    Steps Images.expandImage s 1 1 (run_expand_entry.res.toState s) := by
  exact symRun_sound run_expand_entry codeAt_expand_entry s hpc (by simp [run_expand_entry.res, rv_simp])
theorem codeAt_expand_layer0 : CodeAt Images.expandImage (pcOf 1247) expand_layer0 := by decide +kernel
theorem steps_expand_layer0 (s : MachineState) (hpc : s.pc = pcOf 1247) :
    Steps Images.expandImage s 2 2 (run_expand_layer0.res.toState s) := by
  exact symRun_sound run_expand_layer0 codeAt_expand_layer0 s hpc (by simp [run_expand_layer0.res, rv_simp])
theorem codeAt_expand_layer1 : CodeAt Images.expandImage (pcOf 1249) expand_layer1 := by decide +kernel
theorem steps_expand_layer1 (s : MachineState) (hpc : s.pc = pcOf 1249) :
    Steps Images.expandImage s 2 2 (run_expand_layer1.res.toState s) := by
  exact symRun_sound run_expand_layer1 codeAt_expand_layer1 s hpc (by simp [run_expand_layer1.res, rv_simp])
theorem codeAt_expand_layer23 : CodeAt Images.expandImage (pcOf 1251) expand_layer23 := by decide +kernel
theorem steps_expand_layer23 (s : MachineState) (hpc : s.pc = pcOf 1251) :
    Steps Images.expandImage s 2 2 (run_expand_layer23.res.toState s) := by
  exact symRun_sound run_expand_layer23 codeAt_expand_layer23 s hpc (by simp [run_expand_layer23.res, rv_simp])
theorem codeAt_expand_inc : CodeAt Images.expandImage (pcOf 1252) expand_inc := by decide +kernel
theorem steps_expand_inc (s : MachineState) (hpc : s.pc = pcOf 1252) :
    Steps Images.expandImage s 1 1 (run_expand_inc.res.toState s) := by
  exact symRun_sound run_expand_inc codeAt_expand_inc s hpc (by simp [run_expand_inc.res, rv_simp])
theorem codeAt_expand_body : CodeAt Images.expandImage (pcOf 1253) expand_body := by decide +kernel
theorem steps_expand_body (s : MachineState) (hpc : s.pc = pcOf 1253) :
    Steps Images.expandImage s 19 19 (run_expand_body.res.toState s) := by
  exact symRun_sound run_expand_body codeAt_expand_body s hpc (by simp [run_expand_body.res, rv_simp])
theorem codeAt_expand_store : CodeAt Images.expandImage (pcOf 1038) expand_store := by decide +kernel
theorem steps_expand_store (s : MachineState) (hpc : s.pc = pcOf 1038) :
    Steps Images.expandImage s 8 8 (run_expand_store.res.toState s) := by
  exact symRun_sound run_expand_store codeAt_expand_store s hpc (by simp [run_expand_store.res, rv_simp])
end SigGolfCandidate.T3M.Keygen.PackedBlocks
