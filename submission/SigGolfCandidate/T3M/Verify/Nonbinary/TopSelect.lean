import SigGolfCandidate.T3M.Verify.Nonbinary.LayerPrefix
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3.Nonbinary.LowerLayout

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem prefix_select_spec {image : Image} (s : MachineState) (a : BitVec 256) (d p : Nat)
    (hpc : s.pc = pcOf p)
    (hc0 : CodeAt image (pcOf p) prefixHead)
    (hc2 : CodeAt image (pcOf (p+2)) prefixLow)
    (hc4 : CodeAt image (pcOf (p+4)) prefixHigh)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (hlo : DigAt s d (a.extractLsb' 0 128))
    (hhi : DigAt s (d+16) (a.extractLsb' 128 128)) :
    ∃ k t, Steps image s k k t ∧ k ≤ 4 ∧ t.pc = pcOf (p+6) ∧
      t.getReg .x16 = (T3.TopDualHalf.select a).extractLsb' 0 64 ∧
      t.getReg .x17 = (T3.TopDualHalf.select a).extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17] ∧ Frame s t (fun _ => False) := by
  have hm0 : s.getMem (s.getReg .x12) = (a.extractLsb' 0 128).extractLsb' 0 64 := by rw [h12]; exact hlo.1
  have hm1 : s.getMem (s.getReg .x12 + 8#64) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
    rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hlo.2
  have hm2 : s.getMem (s.getReg .x12 + 16#64) = (a.extractLsb' 128 128).extractLsb' 0 64 := by
    rw [h12, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; exact hhi.1
  have hm3 : s.getMem (s.getReg .x12 + 24#64) = (a.extractLsb' 128 128).extractLsb' 64 64 := by
    rw [h12, show (24#64 : Word) = BitVec.ofNat 64 24 from rfl, ofNat_add_ofNat]
    simpa [Nat.add_assoc] using hhi.2
  have ho : ∀ o ∈ prefixHeadBase.res.st.obl, o.holds s := by
    simp [prefixHeadBase.res, rv_simp, h12, accessValid_iff, MEMORY_BYTES]
    omega
  have es := symRun_sound (prefixHead_run (pcOf p)) hc0 s hpc ((Oblig.all_iff _ _).mpr ho)
  let u := (prefixHeadRes (pcOf p)).toState s
  have ru : RegsExcept s u [.x17] := by
    intro r hr; cases r <;> simp_all [u, prefixHeadRes, prefixHeadBase.res, rv_simp] <;> rfl
  have fu : Frame s u (fun _ => False) := by
    intro A _ _; simp [u, prefixHeadRes, prefixHeadBase.res, rv_simp]
  have pu : u.pc = if T3.TopDualHalf.gate (a.extractLsb' 0 128) then pcOf (p+2) else pcOf (p+4) := by
    change (if (!(s.getMem (s.getReg .x12 + 8#64)).slt (0#64)) = true then
      pcOf p + 4 + 12 else pcOf p + 4 + 4) = _
    rw [hm1,BitVec.slt_zero_eq_msb,BitVec.msb_extractLsb',BitVec.getMsbD_eq_getLsbD]
    change (if (!(a.extractLsb' 0 128).getLsbD 127) = true then
      pcOf p + 4 + 12 else pcOf p + 4 + 4) = _
    by_cases hg : T3.TopDualHalf.gate (a.extractLsb' 0 128)
    · have hb := (T3.TopDualHalf.gate_iff_getLsbD (a.extractLsb' 0 128)).mp hg
      rw [hb,if_pos hg]
      simp [pcOf,ofNat_add_ofNat,Nat.mul_add,Nat.add_assoc] <;> congr 1 <;> omega
    · have hb : (a.extractLsb' 0 128).getLsbD 127 = false := by
        cases hbit : (a.extractLsb' 0 128).getLsbD 127
        · rfl
        · exact False.elim (hg ((T3.TopDualHalf.gate_iff_getLsbD (a.extractLsb' 0 128)).mpr hbit))
      rw [hb,if_neg hg]
      simp [pcOf,ofNat_add_ofNat,Nat.mul_add,Nat.add_assoc] <;> congr 1 <;> omega
  have h12u : u.getReg .x12 = BitVec.ofNat 64 d := (ru.get (by decide)).trans h12
  by_cases hg : T3.TopDualHalf.gate (a.extractLsb' 0 128)
  · rw [if_pos hg] at pu
    have ec := symRun_sound (prefixLow_run (pcOf (p+2))) hc2 u pu (by
      simp [prefixLowRes, prefixLowBase.res, rv_simp, h12u, accessValid_iff, MEMORY_BYTES]; omega)
    let t := (prefixLowRes (pcOf (p+2))).toState u
    have rt : RegsExcept u t [.x16] := by
      intro r hr; cases r <;> simp_all [t, prefixLowRes, prefixLowBase.res, rv_simp] <;> rfl
    have ft : Frame u t (fun _ => False) := by
      intro A _ _; simp [t, prefixLowRes, prefixLowBase.res, rv_simp]
    refine ⟨4,t,es.trans ec,by omega,?_,?_,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · simp [t, prefixLowRes, prefixLowBase.res, rv_simp, pcOf, ofNat_add_ofNat] <;> congr 1 <;> omega
    · simp only [T3.TopDualHalf.select,T3.TopDualHalf.selectPair,if_pos hg]
      simpa [t,u,prefixLowRes,prefixLowBase.res,prefixHeadRes,prefixHeadBase.res,rv_simp] using hm0
    · simp only [T3.TopDualHalf.select,T3.TopDualHalf.selectPair,if_pos hg]
      rw [rt.get (by decide)]
      simpa [u,prefixHeadRes,prefixHeadBase.res,rv_simp] using hm1
  · rw [if_neg hg] at pu
    have ec := symRun_sound (prefixHigh_run (pcOf (p+4))) hc4 u pu (by
      simp [prefixHighRes, prefixHighBase.res, rv_simp, h12u, accessValid_iff, MEMORY_BYTES]; omega)
    let t := (prefixHighRes (pcOf (p+4))).toState u
    have rt : RegsExcept u t [.x16,.x17] := by
      intro r hr; cases r <;> simp_all [t, prefixHighRes, prefixHighBase.res, rv_simp] <;> rfl
    have ft : Frame u t (fun _ => False) := by
      intro A _ _; simp [t, prefixHighRes, prefixHighBase.res, rv_simp]
    refine ⟨4,t,es.trans ec,by omega,?_,?_,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · simp [t, prefixHighRes, prefixHighBase.res, rv_simp, pcOf, ofNat_add_ofNat] <;> congr 1 <;> omega
    · simp only [T3.TopDualHalf.select,T3.TopDualHalf.selectPair,if_neg hg]
      simpa [t,u,prefixHighRes,prefixHighBase.res,prefixHeadRes,prefixHeadBase.res,rv_simp] using hm2
    · simp only [T3.TopDualHalf.select,T3.TopDualHalf.selectPair,if_neg hg]
      simpa [t,u,prefixHighRes,prefixHighBase.res,prefixHeadRes,prefixHeadBase.res,rv_simp] using hm3


end SigGolfCandidate.T3M.Verify.Nonbinary
