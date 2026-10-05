import SigGolfCandidate.T3M.Verify.BCCheck

/- Actual image-bound caller/leaf execution from the finite checked banks.
   These are ordinary physical branch/known-register preconditions. No source
   layer result, chain endpoint, or HASH outcome is supplied as a premise. -/
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/- Attributed BCWords.copyCheck_at proof body, locally named to keep this
   narrow module independent of unrelated byte-field proof declarations. -/
private theorem direct_copyCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : copyCheck lay (trPc lay c) = true := by
  obtain ⟨n3, n2, n1, n0⟩ : nCopy 3 = 1 ∧ nCopy 2 = 64 ∧ nCopy 1 = 64 ∧ nCopy 0 = 128 := by decide
  have hall : ∀ lo n, layerCheck lay lo n = true → lo ≤ c → c < lo + n → copyCheck lay (trPc lay c) = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · by_cases h : c < 64
    · exact hall 0 64 layerCheck_0a (by omega) (by omega)
    · exact hall 64 64 layerCheck_0b (by omega) (by omega)
  · exact hall 0 64 layerCheck_1 (by omega) (by omega)
  · exact hall 0 64 layerCheck_2 (by omega) (by omega)
  · exact hall 0 1 layerCheck_3 (by omega) (by omega)

theorem header_checked (lay c : Nat) (hl : lay<4) (hc : c<nCopy lay) :
    setupCheck lay (trPc lay c)=true := by
  have h := direct_copyCheck_at lay c hl hc
  simp only [copyCheck,Bool.and_eq_true] at h
  exact h.1.1

theorem actual_header (lay c : Nat) (hl : lay<4) (hc : c<nCopy lay)
    (s : MachineState) (hp : s.pc=pcOf (setupPc lay (trPc lay c)))
    (hk : KnownOK (preK lay) s)
    (hb : ∀ b∈(specA lay (trPc lay c)).brs,b.holds s) :
    ∃ t,SpecRes (allowed lay) [] baseK (specA lay (trPc lay c)) (bK lay) keepA s t := by
  have h := header_checked lay c hl hc
  simp only [setupCheck,Bool.and_eq_true] at h
  exact spec_run h.1 s hp hk hb (by simp)

theorem actual_header_x12 (lay c : Nat) (hl : lay<3) (hc : c<nCopy lay)
    (s : MachineState) (hp : s.pc=pcOf (setupPc lay (trPc lay c)))
    (hk : KnownOK (preK lay) s)
    (hb : ∀ b∈(specA lay (trPc lay c)).brs,b.holds s) :
    ∃ t,SpecRes (allowed lay) [] baseK (specA lay (trPc lay c)) (bK lay) keepA s t ∧
      t.getReg .x12=s.getReg .x12 := by
  obtain ⟨t,ht⟩ := actual_header lay c (by omega) hc s hp hk hb
  refine ⟨t,ht,?_⟩
  rw [ht.regs (.x12,.reg .x12) (by
    unfold specA
    rw [if_neg (by omega : lay≠3)]
    split_ifs <;> simp)]
  rfl

theorem actual_leaf (lay c : Nat) (hl : lay<4) (hc : c<nCopy lay)
    (s : MachineState) (hp : s.pc=pcOf (trPc lay c+retOff lay))
    (hk : KnownOK (leafK lay) s) :
    ∃ t,SpecRes [] [] baseK (specLf lay) (postLf lay) keepLf s t := by
  have h := direct_copyCheck_at lay c hl hc
  simp only [copyCheck,Bool.and_eq_true] at h
  exact spec_run h.2 s hp hk (by unfold specLf; split_ifs <;> simp) (by simp)

#print axioms header_checked
#print axioms actual_header
#print axioms actual_header_x12
#print axioms actual_leaf
end SigGolfCandidate.T3M.BC
