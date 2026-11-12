import SigGolfCandidate.OuterPrePass
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterDecode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Expand.PrePass
theorem pre_entry (s0 : MachineState) (b : SharedCodec.CBytes) (hpc : s0.pc = pcOf 87500) (hsig : SigMemC s0.getMem b) :
    ∃ u, Steps OuterImages.expandImage s0 217 217 u ∧ u.pc = pcOf 54569 ∧
      (∀ r ∈ [Reg.x7, .x28, .x29, .x30, .x31], u.getReg r = 0) ∧ RegsExcept s0 u [.x7, .x28, .x29, .x30, .x31] ∧
      SigMem u.getMem (unpackB b) ∧ Frame s0 u (fun A => 0x70a8 ≤ A ∧ A < 0x84c0) := by
  obtain ⟨u, su, pu, zu, ru, mu⟩ := OuterPrePass.pre_spec s0 hpc
  have em : u.getMem = preMem s0.getMem := funext fun A => by rw [mu]
  refine ⟨u, su, pu, zu, fun r hr => ru r hr, by rw [em]; exact sigMem_pre hsig,
    fun A hA hn => ?_⟩
  rw [em]
  have hn' : A < 0x70a8 ∨ 0x84c0 ≤ A := by omega
  apply preMem_other s0.getMem A hA (by omega) (by omega)
  intro c hc he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  unfold hiA at he
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega


theorem dec_gen (s0 : MachineState) (b : SharedCodec.CBytes) (hpc : s0.pc = pcOf 87500) (hsig : SigMemC s0.getMem b)
    (hc : SharedCodec.nOfB b < nCanon) :
    ∃ u k c, Steps OuterImages.expandImage s0 k c u ∧ c ≤ 2365 ∧ u.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30, .x31], u.getReg r = 0) ∧
      RegsExcept s0 u [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30, .x31] ∧
      (∀ k, k < 332 → DigAt u (0x7000 + 16 * k)
        (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k)) ∧
      u.getMem (BitVec.ofNat 64 417792) = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat ∧
      Frame s0 u (fun A => A = 417792 ∨ (0x7000 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨s1, st1, p1, z1, r1, hsig1, f1⟩ := pre_entry s0 b hpc hsig
  have hn : nOfM s1.getMem = SharedCodec.nOfB b := by rw [nOfM_eq hsig1, nOfB_unpack]
  obtain ⟨t, k, c, st, hcc, tp, tz, tr, tm, th, tf⟩ := OuterPrePass.dec_run s1 p1 (by rw [hn]; exact hc)
  refine ⟨t, 217 + k, 217 + c, st1.trans st, by omega, tp, ?_, (r1.trans tr).mono (by decide), ?_,
    by rw [th, hint_eq hsig1, hints_unpack b hc], (f1.trans tf).mono (fun A _ h => ?_)⟩
  · intro r hr
    by_cases hr' : r ∈ [Reg.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30]
    · exact tz r hr'
    · have : r = .x31 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'; tauto
      subst this
      rw [tr .x31 (by decide)]; exact z1 .x31 (by decide)
  · intro k hk
    have e0 := (tm k 0 hk (by omega)).trans (decOut_eq hsig1 k 0 hk (by omega))
    have e1 := (tm k 1 hk (by omega)).trans (decOut_eq hsig1 k 1 hk (by omega))
    unfold slotA at e0 e1
    rw [Nat.mul_zero, Nat.add_zero] at e0
    rw [← inflated_unpack b k hk]
    exact ⟨e0, e1⟩
  · rcases h with ⟨h1, h2⟩ | h
    · exact Or.inr ⟨by omega, h2⟩
    · exact h

#print axioms pre_entry
#print axioms dec_gen
end OuterDecode
