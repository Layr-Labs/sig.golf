import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailLeafMemory
import SigGolfCandidate.T3M.Verify.LeafSem

/- The retained twelve instructions produce the genuine LeafOut consumed by
   Merkle.  The opaque post-state factor avoids evaluating a whole image in
   memory goals.  No bank instruction or HASH is charged in this adapter.
   Pure field/frame arguments follow the attributed T3M.leafT_step proof. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3 SigGolfCandidate.T3M.Verify
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

structure LeafData (w : WBytes) (pk : Digest) (index : Nat) (ends : List Digest)
    (s : MachineState) : Prop where
  glob : Glob (leafK 0) w pk s
  keep : KnownOK (lfKeepK 0) s
  s7 : s.getReg .x23 = BitVec.ofNat 64 (4096 + (route index 0).1)
  tp : s.getReg .x4 = BitVec.ofNat 64 (hdr1 (route index 0).2 (route index 0).1)
  len : ends.length = 54
  ends : ∀ j < 54, DigAt s (slotT j) (ends.getD j 0)
  orig : Verify.Orig w (fun o => 9288 ≤ o ∧ o < layerBase 0 + 64 * height 0) s

structure LeafPost (s t : MachineState) : Prop where
  regMem : LeafRegMem s t
  x3 : t.getReg .x3 = 513#64
  x4 : t.getReg .x4 = 769#64

theorem leaf_post (s : MachineState) (h27 : s.getReg .x27 = 1025#64) :
    LeafPost s (leafResult.toState s) := by
  refine ⟨leaf_reg_mem s, ?_, ?_⟩
  · rw [leaf_model, Result.toState_getReg]
    change (addC (.reg .x27) (-512)).eval s = 513#64
    rw [addC_eval]
    change s.getReg .x27 + BitVec.ofInt 64 (-512) = 513#64
    rw [h27]
    decide +kernel
  · rw [leaf_model, Result.toState_getReg]
    change (addC (.reg .x27) (-256)).eval s = 769#64
    rw [addC_eval]
    change s.getReg .x27 + BitVec.ofInt 64 (-256) = 769#64
    rw [h27]
    decide +kernel

theorem leafout_of_post (w : WBytes) (pk : Digest) (index : Nat)
    (hidx : index < 2 ^ 31) (ends : List Digest) (s t : MachineState)
    (hs : LeafData w pk index ends s) (hp : LeafPost s t) :
    LeafOut w pk index 0 ends t := by
  have h27 : s.getReg .x27 = 1025#64 := hs.glob.1 (.x27, 1025#64) (by norm_num [leafK, hw])
  have fr := hp.regMem.frame h27
  have hk : KnownOK (postLf 0) t := by
    intro p h
    simp only [postLf, List.mem_append] at h
    rcases h with h | h
    · have hn : p.1 ∉ ([.x3,.x4,.x10,.x11,.x14] : List Reg) := by
        simp [leafK, baseK] at h
        rcases h with rfl | rfl | rfl | rfl <;> decide
      exact (hp.regMem.keeps p.1 hn).trans (hs.glob.1 p h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hp.x3
      · exact hp.x4
      · exact hp.regMem.x10
      · exact hp.regMem.x11
      · exact (hp.regMem.keeps .x15 (by decide)).trans
          (hs.glob.1 (.x15, 0xae000) (by norm_num [leafK, hw]))
  have hG : Glob (lfK 0) w pk t := glob_frame hs.glob fr (by
      intro A h; unfold LeafWrites at h; rcases h with rfl | rfl | rfl | rfl <;> norm_num) (by
      intro p h
      rcases List.mem_append.mp h with h | h
      · exact hk p h
      · have hn : p.1 ∉ ([.x3,.x4,.x10,.x11,.x14] : List Reg) := by
          simp [lfKeepK] at h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact (hp.regMem.keeps p.1 hn).trans (hs.keep p h))
  have htr := tree_lt index 0 hidx
  have hlf := leaf_lt index 0
  refine ⟨?_, hG, ?_, (by intro h; exact absurd rfl h), hs.len, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp.regMem.pc]
    exact tgtLf0_eval s _ hlf hs.s7
  · rw [hp.regMem.keeps .x23 (by decide), hs.s7]
    rfl
  · intro j hj
    change j < 54 at hj
    change DigAt t (slotT j) (ends.getD j 0)
    have hsl : slotT j = 512 ∨ (544 ≤ slotT j ∧ slotT j ≤ 1376) := by
      unfold slotT; split <;> omega
    exact (hs.ends j hj).frame fr
      (by omega) (by unfold LeafWrites; omega) (by unfold LeafWrites; omega)
  · have h := hp.regMem.memory h27 528 (by norm_num)
    simp only [lfBase, if_pos rfl] at *
    simpa using (hw2_hdr0 0 _ htr).symm ▸ h
  · simpa [lfBase, hs.tp] using hp.regMem.memory h27 536 (by norm_num)
  · intro _
    exact ⟨by simpa using hp.regMem.memory h27 1392 (by norm_num),
      by simpa using hp.regMem.memory h27 1400 (by norm_num)⟩
  · exact hs.orig.frame (fun j hj ho => fr.get (by unfold WIT WX at *; omega)
      (by unfold LeafWrites WIT; omega))

theorem leafout_steps (w : WBytes) (pk : Digest) (index rank : Nat)
    (hidx : index < 2 ^ 31) (hr : rank < 64) (ends : List Digest) (s : MachineState)
    (hpc : s.pc = pcOf (leafPC rank)) (hs : LeafData w pk index ends s) :
    ∃ t, Steps image s 12 12 t ∧ LeafOut w pk index 0 ends t := by
  have h27 : s.getReg .x27 = 1025#64 := hs.glob.1 (.x27, 1025#64) (by norm_num [leafK, hw])
  exact ⟨leafResult.toState s, leaf_steps rank hr s hpc (leaf_obligations s),
    leafout_of_post w pk index hidx ends s _ hs (leaf_post s h27)⟩

#print axioms leafout_of_post
#print axioms leafout_steps
end SigGolfCandidate.T3M.Nonbinary.InlineTail
