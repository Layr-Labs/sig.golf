import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailMemory

/- Real final3 HASH-input and arbitrary-answer frame refinement.
   Memory laws are attributed to T3M.NCtx.prehash_step; actualnew PCs are
   proved from the new schedule. No old-image execution outcome is used. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3
open SigGolfCandidate.T3M.Nonbinary.NCtx
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem prehash_stage (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (rank ordinal m : Nat) (hr : rank < 64) (ho : ordinal < 3) (hm : m  ≤  2)
    (hdig : c.dig (index ordinal)=digit rank ordinal) (hd : c.dig (index ordinal)  ≤  m)
    (acc : List Digest) (v : Digest) (t : MachineState)
    (ht : Pre c s0 rank ordinal m acc v t) :
    t.getReg .x5=0 ∧ hashArgumentsValid t=true ∧
      hashInput t=toQ (chainInputP 0 c.tree c.leaf (index ordinal) m
        (c.pad0 (index ordinal)) (c.pad1 (index ordinal)) (c.padHeader (index ordinal)) v) ∧
      ∀ a : BitVec 256,
        (m < 2 → Step c s0 rank ordinal (m+1) acc (a.extractLsb' 0 128) (writeHash t a)) ∧
        (m = 2 → End c s0 rank ordinal (acc++[a.extractLsb' 0 128]) (writeHash t a)) := by
  let i:=index ordinal
  have hbi : c.blk (index ordinal)=c.blk i := rfl
  have hsi : slot (index ordinal)=slot i := rfl
  have hi : i < 54 := by dsimp [i,index];omega
  have hiLast : NCtx.last i=2 := last_index ordinal ho
  have hm' : m  ≤  NCtx.last i := by rw [hiLast];exact hm
  obtain ⟨⟨hR, hF, hS⟩, hlen, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = 2 then slot i else c.blk i + 48) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B  ≤  A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm2 => ?_, fun hm2 => ?_⟩
    · have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; omega)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.blk i + 48  ≤  A ∧ A < c.blk i + 48 + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        ⟨?_, ?_, ?_⟩, DigAt.writeHash_lo t a _ d12 (by omega),
        by rw [getReg_writeHash]; exact h10, fun _ => by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slot_props j (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16]
        exact (c.w0_low i m hi (by omega)).1
      · rw [fget _ (by omega) (by omega), h16]
        exact (c.w0_low i m hi (by omega)).2
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash,hpc,show (4 : Word)=BitVec.ofNat 64 4 from rfl,ofNat_add_ofNat]
        have he:=query_rung_next rank ordinal m (by rw [←hdig];exact hd) hm2
        change BitVec.ofNat 64 (0x1000+4*(queryPC rank ordinal m)+4)=
          BitVec.ofNat 64 (0x1000+4*(rungPC rank ordinal (m+1)))
        congr 1
        omega
    · subst hm2
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (slot i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        have := c.blk_le hc i hi
        have hlo := hc.2.2.2.1
        unfold WrIn Wr blk at *
        omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen], ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slot_props j (by omega)
          have hmono : slot j + 16  ≤  slot i := by unfold slot; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
      · rw [pc_writeHash,hpc,show (4 : Word)=BitVec.ofNat 64 4 from rfl,ofNat_add_ofNat]
        have he:=final_query_next rank ordinal (by rw [←hdig];omega)
        change BitVec.ofNat 64 (0x1000+4*(queryPC rank ordinal 2)+4)=
          BitVec.ofNat 64 (0x1000+4*(chainPC rank (ordinal+1)))
        congr 1
        omega

#print axioms prehash_stage
end SigGolfCandidate.T3M.Nonbinary.InlineTail
