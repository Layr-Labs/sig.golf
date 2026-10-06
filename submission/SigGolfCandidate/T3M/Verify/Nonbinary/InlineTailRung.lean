import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailQuery

/- New-image ordinary rung execution and memory frame; memory proof bodies
   retain attribution to T3M.NCtx.rung_piece/rung_step. No old image run
   equality or desired execution outcome is supplied. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3
open SigGolfCandidate.T3M.Nonbinary.NCtx
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem rung_memory (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2)
    (rank ordinal m : Nat) (hrank : rank<64) (ho : ordinal<3) (hm : m ≤ 2)
    (hd : digit rank ordinal < m) (s : MachineState)
    (hpc : s.pc=pcOf (rungPC rank ordinal m))
    (hR : ∀ x ∉ chainRegs,s.getReg x=s0.getReg x)
    (h10 : s.getReg .x10=BitVec.ofNat 64 (c.blk (index ordinal)))
    (hH : c.HdrOk (index ordinal) s) :
    ∃ t,Steps image s (if m=2 then 2 else 1) (if m=2 then 2 else 1) t ∧
      fetch image t=some (.base .ECALL) ∧
      (∀ x,x≠.x12 → t.getReg x=s.getReg x) ∧
      (m=2 → t.getReg .x12=BitVec.ofNat 64 (slot (index ordinal))) ∧
      (m<2 → t.getReg .x12=s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk (index ordinal)+16))=
        BitVec.ofNat 64 (c.w0 (index ordinal)+2^8*m) ∧
      Frame s t (fun A=>A=c.blk (index ordinal)+16) ∧
      t.pc=pcOf (rungPC rank ordinal m+(if m=2 then 2 else 1)) := by
  let i:=index ordinal
  have hbi : c.blk (index ordinal)=c.blk i := rfl
  have hsi : slot (index ordinal)=slot i := rfl
  let p:=rungPC rank ordinal m
  have hi : i<54 := by dsimp [i,index];omega
  have hiLast : NCtx.last i=2 := last_index ordinal ho
  have hmLast : m ≤ NCtx.last i := by rw [hiLast];exact hm
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  set r := rungR m (if m = 2 then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 17⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (17 : Word) = BitVec.ofNat 64 17 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hx:=rung_steps_fetch rank ordinal m hrank ho hd hm s hpc ((Oblig.all_iff _ _).mpr hobl)
  have hn : r.steps = (if m=2 then 2 else 1) ∧ r.cycles = (if m=2 then 2 else 1) := by
    simp only [hr,rungR];split <;> simp_all
  have hst:=hx.1
  have hec:=hx.2
  change Steps image s r.steps r.cycles (r.toState s) at hst
  change fetch image (r.toState s)=some (.base .ECALL) at hec
  rw [hn.1,hn.2] at hst
  have hkeep := rungR_keeps m (if m = 2 then some (slot i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 1 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR i m hmLast]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ 2 by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have hp := c.prefix_props
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1
    unfold w0
    omega
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h2 : m = 2 <;> simp [h2, E.eval,p]
theorem rung_query_next (rank ordinal m : Nat) (hd : digit rank ordinal < m) (hm : m ≤ 2) :
    rungPC rank ordinal m+(if m=2 then 2 else 1)=queryPC rank ordinal m := by
  unfold rungPC queryPC
  split_ifs <;> omega

theorem rung_stage (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2)
    (rank ordinal m : Nat) (hr : rank<64) (ho : ordinal<3) (hm : m ≤ 2)
    (hd : digit rank ordinal < m) (acc : List Digest) (v : Digest)
    (s : MachineState) (hs : Step c s0 rank ordinal m acc v s) :
    ∃ t,Steps image s (if m=2 then 2 else 1) (if m=2 then 2 else 1) t ∧
      Pre c s0 rank ordinal m acc v t := by
  let i:=index ordinal
  have hbi : c.blk (index ordinal)=c.blk i := rfl
  have hsi : slot (index ordinal)=slot i := rfl
  have hi : i<54 := by dsimp [i,index];omega
  obtain ⟨⟨hR,hF,hS⟩,hlen,hH,hv,h10,h12,hpc⟩:=hs
  have hb:=c.blk_props hc i hi
  obtain ⟨t,hst,hec,hreg,h12a,h12b,h16,hfr,hpc'⟩:=
    rung_memory c hc s0 hk rank ordinal m hr ho hm hd s hpc hR h10 hH
  refine ⟨t,hst,⟨⟨fun x hx=>?_,(hF.trans hfr).mono ?_,fun j hj=>?_⟩,
    hlen,h16,?_,?_,?_,?_,?_,hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))];exact hR x hx
  · intro A _ h;rcases h with h|h
    · exact h
    · right;left;omega
  · have hsj:=slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [hfr _ (by omega) (by omega)];exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)];exact h10
  · by_cases h2 : m=2
    · rw [h12a h2,if_pos h2]
    · rw [h12b (by omega),h12 (by omega),if_neg h2]
  · rw [hpc',rung_query_next rank ordinal m hd hm]

#print axioms rung_memory
#print axioms rung_stage
end SigGolfCandidate.T3M.Nonbinary.InlineTail
