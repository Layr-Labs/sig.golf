import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailState

/- Genuine final3 endpoint/header/frame refinement. The zero-query branch
   executes four real native instructions; the positive branch prepares a
   real HASH query at its new PC. Memory-law bodies retain T3M attribution. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3
open SigGolfCandidate.T3M.Nonbinary.NCtx
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem copy_stage (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (rank ordinal : Nat) (hr : rank < 64) (ho : ordinal < 3)
    (hd : digit rank ordinal=3) (acc : List Digest) (s : MachineState)
    (hs : Input c s0 rank ordinal acc s) :
    ∃ t,Steps image s 4 4 t ∧ End c s0 rank ordinal (acc++[c.val (index ordinal)]) t := by
  let i:=index ordinal
  have hi : i < 54 := by dsimp [i,index];omega
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩:=hs
  have kr : ∀ r v,(r,v) ∈ c.known → r ∉ chainRegs → s.getReg r=v :=
    fun r v hm hn => (hR r hn).trans (hk _ hm)
  have h8 : s.getReg .x8=BitVec.ofNat 64 c.S3 := kr _ _ (by simp [NCtx.known]) (by decide)
  let r:=copyFH .x8 (off i) (slot i) (chainPC rank ordinal)
  have he : headResult rank ordinal=r := by simp [headResult,hd,r,i,index]
  have hob : r.obligs s := by
    rw [Result.obligs,Oblig.all_iff]
    simpa [r,copyFH] using c.copy_obl hc h8 i hi
  have hst:=head_steps rank ordinal hr ho s hpc (by rw [he];exact hob)
  rw [he] at hst
  have hkeep:=copyFH_keeps .x8 (off i) (slot i) (chainPC rank ordinal)
  obtain ⟨hF',hS'⟩:=c.copy_post (t:=r.toState s) hc h0 i hi acc hlen hF hS h8
    (fun A _ => by rw [Result.toState_getMem];rfl)
  refine ⟨r.toState s,hst,⟨⟨fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),hF',hS'⟩,
    by simp [hlen],?_⟩⟩
  rw [Result.toState_pc]
  simp only [r,copyFH,E.eval]
  rw [chainPC_succ,hd]
  rfl

theorem head_stage (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (rank ordinal : Nat) (hr : rank < 64) (ho : ordinal < 3)
    (hdig : c.dig (index ordinal)=digit rank ordinal) (hd : c.dig (index ordinal) < 3)
    (acc : List Digest) (s : MachineState) (hs : Input c s0 rank ordinal acc s) :
    ∃ t,Steps image s 4 4 t ∧
      Pre c s0 rank ordinal (c.dig (index ordinal)) acc (c.val (index ordinal)) t := by
  let i:=index ordinal
  let p:=chainPC rank ordinal
  have hi : i < 54 := by dsimp [i,index];omega
  obtain ⟨⟨hR,hF,hS⟩,hlen,hpc⟩:=hs
  have hb:=c.blk_props hc i hi
  have hslot:=slot_props i hi
  have kr : ∀ r v,(r,v) ∈ c.known → r ∉ chainRegs → s.getReg r=v :=
    fun r v hm hn => (hR r hn).trans (hk _ hm)
  have h8 : s.getReg .x8=BitVec.ofNat 64 c.S3 := kr _ _ (by simp [NCtx.known]) (by decide)
  have keyE:=c.kAt_eval hc h8 i hi
  have htable:=c.header_load i (c.dig i) (kr _ _ (by simp [NCtx.known]) (by decide))
  let r:=if c.dig i=2 then headRHT .x8 (off i) (c.dig i) (slot i) p i
    else headRH .x8 (off i) (c.dig i) none p i
  have he : headResult rank ordinal=r := by
    simp only [headResult,←hdig,if_neg (by omega : c.dig (index ordinal)≠3)]
    rfl
  have hobl : ∀ o ∈ r.st.obl,o.holds s := by
    simp only [r]
    split_ifs <;> simp only [headRHT,headRH,List.mem_cons,List.not_mem_nil,or_false]
    all_goals
      rintro o rfl
      show accessValid ((kAt .x8 (off i) 16).eval s) 8=true
      rw [keyE 16 (by omega)]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hob : r.obligs s := (Oblig.all_iff _ _).mpr hobl
  have hst:=head_steps rank ordinal hr ho s hpc (by rw [he];exact hob)
  have hec:=head_fetch rank ordinal hr ho (by rw [←hdig];exact hd) s
    (by rw [he];exact hob)
  rw [he] at hst hec
  have hkeep : Keeps r [.x10,.x12,.x25] := by
    dsimp [r]
    split_ifs
    · exact headRHT_keeps .x8 (off i) (c.dig i) (slot i) p i
    · exact headRH_keeps .x8 (off i) (c.dig i) none p i
  have a0e : (addC (.reg .x8) (off i)).eval s=BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]
    simp only [E.eval,h8]
    exact c.base_off0 hc i hi
  have tm : ∀ A,A < 2^64 → (r.toState s).getMem (BitVec.ofNat 64 A)=
      if A=c.blk i+16 then BitVec.ofNat 64 (c.w0 i+2^8*c.dig i)
      else if A=c.blk i+24 then c.padHeader i else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    have hm : r.st.mem=(headRH .x8 (off i) (c.dig i) none p i).st.mem := by
      dsimp [r];split_ifs <;> rfl
    rw [hm]
    simp only [headRH]
    rw [memEval_one s _ _ (c.blk i+16) A (keyE 16 (by omega)) (by omega) hA]
    change (if A=c.blk i+16 then (hLoad i (c.dig i)).eval s else s.getMem (BitVec.ofNat 64 A))=_
    rw [htable]
    have hpad:=padHeader_at hc h0 hi hF
    split_ifs <;> simp_all
  have fr : Frame s (r.toState s) (fun A => A=c.blk i+16 ∨ A=c.blk i+24) := by
    intro A hA hn
    rw [tm A hA,if_neg (fun h => hn (Or.inl h)),if_neg (fun h => hn (Or.inr h))]
  have hv:=val_at hc h0 hi hF
  have hstep : r.steps=4 ∧ r.cycles=4 := by dsimp [r];split_ifs <;> exact ⟨rfl,rfl⟩
  rw [hstep.1,hstep.2] at hst
  refine ⟨r.toState s,hst,?_⟩
  change c.Base s0 (c.WrIn i) acc (r.toState s) ∧ acc.length=i ∧
    (r.toState s).getMem (BitVec.ofNat 64 (c.blk i+16))=BitVec.ofNat 64 (c.w0 i+2^8*c.dig i) ∧
    (r.toState s).getMem (BitVec.ofNat 64 (c.blk i+24))=c.padHeader i ∧
    DigAt (r.toState s) (c.blk i+48) (c.val i) ∧
    (r.toState s).getReg .x10=BitVec.ofNat 64 (c.blk i) ∧
    (r.toState s).getReg .x12=BitVec.ofNat 64 (if c.dig i=2 then slot i else c.blk i+48) ∧
    (r.toState s).pc=pcOf (queryPC rank ordinal (c.dig i)) ∧
    fetch image (r.toState s)=some (.base .ECALL)
  refine ⟨⟨fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans fr).mono ?_,fun j hj => ?_⟩,hlen,?_,?_,
    hv.frame fr (by omega) (by omega) (by omega),?_,?_,?_,hec⟩
  · intro A _ h
    rcases h with h|h
    · exact Or.inl h
    · right;left;omega
  · have hsj:=slot_props j (by omega)
    exact (hS j hj).frame fr (by omega) (by omega) (by omega)
  · rw [tm _ (by omega),if_pos rfl]
  · rw [tm _ (by omega),if_neg (by omega),if_pos rfl]
  · rw [Result.toState_getReg]
    dsimp [r]
    split_ifs <;> simp only [headRHT,headRH]
    all_goals rw [RegFile.get_set_ne _ _ (by decide),RegFile.get_set_ne _ _ (by decide),
      RegFile.get_set_self _ _ (by decide),a0e]
  · rw [Result.toState_getReg]
    dsimp [r]
    split_ifs with h2
    · simp only [headRHT,headRH]
      rw [RegFile.get_set_ne _ _ (by decide),RegFile.get_set_self _ _ (by decide)]
      simp only [h2,if_true,E.eval]
    · simp only [headRH]
      rw [RegFile.get_set_ne _ _ (by decide),RegFile.get_set_self _ _ (by decide)]
      rw [addC_eval,a0e,show (48 : Word)=BitVec.ofNat 64 48 from rfl,ofNat_add_ofNat]
  · rw [Result.toState_pc]
    have hpq : queryPC rank ordinal (c.dig i)=p+4 := by
      unfold queryPC
      rw [show c.dig i=digit rank ordinal from hdig]
      simp [p]
    rw [hpq]
    dsimp [r]
    split_ifs <;> rfl

#print axioms copy_stage
#print axioms head_stage
end SigGolfCandidate.T3M.Nonbinary.InlineTail
