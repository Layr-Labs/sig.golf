import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailLeafHash

/- Strong ABI export retaining the literal actual post-state. This supplements
   the original public leaf HASH theorem without changing its proved source.
   The final continuation may derive registers/header/frame from this genuine
   state; no completed Merkle outcome is supplied. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem leaf_bank_prepare_exact (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2)
    (h23 : s0.getReg .x23=BitVec.ofNat 64 (4096+c.leaf))
    (rank : Nat) (hr : rank<64) (ends : List Digest) (s : MachineState)
    (hs : c.Base s0 (c.Wr 54) ends s ∧ ends.length=54 ∧ s.pc=pcOf (leafPC rank)) :
    ∃ t,Steps image s 13 13 t ∧ fetch image t=some (.base .ECALL) ∧
      t.getReg .x5=0 ∧ hashArgumentsValid t=true ∧
      hashInput t=toQ (pad64 (leafInput 0 c.tree c.leaf ends)) ∧
      (toQ (pad64 (leafInput 0 c.tree c.leaf ends))).blocks=14 ∧
      t=(bankResult (c.leaf%64)).toState (leafResult.toState s) ∧
      ∀ a : BitVec 256,LeafAfter c t (a.extractLsb' 0 128) (writeHash t a) := by
  let u:=leafResult.toState s
  let sh:=c.leaf%64
  let t:=(bankResult sh).toState u
  have hp:=leaf_prepared_state c s0 hk rank hr ends s hs
  have hpc : u.pc=pcOf (bankPC sh) := hp.pc.trans (leaf_target_eval s0 c.leaf hc.2.1 h23)
  have hsh : sh<64 := Nat.mod_lt _ (by decide)
  obtain ⟨hst,hfetch⟩:=bank_steps_fetch sh hsh u hpc
  have h8 : u.getReg .x8=BitVec.ofNat 64 c.S3 := by
    rw [leaf_keeps s .x8 (by decide),hs.1.1 .x8 (by decide)]
    exact hk (.x8,BitVec.ofNat 64 c.S3) (by simp [NCtx.known])
  have h12 : t.getReg .x12=BitVec.ofNat 64 (leafDest c) := by
    simp only [t,bankResult,Result.toState_getReg,RegFile.get_set_self (r:=.x12) _ _ (by decide),addC_eval,E.eval]
    rw [h8]
    have hlo : 1728 ≤ c.S3 := by have hh:=hc.2.2.2.1;omega
    have he : sh%2=c.leaf%2 := by dsimp [sh];omega
    rw [he]
    apply BitVec.eq_of_toNat_eq
    simp only [leafDest,BitVec.toNat_add,BitVec.toNat_sub,BitVec.toNat_ofNat]
    have hhi:=hc.2.2.2.2.1
    rw [show (1728 : Word).toNat=1728 from rfl]
    omega
  have hreg (r : Reg) (hn : r≠.x12) : t.getReg r=u.getReg r := by
    simp only [t,bankResult,Result.toState_getReg,RegFile.get_set_ne _ _ hn,RegFile.init_get_eval]
  have hmem (A : Word) : t.getMem A=u.getMem A := by
    simp only [t,bankResult,Result.toState_getMem,memEval_nil]
  have h5 : t.getReg .x5=0 := (hreg .x5 (by decide)).trans hp.x5
  have h10 : t.getReg .x10=512#64 := (hreg .x10 (by decide)).trans hp.x10
  have h11 : t.getReg .x11=896#64 := (hreg .x11 (by decide)).trans hp.x11
  have hd : (leafDest c)%8=0 ∧ (leafDest c)+32<2^24 := by
    have hlo:=hc.2.2.2.1
    have hhi:=hc.2.2.2.2.1
    have hal:=hc.2.2.1
    unfold leafDest
    omega
  have hv:=hashArgs_const t 512 896 (leafDest c) h10 h11 h12 (by decide) (by decide) (by decide) hd.1 (by omega)
  have hin:=prepared_hash_input c hc s0 ends u hp
  have hi : hashInput t=hashInput u := by
    simp only [hashInput]
    rw [hreg .x10 (by decide),hreg .x11 (by decide)]
    congr 1
  refine ⟨t,(leaf_steps rank hr s hs.2.2 (leaf_obligations s)).trans hst,hfetch,h5,hv,hi.trans hin.1,hin.2,rfl,?_⟩
  intro a
  refine ⟨DigAt.writeHash_lo t a _ h12 (by omega),Frame.writeHash t a _ h12 (by omega),?_⟩
  rw [pc_writeHash,Result.toState_pc]
  change pcOf (bankPC sh+1)+4=pcOf (bankPC (c.leaf%64)+2)
  change BitVec.ofNat 64 (0x1000+4*(bankPC sh+1))+BitVec.ofNat 64 4 =
    BitVec.ofNat 64 (0x1000+4*(bankPC sh+2))
  rw [ofNat_add_ofNat]
  congr 1 <;> omega

theorem leaf_hash_good_exact (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2)
    (h23 : s0.getReg .x23=BitVec.ofNat 64 (4096+c.leaf))
    (rank : Nat) (hr : rank<64) (ends : List Digest) (s : MachineState)
    (hs : c.Base s0 (c.Wr 54) ends s ∧ ends.length=54 ∧ s.pc=pcOf (leafPC rank))
    (K : Digest→OracleComp Legacy.HashSpec Judg.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ a : BitVec 256,Judg.GoodQ image
      (writeHash ((bankResult (c.leaf%64)).toState (leafResult.toState s)) a)
      N C Q A (K (a.extractLsb' 0 128))) :
    Judg.GoodQ image s (N+14) (C+125) Q (A+125)
      (Judg.ccM (leafHash 0 c.tree c.leaf ends) K) := by
  obtain ⟨t,hst,hf,h5,hv,hi,hb,he,ha⟩:=leaf_bank_prepare_exact c hc s0 hk h23 rank hr ends s hs
  have H:=Judg.GoodQ.shortHash_bind (f:=fun v=>pure v) (K:=K) hf h5 hv hi
    (fun a=>by simpa [he] using hK a)
  rw [hb] at H
  have hh:=H.steps hst
  simpa [leafHash_eq,Judg.ccM_bind,Nat.add_assoc] using hh

#print axioms leaf_bank_prepare_exact
#print axioms leaf_hash_good_exact
end SigGolfCandidate.T3M.Nonbinary.InlineTail
