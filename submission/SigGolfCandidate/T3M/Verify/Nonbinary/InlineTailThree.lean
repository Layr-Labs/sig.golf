import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailChain
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailCost

/- Connected finite final-three-chain source program on the new native image.
   Continuations consume an actually derived endpoint/frame state; no chain
   value, HASH trace, or completed machine execution is supplied as a premise. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def appendSource (c : NCtx) (ordinal : Nat) (acc : List Digest) : M (List Digest) := do
  let i:=index ordinal
  let v←chainP 0 c.tree c.leaf i (c.dig i) (NCtx.topMax i-c.dig i)
    (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i)
  pure (acc++[v])

def threeSource (c : NCtx) (acc : List Digest) : M (List Digest) :=
  appendSource c 0 acc >>= fun a => appendSource c 1 a >>= appendSource c 2

def LeafReady (c : NCtx) (s0 : MachineState) (rank : Nat)
    (ends : List Digest) (t : MachineState) : Prop :=
  c.Base s0 (c.Wr 54) ends t ∧ ends.length=54 ∧ t.pc=pcOf (leafPC rank)

def threeNativeCost (c : NCtx) : Nat := nativeChainCost 0 (c.dig 51)+
  nativeChainCost 1 (c.dig 52)+nativeChainCost 2 (c.dig 53)

theorem end_leaf_ready (c : NCtx) (s0 : MachineState) (rank : Nat) (hr : rank<64)
    (ends : List Digest) (t : MachineState) (ht : End c s0 rank 2 ends t) :
    LeafReady c s0 rank ends t := by
  have he:=of_decide_eq_true (List.all_eq_true.mp leaf_pc_check rank (List.mem_range.mpr hr))
  obtain ⟨hb,hl,hpc⟩:=ht
  exact ⟨hb,hl,by rw [hpc,he]⟩

theorem append_good (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (rank ordinal : Nat) (hr : rank<64) (ho : ordinal<3)
    (hd : c.dig (index ordinal)=digit rank ordinal)
    (acc : List Digest) (K : List Digest→OracleComp Legacy.HashSpec Judg.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,End c s0 rank ordinal ends t→Judg.GoodQ image t N C Q A (K ends))
    (s : MachineState) (hs : Input c s0 rank ordinal acc s) :
    Judg.GoodQ image s (N+40) (C+nativeChainCost ordinal (c.dig (index ordinal))) Q
      (A+nativeChainCost ordinal (c.dig (index ordinal)))
      (Judg.ccM (appendSource c ordinal acc) K) := by
  rw [appendSource,Judg.ccM_bind]
  simp only [Judg.ccM_pure]
  exact one_chain c hc s0 hk h0 rank ordinal hr ho hd acc K N C A Q
    (fun v t ht=>hK (acc++[v]) t ht) s hs

theorem three_good (c : NCtx) (hc : c.ok) (s0 : MachineState)
    (hk : ∀ p ∈ c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (rank : Nat) (hr : rank<64)
    (hd : ∀ ordinal<3,c.dig (index ordinal)=digit rank ordinal)
    (acc : List Digest) (K : List Digest→OracleComp Legacy.HashSpec Judg.Obs)
    (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t,LeafReady c s0 rank ends t→Judg.GoodQ image t N C Q A (K ends))
    (s : MachineState) (hs : Input c s0 rank 0 acc s) :
    Judg.GoodQ image s (N+120) (C+threeNativeCost c) Q (A+threeNativeCost c)
      (Judg.ccM (threeSource c acc) K) := by
  have H1 : ∀ a t,End c s0 rank 1 a t→
      Judg.GoodQ image t (N+40) (C+nativeChainCost 2 (c.dig 53)) Q
        (A+nativeChainCost 2 (c.dig 53)) (Judg.ccM (appendSource c 2 a) K) := by
    intro a t ht
    exact append_good c hc s0 hk h0 rank 2 hr (by decide) (hd 2 (by decide))
      a K N C A Q (fun e u hu=>hK e u (end_leaf_ready c s0 rank hr e u hu))
      t (next_input c s0 rank 1 a t ht)
  have H0 : ∀ a t,End c s0 rank 0 a t→
      Judg.GoodQ image t (N+80)
        (C+nativeChainCost 1 (c.dig 52)+nativeChainCost 2 (c.dig 53)) Q
        (A+nativeChainCost 1 (c.dig 52)+nativeChainCost 2 (c.dig 53))
        (Judg.ccM (appendSource c 1 a >>= appendSource c 2) K) := by
    intro a t ht
    rw [Judg.ccM_bind]
    have H:=append_good c hc s0 hk h0 rank 1 hr (by decide) (hd 1 (by decide)) a
      (fun b=>Judg.ccM (appendSource c 2 b) K) (N+40)
      (C+nativeChainCost 2 (c.dig 53)) (A+nativeChainCost 2 (c.dig 53)) Q H1
      t (next_input c s0 rank 0 a t ht)
    simpa [index,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H
  rw [threeSource,Judg.ccM_bind]
  have H:=append_good c hc s0 hk h0 rank 0 hr (by decide) (hd 0 (by decide)) acc
    (fun a=>Judg.ccM (appendSource c 1 a >>= appendSource c 2) K) (N+80)
    (C+nativeChainCost 1 (c.dig 52)+nativeChainCost 2 (c.dig 53))
    (A+nativeChainCost 1 (c.dig 52)+nativeChainCost 2 (c.dig 53)) Q H0 s hs
  simpa [index,threeNativeCost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H

theorem exact_native_cost_check : ((List.range 64).all fun rank=>decide
    (nativeChainCost 0 (digit rank 0)+nativeChainCost 1 (digit rank 1)+
      nativeChainCost 2 (digit rank 2)=inlineChainCost rank))=true := by
  decide +kernel

theorem cost_exact (c : NCtx) (rank : Nat) (hr : rank<64)
    (hd : ∀ ordinal<3,c.dig (index ordinal)=digit rank ordinal) :
    threeNativeCost c=inlineChainCost rank := by
  unfold threeNativeCost
  rw [show c.dig 51=digit rank 0 from hd 0 (by decide),
    show c.dig 52=digit rank 1 from hd 1 (by decide),
    show c.dig 53=digit rank 2 from hd 2 (by decide)]
  exact of_decide_eq_true (List.all_eq_true.mp exact_native_cost_check rank (List.mem_range.mpr hr))

theorem true_final3_saves_one (c : NCtx) (rank : Nat) (hr : rank<64)
    (hd : ∀ ordinal<3,c.dig (index ordinal)=digit rank ordinal) :
    threeNativeCost c+1=legacyThreeCost rank := by
  rw [cost_exact c rank hr hd]
  exact chain_cost_saved_one rank hr

#print axioms end_leaf_ready
#print axioms three_good
#print axioms true_final3_saves_one
end SigGolfCandidate.T3M.Nonbinary.InlineTail
