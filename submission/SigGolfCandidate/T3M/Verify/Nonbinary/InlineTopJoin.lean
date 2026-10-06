import SigGolfCandidate.T3M.Verify.Nonbinary.InlinePrefixFold
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailThree
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailLeafABI

/- One source program for all54 literal chains and the real14-block leaf.
   This joins actual first51, tail3, and new3-chain proofs. The continuation
   receives a derived leaf-ready state or the exact real HASH post-state;
   no completed chain or Merkle outcome is assumed. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

 theorem threeSource_eq_tail_fold (c : NCtx) (acc : List Digest) :
    threeSource c acc=(List.range' 51 3).foldlM c.chainF acc := by
  simp [threeSource,appendSource,NCtx.chainF,index,List.range',List.foldlM,bind_assoc,pure_bind]

def all54Source (c : NCtx) : M (List Digest) :=
  (List.range' 0 54).foldlM c.chainF []

theorem all54_split (c : NCtx) : all54Source c=
    (List.range' 0 51).foldlM c.chainF [] >>= threeSource c := by
  unfold all54Source
  rw [show (54 : Nat)=51+3 from rfl,←List.range'_append_1,List.foldlM_append]
  congr 1
  funext a
  exact (threeSource_eq_tail_fold c a).symm

theorem tail_input (c : NCtx) (s0 : MachineState) (acc : List Digest) (s : MachineState)
    (hs : c.ChainIn s0 51 acc s) : Input c s0 (c.kOf 17) 0 acc s := by
  simpa only [Input,index,Nat.add_zero,chainPC,List.range_zero,List.map_nil,List.sum_nil,
    NCtx.ChainIn,NCtx.startPc,Nat.reduceMod,if_true,Nat.reduceDiv,entW,if_false,Nat.reduceLT,armPC]
    using hs

theorem tail_digits (c : NCtx) (hd : c.DigitsOk) :
    ∀ o,o<3  →  c.dig (index o)=digit (c.kOf 17) o := by
  have h:=c.kOf_digits hd 17 (by decide)
  have h2:=c.dig_group_le hd 17 2 (by decide) (by decide)
  simp only [mx,Nat.reduceLT,if_false,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow] at h h2
  intro o ho
  interval_cases o <;> simp only [index,digit,Nat.reduceAdd,Nat.reducePow,Nat.div_one]
  · exact h.1.symm
  · exact h.2.1.symm
  · rw [h.2.2,Nat.mod_eq_of_lt (by omega)]

def all54Cost (c : NCtx) : Nat := c.chainsCost 0 51+64+3+threeNativeCost c

theorem all54_good (c : NCtx) (hc : c.ok) (s0 : MachineState) (v : Digest)
    (hk : ∀ p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : NCtx.Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (hranks : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec Judg.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ t0 ends u,LeafReady c (NCtx.tailInitial s0 t0) (c.kOf 17) ends u  → 
      Judg.GoodQ image u N C Q A (K ends))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Judg.GoodQ image s (N+2231) (C+all54Cost c) Q (A+all54Cost c)
      (Judg.ccM (all54Source c) K) := by
  have hd:=c.fit_digits hf
  have hw:=c.prefix_windows hd
  have hr : c.kOf 17<64 := by
    have hh:=c.kOf_lt hd 17 (by decide)
    simpa only [mx,Nat.reduceLT,if_false,Nat.reduceAdd,Nat.reducePow] using hh
  rw [all54_split,Judg.ccM_bind]
  have H:=c.prefix_fiftyone_good hw hc hk h0 he hf hranks
    (fun acc=>Judg.ccM (threeSource c acc) K) (N+123)
    (C+threeNativeCost c+3) (A+threeNativeCost c+3) Q
    (fun acc t ht=>by
      obtain ⟨u,st,hi,h15⟩:=c.prefix_end_tail hw hc hd he hf hv acc t ht
      have H:=three_good c hc (NCtx.tailInitial s0 u)
        (c.tailInitial_known hk) (c.tailInitial_orig h0) (c.kOf 17) hr
        (tail_digits c hd) acc K N C A Q (hK u) u (tail_input c _ acc u hi)
      simpa only [Nat.add_assoc] using H.steps st)
    17 0 (by decide) (by decide) [] s hs
  simpa [all54Cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H

theorem all54_leaf_good (c : NCtx) (hc : c.ok) (s0 : MachineState) (v : Digest)
    (hk : ∀ p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : NCtx.Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (hranks : topRanksValid v=true)
    (h23 : s0.getReg .x23=BitVec.ofNat 64 (4096+c.leaf))
    (K : Digest → OracleComp Legacy.HashSpec Judg.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ t0 ends u,LeafReady c (NCtx.tailInitial s0 t0) (c.kOf 17) ends u →
      ∀ a : BitVec 256,Judg.GoodQ image
        (writeHash ((bankResult (c.leaf%64)).toState (leafResult.toState u)) a)
        N C Q A (K (a.extractLsb' 0 128)))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Judg.GoodQ image s (N+2245) (C+all54Cost c+125) Q (A+all54Cost c+125)
      (Judg.ccM (all54Source c >>= fun ends=>leafHash 0 c.tree c.leaf ends) K) := by
  rw [Judg.ccM_bind]
  have hd:=c.fit_digits hf
  have hr : c.kOf 17<64 := by
    have hh:=c.kOf_lt hd 17 (by decide)
    simpa only [mx,Nat.reduceLT,if_false,Nat.reduceAdd,Nat.reducePow] using hh
  have H:=all54_good c hc s0 v hk h0 he hf hv hranks
    (fun ends=>Judg.ccM (leafHash 0 c.tree c.leaf ends) K) (N+14) (C+125) (A+125) Q
    (fun t0 ends u hu=>by
      have hx : (NCtx.tailInitial s0 t0).getReg .x23=BitVec.ofNat 64 (4096+c.leaf) :=
        (NCtx.tailInitial_regs s0 t0 .x23 (by decide)).trans h23
      exact leaf_hash_good_exact c hc (NCtx.tailInitial s0 t0) (c.tailInitial_known hk)
        hx (c.kOf 17) hr ends u hu K N C A Q (hK t0 ends u hu)) s hs
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H

#print axioms all54_good
#print axioms all54_leaf_good
end SigGolfCandidate.T3M.Nonbinary.InlineTail
