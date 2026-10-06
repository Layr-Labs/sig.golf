import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTopJoin
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineLeafOut
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineMerkleSem

/- Connected all54-to-Merkle source stage.  Endpoint/data invariants are
   derived from the proved chain frame, then the actual twelve leaf setup
   instructions.  The Merkle stage alone charges bank1 and leafHASH14. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3 SigGolfCandidate.T3M.Verify
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem leaf_data_of_base (c : NCtx) (pk : Digest) (index : Nat) (hc : c.ok)
    (hroute : (c.leaf,c.tree) = route index 0) (hS3 : c.S3 = s3v)
    (s0 s : MachineState) (ends : List Digest)
    (hk : KnownOK c.known s0) (hg : Glob baseK c.w pk s0)
    (hkeep : KnownOK (lfKeepK 0) s0) (h15 : s0.getReg .x15 = 0xae000)
    (h23 : s0.getReg .x23 = BitVec.ofNat 64 (4096+c.leaf))
    (ho : Orig c.w (fun o => 9288 ≤ o ∧ o < layerBase 0 + 64 * height 0) s0)
    (hs : c.Base s0 (c.Wr 54) ends s) (hlen : ends.length=54) :
    LeafData c.w pk index ends s := by
  obtain ⟨hR,hF,hD⟩ := hs
  have hr (r : Reg) (hn : r ∉ chainRegs) := hR r hn
  have hleaf : c.leaf=(route index 0).1 := congrArg Prod.fst hroute
  have htree : c.tree=(route index 0).2 := congrArg Prod.snd hroute
  have hknown : KnownOK (leafK 0) s := by
    intro p hp
    simp [leafK,baseK] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (hr .x5 (by decide)).trans (hg.1 (.x5,0) (by simp [baseK]))
    · exact (hr .x18 (by decide)).trans (hg.1 (.x18,0xfff) (by simp [baseK]))
    · exact (hr .x27 (by decide)).trans (hk (.x27,1025#64) (by simp [NCtx.known]))
    · exact (hr .x15 (by decide)).trans h15
  have hglob : Glob (leafK 0) c.w pk s := glob_frame hg hF (by
    intro A h
    have hhi := hc.2.2.2.2.1
    have hlo := hc.2.2.2.1
    unfold NCtx.Wr NCtx.blk at h
    rcases h with h | h <;> omega) hknown
  refine ⟨hglob, ?_, ?_, ?_, hlen, ?_, ?_⟩
  · intro p hp
    have hn : p.1 ∉ chainRegs := by
      simp [lfKeepK] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hr p.1 hn).trans (hkeep p hp)
  · rw [hr .x23 (by decide),h23,hleaf]
  · rw [hr .x4 (by decide),hk (.x4,BitVec.ofNat 64 c.w1) (by simp [NCtx.known])]
    simp only [NCtx.w1,hleaf,htree]
  · intro j hj
    simpa [slot,slotT] using hD j (by omega)
  · exact ho.frame (fun j hj hp => hF.get (by unfold WIT WX at *;omega) (by
      intro h
      unfold NCtx.Wr NCtx.blk at h
      rw [hS3] at h
      have hb : layerBase (0:Layer)+64*height (0:Layer)=10056 := by decide +kernel
      rw [hb] at hp
      norm_num [s3v] at h
      unfold WIT at *
      omega))

def TopMerkleEnd (w : WBytes) (pk : Digest) (index : Nat)
    (ends : List Digest) (root : Digest) (t : MachineState) : Prop :=
  ∃ u, LeafOut w pk index 0 ends u ∧ Merkle.MkStop w pk 0 (route index 0).1 u root t

theorem all54_good_with_heap (c : NCtx) (hc : c.ok) (s0 : MachineState) (v : Digest)
    (hk : ∀ p∈c.known,s0.getReg p.1=p.2) (h0 : c.Orig0 s0)
    (he : NCtx.Encoded v s0) (hf : c.Fit v) (hv : v.toNat<2^125)
    (hranks : topRanksValid v=true)
    (K : List Digest → OracleComp Legacy.HashSpec Judg.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ t0 ends u,t0.getReg .x15=0xae000 → LeafReady c (NCtx.tailInitial s0 t0) (c.kOf 17) ends u  → 
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
        (tail_digits c hd) acc K N C A Q (fun a t ht => hK u a t h15 ht) u (tail_input c _ acc u hi)
      simpa only [Nat.add_assoc] using H.steps st)
    17 0 (by decide) (by decide) [] s hs
  simpa [all54Cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H

def topSource (c : NCtx) (index : Nat) : M Digest := do
  let ends ← all54Source c
  let leaf ← leafHash 0 c.tree c.leaf ends
  Merkle.merklePrefix c.w index 0 leaf

theorem top_good (c : NCtx) (pk : Digest) (index : Nat) (hc : c.ok)
    (hidx : index < 2^31) (hroute : (c.leaf,c.tree)=route index 0) (hS3 : c.S3=s3v)
    (s0 : MachineState) (v : Digest) (hk : KnownOK c.known s0)
    (hg : Glob baseK c.w pk s0) (hkeep : KnownOK (lfKeepK 0) s0)
    (h23 : s0.getReg .x23=BitVec.ofNat 64 (4096+c.leaf))
    (ho : Orig c.w (fun o => 9288 ≤ o ∧ o < layerBase 0+64*height 0) s0)
    (h0 : c.Orig0 s0) (he : NCtx.Encoded v s0) (hf : c.Fit v)
    (hv : v.toNat<2^125) (hranks : topRanksValid v=true)
    (K : Digest → OracleComp Legacy.HashSpec Judg.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends root t, TopMerkleEnd c.w pk index ends root t →
      Judg.GoodQ image t N C Q A (K root))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    Judg.GoodQ image s (N+2231+12+Merkle.mkFuel 0)
      (C+all54Cost c+12+Merkle.mkCyc 0) Q (A+all54Cost c+12+Merkle.mkCyc 0)
      (Judg.ccM (topSource c index) K) := by
  have hd := c.fit_digits hf
  have hr : c.kOf 17<64 := by
    have h := c.kOf_lt hd 17 (by decide)
    simpa only [mx,Nat.reduceLT,if_false,Nat.reduceAdd,Nat.reducePow] using h
  have hleaf : c.leaf=(route index 0).1 := congrArg Prod.fst hroute
  have htree : c.tree=(route index 0).2 := congrArg Prod.snd hroute
  unfold topSource
  rw [Judg.ccM_bind]
  have H := all54_good_with_heap c hc s0 v hk h0 he hf hv hranks
    (fun ends => Judg.ccM (leafHash 0 c.tree c.leaf ends >>= Merkle.merklePrefix c.w index 0) K)
    (N+12+Merkle.mkFuel 0) (C+12+Merkle.mkCyc 0) (A+12+Merkle.mkCyc 0) Q
    (fun t0 ends u hheap hu => by
      let b := NCtx.tailInitial s0 t0
      have fb : Frame s0 b (fun _ => False) := by intro A hA hn; exact NCtx.tailInitial_mem s0 t0 _
      have hgb : Glob baseK c.w pk b := glob_frame hg fb (by intro A h; contradiction) (by
        intro p hp; simp [baseK] at hp
        rcases hp with rfl | rfl <;> rw [NCtx.tailInitial_regs _ _ _ (by decide)]
        · exact hg.1 (.x5,0) (by simp [baseK])
        · exact hg.1 (.x18,0xfff) (by simp [baseK]))
      have hkb : KnownOK (lfKeepK 0) b := by
        intro p hp
        have hn : p.1≠.x15 := by
          simp [lfKeepK] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact (NCtx.tailInitial_regs s0 t0 p.1 hn).trans (hkeep p hp)
      have hb23 : b.getReg .x23=BitVec.ofNat 64 (4096+c.leaf) :=
        (NCtx.tailInitial_regs s0 t0 .x23 (by decide)).trans h23
      have hbo : Orig c.w (fun o => 9288 ≤ o ∧ o < layerBase 0+64*height 0) b :=
        ho.frame (fun _ _ _ => NCtx.tailInitial_mem s0 t0 _)
      have hdata := leaf_data_of_base c pk index hc hroute hS3 b u ends
        (c.tailInitial_known hk) hgb hkb ((NCtx.tailInitial_15 s0 t0).trans hheap) hb23 hbo hu.1 hu.2.1
      obtain ⟨z,hst,hz⟩ := leafout_steps c.w pk index (c.kOf 17) hidx hr ends u hu.2.2 hdata
      have hm := Merkle.merkle_good c.w pk index 0 ends z hidx hz K N C A Q
        (fun root t ht => hK ends root t ⟨z,hz,ht⟩)
      rw [←htree,←hleaf] at hm
      have hh := hm.steps hst
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh) s hs
  convert H using 1 <;> first | omega | rfl

#print axioms leaf_data_of_base
#print axioms top_good
end SigGolfCandidate.T3M.Nonbinary.InlineTail
