import SigGolfCandidate.OuterSignNode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignTree
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open ClaudeWCT ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedTree
variable {sk : BitVec 256}
def Writes (A : Nat) : Prop := treeW A ∨ A=1152 ∨ A=1160
def stepProgram (index c : Nat) (pads : Nat→Digest) (nodes : Array Digest) (heap : Nat) : M (Array Digest) := do
  let value←OuterSignNodeModel.hashProgram c index heap (pads heap) (nodes.getD (2*heap) 0) (nodes.getD (2*heap+1) 0)
  pure (nodes.set! heap value)

def heapProgram (index c : Nat) (pads : Nat→Digest) (leaves : List Digest) : M (Array Digest) :=
  (List.range' 0 (count c)).foldlM (fun nodes k=>stepProgram index c pads nodes (127-k))
    ((List.replicate 128 (0:Digest)++leaves).toArray)

structure Inv (c index : Nat) (s0 : MachineState) (k : Nat) (nodes : Array Digest) (t : MachineState) : Prop where
  pc : t.pc=pcOf (if k<count c then SharedNode.entry c else SharedTail.finishPc c)
  x5 : t.getReg .x5=0
  x18 : t.getReg .x18=BitVec.ofNat 64 (127-k)
  x22 : t.getReg .x22=BitVec.ofNat 64 index
  size : nodes.size=256
  heap : ∀ m, 127-k < m → m < 256 → DigAt t (HEAPW+16*m) (nodes.getD m 0)
  regs : RegsExcept s0 t [.x3,.x6,.x7,.x10,.x11,.x12,.x18,.x28,.x29]
  frame : Frame s0 t Writes

theorem pad_treeFrame {c h : Nat} {pad : Digest} {s t : MachineState}
    (hp:SharedNode.PadAt c h pad s) (hc:c<9) (hf:Frame s t Writes) : SharedNode.PadAt c h pad t := by
  unfold SharedNode.PadAt at hp ⊢
  split_ifs at hp ⊢ with hm
  · have hb:=padBase_bound hc (SharedNode.mode_one hm.1)
    exact hp.frame hf (by rcases hb with hb|hb <;> omega)
      (by unfold Writes treeW;intro hw;rcases hb with hb|hb <;> aoh)
      (by unfold Writes treeW;intro hw;rcases hb with hb|hb <;> aoh)
  · exact hp


theorem unitWrites_writes {h A : Nat} (hh1:1≤h) (hh:h<128) (hu:OuterSignNode.UnitWrites h A) : Writes A := by
  rcases hu with hu|hu|hu
  · exact Or.inl (unitW_treeW hh1 hh hu)
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr hu)

theorem saveCell_writes {A : Nat} (ha:SharedNode.saveCell A) : ¬Writes A := by
  have hn:=saveCell_treeW ha
  intro hw
  rcases hw with hw|hw|hw
  · exact hn hw
  all_goals unfold SharedNode.saveCell at ha;omega

theorem step {c index : Nat} (hn:LookOK OuterImages.signImage (SharedNode.look c)) (ht:LookOK OuterImages.signImage (SharedTail.look c))
    (hc:c<9) (hi:index<2^31) {s0 : MachineState} {pads : Nat→Digest}
    (hpad:∀h,h<128→SharedNode.PadAt c h (pads h) s0) (hz:SharedNode.SaveZ s0)
    (k : Nat) (hk:k<count c) (nodes : Array Digest) (t : MachineState) (h:Inv c index s0 k nodes t) :
    TBSim OuterImages.signImage sk t (SharedNode.unitC+77865) (stepProgram index c pads nodes (127-k)) (Inv c index s0 (k+1)) := by
  have hl:=limit_bounds c
  have hk127:k<127:=by unfold count at hk;omega
  have hh1:1≤127-k:=by omega
  have hh:127-k<128:=by omega
  have hpc:t.pc=pcOf (SharedNode.entry c):=by rw[h.pc,if_pos hk]
  have hp:SharedNode.PadAt c (127-k) (pads (127-k)) t:=
    pad_treeFrame (hpad _ hh) hc h.frame
  unfold stepProgram
  refine (TBSim.bind (W₂:=0) (OuterSignNode.hash_unit hn ht (by
      intro hfirst
      unfold count SharedTail.limit at hk
      rw [if_pos hfirst] at hk
      omega) hc hi hh1 hh (by unfold count at hk; omega) hpc h.x5 h.x18 h.x22
    (h.heap _ (by omega) (by omega)) (h.heap _ (by omega) (by omega)) hp
    (hz.frame h.frame (fun _ ha=>saveCell_writes ha)))
    (fun value u hu=>TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
  obtain ⟨upc,u18,uv,ur,uf⟩:=hu
  refine ⟨?_,?_,?_,?_,?_,fun m hm1 hm2=>?_,(h.regs.trans ur).mono (by simp),?_⟩
  · rw[upc,nodePc_entry c hc]
    congr 1
    unfold count at *
    split_ifs <;> first | rfl | omega
  · rw[ur.get (by simp)];exact h.x5
  · rw[u18,show 127-k-1=127-(k+1) by omega]
  · rw[ur.get (by simp)];exact h.x22
  · simp[h.size]
  · by_cases hm:m=127-k
    · subst m
      rw[WCT9.getD_set_self _ _ _ (by rw[h.size];omega)]
      exact uv
    · rw[WCT9.getD_set_other _ _ _ _ (fun he=>hm he.symm)]
      refine (h.heap m (by omega) hm2).frame uf (by ao) ?_ ?_
      all_goals unfold OuterSignNode.UnitWrites SharedNode.unitW SharedNode.writes
      all_goals rintro ((⟨j,hj,he⟩|he|he|he)|he|he) <;> aoh
  · exact (h.frame.trans uf).mono (fun A _ ha=>ha.elim id (unitWrites_writes hh1 hh))

theorem heap_loop {c index : Nat} (hn:LookOK OuterImages.signImage (SharedNode.look c)) (ht:LookOK OuterImages.signImage (SharedTail.look c))
    (hc:c<9) (hi:index<2^31) {s0 : MachineState} {pads : Nat→Digest} {leaves : List Digest}
    (hpad:∀h,h<128→SharedNode.PadAt c h (pads h) s0) (hz:SharedNode.SaveZ s0)
    (h0:Inv c index s0 0 ((List.replicate 128 (0:Digest)++leaves).toArray) s0) :
    TBSim OuterImages.signImage sk s0 (count c*(SharedNode.unitC+77865)) (heapProgram index c pads leaves) (Inv c index s0 (count c)) := by
  unfold heapProgram
  exact TBSim.foldlM_range' 0 (count c) _ _ (Inv c index s0) (SharedNode.unitC+77865)
    (fun k hk nodes t ht'=>by
      simp only[Nat.zero_add]
      exact step hn ht hc hi hpad hz k hk nodes t ht') h0
#print axioms step
#print axioms heap_loop
end OuterSignTree
