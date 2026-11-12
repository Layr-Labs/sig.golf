import SigGolfCandidate.OuterSignTree
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignCoordinate
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest)
open ClaudeWCT ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open ClaudeWCT.W9.Machine.Sign.SharedReuse (coefW coefRegs coefStepC)
variable {sk : BitVec 256}
def rowsHeap (index c sel : Nat) (word : WCT9.Rank) (coefs : List Digest)
    (leftPads rightPads : Nat→Digest) : M (Array Digest×List Digest) := do
  let rows←SharedLeaves.leafRows index c sel word coefs leftPads
  let nodes←OuterSignTree.heapProgram index c rightPads rows.1
  pure (nodes,rows.2)
def writes (c A : Nat) : Prop := SharedCoordinate.writes c A ∨ A=1152 ∨ A=1160
structure Post (sk : BitVec 256) (c index sel w : Nat) (s0 : MachineState) (rv : Array Digest×List Digest) (t : MachineState) : Prop where
  tree : SharedTree.Inv c index t (SharedTree.count c) rv.1 t
  values : rv.2.length=6 ∧ ∀i,i<6→DigAt t (slotV c i) (rv.2.getD i 0)
  x24 : t.getReg .x24=BitVec.ofNat 64 (SharedNext.raw c sel)
  regs : RegsExcept s0 t (.x18::bodyRegs)
  frame : Frame s0 t (writes c)
theorem rows_heap (hf:SharedReuse.Fetch OuterImages.signImage) {c index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hl:LookOK OuterImages.signImage (SharedLeaf.look c)) (hh:LookOK OuterImages.signImage (SharedLeaf.hookLook c))
    (hn:LookOK OuterImages.signImage (SharedNext.look c)) (hnode:LookOK OuterImages.signImage (SharedNode.look c)) (ht:LookOK OuterImages.signImage (SharedTail.look c))
    (hc:c < 9) (hsel:sel < 128) (hi:index < 2^31) (hw:w < 2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i) (hlen:coefs.length=42)
    {s : MachineState} (hcoef:ClaudeWCT.W9.Machine.Sign.SharedReuse.CoefAt s coefs) {leftPads rightPads : Nat → Digest}
    (hpadL:∀j, j < 128  →  SharedLeaf.PadAt c (SharedNext.raw c j) (leftPads j) s)
    (hpadR:∀h, h < 128  →  SharedNode.PadAt c h (rightPads h) s)
    (hpc:s.pc=pcOf (leafI c)) (hb:BodySt sk 0 index (SharedNext.raw c sel) w s) (hz:SharedNode.SaveZ s) :
    TBSim OuterImages.signImage sk s (128*SharedLeaves.cost+SharedTree.count c*(SharedNode.unitC+77865))
      (rowsHeap index c sel word coefs leftPads rightPads) (Post sk c index sel w s) := by
  unfold rowsHeap
  refine TBSim.bind (SharedLeaves.leaf_loop hf hl hh hn hc hsel hi hw hword hlen hcoef hpadL (SharedLeaves.Inv.init hpc hb))
    (fun rows u hu=>?_)
  have hupc:u.pc=pcOf (SharedNode.entry c):=by rw[hu.pc,if_neg (by omega),nextNode_eq c hc]
  have hub:BodySt sk 127 index (SharedNext.raw c sel) w u:=by have:=hu.body;rwa[if_neg (by omega)]at this
  have countpos:0 < SharedTree.count c:=by have:=SharedTree.limit_bounds c;unfold SharedTree.count;omega
  have h0:OuterSignTree.Inv c index u 0 ((List.replicate 128 (0:Digest)++rows.1).toArray) u:=
    ⟨by rw[if_pos countpos];exact hupc,hub.x5,hub.x18,hub.x22,by simp[hu.len],
      fun m hm1 hm2=>by
        rw[initial_heap_getD _ _ (by omega)]
        have hd:=hu.leaves (m-128) (by omega)
        rwa[show 128+(m-128)=m by omega]at hd,
      RegsExcept.refl _ _,Frame.refl _ _⟩
  have hzu:SharedNode.SaveZ u:=hz.frame hu.frame (fun A ha hw=>by
    unfold SharedNode.saveCell at ha;unfold loopW bodyW at hw;rcases ha with ha|ha|ha|ha <;> (subst ha;aoh))
  refine (TBSim.bind (W₂:=0) (OuterSignTree.heap_loop hnode ht hc hi (fun h hh=>pad_leafFrame (hpadR h hh) hc hu.frame) hzu h0)
    (fun nodes t ht'=>TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
  obtain ⟨hlen,hvals⟩:=hu.vals hsel
  refine ⟨?_,⟨hlen,fun i hi=>?_⟩,?_,?_,?_⟩
  · exact ⟨ht'.pc,ht'.x5,ht'.x18,ht'.x22,ht'.size,ht'.heap,RegsExcept.refl _ _,Frame.refl _ _⟩
  · exact (hvals i hi).frame ht'.frame (by unfold slotV;ao)
      (by unfold OuterSignTree.Writes treeW slotV;intro h;aoh) (by unfold OuterSignTree.Writes treeW slotV;intro h;aoh)
  · rw[ht'.regs.get (by simp)];exact hub.x24
  · exact (hu.regs.trans ht'.regs).mono (by simp[bodyRegs])
  · exact (hu.frame.trans ht'.frame).mono (by
      intro A hA ha
      unfold writes ClaudeWCT.W9.Machine.Sign.SharedCoordinate.writes OuterSignTree.Writes at *
      tauto)

def allWrites (c A : Nat) : Prop := writes c A ∨ FinalWrites c A
structure Out (c index : Nat) (s0 : MachineState) (rv : Array Digest×List Digest)
    (sel : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (SharedEnd.nextPc c)
  x5 : t.getReg .x5=0
  x22 : t.getReg .x22=BitVec.ofNat 64 index
  size : rv.1.size=256
  roots : RootAt c rv.1 t
  values : rv.2.length=6 ∧ ∀i, i < 6 → DigAt t (slotV c i) (rv.2.getD i 0)
  paths : ∀l, l < SharedPath.levels c → DigAt t (SharedPath.target c l) (rv.1.getD (2^(7-l)+(sel/2^l ^^^1)) 0)
  dummy : SharedEnd.first c=true → DigAt t (SharedEnd.target c) 0
  regs : RegsExcept s0 t (.x24::.x18::bodyRegs)
  frame : Frame s0 t (allWrites c)

theorem rows_finish (hf:SharedReuse.Fetch OuterImages.signImage) {c index sel w : Nat} {word : WCT9.Rank} {coefs : List Digest}
    (hl:LookOK OuterImages.signImage (SharedLeaf.look c)) (hh:LookOK OuterImages.signImage (SharedLeaf.hookLook c))
    (hn:LookOK OuterImages.signImage (SharedNext.look c)) (hnode:LookOK OuterImages.signImage (SharedNode.look c)) (ht:LookOK OuterImages.signImage (SharedTail.look c))
    (hfinish:LookOK OuterImages.signImage (SharedFinish.look c)) (hpath:LookOK OuterImages.signImage (SharedPath.look c)) (hend:LookOK OuterImages.signImage (SharedEnd.look c))
    (hc:c < 9) (hsel:sel < 128) (hi:index < 2^31) (hw:w < 2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i) (hlen:coefs.length=42)
    {s : MachineState} (hcoef:ClaudeWCT.W9.Machine.Sign.SharedReuse.CoefAt s coefs) {leftPads rightPads : Nat → Digest}
    (hpadL:∀j, j < 128 → SharedLeaf.PadAt c (SharedNext.raw c j) (leftPads j) s)
    (hpadR:∀h, h < 128 → SharedNode.PadAt c h (rightPads h) s)
    (hpc:s.pc=pcOf (leafI c)) (hb:BodySt sk 0 index (SharedNext.raw c sel) w s) (hz:SharedNode.SaveZ s) :
    TBSim OuterImages.signImage sk s (128*SharedLeaves.cost+SharedTree.count c*(SharedNode.unitC+77865)+110)
      (rowsHeap index c sel word coefs leftPads rightPads) (fun rv t=>Out c index s rv sel t) := by
  have hrun:=rows_heap hf hl hh hn hnode ht hc hsel hi hw hword hlen hcoef hpadL hpadR hpc hb hz
  have h: TBSim OuterImages.signImage sk s (128*SharedLeaves.cost+SharedTree.count c*(SharedNode.unitC+77865)+110)
      (rowsHeap index c sel word coefs leftPads rightPads >>= pure) (fun rv t=>Out c index s rv sel t):=by
    refine TBSim.bind hrun (fun rv u hu=>?_)
    obtain ⟨t,n,st,hn,tpc,roots,paths,dummy,regs,frame⟩:=finish hfinish hpath hend hc hsel u
      (by simpa only[if_neg (Nat.lt_irrefl _)]using hu.tree.pc) hu.x24
      (fun m hm hm2=>hu.tree.heap m (by unfold SharedTree.count;have:=SharedTree.limit_bounds c;omega) hm2)
    refine (TBSim.steps st (TBSim.pure ?_)).mono (by omega) (fun _ _ h=>h)
    refine ⟨tpc,?_,?_,hu.tree.size,roots,⟨hu.values.1,?_⟩,paths,dummy,?_,?_⟩
    · rw[regs.get (by simp)];exact hu.tree.x5
    · rw[regs.get (by simp)];exact hu.tree.x22
    · intro i hi;exact value_frame hc hi (hu.values.2 i hi) frame
    · exact (hu.regs.trans regs).mono (by simp[bodyRegs])
    · exact (hu.frame.trans frame).mono (fun A _ h=>h)
  simpa only[bind_pure]using h
def program (index c sel : Nat) (word : WCT9.Rank) (leftPads rightPads : Nat → Digest) : M (Array Digest×List Digest) := do
  let coefs←WCT9.ftsCoefs index c
  rowsHeap index c sel word coefs leftPads rightPads

def coordinateW (c A : Nat) : Prop := coefW A ∨ allWrites c A
structure FullOut (c index : Nat) (s0 : MachineState) (rv : Array Digest×List Digest)
    (sel : Nat) (t : MachineState) : Prop where
  out : Out c index t rv sel t
  regs : RegsExcept s0 t (.x25::.x24::.x18::bodyRegs)
  frame : Frame s0 t (coordinateW c)

theorem coefs_rows_finish (hf:SharedReuse.Fetch OuterImages.signImage) {c old index sel w : Nat} {word : WCT9.Rank}
    (hl:LookOK OuterImages.signImage (SharedLeaf.look c)) (hh:LookOK OuterImages.signImage (SharedLeaf.hookLook c))
    (hn:LookOK OuterImages.signImage (SharedNext.look c)) (hnode:LookOK OuterImages.signImage (SharedNode.look c)) (ht:LookOK OuterImages.signImage (SharedTail.look c))
    (hfinish:LookOK OuterImages.signImage (SharedFinish.look c)) (hpath:LookOK OuterImages.signImage (SharedPath.look c)) (hend:LookOK OuterImages.signImage (SharedEnd.look c))
    (hc:c < 9) (hsel:sel < 128) (hi:index < 2^31) (hw:w < 2^64)
    (hword:∀i:Fin 6,w/8^i.val%8=WCT9.wordDigit word i)
    {s : MachineState} {leftPads rightPads : Nat → Digest}
    (hpadL:∀j, j < 128 → SharedLeaf.PadAt c (SharedNext.raw c j) (leftPads j) s)
    (hpadR:∀h, h < 128 → SharedNode.PadAt c h (rightPads h) s)
    (hpc:s.pc=pcOf (lwuI c+1)) (hb:BodySt sk old index (SharedNext.raw c sel) w s) (hz:SharedNode.SaveZ s) :
    TBSim OuterImages.signImage sk s (14+21*coefStepC+(128*SharedLeaves.cost+SharedTree.count c*(SharedNode.unitC+77865)+110))
      (program index c sel word leftPads rightPads) (fun rv t=>FullOut c index s rv sel t) := by
  unfold program
  refine TBSim.bind (SharedReuse.coefs_unit hf hc hi hpc hb) (fun coefs u hu=>?_)
  obtain ⟨upc,ub,ulen,ucoefs,ur,uf⟩:=hu
  have hzu:SharedNode.SaveZ u:=hz.frame uf (fun A ha hw=>by
    unfold SharedNode.saveCell at ha;unfold SharedReuse.coefW at hw;rcases ha with ha|ha|ha|ha <;> (subst ha;simp only [COEF] at hw;aoh))
  refine (rows_finish hf hl hh hn hnode ht hfinish hpath hend hc hsel hi hw hword ulen ucoefs
    (fun j hj=>padL_coefFrame (hpadL j hj) hc (SharedNext.raw_lt c hj) uf)
    (fun h hh=>padR_coefFrame (hpadR h hh) hc uf) upc ub hzu).mono le_rfl (fun rv t ht=>?_)
  refine ⟨⟨ht.pc,ht.x5,ht.x22,ht.size,ht.roots,ht.values,ht.paths,ht.dummy,RegsExcept.refl _ _,Frame.refl _ _⟩,?_,?_⟩
  · exact (ur.trans ht.regs).mono (by simp[coefRegs,bodyRegs])
  · exact (uf.trans ht.frame).mono (fun A _ h=>h)
#print axioms rows_finish
#print axioms coefs_rows_finish

#print axioms rows_heap
end OuterSignCoordinate
