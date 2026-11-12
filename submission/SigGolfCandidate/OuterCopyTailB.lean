import SigGolfCandidate.OuterCopyGroundB
import SigGolfCandidate.OuterNodeBankTailB
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCopyTailB
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedBProof
open SigGolfCandidate.FtsGrind
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

theorem tail_eq (coord index j : Nat) (pads sibs tws pads' sibs' tws' : Nat→Digest)
    (hp : ∀ l,l=4 ∨ l=5→pads' l=pads l) (hs : ∀ l,l=4 ∨ l=5→sibs' l=sibs l) (v : Digest) :
    OuterNodeBankTailB.program coord index j 4 1 pads' sibs' tws' v=
      OuterNodeBankTailB.program coord index j 4 1 pads sibs tws v := by
  simp only [OuterNodeBankTailB.program,show List.range' 4 1=[4] from rfl,List.foldlM_cons,List.foldlM_nil,bind_pure,
    childLevelP,hpOf,show ¬(4:Nat)<4 by decide,if_false,hp 4 (Or.inl rfl),hs 4 (Or.inl rfl),hs 5 (Or.inr rfl)]

def Post (coord index j : Nat) (pads sibs : Nat→Digest) (u : MachineState) (res : Nat×Nat×Digest) (t : MachineState) : Prop :=
  ∃ (mid : MachineState) (v4 : Digest) (u' : MachineState),
    OuterCopyGroundB.Post (coordRegion coord) coord index j pads sibs u (res.1,v4) mid ∧
    u'=virt j (coordRegion coord) u mid ∧ (∀ r,u'.getReg r=u.getReg r) ∧
    Frame u u' (OuterCopyGroundB.Changes (coordRegion coord) j) ∧
    OuterNodeHandFinishB.Post coord j u' res.2 t

def program (coord index j : Nat) (pads sibs tws : Nat→Digest) (v : Digest) : M (Nat×Nat×Digest) := do
  let r←groundFold (widthOf (coordRegion coord)) (preC coord index j tws sibs v) (rightC j sibs v)
  let out←OuterNodeBankTailB.program coord index j 4 1 pads sibs tws (r.2.extractLsb' 0 128)
  pure (r.1,out)

theorem run {im : Image} {sk : BitVec 256} (j : Fin 128) (coord : Fin 9) (index : Nat)
    (hc1 : 1≤coord.val) (hc8 : coord.val≠8) (hi : index<2^31)
    (hcode : CopyCodeAt im j.val)
    (hc : CodeAt im (pcOf (childBase j.val)) (OuterNodeBankLayout.bWords j.val))
    (hS : CodeAt im (pcOf SEARCH) searchWords)
    (hT : CodeAt im (pcOf (trampOf j.val)) (trampWords (trampOf j.val) SEARCH (siteB j.val+1)))
    {leaf pads sibs tws : Nat→Digest} {u s : MachineState}
    (hu : ChildPre j.val (coordRegion coord.val) coord.val index leaf pads sibs tws u)
    (hlo : 1848≤coordRegion coord.val) (hB : coordRegion coord.val<2^14)
    (v : Digest) (hs : MidC j.val (coordRegion coord.val) coord.val index u 3 v s) :
    TBSim im sk s (lvlSt j.val 3+1+W_SEARCH (widthOf (coordRegion coord.val))+(cycR j.val 4 1+30740))
      (program coord.val index j.val pads sibs tws v) (Post coord.val index j.val pads sibs u) := by
  have hG:=OuterCopyGroundB.run (sk:=sk) j.isLt hcode hS hT hu hlo hB v s hs
  have h : TBSim im sk s (lvlSt j.val 3+1+W_SEARCH (widthOf (coordRegion coord.val))+(cycR j.val 4 1+30740))
      ((groundFold (widthOf (coordRegion coord.val)) (preC coord.val index j.val tws sibs v) (rightC j.val sibs v) >>=
        fun r=>pure (r.1,r.2.extractLsb' 0 128)) >>= fun r=>
          OuterNodeBankTailB.program coord.val index j.val 4 1 pads sibs tws r.2 >>= fun out=>pure (r.1,out))
      (Post coord.val index j.val pads sibs u) := by
    refine TBSim.bind hG ?_
    intro r mid hground
    have hg:=hground
    obtain ⟨u',leaf',pads',sibs',tws',hpre,hmid,hvirt,hregs,hframe,hpads,hsibs,_⟩:=hground
    have ht:=OuterNodeBankTailB.run (sk:=sk) j coord index hc1 hc8 hi hc hpre 1 4 r.2 rfl hmid
    rw [tail_eq coord.val index j.val pads sibs tws pads' sibs' tws' hpads hsibs r.2] at ht
    have hh:=TBSim.bind ht (fun out t hout=>TBSim.pure (a:=(r.1,out)) (Q:=Post coord.val index j.val pads sibs u)
      ⟨mid,r.2,u',hg,hvirt,hregs,hframe,hout⟩)
    simpa only [Nat.add_zero] using hh
  simpa only [program,bind_assoc,pure_bind] using h

#print axioms tail_eq
#print axioms run
end OuterCopyTailB
