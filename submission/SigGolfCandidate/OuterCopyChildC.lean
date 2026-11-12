import SigGolfCandidate.OuterCopyLayer2C
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCopyChildC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedCProof
open SigGolfCandidate.FtsGrind
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

theorem tail_eq (coord index j : Nat) (pads pads2 sibs tws : Nat→Digest)
    (hp : ∀ l,l≠2→pads2 l=pads l) (v : Digest) :
    OuterCopyTailC.program coord index j pads2 sibs tws v=OuterCopyTailC.program coord index j pads sibs tws v := by
  unfold OuterCopyTailC.program
  congr 1
  funext r
  rw [OuterCopyTailC.tail_eq coord index j pads sibs tws pads2 sibs tws
    (fun l hl=>hp l (by rcases hl with rfl|rfl <;> decide)) (fun _ _=>rfl)]

def program (coord index j : Nat) (leaf pads sibs tws : Nat→Digest) : M (Nat×Nat×Nat×Digest) := do
  let initial←SharedV3.hashSel (hiSel j 0) (leafBytes leaf)
  let v2←(List.range 2).foldlM (childLevelP coord index j pads (hpOf j tws) sibs) initial
  let r2←level2C coord index j (decide (SEL16≤coordRegion coord)) pads tws sibs v2
  let out←OuterCopyTailC.program coord index j pads sibs tws (selD j 3 r2.2)
  pure (out.1,r2.1,out.2)

def Post (coord index j : Nat) (u : MachineState) (res : Nat×Nat×Nat×Digest) (t : MachineState) : Prop :=
  ∃ (s6 : MachineState) (raw2 : HashOutput),
    L2Post j (coordRegion coord) coord index u (decide (SEL16≤coordRegion coord)) (res.2.1,raw2) s6 ∧
    OuterCopyFlatC.Post coord j (virt2 j (coordRegion coord) u s6) (res.1,res.2.2) t

def W (coord j : Nat) : Nat := 17+(cycR j 0 2+(lvlSt j 2+1+W16 (decide (SEL16≤coordRegion coord))+
  (lvlSt j 3+1+W_SEARCH (widthOf (coordRegion coord))+(cycR j 4 1+77844))))

theorem run {im : Image} {sk : BitVec 256} (j : Fin 128) (coord : Fin 9) (index : Nat)
    (hc1 : 1≤coord.val) (hc8 : coord.val=8) (hi : index<2^31) (hcode : CopyCodeAt im j.val)
    (hc : CodeAt im (pcOf (childBase j.val)) (OuterNodeBankLayout.cWords j.val))
    (hS : CodeAt im (pcOf SEARCH) searchWords)
    (hT : CodeAt im (pcOf (trampOf j.val)) (trampWords (trampOf j.val) SEARCH (siteB j.val+1)))
    (hS16 : CodeAt im (pcOf SEARCH16) search16Words)
    (hT16 : CodeAt im (pcOf (tramp16Of j.val)) (trampWords (tramp16Of j.val) SEARCH16 (site16C j.val+1)))
    {leaf pads sibs tws : Nat→Digest} {u x : MachineState}
    (hu : ChildPre j.val (coordRegion coord.val) coord.val index leaf pads sibs tws u)
    (hxu : u=bankPc j.val x) (hpx : x.pc=pcOf (copyBase j.val+1)) :
    TBSim im sk x (W coord.val j.val) (program coord.val index j.val leaf pads sibs tws) (Post coord.val index j.val u) := by
  have hb:=OuterCopyFlatC.base_bounds coord
  have L3 : ∀ (r2 : Nat×HashOutput) (s6 : MachineState),
      L2Post j.val (coordRegion coord.val) coord.val index u (decide (SEL16≤coordRegion coord.val)) r2 s6→
      TBSim im sk s6 (lvlSt j.val 3+1+W_SEARCH (widthOf (coordRegion coord.val))+(cycR j.val 4 1+77844))
        (OuterCopyTailC.program coord.val index j.val pads sibs tws (selD j.val 3 r2.2) >>=fun out=>pure (out.1,r2.1,out.2))
        (Post coord.val index j.val u) := by
    intro r2 s6 h6
    obtain ⟨pads2,hpre,hmid,hpads,hframe⟩:=OuterCopyLayer2C.prepare j hu hb.2 hb.1 r2 h6
    have ht:=OuterCopyTailC.run (sk:=sk) j coord index hc1 hc8 hi hcode hc hS hT hpre hb.1 hb.2 (selD j.val 3 r2.2) hmid
    have hf:=ht.mono le_rfl (fun out t hout=>OuterCopyFlatC.flatten coord j index pads2 sibs _ t out hout)
    rw [tail_eq coord.val index j.val pads pads2 sibs tws hpads] at hf
    have hh:=TBSim.bind hf (fun out t hout=>TBSim.pure (a:=(out.1,r2.1,out.2)) (Q:=Post coord.val index j.val u) ⟨s6,r2.2,h6,hout⟩)
    simpa only [Nat.add_zero] using hh
  have H:=TBSim.bind (leafC_tbsim (sk:=sk) j.isLt hcode hu hxu hpx) (fun v s hs=>
    TBSim.bind (restC_tbsim (sk:=sk) j.isLt hcode hu 2 0 v s rfl hs) (fun v2 s2 hs2=>
      TBSim.bind (lvl2C_tbsim (sk:=sk) j.isLt hcode hS16 hT16 hu hb.1 hb.2 v2 s2 hs2) (fun r2 s6 h6=>L3 r2 s6 h6)))
  simpa only [W,program,List.range_eq_range'] using H

#print axioms tail_eq
#print axioms run
end OuterCopyChildC
