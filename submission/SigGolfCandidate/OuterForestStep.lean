import SigGolfCandidate.OuterForestInv
import SigGolfCandidate.OuterForestRecords
import SigGolfCandidate.OuterForestCompactRecords
import SigGolfCandidate.OuterForestModel
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestStep
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT.W9.Machine.Expand
open ClaudeWCT.W9.Machine.Expand.SharedForestRun (RecInv RecInv16 pcWord eRegion)
open OuterForestInv (Inv witness_view)

def stepW : Nat := 77831+39+89+102+SigGolfCandidate.FtsGrind.W_SEARCH 2+SigGolfCandidate.FtsGrind.W_SEARCH16

theorem step_tbsim (image : Image) (sk : BitVec 256)
    (hchecked : ∀k:Fin 9,symRun {} (SharedDispatch.words k.val) (pcOf (SharedDispatch.start k.val))
      (SharedDispatch.length k.val)=some (SharedDispatch.result k.val))
    (hcode : ∀k:Fin 9,CodeAt image (pcOf (SharedDispatch.start k.val)) (SharedDispatch.words k.val))
    (hslot : ∀rank:Fin 563,Frozen.layout.chainWord (N600.embed rank)=195584+64*rank.val)
    (hcore : ∀ (L:W9Machine.Layout) (k:Fin 9) (j:Fin 128) (rank:Fin 563),
      L.image=image → L.childWord j=W9Drv.SharedBank.copyWord k.val j.val → Chain.base L k=9768-848*k.val →
      (∀r,L.chainWord r=Frozen.layout.chainWord r) → 
      ∀w index,index<2^31 → ∀snapshot u padL padR,
      N600.Pre L (SharedV3.viewWB 2904 w k.val snapshot) index k j rank u → 
      DigAt snapshot (2904+V3.regionOffset k.val+672) padL → 
      DigAt snapshot (2904+V3.regionOffset k.val+160) padR → 
      TBSim L.image sk u (89+OuterSharedBank.cost k)
        (N600.program w index k j rank >>=fun ends=>OuterChildModel.child w index k j ends padL padR)
        (OuterSharedCore.Post L (SharedV3.viewWB 2904 w k.val snapshot) index k j u))
    (w : W9Machine.WBytes) (index : Nat) (hi : index<2^31) (raw : Fin 9 → Fin 128)
    (ranks : Fin 9 → Fin 563) (initial : MachineState) (k : Fin 9) (prev : (Digest×Digest)×List Nat×List Nat×List Nat)
    (u : MachineState)
    (hu : Inv w index raw ranks initial k.val prev.1 u ∧ RecInv raw k.val prev.2.1 u ∧ RecInv16 raw k.val prev.2.2.1 u ∧ OuterForestCompactRecords.Inv k.val prev.2.2.2 u) :
    TBSim image sk u stepW
      (OuterCoordinateModel.coordinate w index k (raw k) (ranks k) prev.1 >>= fun r=>
        pure (r.1,prev.2.1++[r.2.1],prev.2.2.1++[r.2.2.1],if SharedV3.first k.val then prev.2.2.2 else prev.2.2.2++[r.2.2.2]))
      (fun acc t=>Inv w index raw ranks initial (k.val+1) acc.1 t ∧ RecInv raw (k.val+1) acc.2.1 t ∧
        RecInv16 raw (k.val+1) acc.2.2.1 t ∧ OuterForestCompactRecords.Inv (k.val+1) acc.2.2.2 t) := by
  let L:=SharedDispatch.layout image k
  let v:=(SharedDispatch.result k.val).toState u
  have hs:=SharedDispatch.steps image k u (hchecked k) (hcode k)
    (by simpa only [pcWord,if_pos k.isLt] using hu.1.pc)
  have hc:=SharedDispatch.chain_pre image k u (SharedV3.viewWB 2904 w k.val u) index (raw k) (ranks k)
    hi hu.1.fields.index (hu.1.fields.raw k) (hu.1.fields.rank k) (hslot _) (witness_view hu.1)
    (fun h => by rw [hu.1.x8 (by omega), h])
  have hL:DigAt u (2904+V3.regionOffset k.val+672) prev.1.1 := by
    convert hu.1.prevL using 1 <;> unfold V3.regionOffset eRegion SharedV3.handL <;>
      have:=k.isLt <;> simp only [if_neg (by omega : k.val≠9)] <;> omega
  have hR:DigAt u (2904+V3.regionOffset k.val+160) prev.1.2 := by
    convert hu.1.prevR using 1 <;> unfold V3.regionOffset eRegion SharedV3.handR <;>
      have:=k.isLt <;> simp only [if_neg (by omega : k.val≠9)] <;> omega
  have hbase:Chain.base L k=9768-848*k.val := by
    rw [SharedDispatch.layout_base]; unfold coordinateBase; have:=k.isLt; omega
  have hb:=hcore L k (raw k) (ranks k) rfl rfl hbase (fun _=>rfl)
    w index hi u v prev.1.1 prev.1.2 hc hL hR
  have hj' : TBSim image sk v ((89+OuterSharedBank.cost k)+0)
      ((N600.program w index k (raw k) (ranks k) >>=fun ends=>
        OuterChildModel.child w index k (raw k) ends prev.1.1 prev.1.2) >>=fun computed=>
        pure ((SharedV3.orderPair k.val (SharedV3.physical k.val (raw k).val) computed.1
          (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val))),prev.2.1++[computed.2.1],
          prev.2.2.1++[computed.2.2.1],if SharedV3.first k.val then prev.2.2.2 else prev.2.2.2++[computed.2.2.2]))
      (fun acc t=>Inv w index raw ranks initial (k.val+1) acc.1 t ∧ RecInv raw (k.val+1) acc.2.1 t ∧
        RecInv16 raw (k.val+1) acc.2.2.1 t ∧ OuterForestCompactRecords.Inv (k.val+1) acc.2.2.2 t) := by
    refine TBSim.bind hb ?_
    intro computed t ht
    obtain ⟨ends,entry,hp,ht⟩:=ht
    exact TBSim.pure ⟨OuterForestInv.next hu.1 hp ht,OuterForestRecords.rec_next hu.2.1 hp ht,OuterForestRecords.rec16_next hu.2.2.1 hp ht,OuterForestCompactRecords.next hu.2.2.2 hp ht⟩
  have hh:=TBSim.steps hs hj'
  have hlen:SharedDispatch.length k.val≤39:=by fin_cases k <;> decide
  have hcost:OuterSharedBank.cost k≤77831+102+SigGolfCandidate.FtsGrind.W_SEARCH 2+SigGolfCandidate.FtsGrind.W_SEARCH16:=by
    unfold OuterSharedBank.cost W9Drv.SharedBank.costG SigGolfCandidate.FtsGrind.W_SEARCH SigGolfCandidate.FtsGrind.FUEL
      SigGolfCandidate.FtsGrind.ftsWidth SigGolfCandidate.FtsGrind.W16 SigGolfCandidate.FtsGrind.W_SEARCH16
      SigGolfCandidate.FtsGrind.W_PLAIN16
    split_ifs <;> omega
  simpa only [OuterCoordinateModel.coordinate,N600.program,(show N600.embed=ClaudeWCT.WCT9.embed from N600.embed_eq_c1),bind_assoc,pure_bind] using
    hh.mono (show SharedDispatch.length k.val+((89+OuterSharedBank.cost k)+0)≤ stepW by unfold stepW; omega)
      (fun _ _ h=>h)


#print axioms step_tbsim
end OuterForestStep
