import SigGolfCandidate.OuterForestStep
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT.W9.Machine.Expand
open ClaudeWCT.W9.Machine.Expand.SharedForestRun (RecInv RecInv16 Fields)
open OuterForestInv (Inv)
open OuterForestFrame (writes)
open OuterForestStep (stepW)

/-- E8: the expand forest pass, with the 9 ground nonces and their records. -/
def forestW : Nat := 9*stepW
theorem forestW_val : forestW=839187 := by decide

/-- The forest pass's end: the hand-off pair, the frame, the fields, and the 9 nonce records. -/
def ForestPost (initial : MachineState) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563)
    (res : (Digest×Digest)×List Nat×List Nat×List Nat) (t : MachineState) : Prop :=
  t.pc=pcOf 46862 ∧ DigAt t 2904 res.1.1 ∧ DigAt t 2952 res.1.2 ∧
    Frame initial t writes ∧ Fields index raw ranks t ∧ t.getReg .x8=BitVec.ofNat 64 2984 ∧ RecInv raw 9 res.2.1 t ∧
    RecInv16 raw 9 res.2.2.1 t ∧ OuterForestCompactRecords.Inv 9 res.2.2.2 t

 theorem forest_tbsim (image : Image) (sk : BitVec 256)
    (w : W9Machine.WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563)
    (initial : MachineState)
    (hstep : ∀k:Fin 9,∀(prev:(Digest×Digest)×List Nat×List Nat×List Nat) u,
      Inv w index raw ranks initial k.val prev.1 u ∧ RecInv raw k.val prev.2.1 u ∧ RecInv16 raw k.val prev.2.2.1 u ∧ OuterForestCompactRecords.Inv k.val prev.2.2.2 u →
      TBSim image sk u stepW
        (OuterCoordinateModel.coordinate w index k (raw k) (ranks k) prev.1 >>= fun r=>
          pure (r.1,prev.2.1++[r.2.1],prev.2.2.1++[r.2.2.1],if SharedV3.first k.val then prev.2.2.2 else prev.2.2.2++[r.2.2.2]))
        (fun acc t=>Inv w index raw ranks initial (k.val+1) acc.1 t ∧ RecInv raw (k.val+1) acc.2.1 t ∧
          RecInv16 raw (k.val+1) acc.2.2.1 t ∧ OuterForestCompactRecords.Inv (k.val+1) acc.2.2.2 t))
    (h0 : Inv w index raw ranks initial 0 (SharedV3.initialPair w) initial) :
    TBSim image sk initial forestW (OuterForestModel.forest w index raw ranks)
      (ForestPost initial index raw ranks) := by
  have he {α:Type} (f:α → Fin 9 → M α) (init:α) :
      (List.finRange 9).foldlM f init=(List.range' 0 9).foldlM
        (fun st n=>if h:n<9 then f st ⟨n,h⟩ else pure st) init := by
    rw [show List.finRange 9=[0,1,2,3,4,5,6,7,8] from rfl,
      show List.range' 0 9=[0,1,2,3,4,5,6,7,8] from rfl]
    simp only [List.foldlM_cons,List.foldlM_nil]
    rfl
  unfold OuterForestModel.forest
  rw [he]
  have r0 : RecInv raw 0 [] initial :=
    ⟨rfl,fun m h=>absurd h (by omega),fun m h=>absurd h (by omega),fun m h=>absurd h (by omega),
      fun h=>absurd h (by omega),fun h=>absurd h (by omega)⟩
  have r16 : RecInv16 raw 0 [] initial :=
    ⟨rfl,fun m h=>absurd h (by omega),fun m h=>absurd h (by omega),fun m h=>absurd h (by omega),
      fun m h=>absurd h (by omega)⟩
  have rout : OuterForestCompactRecords.Inv 0 [] initial :=
    ⟨by decide,fun m h=>absurd h (by omega)⟩
  have hs:=TBSim.foldlM_range' (image:=image) (sk:=sk) 0 9
    (fun (prev:(Digest×Digest)×List Nat×List Nat×List Nat) (n:Nat)=>if h:n<9 then
      (OuterCoordinateModel.coordinate w index ⟨n,h⟩ (raw ⟨n,h⟩) (ranks ⟨n,h⟩) prev.1 >>= fun r=>
        pure (r.1,prev.2.1++[r.2.1],prev.2.2.1++[r.2.2.1],if SharedV3.first n then prev.2.2.2 else prev.2.2.2++[r.2.2.2])) else pure prev)
    (SharedV3.initialPair w,[],[],[])
    (fun n prev u=>Inv w index raw ranks initial n prev.1 u ∧ RecInv raw n prev.2.1 u ∧ RecInv16 raw n prev.2.2.1 u ∧ OuterForestCompactRecords.Inv n prev.2.2.2 u) stepW
    (fun n hn prev u hu=>by simpa only [Nat.zero_add,dif_pos hn] using hstep ⟨n,hn⟩ prev u hu) ⟨h0,r0,r16,rout⟩
  exact hs.mono (by unfold forestW; omega)
    (fun pair t ht=>⟨ht.1.pc,ht.1.prevL,ht.1.prevR,ht.1.frame,ht.1.fields,ht.1.x8 (by decide),ht.2.1,ht.2.2.1,ht.2.2.2⟩)


#print axioms forest_tbsim
end OuterForestRun
