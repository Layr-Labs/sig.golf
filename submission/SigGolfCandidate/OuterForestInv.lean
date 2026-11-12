import SigGolfCandidate.OuterForestFrame
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestInv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT.W9.Machine.Expand
open ClaudeWCT.W9.Machine.Expand.SharedForestRun (RecInv RecInv16 isHand eRegion pcWord Fields hand_address)
open OuterForestFrame

structure Inv (w : W9Machine.WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563)
    (initial : MachineState) (n : Nat) (prev : Digest×Digest) (u : MachineState) : Prop where
  le : n≤9
  pc : u.pc=pcOf (pcWord n)
  fields : Fields index raw ranks u
  prevL : DigAt u (eRegion n+SharedV3.handL n) prev.1
  prevR : DigAt u (eRegion n+SharedV3.handR n) prev.2
  /-- Original witness words of the coordinates not yet run. Stage 2 (C3): region 9 (the L3 encoding row,
  `WIT + 0 .. WIT + 80`; witness trim) excludes its offset `840` = `WIT + 24`, the row tweak's high word (a witness pad, honest
  LE64 1). No FTS routine reads it, and in the expander's first forest pass the cleared witness prefix still holds 0
  there (the final pass restores it, `SharedScatter.finishCode`). -/
  coords : ∀ (m : Nat), n ≤ m → m ≤ 9 → ∀ (off : Nat), off < 848 → off % 8 = 0 →
    (m = 9 → 768 ≤ off ∧ off ≠ 792) → (m = n → ¬ isHand n off) →
    W9Machine.OrigWD 1352 w u (eRegion m + off)
  frame : Frame initial u writes
  /-- Pairing stage 1: `s0` holds the previous coordinate's base (coordinate 8's dispatch derives its base from it;
  after coordinate 8 it is `coordinateBase 8 = 2984`, read by the hand-off). -/
  x8 : 0 < n → u.getReg .x8 = BitVec.ofNat 64 (2984 + 848 * (9 - n))

theorem witness_view {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {ranks : Fin 9 → Fin 563} {initial u : MachineState} {k : Fin 9} {prev : Digest×Digest}
    (hu : Inv w index raw ranks initial k.val prev u) :
    ∀off,off<848 → off%8=0 → u.getMem (BitVec.ofNat 64 (coordinateBase k - 1352+off))=
      (SharedV3.viewWB 2904 w k.val u).extractLsb' (8*(V3.regionOffset k.val+off)) 64 := by
  intro off ho h8
  have hk:=k.isLt
  have hr8:=V3.regionOffset_mod k.val
  rw [SharedV3.view_wordB 2904 w k.val u _ (by omega) (by unfold V3.regionOffset;omega)]
  by_cases hh:SharedV3.isHand off
  · rw [if_pos ⟨by omega,by simpa only [Nat.add_sub_cancel_left] using hh⟩]
    congr 2
    unfold coordinateBase V3.regionOffset
    omega
  · rw [if_neg (fun h=>hh (by simpa only [Nat.add_sub_cancel_left] using h.2))]
    have hw:=hu.coords k.val (by omega) (by omega) off ho h8 (by omega)
      (fun _=>by simpa only [isHand,if_neg (by omega : k.val≠9)] using hh)
    have he:eRegion k.val+off+1352-0x10A0=V3.regionOffset k.val+off := by
      unfold eRegion V3.regionOffset;omega
    have hb:coordinateBase k - 1352+off=eRegion k.val+off := by unfold coordinateBase eRegion;omega
    rw [hb]
    simpa only [W9Machine.OrigWD,he] using hw

theorem next_other {image : Image} (w : W9Machine.WBytes) (k : Fin 9) (raw : Fin 128)
    (u t : MachineState) (hf : Frame u t (childW (SharedDispatch.layout image k) k raw)) (off : Nat)
    (hoff : off=SharedV3.handL (k.val+1) ∨ off=SharedV3.handR (k.val+1))
    (hsel : if SharedV3.direction k.val (SharedV3.physical k.val raw.val)=0
      then off=SharedV3.handR (k.val+1) else off=SharedV3.handL (k.val+1))
    (h0 : W9Machine.OrigWD 1352 w u (eRegion (k.val+1)+off))
    (h1 : W9Machine.OrigWD 1352 w u (eRegion (k.val+1)+(off+8))) :
    DigAt t (eRegion (k.val+1)+off)
      (SharedV3.topOther w k.val (SharedV3.physical k.val raw.val)) := by
  have hk:=k.isLt
  have h1':W9Machine.OrigWD 1352 w u (eRegion (k.val+1)+off+8) := by rw [Nat.add_assoc];exact h1
  have hlo:0x10A0≤eRegion (k.val+1)+off+1352 := by
    unfold SharedV3.handR SharedV3.handL at hoff
    unfold eRegion
    split_ifs at hoff <;> omega
  have hd:=W9Machine.DigAt_origWD h0 h1' hlo
  have he:eRegion (k.val+1)+off+1352-0x10A0=SharedV3.topOtherOff k.val (SharedV3.physical k.val raw.val) := by
    unfold SharedV3.topOtherOff V3.regionOffset eRegion
    unfold SharedV3.handR SharedV3.handL at hsel ⊢
    split_ifs at hsel ⊢ <;> omega
  rw [he] at hd
  refine hd.frame hf (by unfold SharedV3.handR SharedV3.handL at hoff;unfold eRegion;split_ifs at hoff <;> omega) ?_ ?_
  all_goals
    intro hw
    have hw:=child_low hw (by unfold eRegion; omega) (by
      have ho : off≤816 := by unfold SharedV3.handR SharedV3.handL at hoff; split_ifs at hoff <;> omega
      unfold eRegion; omega)
    rcases hw with hw|hw|hw
    · simp only [SharedChild.writes, SharedChild.outputAddr, SharedChild.handAddr, SharedDispatch.layout_base] at hw
      unfold coordinateBase at hw
      unfold SharedV3.handR SharedV3.handL at hoff hsel
      unfold eRegion at hw
      split_ifs at hsel hw <;> omega
    · unfold SharedChild.recW SigGolfCandidate.FtsGrind.slotA SigGolfCandidate.FtsGrind.SCR at hw
      rw [SharedDispatch.layout_base] at hw
      unfold coordinateBase at hw
      unfold SharedV3.handR SharedV3.handL at hoff
      unfold eRegion at hw
      split_ifs at hoff <;> omega
    · rcases hw with hw|hw
      · unfold SharedChild.scratchW SigGolfCandidate.FtsGrind.SCR at hw
        unfold SharedV3.handR SharedV3.handL at hoff
        unfold eRegion at hw
        split_ifs at hoff <;> omega
      · unfold SharedChild.recW16 SigGolfCandidate.FtsGrind.slot16 SigGolfCandidate.FtsGrind.SCR16 at hw
        unfold SharedV3.handR SharedV3.handL at hoff
        unfold eRegion at hw
        split_ifs at hoff <;> omega

theorem next {image : Image} {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128}
    {ranks : Fin 9 → Fin 563} {initial u entry t : MachineState} {k : Fin 9} {prev : Digest×Digest}
    {ends : List Digest} {computed : Digest × Nat × Nat × Nat} (hu : Inv w index raw ranks initial k.val prev u)
    (hp : Chain.Post (SharedDispatch.layout image k) (SharedV3.viewWB 2904 w k.val u) index k (raw k)
      ((SharedDispatch.result k.val).toState u) ends entry)
    (ht : OuterSharedPost.Post (SharedDispatch.layout image k) k (raw k) entry computed t) :
    Inv w index raw ranks initial (k.val+1)
      (SharedV3.orderPair k.val (SharedV3.physical k.val (raw k).val) computed.1
        (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val))) t := by
  have hk:=k.isLt
  have hf:=core_frame_dispatch hp ht
  have hfg:Frame u t writes:=hf.mono (fun addr _ hw=>child_bounds (image:=image) k (raw k) addr hw)
  have hother:∀off,(off=SharedV3.handL (k.val+1) ∨ off=SharedV3.handR (k.val+1)) → 
      (if SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
        then off=SharedV3.handR (k.val+1) else off=SharedV3.handL (k.val+1)) → 
      DigAt t (eRegion (k.val+1)+off) (SharedV3.topOther w k.val (SharedV3.physical k.val (raw k).val)) := by
    intro off hoff hsel
    have ho:off≤816 ∧ off%8=0 ∧ (k.val+1=9 → off=768 ∨ off=816) := by
      unfold SharedV3.handR SharedV3.handL at hoff;split_ifs at hoff <;> omega
    exact next_other w k (raw k) u t hf off hoff hsel
      (hu.coords (k.val+1) (by omega) (by omega) off (by omega) (by omega)
        (fun h=>by have:=ho.2.2 h;omega) (fun h=>by omega))
      (hu.coords (k.val+1) (by omega) (by omega) (off+8) (by omega) (by omega)
        (fun h=>by have:=ho.2.2 h;omega) (fun h=>by omega))
  refine ⟨by omega,?_,fields_frame hfg hu.fields,?_,?_,?_,?_,?_⟩
  · rw [ht.pc]
    fin_cases k <;> rfl
  · unfold SharedV3.orderPair
    by_cases hd:SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
    · rw [if_pos hd]
      have he:SharedChild.handAddr (SharedDispatch.layout image k) k (raw k)=eRegion (k.val+1)+SharedV3.handL (k.val+1):=by rw [hand_address,if_pos hd]
      rw [←he]
      exact ht.top
    · rw [if_neg hd]
      exact hother (SharedV3.handL (k.val+1)) (Or.inl rfl) (by rw [if_neg hd])
  · unfold SharedV3.orderPair
    by_cases hd:SharedV3.direction k.val (SharedV3.physical k.val (raw k).val)=0
    · rw [if_pos hd]
      exact hother (SharedV3.handR (k.val+1)) (Or.inr rfl) (by rw [if_pos hd])
    · rw [if_neg hd]
      have he:SharedChild.handAddr (SharedDispatch.layout image k) k (raw k)=eRegion (k.val+1)+SharedV3.handR (k.val+1):=by
        rw [hand_address,if_neg hd]
      rw [←he]
      exact ht.top
  · intro m hm1 hm9 off hoff h8 hv hh
    have h0:=hu.coords m (by omega) hm9 off hoff h8 hv (fun h=>by omega)
    unfold W9Machine.OrigWD at h0 ⊢
    rw [←h0]
    apply hf _ (by unfold eRegion;omega)
    intro hw
    have hw:=child_low hw (by unfold eRegion; omega) (by unfold eRegion; omega)
    rcases hw with hw|hw|hw
    rotate_left
    · unfold SharedChild.recW SigGolfCandidate.FtsGrind.slotA SigGolfCandidate.FtsGrind.SCR at hw
      rw [SharedDispatch.layout_base] at hw
      unfold coordinateBase eRegion at *
      omega
    · rcases hw with hw|hw
      · unfold SharedChild.scratchW SigGolfCandidate.FtsGrind.SCR at hw
        unfold eRegion at *
        omega
      · unfold SharedChild.recW16 SigGolfCandidate.FtsGrind.slot16 SigGolfCandidate.FtsGrind.SCR16 at hw
        unfold eRegion at *
        omega
    simp only [SharedChild.writes, SharedChild.outputAddr, SharedChild.handAddr, SharedDispatch.layout_base] at hw
    unfold coordinateBase at hw
    have hmk:eRegion m+848≤eRegion k.val:=by unfold eRegion;omega
    rcases Nat.lt_or_ge (k.val+1) m with hgt|hle
    · have :eRegion m+848≤eRegion (k.val+1):=by unfold eRegion;omega
      unfold eRegion at *
      split_ifs at hw <;> omega
    · have hm':m=k.val+1:=by omega
      subst hm'
      have hn:=hh rfl
      unfold isHand SharedV3.isHand at hn
      unfold eRegion at *
      split_ifs at hn <;> split_ifs at hw <;> omega
  · intro addr ha hn
    exact (hfg addr ha hn).trans (hu.frame addr ha hn)
  · intro _
    rw [ht.keep .x8 (by decide), hp.child.baseReg, SharedDispatch.layout_base]
    simp only [coordinateBase]
    congr 2
    omega

#print axioms witness_view
#print axioms next
end OuterForestInv
