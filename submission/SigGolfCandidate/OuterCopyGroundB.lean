import SigGolfCandidate.OuterNodeBankTailB
import SigGolfCandidate.FtsCopyB
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCopyGroundB
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedBProof
open SigGolfCandidate.FtsGrind
open SphincsSecurity (bytesLE bytesLE_length)

def Changes (B j X : Nat) : Prop :=
  (X=B+padO j 3 ∨ X=B+padO j 3+8) ∨ (SCR≤X ∧ X<SCR+32) ∨
    (slotA B≤X ∧ X<slotA B+16) ∨ (1104≤X ∧ X<1144)

def Post (B k index j : Nat) (pads sibs : Nat→Digest) (u : MachineState) (res : Nat×Digest) (t : MachineState) : Prop :=
  ∃ (u' : MachineState) (leaf' pads' sibs' tws' : Nat→Digest),
    ChildPre j B k index leaf' pads' sibs' tws' u' ∧ Mid j B k index u' 4 res.2 t ∧
    u'=virt j B u t ∧
    (∀ r,u'.getReg r=u.getReg r) ∧ Frame u u' (Changes B j) ∧
    (∀ l,l=4 ∨ l=5→pads' l=pads l) ∧ (∀ l,l=4 ∨ l=5→sibs' l=sibs l) ∧
    t.getMem (BitVec.ofNat 64 (slotA B))=BitVec.ofNat 64 (B+blkO j 3+WADJ) ∧
    t.getMem (BitVec.ofNat 64 (slotA B+8))=BitVec.ofNat 64 res.1 ∧ res.1≤FUEL (widthOf B) ∧
    (∀ i,i<5→t.getMem (BitVec.ofNat 64 (1104+8*i))=0) ∧
    (∀ i,i<4→t.getMem (BitVec.ofNat 64 (SCR+8*i))=0)

variable {im : Image} {sk : BitVec 256} {j : Nat} (hj : j<128) (hcode : CopyCodeAt im j)
  (hS : CodeAt im (pcOf SEARCH) searchWords)
  (hT : CodeAt im (pcOf (trampOf j)) (trampWords (trampOf j) SEARCH (siteB j+1)))
  {B k index : Nat} {leaf pads sibs tws : Nat→Digest} {u : MachineState}
  (hu : ChildPre j B k index leaf pads sibs tws u) (hlo : 1848≤B) (hB : B<2^14)
include hj hcode hS hT hu hlo hB
theorem run (v : Digest) (s : MachineState) (hs : MidC j B k index u 3 v s) :
    TBSim im sk s (lvlSt j 3+1+W_SEARCH (widthOf B))
      (groundFold (widthOf B) (preC k index j tws sibs v) (rightC j sibs v) >>= fun r=>pure (r.1,r.2.extractLsb' 0 128))
      (Post B k index j pads sibs u) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hsl := site_lt j hj
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  obtain ⟨t, hst, -, h5, h10, h11, h12', hpcT, hother, -, -, hP, hpre1, hhdr, hright⟩ :=
    lvl_coreC hj hcode hu 3 (by decide) v s hs
  have hbl := blk_bounds j hj 3 (by decide)
  have hbl4 := blk_bounds j hj 4 (by decide)
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + outO 4 j) := by
    rw [h12', lvlRegs_x12 j 3 (by decide)]
    by_cases hsk : skipA2 j 3 = true
    · rw [if_pos hsk, skipA2_out hsk]
      simp only [E.eval]
      exact hs.a2
    · rw [if_neg hsk, eX8_eval hx8]
  have hoa := outO_lo (hiSel_four j hj)
  have hcur : outO 4 j % 8 = 0 ∧ outO 4 j + 32 ≤ 864 := by have := curO_cases j 4; omega
  -- the site `jal`
  have hjal : CodeAt im (pcOf (siteC j))
      [SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (siteC j) (trampOf j))] := by
    refine codeAt_one ?_ (by unfold siteC copyBase cSlot SigGolfCandidate.FtsGrind.COPY_ODD; omega)
    have hlen : (((childWords j).take (ecIdx j 4)).set (ecIdx j 3)
        (SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (site16C j) (tramp16Of j)))).length =
        ecIdx j 4 := by
      rw [List.length_set, List.length_take]; have := ecIdx4_le j hj; omega
    have := hcode (ecIdx j 4)
      (SigGolfCandidate.FtsGrind.encJal 0 (SigGolfCandidate.FtsGrind.jOff (siteC j) (trampOf j))) (by
      unfold copyPre; rw [List.getElem?_append_right (by omega), hlen]; simp)
    simpa [siteC] using this
  have hjs := SigGolfCandidate.FtsGrind.jal_step (r := .x0) (by decide) rfl hjal
    (by unfold siteC copyBase cSlot SigGolfCandidate.FtsGrind.COPY_ODD; omega)
    (by unfold trampOf cSlot SigGolfCandidate.FtsGrind.TRAMP; omega) t (by rw [hpcT]; rfl)
  set t1 := ((t.setReg .x0 (pcOf (siteC j + 1))).setPC (pcOf (trampOf j))) with ht1
  have r1 : ∀ r, t1.getReg r = t.getReg r := fun r => by cases r <;> rfl
  have m1 : Frame t t1 (fun _ => False) := fun _ _ _ => rfl
  have hA : (B + blkO j 3) % 8 = 0 := by omega
  have F : SearchIn (trampOf j) (siteB j + 1) (B + blkO j 3) (B + outO 4 j) B
      (preC k index j tws sibs v) (rightC j sibs v) t1 :=
    { pc := rfl
      x5 := by rw [r1]; exact h5
      x8 := by rw [r1, hother .x8 (by decide) (by decide) (by decide) (by decide)]; exact hu.s0
      x10 := by rw [r1]; exact h10
      x11 := by rw [r1]; exact h11
      x12 := by rw [r1]; exact h12
      lpre := by simp [preC, bytesLE_length]
      lright := by simp [rightC, bytesLE_length]
      mpre := by
        rw [frame_readWordsG m1 _ 4 (by omega) (fun _ _ h => h), show (4 : Nat) = 2 + 2 from rfl, readWords_add,
          hpre1.words, show B + blkO j 3 + 8 * 2 = B + blkO j 3 + 16 by ring, hhdr.words, preC,
          wordsOf_append _ _ (by simp [bytesLE_length])]
      mright := by
        rw [frame_readWordsG m1 _ 2 (by omega) (fun _ _ h => h), hright.words, rightC]
      hA := hA
      hA1 := by omega
      hA2 := by simp only [SCR]; omega
      hD := by omega
      hD1 := by omega
      hD2 := by simp only [SCR]; omega
      hS0 := h8
      hS1 := by omega
      hS2 := hB
      hb := by unfold trampOf cSlot SigGolfCandidate.FtsGrind.TRAMP; omega
      hret := by unfold siteB childBase; omega }
  have HS := tramp_search (sk := sk) hS hT F
  refine (TBSim.steps hst (TBSim.steps hjs (TBSim.bind (W₂ := 0) HS (fun r s6 ho => ?_)))).mono (by omega) (fun _ _ h => h)
  -- the virtual bank entry and the bank's tail
  have hBl : B + 1024 < 2 ^ 64 := by omega
  set u' := virt j B u s6 with hvd
  have g6 : ∀ x, x ∉ ([] : List Reg) → s6.getReg x = t1.getReg x := ho.regs
  have hsw : ∀ X, X < 2 ^ 64 → ¬ (∃ off ∈ stagesW j 5, X = B + off) →
      ¬ (X = B + padO j 3 ∨ X = B + padO j 3 + 8) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slotA B ≤ X ∧ X < slotA B + 16) → ¬ (1104 ≤ X ∧ X < 1144) →
      s6.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := by
    intro X hX h1 h2 h3 h4 h5'
    have e6 := ho.frame.get hX (by
      unfold SigGolfCandidate.FtsGrind.SearchW
      rintro (h | h | h | h | h | h)
      · rcases h with h | h | h | h
        · exact h1 ⟨outO 4 j, mem_stagesW (m := 4) (by omega) (by simp [stageW]), h⟩
        · exact h1 ⟨outO 4 j + 8, mem_stagesW (m := 4) (by omega) (by simp [stageW]), by omega⟩
        · exact h1 ⟨outO 4 j + 16, mem_stagesW (m := 4) (by omega) (by simp [stageW]), by omega⟩
        · exact h1 ⟨outO 4 j + 24, mem_stagesW (m := 4) (by omega) (by simp [stageW]), by omega⟩
      · exact h2 (Or.inl (by unfold padO; omega))
      · exact h2 (Or.inr (by unfold padO; omega))
      · exact h4 h
      · exact h5' h
      · exact h3 h)
    rw [e6, m1.get hX (fun h => h), hP.get hX (by
      rintro (h | h)
      · exact h1 ⟨tw24 j 3, mem_stagesW (m := 3) (by omega) (by simp [stageW]), h⟩
      · exact h1 ⟨blkO j 3 + 16, mem_stagesW (m := 3) (by omega) (by simp [stageW]), by omega⟩)]
    exact hs.frame.get hX (fun ⟨off, hoff, he⟩ => h1 ⟨off, stagesW_mono hoff (by omega), he⟩)
  have hvu : ∀ X, X < 2 ^ 64 → ¬ (X = B + padO j 3 ∨ X = B + padO j 3 + 8) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slotA B ≤ X ∧ X < slotA B + 16) → ¬ (1104 ≤ X ∧ X < 1144) →
      u'.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := by
    intro X hX h2 h3 h4 h5'
    rw [hvd, virt_getMem j B u s6 hBl hj X hX]
    split_ifs with hw
    · rfl
    · exact hsw X hX hw h2 h3 h4 h5'
  have hp3 := pad3_prefix j hj
  have hbl5 := blk_bounds j hj 5 (by decide)
  have hbl0 : padO j 4 % 16 = 0 ∧ sibO 4 j % 16 = 0 ∧ padO j 3 % 16 = 0 ∧ padO j 5 % 16 = 0 ∧
      sibO 5 j % 16 = 0 := by
    have := sibO_cases j 4 (by decide); have := sibO_cases j 5 (by decide); unfold padO; omega
  have far : ∀ X, B ≤ X → X < B + 1024 → ¬ (SCR ≤ X ∧ X < SCR + 32) ∧ ¬ (slotA B ≤ X ∧ X < slotA B + 16) ∧
      ¬ (1104 ≤ X ∧ X < 1144) := fun X h1 h2 => by simp only [SCR, slotA]; omega
  have hsb4 := sibO_cases j 4 (by decide)
  have hsb5 := sibO_cases j 5 (by decide)
  have dig4 : ∀ (o : Nat) (d : Digest), (o = padO j 4 ∨ o = sibO 4 j ∨ o = padO j 5 ∨ o = sibO 5 j) →
      o + 16 ≤ 1024 → DigAt u (B + o) d →
      DigAt u' (B + o) d := by
    intro o d ho hlt hd
    have h16 : o % 16 = 0 ∧ o ≠ padO j 3 := by rcases ho with rfl | rfl | rfl | rfl <;> omega
    refine DigAt.of_eq hd ?_ ?_
    · have := far (B + o) (by omega) (by omega)
      exact hvu _ (by omega) (by omega) this.1 this.2.1 this.2.2
    · have := far (B + o + 8) (by omega) (by omega)
      exact hvu _ (by omega) (by omega) this.1 this.2.1 this.2.2
  let pads' : Nat → Digest := fun l => if l = 4 ∨ l = 5 then pads l else rdD u' (B + padO j l)
  let sibs' : Nat → Digest := fun l => if l = 4 ∨ l = 5 then sibs l else rdD u' (B + sibO l j)
  let tws' : Nat → Digest := fun l => rdD u' (B + blkO j l + 16)
  let leaf' : Nat → Digest := fun i => rdD u' (B + leafO + 16 * i)
  have hu' : ChildPre j B k index leaf' pads' sibs' tws' u' :=
    { pc := rfl
      base8 := h8
      baseHi := hu.baseHi
      t0 := by rw [virt_getReg]; exact hu.t0
      s0 := by rw [virt_getReg]; exact hu.s0
      a0 := by rw [virt_getReg]; exact hu.a0
      a1 := by rw [virt_getReg]; exact hu.a1
      w0 := by rw [virt_getReg]; exact hu.w0
      heaps := fun h h1 h2 => by rw [virt_getReg]; exact hu.heaps h h1 h2
      leafAt := fun i _ => digAt_rdD _ _
      padAt := fun l hl => by
        by_cases e : l = 4 ∨ l = 5
        · simp only [pads', if_pos e]
          rcases e with rfl | rfl
          · exact dig4 _ _ (Or.inl rfl) (by unfold padO; omega) (hu.padAt 4 (by decide))
          · exact dig4 _ _ (Or.inr (Or.inr (Or.inl rfl))) (by unfold padO; omega) (hu.padAt 5 (by decide))
        · simp only [pads', if_neg e]; exact digAt_rdD _ _
      sibAt := fun l hl => by
        by_cases e : l = 4 ∨ l = 5
        · simp only [sibs', if_pos e]
          rcases e with rfl | rfl
          · exact dig4 _ _ (Or.inr (Or.inl rfl)) (by omega) (hu.sibAt 4 (by decide))
          · exact dig4 _ _ (Or.inr (Or.inr (Or.inr rfl))) (by omega) (hu.sibAt 5 (by decide))
        · simp only [sibs', if_neg e]; exact digAt_rdD _ _
      twAt := fun l _ => digAt_rdD _ _ }
  have hmid : Mid j B k index u' 4 (r.2.extractLsb' 0 128) s6 :=
    { pc := by rw [ho.pc]; unfold siteB; rw [Nat.add_assoc]
      keep := fun x h3 h10' h11' h12' => by
        rw [virt_getReg, g6 x (by simp), r1, hother x h3 h10' h11' h12']
      a1 := fun _ => by rw [g6 _ (by simp), r1]; exact h11
      a2 := by rw [g6 _ (by simp), r1, h12]
      node := by
        have e0 := ho.ans 0 (by decide); have e1 := ho.ans 1 (by decide)
        simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at e0 e1
        rw [← hoa]
        exact ⟨e0.trans (lowHalf r.2).1.symm, e1.trans (lowHalf r.2).2.symm⟩
      frame := fun A hA hn => by
        rw [hvd, virt_getMem j B u s6 hBl hj A hA, if_neg hn] }
  refine TBSim.pure ⟨u',leaf',pads',sibs',tws',hu',hmid,hvd,?_,?_,?_,?_,ho.slot0,ho.slot1,ho.nle,ho.saves,ho.scr⟩
  · exact fun r=>virt_getReg j B u s6 r
  · intro X hX hn
    unfold Changes at hn
    simp only [not_or] at hn
    exact hvu X hX (fun h=>h.elim hn.1.1 hn.1.2) hn.2.1 hn.2.2.1 hn.2.2.2
  · intro l hl
    simp only [pads',if_pos hl]
  · intro l hl
    simp only [sibs',if_pos hl]

#print axioms run
end OuterCopyGroundB
