import SigGolfCandidate.FtsCopyA
import SigGolfCandidate.FtsCopyB
import SigGolfCandidate.FtsCopyC
import SigGolfCandidate.Merge056
set_option debug.skipKernelTC true
set_option linter.all false

/-! # E8: the expand child routines through their copies refine `SharedV3.childNG`

`SharedV3.childNG` is the canonical child program with the level-3 (heap `8..15`) fold ground for
`ftsWidth k` zero bits; it returns the found nonce. Each family's copy proof (`childC_tbsim`) refines the
bank-form `childProgramC`; this module converts it to the shared-layer interface (`SharedChild.Pre` at the copy
pc, `PostC` = `SharedChild.Post` plus the nonce record, the saves and `SCR`). -/

namespace W9Machine.SharedChild
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open SigGolfCandidate.FtsGrind (slotA SCR WADJ FUEL ftsWidth)

/-- E8: the canonical child program with the ground level-3 fold, from the witness pads. -/
def childProgramG (w : WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (ends : List Digest) :
    M (Digest × Nat) :=
  SharedV3.childNG w index k raw ends (SharedV3.leafPad w k.val)
    (SharedV3.nodePad w k.val (SharedV3.physical k.val raw.val) 4)

/-- The nonce records of the coordinate with frame base `B`: level 3 at `slotA B` and (S5185 FTS16, TIER2B D2) level 2
at `slot2 B = slotA B + 16`, each (absolute witness pad address, nonce); the level-2 half only for ground level 2
(`3400 <= B`, coordinates 0..7: coordinate 8's level-2 record word must stay 0 for `copy2`). -/
def recW (B : Nat) (A : Nat) : Prop := slotA B ≤ A ∧ A < slotA B + 16 ∨ 3400 ≤ B ∧ slotA B + 16 ≤ A ∧ A < slotA B + 32

/-- Search scratch: the saves and `SCR`. -/
def scratchW (A : Nat) : Prop := (1104 ≤ A ∧ A < 1144) ∨ (SCR ≤ A ∧ A < SCR + 32)

/-- After a copy routine: `Post` with the record, the zeroed scratch and the widened frame. -/
structure PostC (L : Layout) (k : Fin 9) (raw : Fin 128) (u : MachineState)
    (res : Digest × Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (L.returnWord k + (if k.val = 8 then 79 else if k.val % 2 = 1 then 76 else 75))
  hashLen : t.getReg .x11 = 64
  top : DigAt t (handAddr L k raw) res.1
  a2 : t.getReg .x12 = BitVec.ofNat 64 (outputAddr L k raw)
  keep : ∀ r, r ∉ Child.clobbers → t.getReg r = u.getReg r
  slot0 : t.getMem (BitVec.ofNat 64 (slotA (Chain.base L k))) =
    BitVec.ofNat 64 (Chain.base L k + SharedV3.blkOff (SharedV3.physical k.val raw.val) 3 + WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (slotA (Chain.base L k) + 8)) = BitVec.ofNat 64 res.2
  /-- S5185 (FTS16, TIER2B D2): `res.2 = 2^64 n2 + n3` (NONCE2 packing; `slot1` keeps `n3 = res.2 mod 2^64`). -/
  nle : res.2 % 2 ^ 64 ≤ FUEL (ftsWidth k.val) ∧ res.2 / 2 ^ 64 ≤ FUEL 1
  rec2a : 3400 ≤ Chain.base L k → t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot2 (Chain.base L k))) =
    BitVec.ofNat 64 (Chain.base L k + SharedV3.blkOff (SharedV3.physical k.val raw.val) 2 + WADJ)
  rec2b : 3400 ≤ Chain.base L k →
    t.getMem (BitVec.ofNat 64 (SigGolfCandidate.FtsGrind.slot2 (Chain.base L k) + 8)) = BitVec.ofNat 64 (res.2 / 2 ^ 64)
  plain2 : Chain.base L k < 3400 → res.2 / 2 ^ 64 = 0
  saves : ∀ i < 5, t.getMem (BitVec.ofNat 64 (1104 + 8 * i)) = 0
  scr : ∀ i < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * i)) = 0
  frame : Frame u t (fun A => writes L k raw A ∨ recW (Chain.base L k) A ∨ scratchW A)

end W9Machine.SharedChild

namespace W9Drv.SharedAProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M shortHash)
open SigGolfCandidate.FtsGrind (SEARCH searchWords trampWords widthOf groundFold W_SEARCH FUEL slotA SCR WADJ
  ftsWidth)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem programG_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9)
    (raw : Fin 128) (ends : List Digest) (hf : SharedV3.first k.val = true) (b : Nat)
    (hb : b = ftsWidth k.val) (B : Nat) (hB : 3400 ≤ B ↔ k.val ≤ 7) :
    SharedChild.childProgramG w index k raw ends =
      childProgramC k.val index (SharedV3.physical k.val raw.val)  b B
        (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends)
        (SharedV3.nodePad w k.val (SharedV3.physical k.val raw.val))
        (SharedV3.sibling w k.val (SharedV3.physical k.val raw.val))
        (SharedV3.nodeTw w k.val (SharedV3.physical k.val raw.val)) >>= fun r => pure (r.2, r.1) := by
  -- TIER2B D1: the D1 proof plus the level-2 step: `childStepG`'s level-2 branch (`coord <= 7`, `groundFoldH (hiOut j 3) 1`)
  -- is `node2 (hiSel j 3) B` on `nodeIn .. 2` by `hB` (`take 32` = left ‖ header, `drop 48` = right, as `preC/rightC` at
  -- level 3); coordinate 8 is the plain `hashSel` (= `node2` plain + `selD`); the nonce sum `0 + 2^64 n2 + n3`.
  subst hb
  have hc : k.val ≠ 8 := by
    intro h; rw [h] at hf; contradiction
  have hk7 : k.val ≤ 7 := by have := k.isLt; omega
  have hB3 : 3400 ≤ B := hB.2 hk7
  unfold SharedChild.childProgramG SharedV3.childNG childProgramC
  simp only [SharedV3.lastLevel, hf, ↓reduceIte, hc]
  have he : V3.leafInput k.val index raw.val (SharedV3.leafPad w k.val) ends =
      leafBytes (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends) := rfl
  rw [he]
  have h2 : ChildProof.heapOf 2 (SharedV3.physical k.val raw.val) =
      (128 + SharedV3.physical k.val raw.val) / 2 ^ (2 + 1) := ChildProof.heapOf_eq _ 2 (by decide)
  have h3 : ChildProof.heapOf 3 (SharedV3.physical k.val raw.val) =
      (128 + SharedV3.physical k.val raw.val) / 2 ^ (3 + 1) := ChildProof.heapOf_eq _ 3 (by decide)
  simp only [show List.range 4 = [0,1,2,3] from rfl, show List.range 2 = [0,1] from rfl,
    List.foldlM_cons, List.foldlM_nil, SharedV3.childStepG, show (0:Nat) ≠ 3 by decide,
    show (1:Nat) ≠ 3 by decide, show (2:Nat) ≠ 3 by decide, ↓reduceIte, bind_assoc, bind_map_left,
    pure_bind, childLevelP_eq, shared_input _ _ _ _ _ 0 (by decide),
    shared_input _ _ _ _ _ 1 (by decide), shared_input _ _ _ _ _ 4 (by decide), childLevelHi, hiSel,
    hk7, hB3, SigGolfCandidate.FtsGrind.node2, and_self, Nat.zero_add, and_true, true_and, show (0:Nat) ≠ 2 by decide,
    show (1:Nat) ≠ 2 by decide, false_and, if_false, if_true]
  congr 1; funext v0; congr 1; funext v1; congr 1; funext v2
  congr 1
  · rw [(nodeIn_parts _ _ _ _ _ _ _ 2).1, (nodeIn_parts _ _ _ _ _ _ _ 2).2.2]
    simp only [bitAt, nodeHeader, hpOf, SharedV3.nodeHPad, show (2:Nat) < 4 by decide, ↓reduceIte,
      ← h2, ChildProof.heapOf, heapOf]
    rfl
  · funext r2
    simp only [preC, rightC, selD, hiSel, bitAt, nodeHeader, hpOf, SharedV3.nodeHPad, show (3:Nat) < 4 by decide,
      ↓reduceIte, ← h3, ChildProof.heapOf, heapOf]
    rfl

theorem postC_of {L : W9Machine.Layout} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9)
    (raw : Fin 128) (ends : List Digest) (x : MachineState) (hf : SharedV3.first k.val = true)
    (hx : SharedChild.Pre L w index k raw ends x) (hphys : SharedV3.physical k.val raw.val = raw.val)
    (hw : widthOf (Chain.base L k) = ftsWidth k.val)
    (r : Nat × Digest) (t : MachineState) (ht : HandPostC (Chain.base L k) raw.val (bankPc raw.val x) r t) :
    SharedChild.PostC L k raw x (r.2, r.1) t := by
  have hc : k.val ≠ 8 := by
    intro h; rw [h] at hf; contradiction
  have hb : 768 ≤ Chain.base L k := by unfold Chain.base coordinateBase Layout.shift; have := k.isLt; omega
  have hh : Chain.base L k - handO raw.val + 16 = SharedChild.handAddr L k raw := by
    unfold SharedChild.handAddr SharedV3.direction SharedV3.lastLevel handO bitAt
    simp only [hf, hc, hphys, ↓reduceIte]
    split_ifs <;> omega
  have ho : Chain.base L k - handO raw.val = SharedChild.outputAddr L k raw := by
    unfold SharedChild.outputAddr
    simp only [hc, ↓reduceIte]
    have hho := handO_cases raw.val
    have := hh
    unfold SharedChild.handAddr at this ⊢
    omega
  refine ⟨?_, ht.a1, ?_, ?_, ?_, ?_, ht.slot1, hw ▸ ht.nle, ?_, ht.rec2b, ht.plain2, ht.saves, ht.scr, ?_⟩
  · rw [ht.pc]
    change (x.getReg .x1 + _) &&& _ = _
    rw [hx.returnPC]
    simp only [hc, ↓reduceIte]
    change (pcOf (L.returnWord k)+BitVec.ofNat 64 (4*75)) &&& ~~~1#64 = _
    rw [W9Drv.SharedBank.pcOf_add_words,pcOf_and_not1]
    have hodd : ¬ k.val % 2 = 1 := by simp only [SharedV3.first, decide_eq_true_eq] at hf; omega
    rw [if_neg hodd]
  · rw [← hh]; exact ht.top
  · rw [ht.a2, ho]
  · intro reg hr'
    simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    exact ht.keep reg hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1
  · rw [ht.slot0, hphys]
    rfl
  · intro h; rw [ht.rec2a h, hphys]; rfl
  · intro addr ha hn
    have hn' : ¬(prefixWrites (Chain.base L k) addr ∨
        (Chain.base L k - handO raw.val ≤ addr ∧ addr < Chain.base L k - handO raw.val + 32) ∨
        (slotA (Chain.base L k) ≤ addr ∧ addr < slotA (Chain.base L k) + 16 ∨ 3400 ≤ Chain.base L k ∧
          slotA (Chain.base L k) + 16 ≤ addr ∧ addr < slotA (Chain.base L k) + 32) ∨
        (1104 ≤ addr ∧ addr < 1144) ∨
        (SCR ≤ addr ∧ addr < SCR + 32)) := by
      intro h; apply hn
      rcases h with h | h | h | h | h
      · left; unfold SharedChild.writes; unfold prefixWrites at h; left; split <;> omega
      · left; unfold SharedChild.writes; right; rw [← ho]; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; exact h
    exact ht.frame addr ha hn'

theorem sharedC_tbsim {L : W9Machine.Layout} {sk : BitVec 256} (k : Fin 9) (raw : Fin 128)
    (hf : SharedV3.first k.val = true)
    (hchild : L.childWord raw = copyBase raw.val)
    (hcode : CopyCodeAt L.image raw.val) (hbank : ChildCodeAt L.image raw.val)
    (hS : CodeAt L.image (pcOf SEARCH) searchWords)
    (hT : CodeAt L.image (pcOf (trampOf raw.val)) (trampWords (trampOf raw.val) SEARCH (siteB raw.val + 1)))
    (hS2 : CodeAt L.image (pcOf (SigGolfCandidate.FtsGrind.s2Base (hiSel raw.val 3)))
      (SigGolfCandidate.FtsGrind.search2Words (hiSel raw.val 3)))
    (hT2 : CodeAt L.image (pcOf (tramp2Of raw.val)) (trampWords (tramp2Of raw.val)
      (SigGolfCandidate.FtsGrind.s2Base (hiSel raw.val 3)) (site2C raw.val + 1)))
    (hlo : 1848 ≤ Chain.base L k) (hB : Chain.base L k < 2 ^ 14)
    (hw : widthOf (Chain.base L k) = ftsWidth k.val)
    (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ends : List Digest) (x : MachineState)
    (hx : SharedChild.Pre L w index k raw ends x) :
    TBSim L.image sk x (17 + (cycR raw.val 0 2 + (lvlSt raw.val 2 + 1 + SigGolfCandidate.FtsGrind.W_SEARCH2) + (lvlSt raw.val 3 + 1 + W_SEARCH (ftsWidth k.val) + 13)) + 0)
      (SharedChild.childProgramG w index k raw ends) (SharedChild.PostC L k raw x) := by
  have hn : k.val < 8 ∧ k.val % 2 = 0 := by
    simpa only [SharedV3.first, decide_eq_true_eq] using hf
  have hphys : SharedV3.physical k.val raw.val = raw.val := by
    simp only [SharedV3.physical, hf, SigGolfCandidate.Research.SharedForest.physicalChild, ↓reduceIte]
  have hp := pre_of_shared w index k raw ends x (bankPc raw.val x) hx (fun _ => rfl) (fun _ => rfl)
    (by rw [hphys]; rfl)
  have hB3 : 3400 ≤ Chain.base L k ↔ k.val ≤ 7 := by
    have := Layout.shift_le L
    have hk := k.isLt
    unfold Chain.base coordinateBase
    omega
  have H := childC_tbsim (sk := sk) raw.isLt hcode hbank hS hT (by simpa only [hphys] using hp) hlo hB rfl
    (by rw [hx.pc, hchild]) hS2 hT2
  rw [hw] at H
  rw [programG_eq w index k raw ends hf _ rfl _ hB3, hphys]
  exact TBSim.bind H (fun r t ht => TBSim.pure (postC_of w index k raw ends x hf hx hphys hw r t ht))
end W9Drv.SharedAProof

namespace W9Drv.SharedBProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M shortHash)
open SigGolfCandidate.FtsGrind (SEARCH searchWords trampWords widthOf groundFold W_SEARCH FUEL slotA SCR WADJ
  ftsWidth)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem programG_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9)
    (raw : Fin 128) (ends : List Digest) (hf : SharedV3.first k.val = false) (hc : k.val ≠ 8) (b : Nat)
    (hb : b = ftsWidth k.val) (B : Nat) (hB : 3400 ≤ B ↔ k.val ≤ 7) :
    SharedChild.childProgramG w index k raw ends =
      childProgramC k.val index (SharedV3.physical k.val raw.val)  b B
        (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends)
        (SharedV3.nodePad w k.val (SharedV3.physical k.val raw.val))
        (SharedV3.sibling w k.val (SharedV3.physical k.val raw.val))
        (SharedV3.nodeTw w k.val (SharedV3.physical k.val raw.val)) >>= fun r => pure (r.2, r.1) := by
  -- TIER2B D1: the D1 proof plus the level-2 step: `childStepG`'s level-2 branch (`coord <= 7`, `groundFoldH (hiOut j 3) 1`)
  -- is `node2 (hiSel j 3) B` on `nodeIn .. 2` by `hB` (`take 32` = left ‖ header, `drop 48` = right, as `preC/rightC` at
  -- level 3); coordinate 8 is the plain `hashSel` (= `node2` plain + `selD`); the nonce sum `0 + 2^64 n2 + n3`.
  subst hb
  have hk7 : k.val ≤ 7 := by have := k.isLt; omega
  have hB3 : 3400 ≤ B := hB.2 hk7
  unfold SharedChild.childProgramG SharedV3.childNG childProgramC
  simp only [SharedV3.lastLevel, hf, Bool.false_eq_true, ↓reduceIte, hc]
  have he : V3.leafInput k.val index raw.val (SharedV3.leafPad w k.val) ends =
      leafBytes (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends) := rfl
  rw [he]
  have h2 : ChildProof.heapOf 2 (SharedV3.physical k.val raw.val) =
      (128 + SharedV3.physical k.val raw.val) / 2 ^ (2 + 1) := ChildProof.heapOf_eq _ 2 (by decide)
  have h3 : ChildProof.heapOf 3 (SharedV3.physical k.val raw.val) =
      (128 + SharedV3.physical k.val raw.val) / 2 ^ (3 + 1) := ChildProof.heapOf_eq _ 3 (by decide)
  simp only [show List.range 5 = [0,1,2,3,4] from rfl, show List.range 2 = [0,1] from rfl,
    show List.range' 4 1 = [4] from rfl,
    List.foldlM_cons, List.foldlM_nil, SharedV3.childStepG, show (0:Nat) ≠ 3 by decide,
    show (1:Nat) ≠ 3 by decide, show (2:Nat) ≠ 3 by decide, show (4:Nat) ≠ 3 by decide, ↓reduceIte, bind_assoc,
    bind_map_left, pure_bind, childLevelP_eq, shared_input _ _ _ _ _ 0 (by decide),
    shared_input _ _ _ _ _ 1 (by decide), shared_input _ _ _ _ _ 4 (by decide), shared_input _ _ _ _ _ 5 (by decide),
    childLevelHi, hiSel, hk7, hB3, SigGolfCandidate.FtsGrind.node2, and_self, Nat.zero_add, and_true, true_and,
    show (0:Nat) ≠ 2 by decide, show (1:Nat) ≠ 2 by decide, show (4:Nat) ≠ 2 by decide, false_and, if_false, if_true]
  congr 1; funext v0; congr 1; funext v1; congr 1; funext v2
  congr 1
  · rw [(nodeIn_parts _ _ _ _ _ _ _ 2).1, (nodeIn_parts _ _ _ _ _ _ _ 2).2.2]
    simp only [bitAt, nodeHeader, hpOf, SharedV3.nodeHPad, show (2:Nat) < 4 by decide, ↓reduceIte,
      ← h2, ChildProof.heapOf, heapOf]
    rfl
  · funext r2
    congr 1
    · simp only [preC, rightC, selD, hiSel, bitAt, nodeHeader, hpOf, SharedV3.nodeHPad, show (3:Nat) < 4 by decide,
        ↓reduceIte, ← h3, ChildProof.heapOf, heapOf]
      rfl

theorem postC_of {L : W9Machine.Layout} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9)
    (raw : Fin 128) (ends : List Digest) (x : MachineState) (hf : SharedV3.first k.val = false) (hc : k.val ≠ 8)
    (hx : SharedChild.Pre L w index k raw ends x)
    (hw : widthOf (Chain.base L k) = ftsWidth k.val)
    (r : Nat × Digest) (t : MachineState)
    (ht : HandPostC (Chain.base L k) (SharedV3.physical k.val raw.val) (bankPc (SharedV3.physical k.val raw.val) x) r t) :
    SharedChild.PostC L k raw x (r.2, r.1) t := by
  have hk0 : k.val ≠ 0 := by intro h0; simp [SharedV3.first, h0] at hf
  have hb : 768 ≤ Chain.base L k := by unfold Chain.base coordinateBase Layout.shift; have := k.isLt; omega
  have hh : Chain.base L k - handO (SharedV3.physical k.val raw.val) + 16 = SharedChild.handAddr L k raw := by
    unfold SharedChild.handAddr SharedV3.direction SharedV3.lastLevel handO bitAt
    simp only [hf, hc, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> omega
  have ho : Chain.base L k - handO (SharedV3.physical k.val raw.val) = SharedChild.outputAddr L k raw := by
    unfold SharedChild.outputAddr
    simp only [hc, ↓reduceIte]
    have hho := handO_cases (SharedV3.physical k.val raw.val)
    omega
  refine ⟨?_, ht.a1, ?_, ?_, ?_, ?_, ht.slot1, hw ▸ ht.nle, ?_, ht.rec2b, ht.plain2, ht.saves, ht.scr, ?_⟩
  · rw [ht.pc]
    change (x.getReg .x1 + _) &&& _ = _
    rw [hx.returnPC]
    simp only [hc, ↓reduceIte]
    change (pcOf (L.returnWord k)+BitVec.ofNat 64 (4*76)) &&& ~~~1#64 = _
    rw [W9Drv.SharedBank.pcOf_add_words,pcOf_and_not1]
    have hodd : k.val % 2 = 1 := by
      have := k.isLt; simp only [SharedV3.first, decide_eq_false_iff_not] at hf; omega
    rw [if_pos hodd]
  · rw [← hh]; exact ht.top
  · rw [ht.a2, ho]
  · intro reg hr'
    simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    exact ht.keep reg hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1
  · rw [ht.slot0]
    rfl
  · intro h; rw [ht.rec2a h]; rfl
  · intro addr ha hn
    have hn' : ¬(prefixWrites (Chain.base L k) addr ∨
        (Chain.base L k - handO (SharedV3.physical k.val raw.val) ≤ addr ∧
          addr < Chain.base L k - handO (SharedV3.physical k.val raw.val) + 32) ∨
        (slotA (Chain.base L k) ≤ addr ∧ addr < slotA (Chain.base L k) + 16 ∨ 3400 ≤ Chain.base L k ∧
          slotA (Chain.base L k) + 16 ≤ addr ∧ addr < slotA (Chain.base L k) + 32) ∨
        (1104 ≤ addr ∧ addr < 1144) ∨
        (SCR ≤ addr ∧ addr < SCR + 32)) := by
      intro h; apply hn
      rcases h with h | h | h | h | h
      · left; unfold SharedChild.writes; unfold prefixWrites at h; left; split <;> omega
      · left; unfold SharedChild.writes; right; rw [← ho]; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; exact h
    exact ht.frame addr ha hn'

theorem sharedC_tbsim {L : W9Machine.Layout} {sk : BitVec 256} (k : Fin 9) (raw : Fin 128)
    (hf : SharedV3.first k.val = false) (hc : k.val ≠ 8)
    (hchild : L.childWord raw = copyBase (SharedV3.physical k.val raw.val))
    (hcode : CopyCodeAt L.image (SharedV3.physical k.val raw.val))
    (hbank : ChildCodeAt L.image (SharedV3.physical k.val raw.val))
    (hS : CodeAt L.image (pcOf SEARCH) searchWords)
    (hT : CodeAt L.image (pcOf (trampOf (SharedV3.physical k.val raw.val)))
      (trampWords (trampOf (SharedV3.physical k.val raw.val)) SEARCH (siteB (SharedV3.physical k.val raw.val) + 1)))
    (hS2 : CodeAt L.image (pcOf (SigGolfCandidate.FtsGrind.s2Base (hiSel (SharedV3.physical k.val raw.val) 3)))
      (SigGolfCandidate.FtsGrind.search2Words (hiSel (SharedV3.physical k.val raw.val) 3)))
    (hT2 : CodeAt L.image (pcOf (tramp2Of (SharedV3.physical k.val raw.val))) (trampWords (tramp2Of (SharedV3.physical k.val raw.val))
      (SigGolfCandidate.FtsGrind.s2Base (hiSel (SharedV3.physical k.val raw.val) 3)) (site2C (SharedV3.physical k.val raw.val) + 1)))
    (hlo : 1848 ≤ Chain.base L k) (hB : Chain.base L k < 2 ^ 14)
    (hw : widthOf (Chain.base L k) = ftsWidth k.val)
    (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ends : List Digest) (x : MachineState)
    (hx : SharedChild.Pre L w index k raw ends x) :
    TBSim L.image sk x (17 + (cycR (SharedV3.physical k.val raw.val) 0 2 + (lvlSt (SharedV3.physical k.val raw.val) 2 + 1 + SigGolfCandidate.FtsGrind.W_SEARCH2) + (lvlSt (SharedV3.physical k.val raw.val) 3 +
        1 + W_SEARCH (ftsWidth k.val) + (cycR (SharedV3.physical k.val raw.val) 4 1 + 13))) + 0)
      (SharedChild.childProgramG w index k raw ends) (SharedChild.PostC L k raw x) := by
  have hpj := SharedV3.physical_lt k.val raw.val raw.isLt
  have hp := pre_of_shared w index k raw ends x (bankPc (SharedV3.physical k.val raw.val) x) hx (fun _ => rfl)
    (fun _ => rfl) rfl
  have hB3 : 3400 ≤ Chain.base L k ↔ k.val ≤ 7 := by
    have := Layout.shift_le L
    have hk := k.isLt
    unfold Chain.base coordinateBase
    omega
  have H := childC_tbsim (sk := sk) hpj hcode hbank hS hT hp hlo hB rfl (by rw [hx.pc, hchild]) hS2 hT2
  rw [hw] at H
  rw [programG_eq w index k raw ends hf hc _ rfl _ hB3]
  exact TBSim.bind H (fun r t ht => TBSim.pure (postC_of w index k raw ends x hf hc hx hw r t ht))
end W9Drv.SharedBProof

namespace W9Drv.SharedCProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M shortHash)
open SigGolfCandidate.FtsGrind (SEARCH searchWords trampWords widthOf groundFold W_SEARCH FUEL slotA SCR WADJ
  ftsWidth)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem programG_eq (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9)
    (raw : Fin 128) (ends : List Digest) (hf : SharedV3.first k.val = false) (hc : k.val = 8) (b : Nat)
    (hb : b = ftsWidth k.val) (B : Nat) (hB : 3400 ≤ B ↔ k.val ≤ 7) :
    SharedChild.childProgramG w index k raw ends =
      childProgramC k.val index (SharedV3.physical k.val raw.val)  b B
        (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends)
        (SharedV3.nodePad w k.val (SharedV3.physical k.val raw.val))
        (SharedV3.sibling w k.val (SharedV3.physical k.val raw.val))
        (SharedV3.nodeTw w k.val (SharedV3.physical k.val raw.val)) >>= fun r => pure (r.2, r.1) := by
  -- TIER2B D1: the D1 proof plus the level-2 step: `childStepG`'s level-2 branch (`coord <= 7`, `groundFoldH (hiOut j 3) 1`)
  -- is `node2 (hiSel j 3) B` on `nodeIn .. 2` by `hB` (`take 32` = left ‖ header, `drop 48` = right, as `preC/rightC` at
  -- level 3); coordinate 8 is the plain `hashSel` (= `node2` plain + `selD`); the nonce sum `0 + 2^64 n2 + n3`.
  subst hb
  have hk7 : ¬ k.val ≤ 7 := by omega
  have hB3 : ¬ 3400 ≤ B := fun h => hk7 (hB.1 h)
  have hd : decide (SharedV3.direction k.val (SharedV3.physical k.val raw.val) = 0) =
      topHi (SharedV3.physical k.val raw.val) := by
    unfold topHi bitAt SharedV3.direction SharedV3.lastLevel
    first
      | (rw [hf]; rfl)
      | (simp only [hf, Bool.false_eq_true, ↓reduceIte])
  unfold SharedChild.childProgramG SharedV3.childNG childProgramC
  simp only [SharedV3.lastLevel, hf, Bool.false_eq_true, ↓reduceIte]
  simp only [if_pos hc]
  have he : V3.leafInput k.val index raw.val (SharedV3.leafPad w k.val) ends =
      leafBytes (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends) := rfl
  rw [he]
  have h2 : ChildProof.heapOf 2 (SharedV3.physical k.val raw.val) =
      (128 + SharedV3.physical k.val raw.val) / 2 ^ (2 + 1) := ChildProof.heapOf_eq _ 2 (by decide)
  have h3 : ChildProof.heapOf 3 (SharedV3.physical k.val raw.val) =
      (128 + SharedV3.physical k.val raw.val) / 2 ^ (3 + 1) := ChildProof.heapOf_eq _ 3 (by decide)
  simp only [show List.range 5 = [0,1,2,3,4] from rfl, show List.range 2 = [0,1] from rfl,
    show List.range' 4 1 = [4] from rfl,
    List.foldlM_cons, List.foldlM_nil, SharedV3.childStepG, show (0:Nat) ≠ 3 by decide,
    show (1:Nat) ≠ 3 by decide, show (2:Nat) ≠ 3 by decide, show (4:Nat) ≠ 3 by decide, ↓reduceIte, bind_assoc,
    bind_map_left, pure_bind, childLevelP_eq, shared_input _ _ _ _ _ 0 (by decide),
    shared_input _ _ _ _ _ 1 (by decide), shared_input _ _ _ _ _ 2 (by decide),
    shared_input _ _ _ _ _ 4 (by decide), shared_input _ _ _ _ _ 5 (by decide), childLevelTop, hiSel, hd,
    hk7, hB3, SigGolfCandidate.FtsGrind.node2, and_false, false_and, if_false, if_true]
  congr 1; funext v0; congr 1; funext v1; congr 1; funext v2
  have hL : ∀ L : List UInt8, L.take 32 ++ (L.drop 32).take 16 ++ L.drop 48 = L := by
    intro L
    have h48 : L.drop 48 = (L.drop 32).drop 16 := by simp [List.drop_drop]
    rw [List.append_assoc, h48, List.take_append_drop, List.take_append_drop]
  have hs : ∀ (j m : Nat) (inp : List UInt8), SharedV3.hashSel (SharedV3.hiOut j m) inp =
      (fun a => selD j m a) <$> SigGolfCandidate.T3.publicHash inp := by
    intro j m inp
    unfold SharedV3.hashSel selD hiSel
    cases SharedV3.hiOut j m <;> simp [V3.hashHi, shortHash]
  simp only [Nat.reduceAdd, hs, bind_map_left, hL, mul_zero, Nat.zero_add]
  congr 1; funext a; congr 1
  simp only [preC, rightC, selD, hiSel, bitAt, nodeHeader, hpOf, SharedV3.nodeHPad, show (3:Nat) < 4 by decide,
    ↓reduceIte, ← h3, ChildProof.heapOf, heapOf]
  rfl

theorem postC_of {L : W9Machine.Layout} (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9)
    (raw : Fin 128) (ends : List Digest) (x : MachineState) (hf : SharedV3.first k.val = false) (hc : k.val = 8)
    (hx : SharedChild.Pre L w index k raw ends x)
    (hw : widthOf (Chain.base L k) = ftsWidth k.val)
    (r : Nat × Digest) (t : MachineState)
    (ht : HandPostC (Chain.base L k) (SharedV3.physical k.val raw.val) (bankPc (SharedV3.physical k.val raw.val) x) r t) :
    SharedChild.PostC L k raw x (r.2, r.1) t := by
  have hb : 768 ≤ Chain.base L k := by unfold Chain.base coordinateBase Layout.shift; have := k.isLt; omega
  have hh : Chain.base L k - valO (SharedV3.physical k.val raw.val) = SharedChild.handAddr L k raw := by
    unfold SharedChild.handAddr SharedV3.direction SharedV3.lastLevel valO bitAt
    simp only [hf, if_pos hc, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> omega
  have ho : Chain.base L k - handO (SharedV3.physical k.val raw.val) = SharedChild.outputAddr L k raw := by
    unfold SharedChild.outputAddr SharedChild.handAddr SharedV3.direction SharedV3.lastLevel handO bitAt
    simp only [hf, if_pos hc, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> omega
  refine ⟨?_, ht.a1, ?_, ?_, ?_, ?_, ht.slot1, hw ▸ ht.nle, ?_, ht.rec2b, ht.plain2, ht.saves, ht.scr, ?_⟩
  · rw [ht.pc]
    change (x.getReg .x1 + _) &&& _ = _
    rw [hx.returnPC]
    simp only [if_pos hc, ↓reduceIte]
    change (pcOf (L.returnWord k)+BitVec.ofNat 64 (4*79)) &&& ~~~1#64 = _
    rw [W9Drv.SharedBank.pcOf_add_words,pcOf_and_not1]
  · rw [← hh]; exact ht.top
  · rw [ht.a2, ho]
  · intro reg hr'
    simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    exact ht.keep reg hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1
  · rw [ht.slot0]
    rfl
  · intro h; rw [ht.rec2a h]; rfl
  · intro addr ha hn
    have hn' : ¬(prefixWrites (Chain.base L k) addr ∨
        (Chain.base L k - handO (SharedV3.physical k.val raw.val) ≤ addr ∧
          addr < Chain.base L k - handO (SharedV3.physical k.val raw.val) + 32) ∨
        (slotA (Chain.base L k) ≤ addr ∧ addr < slotA (Chain.base L k) + 16 ∨ 3400 ≤ Chain.base L k ∧
          slotA (Chain.base L k) + 16 ≤ addr ∧ addr < slotA (Chain.base L k) + 32) ∨
        (1104 ≤ addr ∧ addr < 1144) ∨
        (SCR ≤ addr ∧ addr < SCR + 32)) := by
      intro h; apply hn
      rcases h with h | h | h | h | h
      · left; unfold SharedChild.writes; unfold prefixWrites at h; left; split <;> omega
      · left; unfold SharedChild.writes; right; rw [← ho]; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; exact h
    exact ht.frame addr ha hn'

theorem sharedC_tbsim {L : W9Machine.Layout} {sk : BitVec 256} (k : Fin 9) (raw : Fin 128)
    (hf : SharedV3.first k.val = false) (hc : k.val = 8)
    (hchild : L.childWord raw = copyBase (SharedV3.physical k.val raw.val))
    (hcode : CopyCodeAt L.image (SharedV3.physical k.val raw.val))
    (hbank : ChildCodeAt L.image (SharedV3.physical k.val raw.val))
    (hS : CodeAt L.image (pcOf SEARCH) searchWords)
    (hT : CodeAt L.image (pcOf (trampOf (SharedV3.physical k.val raw.val)))
      (trampWords (trampOf (SharedV3.physical k.val raw.val)) SEARCH (siteB (SharedV3.physical k.val raw.val) + 1)))
    (hS2 : CodeAt L.image (pcOf (SigGolfCandidate.FtsGrind.s2Base (hiSel (SharedV3.physical k.val raw.val) 3)))
      (SigGolfCandidate.FtsGrind.search2Words (hiSel (SharedV3.physical k.val raw.val) 3)))
    (hT2 : CodeAt L.image (pcOf (tramp2Of (SharedV3.physical k.val raw.val))) (trampWords (tramp2Of (SharedV3.physical k.val raw.val))
      (SigGolfCandidate.FtsGrind.s2Base (hiSel (SharedV3.physical k.val raw.val) 3)) (site2C (SharedV3.physical k.val raw.val) + 1)))
    (hlo : 1848 ≤ Chain.base L k) (hB : Chain.base L k < 2 ^ 14)
    (hB3 : Chain.base L k < 3400)
    (hw : widthOf (Chain.base L k) = ftsWidth k.val)
    (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (ends : List Digest) (x : MachineState)
    (hx : SharedChild.Pre L w index k raw ends x) :
    TBSim L.image sk x (17 + (cycR (SharedV3.physical k.val raw.val) 0 2 + (lvlSt (SharedV3.physical k.val raw.val) 2 + 1 + SigGolfCandidate.FtsGrind.W_SEARCH2) + (lvlSt (SharedV3.physical k.val raw.val) 3 +
        1 + W_SEARCH (ftsWidth k.val) + (cycR (SharedV3.physical k.val raw.val) 4 1 + 13))) + 0)
      (SharedChild.childProgramG w index k raw ends) (SharedChild.PostC L k raw x) := by
  have hpj := SharedV3.physical_lt k.val raw.val raw.isLt
  have hp := pre_of_shared w index k raw ends x (bankPc (SharedV3.physical k.val raw.val) x) hx (fun _ => rfl)
    (fun _ => rfl) rfl
  have hB3' : 3400 ≤ Chain.base L k ↔ k.val ≤ 7 := ⟨fun h => absurd h (by omega), fun h => by omega⟩
  have H := childC_tbsim (sk := sk) hpj hcode hbank hS hT hp hlo hB rfl (by rw [hx.pc, hchild]) hS2 hT2
  rw [hw] at H
  rw [programG_eq w index k raw ends hf hc _ rfl _ hB3']
  exact TBSim.bind H (fun r t ht => TBSim.pure (postC_of w index k raw ends x hf hc hx hw r t ht))
end W9Drv.SharedCProof

namespace W9Drv.SharedBank
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.FtsGrind (SEARCH searchWords trampWords widthOf W_SEARCH ftsWidth COPY_FIRST COPY_K8 COPY_ODD)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- E8: the copy routine word of raw child `raw` of coordinate `k` (the dispatch's `childPC`). -/
def copyWord (k : Nat) (raw : Nat) : Nat :=
  if k < 8 ∧ k % 2 = 0 then COPY_FIRST + 32 * raw else if k = 8 then COPY_K8 + 64 * raw else COPY_ODD + 64 * raw

/-- E8: the expand image holds the 384 copy prefixes, their trampolines and `SEARCH`. -/
structure CopyCodes (im : Image) : Prop where
  search : CodeAt im (pcOf SEARCH) searchWords
  copyA : ∀ j < 128, SharedAProof.CopyCodeAt im j
  copyB : ∀ j < 128, SharedBProof.CopyCodeAt im j
  copyC : ∀ j < 128, SharedCProof.CopyCodeAt im j
  /-- VR8: the node-8 bank routines (with `ret`) of the expand image, no longer shared with verify. -/
  bankC : ∀ j < 128, SharedCProof.ChildCodeAt im j
  trampA : ∀ j < 128, CodeAt im (pcOf (SharedAProof.trampOf j))
    (trampWords (SharedAProof.trampOf j) SEARCH (SharedAProof.siteB j + 1))
  trampB : ∀ j < 128, CodeAt im (pcOf (SharedBProof.trampOf j))
    (trampWords (SharedBProof.trampOf j) SEARCH (SharedBProof.siteB j + 1))
  trampC : ∀ j < 128, CodeAt im (pcOf (SharedCProof.trampOf j))
    (trampWords (SharedCProof.trampOf j) SEARCH (SharedCProof.siteB j + 1))
  /-- S5185 (FTS16, TIER2 E9/E12): the two level-2 searches and the 384 level-2 trampolines (each returns to the
  copy word after its level-2 site). -/
  search2 : ∀ hi, CodeAt im (pcOf (SigGolfCandidate.FtsGrind.s2Base hi)) (SigGolfCandidate.FtsGrind.search2Words hi)
  tramp2A : ∀ j < 128, CodeAt im (pcOf (SharedAProof.tramp2Of j)) (trampWords (SharedAProof.tramp2Of j)
    (SigGolfCandidate.FtsGrind.s2Base (SharedAProof.hiSel j 3)) (SharedAProof.site2C j + 1))
  tramp2B : ∀ j < 128, CodeAt im (pcOf (SharedBProof.tramp2Of j)) (trampWords (SharedBProof.tramp2Of j)
    (SigGolfCandidate.FtsGrind.s2Base (SharedBProof.hiSel j 3)) (SharedBProof.site2C j + 1))
  tramp2C : ∀ j < 128, CodeAt im (pcOf (SharedCProof.tramp2Of j)) (trampWords (SharedCProof.tramp2Of j)
    (SigGolfCandidate.FtsGrind.s2Base (SharedCProof.hiSel j 3)) (SharedCProof.site2C j + 1))

/-- E8: cycles of a copy routine (all families), the search excluded. -/
theorem copy_cost_A : ∀ j : Fin 128,
    17 + (SharedAProof.cycR j.val 0 3 + (SharedAProof.lvlSt j.val 3 + 1 + 13)) ≤ 110 := by decide
theorem copy_cost_B : ∀ j : Fin 128,
    17 + (SharedBProof.cycR j.val 0 3 + (SharedBProof.lvlSt j.val 3 + 1 + (SharedBProof.cycR j.val 4 1 + 13))) ≤ 110 := by
  decide
theorem copy_cost_C : ∀ j : Fin 128,
    17 + (SharedCProof.cycR j.val 0 3 + (SharedCProof.lvlSt j.val 3 + 1 + (SharedCProof.cycR j.val 4 1 + 13))) ≤ 110 := by
  decide
/-- q098: the level-2-aware cost of a copy routine (all families), the two searches excluded: with the level-2 stage
(`cycR 0 2 + lvlSt 2 + 1`) in place of the old `cycR 0 3`, the sum is still `<= 110` (so `costG` bounds the
`sharedC_tbsim` cycle counts). -/
theorem copy_cost2_A : ∀ j : Fin 128,
    17 + (SharedAProof.cycR j.val 0 2 + (SharedAProof.lvlSt j.val 2 + 1 + (SharedAProof.lvlSt j.val 3 + 1 + 13))) ≤ 110 := by
  decide
theorem copy_cost2_B : ∀ j : Fin 128,
    17 + (SharedBProof.cycR j.val 0 2 + (SharedBProof.lvlSt j.val 2 + 1 +
      (SharedBProof.lvlSt j.val 3 + 1 + (SharedBProof.cycR j.val 4 1 + 13)))) ≤ 110 := by
  decide
theorem copy_cost2_C : ∀ j : Fin 128,
    17 + (SharedCProof.cycR j.val 0 2 + (SharedCProof.lvlSt j.val 2 + 1 +
      (SharedCProof.lvlSt j.val 3 + 1 + (SharedCProof.cycR j.val 4 1 + 13)))) ≤ 110 := by
  decide

/-- E8: the expand frame bases give the P1 widths (`b = 1` on coordinates 0, 1; `b = 2` on 2..8). -/
theorem widthOf_eRegion (k : Fin 9) : widthOf (9768 - 848 * k.val) = ftsWidth k.val := by
  fin_cases k <;> decide

/-- S5185 (FTS16, TIER2B D2): + `W_SEARCH2` for the level-2 trampoline round trip (an upper bound: the replaced plain
level-2 hash stays counted in the 110). -/
def costG (k : Fin 9) : Nat := 110 + W_SEARCH (ftsWidth k.val) + SigGolfCandidate.FtsGrind.W_SEARCH2

end W9Drv.SharedBank

namespace W9Machine.SharedV3
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest M)
open W9Machine.V3 (regionOffset)

/-- E8: the copy child program on the expander's witness view is `childNG` with the hand-off pads. -/
theorem childNG_viewB (B : Nat) (w : WBytes) (index : Nat) (k : Fin 9) (u : MachineState)
    (raw : Fin 128) (ends : List Digest) (padL padR : Digest)
    (hL : DigAt u (B + regionOffset k.val + 672) padL)
    (hR : DigAt u (B + regionOffset k.val + 160) padR) :
    SharedChild.childProgramG ((viewWB B) w k.val u) index k raw ends = childNG w index k raw ends padL padR := by
  have hn : k.val ≤ 8 := by omega
  let j : Fin 128 := ⟨physical k.val raw.val, physical_lt _ _ raw.isLt⟩
  unfold SharedChild.childProgramG
  rw [(leafPad_viewB B) w k.val u hn padL hL, (nodePad4_viewB B) w k.val u hn j padR hR]
  have hi (l : Nat) (hl : l < 6) (value : Digest) :
      childInput ((viewWB B) w k.val u) index k.val (physical k.val raw.val) padR value l =
        childInput w index k.val (physical k.val raw.val) padR value l :=
    (childInput_viewB B) w index k.val u hn j padR value l hl
  have hs : sibling ((viewWB B) w k.val u) k.val (physical k.val raw.val) 3 =
      sibling w k.val (physical k.val raw.val) 3 := (sibling_viewB B) w k.val u hn j 3 (by decide)
  have hh : nodeHPad ((viewWB B) w k.val u) k.val (physical k.val raw.val) 3 =
      nodeHPad w k.val (physical k.val raw.val) 3 := (nodeHPad_viewB B) w k.val u hn j 3
  have hs2 : sibling ((viewWB B) w k.val u) k.val (physical k.val raw.val) 2 =
      sibling w k.val (physical k.val raw.val) 2 := (sibling_viewB B) w k.val u hn j 2 (by decide)
  have hh2 : nodeHPad ((viewWB B) w k.val u) k.val (physical k.val raw.val) 2 =
      nodeHPad w k.val (physical k.val raw.val) 2 := (nodeHPad_viewB B) w k.val u hn j 2
  unfold childNG
  rcases lastLevel_cases k.val with hl | hl
  all_goals simp only [hl, show List.range 4 = [0,1,2,3] from rfl,
    show List.range 5 = [0,1,2,3,4] from rfl, List.foldlM_cons, List.foldlM_nil, childStepG,
    hi 0 (by decide), hi 1 (by decide), hi 2 (by decide), hi 3 (by decide),
    hi 4 (by decide), hi 5 (by decide), hs, hh, hs2, hh2]
end W9Machine.SharedV3
