import SigGolfCandidate.OuterCopyFlatC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCopyLayer2C
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedCProof
open SigGolfCandidate.FtsGrind

def Changes (B j X : Nat) : Prop := X=B+padO j 2 ∨ X=B+padO j 2+8 ∨ far16 B X

theorem prepare (j : Fin 128) {B k index : Nat} {leaf pads sibs tws : Nat→Digest} {u s6 : MachineState}
    (hu : ChildPre j.val B k index leaf pads sibs tws u) (hB : B<2^14) (hlo : 1848≤B)
    (r2 : Nat×HashOutput) (h6 : L2Post j.val B k index u (decide (SEL16≤B)) r2 s6) :
    ∃ pads2 : Nat→Digest,
      ChildPre j.val B k index leaf pads2 sibs tws (virt2 j.val B u s6) ∧
      MidC j.val B k index (virt2 j.val B u s6) 3 (selD j.val 3 r2.2) s6 ∧
      (∀ l,l≠2→pads2 l=pads l) ∧ Frame u (virt2 j.val B u s6) (Changes B j.val) := by
  let child:=j.val
  have hj:=j.isLt
  have h8:=hu.base8
  have hhi:=hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hbl2:=blk_bounds j.val hj 2 (by decide)
  have hfresh:=pad2_fresh j.val hj
  have hfar : ∀ X,B≤X→X<B+1024→¬far16 B X := by
    intro X h1 h2
    simp only [far16,slot16,SCR16]
    omega
  set u2 := virt2 j.val B u s6 with hu2d
  have vu : ∀ o, o + 8 ≤ 1024 → away j.val o = true →
      u2.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho ha
    have := away_spec ha
    rw [hu2d, virt2_getMem j.val B u s6 _ (by omega) (by unfold padO; omega), if_neg]
    rintro (h | h | h)
    · omega
    · omega
    · exact hfar _ (by omega) (by omega) h
  have dv : ∀ o (d : Digest), o + 16 ≤ 1024 → away j.val o = true → away j.val (o + 8) = true → DigAt u (B + o) d →
      DigAt u2 (B + o) d := fun o d ho h1 h2 hd =>
    DigAt.of_eq hd (vu o (by omega) h1) (by rw [Nat.add_assoc]; exact vu (o + 8) (by omega) h2)
  let pads2 : Nat → Digest := fun l => if l = 2 then rdD u2 (B + padO j.val 2) else pads l
  have hu2 : ChildPre j.val B k index leaf pads2 sibs tws u2 :=
    { pc := hu.pc
      base8 := h8
      baseHi := hu.baseHi
      t0 := hu.t0
      s0 := hu.s0
      a0 := hu.a0
      a1 := hu.a1
      w0 := hu.w0
      heaps := hu.heaps
      leafAt := fun i hi => by
        have a1 := hfresh.2 (2 * i) (by omega)
        have a2 := hfresh.2 (2 * i + 1) (by omega)
        rw [show leafO + 8 * (2 * i) = leafO + 16 * i by ring] at a1
        rw [show leafO + 8 * (2 * i + 1) = leafO + 16 * i + 8 by ring] at a2
        have := dv (leafO + 16 * i) (leaf i) (by unfold leafO; omega) a1 a2
          (by rw [← Nat.add_assoc]; exact hu.leafAt i hi)
        rwa [← Nat.add_assoc] at this
      padAt := fun l hl => by
        by_cases e : l = 2
        · subst e; simp only [pads2, if_true]; exact digAt_rdD _ _
        · simp only [pads2, e, if_false]
          have hb := blk_bounds j.val hj l hl
          exact dv _ _ (by unfold padO; omega) ((hfresh.1 l hl).1 e).1 ((hfresh.1 l hl).1 e).2 (hu.padAt l hl)
      sibAt := fun l hl => by
        have hb := blk_bounds j.val hj l hl
        have := sibO_cases j.val l hl
        exact dv _ _ (by omega) (hfresh.1 l hl).2.1 (hfresh.1 l hl).2.2.1 (hu.sibAt l hl)
      twAt := fun l hl => by
        have hb := blk_bounds j.val hj l hl
        have := dv (blkO j.val l + 16) (tws l) (by omega) (hfresh.1 l hl).2.2.2.1
          (by rw [Nat.add_assoc]; exact (hfresh.1 l hl).2.2.2.2) (by rw [← Nat.add_assoc]; exact hu.twAt l hl)
        rwa [← Nat.add_assoc] at this }
  refine ⟨pads2,hu2,h6.mid,?_,?_⟩
  · intro l hl
    simp only [pads2,if_neg hl]
  · intro X hX hn
    change ¬(X=B+padO j.val 2 ∨ X=B+padO j.val 2+8 ∨ far16 B X) at hn
    rw [hu2d,virt2_getMem j.val B u s6 X hX (by unfold padO;omega),if_neg hn]

#print axioms prepare
end OuterCopyLayer2C
