import SigGolfCandidate.Rv
import SigGolfCandidate.T3M.MemBase
import SigGolfCandidate.Choice.Selector

namespace SigGolfCandidate.Choice.MachineSelect
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

-- p+2 forces a blocked row to p+5. Otherwise p+4 chooses p+5 or p+7.
-- The low path jumps over the high loads; both finish at p+9.
def head : List (BitVec 32) := [0x863883, 0x3e8d193, 0x18663]
def choose : List (BitVec 32) := [0x52803183, 0x19663]
def readLow : List (BitVec 32) := [0x63803, 0xc0006f]
def readHigh : List (BitVec 32) := [0x1063803, 0x1863883]
def words : List (BitVec 32) := head ++ choose ++ readLow ++ readHigh
sym_block headBase := symRun {noAlias := true} head (pcOf 1069) 200
sym_block chooseBase := symRun {noAlias := true} choose (pcOf 1072) 200
sym_block lowBase := symRun {noAlias := true} readLow (pcOf 1074) 200
sym_block highBase := symRun {noAlias := true} readHigh (pcOf 1076) 200

def headRes (p : Word) : Result :=
  {headBase.res with pc := (E.ite .eq
    (.bin .srl (.ld (.bin .add (.reg .x12) (.c 8))) (.c 62)) (.c 0)
    (.c (p + 4 + 4 + 12)) (.c (p + 4 + 4 + 4)))}
def chooseRes (p : Word) : Result :=
  {chooseBase.res with pc := (E.ite .ne (.ld (.c 1320)) (.c 0)
    (.c (p + 4 + 12)) (.c (p + 4 + 4)))}
def lowRes (p : Word) : Result := {lowBase.res with pc := .c (p + 4 + 12)}
def highRes (p : Word) : Result := {highBase.res with pc := .c (p + 4 + 4)}
theorem head_run (p : Word) :
    symRun {noAlias := true} head p 200 = some (headRes p) := by rfl
theorem choose_run (p : Word) :
    symRun {noAlias := true} choose p 200 = some (chooseRes p) := by rfl
theorem low_run (p : Word) :
    symRun {noAlias := true} readLow p 200 = some (lowRes p) := by rfl
theorem high_run (p : Word) :
    symRun {noAlias := true} readHigh p 200 = some (highRes p) := by rfl

/-- Seven one-cycle instructions suffice for every witness, not only honest
hints. A forced-low row uses five. No witness-controlled address arithmetic
remains: the only reads are the two halves of the hash result. -/
theorem select_spec {image : Image} (s : MachineState) (a : BitVec 256)
    (hint : Word) (d p : Nat)
    (hpc : s.pc = pcOf p)
    (hc0 : CodeAt image (pcOf p) head)
    (hc3 : CodeAt image (pcOf (p+3)) choose)
    (hc5 : CodeAt image (pcOf (p+5)) readLow)
    (hc7 : CodeAt image (pcOf (p+7)) readHigh)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d)
    (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 32 ≤ 0x7000)
    (hh : s.getMem 1320#64 = hint)
    (hlo : DigAt s d (a.extractLsb' 0 128))
    (hhi : DigAt s (d+16) (a.extractLsb' 128 128)) :
    ∃ k t, Steps image s k k t ∧ k ≤ 7 ∧ t.pc = pcOf (p+9) ∧
      t.getReg .x16 = (Selector.branchRead (Selector.splitEquiv a) hint).extractLsb' 0 64 ∧
      t.getReg .x17 = (Selector.branchRead (Selector.splitEquiv a) hint).extractLsb' 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x3,.x12,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  have hm0 : s.getMem (s.getReg .x12) = (a.extractLsb' 0 128).extractLsb' 0 64 := by
    rw [h12]; exact hlo.1
  have hm1 : s.getMem (s.getReg .x12 + 8#64) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
    rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hlo.2
  have hm2 : s.getMem (s.getReg .x12 + 16#64) = (a.extractLsb' 128 128).extractLsb' 0 64 := by
    rw [h12, show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; exact hhi.1
  have hm3 : s.getMem (s.getReg .x12 + 24#64) = (a.extractLsb' 128 128).extractLsb' 64 64 := by
    rw [h12, show (24#64 : Word) = BitVec.ofNat 64 24 from rfl, ofNat_add_ofNat]
    simpa [Nat.add_assoc] using hhi.2
  have ho : ∀ o ∈ headBase.res.st.obl, o.holds s := by
    simp [headBase.res, rv_simp, h12, accessValid_iff, MEMORY_BYTES]
    omega
  have es := symRun_sound (head_run (pcOf p)) hc0 s hpc ((Oblig.all_iff _ _).mpr ho)
  let u := (headRes (pcOf p)).toState s
  have ru : RegsExcept s u [.x3,.x17] := by
    intro r hr; cases r <;> simp_all [u, headRes, headBase.res, rv_simp] <;> rfl
  have fu : Frame s u (fun _ => False) := by
    intro A _ _; simp [u, headRes, headBase.res, rv_simp]
  have pu : u.pc = if Selector.group (a.extractLsb' 0 128) = 0 then
      pcOf (p+5) else pcOf (p+3) := by
    simp only [u, headRes, headBase.res, rv_simp, hm1]
    change (if (Selector.group (a.extractLsb' 0 128) == 0) = true then
      pcOf p + 4 + 4 + 12 else pcOf p + 4 + 4 + 4) = _
    by_cases hg : Selector.group (a.extractLsb' 0 128) = 0
    all_goals simp [hg, pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc]
  have h12u : u.getReg .x12 = BitVec.ofNat 64 d := (ru.get (by decide)).trans h12
  by_cases hg : Selector.group (a.extractLsb' 0 128) = 0
  · rw [if_pos hg] at pu
    have el := symRun_sound (low_run (pcOf (p+5))) hc5 u pu (by
      simp [lowRes, lowBase.res, rv_simp, h12u, accessValid_iff, MEMORY_BYTES]; omega)
    let t := (lowRes (pcOf (p+5))).toState u
    have rt : RegsExcept u t [.x16] := by
      intro r hr; cases r <;> simp_all [t, lowRes, lowBase.res, rv_simp] <;> rfl
    have ft : Frame u t (fun _ => False) := by
      intro A _ _; simp [t, lowRes, lowBase.res, rv_simp]
    refine ⟨5,t,es.trans el,by omega,?_,?_,?_,?_,
      (ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · simp [t, lowRes, lowBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.add_assoc, Nat.mul_add]
    · simpa [t, u, lowRes, lowBase.res, headRes, headBase.res, rv_simp,
        Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm0
    · simpa [t, u, lowRes, lowBase.res, headRes, headBase.res, rv_simp,
        Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg] using hm1
    · exact (rt.get (by decide)).trans h12u
  · rw [if_neg hg] at pu
    change Selector.group (a.extractLsb' 0 128) ≠ 0#64 at hg
    have ec := symRun_sound (choose_run (pcOf (p+3))) hc3 u pu (by
      simp [chooseRes, chooseBase.res, rv_simp, accessValid_iff, MEMORY_BYTES])
    let v := (chooseRes (pcOf (p+3))).toState u
    have rv : RegsExcept u v [.x3] := by
      intro r hr; cases r <;> simp_all [v, chooseRes, chooseBase.res, rv_simp] <;> rfl
    have fv : Frame u v (fun _ => False) := by
      intro A _ _; simp [v, chooseRes, chooseBase.res, rv_simp]
    have h12v : v.getReg .x12 = BitVec.ofNat 64 d := (rv.get (by decide)).trans h12u
    have pv : v.pc = if hint = 0#64 then pcOf (p+5) else pcOf (p+7) := by
      by_cases hz : hint = 0#64
      all_goals simp [v, u, chooseRes, chooseBase.res, headRes, headBase.res, rv_simp, hh,
        pcOf, ofNat_add_ofNat, Nat.mul_add, Nat.add_assoc, hz]
    by_cases hz : hint = 0#64
    · rw [if_pos hz] at pv
      have el := symRun_sound (low_run (pcOf (p+5))) hc5 v pv (by
        simp [lowRes, lowBase.res, rv_simp, h12v, accessValid_iff, MEMORY_BYTES]; omega)
      let t := (lowRes (pcOf (p+5))).toState v
      have rt : RegsExcept v t [.x16] := by
        intro r hr; cases r <;> simp_all [t, lowRes, lowBase.res, rv_simp] <;> rfl
      have ft : Frame v t (fun _ => False) := by
        intro A _ _; simp [t, lowRes, lowBase.res, rv_simp]
      refine ⟨7,t,(es.trans ec).trans el,by omega,?_,?_,?_,?_,
        ((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
      · simp [t, lowRes, lowBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.add_assoc, Nat.mul_add]
      · simpa [t, v, u, lowRes, lowBase.res, chooseRes, chooseBase.res, headRes, headBase.res,
          rv_simp, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg, hz] using hm0
      · simpa [t, v, u, lowRes, lowBase.res, chooseRes, chooseBase.res, headRes, headBase.res,
          rv_simp, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg, hz] using hm1
      · exact (rt.get (by decide)).trans h12v
    · rw [if_neg hz] at pv
      have eh := symRun_sound (high_run (pcOf (p+7))) hc7 v pv (by
        simp [highRes, highBase.res, rv_simp, h12v, accessValid_iff, MEMORY_BYTES]; omega)
      let t := (highRes (pcOf (p+7))).toState v
      have rt : RegsExcept v t [.x16,.x17] := by
        intro r hr; cases r <;> simp_all [t, highRes, highBase.res, rv_simp] <;> rfl
      have ft : Frame v t (fun _ => False) := by
        intro A _ _; simp [t, highRes, highBase.res, rv_simp]
      refine ⟨7,t,(es.trans ec).trans eh,by omega,?_,?_,?_,?_,
        ((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
      · simp [t, highRes, highBase.res, rv_simp, pcOf, ofNat_add_ofNat, Nat.add_assoc, Nat.mul_add]
      · simpa [t, v, u, highRes, highBase.res, chooseRes, chooseBase.res, headRes, headBase.res,
          rv_simp, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg, hz] using hm2
      · simpa [t, v, u, highRes, highBase.res, chooseRes, chooseBase.res, headRes, headBase.res,
          rv_simp, Selector.branchRead, Selector.branchOffset, Selector.splitEquiv, hg, hz] using hm3
      · exact (rt.get (by decide)).trans h12v

end SigGolfCandidate.Choice.MachineSelect

#print axioms SigGolfCandidate.Choice.MachineSelect.select_spec
