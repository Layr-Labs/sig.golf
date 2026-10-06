import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailImage

/- Actual ordinary execution on the concrete UNSELECTED inline image.
   No runtime-step/fetch outcome is supplied. Only the usual symbolic memory
   access obligations are inputs; CodeAt comes from the checked constructor. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

theorem suffix_codeAt {im : Image} {pc : Word} {ws : List (BitVec 32)}
    (hc : CodeAt im pc ws) (n : Nat) (hn : n ≤ ws.length) :
    CodeAt im (pc+BitVec.ofNat 64 (4*n)) (ws.drop n) := by
  obtain ⟨hlo,hal,hb,hpre⟩:=hc
  have hp : (pc+BitVec.ofNat 64 (4*n)).toNat=pc.toNat+4*n := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [hp];omega
  · rw [hp];omega
  · rw [hp,List.length_drop];omega
  · have hi : (pc.toNat+4*n-0x1000)/4=(pc.toNat-0x1000)/4+n := by omega
    rw [hp,hi]
    simpa only [List.drop_drop] using hpre.drop n

theorem window_codeAt (rank pc : Nat) (hr : rank < 64)
    (hp : armPC rank ≤ pc) (hn : pc-armPC rank ≤ (words rank).length) :
    CodeAt image (pcOf pc) ((words rank).drop (pc-armPC rank)) := by
  have hc:=suffix_codeAt (macro_codeAt rank hr) (pc-armPC rank) hn
  have he : pcOf (armPC rank)+BitVec.ofNat 64 (4*(pc-armPC rank))=pcOf pc := by
    change BitVec.ofNat 64 (0x1000+4*(armPC rank))+BitVec.ofNat 64 (4*(pc-armPC rank))=
      BitVec.ofNat 64 (0x1000+4*pc)
    rw [ofNat_add_ofNat]
    congr 1
    omega
  rw [he] at hc
  exact hc

def headBounds (rank ordinal : Nat) : Bool :=
  decide (armPC rank ≤ chainPC rank ordinal ∧
    chainPC rank ordinal-armPC rank ≤ (words rank).length)
def rungBounds (rank ordinal step : Nat) : Bool :=
  decide (armPC rank ≤ rungPC rank ordinal step ∧
    rungPC rank ordinal step-armPC rank ≤ (words rank).length)
theorem bounds_checks : ((List.range 64).all fun rank =>
    (List.range 3).all fun ordinal => headBounds rank ordinal &&
      ((List.range' (digit rank ordinal+1) (2-digit rank ordinal)).all fun step =>
        rungBounds rank ordinal step))=true := by decide +kernel

theorem head_codeAt (rank ordinal : Nat) (hr : rank < 64) (ho : ordinal < 3) :
    CodeAt image (pcOf (chainPC rank ordinal))
      ((words rank).drop (chainPC rank ordinal-armPC rank)) := by
  have h:=List.all_eq_true.mp bounds_checks rank (List.mem_range.mpr hr)
  have h':=List.all_eq_true.mp h ordinal (List.mem_range.mpr ho)
  simp only [Bool.and_eq_true] at h'
  have he:=of_decide_eq_true h'.1
  exact window_codeAt rank _ hr he.1 he.2

theorem rung_codeAt (rank ordinal step : Nat) (hr : rank < 64) (ho : ordinal < 3)
    (hd : digit rank ordinal < step) (hs : step ≤ 2) :
    CodeAt image (pcOf (rungPC rank ordinal step))
      ((words rank).drop (rungPC rank ordinal step-armPC rank)) := by
  have h:=List.all_eq_true.mp bounds_checks rank (List.mem_range.mpr hr)
  have h':=List.all_eq_true.mp h ordinal (List.mem_range.mpr ho)
  simp only [Bool.and_eq_true] at h'
  have hm : step ∈ List.range' (digit rank ordinal+1) (2-digit rank ordinal) := by
    rw [List.mem_range'_1];omega
  have he:=of_decide_eq_true (List.all_eq_true.mp h'.2 step hm)
  exact window_codeAt rank _ hr he.1 he.2

theorem head_steps (rank ordinal : Nat) (hr : rank < 64) (ho : ordinal < 3)
    (s : MachineState) (hp : s.pc=pcOf (chainPC rank ordinal))
    (hb : (headResult rank ordinal).obligs s) :
    Steps image s (headResult rank ordinal).steps (headResult rank ordinal).cycles
      ((headResult rank ordinal).toState s) :=
  symRun_sound (head_run rank ordinal hr ho) (head_codeAt rank ordinal hr ho) s hp hb

theorem head_fetch (rank ordinal : Nat) (hr : rank < 64) (ho : ordinal < 3)
    (hd : digit rank ordinal < 3) (s : MachineState)
    (hb : (headResult rank ordinal).obligs s) :
    fetch image ((headResult rank ordinal).toState s)=some (.base .ECALL) := by
  have he : (headResult rank ordinal).stop=.ecall := by
    unfold headResult
    rw [if_neg (by omega)]
    split_ifs <;> rfl
  exact symRun_ecall (head_run rank ordinal hr ho) (head_codeAt rank ordinal hr ho) s hb he

theorem rung_steps_fetch (rank ordinal step : Nat) (hr : rank < 64) (ho : ordinal < 3)
    (hd : digit rank ordinal < step) (hs : step ≤ 2) (s : MachineState)
    (hp : s.pc=pcOf (rungPC rank ordinal step))
    (hb : (rungR step (if step=2 then some (slot (51+ordinal)) else none)
      (rungPC rank ordinal step)).obligs s) :
    let r:=rungR step (if step=2 then some (slot (51+ordinal)) else none)
      (rungPC rank ordinal step)
    Steps image s r.steps r.cycles (r.toState s) ∧
      fetch image (r.toState s)=some (.base .ECALL) := by
  let r:=rungR step (if step=2 then some (slot (51+ordinal)) else none)
      (rungPC rank ordinal step)
  have run:=rung_run rank ordinal step hr ho hd hs
  have hc:=rung_codeAt rank ordinal step hr ho hd hs
  exact ⟨symRun_sound run hc s hp hb,symRun_ecall run hc s hb (by simp [r,rungR])⟩

#print axioms head_steps
#print axioms head_fetch
#print axioms rung_steps_fetch
end SigGolfCandidate.T3M.Nonbinary.InlineTail
