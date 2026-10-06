import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailWindows

/- Actual first top-leaf bank entry and ECALL on the inline image. Finite
   guards read only its genuine original sixteen chunks; the unchanged-window
   theorem closes new-image fetch without a supplied fetch premise. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def bankPC (sh : Nat) : Nat := 96256+64*sh
def bankWords (sh : Nat) : List (BitVec 32) :=
  [if sh%2=0 then 2483291667 else 2533623315,115]
def bankResult (sh : Nat) : Result :=
  ⟨⟨RegFile.init.set .x12 (addC (.reg .x8)
      (BitVec.ofNat 64 (48*(sh%2))-1728)),[],[]⟩,.c (pcOf (bankPC sh+1)),.ecall,1,1⟩
def bankRun (sh : Nat) : Option Result := symRun {} (bankWords sh) (pcOf (bankPC sh)) 3

def bankCheck (sh : Nat) : Bool :=
  let p:=bankPC sh
  lstBeq (fun a b : BitVec 32=>a.toNat==b.toNat)
    (((lChunks.getD (p/256) []).drop (p%256)).take 2) (bankWords sh) &&
  decide ((lChunks.getD (p/256) []).length=256) && rOK (bankRun sh) (bankResult sh)

theorem bank_checks : ((List.range 64).all bankCheck)=true := by decide +kernel

theorem bank_codeAt (sh : Nat) (hsh : sh<64) : CodeAt image (pcOf (bankPC sh)) (bankWords sh) := by
  have hc:=List.all_eq_true.mp bank_checks sh (List.mem_range.mpr hsh)
  simp only [bankCheck,Bool.and_eq_true] at hc
  have he:=lstBeq_eq (fun a b h=>BitVec.eq_of_toNat_eq (by simpa using h)) hc.1.1
  have hl:=of_decide_eq_true hc.1.2
  have hp : bankWords sh <+: (lChunks.getD (bankPC sh/256) []).drop (bankPC sh%256) := by
    rw [←he]
    exact List.take_prefix _ _
  have hw : (bankWords sh).length ≤ 256 := by simp [bankWords]
  have ha : 256*(bankPC sh/256)+bankPC sh%256=bankPC sh := by omega
  have h:=unchanged_row_codeAt (bankPC sh/256) (bankPC sh%256)
    (by unfold bankPC;omega) (by omega) hl (Or.inl (by unfold bankPC;omega)) (bankWords sh) hw hp
  rw [ha] at h
  exact h

theorem bank_steps_fetch (sh : Nat) (hsh : sh<64) (s : MachineState)
    (hpc : s.pc=pcOf (bankPC sh)) :
    Steps image s 1 1 ((bankResult sh).toState s) ∧
      fetch image ((bankResult sh).toState s)=some (.base .ECALL) := by
  have hc:=List.all_eq_true.mp bank_checks sh (List.mem_range.mpr hsh)
  simp only [bankCheck,Bool.and_eq_true] at hc
  have hr:=rOK_eq hc.2
  have ho : (bankResult sh).obligs s := by trivial
  exact ⟨symRun_sound hr (bank_codeAt sh hsh) s hpc ho,
    symRun_ecall hr (bank_codeAt sh hsh) s ho rfl⟩

#print axioms bank_checks
#print axioms bank_codeAt
#print axioms bank_steps_fetch
end SigGolfCandidate.T3M.Nonbinary.InlineTail
