import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailSteps
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsGoodOne

/- Physical invariants for the new final3 chain schedule. These preserve
   all original NCtx memory/header/padding laws, but use the new actual PCs.
   No old GoodQ execution outcome is aliased or supplied. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def index (ordinal : Nat) : Nat := 51+ordinal

def Input (c : NCtx) (s0 : MachineState) (rank ordinal : Nat)
    (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (index ordinal)) acc s ∧ acc.length=index ordinal ∧
    s.pc=pcOf (chainPC rank ordinal)

def Step (c : NCtx) (s0 : MachineState) (rank ordinal step : Nat)
    (acc : List Digest) (v : Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn (index ordinal)) acc s ∧ acc.length=index ordinal ∧
    c.HdrOk (index ordinal) s ∧ DigAt s (c.blk (index ordinal)+48) v ∧
    s.getReg .x10=BitVec.ofNat 64 (c.blk (index ordinal)) ∧
    (step<2 → s.getReg .x12=BitVec.ofNat 64 (c.blk (index ordinal)+48)) ∧
    s.pc=pcOf (rungPC rank ordinal step)

def Pre (c : NCtx) (s0 : MachineState) (rank ordinal step : Nat)
    (acc : List Digest) (v : Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn (index ordinal)) acc s ∧ acc.length=index ordinal ∧
    s.getMem (BitVec.ofNat 64 (c.blk (index ordinal)+16))=
      BitVec.ofNat 64 (c.w0 (index ordinal)+2^8*step) ∧
    s.getMem (BitVec.ofNat 64 (c.blk (index ordinal)+24))=c.padHeader (index ordinal) ∧
    DigAt s (c.blk (index ordinal)+48) v ∧
    s.getReg .x10=BitVec.ofNat 64 (c.blk (index ordinal)) ∧
    s.getReg .x12=BitVec.ofNat 64 (if step=2 then slot (index ordinal) else c.blk (index ordinal)+48) ∧
    s.pc=pcOf (queryPC rank ordinal step) ∧ fetch image s=some (.base .ECALL)

def End (c : NCtx) (s0 : MachineState) (rank ordinal : Nat)
    (ends : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (index ordinal+1)) ends s ∧ ends.length=index ordinal+1 ∧
    s.pc=pcOf (chainPC rank (ordinal+1))

theorem chainPC_succ (rank ordinal : Nat) :
    chainPC rank (ordinal+1)=chainPC rank ordinal+pieceLen (digit rank ordinal) := by
  simp [chainPC,List.range_succ,List.map_append,List.sum_append,Nat.add_assoc]

theorem last_index (ordinal : Nat) (ho : ordinal<3) : NCtx.last (index ordinal)=2 := by
  unfold NCtx.last NCtx.topMax mx index
  rw [if_neg (by omega)]

theorem final_query_next (rank ordinal : Nat) (hd : digit rank ordinal<3) :
    queryPC rank ordinal 2+1=chainPC rank (ordinal+1) := by
  rw [chainPC_succ]
  unfold queryPC pieceLen
  split_ifs <;> omega

theorem query_rung_next (rank ordinal step : Nat) (hd : digit rank ordinal ≤ step) (hs : step<2) :
    queryPC rank ordinal step+1=rungPC rank ordinal (step+1) := by
  unfold rungPC
  unfold queryPC
  split_ifs <;> omega

#print axioms chainPC_succ
#print axioms final_query_next
#print axioms query_rung_next
end SigGolfCandidate.T3M.Nonbinary.InlineTail
