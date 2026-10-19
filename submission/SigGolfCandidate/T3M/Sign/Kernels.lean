import SigGolfCandidate.T3M.Sign.Basic
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Keygen.Leaf

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Layer selections admissible digestSearch counterSearch decode
  attemptLimit counterLimit chainCount target Selection)
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((selections N).getD c ⟨0, []⟩).bucket * 128 + ((selections N).getD c ⟨0, []⟩).leaves.getD j 0
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
def dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)
structure DsPre (s : MachineState) (rho : Digest) (m : Message) : Prop where
  pc : s.pc = pcOf 153
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
def DsPost (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => Failed t
  | some (_, N), t => t.pc = pcOf 172 ∧ t.getReg .x5 = 0 ∧ admissible (selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW
def dsCost : Nat := attemptLimit * 700 + 100
def DigestSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (rho : Digest) (m : Message), DsPre s rho m →
    TBSim image sk s dsCost (digestSearch rho m 0 attemptLimit) (DsPost s)
end SigGolfCandidate.T3M.Sign
