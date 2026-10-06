import SigGolfCandidate.W9Machine.WctChainContract
import SigGolfCandidate.W9Machine.WctN600Data

set_option autoImplicit false
namespace W9Machine.N600
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
abbrev Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 600) (u : MachineState) : Prop :=
  Chain.Pre L w index k j (embed rank) u
abbrev Post := Chain.Post
abbrev writes := Chain.writes
abbrev clobbers := Chain.clobbers
def program (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 600) : M (List Digest) :=
  V3.chainProgram w index k j (embed rank)
def Good (L : Layout) (rank : Fin 600) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : List Digest → OracleComp HashSpec Obs),
    Pre L w index k j rank u →
    (∀ ends t, Post L w index k j u ends t → GoodQFor L.image t N C Q A (K ends)) →
    GoodQFor L.image u (N + 89) (C + 89) Q (A + rankCost rank)
      (ccM (program w index k j rank) K)
def AllGood (L : Layout) : Prop := ∀ rank : Fin 600, Good L rank
def NineCost (ranks : Fin 9 → Fin 600) : Nat :=
  ((List.finRange 9).map fun k => rankCost (ranks k)).sum
def ProducerCostOK (ranks : Fin 9 → Fin 600) : Prop := NineCost ranks ≤ 700
end W9Machine.N600
