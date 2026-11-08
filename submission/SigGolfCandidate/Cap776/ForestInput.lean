import SigGolfCandidate.Cap776.CountInput
set_option debug.skipKernelTC false
namespace SigGolfResearch.ProbabilityRows
open Finset
open ClaudeWCT.Numerics
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathPacked
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
attribute [local irreducible] row SharedPathList.coordinate SharedPathPacked.product SharedPathPacked.addFirst

theorem pair_of_rows (r : Nat) (chunks : Nat → Nat)
    (hc : ∀ t, t≤r → row r t=chunks t) :
    pairPacked r=∑ t ∈ range (r+1),Nat.choose r t*chunks t := by
  unfold pairPacked
  apply sum_congr rfl
  intro t ht
  rw [hc t (by have h := mem_range.mp ht;omega)]

theorem forest_of_inputs (r p : Nat) (q : Cell)
    (hp : pairPacked r=p) (hq : SharedPathList.coordinate 128 r=q) :
    forestPacked r=(spread 11 p)^4*spread 10 q.1 := by
  unfold forestPacked
  rw [hp,hq]
end SigGolfResearch.ProbabilityRows
