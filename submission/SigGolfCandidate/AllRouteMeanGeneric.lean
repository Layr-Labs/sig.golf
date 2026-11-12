import SigGolfCandidate.AllRouteMeanBase
set_option debug.skipKernelTC false
open scoped BigOperators
namespace ClaudeWCT.Numerics.AllRouteMean
open Finset SigGolfCandidate.AllRoute
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
attribute [local irreducible] Finset.univ
set_option Elab.async false
 def pairWeight (f : Nat → Nat → Nat → Nat) (s0 s1 : Nat) : Nat := 32*f s0 s1 0 + 32*f s0 s1 1
 def oneWeight (f : Nat → Nat → Nat → Nat) (s0 : Nat) : Nat :=
   2*pairWeight f s0 0 + 66*pairWeight f s0 1 + 60*pairWeight f s0 2
 def allWeight (f : Nat → Nat → Nat → Nat) : Nat :=
   64*(1024*oneWeight f 0 + 2048*oneWeight f 1 + 1024*oneWeight f 2)
 theorem sum_route_savings (f : Nat → Nat → Nat → Nat) :
    (∑ i : Fin (2^31), f (ClaudeWCT.Numerics.TopRoute.pathSave (i.val/524288))
      (lowerSave 1 (i.val/4096%128)) (lowerSave 2 (i.val/64%64))) = allWeight f := by
  have hp (a b : Nat) : (∑ z : Fin 64, f a b (lowerSave 2 z.val)) = pairWeight f a b := by
    simpa only [pairWeight] using SigGolfCandidate.AllRoute.pair_sum (f a b) 2 (Or.inl rfl)
  have ho (a : Nat) : (∑ y : Fin 128, pairWeight f a (lowerSave 1 y.val)) = oneWeight f a := by
    simpa only [oneWeight] using SigGolfCandidate.AllRoute.l1_sum (pairWeight f a)
  calc
    _ = 64 * ∑ x : Fin 4096, ∑ y : Fin 128, ∑ z : Fin 64,
        f (ClaudeWCT.Numerics.TopRoute.pathSave x.val) (lowerSave 1 y.val) (lowerSave 2 z.val) :=
      sum_index_digits (fun x y z => f (ClaudeWCT.Numerics.TopRoute.pathSave x) (lowerSave 1 y) (lowerSave 2 z))
    _ = 64 * ∑ x : Fin 4096, ∑ y : Fin 128,
        pairWeight f (ClaudeWCT.Numerics.TopRoute.pathSave x.val) (lowerSave 1 y.val) := by
      congr 1
      exact sum_congr rfl (fun x _ => sum_congr rfl (fun y _ => hp _ _))
    _ = 64 * ∑ x : Fin 4096, oneWeight f (ClaudeWCT.Numerics.TopRoute.pathSave x.val) := by
      congr 1
      exact sum_congr rfl (fun x _ => ho _)
    _ = allWeight f := by
      exact congrArg (fun n : Nat => 64*n) (SigGolfCandidate.AllRoute.root_sum (oneWeight f))
#print axioms sum_route_savings
end ClaudeWCT.Numerics.AllRouteMean
