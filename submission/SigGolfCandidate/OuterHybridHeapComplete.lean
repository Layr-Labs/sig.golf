import SigGolfCandidate.OuterHybridNodeComplete
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridHeapComplete
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
open ClaudeWCT.W9.T3.TopMoment (Ev)
open OuterGroundCore OuterHybridComplete OuterHybridNodeComplete

theorem E_heap {β : Type} (secret : BitVec 256) (coord index : Nat) (hc : coord<9) (hi : index<2^31)
    (pads : Nat → PairRoot) (leaves : List Digest)
    (F : β × RCache → ENNReal) (hF : ∀ r,F r≤1)
    (S : Nat → Nat → Prop) (hS : HybridSet index S) (hin : ∀ h,ftsGround coord h→S coord h)
    (hin2 : S coord 2) (hin3 : S coord 3) (next : Array Digest → M β) (B : ENNReal)
    (hnext : ∀ a cache,ftsTreeOK coord a=true → outerOK coord a →
      FreshF index (fun c x=>S c x ∧ c≠coord) cache → Ev secret (next a) cache F≤B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    Ev secret (OuterHeapMoment.heap coord index pads leaves >>= next) cache F≤
      B+24*cF+2*((2:ENNReal)^210)⁻¹ := by
  unfold OuterHeapMoment.heap
  rw [bind_assoc]
  refine le_trans (E_inner secret false index coord hc hi pads leaves F hF S hS hin _
    (B+2*((2:ENNReal)^210)⁻¹) (fun nodes c1 hsz hok h1=>?_) cache hfresh) (le_of_eq (by ring))
  refine E_finish secret coord index hc hi nodes (by omega) F hF
    (fun c x=>S c x ∧ ¬(c=coord ∧ 4≤x)) (fun c x hx=>hS c x hx.1)
    ⟨hin2,by omega⟩ ⟨hin3,by omega⟩ next B (fun a c2 he ho h2=>?_) c1 h1
  exact hnext a c2 (he.trans hok) ho (h2.mono (fun c x hx=>⟨⟨hx.1,fun h=>hx.2 h.1⟩,
    fun h=>hx.2 h.1⟩))

#print axioms E_heap
end OuterHybridHeapComplete
