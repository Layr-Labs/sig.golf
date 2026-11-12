import SigGolfCandidate.OuterHybridHeapComplete
import SigGolfCandidate.OuterForestBudget
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridCoordinateComplete
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
open ClaudeWCT.W9.T3.TopMoment (Ev Ev_bind Ev_le_of_support)
open OuterGroundCore OuterHybridComplete OuterHybridNodeComplete OuterHybridHeapComplete OuterForestBudget

def coordOK (first : Bool) (coord : Nat) (nodes : Array Digest) : Prop :=
  ftsTreeOK coord nodes=true ∧ (first=false→ outerOK coord nodes)
noncomputable def coordFailure (first : Bool) : ENNReal := 24*cF+(if first then 0 else 2*((2:ENNReal)^210)⁻¹)

theorem E_buildCoord {β : Type} (secret : BitVec 256) (first : Bool) (coord index : Nat)
    (hc : coord<9) (hi : index<2^31) (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (F : β × RCache → ENNReal) (hF : ∀ r,F r≤1)
    (S : Nat → Nat → Prop) (hS : HybridSet index S) (hin : ∀ h,ftsGround coord h→S coord h)
    (hinOuter : first=false→S coord 2 ∧ S coord 3)
    (next : Array Digest × List Digest → M β) (B : ENNReal)
    (hnext : ∀ a cache,coordOK first coord a.1 → FreshF index (fun c x=>S c x ∧ c≠coord) cache →
      Ev secret (next a) cache F≤B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    Ev secret (buildCoord first index coord selected word pads >>= next) cache F≤B+coordFailure first := by
  have hp:=OuterCoordinate.notF_prelude secret index S (outerSet_of_hybrid hS) first coord selected word pads
  unfold buildCoord
  cases first
  · simp only [Bool.false_eq_true,↓reduceIte]
    unfold OuterCoordinate.build
    simp only [bind_assoc]
    rw [Ev_bind]
    refine Ev_le_of_support secret _ cache (fun st hst=>?_)
    have hs:=freshF_preserved secret hp cache hfresh st hst
    refine le_trans (E_heap secret coord index hc hi pads st.1.1 F hF S hS hin
      (hinOuter rfl).1 (hinOuter rfl).2 _ B (fun nodes c hok ho hfresh=>?_) st.2 hs) ?_
    · simpa only [pure_bind] using hnext (nodes,st.1.2) c ⟨hok,fun _=>ho⟩ hfresh
    · simp [coordFailure,add_assoc]
  · simp only [↓reduceIte]
    unfold buildA
    simp only [bind_assoc]
    rw [Ev_bind]
    refine Ev_le_of_support secret _ cache (fun st hst=>?_)
    have hs:=freshF_preserved secret hp cache hfresh st hst
    refine le_trans (E_inner secret true index coord hc hi pads st.1.1 F hF S hS hin _ B
      (fun nodes c _ hok hfresh=>?_) st.2 hs) ?_
    · simpa only [pure_bind] using hnext (nodes,st.1.2) c ⟨hok,by simp⟩
        (hfresh.mono (fun c x hx=>⟨hx.1,fun h=>hx.2 h.1⟩))
    · simp [coordFailure]

#print axioms E_buildCoord
end OuterHybridCoordinateComplete
