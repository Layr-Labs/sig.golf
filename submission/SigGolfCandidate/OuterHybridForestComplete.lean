import SigGolfCandidate.OuterHybridCoordinateComplete
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridForestComplete
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
open ClaudeWCT.W9.T3.TopMoment (Ev Ev_bind Ev_pure Ev_le_of_support)
open OuterGroundCore OuterHybridComplete OuterHybridNodeComplete OuterForestBudget OuterHybridCoordinateComplete

def coordOKb (first : Bool) (coord : Nat) (nodes : Array Digest) : Bool :=
  ftsTreeOK coord nodes && (if first then true else zeroOk coord (nodes.getD 2 0) && zeroOk coord (nodes.getD 3 0))
theorem coordOKb_true {first : Bool} {coord : Nat} {nodes : Array Digest} (h : coordOK first coord nodes) :
    coordOKb first coord nodes=true := by cases first <;> simp_all [coordOKb,coordOK,outerOK]

def pairCheck (index pair : Nat) (st : Bool × PairRoot) : M (Bool × PairRoot) := do
  let a ← buildCoord true index (2*pair) child0 rank0 (fun _=>st.2)
  let b ← buildCoord false index (2*pair+1) child0 rank0 (nodesPair a.1)
  pure (st.1 && coordOKb true (2*pair) a.1 && coordOKb false (2*pair+1) b.1,(b.1.getD 2 0,b.1.getD 3 0))
def forestCheck (index : Nat) : M Bool := do
  let s1 ← pairCheck index 0 (true,ftsStart)
  let s2 ← pairCheck index 1 s1
  let s3 ← pairCheck index 2 s2
  let s4 ← pairCheck index 3 s3
  let c ← buildCoord false index 8 child0 rank0 (fun _=>s4.2)
  pure (s4.1 && coordOKb false 8 c.1)

noncomputable def eps : ENNReal := ((2:ENNReal)^210)⁻¹
noncomputable def pairFailure : ENNReal := 48*cF+2*eps
noncomputable def lastFailure : ENNReal := 24*cF+2*eps
noncomputable def forestFailure : ENNReal := 216*cF+10*eps

theorem hybridSet_above (k index : Nat) (hi : index<2^31) : HybridSet index (AllAbove k) := by
  intro c h hs
  exact ⟨hs.2.1,hi,hs.2.2.imp_right And.right⟩

theorem E_coordAbove {β : Type} (secret : BitVec 256) (first : Bool) (coord index : Nat)
    (hc : coord<9) (hi : index<2^31) (ho : first=false→OuterCoord coord)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (next : Array Digest × List Digest → M β) (F : β × RCache → ENNReal) (hF : ∀ r,F r≤1) (B : ENNReal)
    (hnext : ∀ a cache,coordOK first coord a.1 → FreshF index (AllAbove (coord+1)) cache →
      Ev secret (next a) cache F≤B)
    (cache : RCache) (hfresh : FreshF index (AllAbove coord) cache) :
    Ev secret (buildCoord first index coord selected word pads >>= next) cache F≤B+coordFailure first := by
  apply E_buildCoord secret first coord index hc hi selected word pads F hF (AllAbove coord)
    (hybridSet_above coord index hi) (fun h hg=>⟨le_rfl,hc,Or.inl hg⟩)
    (fun hf=>⟨⟨le_rfl,hc,Or.inr ⟨ho hf,Or.inl rfl⟩⟩,⟨le_rfl,hc,Or.inr ⟨ho hf,Or.inr rfl⟩⟩⟩)
    next B (fun a c hok hs=>hnext a c hok (hs.mono (fun c x hx=>⟨⟨by have := hx.1;omega,hx.2.1,hx.2.2⟩,by have := hx.1;omega⟩))) cache hfresh

theorem E_pairCheck {β : Type} (secret : BitVec 256) (index p : Nat) (hi : index<2^31) (hp : p<4)
    (st : Bool × PairRoot) (next : Bool × PairRoot → M β) (F : β × RCache → ENNReal) (hF : ∀ r,F r≤1)
    (B : ENNReal) (hnext : ∀ a cache,a.1=st.1 → FreshF index (AllAbove (2*p+2)) cache → Ev secret (next a) cache F≤B)
    (cache : RCache) (hfresh : FreshF index (AllAbove (2*p)) cache) :
    Ev secret (pairCheck index p st >>= next) cache F≤B+pairFailure := by
  unfold pairCheck
  simp only [bind_assoc,pure_bind]
  refine le_trans (E_coordAbove secret true (2*p) index (by omega) hi (by simp) child0 rank0 (fun _=>st.2)
    _ F hF (B+coordFailure false) (fun a c1 ha h1=>?_) cache hfresh) (le_of_eq ?_)
  · refine E_coordAbove secret false (2*p+1) index (by omega) hi (fun _=>Or.inl (by omega)) child0 rank0
      (nodesPair a.1) _ F hF B (fun b c2 hb h2=>?_) c1 h1
    apply hnext _ c2
    · simp [coordOKb_true ha,coordOKb_true hb]
    · simpa only [Nat.add_assoc] using h2
  · simp only [coordFailure,pairFailure,eps,Bool.false_eq_true,↓reduceIte,add_zero]
    ring

theorem E_forestCheck (secret : BitVec 256) (index : Nat) (hidx : index < 2 ^ 31) (cache : RCache)
    (hfresh : FreshF index (AllAbove 0) cache) :
    Ev secret (forestCheck index) cache (fun r => if r.1 then 0 else 1) ≤ forestFailure := by
  have hF : ∀ r : Bool × RCache, (if r.1 then (0 : ℝ≥0∞) else 1) ≤ 1 := fun r => by split <;> simp
  unfold forestCheck
  refine le_trans (E_pairCheck secret index 0 hidx (by decide) _ _ _ hF (lastFailure + pairFailure + pairFailure + pairFailure)
    (fun s1 c1 hs1 h1 => ?_) cache hfresh) (le_of_eq (by unfold forestFailure lastFailure pairFailure;ring))
  refine le_trans (E_pairCheck secret index 1 hidx (by decide) _ _ _ hF (lastFailure + pairFailure + pairFailure)
    (fun s2 c2 hs2 h2 => ?_) c1 h1) le_rfl
  refine le_trans (E_pairCheck secret index 2 hidx (by decide) _ _ _ hF (lastFailure + pairFailure)
    (fun s3 c3 hs3 h3 => ?_) c2 h2) le_rfl
  refine le_trans (E_pairCheck secret index 3 hidx (by decide) _ _ _ hF (lastFailure)
    (fun s4 c4 hs4 h4 => ?_) c3 h3) le_rfl
  refine le_trans (E_coordAbove secret false 8 index (by decide) hidx (fun _=>Or.inr rfl)
    child0 rank0 (fun _=>s4.2) _ _ hF 0 (fun a c5 hok _=>?_) c4 h4) (le_of_eq ?_)
  · rw [Ev_pure]
    simp [hs4,hs3,hs2,hs1,coordOKb_true hok]
  · simp [coordFailure,lastFailure,eps]

#print axioms E_pairCheck
#print axioms E_forestCheck
end OuterHybridForestComplete
