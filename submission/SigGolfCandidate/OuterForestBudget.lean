import SigGolfCandidate.OuterCoordinateAvoid
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterForestBudget
open OracleComp OracleSpec ENNReal OuterGroundCore
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open SigGolfCandidate.T3M (allQ_bind allQ_pure)

def OuterCoord (c : Nat) : Prop := c%2=1 ∨ c=8
instance (c : Nat) : Decidable (OuterCoord c) := inferInstanceAs (Decidable (_ ∨ _))
def AllAbove (k c h : Nat) : Prop := k≤c ∧ c<9 ∧ (ftsGround c h ∨ (OuterCoord c ∧ (h=2 ∨ h=3)))

theorem outerSet_above (k index : Nat) (hi : index<2^31) : OuterGroundAvoid.OuterSet index (AllAbove k) := by
  intro c h hp
  refine ⟨hp.2.1,hi,?_,?_⟩
  rcases hp.2.2 with hg | ⟨_,rfl|rfl⟩
  · have hh:=ftsGround_ge8 hg;omega
  · decide
  · decide
  rcases hp.2.2 with hg | ⟨_,rfl|rfl⟩
  · unfold ftsGround at hg;omega
  · decide
  · decide

def buildA (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat → PairRoot) : M (Array Digest × List Digest) := do
  let state←OuterCoordinate.prelude true index coord selected word pads
  let nodes←OuterInnerMoment.innerHeap true index coord pads state.1
  pure (nodes,state.2)

theorem buildA_eq (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    buildA index coord selected word pads=buildSharedCoordinate true index coord selected word pads := by
  simp only [buildA,OuterCoordinate.prelude,OuterCoordinate.children,buildSharedCoordinate,
    OuterInnerMoment.innerHeap,sharedHeap,bind_assoc,↓reduceIte]
  rfl

theorem notF_buildA (secret : BitVec 256) (index coord : Nat) (hc : coord<9) (S : Nat → Nat → Prop)
    (hS : OuterGroundAvoid.OuterSet index S) (hco : ∀ c h,S c h→c≠coord)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (buildA index coord selected word pads) (NotF secret index S) := by
  unfold buildA
  exact allQ_bind (OuterCoordinate.notF_prelude secret index S hS true coord selected word pads) fun st =>
    allQ_bind (OuterCoordinateAvoid.notF_inner hS coord hc hco true pads st.1) (fun _ => allQ_pure _)

noncomputable def coordBound (z f g o : ENNReal) (first : Bool) : ENNReal :=
  z^3449*f^8*g^16*(if first then 1 else o^2)

def buildCoord (first : Bool) (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    M (Array Digest × List Digest) := if first then buildA index coord selected word pads else
      OuterCoordinate.build index coord selected word pads

theorem notF_buildCoord (secret : BitVec 256) (index coord : Nat) (hc : coord<9) (S : Nat → Nat → Prop)
    (hS : OuterGroundAvoid.OuterSet index S) (hco : ∀ c h,S c h→c≠coord) (first : Bool)
    (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (buildCoord first index coord selected word pads) (NotF secret index S) := by
  cases first
  · exact OuterCoordinateAvoid.notF_build hS coord hc hco selected word pads
  · exact notF_buildA secret index coord hc S hS hco selected word pads

theorem V_buildCoord (secret : BitVec 256) (z f g o : ENNReal) (hz : 1≤z) (first : Bool) (index coord : Nat)
    (hc : coord<9) (hi : index<2^31) (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (hf : FacF z coord f) (hg : FacG z coord g) (ho : FacFH z (width coord) o)
    (hfirst : first=false→OuterCoord coord) (cache : RCache) (hs : FreshF index (AllAbove coord) cache) :
    V secret z (buildCoord first index coord selected word pads) cache≤coordBound z f g o first := by
  have hOld : FreshF index (Above coord) cache := hs.mono (fun c h hp => ⟨hp.1,hp.2.1,Or.inl hp.2.2⟩)
  cases first with
  | false =>
    have hOuter : FreshF index (fun c h => c=coord ∧ (h=2 ∨ h=3)) cache := by
      intro c h hp n l r
      rcases hp with ⟨he,hp⟩
      subst c
      exact hs coord h ⟨le_rfl,hc,Or.inr ⟨hfirst rfl,hp⟩⟩ n l r
    have h:=OuterCoordinate.V_build secret z f g o hz coord index hc hi selected word pads hf hg ho
      (Above coord) (groundSet_above _ hi) (fun h hh => ⟨le_rfl,hc,hh⟩) cache hOld hOuter
    change V secret z (OuterCoordinate.build index coord selected word pads) cache≤_
    have he : z^3349*((z^96*(g^16*(f^8*z^4)))*o^2)=coordBound z f g o false := by unfold coordBound;simp only [Bool.false_eq_true,↓reduceIte];ring
    exact he ▸ h
  | true =>
    have h:=V_buildSharedCoordinate secret z f g hz true index coord hc hi selected word pads hf hg
      (Above coord) (groundSet_above _ hi) (fun h hh => ⟨le_rfl,hc,hh⟩) pure 1
      (fun _ _ _ => by simp [V_pure]) cache hOld
    simpa [buildCoord,buildA_eq,coordBound,CB_eq] using h

theorem V_buildCoord_bind {β : Type} (secret : BitVec 256) (z f g o B : ENNReal) (hz : 1≤z)
    (first : Bool) (index coord : Nat) (hc : coord<9) (hi : index<2^31) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) (hf : FacF z coord f) (hg : FacG z coord g) (ho : FacFH z (width coord) o)
    (hfirst : first=false→OuterCoord coord) (next : Array Digest × List Digest → M β)
    (hnext : ∀ a cache,FreshF index (AllAbove (coord+1)) cache→V secret z (next a) cache≤B)
    (cache : RCache) (hs : FreshF index (AllAbove coord) cache) :
    V secret z (buildCoord first index coord selected word pads >>= next) cache≤coordBound z f g o first*B := by
  have hfuture : FreshF index (AllAbove (coord+1)) cache := hs.mono (fun c h hp => ⟨by have := hp.1;omega,hp.2⟩)
  have hav:=notF_buildCoord secret index coord hc (AllAbove (coord+1)) (outerSet_above _ index hi)
    (fun c h hp => by have := hp.1;omega) first selected word pads
  exact (V_bind_le secret z _ _ cache B (fun result hr =>
    hnext _ _ (freshF_preserved secret hav cache hfuture result hr))).trans
      (mul_le_mul' (V_buildCoord secret z f g o hz first index coord hc hi selected word pads hf hg ho hfirst cache hs) le_rfl)

#print axioms V_buildCoord_bind
#print axioms outerSet_above
#print axioms buildA_eq
#print axioms notF_buildA
end OuterForestBudget
