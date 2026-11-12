import SigGolfCandidate.OuterHeapMoment
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterCoordinate
open OracleComp OracleSpec ENNReal OuterGroundCore
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh

def children (first : Bool) (index coord : Nat) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) (coefs : List Digest) : M (List Digest × List Digest) :=
  (List.range 128).foldlM (fun (state : List Digest × List Digest) j => do
    let (root,values)←buildChildH (128+j) index coord (rawChild first j) word coefs (pads (j/64)).1
    pure (state.1++[root],if j=selected.val then values else state.2)) ([],[])

def prelude (first : Bool) (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    M (List Digest × List Digest) := do
  let coefs←ftsCoefs index coord
  children first index coord selected word pads coefs

theorem bound_children (first : Bool) (index coord : Nat) (hc : coord<9) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) (coefs : List Digest) :
    Bound (FtsQuery index) (fun _ => True) 3328 (children first index coord selected word pads coefs) := by
  unfold children
  exact Bound.foldlM_range_le 128 _ (fun _ _ => True) (fun _ => 26) ([],[]) trivial
    (fun j hj state _ => (ftsBound_buildChildH index (128+j) coord (rawChild first j) word coefs
      (pads (j/64)).1 hc (rawChild_lt first j hj)).bind' (l:=0)
      (fun child _ => .pure _ 0 trivial) (by simp [ClaudeWCT.WCT9.childCost])) (fun _ _ => trivial) (by simp)

theorem bound_prelude (first : Bool) (index coord : Nat) (hc : coord<9) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) : Bound (FtsQuery index) (fun _ => True) 3349 (prelude first index coord selected word pads) := by
  unfold prelude
  exact (ftsBound_ftsCoefs index coord hc).bind' (l:=3328)
    (fun coefs _ => bound_children first index coord hc selected word pads coefs) (by decide)

theorem notF_prelude (secret : BitVec 256) (index : Nat) (S : Nat → Nat → Prop)
    (hS : OuterGroundAvoid.OuterSet index S) (first : Bool) (coord : Nat) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) : AllQueriesSatisfy (prelude first index coord selected word pads) (NotF secret index S) := by
  unfold prelude children
  exact SigGolfCandidate.T3M.allQ_bind (OuterGroundAvoid.notF_ftsCoefs hS coord)
    (fun coefs => OuterGroundAvoid.notF_children hS first coord word selected pads coefs)

def build (index coord : Nat) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    M (Array Digest × List Digest) := do
  let state←prelude false index coord selected word pads
  let nodes←OuterHeapMoment.heap coord index pads state.1
  pure (nodes,state.2)

theorem V_build (secret : BitVec 256) (z f g o : ENNReal) (hz : 1≤z) (coord index : Nat)
    (hc : coord<9) (hi : index<2^31) (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (hf : FacF z coord f) (hg : FacG z coord g) (ho : FacFH z (width coord) o)
    (S : Nat → Nat → Prop) (hS : GroundSet index S) (hin : ∀ h,ftsGround coord h→S coord h)
    (cache : RCache) (hs : FreshF index S cache)
    (hou : FreshF index (fun c h => c=coord ∧ (h=2 ∨ h=3)) cache) :
    V secret z (build index coord selected word pads) cache≤z^3349*((z^96*(g^16*(f^8*z^4)))*o^2) := by
  have hS' : OuterGroundAvoid.OuterSet index S := by
    intro c h hp
    have hh:=(hS c h hp).heap
    exact ⟨(hS c h hp).1,(hS c h hp).2.1,by omega,by omega⟩
  have hO : OuterGroundAvoid.OuterSet index (fun c h => c=coord ∧ (h=2 ∨ h=3)) := by
    intro c h hp
    rcases hp with ⟨rfl,h|h⟩ <;> subst h <;> exact ⟨hc,hi,by decide,by decide⟩
  unfold build
  refine (V_bind_le secret z _ _ cache ((z^96*(g^16*(f^8*z^4)))*o^2) ?_).trans
    (mul_le_mul' (V_of_bound (bound_prelude false index coord hc selected word pads) secret z hz cache) le_rfl)
  intro result hr
  have hsf:=freshF_preserved secret (notF_prelude secret index S hS' false coord selected word pads) cache hs result hr
  have hof:=freshF_preserved secret (notF_prelude secret index _ hO false coord selected word pads) cache hou result hr
  have he:=OuterHeapMoment.V_heap secret z f g o hz coord index hc hi pads result.1.1 hf hg ho S hS hin result.2 hsf hof
  calc
    _ ≤ V secret z (OuterHeapMoment.heap coord index pads result.1.1) result.2*1 :=
      V_bind_le secret z _ _ result.2 1 (fun _ _ => by simp [V_pure])
    _ ≤ _ := by simpa using he

#print axioms V_build
#print axioms bound_prelude
#print axioms notF_prelude
end OuterCoordinate
