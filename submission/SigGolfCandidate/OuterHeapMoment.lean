import SigGolfCandidate.OuterInnerMoment
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterHeapMoment
open OracleComp OracleSpec ENNReal OuterGroundCore OuterGroundFresh OuterInnerMoment
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh

def finish (coord index : Nat) (nodes : Array Digest) : M (Array Digest) := do
  let a←nodeAt coord index 3 (nodes.getD 6 0) (nodes.getD 7 0)
  let b←nodeAt coord index 2 (nodes.getD 4 0) (nodes.getD 5 0)
  pure ((nodes.set! 3 a.2).set! 2 b.2)

theorem V_finish (secret : BitVec 256) (z f : ENNReal) (coord index : Nat) (nodes : Array Digest)
    (hc : coord<9) (hi : index<2^31) (fac : FacFH z (width coord) f)
    (cache : RCache) (hf : FreshF index (fun c h => c=coord ∧ (h=2 ∨ h=3)) cache) :
    V secret z (finish coord index nodes) cache≤f^2 := by
  have h:=V_two secret z f f 1 coord index 3 2 (nodes.getD 6 0) (nodes.getD 7 0)
    (nodes.getD 4 0) (nodes.getD 5 0) ⟨hc,hi,by decide⟩ ⟨hc,hi,by decide⟩ (by decide)
    (fun a b => pure ((nodes.set! 3 a.2).set! 2 b.2))
    (fun _ _ _ _ _ => by simp [V_pure]) fac fac cache
    (fun n => hf coord 3 ⟨rfl,Or.inr rfl⟩ n _ _) (fun n => hf coord 2 ⟨rfl,Or.inl rfl⟩ n _ _)
  simpa [finish,pow_two,mul_assoc] using h

def heap (coord index : Nat) (pads : Nat → PairRoot) (leaves : List Digest) : M (Array Digest) :=
  innerHeap false index coord pads leaves >>= finish coord index

theorem V_heap (secret : BitVec 256) (z f g o : ENNReal) (hz : 1≤z) (coord index : Nat)
    (hc : coord<9) (hi : index<2^31) (pads : Nat → PairRoot) (leaves : List Digest)
    (hf : FacF z coord f) (hg : FacG z coord g) (ho : FacFH z (width coord) o)
    (S : Nat → Nat → Prop) (hS : GroundSet index S)
    (hin : ∀ h,ftsGround coord h→S coord h) (cache : RCache) (hcache : FreshF index S cache)
    (houter : FreshF index (fun c h => c=coord ∧ (h=2 ∨ h=3)) cache) :
    V secret z (heap coord index pads leaves) cache≤(z^96*(g^16*(f^8*z^4)))*o^2 := by
  unfold heap
  refine (V_bind_le secret z _ _ cache (o^2) ?_).trans (mul_le_mul' ?_ le_rfl)
  · intro result hr
    apply V_finish secret z o coord index result.1 hc hi ho result.2
    apply freshF_preserved secret (notF_innerHeap false index coord pads leaves secret _ ?_ hc ?_) cache houter result hr
    · intro c h hp
      rcases hp with ⟨rfl,h|h⟩ <;> subst h <;> exact ⟨hc,hi,by decide,by decide⟩
    · intro c h hp
      rcases hp with ⟨_,h|h⟩ <;> omega
  · exact inner_cost secret z f g hz false index coord hc hi pads hf hg leaves S hS hin cache hcache

#print axioms V_finish
#print axioms V_heap
end OuterHeapMoment
