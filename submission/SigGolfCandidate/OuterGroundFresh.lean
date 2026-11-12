import SigGolfCandidate.OuterGroundCore
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterGroundFresh
open OracleComp OracleSpec ENNReal OuterGroundCore
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.QuerySpace (queryHeader)
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh (fTrial_header)
open SphincsSecurity (bytesLE_injective)

def Position (coord index heap : Nat) : Prop := coord<9 ∧ index<2^31 ∧ heap<128

theorem trial_ne {coord index heap coord' heap' : Nat}
    (h : Position coord index heap) (h' : Position coord' index heap')
    (hne : ¬(coord'=coord ∧ heap'=heap)) (n m : Nat) (l r l' r' : Digest) :
    trial coord' index heap' m l' r'≠trial coord index heap n l r := by
  intro he
  have hh:=congrArg queryHeader he
  rw [fTrial_header,fTrial_header] at hh
  obtain ⟨e1,-,e3⟩:=ClaudeWCT.WCT9.wctNodeHeader_injective h'.1 h'.2.1 (by have := h'.2.2;omega)
    h.1 h.2.1 (by have := h.2.2;omega) (bytesLE_injective hh)
  exact hne ⟨e1,e3⟩

def Fresh (cache : RCache) (coord index heap : Nat) (l r : Digest) : Prop :=
  ∀ n,cache (trial coord index heap n l r)=none

theorem fresh_after_other {coord index heap coord' heap' : Nat}
    (h : Position coord index heap) (h' : Position coord' index heap')
    (hne : ¬(coord'=coord ∧ heap'=heap)) (cache : RCache) (l r l' r' : Digest)
    (hf : Fresh cache coord' index heap' l' r') (n : Nat) (answer : HashOutput) :
    Fresh (cache.cacheQuery (trial coord index heap n l r) answer) coord' index heap' l' r' := by
  intro m
  exact (QueryCache.cacheQuery_of_ne (cache:=cache) answer (trial_ne h h' hne n m l r l' r')).trans (hf m)

theorem V_two {β : Type} (secret : BitVec 256) (z f₁ f₂ B : ENNReal)
    (coord index heap₁ heap₂ : Nat) (l₁ r₁ l₂ r₂ : Digest)
    (h₁ : Position coord index heap₁) (h₂ : Position coord index heap₂) (hne : heap₂≠heap₁)
    (next : (Nat × Digest) → (Nat × Digest) → M β)
    (hnext : ∀ cache n₁ v₁ n₂ v₂,V secret z (next (n₁,v₁) (n₂,v₂)) cache≤B)
    (fac₁ : z*(((2:ENNReal)^width coord)⁻¹+(1-((2:ENNReal)^width coord)⁻¹)*f₁)≤f₁ ∧ z≤f₁)
    (fac₂ : z*(((2:ENNReal)^width coord)⁻¹+(1-((2:ENNReal)^width coord)⁻¹)*f₂)≤f₂ ∧ z≤f₂)
    (cache : RCache) (fresh₁ : Fresh cache coord index heap₁ l₁ r₁)
    (fresh₂ : Fresh cache coord index heap₂ l₂ r₂) :
    V secret z (nodeAt coord index heap₁ l₁ r₁ >>= fun a =>
      nodeAt coord index heap₂ l₂ r₂ >>= next a) cache≤f₁*(f₂*B) := by
  apply V_nodeAt_bind secret z f₁ (f₂*B) coord index heap₁ l₁ r₁
    (fun a => nodeAt coord index heap₂ l₂ r₂ >>= next a)
    (fun c => Fresh c coord index heap₂ l₂ r₂)
  · intro c hf n answer
    exact fresh_after_other h₁ h₂ (fun he => hne he.2) c l₁ r₁ l₂ r₂ hf n answer
  · intro c hf n answer
    apply V_nodeAt_bind secret z f₂ B coord index heap₂ l₂ r₂ (next (n,value coord heap₁ answer))
      (fun _ => True)
    · intros;trivial
    · intro c' _ n' answer'
      exact hnext _ _ _ _ _
    · exact fac₂
    · trivial
    · exact fresh_after_other h₁ h₂ (fun he => hne he.2) c l₁ r₁ l₂ r₂ hf n answer
  · exact fac₁
  · exact fresh₂
  · exact fresh₁

theorem header_ne_top (coord index heap heap' : Nat) (hc : coord<9) :
    SigGolfCandidate.T3.nodeTweak 3 0 0 heap'≠ClaudeWCT.WCT9.wctNodeHeader coord index heap := by
  intro he
  have ht:=congrArg SigGolfCandidate.T3.tweakTag he
  rw [SigGolfCandidate.T3.nodeTweak_top_tag,ClaudeWCT.WCT9.wctNodeHeader_tweakTag hc] at ht
  rcases SigGolfCandidate.T3.topNodeWord_small_or_special heap' with hs | hs | hs
  · split_ifs at ht <;> omega
  · rw [hs] at ht
    split_ifs at ht <;> norm_num at ht
  · rw [hs] at ht
    split_ifs at ht <;> norm_num at ht

#print axioms header_ne_top
#print axioms V_two
#print axioms trial_ne
#print axioms fresh_after_other
end OuterGroundFresh
