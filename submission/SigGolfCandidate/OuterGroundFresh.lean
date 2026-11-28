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

/-- C46: a fold position (heap `2..127`: pair-mates share the tag base and are told apart on the fold heaps only). -/
def Position (coord index heap : Nat) : Prop := coord<9 ∧ index<2^31 ∧ (2≤heap ∧ heap<128)

theorem trial_ne {coord index heap coord' heap' : Nat}
    (h : Position coord index heap) (h' : Position coord' index heap')
    (hne : ¬(coord'=coord ∧ heap'=heap)) (n m : Nat) (l r l' r' : Digest) :
    trial coord' index heap' m l' r'≠trial coord index heap n l r := by
  intro he
  have hh:=congrArg queryHeader he
  rw [fTrial_header,fTrial_header] at hh
  obtain ⟨e1,-,e3⟩:=ClaudeWCT.WCT9.wctNodeHeader_injective_of h'.1 h'.2.1 (by have := h'.2.2;omega)
    h.1 h.2.1 (by have := h.2.2;omega)
    (Or.inl ⟨ClaudeWCT.WCT9.ftsTwoOk_of h'.2.2.1 h'.2.2.2,ClaudeWCT.WCT9.ftsTwoOk_of h.2.2.1 h.2.2.2⟩)
    (bytesLE_injective hh)
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
  -- C31: separated by the low word (coordinate 1's two-word tag 240 equals the special top label's tag). C47: the FTS
  -- node words are `≥ 2 ^ 32` (top labels that large have tags 113 and 0); coordinate 8's swapped heaps carry the
  -- labels 929 * 2^50, 0x1fc0c0000, 0x7f00000, 21684, none a top label.
  intro he
  have hl:=congrArg SigGolfCandidate.T3.tweakLow he
  have ht:=congrArg SigGolfCandidate.T3.tweakTag he
  rw [SigGolfCandidate.T3.nodeTweak_top_low] at hl
  rw [SigGolfCandidate.T3.nodeTweak_top_tag, ClaudeWCT.WCT9.wctNodeHeader_tweakTag hc] at ht
  have hlow:=ClaudeWCT.WCT9.wctNodeHeader_toNat hc index heap
  unfold SigGolfCandidate.T3.tweakLow at hl
  rw [hlow] at hl
  have hN32 := ClaudeWCT.W9.T3M.Extract.ftsNodeLowN_ge32 index coord heap
  have hL32 := ClaudeWCT.W9.T3M.Extract.ftsNodeLow2_ge32 index coord
  have hltN := ClaudeWCT.WCT9.ftsNodeLowN_lt index coord heap
  have hlt2 := ClaudeWCT.WCT9.ftsNodeLow2_lt index coord
  by_cases hs : SigGolfCandidate.T3.ftsSwap8 coord heap
  · have hn : ¬ SigGolfCandidate.T3.FtsNew heap := by obtain ⟨-, h3, h6⟩ := hs; unfold SigGolfCandidate.T3.FtsNew; omega
    rw [if_neg hn, if_pos hs] at hl
    obtain ⟨-, h3, h6⟩ := hs
    have hv := SigGolfCandidate.T3.ftsSwapLabel8_cases h3 h6
    have hlv := SigGolfCandidate.T3.ftsSwapLabel8_lt h3 h6
    generalize SigGolfCandidate.T3.ftsSwapLabel8 heap = v at hl hv hlv
    generalize ClaudeWCT.WCT9.ftsNodeLow2 index coord = B at hl hL32 hlt2
    rcases SigGolfCandidate.T3.topNodeWord_small_or_special heap' with hs | hs | hs | hs | hs <;>
      first | omega | (have := SigGolfCandidate.T3.TopNine.cases hs; omega) |
        (unfold SigGolfCandidate.T3.TopStep at hs; omega)
  · simp only [if_neg hs] at hl ht
    generalize ClaudeWCT.WCT9.ftsNodeLowN index coord heap = A at hl hN32 hltN
    generalize ClaudeWCT.WCT9.ftsNodeLow2 index coord = B at hl hL32 hlt2
    rcases SigGolfCandidate.T3.topNodeWord_small_or_special heap' with hs | hs | hs | hs | hs <;>
      first | (split_ifs at hl ht <;> omega) | (have := SigGolfCandidate.T3.TopNine.cases hs; split_ifs at hl ht <;> omega) |
        (unfold SigGolfCandidate.T3.TopStep at hs; split_ifs at hl ht <;> omega)

#print axioms header_ne_top
#print axioms V_two
#print axioms trial_ne
#print axioms fresh_after_other
end OuterGroundFresh
