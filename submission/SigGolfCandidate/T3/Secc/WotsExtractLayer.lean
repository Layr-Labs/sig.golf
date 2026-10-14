import SigGolfCandidate.T3.Secc.WotsExtractWord

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def WotsPrimitiveSrc (answers : Answers) (trace : List Entry) : Prop :=
  (∃ L, SourceLeaf L ∧ EncodingMatchAt answers trace L) ∨ StructuralHitSrc answers trace ∨
    (∃ a, SourceChain a ∧ TwoEdgeAt answers trace a) ∨
    (∃ a b, SourceChain a ∧ SourceChain b ∧ a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, SourceChain a ∧ MarkerAt answers trace a ∧ ContactAt answers trace a)
theorem WotsPrimitiveSrc.toPrimitive {answers : Answers} {trace : List Entry} (h : WotsPrimitiveSrc answers trace) :
    WotsPrimitive answers trace := by
  rcases h with ⟨L, -, h⟩ | h | ⟨a, -, h⟩ | ⟨a, b, -, -, hab, ha, hb⟩ | ⟨a, -, hm, hc⟩
  · exact Or.inl ⟨L, h⟩
  · exact Or.inr (Or.inl h.toStructuralHit)
  · exact Or.inr (Or.inr (Or.inl ⟨a, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, ha, hb⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hm, hc⟩)))
section mono
variable {answers : Answers} {trace trace' : List Entry}
theorem seenRow_mono {a : ChainAddr} {step : Nat} {value out : Digest} (h : SeenRow trace a step value out)
    (hsub : ∀ e ∈ trace, e ∈ trace') : SeenRow trace' a step value out := by
  obtain ⟨answer, hm, hl⟩ := h
  exact ⟨answer, hsub _ hm, hl⟩
theorem contactAt_mono {a : ChainAddr} (h : ContactAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    ContactAt answers trace' a := by
  obtain ⟨hd, value, hs⟩ := h
  exact ⟨hd, value, seenRow_mono hs hsub⟩
theorem twoEdgeAt_mono {a : ChainAddr} (h : TwoEdgeAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    TwoEdgeAt answers trace' a := by
  obtain ⟨hd, start, middle, h1, h2⟩ := h
  exact ⟨hd, start, middle, seenRow_mono h1 hsub, seenRow_mono h2 hsub⟩
theorem encodingMatchAt_mono {L : LeafAddr} (h : EncodingMatchAt answers trace L) (hsub : ∀ e ∈ trace, e ∈ trace') :
    EncodingMatchAt answers trace' L := by
  obtain ⟨message, counter, answer, hm, hne, hd⟩ := h
  exact ⟨message, counter, answer, hsub _ hm, hne, hd⟩
theorem markerAt_mono {a : ChainAddr} (h : MarkerAt answers trace a) (hsub : ∀ e ∈ trace, e ∈ trace') :
    MarkerAt answers trace' a := by
  obtain ⟨message, counter, answer, digits, hm, hne, hd, hl, hu⟩ := h
  exact ⟨message, counter, answer, digits, hsub _ hm, hne, hd, hl, hu⟩
theorem structuralHit_mono (h : StructuralHit answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    StructuralHit answers trace' := by
  obtain ⟨position, input, answer, hm, hpos, hb, hc, hh⟩ := h
  exact ⟨position, input, answer, hsub _ hm, hpos, hb, hc, hh⟩
theorem WotsPrimitiveSrc.mono (h : WotsPrimitiveSrc answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveSrc answers trace' := by
  rcases h with ⟨L, hL, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨L, hL, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
end mono
end SigGolfCandidate.T3.Security.WotsExtract
