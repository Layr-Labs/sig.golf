import SigGolfCandidate.T3.Secc.WotsPrefixGame

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
def PrefixRow (answers : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr input) => ∃ a, WotsExtract.SourceChain a ∧ PrefixRowAt answers a input
  | _ => False
@[irreducible] noncomputable def sourceChains : Finset ChainAddr :=
  (Finset.univ : Finset Layer).biUnion fun lay => (Finset.range (2 ^ 31)).biUnion fun tree =>
    (Finset.range (2 ^ height lay)).biUnion fun leaf =>
      (Finset.range (chainCount lay)).image fun chain => (⟨⟨lay, tree, leaf⟩, chain⟩ : ChainAddr)
theorem height_le (lay : Layer) : height lay ≤ 12 := by
  fin_cases lay <;> decide
theorem mem_sourceChains (a : ChainAddr) : a ∈ sourceChains ↔ WotsExtract.SourceChain a := by
  unfold sourceChains
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨lay, tree, htree, leaf, hleaf, chain, hchain, rfl⟩
    exact ⟨⟨htree, hleaf⟩, hchain⟩
  · intro ha
    exact ⟨a.key.lay, a.key.tree, ha.1.1, a.key.leaf, ha.1.2, a.chain, ha.2, rfl⟩
noncomputable def twoEdgeRate (q : Nat) : ENNReal :=
  ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) / 2 ^ 128
theorem card_digest : ((Fintype.card Digest : ℕ) : ENNReal) = 2 ^ 128 := by
  rw [Fintype.card_bitVec]
  norm_num
end SigGolfCandidate.T3.Security.Wots
