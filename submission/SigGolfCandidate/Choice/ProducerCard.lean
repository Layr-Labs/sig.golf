import SigGolfCandidate.Choice.Encoding

/-! Accepted output count for the actual canonical producer, not a fixed-half surrogate. -/
namespace ClaudeWCT.WCT9
open SigGolfCandidate.T3 SigGolfCandidate.Choice
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false
attribute [local irreducible] Finset.univ Finset.filter

noncomputable def topProducerOutputs : Finset HashOutput :=
  Finset.univ.filter fun answer => (producerDecode 0 (encodingAnswer 0 answer)).isSome

theorem topProducerOutputs_card : topProducerOutputs.card =
    (Gated.accepted topProducerWords Selector.blocked).card := by
  unfold topProducerOutputs
  refine Finset.card_equiv Selector.splitEquiv ?_
  intro answer
  rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
  rw [← mem_topProducerWords, encodingAnswer_top_choose]
  exact Gated.choose_mem topProducerWords Selector.blocked (Selector.splitEquiv answer)

attribute [local irreducible] topProducerWords topProducerOutputs Gated.accepted

theorem topProducerOutputs_lower :
    topProducerWords.card * (7 * 2^126 - topProducerWords.card) ≤ topProducerOutputs.card := by
  -- Use the current Digest Fintype instance; importing the BitVec-specialized
  -- bound makes elaboration compare two large universe enumerations.
  have hh := Gated.quarter_lower topProducerWords Selector.blocked (2^126)
    (by norm_num) Selector.blocked_card
  exact hh.trans (le_of_eq topProducerOutputs_card.symm)

end ClaudeWCT.WCT9

#print axioms ClaudeWCT.WCT9.topProducerOutputs_card
#print axioms ClaudeWCT.WCT9.topProducerOutputs_lower
