import SigGolfCandidate.ClaudeWCT.Bank.Spec
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (uniformWordAverage)
open ClaudeWCT.WCT9 (Coord Child Rank child rank wordDigit)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev WProposal := Fin (2 ^ 31) × (Coord → Child × Rank)
def outIdx (x : HashOutput) : Fin (2 ^ 31) := ⟨WCT9.digestIndex x, WCT9.digestIndex_lt x⟩
def proposal (x : HashOutput) : WProposal := (outIdx x, fun k => (child x k, rank x k))
def SlotCovered (X : List HashOutput) (N : HashOutput) (k : Coord) (t : Fin 7) : Prop :=
  ∃ x ∈ X, outIdx x = outIdx N ∧ child x k = child N k ∧ wordDigit (rank N k) t ≤ wordDigit (rank x k) t
def Covered (X : List HashOutput) (N : HashOutput) : Prop := ∀ k t, SlotCovered X N k t
def SlotCoveredP (W : List WProposal) (N : HashOutput) (k : Coord) (t : Fin 7) : Prop :=
  ∃ p ∈ W, p.1 = outIdx N ∧ (p.2 k).1 = child N k ∧ wordDigit (rank N k) t ≤ wordDigit (p.2 k).2 t
def CoveredP (W : List WProposal) (N : HashOutput) : Prop := ∀ k t, SlotCoveredP W N k t
theorem slotCovered_iff (X : List HashOutput) (N : HashOutput) (k : Coord) (t : Fin 7) :
    SlotCovered X N k t ↔ SlotCoveredP (X.map proposal) N k t := by
  constructor
  · rintro ⟨x, hx, h1, h2, h3⟩
    exact ⟨proposal x, List.mem_map_of_mem hx, h1, h2, h3⟩
  · rintro ⟨p, hp, h1, h2, h3⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact ⟨x, hx, h1, h2, h3⟩
theorem covered_iff (X : List HashOutput) (N : HashOutput) : Covered X N ↔ CoveredP (X.map proposal) N :=
  forall_congr' fun k => forall_congr' fun t => slotCovered_iff X N k t
theorem coveredP_append (W V : List WProposal) (N : HashOutput) (h : CoveredP W N) : CoveredP (W ++ V) N := by
  intro k t
  obtain ⟨p, hp, h1, h2, h3⟩ := h k t
  exact ⟨p, List.mem_append_left V hp, h1, h2, h3⟩
noncomputable def scoreP (W : List WProposal) (N : HashOutput) : ENNReal :=
  if WCT9.admissible N = true ∧ CoveredP W N then 1 else 0
noncomputable def score (X : List HashOutput) (N : HashOutput) : ENNReal := scoreP (X.map proposal) N
noncomputable def price (W : List WProposal) : ENNReal := 2 ^ 128 * BPORS.finiteAverage (fun N => scoreP W N)
theorem one_le_score (X : List HashOutput) (N : HashOutput) (hadm : WCT9.admissible N = true)
    (hcov : Covered X N) : 1 ≤ score X N := by
  unfold score scoreP
  rw [if_pos ⟨hadm, (covered_iff X N).mp hcov⟩]
theorem scoreP_append_mono (W V : List WProposal) (N : HashOutput) : scoreP W N ≤ scoreP (W ++ V) N := by
  unfold scoreP
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, coveredP_append W V N h1.2⟩ h2
  · exact bot_le
  · exact le_rfl
theorem score_append_mono (X Y : List HashOutput) (N : HashOutput) : score X N ≤ score (X ++ Y) N := by
  unfold score
  rw [List.map_append]
  exact scoreP_append_mono _ _ N
theorem average_score (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => score X N) = price (X.map proposal) / 2 ^ 128 := by
  unfold price score
  rw [mul_comm, ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
theorem admissible_zero : WCT9.admissible 0 = true := by decide
def AcceptedProposalUniform : Prop :=
  ∀ g : WProposal → ENNReal,
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun x => if WCT9.admissible x = true then g (proposal x) else 0) =
      BPORS.finiteAverage g *
        Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
def AcceptanceBound : Prop :=
  Pr[fun x : HashOutput => WCT9.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / 1996
abbrev Coords := Coord → Child × Rank
def capOkC (c : Coords) : Bool :=
  decide ((∑ k, (WCT9.routineCost (c k).2 + WCT9.childExtra (c k).1)) ≤ WCT9.jointCap)
noncomputable def capSet : Finset Coords := Finset.univ.filter fun c => capOkC c = true
noncomputable def honestCoordLaw (c : Coords) : ENNReal :=
  if capOkC c = true then (capSet.card : ENNReal)⁻¹ else 0
noncomputable def honestLaw : WProposal → ENNReal :=
  ClaudeWCT.Numerics.Law.marked (α := Fin (2 ^ 31)) honestCoordLaw
def HonestLawSum : Prop := ∑ p, honestLaw p = 1
def AcceptedProposalHonest : Prop :=
  ∀ g : WProposal → ENNReal,
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun x => if WCT9.producerAdmissible x = true then g (proposal x) else 0) =
      (∑ p, honestLaw p * g p) *
        Pr[fun x : HashOutput => WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
def ProducerAcceptanceBound : Prop :=
  Pr[fun x : HashOutput => WCT9.producerAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / 1996
def ExcessBound (horizon : Nat) (rate : ENNReal) : Prop :=
  ClaudeWCT.Numerics.Law.lawAvg honestLaw horizon (fun W : List WProposal => price W - 1995 / 1996) ≤ rate
noncomputable def wctSpec (hsum : HonestLawSum) (hacc : AcceptedProposalHonest) (hle : ProducerAcceptanceBound)
    (hprod : ∃ x, WCT9.producerAdmissible x = true) (horizon : Nat) (rate : ENNReal)
    (hexc : ExcessBound horizon rate) : FtsBankSpec WProposal where
  specTheta := 1995 / 1996
  admBound := 1 / 1996
  theta_add_admBound := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by unfold CaseC.theta; finiteness)).mp
    unfold CaseC.theta
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num
  admissible := WCT9.admissible
  producer := WCT9.producerAdmissible
  exists_producer := hprod
  acceptance_le := hle
  proposal := proposal
  law := honestLaw
  law_sum := hsum
  accepted_proposal := hacc
  score := score
  covered := Covered
  one_le_score := one_le_score
  score_append_mono := score_append_mono
  price := price
  average_score := average_score
  horizon := horizon
  excessRate := rate
  excess_le := hexc
end ClaudeWCT.Bank.WCT
