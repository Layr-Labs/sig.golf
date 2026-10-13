import SigGolfCandidate.T3.Secc.LargeCouplingSplit

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem Known.mono {D D' : Coord → Prop} (h : ∀ c, D c → D' c) {c : Coord} (hk : Known D c) : Known D' c := by
  induction hk with
  | base hc => exact .base (h _ hc)
  | node _ ih => exact .node ih
def Clear (A : Answers) (K : Coord → Prop) (X : HashInput) (y : HashOutput) : Prop :=
  (∀ N : CanonGraph.Node, Extract.posOf X = some N.toPos →
      ¬(X ≠ Extract.honestInput A N.toPos ∧ y.extractLsb' 0 128 = honestValue A (.inl N))) ∧
  (∀ N : CanonGraph.Node, Extract.posOf X = some N.toPos → ∀ c b, childSlots N = [(c, b)] →
      slotValue X b = honestValue A c → K c) ∧
  (∀ (L : CanonEncoding.EncLeaf) (m : Digest) (ctr : BitVec 32), X = Wots.encodingRow L.toWots m ctr →
      ¬(Wots.referenceInput A L.toWots ≠ some X ∧
        decode L.1.lay (y.extractLsb' 0 128) = some (Wots.referenceDigits A L.toWots)))
theorem Clear.mono {A : Answers} {K K' : Coord → Prop} {X : HashInput} {y : HashOutput}
    (h : Clear A K X y) (hK : ∀ c, K c → K' c) : Clear A K' X y :=
  ⟨h.1, fun N hpos c b hs hv => hK c (h.2.1 N hpos c b hs hv), h.2.2⟩
def EventsAgree (A : Answers) (events : List FirstHit.QueryEvent) : Prop :=
  ∀ event ∈ events, SourceReplay.IsHash event.input → A event.input = event.answer
def chargeOf (events : List FirstHit.QueryEvent) : Nat := (events.map fun event => FullGame.queryCharge event.input).sum
end SigGolfCandidate.T3.Security.LargeCoupling
