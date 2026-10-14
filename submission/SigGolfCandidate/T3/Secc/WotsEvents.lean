import SigGolfCandidate.T3.BPORS

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
structure LeafAddr where
  lay : Layer
  tree : Nat
  leaf : Nat
  deriving DecidableEq
structure ChainAddr where
  key : LeafAddr
  chain : Nat
  deriving DecidableEq
def dummyDigits (lay : Layer) : List Nat :=
  if lay.val = 0 then dummyTop
  else List.replicate 10 6 ++ List.replicate 12 5 ++ List.replicate 20 4 ++ [target lay - 200]
def chainRow (a : ChainAddr) (step : Nat) (value : Digest) : HashInput :=
  chainInput a.key.lay a.key.tree a.key.leaf a.chain step value
abbrev Entry := HashInput × HashOutput
def low (output : HashOutput) : Digest := output.extractLsb' 0 128
/-- A trace row of chain `a` at `step` with input `value` whose answer's relevant half is `out` (campaign S1: the last
step of chain 0 of a lower layer keeps the high half). -/
def SeenRow (trace : List Entry) (a : ChainAddr) (step : Nat) (value out : Digest) : Prop :=
  ∃ answer, (chainRow a step value, answer) ∈ trace ∧ projHalf (chainHigh a.key.lay a.chain step) answer = out
def entriesOf (answers : Answers) (qs : List Spec.Domain) : List Entry :=
  qs.filterMap fun q => match q with
    | .inl (.inr input) => some (input, answers (.inl (.inr input)))
    | _ => none
end SigGolfCandidate.T3.Security.Wots
