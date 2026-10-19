import SigGolfCandidate.T3_BPORS
set_option Elab.async false

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
noncomputable def leafMsg (answers : Answers) (L : LeafAddr) : Digest :=
  if h : L.lay.val < 3 then Extract.honestRoot answers ⟨L.lay.val + 1, by omega⟩ (L.tree * 2 ^ height L.lay + L.leaf)
  else Extract.honestForest answers (L.tree * 2 ^ height L.lay + L.leaf)
noncomputable def referenceSearch (answers : Answers) (L : LeafAddr) : Option (BitVec 32 × List Nat) :=
  evalWithAnswerFn answers (counterSearch L.lay L.tree L.leaf (leafMsg answers L) 0 counterLimit)
def dummyDigits (lay : Layer) : List Nat :=
  if lay.val = 0 then dummyTop
  else List.replicate 10 6 ++ List.replicate 12 5 ++ List.replicate 20 4 ++ [target lay - 200]
noncomputable def referenceDigits (answers : Answers) (L : LeafAddr) : List Nat :=
  ((referenceSearch answers L).map Prod.snd).getD (dummyDigits L.lay)
noncomputable def depth (answers : Answers) (a : ChainAddr) : Nat :=
  (referenceDigits answers a.key).getD a.chain 0
noncomputable def frontierValue (answers : Answers) (a : ChainAddr) : Digest :=
  honestChainValue answers a.key.lay a.key.tree a.key.leaf a.chain
    (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain) (depth answers a)
def chainRow (a : ChainAddr) (step : Nat) (value : Digest) : HashInput :=
  chainInput a.key.lay a.key.tree a.key.leaf a.chain step value
abbrev Entry := HashInput × HashOutput
def low (output : HashOutput) : Digest := output.extractLsb' 0 128
def SeenRow (trace : List Entry) (a : ChainAddr) (step : Nat) (value out : Digest) : Prop :=
  ∃ answer, (chainRow a step value, answer) ∈ trace ∧ low answer = out
def ContactAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  1 ≤ depth answers a ∧ ∃ value, SeenRow trace a (depth answers a - 1) value (frontierValue answers a)
def TwoEdgeAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  2 ≤ depth answers a ∧ ∃ start middle, SeenRow trace a (depth answers a - 2) start middle ∧
    SeenRow trace a (depth answers a - 1) middle (frontierValue answers a)
def encodingRow (L : LeafAddr) (message : Digest) (counter : BitVec 32) : HashInput :=
  pad64 (encodingInput L.lay L.tree L.leaf message counter)
noncomputable def referenceInput (answers : Answers) (L : LeafAddr) : Option HashInput :=
  (referenceSearch answers L).map fun selected => encodingRow L (leafMsg answers L) selected.1
def EncodingMatchAt (answers : Answers) (trace : List Entry) (L : LeafAddr) : Prop :=
  ∃ message counter answer, (encodingRow L message counter, answer) ∈ trace ∧
    referenceInput answers L ≠ some (encodingRow L message counter) ∧
    decode L.lay (low answer) = some (referenceDigits answers L)
def MarkerAt (answers : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ message counter answer digits, (encodingRow a.key message counter, answer) ∈ trace ∧
    referenceInput answers a.key ≠ some (encodingRow a.key message counter) ∧
    decode a.key.lay (low answer) = some digits ∧
    digits.getD a.chain 0 + 1 = (referenceDigits answers a.key).getD a.chain 0 ∧
    ∀ i, i ≠ a.chain → (referenceDigits answers a.key).getD i 0 ≤ digits.getD i 0
def entriesOf (answers : Answers) (qs : List Spec.Domain) : List Entry :=
  qs.filterMap fun q => match q with
    | .inl (.inr input) => some (input, answers (.inl (.inr input)))
    | _ => none
end SigGolfCandidate.T3.Security.Wots
