import SigGolfCandidate.OuterForestConcrete
import SigGolfCandidate.OuterForestCorrectness
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
namespace OuterSigning
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
abbrev Signature := SigGolfCandidate.Research.SharedForest.Signature
abbrev Witness := SigGolfCandidate.Research.SharedForest.Witness

def rootPool (leaf : Nat) : Nat := 75-CanonicalPolicy.topPathSave leaf
def requiredCredit (index : Nat) : Nat := rootPool (route index 0).1

theorem rootPool_bounds (leaf : Nat) : 72≤rootPool leaf ∧ rootPool leaf≤75 := by
  have := CanonicalPolicy.topPathSave_le_three leaf
  unfold rootPool
  omega

theorem requiredCredit_bounds (index : Nat) : 72≤requiredCredit index ∧ requiredCredit index≤75 := rootPool_bounds _

/-- The top floor `max 16 (pool-57)`: 18 when the top path saves nothing (pool 75), 17 when it saves one
(pool 74), 16 otherwise (pools 73, 72). -/
theorem rootPool_floor (leaf : Nat) :
    Policy75Safe23.threshold 0 (rootPool leaf)=
      if CanonicalPolicy.topPathSave leaf=0 then 18 else if CanonicalPolicy.topPathSave leaf=1 then 17 else 16 := by
  have h := CanonicalPolicy.topPathSave_le_three leaf
  rw [Policy75Safe23.threshold_top]
  unfold rootPool
  split_ifs <;> omega

theorem root_floor (index : Nat) : Policy75Safe23.threshold 0 (requiredCredit index)=
    if CanonicalPolicy.topPathSave (route index 0).1=0 then 18
    else if CanonicalPolicy.topPathSave (route index 0).1=1 then 17 else 16 := rootPool_floor _

theorem root_floor_bounds (index : Nat) :
    16≤Policy75Safe23.threshold 0 (requiredCredit index) ∧ Policy75Safe23.threshold 0 (requiredCredit index)≤18 := by
  rw [root_floor]
  split_ifs <;> omega

def searchPreparedLayers (cache : SigGolfCandidate.T3.Cache) (index : Nat) (prepared : PreparedRoots)
    (forest : PairRoot) : M (Option CanonicalLayers) := do
  let pair0 := topPair 1 prepared.one.levels
  let pair1 := topPair 2 prepared.two.levels
  let pair2 := topPair 3 prepared.three.levels
  let some (counter0, digits0, low0) ← CanonicalPolicy.layerCounterSearchAt 0
    (Policy75Safe23.threshold 0 (requiredCredit index))
    (route index 0).2 (route index 0).1 (.pair pair0.1 pair0.2) 0 (searchLimit 0)
    | pure none
  let residual1 := routeResidual index (requiredCredit index) 0 low0 digits0
  let floor1 := Policy75Safe23.threshold 1 residual1
  if floor1 ≥ 17 then return none
  let some (counter1, digits1, low1) ← CanonicalPolicy.layerCounterSearchAt 1
    floor1
    (route index 1).2 (route index 1).1 (.pair pair1.1 pair1.2) 0 (searchLimit 1)
    | pure none
  let residual2 := routeResidual index residual1 1 low1 digits1
  let floor2 := Policy75Safe23.threshold 2 residual2
  if floor2 ≥ 24 then return none
  let some (counter2, digits2, low2) ← CanonicalPolicy.layerCounterSearchAt 2
    floor2
    (route index 2).2 (route index 2).1 (.pair pair2.1 pair2.2) 0 (searchLimit 2)
    | pure none
  let residual3 := routeResidual index residual2 2 low2 digits2
  let floor3 := Policy75Safe23.threshold 3 residual3
  if floor3 ≥ 24 then return none
  let some (counter3, digits3, low3) ← CanonicalPolicy.layerCounterSearchAt 3
    floor3
    (route index 3).2 (route index 3).1 (.pair forest.1 forest.2) 0 (searchLimit 3)
    | pure none
  let top ← signTop cache (route index 0).1 digits0
  pure (some ⟨[top,
      preparedPieces 1 (route index 1).1 prepared.one digits1,
      preparedPieces 2 (route index 2).1 prepared.two digits2,
      preparedPieces 3 (route index 3).1 prepared.three digits3],
    [counter0, counter1, counter2, counter3], [digits0, digits1, digits2, digits3],
    [low0, low1, low2, low3],
    CanonicalPolicy.nextResidual residual3 3 low3 digits3,
    BitVec.ofNat 16 (576 * floor1 + 24 * floor2 + floor3)⟩)

/-- Source signing continuation after the FTS digest search has selected an
output. The enclosing producer supplies the accepted output and its counter. -/
def signFromOutput (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (digestCounter : BitVec 32)
    (output : HashOutput) : M (Option Witness) := do
  let index := digestIndex output
  let forest ← OuterForestMoment.forest index (forestSelectionFromOutput output) (forestWordsFromOutput output)
  let prepared ← prepareRoots (SigGolfCandidate.T3.hyperIndex index)
  let some layers ← searchPreparedLayers cache (SigGolfCandidate.T3.hyperIndex index) prepared forest.2 | pure none
  let signature : Signature := ⟨rho, layers.policyHints, forest.1,
    fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
  pure (some ⟨signature, digestCounter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true), [],
    fun _ => [], [], []⟩)

def signPayload (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (counter, output) ← sharedDigestSearch rho message 0 digestAttemptLimit | pure none
  let some witness ← signFromOutput cache rho counter output | pure none
  pure (some witness.signature)

def sign (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message


def hintFloor (index : Nat) (hints : BitVec 16) (lay : Layer) : Nat :=
  if lay = 0 then Policy75Safe23.threshold 0 (requiredCredit index) else hints.toNat / 24 ^ (3 - lay.val) % 24

def policyHintsValid (index : Nat) (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool) : Bool :=
  let residual1 := routeResidual index (requiredCredit index) 0 (lows.getD 0 true) (digits.getD 0 [])
  let residual2 := routeResidual index residual1 1 (lows.getD 1 true) (digits.getD 1 [])
  let residual3 := routeResidual index residual2 2 (lows.getD 2 true) (digits.getD 2 [])
  decide (hints.toNat < 12288 ∧ digits.length = 4 ∧
    hintFloor index hints 1 = Policy75Safe23.threshold 1 residual1 ∧
    hintFloor index hints 2 = Policy75Safe23.threshold 2 residual2 ∧
    hintFloor index hints 3 = Policy75Safe23.threshold 3 residual3)


#print axioms root_floor
#print axioms root_floor_bounds
end OuterSigning
