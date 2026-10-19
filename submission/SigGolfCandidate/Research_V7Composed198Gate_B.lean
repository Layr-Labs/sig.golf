import SigGolfCandidate.Research_V7Composed198Gate_A

set_option autoImplicit false
set_option Elab.async false


/-! Private roots-first canonical producer. Retained chain prefixes let the
ancestor-only search choose digits after every lower root has been fixed. -/
namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- Retain each prefix while evaluating a WOTS chain once, in its ordinary order. Stage 2 (C3, #866): each step
keeps the half `chainHigh lay i start` of its output, as `WCT9.chainW` does (the last step of chain 0 of a lower
layer keeps the HIGH half). -/
def chainPrefixes (lay : Layer) (tree leaf i start : Nat) :
    Nat → Digest → M (List Digest)
  | 0, value => pure [value]
  | count + 1, value => do
      let next ← halfHash (chainHigh lay i start) (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)
      let tail ← chainPrefixes lay tree leaf i (start + 1) count next
      pure (value :: tail)

def buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    M ((Digest × List (List Digest)) × List Digest) := do
  let (coefs, carry) ← lowerCoefs lay tree leaf carry
  let prefixes ← (List.range (chainCount lay)).mapM fun i =>
    chainPrefixes lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed coefs lay leaf i)
  let root ← lowerLeafHash lay tree leaf
    ((List.range (chainCount lay)).map fun i =>
      (prefixes.getD i []).getD (maxDigit lay i) 0)
  pure ((root, prefixes), carry)

structure PreparedLower where
  levels : List (List Digest)
  prefixes : List (List Digest)

/-- Only the selected leaf retains its prefixes; every other leaf uses the
existing full-chain builder. No chain is evaluated again after digit search. -/
def buildTreePrefixes (lay : Layer) (tree selected : Nat) : M PreparedLower := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List (List Digest) × List Digest) leaf => do
      let ((root, prefixes), carry) ←
        if leaf = selected then buildLeafPrefixes lay tree leaf state.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree leaf [] state.2.2
          pure ((root, []), carry)
      pure (state.1 ++ [root], if leaf = selected then prefixes else state.2.1, carry))
    ([], [], [])
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure ⟨levels, state.2.1⟩

def preparedPieces (lay : Layer) (leaf : Nat) (prepared : PreparedLower)
    (digits : List Nat) : Pieces :=
  ((List.range (chainCount lay)).map fun i =>
      (prepared.prefixes.getD i []).getD (digits.getD i 0) 0,
   (List.range (height lay)).map fun level =>
      (prepared.levels.getD level []).getD (leaf / 2 ^ level ^^^ 1) 0)

structure PreparedRoots where
  one : PreparedLower
  two : PreparedLower
  three : PreparedLower

def prepareRoots (index : Nat) : M PreparedRoots := do
  let one ← buildTreePrefixes 1 (route index 1).2 (route index 1).1
  let two ← buildTreePrefixes 2 (route index 2).2 (route index 2).1
  let three ← buildTreePrefixes 3 (route index 3).2 (route index 3).1
  pure ⟨one, two, three⟩

structure CanonicalLayers where
  pieces : List Pieces
  counters : List (BitVec 32)
  digits : List (List Nat)
  /-- The selected half of every layer (`true` = LOW). -/
  lows : List Bool
  residual : Nat
  policyHints : BitVec 16

/-- All thresholds are determined by the canonical ancestors. The lower
tree roots are already fixed, and lower reveals are pure prefix lookups. -/
def searchPreparedLayers (cache : SigGolfCandidate.T3.Cache) (index : Nat) (prepared : PreparedRoots)
    (forest : PairRoot) : M (Option CanonicalLayers) := do
  let pair0 := topPair 1 prepared.one.levels
  let pair1 := topPair 2 prepared.two.levels
  let pair2 := topPair 3 prepared.three.levels
  let some (counter0, digits0, low0) ← CanonicalPolicy.layerCounterSearchAt 0
    (CanonicalPolicy.threshold 0 CanonicalPolicy.totalCredit)
    (route index 0).2 (route index 0).1 (.pair pair0.1 pair0.2) 0 (searchLimit 0)
    | pure none
  let residual1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 low0 digits0
  let floor1 := CanonicalPolicy.threshold 1 residual1
  if floor1 ≥ 16 then return none
  let some (counter1, digits1, low1) ← CanonicalPolicy.layerCounterSearchAt 1
    floor1
    (route index 1).2 (route index 1).1 (.pair pair1.1 pair1.2) 0 (searchLimit 1)
    | pure none
  let residual2 := CanonicalPolicy.nextResidual residual1 1 low1 digits1
  let floor2 := CanonicalPolicy.threshold 2 residual2
  if floor2 ≥ 22 then return none
  let some (counter2, digits2, low2) ← CanonicalPolicy.layerCounterSearchAt 2
    floor2
    (route index 2).2 (route index 2).1 (.pair pair2.1 pair2.2) 0 (searchLimit 2)
    | pure none
  let residual3 := CanonicalPolicy.nextResidual residual2 2 low2 digits2
  let floor3 := CanonicalPolicy.threshold 3 residual3
  if floor3 ≥ 22 then return none
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
    BitVec.ofNat 16 (484 * floor1 + 22 * floor2 + floor3)⟩)

/-- Source signing continuation after the FTS digest search has selected an
output. The enclosing producer supplies the accepted output and its counter. -/
def signFromOutput (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (digestCounter : BitVec 32)
    (output : HashOutput) : M (Option Witness) := do
  let index := digestIndex output
  let forest ← buildForest index (forestSelectionFromOutput output) (forestWordsFromOutput output)
  let prepared ← prepareRoots index
  let some layers ← searchPreparedLayers cache index prepared forest.2 | pure none
  let signature : Signature := ⟨rho, layers.policyHints, forest.1,
    fun lay => piecesSignature lay (layers.pieces.getD lay.val ([], []))⟩
  pure (some ⟨signature, digestCounter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true), []⟩)

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness

theorem lower_chain_succ_first (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    SigGolfCandidate.T3.chain lay tree leaf i start (count + 1) value = (do
      let next ← shortHash (SigGolfCandidate.T3.chainInput lay tree leaf i start value)
      SigGolfCandidate.T3.chain lay tree leaf i (start + 1) count next) := by
  rw [show count + 1 = 1 + count by omega, SigGolfCandidate.T3.Correctness.chain_add]
  rfl

/-- Stage 2 (C3): `lower_chain_succ_first` for the chain of the current scheme. -/
theorem lower_chainW_succ_first (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    ClaudeWCT.WCT9.chainW lay tree leaf i start (count + 1) value = (do
      let next ← ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i start)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)
      ClaudeWCT.WCT9.chainW lay tree leaf i (start + 1) count next) := by
  rw [show count + 1 = 1 + count by omega, ClaudeWCT.WCT9.chainW_add]
  have h1 : ClaudeWCT.WCT9.chainW lay tree leaf i start 1 value =
      ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i start)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value) := by
    unfold ClaudeWCT.WCT9.chainW
    simp only [List.range'_one, List.foldlM_cons, List.foldlM_nil, bind_pure]
  rw [h1]

theorem eval_chainPrefixes_length (answers : Answers) (lay : Layer)
    (tree leaf i start count : Nat) (value : Digest) :
    (evalWithAnswerFn answers (chainPrefixes lay tree leaf i start count value)).length = count + 1 := by
  induction count generalizing start value with
  | zero => simp [chainPrefixes, evalWithAnswerFn_pure]
  | succ count ih =>
    simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.length_cons, ih]

theorem eval_chainPrefixes_getD (answers : Answers) (lay : Layer)
    (tree leaf i start count : Nat) (value : Digest) (j : Nat) (hj : j ≤ count) :
    (evalWithAnswerFn answers (chainPrefixes lay tree leaf i start count value)).getD j 0 =
      evalWithAnswerFn answers (ClaudeWCT.WCT9.chainW lay tree leaf i start j value) := by
  induction count generalizing start value j with
  | zero =>
    have hz : j = 0 := by omega
    subst j
    rfl
  | succ count ih =>
    cases j with
    | zero =>
      simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.getD_cons_zero]
      rfl
    | succ j =>
      simp only [chainPrefixes, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.getD_cons_succ]
      rw [ih _ _ _ (by omega), lower_chainW_succ_first, evalWithAnswerFn_bind]

#print axioms eval_chainPrefixes_length
#print axioms eval_chainPrefixes_getD
end SigGolfCandidate.Research.SharedForest

/-! Shared-forest digest selection and the exact producer cap. The selector
bit shared by each pair does not enter either child's variable cycle count. -/
namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

def firstCoord (coord : Nat) : Bool := decide (coord < 8 ∧ coord % 2 = 0)
def rawChildBase (coord : Nat) : Nat := [0, 6, 64, 70, 128, 134, 192, 198, 229].getD coord 0

def rawChildFromOutput (output : HashOutput) (coord : Fin 9) : Child :=
  ⟨output.toNat / 2 ^ rawChildBase coord.val % 128, Nat.mod_lt _ (by decide)⟩

def physicalChildFromOutput (output : HashOutput) (coord : Fin 9) : Child :=
  ⟨physicalChild (firstCoord coord.val) (rawChildFromOutput output coord).val,
    physicalChild_lt _ _ (rawChildFromOutput output coord).isLt⟩

/-- C1 (stage 1): the per-child cycle correction `2 - skips′` of the physical child's class (A routines fit
their 32-word slots, so there is no spill term). -/
def accountingCorrection (coord : Nat) (raw : Child) : Nat :=
  2 - SharedPathPacking.saves (physicalChild (firstCoord coord) raw.val)

def coordinateAccountingCost (output : HashOutput) (coord : Fin 9) : Nat :=
  routineCost (forestRank output coord.val) + accountingCorrection coord.val (rawChildFromOutput output coord)

def jointAccountingCost (output : HashOutput) : Nat :=
  ((List.finRange 9).map (coordinateAccountingCost output)).sum

def ranksAccepted (output : HashOutput) : Bool :=
  (List.finRange 9).all (fun coord => decide (rawForestRank output coord.val < 563))

/-- Joint cap 777 (`P(joint ≤ 777 | gate, ranks) = 0.990672`). -/
def digestAccepted (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 242 % 16384 < 734) && ranksAccepted output &&
    decide (jointAccountingCost output ≤ 777)

theorem firstCoord_eq_shared (coord : Nat) : firstCoord coord = decide (coord < 8 ∧ coord % 2 = 0) := rfl

theorem ranksAccepted_iff (output : HashOutput) : ranksAccepted output = true ↔
    ∀ coord : Fin 9, rawForestRank output coord.val < 563 := by
  simp [ranksAccepted, List.all_eq_true]

theorem accepted_conditions (output : HashOutput) (h : digestAccepted output = true) :
    output.toNat / 2 ^ 242 % 16384 < 734 ∧
    (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
    jointAccountingCost output ≤ 777 := by
  simpa only [digestAccepted, Bool.and_eq_true, decide_eq_true_eq, ranksAccepted_iff,
    and_assoc] using h
end SigGolfCandidate.Research.SharedForest

/-! The compact signature carries explicit canonical policy hints. All128 nonce
bits are retained; the hints are checked again after bottom-up recovery. -/
namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- Policy hint bound (img-v4/v6 mixed radix): h = 484·f1 + 22·f2 + f3 with f1 ≤ 15, f2, f3 ≤ 21, h < 7744. -/
def policyHintBound : Nat := 7744

def hintFloor (hints : BitVec 16) (lay : Layer) : Nat :=
  if lay = 0 then CanonicalPolicy.topFloor else hints.toNat / 22 ^ (3 - lay.val) % 22

def policyHintsValid (hints : BitVec 16) (digits : List (List Nat)) (lows : List Bool) : Bool :=
  let residual1 := CanonicalPolicy.nextResidual CanonicalPolicy.totalCredit 0 (lows.getD 0 true) (digits.getD 0 [])
  let residual2 := CanonicalPolicy.nextResidual residual1 1 (lows.getD 1 true) (digits.getD 1 [])
  let residual3 := CanonicalPolicy.nextResidual residual2 2 (lows.getD 2 true) (digits.getD 2 [])
  decide (hints.toNat < 7744 ∧ digits.length = 4 ∧
    hintFloor hints 1 = CanonicalPolicy.threshold 1 residual1 ∧
    hintFloor hints 2 = CanonicalPolicy.threshold 2 residual2 ∧
    hintFloor hints 3 = CanonicalPolicy.threshold 3 residual3)

/-- Adapter for the unchanged main-tree recovery kernels. The forest opening
is recovered separately; no dummy opening is inspected by those kernels. -/
def mainSignature (sig : Signature) : ClaudeWCT.WCT9.Signature :=
  ⟨sig.rho, fun _ => ⟨fun _ => 0, fun _ => 0⟩, sig.layers⟩

def fillTopSignature (sig : Signature) (c : Nat) : Signature :=
  { sig with layers := fun lay => fillLayer lay (sig.layers lay) c }

/-- img-v6 normal form of a top path node at height `j`: the 5,239-byte codec does not store the zero-test bits
(`T3.topZeroOk`): top `j` bits for `j = 1..10`; for the top sibling (`j = 11`) bits 98..127 (98..108 zero-test
bits, 109..127 brute-forced). -/
def normPathD (j : Nat) (d : Digest) : Digest :=
  if 1 ≤ j ∧ j ≤ 10 then BitVec.ofNat 128 (d.toNat % 2 ^ (128 - j))
  else if j = 11 then BitVec.ofNat 128 (d.toNat % 2 ^ 98) else d

def normLayer (lay : Layer) (ls : LayerSignature lay) : LayerSignature lay :=
  ⟨ls.values, fun j => if lay.val = 0 then normPathD j.val (ls.path j) else ls.path j⟩

/-- img-v6: what the 5,239-byte codec keeps (13-bit hint, normalized top path); `expand` applies it first. -/
def normTop (sig : Signature) : Signature :=
  { sig with policyHints := BitVec.ofNat 16 (sig.policyHints.toNat % 2 ^ 13)
             layers := fun lay => normLayer lay (sig.layers lay) }

/-- The honest top path passes its zero tests (no nonce search hit its cap). -/
def TopPathOK (sig : Signature) : Prop :=
  ∀ j : Fin (height 0), 1 ≤ j.val → topZeroOk j.val ((sig.layers 0).path j) = true

structure RecoveredLayers where
  foldedTop : Digest
  root : Digest
  counters : List (BitVec 32)
  digits : List (List Nat)
  /-- The selected half of every layer (`true` = LOW), top first. -/
  lows : List Bool
  /-- Top-bytes layer: the nonces of the top path nodes of heights 1..11 (re-derived by `topFoldN`). -/
  nonces : List Nat

/-- Hints allow one bottom-up pass. The final check compares these hints with
the unique ancestor policy, so alternate hint encodings are rejected. -/
def recoverHintedLayers (sig : Signature) (index : Nat) (other : Digest) :
    Nat → LayerMsg → M (Option RecoveredLayers)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let some (counter, digits, low) ← CanonicalPolicy.layerCounterSearchAt lay
        (hintFloor sig.policyHints lay) tree leaf msg 0 (searchLimit lay) | pure none
      if n = 0 then
        let (folded, nonces) ← topFoldN (mainSignature sig) index digits
        let root ← topNode index folded other
        pure (some ⟨folded, root, [counter], [digits], [low], nonces⟩)
      else
        let pair ← recoverLayerPair (mainSignature sig) index lay digits
        let some previous ← recoverHintedLayers sig index other n (.pair pair.1 pair.2) | pure none
        pure (some { previous with
          counters := previous.counters ++ [counter]
          digits := previous.digits ++ [digits]
          lows := previous.lows ++ [low] })

def sharedDigestSearch (rho : Digest) (message : Message) (counter : Nat) :
    Nat → M (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← digest rho message (BitVec.ofNat 32 counter)
      if digestAccepted output then return some (BitVec.ofNat 32 counter, output)
      sharedDigestSearch rho message (counter + 1) fuel

def signPayload (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (counter, output) ← sharedDigestSearch rho message 0 digestAttemptLimit | pure none
  let some witness ← signFromOutput cache rho counter output | pure none
  pure (some witness.signature)

def sign (cache : SigGolfCandidate.T3.Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayload cache message

/-- The pre-v6 expansion kernel (hint check, top sibling field cleared, brute force). -/
def expandFill (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) := do
  if sig.policyHints.toNat ≥ 7744 then return none
  let sig0 := fillTopSignature sig 0
  let some (counter, output) ← sharedDigestSearch sig0.rho message 0 digestAttemptLimit | pure none
  let index := digestIndex output
  let forest ← recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig0.forest
  let some layers ← recoverHintedLayers sig0 index ((sig0.layers 0).path topJ)
    4 (.pair forest.1 forest.2) | pure none
  if !policyHintsValid sig0.policyHints layers.digits layers.lows then return none
  if layers.root = pk then
    return some ⟨sig0, counter, fun lay => layers.counters.getD lay.val 0, !(layers.lows.getD 0 true),
      layers.nonces⟩
  let some c ← searchTop index layers.foldedTop ((sig0.layers 0).path topJ) pk searchFuel 1 | pure none
  pure (some ⟨fillTopSignature sig0 c, counter, fun lay => layers.counters.getD lay.val 0,
    !(layers.lows.getD 0 true), layers.nonces⟩)

/-- img-v6 expansion: normalize to what the 5,239-byte codec keeps, then the old kernel. -/
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) :=
  expandFill message pk (normTop sig)

theorem nonce_retained (sig : Signature) (c : Nat) :
    (fillTopSignature sig c).rho = sig.rho := rfl

theorem hints_retained (sig : Signature) (c : Nat) :
    (fillTopSignature sig c).policyHints = sig.policyHints := rfl

theorem ofNat_mod_pow_idem (n m x : Nat) (hm : m ≤ n) :
    BitVec.ofNat n ((BitVec.ofNat n (x % 2 ^ m)).toNat % 2 ^ m) = BitVec.ofNat n (x % 2 ^ m) := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hm), Nat.mod_mod]

theorem normPathD_idem (j : Nat) (d : Digest) : normPathD j (normPathD j d) = normPathD j d := by
  unfold normPathD
  by_cases h1 : 1 ≤ j ∧ j ≤ 10
  · simp only [if_pos h1]
    exact ofNat_mod_pow_idem 128 (128 - j) d.toNat (by omega)
  · by_cases h11 : j = 11
    · simp only [if_neg h1, if_pos h11]
      exact ofNat_mod_pow_idem 128 98 d.toNat (by omega)
    · simp only [if_neg h1, if_neg h11]

theorem normPathD_setTop (d : Digest) (c : Nat) : normPathD 11 (setTop d c) = normPathD 11 d := by
  unfold normPathD
  simp only [show ¬(1 ≤ 11 ∧ 11 ≤ 10) by omega, if_false, if_true]
  congr 1
  rw [setTop_toNat, Nat.add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 98 ≤ 109)),
    show c % 2 ^ 19 * 2 ^ 109 % 2 ^ 98 = 0 from
      Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by norm_num)) _), add_zero, Nat.mod_mod]

theorem normZeroBits_eq (j : Nat) (hj : j ≤ 11) : topZeroBits j = j := by
  interval_cases j <;> rfl

/-- A path node that passes its zero test is fixed by the normal form (the top sibling up to its brute-forced
bits 109..127). -/
theorem normPathD_ok (j : Nat) (hj : j < 12) (d : Digest) (hz : 1 ≤ j → topZeroOk j d = true) :
    normPathD j d = if j = 11 then setTop d 0 else d := by
  unfold normPathD
  by_cases hj0 : j = 0
  · subst hj0
    simp
  by_cases h11 : j = 11
  · subst h11
    simp only [show ¬(1 ≤ 11 ∧ 11 ≤ 10) by omega, if_false, if_true]
    have h' : d.toNat / 2 ^ 98 % 2 ^ 11 = 0 := by
      have := hz (by omega)
      unfold topZeroOk at this
      simpa using this
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, setTop_toNat, show (2 : Nat) ^ 109 = 2 ^ 98 * 2 ^ 11 by norm_num, Nat.mod_mul, h']
    simp only [mul_zero, add_zero, Nat.zero_mod, zero_mul]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) d.isLt)
  · have h1 : 1 ≤ j ∧ j ≤ 10 := by omega
    simp only [if_pos h1, if_neg h11]
    have hz' := hz (by omega)
    unfold topZeroOk at hz'
    rw [if_neg h11, normZeroBits_eq j (by omega), beq_iff_eq] at hz'
    have hdm := Nat.div_add_mod d.toNat (2 ^ (128 - j))
    rw [hz', mul_zero, zero_add] at hdm
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hdm]
    exact Nat.mod_eq_of_lt d.isLt

theorem normTop_rho (sig : Signature) : (normTop sig).rho = sig.rho := rfl
theorem normTop_forest (sig : Signature) : (normTop sig).forest = sig.forest := rfl

theorem normTop_layers_ne (sig : Signature) (lay : Layer) (h : lay ≠ 0) : (normTop sig).layers lay = sig.layers lay := by
  have h0 : lay.val ≠ 0 := fun hv => h (Fin.ext hv)
  unfold normTop normLayer
  simp only [h0, if_false]

theorem normTop_hints (sig : Signature) (h : sig.policyHints.toNat < 2 ^ 13) :
    (normTop sig).policyHints = sig.policyHints := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 16 (sig.policyHints.toNat % 2 ^ 13)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt sig.policyHints.isLt]

theorem normTop_normTop (sig : Signature) : normTop (normTop sig) = normTop sig := by
  unfold normTop
  congr 1
  · exact ofNat_mod_pow_idem 16 13 sig.policyHints.toNat (by omega)
  · funext lay
    unfold normLayer
    congr 1
    funext j
    by_cases h0 : lay.val = 0
    · simp only [h0, if_true, normPathD_idem]
    · simp only [h0, if_false]

theorem normTop_fill (sig : Signature) (c : Nat) : normTop (fillTopSignature sig c) = normTop sig := by
  unfold normTop fillTopSignature
  congr 1
  funext lay
  unfold normLayer fillLayer
  congr 1
  funext j
  by_cases h0 : lay.val = 0
  · by_cases h11 : j.val = 11
    · simp only [h0, h11, and_self, if_true, normPathD_setTop]
    · simp only [h0, h11, and_false, true_and, if_true, if_false]
  · simp only [h0, false_and, if_false]

/-- Honest signatures (top path zero tests passed, 13-bit hint) normalize to the old `fillTopSignature sig 0`. -/
theorem normTop_eq_fill (sig : Signature) (hh : sig.policyHints.toNat < 2 ^ 13) (hz : TopPathOK sig) :
    normTop sig = fillTopSignature sig 0 := by
  unfold normTop fillTopSignature
  congr 1
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt sig.policyHints.isLt]
  · funext lay
    unfold normLayer fillLayer
    congr 1
    funext j
    by_cases h0 : lay.val = 0
    · have hl : lay = 0 := Fin.ext h0
      subst hl
      have hj : j.val < 12 := j.isLt
      rw [normPathD_ok j.val hj _ (hz j)]
      by_cases h11 : j.val = 11
      · simp [h11]
      · simp [h11]
    · simp only [h0, false_and, if_false]

theorem expand_normTop (message : Message) (pk : Digest) (sig : Signature) :
    expand message pk (normTop sig) = expand message pk sig := by
  unfold expand
  rw [normTop_normTop]

theorem fillTopSignature_fill (sig : Signature) (a b : Nat) :
    fillTopSignature (fillTopSignature sig a) b = fillTopSignature sig b := by
  unfold fillTopSignature
  simp only [Signature.mk.injEq, true_and]
  funext lay
  exact fillLayer_fillLayer lay (sig.layers lay) a b

theorem expandFill_fill (message : Message) (pk : Digest) (sig : Signature) (c : Nat) :
    expandFill message pk (fillTopSignature sig c) = expandFill message pk sig := by
  simp only [expandFill, hints_retained, fillTopSignature_fill]

/-- On an honest signature (13-bit hint, top path zero tests passed) `expand` is the old kernel. -/
theorem expand_eq_expandFill (message : Message) (pk : Digest) (sig : Signature)
    (hh : sig.policyHints.toNat < 2 ^ 13) (htop : TopPathOK sig) :
    expand message pk sig = expandFill message pk sig := by
  unfold expand
  rw [normTop_eq_fill sig hh htop, expandFill_fill]


theorem canonical_fts_window : CanonicalPolicy.ftsSearchLimit = digestAttemptLimit := rfl

#print axioms canonical_fts_window
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

def aCorrection (low : Nat) : Nat := 2 - SharedPathPacking.saves low
def bCorrection (low : Nat) : Nat := 2 - SharedPathPacking.saves low

/-- C1 (stage 1): the correction `2 - skips′` of each low-field class (13 classes 0, 16 classes 1, 3 classes 2). -/
def correctionTable : List Nat :=
  [2,1,1,1,1,0,0,1,1,0,0,0,0,0,0,1,2,1,1,0,1,0,0,1,1,0,0,1,1,1,1,2]

set_option maxRecDepth 100000 in
theorem aCorrection_table : ∀ c : Fin 32, aCorrection c.val = correctionTable.getD c.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bCorrection_table : ∀ c : Fin 32, bCorrection c.val = correctionTable.getD c.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Only five unshared selector bits influence a coordinate's accounting
cost. The shared pair-branch bit is absent from this formula. -/
theorem accountingCorrection_low (coord : Fin 9) (raw : Child) :
    accountingCorrection coord.val raw =
      if firstCoord coord.val then aCorrection (raw.val % 32)
      else bCorrection (raw.val / 2 % 32) := by
  fin_cases coord <;> fin_cases raw <;> decide +kernel

def costFieldBase (coord : Nat) : Nat := rawChildBase coord + (if firstCoord coord then 0 else 1)
def costField (output : HashOutput) (coord : Fin 9) : Fin 32 :=
  ⟨output.toNat / 2 ^ costFieldBase coord.val % 32, Nat.mod_lt _ (by decide)⟩

theorem accountingCorrection_field (output : HashOutput) (coord : Fin 9) :
    accountingCorrection coord.val (rawChildFromOutput output coord) =
      if firstCoord coord.val then aCorrection (costField output coord).val
      else bCorrection (costField output coord).val := by
  rw [accountingCorrection_low]
  unfold rawChildFromOutput costField costFieldBase
  split
  · rename_i h
    simp only [h, ↓reduceIte, Nat.add_zero]
    congr 1
    omega
  · rename_i h
    simp only [h, ↓reduceIte, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    congr 1
    omega

theorem costFieldBases : (List.range 9).map costFieldBase =
    [0, 7, 64, 71, 128, 135, 192, 199, 230] := by decide +kernel

/-- All nine5-bit cost fields, nine10-bit rank fields, the31-bit index,
and14-bit gate occupy disjoint ranges of the256-bit digest. -/
def countingFields : List (Nat × Nat) :=
  ((List.range 9).map fun k => (costFieldBase k, 5)) ++
  ((List.range 9).map fun k => (rankBase k, 10)) ++ [(33,31), (242,14)]

def countingFieldsOK : Bool :=
  countingFields.all (fun a => decide (a.1 + a.2 ≤ 256)) &&
    (countingFields.zipIdx).all (fun ai =>
      (countingFields.zipIdx).all (fun bj =>
        decide (ai.2 = bj.2 ∨ ai.1.1 + ai.1.2 ≤ bj.1.1 ∨ bj.1.1 + bj.1.2 ≤ ai.1.1)))

theorem countingFields_disjoint : countingFieldsOK = true := by decide +kernel
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness

def prefixRows (answers : Answers) (lay : Layer) (tree leaf : Nat) : List (List Digest) :=
  (List.range (chainCount lay)).map fun i =>
    evalWithAnswerFn answers (chainPrefixes lay tree leaf i 0 (maxDigit lay i)
      (wotsSeed answers lay tree leaf i))

theorem prefixRows_getD (answers : Answers) (lay : Layer) (tree leaf i j : Nat)
    (hi : i < chainCount lay) (hj : j ≤ maxDigit lay i) :
    ((prefixRows answers lay tree leaf).getD i []).getD j 0 =
      evalWithAnswerFn answers (chainW lay tree leaf i 0 j
        (wotsSeed answers lay tree leaf i)) := by
  unfold prefixRows
  rw [List.getD_eq_getElem _ [] (by simpa)]
  simp only [List.getElem_map, List.getElem_range]
  exact eval_chainPrefixes_getD answers lay tree leaf i 0 _ _ j hj

theorem buildLeafPrefixes_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree leaf : Nat) (carry : List Digest)
    (hcarry : leaf % famGrp lay ≠ 0 → carry = famCoefL answers lay tree (famOf lay leaf)) :
    evalWithAnswerFn answers (buildLeafPrefixes lay tree leaf carry) =
      ((wotsRoot answers lay tree leaf, prefixRows answers lay tree leaf),
       leafCarryOut answers lay tree leaf) := by
  simp only [buildLeafPrefixes, evalWithAnswerFn_bind,
    eval_lowerCoefs answers hlay tree leaf carry hcarry, evalWithAnswerFn_pure, eval_mapM,
    lowerFamilySeed_eq answers hlay]
  change ((evalWithAnswerFn answers (lowerLeafHash lay tree leaf
    ((List.range (chainCount lay)).map fun i =>
      ((prefixRows answers lay tree leaf).getD i []).getD (maxDigit lay i) 0)),
    prefixRows answers lay tree leaf), _) = _
  have he : (List.range (chainCount lay)).map (fun i =>
      ((prefixRows answers lay tree leaf).getD i []).getD (maxDigit lay i) 0) =
      (List.range (chainCount lay)).map (wotsEnd answers lay tree leaf) := by
    apply List.map_congr_left
    intro i hi
    exact prefixRows_getD answers lay tree leaf i _ (List.mem_range.mp hi) (by omega)
  rw [he]
  rfl

def prefixTreeRows (lay : Layer) (tree selected : Nat) :
    M (List Digest × List (List Digest) × List Digest) :=
  (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List (List Digest) × List Digest) leaf => do
      let ((root, prefixes), carry) ←
        if leaf = selected then buildLeafPrefixes lay tree leaf state.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree leaf [] state.2.2
          pure ((root, []), carry)
      pure (state.1 ++ [root], if leaf = selected then prefixes else state.2.1, carry))
    ([], [], [])

def PrefixTreeRows (answers : Answers) (lay : Layer) (tree selected done : Nat)
    (rows : List Digest × List (List Digest) × List Digest) : Prop :=
  rows.1.length = done ∧
    (∀ j, j < done → rows.1.getD j 0 = wotsRoot answers lay tree j) ∧
    rows.2.1 = (if selected < done then prefixRows answers lay tree selected else []) ∧
    rows.2.2 = treeCarry answers lay tree done

theorem eval_prefixTreeRows (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) :
    PrefixTreeRows answers lay tree selected (2 ^ height lay)
      (evalWithAnswerFn answers (prefixTreeRows lay tree selected)) := by
  unfold prefixTreeRows
  refine eval_foldlM_range_inv answers (2 ^ height lay) _
    (PrefixTreeRows answers lay tree selected) ([], [], [])
    (by simp [PrefixTreeRows, treeCarry]) ?_
  intro done _ rows hrows
  rcases hrows with ⟨hlen, hroot, hvalues, hc⟩
  have hstep : evalWithAnswerFn answers (do
      let ((root, prefixes), carry) ←
        if done = selected then buildLeafPrefixes lay tree done rows.2.2
        else do
          let ((root, _), carry) ← buildLeafPF lay tree done [] rows.2.2
          pure ((root, []), carry)
      pure (rows.1 ++ [root], if done = selected then prefixes else rows.2.1, carry)) =
      (rows.1 ++ [wotsRoot answers lay tree done],
       if done = selected then prefixRows answers lay tree done else rows.2.1,
       leafCarryOut answers lay tree done) := by
    by_cases hs : done = selected
    · subst selected
      simp only [↓reduceIte, evalWithAnswerFn_bind, hc,
        buildLeafPrefixes_result answers hlay tree done _
          (carryOk_treeCarry answers lay tree done), evalWithAnswerFn_pure]
    · simp only [hs, ↓reduceIte, evalWithAnswerFn_bind, hc,
        buildLeafPF_result answers hlay tree done [] (Cost.validDigits_nil lay) _
          (carryOk_treeCarry answers lay tree done), evalWithAnswerFn_pure]
  rw [hstep]
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro j hj
    rw [ClaudeWCT.WCT9.getD_append_singleton, hlen]
    by_cases hjd : j < done
    · rw [if_pos hjd]; exact hroot j hjd
    · have he : j = done := by omega
      subst j
      simp
  · by_cases hs : done = selected
    · subst hs; simp
    · have hs' : selected < done + 1 ↔ selected < done := by omega
      simp only [if_neg hs, hvalues, hs']
  · show leafCarryOut answers lay tree done = treeCarry answers lay tree (done + 1)
    unfold treeCarry
    rw [if_neg (show done + 1 ≠ 0 by omega), Nat.add_sub_cancel]

theorem buildTreePrefixes_factor (lay : Layer) (tree selected : Nat) :
    buildTreePrefixes lay tree selected = (do
      let rows ← prefixTreeRows lay tree selected
      let levels ← buildLevelsBelow 3 lay.val tree (height lay) rows.1
      pure ⟨levels, rows.2.1⟩) := rfl

theorem eval_buildTreePrefixes_result (answers : Answers) {lay : Layer}
    (hlay : lay ≠ 0) (tree selected : Nat) (hsel : selected < 2 ^ height lay) :
    evalWithAnswerFn answers (buildTreePrefixes lay tree selected) =
      ⟨(wotsTree answers lay tree).take (height lay),
        prefixRows answers lay tree selected⟩ := by
  let rows := evalWithAnswerFn answers (prefixTreeRows lay tree selected)
  have hr : PrefixTreeRows answers lay tree selected (2 ^ height lay) rows :=
    eval_prefixTreeRows answers hlay tree selected
  rcases hr with ⟨hlen, hroot, hvalues, -⟩
  have hroots : rows.1 = (List.range (2 ^ height lay)).map (wotsRoot answers lay tree) :=
    list_eq_range_map _ _ _ hlen hroot
  rw [if_pos hsel] at hvalues
  rw [buildTreePrefixes_factor, evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (⟨evalWithAnswerFn answers (buildLevelsBelow 3 lay.val tree (height lay) rows.1),
    rows.2.1⟩ : PreparedLower) = _
  rw [hroots, hvalues, eval_buildLevelsBelow answers 3 lay.val tree (height lay) _ (by simp)
    (by fin_cases lay <;> decide)]
  simp only [wotsTree, if_neg hlay]

theorem preparedPieces_result (answers : Answers) {lay : Layer} (hlay : lay ≠ 0)
    (tree selected : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (hsel : selected < 2 ^ height lay) :
    preparedPieces lay selected
      (evalWithAnswerFn answers (buildTreePrefixes lay tree selected)) digits =
      wotsPieces answers lay tree selected digits := by
  rw [eval_buildTreePrefixes_result answers hlay tree selected hsel]
  unfold preparedPieces wotsPieces
  apply Prod.ext
  · apply List.map_congr_left
    intro i hi
    exact prefixRows_getD answers lay tree selected i _ (List.mem_range.mp hi)
      (hvalid i (List.mem_range.mp hi))
  · exact map_range_take_path _ _ _

#print axioms buildLeafPrefixes_result
#print axioms eval_buildTreePrefixes_result
#print axioms preparedPieces_result
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem base22_unique {x y : Nat} (hx : x < 7744) (hy : y < 7744)
    (h1 : x / 484 % 22 = y / 484 % 22) (h2 : x / 22 % 22 = y / 22 % 22)
    (h3 : x % 22 = y % 22) : x = y := by
  omega

theorem hintFloor_unique {a b : BitVec 16} (ha : a.toNat < 7744) (hb : b.toNat < 7744)
    (h1 : hintFloor a 1 = hintFloor b 1)
    (h2 : hintFloor a 2 = hintFloor b 2)
    (h3 : hintFloor a 3 = hintFloor b 3) : a = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [hintFloor, show (1 : Layer) ≠ 0 by decide, show (2 : Layer) ≠ 0 by decide,
    show (3 : Layer) ≠ 0 by decide, if_false] at h1 h2 h3
  norm_num at h1 h2 h3
  exact base22_unique ha hb h1 h2 h3

theorem policyHintsValid_unique {a b : BitVec 16} {digits : List (List Nat)} {lows : List Bool}
    (ha : policyHintsValid a digits lows = true) (hb : policyHintsValid b digits lows = true) : a = b := by
  simp only [policyHintsValid, decide_eq_true_eq] at ha hb
  exact hintFloor_unique ha.1 hb.1 (ha.2.2.1.trans hb.2.2.1.symm)
    (ha.2.2.2.1.trans hb.2.2.2.1.symm) (ha.2.2.2.2.trans hb.2.2.2.2.symm)

theorem encodedHints_spec (a b c : Nat) (ha : a < 16) (hb : b < 22) (hc : c < 22) :
    let code := BitVec.ofNat 16 (484 * a + 22 * b + c)
    code.toNat < 7744 ∧ hintFloor code 1 = a ∧
      hintFloor code 2 = b ∧ hintFloor code 3 = c := by
  dsimp only
  simp only [hintFloor, show (1 : Layer) ≠ 0 by decide,
    show (2 : Layer) ≠ 0 by decide, show (3 : Layer) ≠ 0 by decide, if_false]
  norm_num [BitVec.toNat_ofNat]
  have hn : 484 * a + 22 * b + c < 65536 := by omega
  rw [Nat.mod_eq_of_lt hn]
  omega

#print axioms policyHintsValid_unique
#print axioms encodedHints_spec
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem firstThreshold_window : ∀ r : Fin 56,
    CanonicalPolicy.threshold 1 r.val < 16 ∧
      r.val - CanonicalPolicy.threshold 1 r.val ≤ 40 := by
  decide +kernel

theorem secondThreshold_window : ∀ r : Fin 41,
    CanonicalPolicy.threshold 2 r.val < 22 ∧
      r.val - CanonicalPolicy.threshold 2 r.val ≤ 21 := by
  decide +kernel

theorem thirdThreshold_window (r : Nat) (hr : r ≤ 21) :
    CanonicalPolicy.threshold 3 r = r := by
  simp [CanonicalPolicy.threshold, hr]

end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Cost ClaudeWCT.WCT9.Cost

theorem bound_chainPrefixes (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    CBound (fun xs => xs.length = count + 1) count
      (chainPrefixes lay tree leaf i start count value) := by
  induction count generalizing start value with
  | zero => exact .pure [value] 0 rfl
  | succ count ih =>
    unfold chainPrefixes
    have hs : CBound (fun _ => True) 1
        (halfHash (chainHigh lay i start)
          (ClaudeWCT.WCT9.chainInputW lay tree leaf i start value)) := by
      apply bound_halfHash <;>
        simp [ClaudeWCT.WCT9.chainInputW_length, pad64_length]
    refine hs.bind' (l := count) (fun next _ => ?_) (by omega)
    refine (ih (start + 1) next).bind' (l := 0) (n := count)
      (fun tail ht => .pure (value :: tail) 0 (by simp [ht])) (by omega)

theorem sum_map_range_eq (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem bound_buildLeafPrefixes (lay : Layer) (tree leaf : Nat) (carry : List Digest) :
    CBound (fun result => result.1.2.length = chainCount lay) (leafCostP lay leaf)
      (buildLeafPrefixes lay tree leaf carry) := by
  unfold buildLeafPrefixes
  refine (bound_lowerCoefs lay tree leaf carry).bind' (l := digitTotal lay + leafHashCost lay)
    (fun res _ => ?_) (by unfold leafCostP; omega)
  refine (Bound.mapM_list (P := GoodQuery) (List.range (chainCount lay)) _
    (fun i => maxDigit lay i) (fun i _ =>
      (bound_chainPrefixes lay tree leaf i 0 (maxDigit lay i) (lowerFamilySeed res.1 lay leaf i)).mono
        (fun _ h => h) (fun _ _ => trivial))).bind' (l := leafHashCost lay)
    (fun prefixes hprefixes => ?_) ?_
  · refine (bound_lowerLeafHash lay tree leaf _ (by simp only [List.length_map, List.length_range])).bind' (l := 0) (n := leafHashCost lay)
      (fun root _ => .pure _ 0 (by simpa using hprefixes)) (by omega)
  · unfold digitTotal
    simp only [sum_map_range_eq]
    exact le_rfl

theorem bound_buildTreePrefixes (lay : Layer) (tree selected : Nat) :
    CBound (fun result => LevelShape (height lay) (height lay - 1) result.levels)
      (treeCostP lay) (buildTreePrefixes lay tree selected) := by
  unfold buildTreePrefixes
  refine Bound.bind' (l := 2 ^ height lay - 2) (Bound.foldlM_range (2 ^ height lay) _
    (fun i (state : List Digest × List (List Digest) × List Digest) => state.1.length = i)
    (leafCostP lay) ([], [], []) rfl (fun leaf _ state hstate => ?_))
    (fun state hstate => ?_) le_rfl
  · by_cases hs : leaf = selected
    · simp only [if_pos hs]
      refine (bound_buildLeafPrefixes lay tree leaf state.2.2).bind' (l := 0)
        (fun result _ => .pure _ 0 (by simp [hstate])) (by omega)
    · simp only [if_neg hs]
      refine (bound_buildLeafPF lay tree leaf [] (validDigits_nil lay) state.2.2).bind' (l := 0)
        (fun result _ => ?_) (by omega)
      exact .pure _ 0 (by simp [hstate])
  · refine (bound_buildLevelsBelow 3 lay.val tree (height lay) state.1 hstate
      (by fin_cases lay <;> decide)).bind' (l := 0)
      (fun levels hlevels => .pure (PreparedLower.mk levels state.2.1) 0 hlevels) (by omega)

theorem bound_prepareRoots (index : Nat) :
    CBound (fun _ => True) (treeCostP 1 + treeCostP 2 + treeCostP 3) (prepareRoots index) := by
  unfold prepareRoots
  refine (bound_buildTreePrefixes 1 (route index 1).2 (route index 1).1).bind'
    (l := treeCostP 2 + treeCostP 3) (fun one _ => ?_) (by omega)
  refine (bound_buildTreePrefixes 2 (route index 2).2 (route index 2).1).bind'
    (l := treeCostP 3) (fun two _ => ?_) (by omega)
  exact (bound_buildTreePrefixes 3 (route index 3).2 (route index 3).1).bind'
    (l := 0) (fun three _ => .pure (PreparedRoots.mk one two three) 0 trivial) (by omega)

/-- v6 lower families: 81146 − 325 (L1 349 + L2/L3 175 family pairs instead of 4 per leaf). -/
theorem prepared_roots_cost : treeCostP 1 + treeCostP 2 + treeCostP 3 = 80821 := by
  rw [treeCostP_one, treeCostP_two, treeCostP_three]

#print axioms bound_chainPrefixes
#print axioms bound_buildLeafPrefixes
#print axioms bound_buildTreePrefixes
#print axioms bound_prepareRoots
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Cost ClaudeWCT.WCT9.Cost

theorem rawChild_lt (first : Bool) (physical : Nat) (h : physical < 128) :
    rawChild first physical < 128 := by
  cases first <;> simp only [rawChild, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem bound_highHash64 (input : HashInput) (hlen : input.length = 64) :
    CBound (fun _ => True) 1 (highHash input) := by
  apply bound_highHashP
  · simp only [GoodQuery, pad64_length, hlen]
    norm_num
  · simp only [pad64_length, hlen]
    norm_num

theorem bound_sharedOuterHash (coord index heap : Nat) (left right : Digest) :
    CBound (fun _ => True) 1 (sharedOuterHash coord index heap left right) := by
  unfold sharedOuterHash
  split
  · apply bound_shortHash <;> simp [wctTopInput_length, pad64_length]
  · exact bound_highHash64 _ (wctTopInput_length ..)

theorem bound_sharedNode (first : Bool) (coord index heap : Nat) (pads : Nat → PairRoot)
    (left right : Digest) :
    CBound (fun _ => True) 1 (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · exact bound_sharedOuterHash ..
  · split
    · split
      · exact bound_highHash64 _ (wctTopInput_length ..)
      · apply bound_shortHash <;> simp [wctTopInput_length, pad64_length]
    · rw [nodeHashH_eq, ftsHash_eq]
      split
      · exact bound_highHash64 _ (nodeInput_length ..)
      · apply bound_shortHash <;> simp [nodeInput_length, pad64_length]

theorem bound_sharedHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot)
    (leaves : List Digest) :
    CBound (fun _ => True) (if first then 124 else 126) (sharedHeap first index coord pads leaves) := by
  unfold sharedHeap
  apply (Bound.foldlM_list (P := GoodQuery)
    (List.range' (if first then 4 else 2) (if first then 124 else 126)).reverse
    (fun (nodes : Array Digest) heap => do
      let value ← sharedNode first coord index heap pads
        (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
      pure (nodes.set! heap value)) (fun _ _ => True) (fun _ => 1) _
    trivial (fun i hi nodes _ =>
      (bound_sharedNode first coord index _ pads _ _).bind' (l := 0)
        (fun value _ => .pure (nodes.set! _ value) 0 trivial) (by omega))).mono_k
  simp

theorem bound_buildSharedCoordinate (first : Bool) (index coord : Nat)
    (hcoord : coord < 9) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    CBound (fun _ => True) (if first then 3479 else 3481)
      (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate
  refine (cbound_of_ftsBound (ftsBound_ftsCoefs index coord hcoord)).bind'
    (l := 3328 + if first then 124 else 126) (fun coefs _ => ?_) ?_
  · refine (Bound.foldlM_range_le 128 _ (fun _ _ => True) (fun _ => 26) ([], [])
      trivial (fun j hj state _ => ?_) (fun _ _ => trivial) (by simp)).bind'
      (l := if first then 124 else 126) (fun state _ => ?_) le_rfl
    · refine (bound_buildChildH (128 + j) index coord (rawChild first j) word coefs (pads (j / 64)).1
        hcoord (rawChild_lt first j hj)).bind' (l := 0)
        (fun child _ => .pure _ 0 trivial) (by simp [ClaudeWCT.WCT9.childCost])
    · exact (bound_sharedHeap first index coord pads state.1).bind' (l := 0)
        (fun nodes _ => .pure (nodes, state.2) 0 trivial) (by omega)
  · cases first <;> decide

theorem bound_buildPair (index pair : Nat) (hpair : pair < 4) (s : Selection)
    (aWord bWord : Rank) (prev : PairRoot) :
    CBound (fun _ => True) 6960 (buildPair index pair s aWord bWord prev) := by
  unfold buildPair
  refine (bound_buildSharedCoordinate true index (2 * pair) (by omega)
    (firstChild s) aWord (fun _ => prev)).bind' (l := 3481) (fun a _ => ?_) (by decide)
  exact (bound_buildSharedCoordinate false index (2 * pair + 1) (by omega)
    (secondChild s) bWord (nodesPair a.1)).bind' (l := 0)
    (fun b _ => .pure _ 0 trivial) (by decide)

theorem bound_buildSingleton (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) :
    CBound (fun _ => True) 3481 (buildSingleton index selected word prev) := by
  unfold buildSingleton
  exact (bound_buildSharedCoordinate false index 8 (by decide) selected word (fun _ => prev)).bind'
    (l := 0) (fun built _ => .pure _ 0 trivial) (by decide)

theorem bound_buildForest (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    CBound (fun _ => True) 31321 (buildForest index selected words) := by
  unfold buildForest
  refine (Bound.foldlM_list (P := GoodQuery) (List.finRange 4) _ (fun _ _ => True)
    (fun _ => 6960) ([], ftsStart) trivial (fun i hi state _ => ?_)).bind'
    (l := 3481) (fun state _ => ?_) (by simp)
  · exact (bound_buildPair index _ ((List.finRange 4)[i]'hi).isLt _ _ _ state.2).bind'
      (l := 0) (fun built _ => .pure _ 0 trivial) (by decide)
  · exact (bound_buildSingleton index selected.singleton words.singleton state.2).bind'
      (l := 0) (fun last _ => .pure _ 0 trivial) (by decide)

#print axioms bound_buildSharedCoordinate
#print axioms bound_buildForest
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem canonical_decode_valid {lay : Layer} {answer : Digest} {digits : List Nat}
    (h : CanonicalPolicy.decode lay answer = some digits) :
    Cost.ValidDigits lay digits := by
  have hv := Cost.validDigits_decode h
  fin_cases lay <;> simpa [CanonicalPolicy.normalLayer, Cost.ValidDigits, chainCount, maxDigit] using hv

theorem canonical_search_some (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) : ∀ fuel counter found digits low, counter + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low) →
      counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
        CanonicalPolicy.producerDecodeOut lay floor
          (evalWithAnswerFn answers (publicHash (layerEncodingInput lay tree leaf msg found))) =
            some (digits, low) := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter found digits low _ he
      simp [CanonicalPolicy.layerCounterSearchAt] at he
  | succ fuel ih =>
      intro counter found digits low hlimit he
      simp only [CanonicalPolicy.layerCounterSearchAt, evalWithAnswerFn_bind] at he
      cases hd : CanonicalPolicy.producerDecodeOut lay floor (evalWithAnswerFn answers
        (publicHash (layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 counter)))) with
      | none =>
          simp only [hd] at he
          obtain ⟨hlo, hhi, hgood⟩ := ih (counter + 1) found digits low (by omega) he
          exact ⟨by omega, by omega, hgood⟩
      | some values =>
          simp only [hd, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hcount : (BitVec.ofNat 32 counter).toNat = counter := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact ⟨by rw [hcount], by rw [hcount]; omega, hd⟩

/-- `canonical_search_some` unpacked: the returned half is the canonical one and the producer accepted the
canonical word (`encodingHash`) with that half. -/
theorem canonical_search_some' (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (fuel counter : Nat) (found : BitVec 32) (digits : List Nat) (low : Bool)
    (hlimit : counter + fuel ≤ 2 ^ 32)
    (he : evalWithAnswerFn answers
        (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low)) :
    counter ≤ found.toNat ∧ found.toNat < counter + fuel ∧
      low = lowSelected lay (evalWithAnswerFn answers (publicHash (layerEncodingInput lay tree leaf msg found))) ∧
      CanonicalPolicy.producerDecodeAt lay floor low
        (evalWithAnswerFn answers (encodingHash lay (layerEncodingInput lay tree leaf msg found))) = some digits := by
  obtain ⟨h1, h2, h3⟩ := canonical_search_some answers lay floor tree leaf msg fuel counter found digits low hlimit he
  obtain ⟨hl, hd⟩ := CanonicalPolicy.producerDecodeOut_spec h3
  exact ⟨h1, h2, hl, hd⟩

theorem canonical_search_valid_credit (answers : Answers) (lay : Layer) (floor tree leaf : Nat)
    (msg : LayerMsg) (fuel counter : Nat) (found : BitVec 32) (digits : List Nat) (low : Bool)
    (hlimit : counter + fuel ≤ 2 ^ 32)
    (he : evalWithAnswerFn answers
      (CanonicalPolicy.layerCounterSearchAt lay floor tree leaf msg counter fuel) = some (found, digits, low)) :
    Cost.ValidDigits lay digits ∧ floor ≤ CanonicalPolicy.credit lay low digits := by
  have hd := (canonical_search_some' answers lay floor tree leaf msg fuel counter found digits low hlimit he).2.2.2
  exact ⟨canonical_decode_valid (CanonicalPolicy.producerDecodeAt_spec hd).1,
    CanonicalPolicy.producerDecodeAt_credit hd⟩

theorem canonical_four_residual (d0 d1 d2 d3 : List Nat) (l0 l1 l2 l3 : Bool)
    (h0 : 19 ≤ CanonicalPolicy.credit 0 l0 d0)
    (h1 : CanonicalPolicy.threshold 1 (CanonicalPolicy.nextResidual 74 0 l0 d0) ≤
      CanonicalPolicy.credit 1 l1 d1)
    (h2 : CanonicalPolicy.threshold 2
      (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 74 0 l0 d0) 1 l1 d1) ≤
      CanonicalPolicy.credit 2 l2 d2)
    (h3 : CanonicalPolicy.threshold 3
      (CanonicalPolicy.nextResidual
        (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 74 0 l0 d0) 1 l1 d1) 2 l2 d2) ≤
      CanonicalPolicy.credit 3 l3 d3) :
    CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual
      (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 74 0 l0 d0) 1 l1 d1) 2 l2 d2) 3 l3 d3 = 0 := by
  let r1 := CanonicalPolicy.nextResidual 74 0 l0 d0
  have hr1 : r1 < 56 := by dsimp [r1, CanonicalPolicy.nextResidual]; omega
  have hw1 := firstThreshold_window ⟨r1, hr1⟩
  change CanonicalPolicy.threshold 1 r1 < 16 ∧ r1 - CanonicalPolicy.threshold 1 r1 ≤ 40 at hw1
  let r2 := CanonicalPolicy.nextResidual r1 1 l1 d1
  have hr2 : r2 < 41 := by
    change CanonicalPolicy.threshold 1 r1 ≤ CanonicalPolicy.credit 1 l1 d1 at h1
    dsimp [r2, CanonicalPolicy.nextResidual]; omega
  have hw2 := secondThreshold_window ⟨r2, hr2⟩
  change CanonicalPolicy.threshold 2 r2 < 22 ∧ r2 - CanonicalPolicy.threshold 2 r2 ≤ 21 at hw2
  let r3 := CanonicalPolicy.nextResidual r2 2 l2 d2
  have hr3 : r3 ≤ 21 := by
    change CanonicalPolicy.threshold 2 r2 ≤ CanonicalPolicy.credit 2 l2 d2 at h2
    dsimp [r3, CanonicalPolicy.nextResidual]; omega
  change CanonicalPolicy.threshold 3 r3 ≤ CanonicalPolicy.credit 3 l3 d3 at h3
  rw [thirdThreshold_window r3 hr3] at h3
  change r3 - CanonicalPolicy.credit 3 l3 d3 = 0
  omega

#print axioms canonical_decode_valid
#print axioms canonical_search_some
#print axioms canonical_four_residual
end SigGolfCandidate.Research.SharedForest

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9

def verifyDigestAccepted (output : HashOutput) : Bool :=
  decide (output.toNat / 2 ^ 242 % 16384 < 734) && ranksAccepted output

theorem digestAccepted_implies_verify {output : HashOutput} (h : digestAccepted output = true) :
    verifyDigestAccepted output = true := by
  simp only [digestAccepted, Bool.and_eq_true] at h
  simpa only [verifyDigestAccepted, Bool.and_eq_true] using h.1

/-- Broad normalized verification retains the machine's early abort ordering.
Canonical producer floors and hints are checked by the signer and expander. -/
def verifyLayers (w : Witness) (index : Nat) : Nat → LayerMsg → M (Option Digest)
  | 0, _ => pure none
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let counter := w.counters lay
      if counter.toNat ≥ verifyWindow then return none
      let (leaf, tree) := route index lay
      let answer ← verificationHash lay w.topHigh (layerEncodingInput lay tree leaf msg counter)
      if n = 0 then verifyTopN (mainSignature w.signature) w.topNonces index answer
      else
        let some digits := CanonicalPolicy.decode lay answer | pure none
        let some pair ← recoverLayerPairGuard (mainSignature w.signature) index lay answer digits | pure none
        verifyLayers w index n (.pair pair.1 pair.2)

def verify (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ digestVerifyWindow then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !verifyDigestAccepted output then return false
  let index := digestIndex output
  let forest ← recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) w.signature.forest
  let some root ← verifyLayers w index 4 (.pair forest.1 forest.2) | pure false
  pure (root == pk)

end SigGolfCandidate.Research.SharedForest
