import SigGolfCandidate.Merge056
set_option debug.skipKernelTC true
set_option linter.all false

/-! # E8: the verifier's FTS forest reads the ground nonces from the level-3 pads

`SharedV3.forest` (the unchanged verify machine's program) on a witness whose path readout has the nonce word
`nDig n` in the level-3 pad of each coordinate is `recoverForestN` with those nonces: the level-3 (heap `8..15`)
node is then exactly the trial input `ftsNodeInputN` hashed for its low half, and every other node is the
canonical one. -/

namespace W9Drv.SharedCanonical
open OracleComp SigGolfCandidate.T3 ClaudeWCT.WCT9 W9Machine
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The 16-byte pad holding nonce `n` (low word `n`, high word 0). -/
def nDig (n : Nat) : Digest := BitVec.ofNat 128 (n % 2 ^ 64)

/-- The canonical recovered-path step with the level-3 pad `p3`. -/
def canonicalStepN (first : Bool) (index coord child : Nat) (path : Nat → Digest) (padR p3 p2 : Digest)
    (value : Digest) (level : Nat) : M Digest :=
  if level = 4 ∧ first then highHash (canonicalChildInput index coord child path padR p3 value level p2)
  else SharedV3.hashSel (SharedV3.hiOut child (level + 1))
    (canonicalChildInput index coord child path padR p3 value level p2)

theorem recoverSharedInnerN_canon (first : Bool) (index coord : Nat) (child : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (n : Nat) (prev : PairRoot) :
    recoverSharedInnerN first index coord child word values path n prev = (do
      let ends ← (List.finRange 6).mapM fun i =>
        ClaudeWCT.WCT9.chain index coord (rawChild first child.val) i.val (4 - wordDigit word i)
          (wordDigit word i) (values i)
      let leaf ← leafHashH (128 + child.val) index coord (rawChild first child.val) prev.1 ends
      (List.range 5).foldlM (canonicalStepN first index coord child.val path prev.2 (nDig n)
        (if coord ≤ 7 then nDig (n / 2 ^ 64) else 0)) leaf) := by
  have hNonce : ∀ (heap m : Nat) (left right : Digest), ClaudeWCT.WCT9.ftsNodeInputN coord index heap m left right
      = wctTopInput coord index heap left (nDig m) right := fun _ _ _ _ => rfl
  have hc : child.val < 128 := child.isLt
  unfold recoverSharedInnerN
  apply bind_congr
  intro ends
  apply bind_congr
  intro leaf
  apply foldlM_congr_mem
  intro value level hl
  have hl5 : level < 5 := List.mem_range.mp hl
  show (do
      let other := path level
      let lr := if child.val / 2 ^ level % 2 = 0 then (value, other) else (other, value)
      sharedNodeN first coord index ((128 + child.val) / 2 ^ (level + 1)) (fun _ => prev) n lr.1 lr.2) =
      canonicalStepN first index coord child.val path prev.2 (nDig n)
        (if coord ≤ 7 then nDig (n / 2 ^ 64) else 0) value level
  set other := path level with hother
  set lr : Digest × Digest := if child.val / 2 ^ level % 2 = 0 then (value, other) else (other, value) with hlr
  show sharedNodeN first coord index ((128 + child.val) / 2 ^ (level + 1)) (fun _ => prev) n lr.1 lr.2 =
      canonicalStepN first index coord child.val path prev.2 (nDig n)
        (if coord ≤ 7 then nDig (n / 2 ^ 64) else 0) value level
  have hleft : canonicalChildInput index coord child.val path prev.2 (nDig n) value level
      (if coord ≤ 7 then nDig (n / 2 ^ 64) else 0) =
      wctTopInput coord index ((128 + child.val) / 2 ^ (level + 1)) lr.1
        (if level = 4 then prev.2 else if level = 3 then nDig n
          else if level = 2 then (if coord ≤ 7 then nDig (n / 2 ^ 64) else 0) else 0) lr.2 := by
    unfold canonicalChildInput
    simp only [hlr, hother]
    split_ifs <;> rfl
  interval_cases level
  · -- level = 0 : heap in [64,128), non-ground
    unfold sharedNodeN canonicalStepN
    rw [if_neg (by omega : ¬ (8 ≤ (128 + child.val) / 2 ^ (0 + 1) ∧ (128 + child.val) / 2 ^ (0 + 1) < 16)),
      if_neg (by omega : ¬ (16 ≤ (128 + child.val) / 2 ^ (0 + 1) ∧ (128 + child.val) / 2 ^ (0 + 1) < 32 ∧ coord ≤ 7)),
      if_neg (by omega : ¬ ((0 : Nat) = 4 ∧ first))]
    unfold sharedNode
    rw [if_neg (by omega : ¬ (128 + child.val) / 2 ^ (0 + 1) < 4),
      if_neg (by omega : ¬ (128 + child.val) / 2 ^ (0 + 1) < 8)]
    unfold ftsNodeG ftsNodeAt
    rw [if_pos (by unfold ftsZeroBits; rw [if_neg (by omega), if_neg (by omega)])]
    simp only [Functor.map_map]
    rw [hleft, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    have := sel_topInput_zero (coord := coord) (index := index) (heap := (128 + child.val) / 2 ^ (0 + 1))
      (hi := SharedV3.hiOut child.val (0 + 1)) (hiOut_heap child.val 1 hc (by omega)) lr.1 lr.2
    simpa [Function.comp, wctNodeHashH] using this.symm
  · -- level = 1 : heap in [32,64), non-ground
    unfold sharedNodeN canonicalStepN
    rw [if_neg (by omega : ¬ (8 ≤ (128 + child.val) / 2 ^ 2 ∧ (128 + child.val) / 2 ^ 2 < 16)),
      if_neg (by omega : ¬ (16 ≤ (128 + child.val) / 2 ^ 2 ∧ (128 + child.val) / 2 ^ 2 < 32 ∧ coord ≤ 7)),
      if_neg (by omega : ¬ ((1 : Nat) = 4 ∧ first))]
    unfold sharedNode
    rw [if_neg (by omega : ¬ (128 + child.val) / 2 ^ 2 < 4), if_neg (by omega : ¬ (128 + child.val) / 2 ^ 2 < 8)]
    unfold ftsNodeG ftsNodeAt
    rw [if_pos (by unfold ftsZeroBits; rw [if_neg (by omega), if_neg (by omega)])]
    simp only [Functor.map_map]
    rw [hleft, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    have := sel_topInput_zero (coord := coord) (index := index) (heap := (128 + child.val) / 2 ^ 2)
      (hi := SharedV3.hiOut child.val (1 + 1)) (hiOut_heap child.val 2 hc (by omega)) lr.1 lr.2
    simpa [Function.comp, wctNodeHashH] using this.symm
  · -- level = 2 : heap in [16,32); ground when coord ≤ 7, else not
    by_cases h7 : coord ≤ 7
    · unfold sharedNodeN
      rw [if_neg (by omega : ¬ (8 ≤ (128 + child.val) / 2 ^ 3 ∧ (128 + child.val) / 2 ^ 3 < 16)),
        if_pos (show 16 ≤ (128 + child.val) / 2 ^ 3 ∧ (128 + child.val) / 2 ^ 3 < 32 ∧ coord ≤ 7 by omega)]
      unfold canonicalStepN
      rw [if_neg (by omega : ¬ ((2 : Nat) = 4 ∧ first))]
      rw [hleft, if_neg (by decide), if_neg (by decide), if_pos (by decide), if_pos h7]
      unfold ClaudeWCT.WCT9.ftsNodeHashN
      rw [hNonce, hashSel_eq_ftsHash (hiOut_heap child.val 3 hc (by omega))]
    · unfold sharedNodeN canonicalStepN
      rw [if_neg (by omega : ¬ (8 ≤ (128 + child.val) / 2 ^ 3 ∧ (128 + child.val) / 2 ^ 3 < 16)),
        if_neg (by omega : ¬ (16 ≤ (128 + child.val) / 2 ^ 3 ∧ (128 + child.val) / 2 ^ 3 < 32 ∧ coord ≤ 7)),
        if_neg (by omega : ¬ ((2 : Nat) = 4 ∧ first))]
      unfold sharedNode
      rw [if_neg (by omega : ¬ (128 + child.val) / 2 ^ 3 < 4), if_neg (by omega : ¬ (128 + child.val) / 2 ^ 3 < 8)]
      unfold ftsNodeG ftsNodeAt
      rw [if_pos (by unfold ftsZeroBits; rw [if_neg (by omega), if_neg (by omega)])]
      simp only [Functor.map_map]
      rw [hleft, if_neg (by decide), if_neg (by decide), if_pos (by decide), if_neg h7]
      have := sel_topInput_zero (coord := coord) (index := index) (heap := (128 + child.val) / 2 ^ 3)
        (hi := SharedV3.hiOut child.val (2 + 1)) (hiOut_heap child.val 3 hc (by omega)) lr.1 lr.2
      simpa [Function.comp, wctNodeHashH] using this.symm
  · -- level = 3 : heap in [8,16), always ground
    unfold sharedNodeN
    rw [if_pos (show 8 ≤ (128 + child.val) / 2 ^ 4 ∧ (128 + child.val) / 2 ^ 4 < 16 by omega)]
    unfold canonicalStepN
    rw [if_neg (by omega : ¬ ((3 : Nat) = 4 ∧ first))]
    rw [hleft, if_neg (by decide), if_pos (by decide)]
    unfold ClaudeWCT.WCT9.ftsNodeHashN
    rw [hNonce, hashSel_eq_ftsHash (hiOut_heap child.val 4 hc (by omega))]
  · -- level = 4 : heap in [4,8)
    unfold sharedNodeN
    rw [if_neg (by omega : ¬ (8 ≤ (128 + child.val) / 2 ^ 5 ∧ (128 + child.val) / 2 ^ 5 < 16)),
      if_neg (by omega : ¬ (16 ≤ (128 + child.val) / 2 ^ 5 ∧ (128 + child.val) / 2 ^ 5 < 32 ∧ coord ≤ 7))]
    unfold sharedNode
    rw [if_neg (by omega : ¬ (128 + child.val) / 2 ^ 5 < 4),
      if_pos (by omega : (128 + child.val) / 2 ^ 5 < 8)]
    unfold canonicalStepN
    rw [hleft, if_pos rfl]
    cases hf : first with
    | true => rw [if_pos (⟨rfl, rfl⟩ : (4 : Nat) = 4 ∧ true = true), if_pos rfl]
    | false =>
        rw [if_neg (by decide), if_neg (by decide)]
        have hhigh : ftsHighHeap ((128 + child.val) / 2 ^ (4 + 1)) = false :=
          ftsHighHeap_mid (by omega) (by omega)
        have heq : SharedV3.hiOut child.val (4 + 1) = ftsHighHeap ((128 + child.val) / 2 ^ (4 + 1)) := by
          rw [hhigh]; simp [SharedV3.hiOut]
        rw [hashSel_eq_ftsHash heq, ftsHash_of_low hhigh]

/-- E8: the verifier's source coordinate, its level-3 node hashed with nonce `n`. -/
def sourceCoordinateN (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (values : Fin 6 → Digest) (path : Nat → Digest) (n : Nat) (prev : PairRoot) : M PairRoot := do
  let child : Child := ⟨SharedV3.physical coord.val raw.val, SharedV3.physical_lt _ _ raw.isLt⟩
  let inner ← recoverSharedInnerN (SharedV3.first coord.val) index coord.val child word values path n prev
  if SharedV3.first coord.val then
    pure (SharedV3.orderPair coord.val child.val inner (path 5))
  else
    let lr := if child.val / 32 % 2 = 0 then (inner, path 5) else (path 5, inner)
    let outer ← sharedOuterHash coord.val index (2 + child.val / 64) lr.1 lr.2
    pure (SharedV3.orderPair coord.val child.val outer (path 6))

theorem canonicalCoordinate_eq_sourceN (index : Nat) (coord : Fin 9)
    (raw : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (n : Nat) (prev : PairRoot) :
    canonicalCoordinate index coord raw word values path prev (nDig n)
        (if coord.val ≤ 7 then nDig (n / 2 ^ 64) else 0) =
      sourceCoordinateN index coord raw word values path n prev := by
  -- S5185 INTEG (STATEMENT CHANGE, X2): the level-2 pad `p2 = if coord ≤ 7 then nDig (n / 2^64) else 0` is threaded
  -- into `canonicalCoordinate` (was `p2 := 0`, FALSE since T12/T4: coord = 0, n = 2^64); the old proof plus `p2`.
  have hraw : rawChild (SharedV3.first coord.val) (SharedV3.physical coord.val raw.val) = raw.val :=
    raw_physical_child _ _ raw.isLt
  unfold canonicalCoordinate canonicalChildN sourceCoordinateN
  simp only [recoverSharedInnerN_canon]
  cases hf : SharedV3.first coord.val with
  | false =>
      simp only [hf] at hraw
      simp only [hf, hraw, Bool.false_eq_true, ↓reduceIte, bind_assoc, SharedV3.lastLevel]
      apply bind_congr
      intro ends
      apply bind_congr
      intro leaf
      have hfold : (List.range 5).foldlM (fun value level => SharedV3.hashSel
          (SharedV3.hiOut (SharedV3.physical coord.val raw.val) (level + 1))
          (canonicalChildInput index coord.val (SharedV3.physical coord.val raw.val) path prev.2 (nDig n) value level
            (if coord.val ≤ 7 then nDig (n / 2 ^ 64) else 0)))
          leaf =
          (List.range 5).foldlM (canonicalStepN false index coord.val (SharedV3.physical coord.val raw.val) path
            prev.2 (nDig n) (if coord.val ≤ 7 then nDig (n / 2 ^ 64) else 0)) leaf := by
        apply foldlM_congr_mem
        intro value level _
        simp only [canonicalStepN, Bool.false_eq_true, and_false, if_false]
      rw [← hfold]
      apply bind_congr
      intro acc
      have := canonical_top_outer coord (SharedV3.physical coord.val raw.val)
        (SharedV3.physical_lt _ _ raw.isLt) hf
      rw [this]
      have heap : (128 + SharedV3.physical coord.val raw.val) / 2 ^ (5 + 1) =
          2 + SharedV3.physical coord.val raw.val / 64 := by norm_num; omega
      simp only [canonicalChildInput, sharedOuterHash, heap, show (5 : Nat) ≠ 4 by decide,
        show (5 : Nat) ≠ 3 by decide, show (5 : Nat) ≠ 2 by decide, if_false, show 2 ^ 5 = 32 by decide]
      split_ifs <;> rfl
  | true =>
      have hn : coord.val ≠ 8 := by
        intro he
        simp [SharedV3.first, he] at hf
      have hp : SharedV3.physical coord.val raw.val = raw.val := by
        simp [SharedV3.physical, hf, physicalChild]
      simp only [hf, hp, ↓reduceIte, hn, bind_assoc, SharedV3.lastLevel]
      apply bind_congr
      intro ends
      apply bind_congr
      intro leaf
      rw [show List.range 5 = List.range 4 ++ [4] from rfl, List.foldlM_append]
      simp only [bind_assoc, List.foldlM_cons, List.foldlM_nil, bind_pure]
      have hfold : (List.range 4).foldlM (fun value level => SharedV3.hashSel
          (SharedV3.hiOut raw.val (level + 1))
          (canonicalChildInput index coord.val raw.val path prev.2 (nDig n) value level
            (if coord.val ≤ 7 then nDig (n / 2 ^ 64) else 0))) leaf =
          (List.range 4).foldlM (canonicalStepN true index coord.val raw.val path prev.2 (nDig n)
            (if coord.val ≤ 7 then nDig (n / 2 ^ 64) else 0)) leaf := by
        apply foldlM_congr_mem
        intro value level hl
        have := List.mem_range.mp hl
        simp only [canonicalStepN]
        rw [if_neg (show ¬ (level = 4 ∧ True) from fun h => absurd h.1 (by omega))]
      rw [← hfold]
      apply bind_congr
      intro acc
      simp only [canonicalStepN, and_self, if_true, show (4 : Nat) = 4 from rfl, and_true]
      try rfl

def sourcePairN (index : Nat) (pair : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (nonces : List Nat) (prev : PairRoot) : M PairRoot := do
  let a ← sourceCoordinateN index ⟨2 * pair.val, by omega⟩
    (rawOfPhysical true (firstChild s)) aWord opened.firstValues
    (fun i => opened.firstPath ⟨i % 6, Nat.mod_lt _ (by decide)⟩) (nonces.getD (2 * pair.val) 0) prev
  sourceCoordinateN index ⟨2 * pair.val + 1, by omega⟩
    (rawOfPhysical false (secondChild s)) bWord opened.secondValues
    (fun i => opened.secondPath ⟨i % 7, Nat.mod_lt _ (by decide)⟩) (nonces.getD (2 * pair.val + 1) 0) a

theorem sourcePairN_eq (index : Nat) (pair : Fin 4) (s : SigGolfCandidate.Research.SharedForest.Selection)
    (aWord bWord : Rank) (opened : PairOpening) (nonces : List Nat) (prev : PairRoot) :
    sourcePairN index pair s aWord bWord opened nonces prev =
      recoverPairN index pair.val s aWord bWord opened nonces prev := by
  have hfirst : SharedV3.first (2 * pair.val) = true := by simp [SharedV3.first]; omega
  have hsecond : SharedV3.first (2 * pair.val + 1) = false := by simp [SharedV3.first]
  have ha : SharedV3.physical (2 * pair.val) (rawOfPhysical true (firstChild s)).val = (firstChild s).val := by
    simp only [SharedV3.physical, hfirst, physical_rawOfPhysical]
  have hb : SharedV3.physical (2 * pair.val + 1) (rawOfPhysical false (secondChild s)).val =
      (secondChild s).val := by
    simp only [SharedV3.physical, hsecond, physical_rawOfPhysical]
  unfold sourcePairN sourceCoordinateN recoverPairN recoverSharedOuterN
  simp only [ha, hb, hfirst, hsecond, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
    SharedV3.orderPair, SharedV3.direction, SharedV3.lastLevel]
  rfl

def sourceSingletonN (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (n : Nat) (prev : PairRoot) : M PairRoot :=
  sourceCoordinateN index 8 (rawOfPhysical false selected) word opened.values
    (fun i => opened.path ⟨i % 7, Nat.mod_lt _ (by decide)⟩) n prev

theorem sourceSingletonN_eq (index : Nat) (selected : Child) (word : Rank)
    (opened : SingletonOpening) (n : Nat) (prev : PairRoot) :
    sourceSingletonN index selected word opened n prev = recoverSingletonN index selected word opened n prev := by
  have hf : SharedV3.first 8 = false := by decide
  have hp : SharedV3.physical 8 (rawOfPhysical false selected).val = selected.val := by
    simp only [SharedV3.physical, hf, physical_rawOfPhysical]
  unfold sourceSingletonN sourceCoordinateN recoverSingletonN
  simp only [show (8 : Fin 9).val = 8 from rfl, hp, hf, Bool.false_eq_true, ↓reduceIte, SharedV3.orderPair,
    SharedV3.direction, SharedV3.lastLevel]
  rfl

def sourceNineForestN (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (opened : ForestOpening) (nonces : List Nat) : M PairRoot :=
  (List.finRange 9).foldlM (fun (acc : PairRoot) coord =>
    sourceCoordinateN index coord (coordinateRaw selected coord) (coordinateWord words coord)
      (coordinateValues opened coord) (coordinatePath opened coord) (nonces.getD coord.val 0) acc) ftsStart

attribute [local irreducible] sourceCoordinateN rawOfPhysical

theorem sourceNineForestN_eq (index : Nat) (selected : ForestSelection)
    (words : ForestWords) (opened : ForestOpening) (nonces : List Nat) :
    sourceNineForestN index selected words opened nonces = recoverForestN index selected words opened nonces := by
  have hnine : List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [sourceNineForestN, recoverForestN, hnine, hfour, List.foldlM_cons, List.foldlM_nil, bind_assoc,
    pure_bind, bind_pure]
  simp only [← sourcePairN_eq, ← sourceSingletonN_eq]
  simp only [sourcePairN, sourceSingletonN, bind_assoc, pure_bind, bind_pure]
  simp only [coordinateRaw, coordinateChild, coordinateWord, coordinateValues, coordinatePath]
  norm_num [SharedV3.first]
  rfl

/-- E8: the verifier's forest on a witness with nonce `nonces[k]` in coordinate `k`'s level-3 pad. -/
theorem forest_canonicalN (w : SharedV3.WBytes) (index : Nat) (hi : index < 2 ^ 31)
    (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) (nonces : List Nat)
    (hstart : SharedV3.initialPair w = ftsStart)
    (hc : ∀ coord, ChainReadout w coord (coordinateWord words coord) (coordinateValues opened coord))
    (hp : ∀ coord, PathReadout w coord (coordinateRaw selected coord) (coordinatePath opened coord)
      (nDig (nonces.getD coord.val 0)) (if coord.val ≤ 7 then nDig (nonces.getD coord.val 0 / 2 ^ 64) else 0)) :
    SharedV3.forest w index (coordinateRaw selected)
      (fun coord => ClaudeWCT.WCT9.embed (coordinateWord words coord)) =
        recoverForestN index selected words opened nonces := by
  -- S5185 INTEG (STATEMENT CHANGE, X4): `hp` carries the level-2 pad `p2 = if k ≤ 7 then nDig (nonces[k] / 2^64)
  -- else 0` (was `p2 := 0`, FALSE: zero level-2 pads and `nonces = [2^64]`); proof unchanged (through X2 restated).
  rw [← sourceNineForestN_eq]
  unfold SharedV3.forest sourceNineForestN
  rw [hstart]
  apply foldlM_congr_mem
  intro acc coord _
  rw [coordinate_canonical w index coord _ _ _ _ acc _ hi (hc coord) (hp coord),
    canonicalCoordinate_eq_sourceN]

end W9Drv.SharedCanonical
