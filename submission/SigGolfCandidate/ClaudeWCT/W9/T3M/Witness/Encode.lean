import SigGolfCandidate.W9Machine.WctV3Source
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (zeros layerBytes sibOff)
open SphincsSecurity (bytesLE)
/-- The H2 expander (two omitted signature bytes recovered by search), with the digest output. -/
def expandN (message : Message) (pk : Digest) (sig : WCT9.Signature) :
    M (Option (HashOutput × WCT9.Witness)) :=
  WCT9.expandS WCT9.digestAttemptLimit message pk sig
/-- The expander before H2 (the full signature), with the digest output. -/
def expandN0 (message : Message) (pk : Digest) (sig : WCT9.Signature) :
    M (Option (HashOutput × WCT9.Witness)) := do
  let some (counter, output) ← WCT9.digestSearch sig.rho message 0 WCT9.digestAttemptLimit | pure none
  let index := WCT9.digestIndex output
  let top ← WCT9.recoverFts sig index output
  let some (root, counters) ← WCT9.expandLayersBC sig index 4 (.pair top.1 top.2) | pure none
  if root ≠ pk then return none
  pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩))
/-- Nested FTS (r1-1): the 176 bytes before coordinate 8's region (virtual tree 9). Offset 0 is the L3 block's left
slot (L8), 32 its counter, 48 its right slot (overwritten by the verifier with the copy of offset 144), 144 the R9
slot. Coordinate 8's supplied top sibling sits at `topSlot 8 child` (offset 0 or 144). -/
def headerBytes (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
    zeros 16 ++ bytesLE 4 (w.counters 3) ++ zeros 108 ++
    (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
    zeros 16
def authByte (child : Nat) (op : WCT9.Opening) (p : Nat) : UInt8 :=
  match (List.finRange 7).find? (fun l => decide (authSibOff child l.val ≤ p ∧ p < authSibOff child l.val + 16)) with
  | some l => (bytesLE 16 (op.path l)).getD (p - authSibOff child l.val) 0
  | none => 0
/-- Nested FTS (r1-1): the fold blocks of levels 0..4 (`[0, 320)` of a region); levels 5 and 6 are placed
elsewhere. -/
def authByte5 (child : Nat) (op : WCT9.Opening) (p : Nat) : UInt8 :=
  match (List.finRange 5).find? (fun l => decide (authSibOff child l.val ≤ p ∧ p < authSibOff child l.val + 16)) with
  | some l => (bytesLE 16 (op.path (Fin.castLE (by decide) l))).getD (p - authSibOff child l.val) 0
  | none => 0
def merkleBytes (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.range 320).map (authByte5 child op)
def chainBytes (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 5).reverse.flatMap fun i => zeros 48 ++ bytesLE 16 (op.values i.succ)
/-- Leaf block: `end0 | header slot (zero) | leaf pad | end1..end5`. -/
def leafBytes (op : WCT9.Opening) (pad : List UInt8) : List UInt8 :=
  bytesLE 16 (op.values 0) ++ zeros 16 ++ pad ++ (List.finRange 5).flatMap fun i => bytesLE 16 (op.values i.succ)
/-- Nested FTS (r1-1): the level-6 fold block `[left | header (zero) | pad | right]` at offset 832 of a region; the
supplied level-5 sibling is on the side opposite the computed value. -/
def topBlockBytes (child : Nat) (op : WCT9.Opening) (pad : List UInt8) : List UInt8 :=
  (if child / 2 ^ 5 % 2 = 1 then bytesLE 16 (op.path 5) else zeros 16) ++ zeros 16 ++ pad ++
    (if child / 2 ^ 5 % 2 = 0 then bytesLE 16 (op.path 5) else zeros 16)
/-- Region of coordinate `k` (896 bytes). `padL`/`padZ` hold coordinate `k - 1`'s supplied top sibling (16 bytes in
one of them, zeros in the other; both zero for `k = 0`). -/
def regionBytes (child : Nat) (op : WCT9.Opening) (padL padZ : List UInt8) : List UInt8 :=
  merkleBytes child op ++ chainBytes op ++ zeros 48 ++ leafBytes op padL ++ zeros 16 ++ topBlockBytes child op padZ
/-- Coordinate `k - 1`'s top sibling in coordinate `k`'s leaf pad (bit 6 of its child set) or level-6 pad. -/
def prevSibL (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : List UInt8 :=
  if k = 0 then zeros 16 else
    if (WCT9.child N (Fin.ofNat 9 (k - 1))).val / 2 ^ 6 % 2 = 1 then
      bytesLE 16 ((sig.openings (Fin.ofNat 9 (k - 1))).path 6) else zeros 16
def prevSibZ (N : HashOutput) (sig : WCT9.Signature) (k : Nat) : List UInt8 :=
  if k = 0 then zeros 16 else
    if (WCT9.child N (Fin.ofNat 9 (k - 1))).val / 2 ^ 6 % 2 = 0 then
      bytesLE 16 ((sig.openings (Fin.ofNat 9 (k - 1))).path 6) else zeros 16
def wctBytes (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).reverse.flatMap fun k =>
    regionBytes (WCT9.child N k).val (sig.openings k) (prevSibL N sig k.val) (prevSibZ N sig k.val) ++
      (if k.val = 0 then zeros 16 else [])
def lowerSibSlot (lay : Layer) (leaf j : Nat) : Nat := 16 * (lowerPlan lay leaf).getD j 0 + sibOff (leaf / 2 ^ j % 2)
def lowerCtrSlot (lay : Layer) (leaf : Nat) : Nat := 16 * (lowerPlan lay leaf).getD (height lay - 1) 0 + 32
def lowerPathByte (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) (p : Nat) : UInt8 :=
  match (List.finRange (height lay)).find?
      (fun j => decide (lowerSibSlot lay leaf j.val ≤ p ∧ p < lowerSibSlot lay leaf j.val + 16)) with
  | some j => (bytesLE 16 (ls.path j)).getD (p - lowerSibSlot lay leaf j.val) 0
  | none => if lowerCtrSlot lay leaf ≤ p ∧ p < lowerCtrSlot lay leaf + 4 then
      (bytesLE 4 ctr).getD (p - lowerCtrSlot lay leaf) 0 else 0
def lowerPathBytes (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  (List.range (16 * pathSlots lay)).map (lowerPathByte lay leaf ls ctr)
def layerRegion (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then layerBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
  else lowerPathBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
      (w.counters (Fin.ofNat 4 (lay.val - 1))) ++
    (layerBytes lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)).drop (64 * height lay)
def endpointBytes (sig : WCT9.Signature) (lay : Layer) : List UInt8 :=
  (List.finRange (chainCount lay)).flatMap fun i => bytesLE 16 ((sig.layers lay).values i)
def leafBufferBytes (sig : WCT9.Signature) (lay : Layer) : List UInt8 :=
  if lay = 0 then zeros 32 ++ endpointBytes sig lay ++ zeros 16
  else (endpointBytes sig lay).take 16 ++ zeros 16 ++ (endpointBytes sig lay).drop 16 ++ zeros 32
def leafBuffersBytes (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 4).reverse.flatMap (leafBufferBytes sig)
def tailBytes (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ zeros 8 ++ bytesLE 4 w.digestCounter ++ zeros 4
def witList (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytes N w ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++ leafBuffersBytes w.signature ++ tailBytes w
def witEnc (N : HashOutput) (w : WCT9.Witness) : WBytes := BitVec.ofNat _ (readLE (witList N w))
def expandB (message : Message) (pk : Digest) (sig : WCT9.Signature) : M (Option WBytes) :=
  (Option.map fun x => witEnc x.1 x.2) <$> expandN message pk sig
def witDecP (N : HashOutput) (w : WBytes) : WCT9.Witness where
  signature :=
    { rho := wrho w
      openings := fun k =>
        ⟨fun t => wreveal w k.val t.val (WCT9.wordDigit (WCT9.rank N k) t),
          fun l => wsib w k.val (WCT9.child N k).val l.val⟩
      layers := fun lay =>
        ⟨fun i => wvalue w lay i.val, fun j => wpath w lay (route (WCT9.digestIndex N) lay).1 j.val⟩ }
  digestCounter := wdc w
  counters := fun lay => wbcCtr w (WCT9.digestIndex N) lay
def padDecP (N : HashOutput) (w : WBytes) : Pads where
  wctChain k t := wcpads w k.val t.val
  wctChainHigh k t := wcHeaderPad w k.val t.val
  wctMerkle k l := if l.val < 5 ∨ (l.val = 5 ∧ k.val = 0) then wmpad w k.val (WCT9.child N k).val l.val else 0
  wctMerkleHigh k l := wmhpad w k.val (WCT9.child N k).val l.val
  wctLeaf k := if k.val = 0 then wleafPad w 0 else 0
  chain lay i := wchainPads w lay i.val
  merkle lay j := if j.val + 1 < height lay ∨ lay.val = 0 then
    wmerklePad w lay (route (WCT9.digestIndex N) lay).1 j.val else 0
  chainHeader lay i := wchainHeaderPad w lay i.val
  bc lay := wbcPad w (WCT9.digestIndex N) lay
  bcRight := wbcRight w
  endpointMask lay i := wvalue w lay i.val ^^^ wdig w (leafBufferSlot lay i.val)
@[simp] theorem valueP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) :
    valueP (witDecP N w).signature (padDecP N w) lay digits i = wvalueFor w lay digits i.val := by
  simp [valueP, witDecP, padDecP, wvalueFor, BitVec.xor_assoc]
def Shaped (N : HashOutput) (_w : WBytes) : Prop := WCT9.admissible N = true
instance (N : HashOutput) (w : WBytes) : Decidable (Shaped N w) := by
  unfold Shaped; infer_instance
def verifyTailP (pk : Digest) (w : WBytes) (N : HashOutput) : M Bool := do
  if !gateOk N then return false
  let index := WCT9.digestIndex N
  let some top ← wctP w N | pure false
  let some root ← layersBC w index 4 (.pair top.1 top.2) | pure false
  pure (root == pk)
def rejectTail (w : WBytes) (N : HashOutput) : M Bool :=
  if !gateOk N then pure false else (fun _ => false) <$> wctP w N
end ClaudeWCT.W9.T3M


namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open W9Machine
open SphincsSecurity (bytesLE)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Canonical coordinate views of the compact four-pair forest. -/
def coordinateValues (opened : ForestOpening) (coord : Fin 9) : Fin 6 → Digest :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then (opened.pairs pair).firstValues else (opened.pairs pair).secondValues
  else opened.singleton.values

def coordinatePath (opened : ForestOpening) (coord : Fin 9) : Nat → Digest :=
  if h : coord.val < 8 then
    let pair : Fin 4 := ⟨coord.val / 2, by omega⟩
    if coord.val % 2 = 0 then fun level => (opened.pairs pair).firstPath ⟨level % 6, Nat.mod_lt _ (by decide)⟩
    else fun level => (opened.pairs pair).secondPath ⟨level % 7, Nat.mod_lt _ (by decide)⟩
  else fun level => opened.singleton.path ⟨level % 7, Nat.mod_lt _ (by decide)⟩

/-- Each reveal is present at the chain input and at the endpoint location used
by a zero-step chain. Authentication siblings use the installed shared layout. -/
def coordinateSlots (output : HashOutput) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (coord : Fin 9) : List (Nat × Digest) :=
  let physical := SharedV3.physical coord.val (rawChildFromOutput output coord).val
  let values := coordinateValues sig.forest coord
  let path := coordinatePath sig.forest coord
  ((List.finRange 6).flatMap fun i =>
    [(V3.chainOffset coord.val i.val + 48, values i),
      (V3.regionOffset coord.val + V3.leafSlot i.val, values i)]) ++
    ((List.range (SharedV3.lastLevel coord.val + 1)).map fun level =>
      (V3.regionOffset coord.val + SharedV3.sibOff physical level, path level)) ++
    [(SharedV3.topOtherOff coord.val physical, path (SharedV3.lastLevel coord.val + 1))]

def forestSlots (output : HashOutput) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    List (Nat × Digest) := (List.finRange 9).flatMap (coordinateSlots output sig)

def slotByte (slots : List (Nat × Digest)) (offset : Nat) : UInt8 :=
  match slots.find? (fun p => decide (p.1 ≤ offset ∧ offset < p.1 + 16)) with
  | some p => (bytesLE 16 p.2).getD (offset - p.1) 0
  | none => 0

def forestBytes (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : List UInt8 :=
  (List.range 8256).map fun offset =>
    if 32 ≤ offset ∧ offset < 36 then (bytesLE 4 (witness.counters 3)).getD (offset - 32) 0
    else slotByte (forestSlots output witness.signature) offset

def mainWitness (witness : SigGolfCandidate.Research.SharedForest.Witness) : WCT9.Witness :=
  ⟨mainSignature witness.signature, witness.digestCounter, witness.counters⟩

def witList (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : List UInt8 :=
  forestBytes output witness ++ (ClaudeWCT.W9.T3M.witList output (mainWitness witness)).drop 8256

def witEnc (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness) : WBytes :=
  BitVec.ofNat _ (readLE (witList output witness))

@[simp] theorem forestBytes_length (output : HashOutput)
    (witness : SigGolfCandidate.Research.SharedForest.Witness) : (forestBytes output witness).length = 8256 := by
  simp [forestBytes]

/-- Query-identical expansion retaining the digest output needed by the memory encoder. -/
def expandN (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    M (Option (HashOutput × SigGolfCandidate.Research.SharedForest.Witness)) := do
  if sig.policyHints.toNat ≥ 5832 then return none
  let sig0 := fillTopSignature sig 0
  let some (counter, output) ← sharedDigestSearch sig0.rho message 0 WCT9.digestAttemptLimit | pure none
  let index := WCT9.digestIndex output
  let forest ← recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output) sig0.forest
  let some layers ← recoverHintedLayers sig0 index ((sig0.layers 0).path WCT9.topJ)
    4 (.pair forest.1 forest.2) | pure none
  if !policyHintsValid sig0.policyHints layers.digits then return none
  if layers.root = pk then
    return some (output, ⟨sig0, counter, fun lay => layers.counters.getD lay.val 0⟩)
  let some c ← WCT9.searchTop index layers.foldedTop ((sig0.layers 0).path WCT9.topJ) pk WCT9.searchFuel 1 | pure none
  pure (some (output, ⟨fillTopSignature sig0 c, counter, fun lay => layers.counters.getD lay.val 0⟩))

def expandB (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    M (Option WBytes) := (Option.map fun p => witEnc p.1 p.2) <$> expandN message pk sig

/-- Invalid ranks stop at their coordinate after the preceding coordinates' queries. -/
def ftsStep (w : WBytes) (output : HashOutput) (state : Option (List (Digest × Digest)))
    (coord : Fin 9) : M (Option (List (Digest × Digest))) := do
  let some pairs := state | pure none
  if ¬rawForestRank output coord.val < 563 then return none
  let pair ← SharedV3.coordinate w (WCT9.digestIndex output) coord (rawChildFromOutput output coord)
    (WCT9.embed (forestRank output coord.val)) (pairs.getLastD (SharedV3.initialPair w))
  pure (some (pairs ++ [pair]))

def ftsP (w : WBytes) (output : HashOutput) : M (Option (Digest × Digest)) := do
  if !(decide (output.toNat / 2^242 % 16384 < 734) : Bool) then return none
  let some pairs ← (List.finRange 9).foldlM (ftsStep w output) (some []) | pure none
  pure (some (pairs.getLastD (SharedV3.initialPair w)))

def verifyP (message : Message) (pk : Digest) (w : WBytes) : M Bool := do
  let some output ← digestP message w | pure false
  let some top ← ftsP w output | pure false
  let some root ← layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2) | pure false
  pure (root == pk)

theorem expandN_snd (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    Option.map Prod.snd <$> expandN message pk sig =
      SigGolfCandidate.Research.SharedForest.expand message pk sig := by
  unfold expandN SigGolfCandidate.Research.SharedForest.expand
  split
  · simp
  · try simp only [map_bind]
    apply bind_congr
    intro result
    cases result with
    | none => simp
    | some result =>
      obtain ⟨counter,output⟩ := result
      dsimp only
      try simp only [map_bind]
      apply bind_congr
      intro forest
      try simp only [map_bind]
      apply bind_congr
      intro layers
      cases layers with
      | none => simp
      | some layers =>
        dsimp only
        split
        · simp
        · split
          · simp
          · try simp only [map_bind]
            apply bind_congr
            intro completed
            cases completed <;> simp

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.Research.SharedForest W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def plainFtsStep (w : WBytes) (output : HashOutput) (prev : Digest × Digest) (coord : Fin 9) :
    M (Digest × Digest) :=
  SharedV3.coordinate w (WCT9.digestIndex output) coord (rawChildFromOutput output coord)
    (WCT9.embed (forestRank output coord.val)) prev

theorem fts_fold_none (w : WBytes) (output : HashOutput) (xs : List (Fin 9)) :
    xs.foldlM (ftsStep w output) none = pure none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldlM_cons, ftsStep, pure_bind, ih]

theorem fts_fold_cons_good (w : WBytes) (output : HashOutput) (x : Fin 9) (xs : List (Fin 9))
    (pairs : List (Digest × Digest)) (hr : rawForestRank output x.val < 563) :
    (x::xs).foldlM (ftsStep w output) (some pairs) =
      (plainFtsStep w output (pairs.getLastD (SharedV3.initialPair w)) x >>= fun pair =>
        xs.foldlM (ftsStep w output) (some (pairs ++ [pair]))) := by
  simp only [List.foldlM_cons, ftsStep, hr, not_true_eq_false, if_false, bind_assoc, pure_bind]
  rfl

theorem fts_fold_success (answers : Answers) (w : WBytes) (output : HashOutput) :
    ∀ (xs : List (Fin 9)) (pairs found : List (Digest × Digest)),
    evalWithAnswerFn answers (xs.foldlM (ftsStep w output) (some pairs)) = some found →
    (∀ coord ∈ xs, rawForestRank output coord.val < 563) ∧
    evalWithAnswerFn answers (xs.foldlM (plainFtsStep w output) (pairs.getLastD (SharedV3.initialPair w))) =
      found.getLastD (SharedV3.initialPair w) ∧
    queried answers (xs.foldlM (plainFtsStep w output) (pairs.getLastD (SharedV3.initialPair w))) =
      queried answers (xs.foldlM (ftsStep w output) (some pairs)) := by
  intro xs
  induction xs with
  | nil =>
      intro pairs found h
      simp only [List.foldlM_nil, evalWithAnswerFn_pure, Option.some.injEq] at h
      subst found
      exact ⟨fun _ h => False.elim (List.not_mem_nil h), rfl, rfl⟩
  | cons x xs ih =>
      intro pairs found h
      have hr : rawForestRank output x.val < 563 := by
        by_contra hn
        simp only [List.foldlM_cons, ftsStep, hn, not_false_eq_true, if_true, pure_bind,
          fts_fold_none, evalWithAnswerFn_pure] at h
        cases h
      rw [fts_fold_cons_good w output x xs pairs hr, evalWithAnswerFn_bind] at h
      obtain ⟨hgood, heval, hqueries⟩ := ih (pairs ++ [evalWithAnswerFn answers
        (plainFtsStep w output (pairs.getLastD (SharedV3.initialPair w)) x)]) found h
      simp only [List.getLastD_concat] at heval hqueries
      refine ⟨fun coord hc => ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact hr
        · exact hgood coord hc
      · rw [List.foldlM_cons, evalWithAnswerFn_bind]
        exact heval
      · rw [List.foldlM_cons, queried_bind, fts_fold_cons_good w output x xs pairs hr, queried_bind]
        exact congrArg (fun tail => queried answers
          (plainFtsStep w output (pairs.getLastD (SharedV3.initialPair w)) x) ++ tail) hqueries

theorem ftsP_success (answers : Answers) (w : WBytes) (output : HashOutput) (top : Digest × Digest)
    (h : evalWithAnswerFn answers (ftsP w output) = some top) :
    output.toNat / 2^242 % 16384 < 734 ∧
    (∀ coord : Fin 9, rawForestRank output coord.val < 563) ∧
    evalWithAnswerFn answers (SharedV3.forest w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) = top ∧
    queried answers (SharedV3.forest w (WCT9.digestIndex output)
      (rawChildFromOutput output) (fun k => WCT9.embed (forestRank output k.val))) =
      queried answers (ftsP w output) := by
  have hg : output.toNat / 2^242 % 16384 < 734 := by
    by_contra hn
    simp only [ftsP, hn, decide_false, Bool.not_false, ↓reduceIte, evalWithAnswerFn_pure] at h
    cases h
  simp only [ftsP, hg, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    evalWithAnswerFn_bind] at h
  cases hf : evalWithAnswerFn answers ((List.finRange 9).foldlM (ftsStep w output) (some [])) with
  | none => rw [hf] at h; simp at h
  | some pairs =>
      rw [hf, evalWithAnswerFn_pure, Option.some.injEq] at h
      obtain ⟨hr, he, hq⟩ := fts_fold_success answers w output (List.finRange 9) [] pairs hf
      refine ⟨hg, fun coord => hr coord (List.mem_finRange coord), ?_, ?_⟩
      · exact he.trans h
      · simp only [ftsP, hg, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          queried_bind, hf, queried_pure, List.append_nil]
        exact hq
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem verifyP_split (answers : Answers) (message : Message) (pk : Digest) (w : WBytes)
    (h : evalWithAnswerFn answers (verifyP message pk w) = true) :
    ∃ output top,
      evalWithAnswerFn answers (digestP message w) = some output ∧
      evalWithAnswerFn answers (ftsP w output) = some top ∧
      evalWithAnswerFn answers (layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2)) = some pk ∧
      (∀ q ∈ queried answers (digestP message w), q ∈ queried answers (verifyP message pk w)) ∧
      (∀ q ∈ queried answers (ftsP w output), q ∈ queried answers (verifyP message pk w)) ∧
      (∀ q ∈ queried answers (layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2)),
        q ∈ queried answers (verifyP message pk w)) := by
  rw [verifyP, evalWithAnswerFn_bind] at h
  cases hd : evalWithAnswerFn answers (digestP message w) with
  | none => rw [hd] at h; simp at h
  | some output =>
      rw [hd, evalWithAnswerFn_bind] at h
      cases hf : evalWithAnswerFn answers (ftsP w output) with
      | none => rw [hf] at h; simp at h
      | some top =>
          rw [hf, evalWithAnswerFn_bind] at h
          cases hl : evalWithAnswerFn answers
            (layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2)) with
          | none => rw [hl] at h; simp at h
          | some root =>
              rw [hl, evalWithAnswerFn_pure, beq_iff_eq] at h
              subst root
              have hq : queried answers (verifyP message pk w) =
                  queried answers (digestP message w) ++
                    (queried answers (ftsP w output) ++
                      queried answers (layersCanonicalBC w (WCT9.digestIndex output) 4 (.pair top.1 top.2))) := by
                simp only [verifyP, queried_bind, hd, hf, hl, queried_pure, List.append_nil]
              refine ⟨output, top, (by first | exact hd | rfl), (by first | exact hf | rfl), (by first | exact hl | rfl), ?_, ?_, ?_⟩
              · intro q hqD
                rw [hq]
                exact List.mem_append_left _ hqD
              · intro q hqF
                rw [hq]
                exact List.mem_append_right _ (List.mem_append_left _ hqF)
              · intro q hqL
                rw [hq]
                exact List.mem_append_right _ (List.mem_append_right _ hqL)

theorem digestP_success (answers : Answers) (message : Message) (w : WBytes) (output : HashOutput)
    (h : evalWithAnswerFn answers (digestP message w) = some output) :
    (wdc w).toNat < WCT9.digestVerifyWindow ∧
    evalWithAnswerFn answers (digest (wrho w) message (wdc w)) = output ∧
    queried answers (digestP message w) =
      [.inl (.inr (pad64 (digestInput (wrho w) message (wdc w))))] := by
  unfold digestP at h ⊢
  split_ifs at h ⊢ with hc
  · simp at h
  · simp only [evalWithAnswerFn_map, Option.some.injEq] at h
    refine ⟨by omega, h, ?_⟩
    rw [map_eq_bind_pure_comp, queried_bind]
    rfl
end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem expandN_selections (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    sig.policyHints.toNat < 5832 ∧ ∃ counter result c,
      evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 WCT9.digestAttemptLimit) =
        some (counter, output) ∧
      evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0) (WCT9.digestIndex output)
        (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)) = some result ∧
      policyHintsValid sig.policyHints result.digits = true ∧
      w.signature = fillTopSignature sig c ∧ w.digestCounter = counter ∧
      (∀ lay, w.counters lay = result.counters.getD lay.val 0) := by
  unfold expandN at he
  simp only [show (fillTopSignature sig 0).rho = sig.rho from rfl,
    show (fillTopSignature sig 0).forest = sig.forest from rfl,
    show (fillTopSignature sig 0).policyHints = sig.policyHints from rfl] at he
  by_cases hh : sig.policyHints.toNat ≥ 5832
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  · simp only [hh, if_false, evalWithAnswerFn_bind] at he
    cases hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 WCT9.digestAttemptLimit) with
    | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some found =>
        obtain ⟨counter, N⟩ := found
        simp only [hd, evalWithAnswerFn_bind] at he
        let forest := evalWithAnswerFn answers (recoverForest (WCT9.digestIndex N)
          (forestSelectionFromOutput N) (forestWordsFromOutput N) sig.forest)
        cases hr : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0)
          (WCT9.digestIndex N) (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
          (.pair forest.1 forest.2)) with
        | none =>
            dsimp only [forest] at hr
            simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
        | some result =>
            dsimp only [forest] at hr
            simp only [hr] at he
            by_cases hp : policyHintsValid sig.policyHints result.digits = true
            · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hk : result.root = pk
              · simp only [hk, if_true, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                exact ⟨by omega, counter, result, 0, (by first | exact hd | rfl), (by first | exact hr | rfl), hp, rfl, rfl, fun _ => rfl⟩
              · simp only [hk, if_false, evalWithAnswerFn_bind] at he
                cases hc : evalWithAnswerFn answers (WCT9.searchTop (WCT9.digestIndex N) result.foldedTop
                  (((fillTopSignature sig 0).layers 0).path WCT9.topJ) pk WCT9.searchFuel 1) with
                | none => simp only [hc, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    simp only [hc, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                    obtain ⟨rfl, rfl⟩ := he
                    exact ⟨by omega, counter, result, c, (by first | exact hd | rfl), (by first | exact hr | rfl), hp,
                      fillTopSignature_fillTopSignature sig 0 c, rfl, fun _ => rfl⟩
            · have hp0 := Bool.eq_false_of_not_eq_true hp
              simp only [hp0, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem forest_eq_of_coordinates (a b : ForestOpening)
    (hv : ∀ (coord : Fin 9) (i : Fin 6), coordinateValues a coord i = coordinateValues b coord i)
    (hp : ∀ (coord : Fin 9) level, level < (if coord.val < 8 ∧ coord.val % 2 = 0 then 6 else 7) →
      coordinatePath a coord level = coordinatePath b coord level) : a = b := by
  have hpair : a.pairs = b.pairs := by
    funext pair
    have hvalA : (a.pairs pair).firstValues = (b.pairs pair).firstValues := by
      funext i
      have h := hv ⟨2*pair.val,by have := pair.isLt;omega⟩ i
      fin_cases pair <;> simpa only [coordinateValues, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod,
        Nat.reduceDiv, dite_true, if_true] using h
    have hvalB : (a.pairs pair).secondValues = (b.pairs pair).secondValues := by
      funext i
      have h := hv ⟨2*pair.val+1,by have := pair.isLt;omega⟩ i
      fin_cases pair <;> simpa only [coordinateValues, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceMod, Nat.reduceDiv, dite_true, Nat.reduceEqDiff, if_false] using h
    have hpathA : (a.pairs pair).firstPath = (b.pairs pair).firstPath := by
      funext i
      have h := hp ⟨2*pair.val,by have := pair.isLt;omega⟩ i.val
        (by fin_cases pair <;> simpa using i.isLt)
      fin_cases pair <;> simpa [coordinatePath, Nat.mod_eq_of_lt i.isLt] using h
    have hpathB : (a.pairs pair).secondPath = (b.pairs pair).secondPath := by
      funext i
      have h := hp ⟨2*pair.val+1,by have := pair.isLt;omega⟩ i.val
        (by fin_cases pair <;> simpa using i.isLt)
      fin_cases pair <;> simpa [coordinatePath, Nat.mod_eq_of_lt i.isLt] using h
    cases ha : a.pairs pair
    cases hb : b.pairs pair
    simp only [ha,hb] at hvalA hvalB hpathA hpathB
    cases hvalA;cases hvalB;cases hpathA;cases hpathB;rfl
  have hsingleton : a.singleton = b.singleton := by
    have hval : a.singleton.values = b.singleton.values := by
      funext i
      exact hv 8 i
    have hpath : a.singleton.path = b.singleton.path := by
      funext i
      have h := hp 8 i.val (by simpa using i.isLt)
      simpa [coordinatePath, Nat.mod_eq_of_lt i.isLt] using h
    cases ha : a.singleton
    cases hb : b.singleton
    simp only [ha,hb] at hval hpath
    cases hval;cases hpath;rfl
  cases a
  cases b
  simp only [ForestOpening.mk.injEq]
  exact ⟨hpair,hsingleton⟩
end ClaudeWCT.W9.T3M.Paired
