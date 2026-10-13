import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonEncoding
import SigGolfCandidate.T3.Secc.LargeResidualT3
import SigGolfCandidate.T3.Secc.WotsExtractWord

namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue routeAddr IsDigestRow)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeResidualT3 : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
def digestIndex (N : HashOutput) : Fin (2^31) := ⟨WCT9.digestIndex N, WCT9.digestIndex_lt N⟩
/-- Observable secret-side coordinates: WOTS seeds and FTS seeds (the latter are family evaluations, see
`FamResidual`; the hidden FTS coefficients are not observables). -/
abbrev SeedIndex := ChainGraph.Address ⊕ WctAddr
/-- The observable seeds of a secret table: WOTS seeds (top: secrets; lower: leaf-family values) and FTS seeds. -/
def seedView (secrets : CanonGraph.Secrets) : SeedIndex → Digest :=
  Sum.elim (seedsOf secrets) (wctSeedsOf secrets)
abbrev Coord := CanonGraph.Node ⊕ SeedIndex
def chainChild (p : ChainGraph.Point) : Coord :=
  if p.2.val = 0 then .inr (.inl p.1) else .inl (.chain (ChainGraph.predecessor p))
def treeChild (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option Coord :=
  if level = 0 then (leafAt lay tree c).map fun L => .inl (.leaf L)
  else (treeNodeAt lay tree (level - 1) c).map fun n => .inl (.node n)
def wctItem (a : WctAddr) (p : Nat) : Coord :=
  if p = 0 then .inr (.inr a) else .inl (.wctChain (a, ⟨(p - 1) % 4, Nat.mod_lt _ (by decide)⟩))
def ftsChild (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) : Option Coord :=
  if level = 0 then (if h : c < 128 then some (.inl (.wctLeaf ⟨index, coord, ⟨c, h⟩⟩)) else none)
  else (ftsNodeAt index coord (level - 1) c).map fun n => .inl (.wctNode n)
def endPoint (L : LeafPos) (i : Nat) : ChainGraph.Point :=
  (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(maxDigit L.lay i - 1) % 7, Nat.mod_lt _ (by decide)⟩)
def leafBlock (lay : Layer) (i : Nat) : Nat := if lay = 0 then i + 2 else listBlock i
/-- Block of FTS end `t` in the padded FTS leaf `end0 | hdr | pad | end1..end5` (campaign T8). -/
def ftsLeafSlot (t : Nat) : Nat := if t = 0 then 0 else t + 2
/-- Pad source of FTS coordinate `coord` (nested FTS r1-1): top node `b` of coordinate `coord - 1`; none for
coordinate 0, whose pads are the constant `ftsStart`. -/
def prevTop (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) : Option Coord :=
  if h : coord.val = 0 then none else some (.inl (.wctNode (ftsTopNode index ⟨coord.val - 1, by omega⟩ b)))
def childSlots : CanonGraph.Node → List (Coord × Nat)
  | .chain p => [(chainChild p, 3)]
  | .leaf L => (List.range (chainCount L.1.lay)).map fun i => (.inl (.chain (endPoint L.1 i)), leafBlock L.1.lay i)
  | .node n => ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .wctChain p => [(wctItem p.1 p.2.val, 3)]
  | .wctLeaf L => (List.ofFn fun t : Fin 6 => (wctItem (L.index, L.coord, L.child, t) 4, ftsLeafSlot t.val)) ++
      ((prevTop L.index L.coord 0).map (·, 2)).toList
  | .wctNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList ++
      (if n.1.level.val = 5 then ((prevTop n.1.index n.1.coord 1).map (·, 2)).toList else [])
  | .forest index => (List.range 9).flatMap fun c =>
      [(.inl (.wctNode (ftsTopNode index (fin9 c) 0)), 2 + 2 * c), (.inl (.wctNode (ftsTopNode index (fin9 c) 1)), 3 + 2 * c)]
noncomputable def honestValue (A : Answers) : Coord → Digest
  | .inl N => N.toPos.proj (A (.inl (.inr (Extract.honestInput A N.toPos))))
  | .inr s => seedView (secretsOf A) s
inductive Known (D : Coord → Prop) : Coord → Prop
  | base {c : Coord} : D c → Known D c
  | node {N : CanonGraph.Node} : (∀ cs ∈ childSlots N, Known D cs.1) → Known D (.inl N)
noncomputable def firstUnknown (K : Coord → Prop) (N : CanonGraph.Node) : Option (Coord × Nat) :=
  (childSlots N).find? fun cs => decide (¬K cs.1)
def keygenCacheDisclosed : List Coord :=
  (List.range' 0 13).flatMap fun level =>
    (List.range (2 ^ (12 - level))).filterMap fun node => treeChild 0 0 level node
def chainItem (L : LeafPos) (i d : Nat) : Coord :=
  if d = 0 then .inr (.inl ⟨L.lay, L.tree, L.leaf, fin58 i⟩)
  else .inl (.chain (⟨L.lay, L.tree, L.leaf, fin58 i⟩, ⟨(d - 1) % 7, Nat.mod_lt _ (by decide)⟩))
def wctOpened (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) : List Coord :=
  List.ofFn fun t : Fin 6 => wctItem (index, k, WCT9.child N k, t) (4 - WCT9.wordDigit (WCT9.rank N k) t)
def wctPath (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) : List Coord :=
  (List.range 7).filterMap fun l => ftsChild index k l ((WCT9.child N k).val / 2 ^ l ^^^ 1)
def ftsItems (index : Fin (2^31)) (N : HashOutput) : List Coord :=
  (List.finRange 9).flatMap fun k => wctOpened index k N ++ wctPath index k N
def layerChains (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 ∧ (route index.val lay).1 < 4096 then
    (List.range (chainCount lay)).map fun i =>
      chainItem ⟨lay, ⟨(route index.val lay).2, h.1⟩, ⟨(route index.val lay).1, h.2⟩⟩ i
        ((digitsOf (routeAddr index.val lay)).getD i 0)
  else []
def layerPath (index : Fin (2^31)) (lay : Layer) : List Coord :=
  if h : (route index.val lay).2 < 2 ^ 31 then
    (List.range (height lay)).filterMap fun j =>
      treeChild lay ⟨(route index.val lay).2, h⟩ j ((route index.val lay).1 / 2 ^ j ^^^ 1)
  else []
def layerItems (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) : List Coord :=
  (List.finRange 4).flatMap fun lay => layerChains digitsOf index lay ++ layerPath index lay
def signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) : List Coord :=
  ftsItems (digestIndex N) N ++ layerItems digitsOf (digestIndex N)
noncomputable def signItems (A : Answers) (N : HashOutput) : List Coord :=
  signItemsWith (Wots.referenceDigits A) N
def RouteOk (A : Answers) (index : Nat) : Prop :=
  ∀ lay : Layer, lay ≠ 0 → (Wots.referenceSearch A (routeAddr index lay)).isSome
noncomputable def signDigest (A : Answers) (message : Message) : Option (BitVec 32 × HashOutput) :=
  evalWithAnswerFn A (WCT9.digestSearch (evalWithAnswerFn A (privateNonce message)) message 0
    WCT9.digestAttemptLimit)
noncomputable def signDisclosed (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    List Coord :=
  if request.cache = published then
    match signDigest A request.message with
    | some (_, N) => if RouteOk A (WCT9.digestIndex N) then signItems A N else []
    | none => []
  else []
def msgSlots (L : EncLeaf) : List (Coord × Nat) :=
  if h : L.1.lay.val < 3 then
    [(.inl (.node (topNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L h) 0)), 0),
      (.inl (.node (topNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L h) 1)), 3)]
  else [(.inl (.wctNode (ftsTopNode (childIndex L) 8 0)), 0), (.inl (.wctNode (ftsTopNode (childIndex L) 8 1)), 3)]
/-- The large-game simulator may reveal internal message roots for free. These
coordinates contain neither WOTS chain values nor FTS chain values or seeds. -/
noncomputable def encodingDisclosed : List Coord :=
  (Finset.univ : Finset EncLeaf).toList.flatMap fun L => (msgSlots L).map Prod.fst

noncomputable def keygenDisclosed : List Coord :=
  keygenCacheDisclosed ++ encodingDisclosed

attribute [local irreducible] Finset.univ

theorem msgSlot_mem_keygen {L : EncLeaf} {cs : Coord × Nat} (hc : cs ∈ msgSlots L) :
    cs.1 ∈ keygenDisclosed := by
  apply List.mem_append_right keygenCacheDisclosed
  exact List.mem_flatMap.mpr ⟨L, Finset.mem_toList.mpr (Finset.mem_univ _),
    List.mem_map.mpr ⟨cs, hc, rfl⟩⟩

theorem encodingDisclosed_shape {c : Coord} (hc : c ∈ encodingDisclosed) :
    (∃ n, c = .inl (.node n)) ∨ ∃ n, c = .inl (.wctNode n) := by
  unfold encodingDisclosed at hc
  obtain ⟨L, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
  unfold msgSlots at hcs
  split_ifs at hcs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
    rcases hcs with rfl | rfl <;> exact Or.inl ⟨_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
    rcases hcs with rfl | rfl <;> exact Or.inr ⟨_, rfl⟩

def msgVals (vals : Coord → Digest) (L : EncLeaf) : WCT9.LayerMsg :=
  if h : L.1.lay.val < 3 then
    .pair (vals (.inl (.node (topNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L h) 0))))
      (vals (.inl (.node (topNode ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (childIndex_treeBits L h) 1))))
  else .pair (vals (.inl (.wctNode (ftsTopNode (childIndex L) 8 0))))
    (vals (.inl (.wctNode (ftsTopNode (childIndex L) 8 1))))
noncomputable def firstUnknownMsg (K : Coord → Prop) (L : EncLeaf) : Option (Coord × Nat) :=
  (msgSlots L).find? fun cs => decide (¬K cs.1)
def StructuralContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ N : CanonGraph.Node, Extract.posOf input = some N.toPos ∧
    ((∃ cs, firstUnknown K N = some cs ∧ slotValue input cs.2 = honestValue A cs.1) ∨
      (input ≠ Extract.honestInput A N.toPos ∧ N.toPos.proj answer = honestValue A (.inl N)))
def EncodingContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (L : EncLeaf) (m : WCT9.LayerMsg) (ctr : BitVec 32) (pad : Wots.RowPad), Extract.msgFits L.1.lay m ∧
    input = Wots.encRow L.toWots m ctr pad ∧
    ((∃ cs, firstUnknownMsg K L = some cs ∧ slotValue input cs.2 = honestValue A cs.1) ∨
      (Wots.referenceInput A L.toWots ≠ some input ∧
        decode L.1.lay (WCT9.encodingAnswer L.1.lay answer) = some (Wots.referenceDigits A L.toWots)))
def ContactTest (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
  StructuralContact A K input answer ∨ EncodingContact A K input answer
end ClaudeWCT.W9.T3.Security.LargeResidual
