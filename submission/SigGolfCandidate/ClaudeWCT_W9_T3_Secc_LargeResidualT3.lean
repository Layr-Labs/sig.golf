import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEncodingResample
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_CanonEncoding
import SigGolfCandidate.T3_Secc_LargeResidualT3
import SigGolfCandidate.T3_Secc_WotsExtractWord

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
/-- Block of chain end `i` in a WOTS leaf input. Campaign T51 ("endpad"): the top leaf `end_0 | tweak | end_1 ..` has
the lower shape (#938: `pad | tweak | end_0 ..`, block `i + 2`). -/
def leafBlock (lay : Layer) (i : Nat) : Nat := if lay = 0 then listBlock i else listBlock i
/-- Block of FTS end `t` in the padded FTS leaf `end0 | hdr | pad | end1..end5` (campaign T8). -/
def ftsLeafSlot (t : Nat) : Nat := if t = 0 then 0 else t + 2
/-- Pad source of FTS coordinate `coord` (nested FTS r1-1): top node `b` of coordinate `coord - 1`; none for
coordinate 0, whose pads are the constant `ftsStart`. -/
def prevTop (index : Fin (2^31)) (coord : Fin 9) (b : Fin 2) : Option Coord :=
  if h : coord.val = 0 then none else some (.inl (.wctNode (ftsTopNode index ⟨coord.val - 1, by omega⟩ b)))
def childSlots : CanonGraph.Node → List (Coord × Nat)
  | .chain p => [(chainChild p, if WCT9.isG p.1.layer p.1.chain.val then 0 else 3)]
  | .leaf L => (List.range (chainCount L.1.lay)).map fun i => (.inl (.chain (endPoint L.1 i)), leafBlock L.1.lay i)
  | .node n => if trialCap n.1.lay n.1.level.val ≤ n.1.nonce.val then [] else
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList
  | .wctChain p => [(wctItem p.1 p.2.val, if WCT9.ftsIsG p.1.2.2.2.val then 0 else 3)]
  | .wctLeaf L => (List.ofFn fun t : Fin 6 => (wctItem (L.index, L.coord, L.child, t) 4, ftsLeafSlot t.val)) ++
      ((prevTop L.index L.coord 0).map (·, 2)).toList
  | .wctNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map (·, 0)).toList ++
      ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map (·, 3)).toList ++
      (if n.1.level.val = 5 then ((prevTop n.1.index n.1.coord 1).map (·, 2)).toList else [])
  | .forest index => (List.range 9).flatMap fun c =>
      [(.inl (.wctNode (ftsTopNode index (fin9 c) 0)), 2 + 2 * c), (.inl (.wctNode (ftsTopNode index (fin9 c) 1)), 3 + 2 * c)]
/-! ### Top-nonce layer (r3-lean-nonsec, Subagent L)
Trial nodes are ordinary coordinates. The value-level trial selection mirrors `CanonGraph.selNonce` with the label
of a trial replaced by its coordinate value (the used half). -/
/-- Coordinate of trial `j` of the position of `n`. -/
def trialCoord (n : TreeNode) (j : Nat) : Coord := .inl (.node (withNonce n j))
/-- Value-level `trialFails`. -/
def trialFailsV (v : Coord → Digest) (n : TreeNode) (j : Nat) : Prop :=
  topZeroOk (n.1.level.val + 1) (v (trialCoord n j)) = false
instance (v : Coord → Digest) (n : TreeNode) (j : Nat) : Decidable (trialFailsV v n j) := by
  unfold trialFailsV; infer_instance
/-- Value-level `Active`. -/
def ActiveV (v : Coord → Digest) (n : TreeNode) : Prop :=
  n.1.nonce.val < trialCap n.1.lay n.1.level.val ∧ ∀ j < n.1.nonce.val, trialFailsV v n j
instance (v : Coord → Digest) (n : TreeNode) : Decidable (ActiveV v n) := by unfold ActiveV; infer_instance
/-- Value-level `selNonce`. -/
def selNonceV (v : Coord → Digest) (n : TreeNode) : Nat :=
  ((List.range (trialCap n.1.lay n.1.level.val)).find? fun j => !decide (trialFailsV v n j)).getD
    (trialCap n.1.lay n.1.level.val - 1)
/-- The selected trial coordinate of a tree-node coordinate (identity on other coordinates). -/
def selCoordV (v : Coord → Digest) : Coord → Coord
  | .inl (.node n) => .inl (.node (withNonce n (selNonceV v n)))
  | c => c
/-- Tree value from coordinate values: the value of the selected trial of the child position. -/
def treeVal (v : Coord → Digest) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Digest :=
  ((treeChild lay tree level c).map fun x => v (selCoordV v x)).getD 0
/-- Coordinate values read through the selected trial (the published/honest value of a tree position). -/
def selVals (v : Coord → Digest) : Coord → Digest := fun c => v (selCoordV v c)
/-- Trials read by the cell of a tree node of this position (none for single-trial positions). -/
def trialDeps (n : TreeNode) : List Coord :=
  if trialCap n.1.lay n.1.level.val = 1 then [] else (List.range (trialCap n.1.lay n.1.level.val)).map (trialCoord n)
def childTrialDeps (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : List Coord :=
  match treeChild lay tree level c with
  | some (.inl (.node m)) => trialDeps m
  | _ => []
/-- Every coordinate the cell of a node reads: its slots, and for tree nodes the trials of the own position and of
the child positions. -/
def cellDeps : CanonGraph.Node → List Coord
  | .node n => (childSlots (.node n)).map Prod.fst ++ trialDeps n ++
      childTrialDeps n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val) ++
      childTrialDeps n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)
  | N => (childSlots N).map Prod.fst
theorem selNonceV_lt (v : Coord → Digest) (n : TreeNode) : selNonceV v n < trialCap n.1.lay n.1.level.val := by
  have hc := trialCap_pos n.1.lay n.1.level.val
  unfold selNonceV
  cases hf : (List.range (trialCap n.1.lay n.1.level.val)).find? fun j => !decide (trialFailsV v n j) with
  | none => simp only [Option.getD_none]; omega
  | some j =>
      simp only [Option.getD_some]
      exact List.mem_range.mp (List.mem_of_find?_eq_some hf)
theorem selNonceV_congr {v w : Coord → Digest} {n : TreeNode}
    (h : ∀ j < trialCap n.1.lay n.1.level.val, v (trialCoord n j) = w (trialCoord n j)) :
    selNonceV v n = selNonceV w n := by
  unfold selNonceV
  congr 1
  apply find?_congr'
  intro j hj
  rw [List.mem_range] at hj
  have hiff : trialFailsV v n j ↔ trialFailsV w n j := by unfold trialFailsV; rw [h j hj]
  simp only [decide_eq_decide.mpr hiff]
theorem selNonceV_cap_one {v : Coord → Digest} {n : TreeNode} (h : trialCap n.1.lay n.1.level.val = 1) :
    selNonceV v n = 0 := by
  have := selNonceV_lt v n; omega
theorem activeV_congr {v w : Coord → Digest} {n : TreeNode}
    (h : trialCap n.1.lay n.1.level.val ≠ 1 → ∀ j < trialCap n.1.lay n.1.level.val, v (trialCoord n j) = w (trialCoord n j)) :
    ActiveV v n ↔ ActiveV w n := by
  unfold ActiveV trialFailsV
  by_cases h1 : trialCap n.1.lay n.1.level.val = 1
  · rw [h1]
    constructor <;> rintro ⟨hn, -⟩ <;> exact ⟨hn, fun j hj => by omega⟩
  · constructor <;> rintro ⟨hn, hj⟩ <;> refine ⟨hn, fun j hjn => ?_⟩
    · rw [← h h1 j (by omega)]; exact hj j hjn
    · rw [h h1 j (by omega)]; exact hj j hjn
theorem mem_trialDeps {n : TreeNode} (h : trialCap n.1.lay n.1.level.val ≠ 1) {j : Nat}
    (hj : j < trialCap n.1.lay n.1.level.val) : trialCoord n j ∈ trialDeps n := by
  unfold trialDeps
  rw [if_neg h]
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
/-- Selection of a coordinate only reads the trials of its position. -/
theorem selCoordV_congr {v w : Coord → Digest} (c : Coord)
    (h : ∀ n : TreeNode, c = .inl (.node n) → trialCap n.1.lay n.1.level.val ≠ 1 →
      ∀ j < trialCap n.1.lay n.1.level.val, v (trialCoord n j) = w (trialCoord n j)) :
    selCoordV v c = selCoordV w c := by
  rcases c with (_ | _ | n | _ | _ | _ | _) | s
  all_goals try rfl
  simp only [selCoordV]
  by_cases h1 : trialCap n.1.lay n.1.level.val = 1
  · rw [selNonceV_cap_one h1, selNonceV_cap_one h1]
  · rw [selNonceV_congr (h n rfl h1)]
theorem treeVal_congr {v w : Coord → Digest} (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ x ∈ (treeChild lay tree level c).toList, v (selCoordV v x) = w (selCoordV v x))
    (hd : ∀ x ∈ childTrialDeps lay tree level c, v x = w x) :
    treeVal v lay tree level c = treeVal w lay tree level c := by
  unfold treeVal
  cases ht : treeChild lay tree level c with
  | none => rfl
  | some x =>
      simp only [Option.map_some, Option.getD_some]
      rw [ht] at h
      have hx := h x (by simp)
      rw [hx]
      congr 1
      apply selCoordV_congr
      intro n hn h1 j hj
      apply hd
      unfold childTrialDeps
      rw [ht, hn]
      exact mem_trialDeps h1 hj

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

/-- Top-nonce layer: every keygen nonce trial of a top position is a disclosed keygen coordinate (its input is
public: children are cache values, the nonce is the trial index; no secret value). -/
noncomputable def topTrialsDisclosed : List Coord :=
  ((Finset.univ : Finset TreeNode).filter fun n =>
    n.1.lay = 0 ∧ trialCap n.1.lay n.1.level.val ≠ 1 ∧ n.1.nonce.val < trialCap n.1.lay n.1.level.val).toList.map
    fun n => .inl (.node n)

noncomputable def keygenDisclosed : List Coord :=
  keygenCacheDisclosed ++ encodingDisclosed ++ topTrialsDisclosed

attribute [local irreducible] Finset.univ

theorem msgSlot_mem_keygen {L : EncLeaf} {cs : Coord × Nat} (hc : cs ∈ msgSlots L) :
    cs.1 ∈ keygenDisclosed := by
  apply List.mem_append_left topTrialsDisclosed
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

theorem mem_topTrialsDisclosed {c : Coord} :
    c ∈ topTrialsDisclosed ↔ ∃ n : TreeNode, c = .inl (.node n) ∧
      n.1.lay = 0 ∧ trialCap n.1.lay n.1.level.val ≠ 1 ∧ n.1.nonce.val < trialCap n.1.lay n.1.level.val := by
  unfold topTrialsDisclosed
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, rfl, hn⟩
  · rintro ⟨n, rfl, hn⟩; exact ⟨n, hn, rfl⟩
theorem topTrialsDisclosed_shape {c : Coord} (hc : c ∈ topTrialsDisclosed) : ∃ n, c = .inl (.node n) := by
  obtain ⟨n, rfl, -⟩ := mem_topTrialsDisclosed.mp hc
  exact ⟨n, rfl⟩
theorem trialCoord_mem_topTrials {n : TreeNode} (hl : n.1.lay = 0) (hc : trialCap n.1.lay n.1.level.val ≠ 1) {j : Nat}
    (hj : j < trialCap n.1.lay n.1.level.val) : trialCoord n j ∈ topTrialsDisclosed := by
  refine mem_topTrialsDisclosed.mpr ⟨withNonce n j, rfl, hl, hc, ?_⟩
  have := trialCap_le n.1.lay n.1.level.val
  rw [withNonce_nonce n (by omega)]
  exact hj
theorem trialCoord_mem_keygen {n : TreeNode} (hl : n.1.lay = 0) (hc : trialCap n.1.lay n.1.level.val ≠ 1) {j : Nat}
    (hj : j < trialCap n.1.lay n.1.level.val) : trialCoord n j ∈ keygenDisclosed := by
  apply List.mem_append_right
  refine mem_topTrialsDisclosed.mpr ⟨withNonce n j, rfl, hl, hc, ?_⟩
  have := trialCap_le n.1.lay n.1.level.val
  rw [withNonce_nonce n (by omega)]
  exact hj
/-- Membership in the keygen disclosure by its three parts. -/
theorem mem_keygenDisclosed {c : Coord} :
    c ∈ keygenDisclosed ↔ c ∈ keygenCacheDisclosed ∨ c ∈ encodingDisclosed ∨ c ∈ topTrialsDisclosed := by
  unfold keygenDisclosed
  simp only [List.mem_append, or_assoc]

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

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
open SigGolfCandidate.T3.Security.LargeResidual (slotValue)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Physical tree leaves retain their raw seed-family coordinates. -/
def ftsChild (index : Fin (2^31)) (coord : Fin 9) (level physical : Nat) : Option Coord :=
 if level=0 then
   if h:CanonGraph.Paired.rawLeaf coord.val physical<128 then
     some (.inl (.wctLeaf ⟨index,coord,⟨CanonGraph.Paired.rawLeaf coord.val physical,h⟩⟩))
   else none
 else (ftsNodeAt index coord (level-1) physical).map fun n => .inl (.wctNode n)

/-- The exact branch-dependent L/R pad source. -/
def padCoord (index : Fin (2^31)) (coord : Fin 9) (branch : Nat) (side : Fin 2) : Option Coord :=
 if h:coord.val=0 then none else
   let previous : Fin 9 := ⟨coord.val-1,by have:=coord.isLt;omega⟩
   if coord.val%2=1 then ftsChild index previous 5 (2*branch+side.val)
   else ftsChild index previous 6 side.val

def childSlots : CanonGraph.Node → List (Coord×Nat)
 | .wctLeaf L => (List.ofFn fun t:Fin 6 => (wctItem (L.index,L.coord,L.child,t) 4,ftsLeafSlot t.val)) ++
   ((padCoord L.index L.coord (L.child.val%2) 0).map (·,2)).toList
 | .wctNode n => ((ftsChild n.1.index n.1.coord n.1.level.val (2*n.1.idx.val)).map (·,0)).toList ++
   ((ftsChild n.1.index n.1.coord n.1.level.val (2*n.1.idx.val+1)).map (·,3)).toList ++
   (if n.1.level.val=4 then ((padCoord n.1.index n.1.coord (n.1.idx.val/2) 1).map (·,2)).toList else [])
 | n => LargeResidual.childSlots n

noncomputable def honestValue (A : Answers) : Coord → Digest
 | .inl n => Extract.Paired.proj n.toPos (A (.inl (.inr (Extract.Paired.honestInput A n.toPos))))
 | .inr s => seedView (secretsOf A) s

inductive Known (D : Coord → Prop) : Coord → Prop
 | base {c : Coord} : D c → Known D c
 | node {n : CanonGraph.Node} : (∀cs∈childSlots n,Known D cs.1) → Known D (.inl n)

noncomputable def firstUnknown (K : Coord → Prop) (n : CanonGraph.Node) : Option (Coord×Nat) :=
 (childSlots n).find? fun cs => decide (¬K cs.1)

def StructuralContact (A : Answers) (K : Coord → Prop) (input : HashInput) (answer : HashOutput) : Prop :=
 ∃n:CanonGraph.Node, Extract.Paired.Bounded n.toPos ∧ Extract.posOf input=some n.toPos ∧
   ((∃cs,firstUnknown K n=some cs ∧ slotValue input cs.2=honestValue A cs.1) ∨
    (input≠Extract.Paired.honestInput A n.toPos ∧ Extract.Paired.proj n.toPos answer=honestValue A (.inl n)))

def EncodingContact (A : Answers) (input : HashInput) (answer : HashOutput) : Prop :=
 ∃(L:EncLeaf)(m:WCT9.LayerMsg)(ctr:BitVec 32)(pad:Wots.RowPad),Extract.msgFits L.1.lay m ∧
  input=Wots.encRow L.toWots m ctr pad ∧
  Wots.CanonicalRef.referenceSearch A (Wots.CanonicalRef.sourceMessages A) L.toWots≠none ∧
  Wots.CanonicalRef.referenceInput A (Wots.CanonicalRef.sourceMessages A) L.toWots≠some input ∧
  Wots.CanonicalRef.NotSearched A (Wots.CanonicalRef.sourceMessages A) L.toWots input ∧
  WCT9.encodingCanDecode L.1.lay answer
    (Wots.CanonicalRef.referenceDigits A (Wots.CanonicalRef.sourceMessages A) L.toWots)

def ContactTest (A : Answers) (K : Coord→Prop) (input : HashInput) (answer : HashOutput) : Prop :=
 StructuralContact A K input answer ∨ EncodingContact A input answer

theorem Known.mono {D D':Coord→Prop} (h:∀c,D c→D' c) {c:Coord} (hk:Known D c) : Known D' c := by
 induction hk with
 | base hc=>exact .base (h _ hc)
 | node _ ih=>exact .node ih

theorem firstUnknown_single (K:Coord→Prop) (n:CanonGraph.Node) (c:Coord) (b:Nat)
 (h:childSlots n=[(c,b)]) (hk:¬K c) : firstUnknown K n= some (c,b) := by
 unfold firstUnknown
 rw [h]
 simp [hk]

def Clear (A:Answers) (K:Coord→Prop) (X:HashInput) (y:HashOutput) : Prop :=
 (∀n:CanonGraph.Node,Extract.Paired.Bounded n.toPos→Extract.posOf X=some n.toPos→
   ¬(X≠Extract.Paired.honestInput A n.toPos ∧ Extract.Paired.proj n.toPos y=honestValue A (.inl n))) ∧
 (∀n:CanonGraph.Node,Extract.Paired.Bounded n.toPos→Extract.posOf X=some n.toPos→∀c b,
   childSlots n=[(c,b)]→slotValue X b=honestValue A c→K c) ∧
 ¬EncodingContact A X y

theorem clear_of_not_contact {A:Answers}{K:Coord→Prop}{X:HashInput}{y:HashOutput}
 (h:¬ContactTest A K X y) : Clear A K X y := by
 refine ⟨fun n hn hp hh=>h (Or.inl ⟨n,hn,hp,Or.inr hh⟩),?_,fun he=>h (Or.inr he)⟩
 intro n hn hp c b hc hv
 by_contra hk
 exact h (Or.inl ⟨n,hn,hp,Or.inl ⟨(c,b),firstUnknown_single K n c b hc hk,hv⟩⟩)

theorem Clear.mono {A:Answers}{K K':Coord→Prop}{X:HashInput}{y:HashOutput}
 (h:Clear A K X y) (hK:∀c,K c→K' c) : Clear A K' X y :=
 ⟨h.1,fun n hn hp c b hc hv=>hK c (h.2.1 n hn hp c b hc hv),h.2.2⟩
#print axioms clear_of_not_contact
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired

namespace ClaudeWCT.W9.T3.Security.LargeResidual.Paired
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open CanonGraph
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _

def wctOpened (index : Fin (2^31)) (k : Fin 9) (output : HashOutput) : List Coord :=
 List.ofFn fun t : Fin 6 => wctItem (index,k,rawChildFromOutput output k,t)
   (4-WCT9.wordDigit (forestRank output k.val) t)
def wctPath (index : Fin (2^31)) (k : Fin 9) (output : HashOutput) : List Coord :=
 (List.range (if firstCoord k.val then 6 else 7)).filterMap fun l =>
   ftsChild index k l ((physicalChildFromOutput output k).val/2^l ^^^ 1)
def ftsItems (index : Fin (2^31)) (output : HashOutput) : List Coord :=
 (List.finRange 9).flatMap fun k => wctOpened index k output ++ wctPath index k output
noncomputable def signItems (answers : Answers) (output : HashOutput) : List Coord :=
 ftsItems (digestIndex output) output ++ layerItems
   (Wots.CanonicalRef.referenceDigits answers (Wots.CanonicalRef.sourceMessages answers)) (digestIndex output)
def RouteOk (answers : Answers) (index : Nat) : Prop :=
 ∀lay : Layer,(Wots.CanonicalRef.referenceSearch answers (Wots.CanonicalRef.sourceMessages answers)
   (SigGolfCandidate.T3.Security.LargeResidual.routeAddr index lay)).isSome
noncomputable def signDigest (answers : Answers) (message : Message) : Option (BitVec 32×HashOutput) :=
 evalWithAnswerFn answers (sharedDigestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
   WCT9.digestAttemptLimit)
noncomputable def signDisclosed (answers : Answers) (published : SigGolfCandidate.T3.Cache)
    (request : SigGolfCandidate.T3.Security.Request) : List Coord :=
 if request.cache=published then
   match signDigest answers request.message with
   | some (_,output) => if RouteOk answers (WCT9.digestIndex output) then signItems answers output else []
   | none => []
 else []
end ClaudeWCT.W9.T3.Security.LargeResidual.Paired
