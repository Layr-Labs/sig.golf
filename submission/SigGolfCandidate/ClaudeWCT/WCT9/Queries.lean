import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.ClaudeWCT.WCT9.Domains
import SigGolfCandidate.T3M.Extract.Leaf
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def leafInput (index coord selected : Nat) (ends : List Digest) : HashInput :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (ftsLeafHeader index coord selected) ++ zero16 ++
    (ends.drop 1).flatMap (bytesLE 16)
def nodeInput (coord index heap : Nat) (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 (wctNodeHeader coord index heap) ++ zero16 ++ bytesLE 16 right
theorem leafHash_eq (index coord selected : Nat) (ends : List Digest) :
    leafHash index coord selected ends = shortHash (leafInput index coord selected ends) := rfl
theorem leafInputP_zero (index coord selected : Nat) (ends : List Digest) :
    leafInputP index coord selected 0 ends = leafInput index coord selected ends := by
  unfold leafInputP leafInput
  rw [bytesLE_zero16]
theorem leafInputP_length (index coord selected : Nat) (pad : Digest) (ends : List Digest) (hlen : ends.length = 6) :
    (leafInputP index coord selected pad ends).length = 128 := by
  simp only [leafInputP, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop, hlen]
theorem nodeHash_eq (coord index heap : Nat) (left right : Digest) :
    wctNodeHash coord index heap left right = shortHash (nodeInput coord index heap left right) := rfl
theorem forestPk_eq (index : Nat) (pairs : List (Digest × Digest)) :
    forestPk index pairs = shortHash (forestInput index pairs) := rfl
theorem leafInput_length (index coord selected : Nat) (ends : List Digest) (hlen : ends.length = 6) :
    (leafInput index coord selected ends).length = 128 := by
  simp only [leafInput, zero16, List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop,
    List.length_replicate, hlen]
theorem nodeInput_length (coord index heap : Nat) (left right : Digest) :
    (nodeInput coord index heap left right).length = 64 := by
  simp only [nodeInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem pad64_of_mod {x : HashInput} (h : x.length % 64 = 0) : pad64 x = x := by
  simp only [pad64, h, Nat.sub_zero, Nat.mod_self, List.replicate_zero, List.append_nil]
inductive FtsInput (index : Nat) : HashInput → Prop
  | chain {coord selected t step : Nat} (value : Digest) (hcoord : coord < 9) (hsel : selected < 128)
      (ht : t < 6) (hstep : step < 4) :
      FtsInput index (pad64 (chainInput index coord selected t step value))
  | leaf {coord selected : Nat} {ends : List Digest} (hcoord : coord < 9) (hsel : selected < 128)
      (hlen : ends.length = 6) :
      FtsInput index (pad64 (leafInput index coord selected ends))
  | node {coord heap : Nat} (left right : Digest) (hcoord : coord < 9) (hlo : 2 ≤ heap) (hhi : heap < 128) :
      FtsInput index (pad64 (nodeInput coord index heap left right))
  | forest {pairs : List (Digest × Digest)} (hlen : pairs.length = 9) :
      FtsInput index (pad64 (forestInput index pairs))
/-- FTS private queries: the 51 coefficient pairs of each coordinate's seed family (campaign X1, stage A). -/
def FtsSeed (index : Nat) (tweak : BitVec 128) : Prop :=
  ∃ coord pair, coord < 9 ∧ pair < ftsCoefPairs ∧ tweak = ftsSeedHeader coord index pair
def FtsQuery (index : Nat) : Query → Prop
  | .inl (.inr input) => FtsInput index input
  | .inr (.inl tweak) => FtsSeed index tweak
  | _ => False
@[simp] theorem ftsQuery_public (index : Nat) (input : HashInput) :
    FtsQuery index (.inl (.inr input)) ↔ FtsInput index input := Iff.rfl
@[simp] theorem ftsQuery_private (index : Nat) (tweak : BitVec 128) :
    FtsQuery index (.inr (.inl tweak)) ↔ FtsSeed index tweak := Iff.rfl
theorem FtsInput.length {index : Nat} {x : HashInput} (h : FtsInput index x) :
    x.length = 64 ∨ x.length = 128 ∨ x.length = 320 := by
  cases h with
  | chain value hcoord hsel ht hstep =>
      left
      rw [pad64_of_mod (by rw [chainInput_length])]
      exact chainInput_length _ _ _ _ _ _
  | leaf hcoord hsel hlen =>
      right; left
      rw [pad64_of_mod (by rw [leafInput_length _ _ _ _ hlen])]
      exact leafInput_length _ _ _ _ hlen
  | node left right hcoord hlo hhi =>
      left
      rw [pad64_of_mod (by rw [nodeInput_length])]
      exact nodeInput_length _ _ _ _ _
  | forest hlen =>
      right; right
      rw [pad64_of_mod (by rw [forestInput_length _ _ hlen]), forestInput_length _ _ hlen]
theorem FtsInput.length_le {index : Nat} {x : HashInput} (h : FtsInput index x) : x.length ≤ 320 := by
  rcases h.length with h | h | h <;> omega
theorem ftsQuery_good {index : Nat} {q : Query} (h : FtsQuery index q) : GoodQuery q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · rcases (show FtsInput index input from h).length with hl | hl | hl <;>
      exact ⟨by omega, by omega⟩
  · trivial
  · exact h.elim
theorem hdrBlock_pad64_prefix (a : HashInput) (h : BitVec 128) (rest : HashInput) (ha : a.length = 16) :
    SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (a ++ bytesLE 16 h ++ rest)) = bytesLE 16 h := by
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [ha, bytesLE_length]; omega)]
  unfold SigGolfCandidate.T3M.Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' (bytesLE_length 16 h)]
theorem FtsInput.hdrBlock {index : Nat} {x : HashInput} (h : FtsInput index x) :
    (∃ coord selected t step, SigGolfCandidate.T3M.Extract.hdrBlock x =
      bytesLE 16 (ftsChainHeader index coord selected t step)) ∨
    (∃ coord selected, coord < 9 ∧ selected < 128 ∧
      SigGolfCandidate.T3M.Extract.hdrBlock x = bytesLE 16 (ftsLeafHeader index coord selected)) ∨
    (∃ coord heap, coord < 9 ∧ 2 ≤ heap ∧ heap < 128 ∧
      SigGolfCandidate.T3M.Extract.hdrBlock x = bytesLE 16 (wctNodeHeader coord index heap)) ∨
    SigGolfCandidate.T3M.Extract.hdrBlock x = bytesLE 16 (header 15 0 index 0 0) := by
  cases h with
  | @chain coord selected t step value hcoord hsel ht hstep =>
      refine Or.inl ⟨coord, selected, t, step, ?_⟩
      unfold chainInput
      rw [List.append_assoc (zero16 ++ _), hdrBlock_pad64_prefix _ _ _ (by simp [zero16])]
  | @leaf coord selected ends hcoord hsel hlen =>
      refine Or.inr (Or.inl ⟨coord, selected, hcoord, hsel, ?_⟩)
      unfold leafInput
      rw [List.append_assoc (bytesLE 16 _ ++ bytesLE 16 _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
  | @node coord heap left right hcoord hlo hhi =>
      refine Or.inr (Or.inr (Or.inl ⟨coord, heap, hcoord, hlo, hhi, ?_⟩))
      unfold nodeInput
      rw [List.append_assoc (bytesLE 16 left ++ _), hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
  | @forest pairs hlen =>
      refine Or.inr (Or.inr (Or.inr ?_))
      unfold forestInput
      rw [show zero16 = bytesLE 16 (0 : Digest) by decide, hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)]
theorem bound_shortHashP {P : Query → Prop} (input : HashInput) (k : Nat)
    (hq : P (.inl (.inr (pad64 input)))) (hk : (pad64 input).length / 64 ≤ k) :
    Bound P (fun _ => True) k (shortHash input) := by
  unfold shortHash publicHash
  exact Bound.qry_bind (k := 0) hq (fun _ => .pure _ 0 trivial) (by simpa only [weight, Nat.add_zero] using hk)
theorem bound_privatePairP {P : Query → Prop} (tag lay tree position index : Nat)
    (hq : P (.inr (.inl (header tag lay tree position index)))) :
    Bound P (fun _ => True) 1 (privatePair tag lay tree position index) := by
  unfold privatePair privateHash
  exact Bound.qry_bind (k := 0) hq (fun _ => .pure _ 0 trivial) (by simp only [weight]; omega)
theorem allQueriesSatisfy_of_bound {P : Query → Prop} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound P Post k oa) : AllQueriesSatisfy oa P := by
  induction h with
  | pure a k hp => exact allQueriesSatisfy_pure _ _
  | query q f k hq _ ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hq, ih⟩
theorem cbound_of_ftsBound {index : Nat} {α : Type} {Post : α → Prop} {k : Nat} {oa : M α}
    (h : Bound (FtsQuery index) Post k oa) : CBound Post k oa :=
  h.mono (fun _ hq => ftsQuery_good hq) (fun _ hp => hp)
section Programs
variable (index : Nat)
theorem ftsBound_chain (coord selected t start count : Nat) (value : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (ht : t < 6) (hend : start + count ≤ 4) :
    Bound (FtsQuery index) (fun _ => True) count (chain index coord selected t start count value) := by
  unfold chain
  refine Bound.foldlM_range'_le start count _ (fun _ _ => True) (fun _ => 1) value trivial
    (fun n hn value _ => ?_) (fun _ _ => trivial) (by simp)
  exact bound_shortHashP _ 1 (FtsInput.chain value hcoord hsel ht (by omega))
    (by simp [Cost.pad64_length, chainInput_length])
theorem ftsBound_leafHash (coord selected : Nat) (ends : List Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (hlen : ends.length = 6) :
    Bound (FtsQuery index) (fun _ => True) 2 (leafHash index coord selected ends) := by
  rw [leafHash_eq]
  exact bound_shortHashP _ 2 (FtsInput.leaf hcoord hsel hlen)
    (by rw [pad64_of_mod (by rw [leafInput_length _ _ _ _ hlen]), leafInput_length _ _ _ _ hlen])
theorem ftsBound_nodeHash (coord heap : Nat) (left right : Digest)
    (hcoord : coord < 9) (hlo : 2 ≤ heap) (hhi : heap < 128) :
    Bound (FtsQuery index) (fun _ => True) 1 (wctNodeHash coord index heap left right) := by
  rw [nodeHash_eq]
  exact bound_shortHashP _ 1 (FtsInput.node left right hcoord hlo hhi)
    (by rw [pad64_of_mod (by rw [nodeInput_length]), nodeInput_length])
theorem ftsBound_forestPk (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    Bound (FtsQuery index) (fun _ => True) 5 (forestPk index pairs) := by
  rw [forestPk_eq]
  exact bound_shortHashP _ 5 (FtsInput.forest hlen)
    (by rw [pad64_of_mod (by rw [forestInput_length _ _ hlen]), forestInput_length _ _ hlen])
theorem ftsBound_seedPair (coord pair : Nat) (hcoord : coord < 9) (hpair : pair < ftsCoefPairs) :
    Bound (FtsQuery index) (fun _ => True) 1 (ftsSeedPair index coord pair) :=
  bound_privatePairP _ _ _ _ _ ⟨coord, pair, hcoord, hpair, rfl⟩
/-- Kept for the lower layers' packed seeds (`Cost.lean`): one private query per even ordinal. -/
def seedCost (q : Nat) : Nat := if q % 2 = 0 then 1 else 0
theorem ftsBound_ftsCoefs (coord : Nat) (hcoord : coord < 9) :
    Bound (FtsQuery index) (fun _ => True) ftsCoefPairs (ftsCoefs index coord) := by
  unfold ftsCoefs
  refine Bound.foldlM_range_le (P := FtsQuery index) ftsCoefPairs _ (fun _ _ => True) (fun _ => 1) []
    trivial (fun j hj acc _ => ?_) (fun _ _ => trivial) (by simp)
  exact (ftsBound_seedPair index coord j hcoord hj).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by omega)
theorem ftsBound_childStep (coord selected : Nat) (word : Rank) (coefs : List Digest)
    (state : List Digest × List Digest) (i : Fin 6) (hcoord : coord < 9) (hsel : selected < 128)
    (hstate : state.1.length = i.val ∧ state.2.length = i.val) :
    Bound (FtsQuery index)
      (fun rows : List Digest × List Digest => rows.1.length = i.val + 1 ∧ rows.2.length = i.val + 1)
      4 (childStep index coord selected word coefs state i) := by
  unfold childStep
  have hd := wordDigit_le_four word i
  refine (ftsBound_chain index coord selected _ 0 _ _ hcoord hsel i.isLt (by omega)).bind'
    (l := wordDigit word i) (fun value _ => ?_) (by omega)
  refine (ftsBound_chain index coord selected _ _ _ value hcoord hsel i.isLt (by omega)).bind'
    (l := 0) (fun last _ => ?_) (by omega)
  exact .pure _ 0 ⟨by simp only [List.length_append, List.length_singleton]; omega,
    by simp only [List.length_append, List.length_singleton]; omega⟩
theorem ftsBound_childRows (coord selected : Nat) (word : Rank) (coefs : List Digest) (hcoord : coord < 9)
    (hsel : selected < 128) :
    Bound (FtsQuery index) (fun rows : List Digest × List Digest => rows.1.length = 6 ∧ rows.2.length = 6)
      24 (childRows index coord selected word coefs) := by
  unfold childRows
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 6) _
    (fun i (rows : List Digest × List Digest) => rows.1.length = i ∧ rows.2.length = i)
    (fun _ => 4) ([], []) ⟨rfl, rfl⟩
    (fun i hi rows hrows => ?_)).mono (fun _ h => h) (fun rows h => by simpa using h)).mono_k (by simp)
  have hi7 : i < 6 := by simpa using hi
  simp only [List.getElem_finRange, Fin.cast_mk]
  exact ftsBound_childStep index coord selected word coefs rows ⟨i, hi7⟩ hcoord hsel hrows
/-- Compressions per FTS child: 24 chain steps (6 chains of 4) and the 2-block leaf (no seed queries: stage-A
family seeds). -/
def childCost : Nat := 26
theorem ftsBound_buildChildF (coord selected : Nat) (word : Rank) (coefs : List Digest) (hcoord : coord < 9)
    (hsel : selected < 128) :
    Bound (FtsQuery index) (fun result : Digest × List Digest => result.2.length = 6)
      childCost (buildChildF index coord selected word coefs) := by
  rw [buildChildF_factor]
  refine (ftsBound_childRows index coord selected word coefs hcoord hsel).bind' (l := 2)
    (fun rows hrows => ?_) (by unfold childCost; omega)
  exact (ftsBound_leafHash index coord selected rows.1 hcoord hsel hrows.1).bind' (l := 0)
    (fun root _ => .pure _ 0 hrows.2) (by decide)
theorem ftsBound_coordRows (coord : Coord) (selected : Child) (word : Rank) (coefs : List Digest) :
    Bound (FtsQuery index) (fun _ => True) 3328 (coordRows index coord selected word coefs) := by
  unfold coordRows
  refine Bound.foldlM_range_le (P := FtsQuery index) 128 _ (fun _ _ => True) (fun _ => childCost) ([], [])
    trivial (fun j hj state _ => ?_) (fun _ _ => trivial) (by simp [childCost])
  exact (ftsBound_buildChildF index coord.val j word coefs coord.isLt hj).bind' (l := 0)
    (fun result _ => .pure _ 0 trivial) (by omega)
theorem ftsBound_heapBuild (coord : Nat) (hcoord : coord < 9) (leaves : List Digest) :
    Bound (FtsQuery index) (fun _ => True) 126 (heapBuild index coord leaves) := by
  unfold heapBuild
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.range' 2 126).reverse _ (fun _ _ => True)
    (fun _ => 1) _ trivial (fun i hi nodes _ => ?_)).mono (fun _ h => h) (fun _ _ => trivial)).mono_k
    (by simp)
  have hi' : i < 126 := by simpa using hi
  rw [heap_order i hi']
  exact (ftsBound_nodeHash index coord (127 - i) _ _ hcoord (by omega) (by omega)).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by omega)
/-- Per coordinate: 51 coefficient pairs, 128 children of 26, 126 heap nodes. -/
theorem ftsBound_buildCoordinateF (coord : Coord) (selected : Child) (word : Rank) :
    Bound (FtsQuery index) (fun _ => True) 3481 (buildCoordinateF index coord selected word) := by
  rw [buildCoordinateF_factor]
  refine (ftsBound_ftsCoefs index coord.val coord.isLt).bind' (l := 3454) (fun coefs _ => ?_)
    (by simp [ftsCoefPairs])
  refine (ftsBound_coordRows index coord selected word coefs).bind' (l := 126) (fun rows _ => ?_) (by decide)
  exact (ftsBound_heapBuild index coord.val coord.isLt rows.1).bind' (l := 0)
    (fun _ _ => .pure _ 0 trivial) (by decide)
theorem ftsBound_forestRows (output : HashOutput) :
    Bound (FtsQuery index)
      (fun state : List Opening × List (Digest × Digest) => state.1.length = 9 ∧ state.2.length = 9)
      31329 (forestRows index output) := by
  unfold forestRows
  refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 9) _
    (fun i (state : List Opening × List (Digest × Digest)) => state.1.length = i ∧ state.2.length = i)
    (fun _ => 3481) ([], []) ⟨rfl, rfl⟩ (fun i hi state hstate => ?_)).mono (fun _ h => h)
    (fun state h => by simpa using h)).mono_k (by simp)
  unfold openingStep
  exact (ftsBound_buildCoordinateF index _ _ _).bind' (l := 0)
    (fun result _ => .pure _ 0 ⟨by simp [hstate.1], by simp [hstate.2]⟩) (by decide)
theorem ftsBound_signForest (output : HashOutput) :
    Bound (FtsQuery index) (fun result : List Opening × Digest => result.1.length = 9) 31334
      (signForest index output) := by
  unfold signForest
  refine (ftsBound_forestRows index output).bind' (l := 5) (fun state hstate => ?_) (by decide)
  exact (ftsBound_forestPk index state.2 hstate.2).bind' (l := 0)
    (fun root _ => .pure _ 0 hstate.1) (by decide)
theorem recover_heap_bounds (level s : Nat) (hl : level < 6) (hs : s < 128) :
    2 ≤ 2 ^ (6 - level) + s / 2 ^ (level + 1) ∧ 2 ^ (6 - level) + s / 2 ^ (level + 1) < 128 := by
  interval_cases level <;> simp <;> omega
theorem ftsBound_recoverCoordinate (sig : Signature) (output : HashOutput) (coord : Coord) :
    Bound (FtsQuery index) (fun _ => True) 15 (recoverCoordinate sig index output coord) := by
  unfold recoverCoordinate
  dsimp only
  refine (Bound.mapM_list (P := FtsQuery index) (List.finRange 6) _ (fun i => wordDigit (rank output coord) i)
    (fun i _ => ftsBound_chain index coord.val (child output coord).val i.val _ _ _ coord.isLt
      (child output coord).isLt i.isLt (by have := wordDigit_le_four (rank output coord) i; omega))).bind'
    (l := 8) (fun ends hends => ?_) ?_
  · refine (ftsBound_leafHash index coord.val (child output coord).val ends coord.isLt (child output coord).isLt
      (by simpa using hends)).bind' (l := 6) (fun root _ => ?_) (by decide)
    refine ((Bound.foldlM_list (P := FtsQuery index) (List.finRange 6) _ (fun _ _ => True) (fun _ => 1) root
      trivial (fun i hi value _ => ?_)).mono (fun _ h => h) (fun _ _ => trivial)).bind' (l := 0)
      (fun _ _ => .pure _ 0 trivial) (by simp)
    have hi6 : i < 6 := by simpa using hi
    simp only [List.getElem_finRange, Fin.cast_mk]
    have hb := recover_heap_bounds i (child output coord).val hi6 (child output coord).isLt
    exact ftsBound_nodeHash index coord.val _ _ _ coord.isLt hb.1 hb.2
  · rw [← Fin.sum_univ_def, wordStep_count]
theorem ftsBound_recoverFts (sig : Signature) (output : HashOutput) :
    Bound (FtsQuery index) (fun _ => True) 140 (recoverFts sig index output) := by
  unfold recoverFts
  refine (Bound.mapM_list (P := FtsQuery index) (List.finRange 9) _ (fun _ => 15)
    (fun coord _ => ftsBound_recoverCoordinate index sig output coord)).bind' (l := 5)
    (fun pairs hpairs => ?_) (by simp)
  exact ftsBound_forestPk index pairs (by simpa using hpairs)
theorem chain_queries (coord selected t start count : Nat) (value : Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (ht : t < 6) (hend : start + count ≤ 4) :
    AllQueriesSatisfy (chain index coord selected t start count value) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_chain index coord selected t start count value hcoord hsel ht hend)
theorem leafHash_queries (coord selected : Nat) (ends : List Digest)
    (hcoord : coord < 9) (hsel : selected < 128) (hlen : ends.length = 6) :
    AllQueriesSatisfy (leafHash index coord selected ends) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_leafHash index coord selected ends hcoord hsel hlen)
theorem forestPk_queries (pairs : List (Digest × Digest)) (hlen : pairs.length = 9) :
    AllQueriesSatisfy (forestPk index pairs) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_forestPk index pairs hlen)
theorem buildChildF_queries (coord selected : Nat) (word : Rank) (coefs : List Digest) (hcoord : coord < 9)
    (hsel : selected < 128) :
    AllQueriesSatisfy (buildChildF index coord selected word coefs) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_buildChildF index coord selected word coefs hcoord hsel)
theorem buildCoordinateF_queries (coord : Coord) (selected : Child) (word : Rank) :
    AllQueriesSatisfy (buildCoordinateF index coord selected word) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_buildCoordinateF index coord selected word)
theorem forestRows_queries (output : HashOutput) :
    AllQueriesSatisfy (forestRows index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_forestRows index output)
theorem signForest_queries (output : HashOutput) :
    AllQueriesSatisfy (signForest index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_signForest index output)
theorem recoverCoordinate_queries (sig : Signature) (output : HashOutput) (coord : Coord) :
    AllQueriesSatisfy (recoverCoordinate sig index output coord) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_recoverCoordinate index sig output coord)
theorem recoverFts_queries (sig : Signature) (output : HashOutput) :
    AllQueriesSatisfy (recoverFts sig index output) (FtsQuery index) :=
  allQueriesSatisfy_of_bound (ftsBound_recoverFts index sig output)
end Programs
end ClaudeWCT.WCT9
