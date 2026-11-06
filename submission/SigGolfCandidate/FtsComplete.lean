import Mathlib.Data.Fin.Basic
import SigGolfCandidate.FtsMoment
set_option linter.all false

/-! # E8 stage 2: completeness of the FTS ground nodes

Every FTS node of heap `8..15` is a first-nonce search (`ftsNodeAt`) with cap `128 · 2^b`; on exhaustion it keeps the
last trial, whose top `b` bits may be set. The codec stores carrier bits there (`FtsPathOK`), so completeness needs
`FtsTreesOK`: every heap-`8..15` node of every FTS forest index passes its zero test.

* `ftsCheck` builds the nine coordinate trees of every forest index `< 2^31` (the node values do not depend on the
  selection or the words, so it builds them at child 0, rank 0) and tests their ground nodes;
  `eval_ftsCheck_true : evalWithAnswerFn answers ftsCheck = true → FtsTreesOK answers`.
* `Ev_ftsCheck_false`: from any cache with every FTS ground trial fresh (`AllFFresh`) the check fails with
  probability `≤ 2^-170` (per node `(1 - 2^-b)^(128·2^b) ≤ (3/4)^512`, 72 nodes per index, `2^31` indices; the
  cap-failure analogue of `FtsMoment.V_buildForest`, structured like U16b's `E_tree0`).
* `sign_ftsPathOK`: on `FtsTreesOK` the honest signature has `FtsPathOK`. -/

namespace ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.T3.Freshness (Avoids avoids_pure avoids_bind preserves avoidsQuery)
open SigGolfCandidate.T3.QuerySpace (queryHeader queryHeader_padded)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9 (Rank Child)
open ClaudeWCT.WCT9 (ftsNodeInputN ftsNodeHashN ftsNonceSearch ftsNodeAt ftsNodeG ftsZeroBits ftsZeroOk
  ftsNonceCap wctNodeHeader ftsStart)
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.TopMoment (Ev Ev_bind Ev_pure Ev_le_of_support Ev_publicQuery_fresh Ev_const_le)
open SigGolfCandidate.T3M (allQ_pure allQ_bind allQ_map allQ_foldlM allQ_mono)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-! ## The check -/

/-- Do the ground nodes (heaps `8..15`) of one coordinate tree pass their zero tests? -/
def ftsTreeOK (coord : Nat) (nodes : Array Digest) : Bool :=
  (List.range' 8 8).all fun heap => ftsZeroOk coord heap (nodes.getD heap 0)

/-- The child and rank at which `ftsCheck` builds a coordinate (the nodes do not depend on them). -/
def child0 : Child := ⟨0, by decide⟩
def rank0 : Rank := ⟨0, by decide⟩

/-- One FTS pair (`buildPair`'s two coordinate trees, previous pair root `st.2`), testing their ground nodes. -/
def ftsPairCheck (index pair : Nat) (st : Bool × PairRoot) : M (Bool × PairRoot) := do
  let a ← buildSharedCoordinate true index (2 * pair) child0 rank0 (fun _ => st.2)
  let b ← buildSharedCoordinate false index (2 * pair + 1) child0 rank0 (nodesPair a.1)
  pure (st.1 && ftsTreeOK (2 * pair) a.1 && ftsTreeOK (2 * pair + 1) b.1, (b.1.getD 2 0, b.1.getD 3 0))

/-- The nine coordinate trees of the FTS forest `index` (`buildForest`'s pad chain), testing their ground nodes. -/
def ftsForestCheck (index : Nat) : M Bool := do
  let s1 ← ftsPairCheck index 0 (true, ftsStart)
  let s2 ← ftsPairCheck index 1 s1
  let s3 ← ftsPairCheck index 2 s2
  let s4 ← ftsPairCheck index 3 s3
  let c ← buildSharedCoordinate false index 8 child0 rank0 (fun _ => s4.2)
  pure (s4.1 && ftsTreeOK 8 c.1)

def ftsCheckStep (acc : Bool) (index : Nat) : M Bool := do
  let ok ← ftsForestCheck index
  pure (acc && ok)

/-- The FTS forest indices (kept irreducible so that no elaboration step unfolds the `2^31`-element list). -/
@[irreducible] def ftsIndices : List Nat := List.range (2 ^ 31)

theorem mem_ftsIndices {index : Nat} : index ∈ ftsIndices ↔ index < 2 ^ 31 := by
  unfold ftsIndices; exact List.mem_range

theorem ftsIndices_nodup : ftsIndices.Nodup := by
  unfold ftsIndices; exact List.nodup_range

theorem ftsIndices_length : ftsIndices.length = 2 ^ 31 := by
  unfold ftsIndices; exact List.length_range

/-- E8 stage 2 completeness check: every FTS ground node of every forest index passes its zero test. -/
def ftsCheck : M Bool := ftsIndices.foldlM ftsCheckStep true

/-! ## `ftsCheck` accepts only on `FtsTreesOK` -/

section evals
open SigGolfCandidate.T3.Correctness
attribute [local irreducible] sharedNodes

theorem ftsTreeOK_at {coord : Nat} {nodes : Array Digest} (h : ftsTreeOK coord nodes = true) {heap : Nat}
    (h8 : 8 ≤ heap) (h16 : heap < 16) : ftsZeroOk coord heap (nodes.getD heap 0) = true := by
  unfold ftsTreeOK at h
  rw [List.all_eq_true] at h
  exact h heap (List.mem_range'_1.mpr ⟨h8, by omega⟩)

theorem eval_ftsPairCheck (answers : Answers) (index pair : Nat) (b : Bool) (prev : PairRoot) :
    evalWithAnswerFn answers (ftsPairCheck index pair (b, prev)) =
      (b && ftsTreeOK (2 * pair) (firstNodes answers index pair prev) &&
        ftsTreeOK (2 * pair + 1) (secondNodes answers index pair prev), expectedPairRoot answers index pair prev) := by
  simp only [ftsPairCheck, evalWithAnswerFn_bind, buildSharedCoordinate_result, evalWithAnswerFn_pure]
  rfl

theorem eval_ftsForestCheck_true (answers : Answers) (index : Nat)
    (h : evalWithAnswerFn answers (ftsForestCheck index) = true) :
    (∀ pair, pair < 4 →
      ftsTreeOK (2 * pair) (firstNodes answers index pair (forestPrev answers index pair)) = true ∧
      ftsTreeOK (2 * pair + 1) (secondNodes answers index pair (forestPrev answers index pair)) = true) ∧
    ftsTreeOK 8 (sharedNodes answers false index 8 (fun _ => forestPrev answers index 4)) = true := by
  simp only [ftsForestCheck, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_ftsPairCheck,
    buildSharedCoordinate_result, Bool.and_eq_true, Bool.true_and] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨fun pair hp => ?_, h8⟩
  interval_cases pair
  · exact ⟨h0, h1⟩
  · exact ⟨h2, h3⟩
  · exact ⟨h4, h5⟩
  · exact ⟨h6, h7⟩

theorem eval_ftsCheckFold_true (answers : Answers) :
    ∀ (L : List Nat) (acc : Bool), evalWithAnswerFn answers (L.foldlM ftsCheckStep acc) = true →
      acc = true ∧ ∀ index ∈ L, evalWithAnswerFn answers (ftsForestCheck index) = true := by
  intro L
  induction L with
  | nil => intro acc h; simpa using h
  | cons index L ih =>
      intro acc h
      rw [List.foldlM_cons, evalWithAnswerFn_bind] at h
      unfold ftsCheckStep at h
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h
      obtain ⟨h1, h2⟩ := ih _ h
      simp only [Bool.and_eq_true] at h1
      refine ⟨h1.1, fun i hi => ?_⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h1.2
      · exact h2 i hi

/-- **`ftsCheck` accepts only if every FTS ground node passes its zero test.** -/
theorem eval_ftsCheck_true (answers : Answers) (h : evalWithAnswerFn answers ftsCheck = true) :
    FtsTreesOK answers := by
  have hall := (eval_ftsCheckFold_true answers _ true h).2
  intro index hidx heap h8 h16
  obtain ⟨hp, hs⟩ := eval_ftsForestCheck_true answers index (hall index (mem_ftsIndices.mpr hidx))
  exact ⟨fun pair hpair => ⟨ftsTreeOK_at (hp pair hpair).1 h8 h16, ftsTreeOK_at (hp pair hpair).2 h8 h16⟩,
    ftsTreeOK_at hs h8 h16⟩

end evals

/-! ## Hash-only -/

section hashOnly
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_foldlM
  hashOnly_shortHash hashOnly_privatePair hashOnly_publicHash hashOnly_projHash)

theorem hoF_ftsHash (heap : Nat) (input : HashInput) : HashOnly (ClaudeWCT.WCT9.ftsHash heap input) := by
  unfold ClaudeWCT.WCT9.ftsHash
  split
  · unfold ClaudeWCT.WCT9.highHash
    exact hashOnly_bind (hashOnly_publicHash _) fun _ => hashOnly_pure _
  · exact hashOnly_shortHash _

theorem hoF_buildChildH (heap index coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    HashOnly (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs pad) := by
  have hc : ∀ i start count (v : Digest), HashOnly (ClaudeWCT.WCT9.chain index coord selected i start count v) :=
    fun _ _ _ _ => by
      unfold ClaudeWCT.WCT9.chain
      exact hashOnly_foldlM _ _ (fun _ _ => hashOnly_projHash _ _) _
  unfold ClaudeWCT.WCT9.buildChildH
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state i => ?_) _) fun state => ?_
  · exact hashOnly_bind (hc _ _ _ _) fun _ => hashOnly_bind (hc _ _ _ _) fun _ => hashOnly_pure _
  · exact hashOnly_bind (hoF_ftsHash _ _) fun _ => hashOnly_pure _

theorem hoF_ftsCoefs (index coord : Nat) : HashOnly (ClaudeWCT.WCT9.ftsCoefs index coord) := by
  unfold ClaudeWCT.WCT9.ftsCoefs ClaudeWCT.WCT9.ftsSeedPair
  exact hashOnly_foldlM _ _ (fun acc j => hashOnly_bind (hashOnly_privatePair _ _ _ _ _) fun _ => hashOnly_pure _) _

theorem hoF_ftsNonceSearch (coord index heap : Nat) (left right : Digest) :
    ∀ fuel n, HashOnly (ftsNonceSearch coord index heap left right fuel n) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n; unfold ftsNonceSearch ftsNodeHashN
      exact hashOnly_bind (hashOnly_shortHash _) fun _ => hashOnly_pure _
  | succ fuel ih =>
      intro n; unfold ftsNonceSearch
      refine hashOnly_bind (by unfold ftsNodeHashN; exact hashOnly_shortHash _) fun _ => ?_
      split
      · exact hashOnly_pure _
      · exact ih _

theorem hoF_sharedNode (first : Bool) (coord index heap : Nat) (pads : Nat → PairRoot) (left right : Digest) :
    HashOnly (sharedNode first coord index heap pads left right) := by
  unfold sharedNode
  split
  · unfold sharedOuterHash
    split
    · exact hashOnly_shortHash _
    · unfold ClaudeWCT.WCT9.highHash
      exact hashOnly_bind (hashOnly_publicHash _) fun _ => hashOnly_pure _
  · split
    · split
      · unfold ClaudeWCT.WCT9.highHash
        exact hashOnly_bind (hashOnly_publicHash _) fun _ => hashOnly_pure _
      · exact hashOnly_shortHash _
    · unfold ftsNodeG ftsNodeAt
      refine hashOnly_map _ ?_
      split
      · exact hashOnly_map _ (by unfold ClaudeWCT.WCT9.wctNodeHashH; exact hoF_ftsHash _ _)
      · exact hoF_ftsNonceSearch _ _ _ _ _ _ _

theorem hoF_buildSharedCoordinate (first : Bool) (index coord : Nat) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) : HashOnly (buildSharedCoordinate first index coord selected word pads) := by
  unfold buildSharedCoordinate sharedHeap
  exact hashOnly_bind (hoF_ftsCoefs _ _) fun _ =>
    hashOnly_bind (hashOnly_foldlM _ _ (fun _ _ => hashOnly_bind (hoF_buildChildH _ _ _ _ _ _ _) fun _ =>
      hashOnly_pure _) _) fun _ =>
    hashOnly_bind (hashOnly_foldlM _ _ (fun _ _ => hashOnly_bind (hoF_sharedNode _ _ _ _ _ _ _) fun _ =>
      hashOnly_pure _) _) fun _ => hashOnly_pure _

theorem hashOnly_ftsPairCheck (index pair : Nat) (st : Bool × PairRoot) : HashOnly (ftsPairCheck index pair st) := by
  unfold ftsPairCheck
  exact hashOnly_bind (hoF_buildSharedCoordinate _ _ _ _ _ _) fun _ =>
    hashOnly_bind (hoF_buildSharedCoordinate _ _ _ _ _ _) fun _ => hashOnly_pure _

theorem hashOnly_ftsForestCheck (index : Nat) : HashOnly (ftsForestCheck index) := by
  unfold ftsForestCheck
  exact hashOnly_bind (hashOnly_ftsPairCheck _ _ _) fun _ => hashOnly_bind (hashOnly_ftsPairCheck _ _ _) fun _ =>
    hashOnly_bind (hashOnly_ftsPairCheck _ _ _) fun _ => hashOnly_bind (hashOnly_ftsPairCheck _ _ _) fun _ =>
    hashOnly_bind (hoF_buildSharedCoordinate _ _ _ _ _ _) fun _ => hashOnly_pure _

theorem hashOnly_ftsCheckFold (L : List Nat) (acc : Bool) : HashOnly (L.foldlM ftsCheckStep acc) :=
  hashOnly_foldlM L ftsCheckStep
    (fun _ index => hashOnly_bind (hashOnly_ftsForestCheck index) fun _ => hashOnly_pure _) acc

theorem hashOnly_ftsCheck : HashOnly ftsCheck := by
  unfold ftsCheck
  exact hashOnly_ftsCheckFold _ _

end hashOnly

/-! ## Other forest indices: the check of index `i` avoids every ground trial of index `j ≠ i` -/

section cross
variable {secret : BitVec 256} {i j : Nat} {S : Nat → Nat → Prop}

theorem nodeHdr_ne_cross (hS : GroundSet j S) (hi : i < 2 ^ 31) (hij : i ≠ j) {coord heap : Nat}
    (hc : coord < 9) (hh : heap < 2 ^ 64) : ∀ c x, S c x → wctNodeHeader coord i heap ≠ wctNodeHeader c j x := by
  intro c x hs he
  have hp := hS c x hs
  obtain ⟨-, e2, -⟩ := ClaudeWCT.WCT9.wctNodeHeader_injective hc hi hh hp.1 hp.2.1
    (by have := hp.2.2.2; omega) he
  exact hij e2

theorem xF_chain (coord selected k start count : Nat) (value : Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.chain i coord selected k start count value) (NotF secret j S) := by
  unfold ClaudeWCT.WCT9.chain
  exact allQ_foldlM _ _ (fun v step => notF_projHash _
    (ftsChainInputW_header (S := fun _ _ => False) (fun _ _ h => h.elim) coord selected k step v)
    (fun c x _ he => ClaudeWCT.WCT9.wctNodeHeader_ne_ftsChainHeaderP c j x _ _ _ _ _ _ he.symm)) _

theorem xF_buildChildH (hS : GroundSet j S) (heap coord selected : Nat) (word : Rank) (coefs : List Digest)
    (pad : Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.buildChildH heap i coord selected word coefs pad) (NotF secret j S) := by
  unfold ClaudeWCT.WCT9.buildChildH
  refine allQ_bind (allQ_foldlM _ _ (fun st k => ?_) _) fun st => ?_
  · exact allQ_bind (xF_chain _ _ _ _ _ _) fun _ => allQ_bind (xF_chain _ _ _ _ _ _) fun _ => allQ_pure _
  · refine allQ_bind ?_ fun _ => allQ_pure _
    unfold ClaudeWCT.WCT9.leafHashH
    refine notF_ftsHash heap (hdr := ClaudeWCT.WCT9.ftsLeafHeader i coord selected) ?_
      (fun c x hs he => ClaudeWCT.WCT9.ftsLeafHeader_ne_wctNodeHeader i coord selected (hS c x hs).1 j x
        (by have := (hS c x hs).2.2; omega) he)
    unfold ClaudeWCT.WCT9.leafInputP
    simpa only [List.append_assoc] using
      queryHeader_padded (bytesLE 16 (st.1.getD 0 0)) (bytesLE 16 pad ++ (st.1.drop 1).flatMap (bytesLE 16))
        (bytesLE_length ..) (ClaudeWCT.WCT9.ftsLeafHeader i coord selected)

theorem xF_ftsCoefs (hS : GroundSet j S) (coord : Nat) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.ftsCoefs i coord) (NotF secret j S) := by
  unfold ClaudeWCT.WCT9.ftsCoefs
  refine allQ_foldlM _ _ (fun acc k => ?_) _
  unfold ClaudeWCT.WCT9.ftsSeedPair privatePair privateHash
  exact allQ_bind ((allQueriesSatisfy_query_iff _ _).mpr
    (notF_private (fun c x h => (hS c x h).1) 8 coord i 0 k (by decide))) fun _ => allQ_pure _

theorem xF_sharedNode (hS : GroundSet j S) (hi : i < 2 ^ 31) (hij : i ≠ j) (first : Bool) (coord heap : Nat)
    (pads : Nat → PairRoot) (left right : Digest) (hc : coord < 9) (hh : heap < 128) :
    AllQueriesSatisfy (sharedNode first coord i heap pads left right) (NotF secret j S) := by
  have hne := nodeHdr_ne_cross hS hi hij hc (show heap < 2 ^ 64 by omega)
  unfold sharedNode
  split
  · unfold sharedOuterHash
    split
    · exact notF_shortHash (wctTopInput_header ..) hne
    · exact notF_highHash (wctTopInput_header ..) hne
  · split
    · split
      · exact notF_highHash (wctTopInput_header ..) hne
      · exact notF_shortHash (wctTopInput_header ..) hne
    · refine ClaudeWCT.WCT9.allQ_ftsNodeG _ _ _ _ _ ?_ (fun n _ => ?_)
      · unfold ClaudeWCT.WCT9.wctNodeHashH
        exact notF_ftsHash heap (nodeH_header ..) hne
      · unfold ftsNodeHashN
        exact notF_shortHash (fTrial_header coord i heap n left right) hne

theorem allQ_foldlM_mem {α β : Type} {P : Spec.Domain → Prop} (f : α → β → M α) :
    ∀ (l : List β) (init : α), (∀ a, ∀ b ∈ l, AllQueriesSatisfy (f a b) P) →
      AllQueriesSatisfy (l.foldlM f init) P
  | [], init, _ => by rw [List.foldlM_nil]; exact allQ_pure _
  | b :: l, init, h => by
      rw [List.foldlM_cons]
      exact allQ_bind (h init b (List.mem_cons_self ..)) fun a =>
        allQ_foldlM_mem f l a (fun a' b' hb' => h a' b' (List.mem_cons_of_mem _ hb'))

theorem xF_buildSharedCoordinate (hS : GroundSet j S) (hi : i < 2 ^ 31) (hij : i ≠ j) (first : Bool)
    (coord : Nat) (hc : coord < 9) (selected : Child) (word : Rank) (pads : Nat → PairRoot) :
    AllQueriesSatisfy (buildSharedCoordinate first i coord selected word pads) (NotF secret j S) := by
  unfold buildSharedCoordinate sharedHeap
  refine allQ_bind (xF_ftsCoefs hS coord) fun coefs => allQ_bind
    (allQ_foldlM _ _ (fun _ _ => allQ_bind (xF_buildChildH hS _ _ _ _ _ _) fun _ => allQ_pure _) _) fun _ =>
    allQ_bind (allQ_foldlM_mem _ _ _ (fun nodes heap hm => ?_)) fun _ => allQ_pure _
  have hh : heap < 128 := by
    rw [List.mem_reverse, List.mem_range'_1] at hm
    cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;> omega
  exact allQ_bind (xF_sharedNode hS hi hij first coord heap pads _ _ hc hh) fun _ => allQ_pure _

theorem xF_ftsPairCheck (hi : i < 2 ^ 31) (hj : j < 2 ^ 31) (hij : i ≠ j) (pair : Nat) (hp : pair < 4)
    (st : Bool × PairRoot) : AllQueriesSatisfy (ftsPairCheck i pair st) (NotF secret j (Above 0)) := by
  unfold ftsPairCheck
  exact allQ_bind (xF_buildSharedCoordinate (groundSet_above 0 hj) hi hij _ _ (by omega) _ _ _) fun _ =>
    allQ_bind (xF_buildSharedCoordinate (groundSet_above 0 hj) hi hij _ _ (by omega) _ _ _) fun _ => allQ_pure _

theorem xF_ftsForestCheck (hi : i < 2 ^ 31) (hj : j < 2 ^ 31) (hij : i ≠ j) :
    AllQueriesSatisfy (ftsForestCheck i) (NotF secret j (Above 0)) := by
  unfold ftsForestCheck
  exact allQ_bind (xF_ftsPairCheck hi hj hij 0 (by decide) _) fun _ =>
    allQ_bind (xF_ftsPairCheck hi hj hij 1 (by decide) _) fun _ =>
    allQ_bind (xF_ftsPairCheck hi hj hij 2 (by decide) _) fun _ =>
    allQ_bind (xF_ftsPairCheck hi hj hij 3 (by decide) _) fun _ =>
    allQ_bind (xF_buildSharedCoordinate (groundSet_above 0 hj) hi hij _ _ (by decide) _ _ _) fun _ => allQ_pure _

end cross

/-! ## Cap failure of the ground nodes -/

/-- Probability that one FTS ground search with `b` zero bits exhausts its cap `128 · 2^b`. -/
noncomputable def fcap (b : Nat) : ℝ≥0∞ := (1 - ((2 : ℝ≥0∞) ^ b)⁻¹) ^ (128 * 2 ^ b)

/-- `(81/256)^128 = (3/4)^512`: a bound on every FTS ground cap failure (`b ∈ {1, 2}`). -/
noncomputable def cF : ℝ≥0∞ := ENNReal.ofReal ((81 / 256 : ℝ) ^ 128)

theorem fcap_le (coord : Nat) : fcap (ftsZeroBits coord 8) ≤ cF := by
  have hb : ftsZeroBits coord 8 = 1 ∨ ftsZeroBits coord 8 = 2 := by
    unfold ftsZeroBits; split_ifs <;> simp_all
  have key : ∀ b : Nat, fcap b = ENNReal.ofReal ((1 - 1 / 2 ^ b : ℝ) ^ (128 * 2 ^ b)) := by
    intro b
    unfold fcap
    have hx : (0 : ℝ) ≤ 1 / 2 ^ b := by positivity
    have hx1 : 1 / 2 ^ b ≤ (1 : ℝ) := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    rw [ENNReal.ofReal_pow (show (0 : ℝ) ≤ 1 - 1 / 2 ^ b by linarith), ENNReal.ofReal_sub _ hx,
      ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 ^ b by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat, one_div]
  unfold cF
  rw [key]
  apply ENNReal.ofReal_le_ofReal
  rcases hb with h | h <;> rw [h]
  · rw [show 128 * 2 ^ 1 = 2 * 128 from rfl, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) 128
  · rw [show 128 * 2 ^ 2 = 4 * 128 from rfl, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) 128

theorem capF_step (p B : ℝ≥0∞) (hp : p ≤ 1) (k : Nat) :
    p * B + (1 - p) * (B + (1 - p) ^ (k + 1)) ≤ B + (1 - p) ^ (k + 1 + 1) := by
  rw [mul_add, ← add_assoc, ← add_mul, add_tsub_cancel_of_le hp, one_mul, ← pow_succ']

theorem capF_tail (p B : ℝ≥0∞) (hp : p ≤ 1) : p * B + (1 - p) * 1 ≤ B + (1 - p) ^ (0 + 1) := by
  rw [mul_one, zero_add, pow_one]
  exact add_le_add (mul_le_of_le_one_left (by positivity) hp) le_rfl

theorem ftsZeroOk_off {coord heap : Nat} (h : ¬ (8 ≤ heap ∧ heap < 16)) (v : Digest) :
    ftsZeroOk coord heap v = true := by
  unfold ftsZeroOk
  rw [ClaudeWCT.WCT9.ftsZeroBits_off h]
  have := v.isLt
  simp only [Nat.sub_zero, beq_iff_eq]
  exact Nat.div_eq_of_lt this

theorem ftsZeroOk_ground {coord heap : Nat} (h8 : 8 ≤ heap) (h16 : heap < 16) (v : Digest) :
    ftsZeroOk coord heap v = ftsZeroOk coord 8 v := by
  unfold ftsZeroOk
  rw [ftsZeroBits_ground ⟨h8, h16⟩]

/-- Value-weighted FTS nonce-search bound, fuel-indexed (copy of U16b's `Ev_lowerNonceSearch_fuel`). -/
theorem Ev_ftsNonceSearch_fuel {β : Type} (secret : BitVec 256) (coord index heap : Nat) (left right : Digest)
    (next : Nat × Digest → M β) (F : β × RCache → ℝ≥0∞) (G : RCache → Prop) (w : Digest → ℝ≥0∞) (b : Nat → ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (fTrial coord index heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      Ev secret (next (k, fVal answer)) (cache.cacheQuery (fTrial coord index heap k left right) answer) F ≤
        w (fVal answer))
    (hstep : ∀ k, expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if ftsZeroOk coord heap (fVal answer) then w (fVal answer) else b k) ≤ b (k + 1))
    (htail : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun answer => w (fVal answer)) ≤ b 0) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (fTrial coord index heap k left right) = none) →
      Ev secret (ftsNonceSearch coord index heap left right fuel n >>= next) cache F ≤ b fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [ftsNonceSearch_zero_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      exact (expectedValue_mono _ fun answer => hnext cache hg n answer).trans htail
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [ftsNonceSearch_succ_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      refine le_trans (expectedValue_mono _ fun answer => ?_) (hstep fuel)
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : fTrial coord index heap k left right ≠ fTrial coord index heap n left right := by
          intro he
          have := fTrial_injective coord index heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))

/-- **One FTS ground node**: if every continuation after a node passing its zero test is bounded by `B` (and
`F ≤ 1`), the node search plus continuation is bounded by `B + fcap b` (cap-failure analogue of `V_fnode`). -/
theorem E_fnode {β : Type} (secret : BitVec 256) (coord index heap : Nat) (hp : FP coord index heap)
    (left right : Digest) (next : Digest → M β) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1)
    (S : Nat → Nat → Prop) (hS : GroundSet index S) (B : ℝ≥0∞)
    (hnext : ∀ v cache, ftsZeroOk coord heap v = true →
      FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) cache → Ev secret (next v) cache F ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) (hin : S coord heap) :
    Ev secret (ftsNodeG coord index heap left right >>= next) cache F ≤ B + fcap (ftsZeroBits coord heap) := by
  have hg : 8 ≤ heap ∧ heap < 16 := ⟨hp.2.2.1, hp.2.2.2⟩
  have hpres : ∀ (c : RCache) k ans, FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) c →
      FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap))
        (c.cacheQuery (fTrial coord index heap k left right) ans) := by
    intro c k ans hc x y hxy n l r
    exact (QueryCache.cacheQuery_of_ne (cache := c) ans
      (fTrial_ne hp (hS x y hxy.1) hxy.2 k n left right l r)).trans (hc x y hxy n l r)
  have hb : ftsZeroBits coord heap ≠ 0 := by
    simp only [ftsZeroBits, if_pos hg]; split <;> omega
  unfold ftsNodeG
  rw [bind_map_left]
  unfold ftsNodeAt
  rw [if_neg hb]
  have hcap : ftsNonceCap coord heap - 1 < 2 ^ 64 := by
    have := ftsZeroBits_le2 coord heap
    unfold ftsNonceCap
    have : 2 ^ ftsZeroBits coord heap ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hcap1 : ftsNonceCap coord heap - 1 + 1 = 128 * 2 ^ ftsZeroBits coord heap := by
    unfold ftsNonceCap; have : 0 < 2 ^ ftsZeroBits coord heap := by positivity
    omega
  set p : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ ftsZeroBits coord heap)⁻¹ with hpdef
  have hp1 : p ≤ 1 := by
    rw [hpdef, ← prob_fAccept coord heap]; exact probEvent_le_one
  have hres := Ev_ftsNonceSearch_fuel secret coord index heap left right (fun x : Nat × Digest => next x.2) F
    (FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)))
    (fun v => if ftsZeroOk coord heap v then B else 1)
    (fun k => B + (1 - p) ^ (k + 1)) (fun c hc k a => hpres c k a hc) ?_ ?_ ?_
    (ftsNonceCap coord heap - 1) 0 (by omega) cache
    (hfresh.mono (fun x y hxy => hxy.1)) (fun k _ _ => hfresh coord heap hin k left right)
  · refine hres.trans (le_of_eq ?_)
    unfold fcap
    rw [hcap1]
  · intro σ hσ k ans
    dsimp only
    split
    · rename_i hok
      exact hnext _ _ hok (hpres σ k ans hσ)
    · exact Ev_le_of_support secret _ _ (fun r _ => hF r)
  · intro k
    have he : (fun answer => if ftsZeroOk coord heap (fVal answer) = true then
        (if ftsZeroOk coord heap (fVal answer) = true then B else 1)
        else B + (1 - p) ^ (k + 1)) =
        fun a => if ftsZeroOk coord heap (fVal a) = true then B else B + (1 - p) ^ (k + 1) := by
      funext a; split <;> simp_all
    rw [he, expectedValue_uniform_ite_F (fun a => ftsZeroOk coord heap (fVal a) = true), prob_fAccept]
    exact capF_step p B hp1 k
  · have he : (fun answer => if ftsZeroOk coord heap (fVal answer) = true then B
        else (1 : ℝ≥0∞)) = fun a => if ftsZeroOk coord heap (fVal a) = true then B else 1 := rfl
    rw [he, expectedValue_uniform_ite_F (fun a => ftsZeroOk coord heap (fVal a) = true), prob_fAccept]
    exact capF_tail p B hp1

/-- Per-heap cap failure of a shared node (`0` off the ground). -/
noncomputable def gcap (coord heap : Nat) : ℝ≥0∞ := if 8 ≤ heap ∧ heap < 16 then fcap (ftsZeroBits coord 8) else 0

/-- **One shared node**: `B + gcap`. -/
theorem E_snode {β : Type} (secret : BitVec 256) (first : Bool) (coord index heap : Nat) (hc : coord < 9)
    (hidx : index < 2 ^ 31) (h2 : 2 ≤ heap) (hh : heap < 128) (pads : Nat → PairRoot) (left right : Digest)
    (next : Digest → M β) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1)
    (S : Nat → Nat → Prop) (hS : GroundSet index S) (B : ℝ≥0∞)
    (hnext : ∀ v cache, ftsZeroOk coord heap v = true →
      FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) cache → Ev secret (next v) cache F ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) (hin : 8 ≤ heap ∧ heap < 16 → S coord heap) :
    Ev secret (sharedNode first coord index heap pads left right >>= next) cache F ≤ B + gcap coord heap := by
  unfold gcap
  by_cases hg : 8 ≤ heap ∧ heap < 16
  · have e : sharedNode first coord index heap pads left right = ftsNodeG coord index heap left right := by
      simp only [sharedNode, if_neg (show ¬ heap < 4 by omega), if_neg (show ¬ heap < 8 by omega)]
    rw [e, if_pos hg, ← ftsZeroBits_ground (coord := coord) hg]
    exact E_fnode secret coord index heap ⟨hc, hidx, hg⟩ left right next F hF S hS B hnext cache hfresh (hin hg)
  · rw [if_neg hg, add_zero, Ev_bind]
    refine Ev_le_of_support secret _ cache (fun r hr => hnext r.1 r.2 (ftsZeroOk_off hg _) ?_)
    exact (freshF_preserved secret (notF_sharedNode_plain hS first coord heap pads left right hc hh hg) cache hfresh
      r hr).mono fun x y hxy => hxy.1

/-- The ground nodes of the heaps `D` pass their zero tests. -/
def OKAt (coord : Nat) (D : Nat → Prop) (nodes : Array Digest) : Prop :=
  ∀ h, D h → 8 ≤ h → h < 16 → ftsZeroOk coord h (nodes.getD h 0) = true

/-- **A list of shared heap steps**: `B + Σ gcap`, the continuation seeing every ground node of the list pass. -/
theorem E_heapList {β : Type} (secret : BitVec 256) (first : Bool) (index coord : Nat) (hc : coord < 9)
    (hidx : index < 2 ^ 31) (pads : Nat → PairRoot) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1) :
    ∀ (l : List Nat), (∀ h ∈ l, 2 ≤ h ∧ h < 128) → l.Nodup →
    ∀ (S : Nat → Nat → Prop) (D : Nat → Prop) (init : Array Digest) (next : Array Digest → M β) (B : ℝ≥0∞),
      GroundSet index S → (∀ h ∈ l, 8 ≤ h ∧ h < 16 → S coord h) → (∀ h ∈ l, ¬ D h) → 16 ≤ init.size →
      OKAt coord D init →
      (∀ a cache, OKAt coord (fun h => D h ∨ h ∈ l) a →
        FreshF index (fun c' x => S c' x ∧ ¬ (c' = coord ∧ x ∈ l)) cache → Ev secret (next a) cache F ≤ B) →
      ∀ cache, FreshF index S cache →
        Ev secret ((l.foldlM (heapStep first index coord pads) init) >>= next) cache F ≤
          B + (l.map (gcap coord)).sum := by
  intro l
  induction l with
  | nil =>
      intro _ _ S D init next B _ _ _ _ hok hnext cache hfresh
      simp only [List.foldlM_nil, pure_bind, List.map_nil, List.sum_nil, add_zero]
      exact hnext init cache (fun h hd => hok h (by simpa using hd)) (hfresh.mono fun x y h => h.1)
  | cons h t ih =>
      intro hl hnd S D init next B hS hin hD hsize hok hnext cache hfresh
      have hnd' := List.nodup_cons.mp hnd
      rw [List.foldlM_cons]
      unfold heapStep
      simp only [bind_assoc, pure_bind]
      have hh := hl h (List.mem_cons_self ..)
      refine le_trans (E_snode secret first coord index h hc hidx hh.1 hh.2 pads _ _ _ F hF S hS
        (B + (t.map (gcap coord)).sum) (fun v cache' hv hc' => ?_) cache hfresh
        (hin h (List.mem_cons_self ..))) (le_of_eq ?_)
      · refine ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hnd'.2
          (fun c' x => S c' x ∧ ¬ (c' = coord ∧ x = h)) (fun x => D x ∨ x = h) (init.set! h v) next B
          (fun c' x hx => hS c' x hx.1)
          (fun x hx hg => ⟨hin x (List.mem_cons_of_mem _ hx) hg, fun he => hnd'.1 (he.2 ▸ hx)⟩)
          (fun x hx hd => by
            rcases hd with hd | rfl
            · exact hD x (List.mem_cons_of_mem _ hx) hd
            · exact hnd'.1 hx)
          (by rw [Array.size_set!]; exact hsize)
          (fun x hx h8 h16 => ?_)
          (fun a cache'' hok' hc'' => hnext a cache''
            (fun x hx h8 h16 => hok' x (by
              rcases hx with hx | hx
              · exact Or.inl (Or.inl hx)
              · rcases List.mem_cons.mp hx with rfl | hx
                · exact Or.inl (Or.inr rfl)
                · exact Or.inr hx) h8 h16)
            (hc''.mono fun c' x hx =>
              ⟨⟨hx.1, fun he => hx.2 ⟨he.1, by rw [he.2]; exact List.mem_cons_self ..⟩⟩,
                fun he => hx.2 ⟨he.1, List.mem_cons_of_mem _ he.2⟩⟩)) cache' hc'
        rcases hx with hd | rfl
        · have hxh : h ≠ x := fun he => hD h (List.mem_cons_self ..) (he ▸ hd)
          rw [ClaudeWCT.WCT9.getD_set_other init h x v hxh]
          exact hok x hd h8 h16
        · rw [ClaudeWCT.WCT9.getD_set_self init _ v (by omega)]
          exact hv
      · rw [List.map_cons, List.sum_cons]; ring

theorem heapList_sum (coord a m : Nat) (ham : a + m = 8) :
    (((List.range' a (m + (8 + 112))).reverse).map (gcap coord)).sum = 8 * fcap (ftsZeroBits coord 8) := by
  rw [← List.range'_append_1 (s := a) (m := m) (n := 8 + 112), ham,
    ← List.range'_append_1 (s := 8) (m := 8) (n := 112), List.reverse_append,
    List.reverse_append, List.map_append, List.map_append, List.sum_append, List.sum_append]
  have z1 : ((List.range' (8 + 8) 112).reverse.map (gcap coord)).sum = 0 := by
    rw [List.map_congr_left (g := fun _ => (0 : ℝ≥0∞)) (fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx
      unfold gcap; rw [if_neg (by omega)])]
    simp
  have z3 : ((List.range' a m).reverse.map (gcap coord)).sum = 0 := by
    rw [List.map_congr_left (g := fun _ => (0 : ℝ≥0∞)) (fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx
      unfold gcap; rw [if_neg (by omega)])]
    simp
  have z2 : ((List.range' 8 8).reverse.map (gcap coord)).sum = 8 * fcap (ftsZeroBits coord 8) := by
    rw [List.map_congr_left (g := fun _ => fcap (ftsZeroBits coord 8)) (fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx
      unfold gcap; rw [if_pos (by omega)])]
    simp only [List.map_const', List.sum_replicate, List.length_reverse, List.length_range', nsmul_eq_mul]
    norm_num
  rw [z1, z2, z3, zero_add, add_zero]

/-- **The shared heap**: `B + 8 · fcap`, the continuation seeing `ftsTreeOK`. -/
theorem E_sharedHeap {β : Type} (secret : BitVec 256) (first : Bool) (index coord : Nat) (hc : coord < 9)
    (hidx : index < 2 ^ 31) (pads : Nat → PairRoot) (leaves : List Digest) (F : β × RCache → ℝ≥0∞)
    (hF : ∀ r, F r ≤ 1) (S : Nat → Nat → Prop) (hS : GroundSet index S) (hin : ∀ h, 8 ≤ h ∧ h < 16 → S coord h)
    (next : Array Digest → M β) (B : ℝ≥0∞)
    (hnext : ∀ a cache, ftsTreeOK coord a = true → FreshF index (fun c' x => S c' x ∧ c' ≠ coord) cache →
      Ev secret (next a) cache F ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    Ev secret (sharedHeap first index coord pads leaves >>= next) cache F ≤ B + 8 * fcap (ftsZeroBits coord 8) := by
  have key : ∀ (a m : Nat), a + m = 8 → 2 ≤ a →
      Ev secret (((List.range' a (m + (8 + 112))).reverse.foldlM (heapStep first index coord pads)
        ((List.replicate 128 (0 : Digest) ++ leaves).toArray)) >>= next) cache F ≤
        B + 8 * fcap (ftsZeroBits coord 8) := by
    intro a m ham ha
    have hmem : ∀ x, x ∈ (List.range' a (m + (8 + 112))).reverse ↔ a ≤ x ∧ x < 128 := by
      intro x; rw [List.mem_reverse, List.mem_range'_1]; omega
    rw [← heapList_sum coord a m ham]
    refine E_heapList secret first index coord hc hidx pads F hF _
      (fun x hx => by have := (hmem x).mp hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..))
      S (fun _ => False) _ next B hS (fun x _ hg => hin x hg) (fun _ _ h => h)
      (show 16 ≤ (List.replicate 128 (0 : Digest) ++ leaves).length by simp only [List.length_append, List.length_replicate]; omega)
      (fun _ h => h.elim)
      (fun nodes c hok hc' => hnext nodes c ?_ ?_) cache hfresh
    · unfold ftsTreeOK
      rw [List.all_eq_true]
      intro x hx
      rw [List.mem_range'_1] at hx
      exact hok x (Or.inr ((hmem x).mpr ⟨by omega, by omega⟩)) hx.1 (by omega)
    · exact hc'.mono fun c' x hx => ⟨hx.1, fun he => hx.2 he.1⟩
  unfold sharedHeap
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (126 : Nat) = 6 + (8 + 112) from rfl]
    exact key 2 6 rfl le_rfl
  · simp only [↓reduceIte]
    rw [show (124 : Nat) = 4 + (8 + 112) from rfl]
    exact key 4 4 rfl (by omega)

/-- **One coordinate tree**: `B + 8 · cF`, the continuation seeing `ftsTreeOK`. -/
theorem E_coord {β : Type} (secret : BitVec 256) (first : Bool) (index coord : Nat) (hc : coord < 9)
    (hidx : index < 2 ^ 31) (selected : Child) (word : Rank) (pads : Nat → PairRoot)
    (S : Nat → Nat → Prop) (hS : GroundSet index S) (hin : ∀ h, 8 ≤ h ∧ h < 16 → S coord h)
    (next : Array Digest × List Digest → M β) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1) (B : ℝ≥0∞)
    (hnext : ∀ a cache, ftsTreeOK coord a.1 = true → FreshF index (fun c' x => S c' x ∧ c' ≠ coord) cache →
      Ev secret (next a) cache F ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    Ev secret (buildSharedCoordinate first index coord selected word pads >>= next) cache F ≤ B + 8 * cF := by
  refine le_trans ?_ (add_le_add le_rfl (mul_le_mul' le_rfl (fcap_le coord)))
  unfold buildSharedCoordinate
  simp only [bind_assoc]
  rw [Ev_bind]
  refine Ev_le_of_support secret _ cache (fun r1 hr1 => ?_)
  have h1 := freshF_preserved secret (notF_ftsCoefs hS coord) cache hfresh r1 hr1
  try dsimp only
  rw [Ev_bind]
  refine Ev_le_of_support secret _ r1.2 (fun r2 hr2 => ?_)
  have h2 := freshF_preserved secret (notF_children hS first coord word selected pads r1.1) r1.2 h1 r2 hr2
  try dsimp only
  exact E_sharedHeap secret first index coord hc hidx pads r2.1.1 F hF S hS hin _ B
    (fun nodes c3 hok h3 => by simpa only [pure_bind] using hnext (nodes, r2.1.2) c3 hok h3) r2.2 h2

/-- **One FTS pair**: `B + 16 · cF`; the continuation sees the incoming flag kept. -/
theorem E_pairCheck {β : Type} (secret : BitVec 256) (index pair : Nat) (hidx : index < 2 ^ 31) (hp : pair < 4)
    (st : Bool × PairRoot) (next : Bool × PairRoot → M β) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1)
    (B : ℝ≥0∞) (hnext : ∀ r cache, r.1 = st.1 → FreshF index (Above (2 * pair + 2)) cache →
      Ev secret (next r) cache F ≤ B)
    (cache : RCache) (hfresh : FreshF index (Above (2 * pair)) cache) :
    Ev secret (ftsPairCheck index pair st >>= next) cache F ≤ B + 16 * cF := by
  unfold ftsPairCheck
  simp only [bind_assoc, pure_bind]
  refine le_trans (E_coord secret true index (2 * pair) (by omega) hidx child0 rank0 (fun _ => st.2)
    (Above (2 * pair)) (groundSet_above _ hidx) (fun h hh => ⟨le_rfl, by omega, hh⟩) _ F hF (B + 8 * cF)
    (fun a c1 hok1 h1 => ?_) cache hfresh) (le_of_eq (by ring))
  refine E_coord secret false index (2 * pair + 1) (by omega) hidx child0 rank0 (nodesPair a.1)
    (Above (2 * pair + 1)) (groundSet_above _ hidx) (fun h hh => ⟨le_rfl, by omega, hh⟩) _ F hF B
    (fun b c2 hok2 h2 => ?_) c1
    (h1.mono fun c' x hx => ⟨⟨by have := hx.1; omega, hx.2.1, hx.2.2⟩, by have := hx.1; omega⟩)
  exact hnext _ c2 (by simp [hok1, hok2])
    (h2.mono fun c' x hx => ⟨⟨by have := hx.1; omega, hx.2.1, hx.2.2⟩, by have := hx.1; omega⟩)

/-- **One FTS forest**: `Pr[ftsForestCheck = false] ≤ 72 · cF`, its ground trials fresh. -/
theorem E_forestCheck (secret : BitVec 256) (index : Nat) (hidx : index < 2 ^ 31) (cache : RCache)
    (hfresh : FreshF index (Above 0) cache) :
    Ev secret (ftsForestCheck index) cache (fun r => if r.1 then 0 else 1) ≤ 72 * cF := by
  have hF : ∀ r : Bool × RCache, (if r.1 then (0 : ℝ≥0∞) else 1) ≤ 1 := fun r => by split <;> simp
  unfold ftsForestCheck
  refine le_trans (E_pairCheck secret index 0 hidx (by decide) _ _ _ hF (8 * cF + 16 * cF + 16 * cF + 16 * cF)
    (fun s1 c1 hs1 h1 => ?_) cache hfresh) (le_of_eq (by ring))
  refine le_trans (E_pairCheck secret index 1 hidx (by decide) _ _ _ hF (8 * cF + 16 * cF + 16 * cF)
    (fun s2 c2 hs2 h2 => ?_) c1 h1) le_rfl
  refine le_trans (E_pairCheck secret index 2 hidx (by decide) _ _ _ hF (8 * cF + 16 * cF)
    (fun s3 c3 hs3 h3 => ?_) c2 h2) le_rfl
  refine le_trans (E_pairCheck secret index 3 hidx (by decide) _ _ _ hF (8 * cF)
    (fun s4 c4 hs4 h4 => ?_) c3 h3) le_rfl
  refine le_trans (E_coord secret false index 8 (by decide) hidx child0 rank0 (fun _ => s4.2) (Above 8)
    (groundSet_above _ hidx) (fun h hh => ⟨le_rfl, by omega, hh⟩) _ _ hF 0 (fun a c5 hok _ => ?_) c4 h4)
    (le_of_eq (zero_add _))
  rw [Ev_pure]
  simp [hs4, hs3, hs2, hs1, hok]

/-- **The fold of `ftsCheck`**: `E[1_{false}] ≤ 1_{¬acc} + |L| · 72 · cF` from a cache where the ground trials of
the remaining indices are fresh. -/
theorem E_ftsCheckFold (secret : BitVec 256) :
    ∀ (L : List Nat) (acc : Bool) (cache : RCache), L.Nodup →
      (∀ index ∈ L, index < 2 ^ 31 ∧ FreshF index (Above 0) cache) →
      Ev secret (L.foldlM ftsCheckStep acc) cache (fun r => if r.1 then 0 else 1) ≤
        (if acc then 0 else 1) + L.length * (72 * cF) := by
  intro L
  induction L with
  | nil =>
      intro acc cache _ _
      simp only [List.foldlM_nil, Ev_pure, List.length_nil, Nat.cast_zero, zero_mul, add_zero]
      exact le_rfl
  | cons index L ih =>
      intro acc cache hnd hL
      obtain ⟨hidx, hf⟩ := hL index (List.mem_cons_self ..)
      rw [List.foldlM_cons]
      unfold ftsCheckStep
      simp only [bind_assoc, pure_bind]
      rw [Ev_bind]
      have hrest : ∀ r ∈ support (roRun secret (ftsForestCheck index) cache),
          Ev secret (L.foldlM ftsCheckStep (acc && r.1)) r.2 (fun r => if r.1 then 0 else 1) ≤
          ((if acc then 0 else 1) + L.length * (72 * cF)) + (if r.1 then 0 else 1) := by
        intro r hr
        refine (ih _ r.2 (List.nodup_cons.mp hnd).2 fun j hj => ?_).trans ?_
        · obtain ⟨hj31, hfj⟩ := hL j (List.mem_cons_of_mem _ hj)
          have hne : index ≠ j := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hj)
          exact ⟨hj31, freshF_preserved secret (xF_ftsForestCheck hidx hj31 hne) cache hfj r hr⟩
        · rcases r with ⟨b, c⟩
          cases acc <;> cases b <;> simp [add_comm]
      refine (expectedValue_mono_of_support hrest).trans ?_
      have hadd := expectedValue_add (roRun secret (ftsForestCheck index) cache)
        (fun _ => (if acc then 0 else 1) + L.length * (72 * cF))
        (fun r => if r.1 then (0 : ℝ≥0∞) else 1)
      refine (le_of_eq hadd).trans ?_
      have h1 := Ev_const_le secret (ftsForestCheck index) cache ((if acc then 0 else 1) + L.length * (72 * cF))
      have h2 := E_forestCheck secret index hidx cache hf
      refine (add_le_add h1 h2).trans (le_of_eq ?_)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

theorem ftsCheck_sum_le : ((2 ^ 31 : ℕ) : ℝ≥0∞) * (72 * cF) ≤ ENNReal.ofReal (1 / 2 ^ 170) := by
  unfold cF
  have e : ((2 ^ 31 : ℕ) : ℝ≥0∞) * (72 * ENNReal.ofReal ((81 / 256 : ℝ) ^ 128)) =
      ENNReal.ofReal (((2 ^ 31 : ℕ) : ℝ) * (72 * (81 / 256 : ℝ) ^ 128)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 72),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [e]
  apply ENNReal.ofReal_le_ofReal
  norm_num

/-- **E8 stage 2 FTS cap exhaustion** (Ev form): from any cache where no FTS ground trial is cached. -/
theorem Ev_ftsCheck_false (secret : BitVec 256) (cache : RCache) (hc : AllFFresh cache) :
    Ev secret ftsCheck cache (fun r => if r.1 then 0 else 1) ≤ ENNReal.ofReal (1 / 2 ^ 170) := by
  unfold ftsCheck
  refine (E_ftsCheckFold secret _ true cache ftsIndices_nodup fun index hi => ?_).trans ?_
  · have hidx := mem_ftsIndices.mp hi
    exact ⟨hidx, freshF_of_all hidx hc⟩
  · rw [ftsIndices_length]
    simpa using ftsCheck_sum_le

/-- The keygen top tree leaves every FTS ground trial fresh. -/
theorem buildTopTree_allFFresh (secret : BitVec 256) (cache : RCache) (hc : AllFFresh cache)
    (r : List (List Digest) × RCache) (hr : r ∈ support (roRun secret buildTopTree cache)) : AllFFresh r.2 :=
  preserves_allF secret buildTopTree
    (fun target coord index heap ht hp => fav_buildTopTree secret target coord index heap ht hp) cache hc r hr

/-! ## The honest signature's level-4 FTS siblings -/

section sign
open SigGolfCandidate.T3.Correctness
attribute [local irreducible] sharedNodes

theorem buildForest_pairs (answers : Answers) (index : Nat) (selected : ForestSelection) (words : ForestWords)
    (p : Fin 4) :
    (evalWithAnswerFn answers (buildForest index selected words)).1.pairs p =
      expectedPairOpening answers index p.val (selected.pairs p) (words.first p) (words.second p)
        (forestPrev answers index p.val) := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [buildForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, buildPair_result,
    buildSingleton, buildSharedCoordinate_result]
  fin_cases p <;> rfl

theorem buildForest_singleton_path (answers : Answers) (index : Nat) (selected : ForestSelection)
    (words : ForestWords) (i : Fin 7) :
    (evalWithAnswerFn answers (buildForest index selected words)).1.singleton.path i =
      authAt (sharedNodes answers false index 8 (fun _ => forestPrev answers index 4)) selected.singleton.val i.val := by
  have hfour : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp only [buildForest, hfour, List.foldlM_cons, List.foldlM_nil,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, buildPair_result,
    buildSingleton, buildSharedCoordinate_result]
  rfl

/-- The signer's forest opening is `buildForest`'s. -/
theorem signFromOutput_forest (answers : Answers) (cache : SigGolfCandidate.T3.Cache) (rho : Digest)
    (counter : BitVec 32) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers
      (SigGolfCandidate.Research.SharedForest.signFromOutput cache rho counter output) = some w) :
    w.signature.forest = (evalWithAnswerFn answers (buildForest (ClaudeWCT.WCT9.digestIndex output)
      (forestSelectionFromOutput output) (forestWordsFromOutput output))).1 := by
  let index := ClaudeWCT.WCT9.digestIndex output
  let built := evalWithAnswerFn answers (buildForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output))
  let prepared := evalWithAnswerFn answers (prepareRoots index)
  unfold SigGolfCandidate.Research.SharedForest.signFromOutput at he
  simp only [evalWithAnswerFn_bind] at he
  cases hs : evalWithAnswerFn answers (searchPreparedLayers cache index prepared built.2) with
  | none =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some layers =>
    dsimp only [index, prepared, built] at hs
    simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
    subst w
    rfl

/-- The level-4 sibling of a selected child is a ground node (heap `8..15`). -/
theorem authAt_four_ok {coord : Nat} {nodes : Array Digest} {selected : Nat} (hs : selected < 128)
    (h : ∀ heap, 8 ≤ heap → heap < 16 → ftsZeroOk coord heap (nodes.getD heap 0) = true) :
    ftsZeroOk coord 8 (authAt nodes selected 4) = true := by
  unfold authAt
  have hk : 8 ≤ (128 + selected) / 2 ^ 4 ∧ (128 + selected) / 2 ^ 4 < 16 := by
    norm_num only [Nat.reducePow]; omega
  have hx : 8 ≤ ((128 + selected) / 2 ^ 4) ^^^ 1 ∧ ((128 + selected) / 2 ^ 4) ^^^ 1 < 16 := by
    generalize (128 + selected) / 2 ^ 4 = k at hk ⊢
    obtain ⟨h1, h2⟩ := hk
    interval_cases k <;> decide
  rw [← ftsZeroOk_ground hx.1 hx.2]
  exact h _ hx.1 hx.2

theorem signFromOutput_ftsPathOK (answers : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hfts : FtsTreesOK answers) (rho : Digest) (counter : BitVec 32) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers
      (SigGolfCandidate.Research.SharedForest.signFromOutput cache rho counter output) = some w) :
    FtsPathOK w.signature := by
  have hf := signFromOutput_forest answers cache rho counter output w he
  have hT := hfts (ClaudeWCT.WCT9.digestIndex output) (ClaudeWCT.WCT9.digestIndex_lt output)
  refine ⟨fun p => ?_, ?_⟩
  · rw [hf, buildForest_pairs]
    exact ⟨authAt_four_ok (firstChild _).isLt (fun heap h8 h16 => ((hT heap h8 h16).1 p.val p.isLt).1),
      authAt_four_ok (secondChild _).isLt (fun heap h8 h16 => ((hT heap h8 h16).1 p.val p.isLt).2)⟩
  · rw [hf, buildForest_singleton_path]
    exact authAt_four_ok (forestSelectionFromOutput output).singleton.isLt (fun heap h8 h16 => (hT heap h8 h16).2)

/-- **E8 stage 2**: on oracles whose FTS ground nodes pass every zero test, the honest signature's opened level-4
FTS siblings pass theirs (FTS analogue of `sign_lowerPathOK_U16`). -/
theorem sign_ftsPathOK (answers : Answers) (hfts : FtsTreesOK answers) (message : Message)
    (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (he : evalWithAnswerFn answers
      (SigGolfCandidate.Research.SharedForest.sign (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 message) =
        some sig) :
    FtsPathOK sig := by
  unfold SigGolfCandidate.Research.SharedForest.sign at he
  simp only [evalWithAnswerFn_bind] at he
  split_ifs at he with htag
  · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
  · unfold SigGolfCandidate.Research.SharedForest.signPayload at he
    simp only [evalWithAnswerFn_bind] at he
    cases hd : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.sharedDigestSearch
        (evalWithAnswerFn answers (privateNonce message)) message 0 ClaudeWCT.WCT9.digestAttemptLimit) with
    | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some found =>
        obtain ⟨counter, output⟩ := found
        simp only [hd, evalWithAnswerFn_bind] at he
        cases hs : evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.signFromOutput
            (evalWithAnswerFn answers SigGolfCandidate.T3.keygen).2 (evalWithAnswerFn answers (privateNonce message)) counter output) with
        | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
        | some original =>
            simp only [hs, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst sig
            exact signFromOutput_ftsPathOK answers _ hfts _ _ _ original hs

end sign

end ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
