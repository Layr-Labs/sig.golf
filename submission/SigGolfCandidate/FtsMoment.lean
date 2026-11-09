import Mathlib.Data.Fin.Basic
import SigGolfCandidate.Merge053
set_option debug.skipKernelTC true
set_option linter.all false

/-! # E8: sign cost moment of the FTS ground nodes

Every FTS node of heap `8..15` (8 per coordinate tree, 72 per signature) is a first-nonce search (`ftsNodeAt`):
trial `n` hashes `ftsNodeInputN` (the nonce in the pad) until the kept low half has its top `ftsZeroBits` bits clear.
With every trial fresh, one ground node of width `b` contributes a geometric factor `f` with
`z · (2^-b + (1 - 2^-b) f) ≤ f`, `z ≤ f` (copy of U16b's `V_gnode`), and `buildForest` is bounded by
`z^31249 · Π_c f_c^8` (31,321 fixed queries minus the 72 ground nodes). -/

namespace ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.T3.Freshness (Avoids avoids_pure avoids_bind preserves avoidsQuery hasTag_privatePair HasTag)
open SigGolfCandidate.T3.QuerySpace (queryHeader queryHeader_padded)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9 (Rank Child)
open SigGolfCandidate.T3.Cost (Bound)
open ClaudeWCT.WCT9 (ftsNodeInputN ftsNodeHashN ftsNonceSearch ftsNodeAt ftsNodeG ftsZeroBits ftsZeroOk
  ftsNonceCap wctNodeHeader)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-! ## Trials -/

/-- Oracle input of trial `n` of the FTS node `(coord, index, heap)`. -/
def fTrial (coord index heap n : Nat) (left right : Digest) : HashInput :=
  pad64 (ftsNodeInputN coord index heap n left right)

theorem fTrial_header (coord index heap n : Nat) (left right : Digest) :
    queryHeader (fTrial coord index heap n left right) = bytesLE 16 (wctNodeHeader coord index heap) := by
  unfold fTrial ftsNodeInputN
  simpa only [List.append_assoc] using
    queryHeader_padded (bytesLE 16 left) (nonceBytes n ++ bytesLE 16 right) (bytesLE_length ..)
      (wctNodeHeader coord index heap)

theorem ftsNodeInputN_length (coord index heap n : Nat) (left right : Digest) :
    (ftsNodeInputN coord index heap n left right).length = 64 := by
  simp [ftsNodeInputN, nonceBytes, bytesLE_length]

theorem fTrial_length (coord index heap n : Nat) (left right : Digest) :
    (fTrial coord index heap n left right).length = 64 := by
  simp [fTrial, pad64, ftsNodeInputN_length]

theorem fTrial_injective (coord index heap : Nat) (left right : Digest) {k n : Nat} (hk : k < 2 ^ 64)
    (hn : n < 2 ^ 64) (he : fTrial coord index heap k left right = fTrial coord index heap n left right) : k = n := by
  unfold fTrial at he
  have he' : ftsNodeInputN coord index heap k left right = ftsNodeInputN coord index heap n left right := by
    unfold pad64 at he
    rw [ftsNodeInputN_length, ftsNodeInputN_length] at he
    exact List.append_cancel_right he
  unfold ftsNodeInputN at he'
  simp only [List.append_assoc] at he'
  have h1 := List.append_inj he' (by simp [bytesLE_length])
  have h2 := List.append_inj h1.2 (by simp [bytesLE_length])
  have h3 := List.append_inj h2.2 (by simp [nonceBytes, bytesLE_length])
  have h4 := bytesLE_injective h3.1
  have h5 := congrArg BitVec.toNat h4
  simp only [BitVec.toNat_ofNat] at h5
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hn] at h5
  exact h5

/-- A ground FTS position: coordinate, 31-bit index, heap `8..15`. -/
def FP (coord index heap : Nat) : Prop := coord < 9 ∧ index < 2 ^ 31 ∧ 8 ≤ heap ∧ heap < 16

theorem fTrial_ne {coord index heap coord' heap' : Nat} (h : FP coord index heap) (h' : FP coord' index heap')
    (hne : ¬ (coord' = coord ∧ heap' = heap)) (n m : Nat) (l r l' r' : Digest) :
    fTrial coord' index heap' m l' r' ≠ fTrial coord index heap n l r := by
  intro he
  have hh := congrArg queryHeader he
  rw [fTrial_header, fTrial_header] at hh
  obtain ⟨e1, -, e3⟩ := ClaudeWCT.WCT9.wctNodeHeader_injective h'.1 h'.2.1 (by have := h'.2.2.2; omega)
    h.1 h.2.1 (by have := h.2.2.2; omega) (bytesLE_injective hh)
  exact hne ⟨e1, e3⟩

/-! ## Freshness -/

/-- The trials of every ground node `(coord, heap)` in `S` of the FTS forest `index` are fresh. -/
def FreshF (index : Nat) (S : Nat → Nat → Prop) (cache : RCache) : Prop :=
  ∀ coord heap, S coord heap → ∀ n l r, cache (fTrial coord index heap n l r) = none

theorem FreshF.mono {index : Nat} {S S' : Nat → Nat → Prop} {cache : RCache} (h : FreshF index S cache)
    (hS : ∀ c x, S' c x → S c x) : FreshF index S' cache := fun c x hs => h c x (hS c x hs)

/-- `q` avoids every trial of the ground nodes in `S`. -/
def NotF (secret : BitVec 256) (index : Nat) (S : Nat → Nat → Prop) (q : Spec.Domain) : Prop :=
  ∀ coord heap, S coord heap → ∀ n l r, avoidsQuery secret (fTrial coord index heap n l r) q

theorem freshF_preserved {α : Type} (secret : BitVec 256) {index : Nat} {S : Nat → Nat → Prop} {p : M α}
    (hp : AllQueriesSatisfy p (NotF secret index S)) (cache : RCache) (hc : FreshF index S cache)
    (result : α × RCache) (hr : result ∈ support (roRun secret p cache)) : FreshF index S result.2 := by
  intro coord heap hs n l r
  rw [preserves secret _ p (ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono hp fun q hq => hq coord heap hs n l r)
    cache result hr]
  exact hc coord heap hs n l r

/-- A public query whose header is no ground node header of `S`. -/
theorem notF_public {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop} {input : HashInput} {hdr : BitVec 128}
    (h : queryHeader input = bytesLE 16 hdr) (hne : ∀ c x, S c x → hdr ≠ wctNodeHeader c index x) :
    NotF secret index S (.inl (.inr input)) := by
  intro coord heap hs n l r
  show input ≠ _
  intro he
  exact hne coord heap hs (bytesLE_injective (n := 16) (by rw [← h, he, fTrial_header]))

/-- A tagged private query (tag byte `≠ 6`). -/
theorem notF_private {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop} (hS : ∀ c x, S c x → c < 9)
    (tag lay tree position idx : Nat) (ht : tag % 256 ≠ 254) :
    NotF secret index S (.inr (.inl (header tag lay tree position idx))) := by
  intro coord heap hs n l r
  show privateInput secret (.inl (header tag lay tree position idx)) ≠ _
  intro he
  obtain ⟨l', t', p', i', hh⟩ := hasTag_privatePair secret tag lay tree position idx
  have := hh
  rw [he, fTrial_header] at this
  exact ClaudeWCT.WCT9.wctNodeHeader_ne_header (hS coord heap hs) index heap tag l' t' p' i' ht (bytesLE_injective this)


open SigGolfCandidate.T3M (allQ_pure allQ_bind allQ_map allQ_foldlM allQ_mono)

section headers
variable {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop}

theorem notF_publicHash {input : HashInput} {hdr : BitVec 128} (h : queryHeader (pad64 input) = bytesLE 16 hdr)
    (hne : ∀ c x, S c x → hdr ≠ wctNodeHeader c index x) :
    AllQueriesSatisfy (publicHash input) (NotF secret index S) :=
  (allQueriesSatisfy_query_iff _ _).mpr (notF_public h hne)

theorem notF_shortHash {input : HashInput} {hdr : BitVec 128} (h : queryHeader (pad64 input) = bytesLE 16 hdr)
    (hne : ∀ c x, S c x → hdr ≠ wctNodeHeader c index x) :
    AllQueriesSatisfy (shortHash input) (NotF secret index S) := by
  unfold shortHash
  exact allQ_bind (notF_publicHash h hne) fun _ => allQ_pure _

theorem notF_highHash {input : HashInput} {hdr : BitVec 128} (h : queryHeader (pad64 input) = bytesLE 16 hdr)
    (hne : ∀ c x, S c x → hdr ≠ wctNodeHeader c index x) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.highHash input) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.highHash
  exact allQ_bind (notF_publicHash h hne) fun _ => allQ_pure _

theorem notF_projHash (high : Bool) {input : HashInput} {hdr : BitVec 128}
    (h : queryHeader (pad64 input) = bytesLE 16 hdr) (hne : ∀ c x, S c x → hdr ≠ wctNodeHeader c index x) :
    AllQueriesSatisfy (projHash high input) (NotF secret index S) := by
  unfold projHash
  exact allQ_bind (notF_publicHash h hne) fun _ => allQ_pure _

theorem notF_ftsHash (heap : Nat) {input : HashInput} {hdr : BitVec 128}
    (h : queryHeader (pad64 input) = bytesLE 16 hdr) (hne : ∀ c x, S c x → hdr ≠ wctNodeHeader c index x) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.ftsHash heap input) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.ftsHash
  split
  · exact notF_highHash h hne
  · exact notF_shortHash h hne

/-- Ground positions only. -/
def GroundSet (index : Nat) (S : Nat → Nat → Prop) : Prop := ∀ c x, S c x → FP c index x

theorem wctTopInput_header (coord index heap : Nat) (l p r : Digest) :
    queryHeader (pad64 (ClaudeWCT.WCT9.wctTopInput coord index heap l p r)) = bytesLE 16 (wctNodeHeader coord index heap) := by
  unfold ClaudeWCT.WCT9.wctTopInput
  simpa only [List.append_assoc] using
    queryHeader_padded (bytesLE 16 l) (bytesLE 16 p ++ bytesLE 16 r) (bytesLE_length ..) (wctNodeHeader coord index heap)

theorem nodeH_header (coord index heap : Nat) (l r : Digest) :
    queryHeader (pad64 (bytesLE 16 l ++ bytesLE 16 (wctNodeHeader coord index heap) ++ SigGolfCandidate.T3.zero16 ++ bytesLE 16 r)) =
      bytesLE 16 (wctNodeHeader coord index heap) := by
  simpa only [List.append_assoc] using
    queryHeader_padded (bytesLE 16 l) (SigGolfCandidate.T3.zero16 ++ bytesLE 16 r) (bytesLE_length ..) (wctNodeHeader coord index heap)

/-- A node header of a non-ground heap is no ground header. -/
theorem node_ne_ground (hS : GroundSet index S) {coord heap : Nat} (hc : coord < 9) (hh : heap < 128)
    (hng : ¬ (8 ≤ heap ∧ heap < 16)) : ∀ c x, S c x → wctNodeHeader coord index heap ≠ wctNodeHeader c index x := by
  intro c x hs he
  have hp := hS c x hs
  have hx := hp.2.2.2
  obtain ⟨-, -, e3⟩ := ClaudeWCT.WCT9.wctNodeHeader_injective hc hp.2.1 (by omega) hp.1 hp.2.1 (by omega) he
  exact hng ⟨by have := hp.2.2.1; omega, by have := hp.2.2.2; omega⟩

/-- A node header of a coordinate outside `S`'s coordinates is no ground header. -/
theorem node_ne_ground_coord (hS : GroundSet index S) {coord heap : Nat} (hc : coord < 9) (hh : heap < 2 ^ 64)
    (hco : ∀ c x, S c x → c ≠ coord) : ∀ c x, S c x → wctNodeHeader coord index heap ≠ wctNodeHeader c index x := by
  intro c x hs he
  have hp := hS c x hs
  have hx := hp.2.2.2
  obtain ⟨e1, -, -⟩ := ClaudeWCT.WCT9.wctNodeHeader_injective hc hp.2.1 hh hp.1 hp.2.1 (by omega) he
  exact hco c x hs e1.symm

end headers


section programs
variable {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop} (hS : GroundSet index S)
include hS

theorem ftsChainInputW_header (coord selected i step : Nat) (value : Digest) :
    queryHeader (pad64 (ClaudeWCT.WCT9.ftsChainInputW index coord selected i step value)) =
      bytesLE 16 (ClaudeWCT.WCT9.ftsChainHeader index coord selected i step) := by
  unfold ClaudeWCT.WCT9.ftsChainInputW
  split
  · simpa only [List.append_assoc] using
      queryHeader_padded (bytesLE 16 value) (zero16 ++ zero16) (bytesLE_length ..)
        (ClaudeWCT.WCT9.ftsChainHeader index coord selected i step)
  · simpa only [ClaudeWCT.WCT9.chainInput, List.append_assoc] using
      queryHeader_padded zero16 (_ : HashInput) (by simp [zero16])
        (ClaudeWCT.WCT9.ftsChainHeader index coord selected i step)

theorem notF_chain (coord selected i start count : Nat) (value : Digest) (hi : i < 6) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.chain index coord selected i start count value) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.chain
  exact allQ_foldlM _ _ (fun v step => notF_projHash _ (ftsChainInputW_header hS coord selected i step v)
    (fun c x _ he => ClaudeWCT.WCT9.wctNodeHeader_ne_ftsChainHeaderP c index x _ _ _ _ _ _ hi he.symm)) _

theorem notF_leafHashH (heap coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.leafHashH heap index coord selected pad ends) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.leafHashH
  refine notF_ftsHash heap (hdr := ClaudeWCT.WCT9.ftsLeafHeader index coord selected) ?_
    (fun c x hs he => ClaudeWCT.WCT9.ftsLeafHeader_ne_wctNodeHeader index coord selected (hS c x hs).1 index x
      (by have := (hS c x hs).2.2; omega) he)
  unfold ClaudeWCT.WCT9.leafInputP
  simpa only [List.append_assoc] using
    queryHeader_padded (bytesLE 16 (ends.getD 0 0)) (bytesLE 16 pad ++ (ends.drop 1).flatMap (bytesLE 16))
      (bytesLE_length ..) (ClaudeWCT.WCT9.ftsLeafHeader index coord selected)

theorem notF_buildChildH (heap coord selected : Nat) (word : Rank) (coefs : List Digest) (pad : Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.buildChildH heap index coord selected word coefs pad) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.buildChildH
  refine allQ_bind (allQ_foldlM _ _ (fun st i => ?_) _) fun st => ?_
  · exact allQ_bind (notF_chain hS _ _ _ _ _ _ (by omega)) fun _ =>
      allQ_bind (notF_chain hS _ _ _ _ _ _ (by omega)) fun _ => allQ_pure _
  · exact allQ_bind (notF_leafHashH hS _ _ _ _ _) fun _ => allQ_pure _

theorem notF_ftsCoefs (coord : Nat) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.ftsCoefs index coord) (NotF secret index S) := by
  unfold ClaudeWCT.WCT9.ftsCoefs
  refine allQ_foldlM _ _ (fun acc j => ?_) _
  unfold ClaudeWCT.WCT9.ftsSeedPair privatePair privateHash
  exact allQ_bind ((allQueriesSatisfy_query_iff _ _).mpr
    (notF_private (fun c x h => (hS c x h).1) 8 coord index 0 j (by decide))) fun _ => allQ_pure _

/-- The children of a coordinate (coefficients and the 128 leaves) avoid every ground trial. -/
theorem notF_children (first : Bool) (coord : Nat) (word : Rank) (selected : Child) (pads : Nat → PairRoot)
    (coefs : List Digest) :
    AllQueriesSatisfy ((List.range 128).foldlM
      (fun (state : List Digest × List Digest) j => do
        let (root, values) ← ClaudeWCT.WCT9.buildChildH (128 + j) index coord (rawChild first j) word coefs
          (pads (j / 64)).1
        pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], []))
      (NotF secret index S) :=
  allQ_foldlM _ _ (fun _ _ => allQ_bind (notF_buildChildH hS _ _ _ _ _ _) fun _ => allQ_pure _) _

/-- A shared node off the ground heaps avoids every ground trial. -/
theorem notF_sharedNode_plain (first : Bool) (coord heap : Nat) (pads : Nat → PairRoot) (left right : Digest)
    (hc : coord < 9) (hh : heap < 128) (hng : ¬ (8 ≤ heap ∧ heap < 16)) :
    AllQueriesSatisfy (sharedNode first coord index heap pads left right) (NotF secret index S) := by
  have hne := node_ne_ground hS hc hh hng
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
    · rw [ClaudeWCT.WCT9.ftsNodeG_of_zero (ClaudeWCT.WCT9.ftsZeroBits_off hng)]
      unfold ClaudeWCT.WCT9.wctNodeHashH
      exact notF_ftsHash heap (nodeH_header ..) hne

/-- A shared node of a coordinate outside `S` avoids every ground trial of `S`. -/
theorem notF_sharedNode_coord (first : Bool) (coord heap : Nat) (pads : Nat → PairRoot) (left right : Digest)
    (hc : coord < 9) (hh : heap < 128) (hco : ∀ c x, S c x → c ≠ coord) :
    AllQueriesSatisfy (sharedNode first coord index heap pads left right) (NotF secret index S) := by
  have hne := node_ne_ground_coord hS hc (show heap < 2 ^ 64 by omega) hco
  by_cases hng : 8 ≤ heap ∧ heap < 16
  · have e : sharedNode first coord index heap pads left right = ftsNodeG coord index heap left right := by
      simp only [sharedNode, if_neg (show ¬ heap < 4 by omega), if_neg (show ¬ heap < 8 by omega)]
    rw [e]
    refine ClaudeWCT.WCT9.allQ_ftsNodeG _ _ _ _ _ ?_ (fun n _ => ?_)
    · unfold ClaudeWCT.WCT9.wctNodeHashH
      exact notF_ftsHash heap (nodeH_header ..) hne
    · unfold ftsNodeHashN
      exact notF_shortHash (fTrial_header coord index heap n left right) hne
  · exact notF_sharedNode_plain hS first coord heap pads left right hc hh hng

end programs


/-! ## Cost moment -/

/-- The kept (low) half of an FTS ground trial answer. -/
def fVal (a : HashOutput) : Digest := a.extractLsb' 0 128

theorem ftsNodeHashN_eq (coord index heap n : Nat) (left right : Digest) :
    ftsNodeHashN coord index heap n left right =
      (publicQuery (fTrial coord index heap n left right) >>= fun a => pure (fVal a)) := rfl

theorem ftsNonceSearch_zero_bind {β : Type} (coord index heap : Nat) (left right : Digest) (n : Nat)
    (next : Nat × Digest → M β) :
    (ftsNonceSearch coord index heap left right 0 n >>= next) =
      (publicQuery (fTrial coord index heap n left right) >>= fun answer => next (n, fVal answer)) := by
  simp only [ftsNonceSearch, ftsNodeHashN_eq, bind_assoc, pure_bind]

theorem ftsNonceSearch_succ_bind {β : Type} (coord index heap : Nat) (left right : Digest) (fuel n : Nat)
    (next : Nat × Digest → M β) :
    (ftsNonceSearch coord index heap left right (fuel + 1) n >>= next) =
      (publicQuery (fTrial coord index heap n left right) >>= fun answer =>
        if ftsZeroOk coord heap (fVal answer) then next (n, fVal answer)
        else (ftsNonceSearch coord index heap left right fuel (n + 1) >>= next)) := by
  simp only [ftsNonceSearch, ftsNodeHashN_eq, bind_assoc, pure_bind]
  congr 1
  funext answer
  split <;> simp only [pure_bind]

/-- **Cost moment of an FTS nonce search** (copy of U16b's `V_lowerNonceSearch_bind`). -/
theorem V_ftsNonceSearch_bind {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (coord index heap : Nat)
    (left right : Digest) (next : Nat × Digest → M β) (G : RCache → Prop) (B b : ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (fTrial coord index heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      V secret z (next (k, fVal answer)) (cache.cacheQuery (fTrial coord index heap k left right) answer) ≤ B)
    (hstep : z * expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if ftsZeroOk coord heap (fVal answer) then B else b) ≤ b)
    (htail : z * B ≤ b) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (fTrial coord index heap k left right) = none) →
      V secret z (ftsNonceSearch coord index heap left right fuel n >>= next) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [ftsNonceSearch_zero_bind, V_publicQuery, fTrial_length]
      have hf := expectedValue_fresh (fTrial coord index heap n left right) cache (hfresh n le_rfl (by omega))
        (fun r => V secret z (next (n, fVal r.1)) r.2)
      refine le_trans (le_of_eq (congrArg (fun t => z ^ (64 / 64) * t) hf)) ?_
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      refine le_trans (mul_le_mul' le_rfl ?_) htail
      refine (expectedValue_mono _ fun answer => hnext cache hg n answer).trans ?_
      rw [expectedValue_const (by simp)]
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [ftsNonceSearch_succ_bind, V_publicQuery, fTrial_length]
      have hf := expectedValue_fresh (fTrial coord index heap n left right) cache (hfresh n le_rfl (by omega))
        (fun r => V secret z (if ftsZeroOk coord heap (fVal r.1) then next (n, fVal r.1)
          else (ftsNonceSearch coord index heap left right fuel (n + 1) >>= next)) r.2)
      refine le_trans (le_of_eq (congrArg (fun t => z ^ (64 / 64) * t) hf)) ?_
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      refine le_trans (mul_le_mul' le_rfl (expectedValue_mono _ fun answer => ?_)) hstep
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : fTrial coord index heap k left right ≠ fTrial coord index heap n left right := by
          intro he
          have := fTrial_injective coord index heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))

theorem ftsZeroBits_le2 (coord heap : Nat) : ftsZeroBits coord heap ≤ 2 := by
  unfold ftsZeroBits; split_ifs <;> omega

theorem fZeroOk_iff (coord heap : Nat) (a : HashOutput) :
    ftsZeroOk coord heap (fVal a) = true ↔
      a.toNat / 2 ^ (128 - ftsZeroBits coord heap) % 2 ^ ftsZeroBits coord heap = 0 := by
  have hb := ftsZeroBits_le2 coord heap
  unfold ftsZeroOk fVal
  generalize ftsZeroBits coord heap = b at hb ⊢
  have hv : (a.extractLsb' 0 128).toNat = a.toNat % 2 ^ 128 := by
    simp [BitVec.extractLsb'_toNat]
  rw [beq_iff_eq, hv]
  have hlt : a.toNat % 2 ^ 128 / 2 ^ (128 - b) < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [← Nat.mod_eq_of_lt hlt, ClaudeWCT.W9.T3.TopMoment.window_of_half _ _ _ (by omega)]

/-- **Acceptance probability** of an FTS ground trial: exactly `2^-b`. -/
theorem prob_fAccept (coord heap : Nat) :
    Pr[fun a : HashOutput => ftsZeroOk coord heap (fVal a) = true |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ((2 : ℝ≥0∞) ^ ftsZeroBits coord heap)⁻¹ := by
  have hb := ftsZeroBits_le2 coord heap
  simp only [fZeroOk_iff]
  exact ClaudeWCT.W9.T3.TopMoment.prob_window _ _ _ (by omega) (by positivity)

theorem expectedValue_uniform_ite_F (P : HashOutput → Prop) [DecidablePred P] (B b : ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => if P a then B else b) =
      Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] * B +
        (1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)]) * b := by
  have hc := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) P
  rw [probFailure_uniformSample, tsub_zero] at hc
  have hn : Pr[fun a => ¬P a | ($ᵗ HashOutput : ProbComp HashOutput)] =
      1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hc ▸ le_add_right le_rfl)) (by
      rw [add_comm]; exact hc)
  have he : (fun a => if P a then B else b) =
      fun a => (if P a then 1 else 0) * B + (if ¬P a then 1 else 0) * b := by
    funext a; by_cases hp : P a <;> simp [hp]
  rw [he, expectedValue_add, expectedValue_mul_const, expectedValue_mul_const, expectedValue_ite_one,
    expectedValue_ite_one, hn]

/-- The ground factor condition for coordinate `coord` (width `ftsZeroBits coord 8`). -/
def FacF (z : ℝ≥0∞) (coord : Nat) (f : ℝ≥0∞) : Prop :=
  z * (((2 : ℝ≥0∞) ^ ftsZeroBits coord 8)⁻¹ + (1 - ((2 : ℝ≥0∞) ^ ftsZeroBits coord 8)⁻¹) * f) ≤ f ∧ z ≤ f

theorem ftsZeroBits_ground {coord heap : Nat} (h : 8 ≤ heap ∧ heap < 16) :
    ftsZeroBits coord heap = ftsZeroBits coord 8 := by
  simp [ftsZeroBits, h]

/-- A plain program (bounded, avoiding the ground trials). -/
theorem V_plainF {α β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (hz : 1 ≤ z) {index : Nat} {S : Nat → Nat → Prop}
    {p : M α} {P : SigGolfCandidate.T3.Cost.Query → Prop} {Post : α → Prop} {k : Nat} (hb : Bound P Post k p)
    (hp : AllQueriesSatisfy p (NotF secret index S)) (next : α → M β) (B : ℝ≥0∞)
    (hnext : ∀ a cache, FreshF index S cache → V secret z (next a) cache ≤ B) (cache : RCache)
    (hc : FreshF index S cache) : V secret z (p >>= next) cache ≤ z ^ k * B :=
  (V_bind_le secret z p next cache B fun r hr => hnext _ _ (freshF_preserved secret hp cache hc r hr)).trans
    (mul_le_mul' (V_of_bound hb secret z hz cache) le_rfl)

/-- **One ground FTS node**: `V ≤ f · B` (its trials fresh). -/
theorem V_fnode {β : Type} (secret : BitVec 256) (z f B : ℝ≥0∞) (coord index heap : Nat) (hp : FP coord index heap)
    (left right : Digest) (next : Digest → M β) (S : Nat → Nat → Prop) (hS : GroundSet index S)
    (hfac : FacF z coord f)
    (hnext : ∀ v cache, FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) cache → V secret z (next v) cache ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) (hin : S coord heap) :
    V secret z (ftsNodeG coord index heap left right >>= next) cache ≤ f * B := by
  obtain ⟨hst, hzf⟩ := hfac
  have hg : 8 ≤ heap ∧ heap < 16 := ⟨hp.2.2.1, hp.2.2.2⟩
  rw [← ftsZeroBits_ground hg] at hst
  have hpres : ∀ (c : RCache) k ans, FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) c →
      FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap))
        (c.cacheQuery (fTrial coord index heap k left right) ans) := by
    intro c k ans hc x y hxy n l r
    exact (QueryCache.cacheQuery_of_ne (cache := c) ans
      (fTrial_ne hp (hS x y hxy.1) hxy.2 k n left right l r)).trans (hc x y hxy n l r)
  have hb : ftsZeroBits coord heap ≠ 0 := by
    simp only [ftsZeroBits, if_pos hg]; norm_num
  unfold ftsNodeG
  rw [bind_map_left]
  unfold ftsNodeAt
  rw [if_neg hb]
  have hcap : ftsNonceCap coord heap - 1 < 2 ^ 64 := by
    have := ftsZeroBits_le2 coord heap
    unfold ftsNonceCap
    have : 2 ^ ftsZeroBits coord heap ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  refine V_ftsNonceSearch_bind secret z coord index heap left right (fun x : Nat × Digest => next x.2)
    (FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap))) B (f * B) (fun c hc k a => hpres c k a hc)
    (fun c hc k a => hnext (fVal a) _ (hpres c k a hc)) ?_ ?_ (ftsNonceCap coord heap - 1) 0 (by omega) cache
    (hfresh.mono (fun x y hxy => hxy.1)) (fun k _ _ => hfresh coord heap hin k left right)
  · rw [expectedValue_uniform_ite_F
      (fun a => ftsZeroOk coord heap (fVal a) = true), prob_fAccept]
    calc z * (((2 : ℝ≥0∞) ^ ftsZeroBits coord heap)⁻¹ * B +
          (1 - ((2 : ℝ≥0∞) ^ ftsZeroBits coord heap)⁻¹) * (f * B))
        = z * (((2 : ℝ≥0∞) ^ ftsZeroBits coord heap)⁻¹ +
          (1 - ((2 : ℝ≥0∞) ^ ftsZeroBits coord heap)⁻¹) * f) * B := by ring
      _ ≤ f * B := mul_le_mul' hst le_rfl
  · exact mul_le_mul' hzf le_rfl

/-- **One shared node** of coordinate `coord`: `V ≤ f · B`, with `f` the ground factor on heaps `8..15` and any
`f ≥ z` elsewhere. -/
theorem V_snode {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (hz : 1 ≤ z) (first : Bool) (coord index heap : Nat)
    (hc : coord < 9) (hidx : index < 2 ^ 31) (h2 : 2 ≤ heap) (hh : heap < 128) (pads : Nat → PairRoot)
    (left right : Digest) (S : Nat → Nat → Prop) (hS : GroundSet index S) (f B : ℝ≥0∞)
    (hfg : 8 ≤ heap ∧ heap < 16 → FacF z coord f) (hfp : ¬ (8 ≤ heap ∧ heap < 16) → z ≤ f) (next : Digest → M β)
    (hnext : ∀ v cache, FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) cache → V secret z (next v) cache ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) (hin : 8 ≤ heap ∧ heap < 16 → S coord heap) :
    V secret z (sharedNode first coord index heap pads left right >>= next) cache ≤ f * B := by
  by_cases hg : 8 ≤ heap ∧ heap < 16
  · have e : sharedNode first coord index heap pads left right = ftsNodeG coord index heap left right := by
      simp only [sharedNode, if_neg (show ¬ heap < 4 by omega), if_neg (show ¬ heap < 8 by omega)]
    rw [e]
    exact V_fnode secret z f B coord index heap ⟨hc, hidx, hg⟩ left right next S hS (hfg hg) hnext cache hfresh (hin hg)
  · have hb := SigGolfCandidate.Research.SharedForest.bound_sharedNode first coord index heap pads left right
    have hcost : sharedNodeCost coord heap = 1 := by unfold sharedNodeCost; rw [if_neg hg]
    rw [hcost] at hb
    refine (V_plainF secret z hz hb (notF_sharedNode_plain hS first coord heap pads left right hc hh hg) next B
      (fun v c hc' => hnext v c (hc'.mono fun x y h => h.1)) cache hfresh).trans ?_
    rw [pow_one]
    exact mul_le_mul' (hfp hg) le_rfl


/-- One heap step of `sharedHeap`. -/
def heapStep (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) (nodes : Array Digest) (heap : Nat) :
    M (Array Digest) := do
  let value ← sharedNode first coord index heap pads (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
  pure (nodes.set! heap value)

/-- A segment of heaps with a uniform per-node factor `c`. -/
theorem V_heapSeg {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (hz : 1 ≤ z) (first : Bool) (index coord : Nat)
    (hc : coord < 9) (hidx : index < 2 ^ 31) (pads : Nat → PairRoot) (c : ℝ≥0∞) :
    ∀ (l : List Nat), (∀ h ∈ l, (8 ≤ h ∧ h < 16 → FacF z coord c) ∧ (¬ (8 ≤ h ∧ h < 16) → z ≤ c)) →
      (∀ h ∈ l, 2 ≤ h ∧ h < 128) → l.Nodup →
    ∀ (S : Nat → Nat → Prop) (init : Array Digest) (next : Array Digest → M β) (B : ℝ≥0∞),
      GroundSet index S → (∀ h ∈ l, 8 ≤ h ∧ h < 16 → S coord h) →
      (∀ a cache, FreshF index (fun c' x => S c' x ∧ ¬ (c' = coord ∧ x ∈ l)) cache → V secret z (next a) cache ≤ B) →
      ∀ cache, FreshF index S cache →
        V secret z ((l.foldlM (heapStep first index coord pads) init) >>= next) cache ≤ c ^ l.length * B := by
  intro l
  induction l with
  | nil =>
      intro _ _ _ S init next B _ _ hnext cache hfresh
      simp only [List.foldlM_nil, pure_bind, List.length_nil, pow_zero, one_mul]
      exact hnext init cache (hfresh.mono fun x y h => h.1)
  | cons h t ih =>
      intro hfac hl hnd S init next B hS hin hnext cache hfresh
      have hnd' := List.nodup_cons.mp hnd
      rw [List.foldlM_cons]
      unfold heapStep
      simp only [bind_assoc, pure_bind]
      have hh := hl h (List.mem_cons_self ..)
      refine le_trans (V_snode secret z hz first coord index h hc hidx hh.1 hh.2 pads _ _ S hS c (c ^ t.length * B)
        (hfac h (List.mem_cons_self ..)).1 (hfac h (List.mem_cons_self ..)).2 _ (fun v cache' hc' => ?_) cache hfresh
        (hin h (List.mem_cons_self ..))) (le_of_eq ?_)
      · exact ih (fun x hx => hfac x (List.mem_cons_of_mem _ hx)) (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hnd'.2 (fun c' x => S c' x ∧ ¬ (c' = coord ∧ x = h))
          (init.set! h v) next B (fun c' x hx => hS c' x hx.1)
          (fun x hx hg => ⟨hin x (List.mem_cons_of_mem _ hx) hg, fun he => hnd'.1 (he.2 ▸ hx)⟩)
          (fun a cache'' hc'' => hnext a cache'' (hc''.mono fun c' x hx =>
            ⟨⟨hx.1, fun he => hx.2 ⟨he.1, by rw [he.2]; exact List.mem_cons_self ..⟩⟩,
              fun he => hx.2 ⟨he.1, List.mem_cons_of_mem _ he.2⟩⟩)) cache' hc'
      · rw [List.length_cons, pow_succ]; ring

theorem V_heapSegN {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (hz : 1 ≤ z) (first : Bool) (index coord : Nat)
    (hc : coord < 9) (hidx : index < 2 ^ 31) (pads : Nat → PairRoot) (c : ℝ≥0∞) (l : List Nat) (n : Nat)
    (hn : l.length = n)
    (hfac : ∀ h ∈ l, (8 ≤ h ∧ h < 16 → FacF z coord c) ∧ (¬ (8 ≤ h ∧ h < 16) → z ≤ c))
    (hl : ∀ h ∈ l, 2 ≤ h ∧ h < 128) (hnd : l.Nodup)
    (S : Nat → Nat → Prop) (init : Array Digest) (next : Array Digest → M β) (B : ℝ≥0∞)
    (hS : GroundSet index S) (hin : ∀ h ∈ l, 8 ≤ h ∧ h < 16 → S coord h)
    (hnext : ∀ a cache, FreshF index (fun c' x => S c' x ∧ ¬ (c' = coord ∧ x ∈ l)) cache → V secret z (next a) cache ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    V secret z ((l.foldlM (heapStep first index coord pads) init) >>= next) cache ≤ c ^ n * B := by
  subst hn
  exact V_heapSeg secret z hz first index coord hc hidx pads c l hfac hl hnd S init next B hS hin hnext cache hfresh

/-- The whole shared heap: `z^(112 + m) · f^8` (heaps `16..127`, the 8 ground heaps, the `m` top heaps). -/
theorem V_sharedHeap {β : Type} (secret : BitVec 256) (z f : ℝ≥0∞) (hz : 1 ≤ z) (first : Bool) (index coord : Nat)
    (hc : coord < 9) (hidx : index < 2 ^ 31) (pads : Nat → PairRoot) (hf : FacF z coord f) (leaves : List Digest)
    (S : Nat → Nat → Prop) (hS : GroundSet index S) (hin : ∀ h, 8 ≤ h ∧ h < 16 → S coord h)
    (next : Array Digest → M β) (B : ℝ≥0∞)
    (hnext : ∀ a cache, FreshF index (fun c' x => S c' x ∧ c' ≠ coord) cache → V secret z (next a) cache ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    V secret z (sharedHeap first index coord pads leaves >>= next) cache ≤
      z ^ 112 * (f ^ 8 * (z ^ (if first then 4 else 6) * B)) := by
  have hhm : ∀ (a m : Nat), a + m = 8 → 2 ≤ a →
      (List.range' a (m + (8 + 112))).reverse =
        (List.range' (8 + 8) 112).reverse ++ ((List.range' 8 8).reverse ++ (List.range' a m).reverse) := by
    intro a m ham _
    rw [← List.range'_append_1 (s := a) (m := m) (n := 8 + 112), ham,
      ← List.range'_append_1 (s := 8) (m := 8) (n := 112), List.reverse_append,
      List.reverse_append, List.append_assoc]
  have key : ∀ (a m : Nat), a + m = 8 → 2 ≤ a → ∀ init : Array Digest,
      V secret z (((List.range' a (m + (8 + 112))).reverse.foldlM (heapStep first index coord pads) init) >>= next)
        cache ≤ z ^ 112 * (f ^ 8 * (z ^ m * B)) := by
    intro a m ham ha init
    rw [hhm a m ham ha]
    simp only [List.foldlM_append, bind_assoc]
    have mem1 : ∀ x ∈ (List.range' (8 + 8) 112).reverse, 16 ≤ x ∧ x < 128 := fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx; omega
    have mem2 : ∀ x ∈ (List.range' 8 8).reverse, 8 ≤ x ∧ x < 16 := fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx; omega
    have mem3 : ∀ x ∈ (List.range' a m).reverse, a ≤ x ∧ x < 8 := fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx; omega
    have l1 : ((List.range' (8 + 8) 112).reverse).length = 112 := by simp
    have l2 : ((List.range' 8 8).reverse).length = 8 := by simp
    have l3 : ((List.range' a m).reverse).length = m := by simp
    refine V_heapSegN secret z hz first index coord hc hidx pads z _ _ l1
      (fun x hx => ⟨fun h => absurd h (by have := mem1 x hx; omega), fun _ => le_rfl⟩)
      (fun x hx => by have := mem1 x hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..)) S init _ _ hS
      (fun x hx h => absurd h (by have := mem1 x hx; omega)) (fun nodes c1 h1 => ?_) cache hfresh
    refine V_heapSegN secret z hz first index coord hc hidx pads f _ _ l2
      (fun x hx => ⟨fun _ => hf, fun h => absurd (mem2 x hx) h⟩)
      (fun x hx => by have := mem2 x hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..))
      (fun c' x => S c' x ∧ ¬ (c' = coord ∧ x ∈ (List.range' (8 + 8) 112).reverse)) nodes _ _
      (fun c' x hx => hS c' x hx.1)
      (fun x hx hg => ⟨hin x hg, fun he => by have := mem1 x he.2; omega⟩) (fun nodes2 c2 h2 => ?_) c1 h1
    refine V_heapSegN secret z hz first index coord hc hidx pads z _ _ l3
      (fun x hx => ⟨fun h => absurd h (by have := mem3 x hx; omega), fun _ => le_rfl⟩)
      (fun x hx => by have := mem3 x hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..))
      (fun c' x => (S c' x ∧ ¬ (c' = coord ∧ x ∈ (List.range' (8 + 8) 112).reverse)) ∧
        ¬ (c' = coord ∧ x ∈ (List.range' 8 8).reverse)) nodes2 _ _
      (fun c' x hx => hS c' x hx.1.1)
      (fun x hx hg => absurd hg (by have := mem3 x hx; omega)) (fun nodes3 c3 h3 => ?_) c2 h2
    exact hnext nodes3 c3 (h3.mono fun c' x hx => ⟨⟨⟨hx.1, fun he => hx.2 he.1⟩, fun he => hx.2 he.1⟩,
      fun he => hx.2 he.1⟩)
  unfold sharedHeap
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (126 : Nat) = 6 + (8 + 112) from rfl]
    exact key 2 6 rfl le_rfl _
  · simp only [↓reduceIte]
    rw [show (124 : Nat) = 4 + (8 + 112) from rfl]
    exact key 4 4 rfl (by omega) _


/-- The moment bound of one coordinate before its continuation `B`. -/
noncomputable def CB (z : ℝ≥0∞) (first : Bool) (f B : ℝ≥0∞) : ℝ≥0∞ :=
  z ^ 27 * (z ^ 3328 * (z ^ 112 * (f ^ 8 * (z ^ (if first then 4 else 6) * B))))

theorem V_buildSharedCoordinate {β : Type} (secret : BitVec 256) (z f : ℝ≥0∞) (hz : 1 ≤ z) (first : Bool)
    (index coord : Nat) (hc : coord < 9) (hidx : index < 2 ^ 31) (selected : Child) (word : Rank)
    (pads : Nat → PairRoot) (hf : FacF z coord f) (S : Nat → Nat → Prop) (hS : GroundSet index S)
    (hin : ∀ h, 8 ≤ h ∧ h < 16 → S coord h) (next : Array Digest × List Digest → M β) (B : ℝ≥0∞)
    (hnext : ∀ a cache, FreshF index (fun c' x => S c' x ∧ c' ≠ coord) cache → V secret z (next a) cache ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    V secret z (buildSharedCoordinate first index coord selected word pads >>= next) cache ≤ CB z first f B := by
  unfold buildSharedCoordinate CB
  simp only [bind_assoc]
  refine V_plainF secret z hz (ClaudeWCT.WCT9.ftsBound_ftsCoefs index coord hc) (notF_ftsCoefs hS coord) _ _
    (fun coefs c1 h1 => ?_) cache hfresh
  have hb : Bound (ClaudeWCT.WCT9.FtsQuery index) (fun _ => True) 3328 ((List.range 128).foldlM
      (fun (state : List Digest × List Digest) j => do
        let (root, values) ← ClaudeWCT.WCT9.buildChildH (128 + j) index coord (rawChild first j) word coefs
          (pads (j / 64)).1
        pure (state.1 ++ [root], if j = selected.val then values else state.2)) ([], [])) :=
    Bound.foldlM_range_le 128 _ (fun _ _ => True) (fun _ => 26) ([], [])
      trivial (fun j hj state _ => (ClaudeWCT.WCT9.ftsBound_buildChildH index (128 + j) coord (rawChild first j) word
        coefs (pads (j / 64)).1 hc (rawChild_lt first j hj)).bind' (l := 0)
        (fun child _ => .pure _ 0 trivial) (by simp [ClaudeWCT.WCT9.childCost])) (fun _ _ => trivial) (by simp)
  refine V_plainF secret z hz hb (notF_children hS first coord word selected pads coefs) _ _
    (fun state c2 h2 => ?_) c1 h1
  exact V_sharedHeap secret z f hz first index coord hc hidx pads hf state.1 S hS hin _ B
    (fun nodes c3 h3 => by simpa only [pure_bind] using hnext (nodes, state.2) c3 h3) c2 h2

/-- The ground positions of the coordinates `≥ k`. -/
def Above (k : Nat) (c h : Nat) : Prop := k ≤ c ∧ c < 9 ∧ 8 ≤ h ∧ h < 16

theorem groundSet_above (k : Nat) {index : Nat} (hidx : index < 2 ^ 31) : GroundSet index (Above k) :=
  fun _ _ h => ⟨h.2.1, hidx, h.2.2.1, h.2.2.2⟩

theorem V_buildPair {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (hz : 1 ≤ z) (index pair : Nat)
    (hidx : index < 2 ^ 31) (hp : pair < 4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank) (prev : PairRoot)
    (fa fb : ℝ≥0∞) (ha : FacF z (2 * pair) fa) (hb : FacF z (2 * pair + 1) fb)
    (next : PairOpening × PairRoot → M β) (B : ℝ≥0∞)
    (hnext : ∀ a cache, FreshF index (Above (2 * pair + 2)) cache → V secret z (next a) cache ≤ B)
    (cache : RCache) (hfresh : FreshF index (Above (2 * pair)) cache) :
    V secret z (buildPair index pair s aWord bWord prev >>= next) cache ≤ CB z true fa (CB z false fb B) := by
  unfold buildPair
  simp only [bind_assoc]
  refine V_buildSharedCoordinate secret z fa hz true index (2 * pair) (by omega) hidx (firstChild s) aWord
    (fun _ => prev) ha (Above (2 * pair))
    (groundSet_above _ hidx) (fun h hh => ⟨le_rfl, by omega, hh⟩) _ _ (fun a c1 h1 => ?_) cache hfresh
  refine V_buildSharedCoordinate secret z fb hz false index (2 * pair + 1) (by omega) hidx (secondChild s) bWord
    (nodesPair a.1) hb
    (Above (2 * pair + 1)) (groundSet_above _ hidx) (fun h hh => ⟨le_rfl, by omega, hh⟩) _ _
    (fun b c2 h2 => ?_) c1 (h1.mono fun c' x hx => ⟨⟨by have := hx.1; omega, hx.2.1, hx.2.2⟩, by have := hx.1; omega⟩)
  simp only [pure_bind]
  exact hnext _ c2 (h2.mono fun c' x hx => ⟨⟨by have := hx.1; omega, hx.2.1, hx.2.2⟩, by have := hx.1; omega⟩)

theorem V_buildSingleton {β : Type} (secret : BitVec 256) (z f : ℝ≥0∞) (hz : 1 ≤ z) (index : Nat)
    (hidx : index < 2 ^ 31) (selected : Child) (word : Rank) (prev : PairRoot) (hf : FacF z 8 f)
    (next : SingletonOpening × PairRoot → M β) (B : ℝ≥0∞)
    (hnext : ∀ a cache, V secret z (next a) cache ≤ B)
    (cache : RCache) (hfresh : FreshF index (Above 8) cache) :
    V secret z (buildSingleton index selected word prev >>= next) cache ≤ CB z false f B := by
  unfold buildSingleton
  simp only [bind_assoc]
  refine V_buildSharedCoordinate secret z f hz false index 8 (by omega) hidx selected word (fun _ => prev) hf (Above 8)
    (groundSet_above _ hidx) (fun h hh => ⟨le_rfl, by omega, hh⟩) _ _ (fun a c1 _ => ?_) cache hfresh
  simp only [pure_bind]
  exact hnext _ c1

/-- **The FTS forest moment**: with every ground trial of the forest `index` fresh, `buildForest` costs at most the
fixed part times the 72 ground factors (`CB` nests the nine coordinates). -/
theorem V_buildForest (secret : BitVec 256) (z : ℝ≥0∞) (hz : 1 ≤ z) (index : Nat) (hidx : index < 2 ^ 31)
    (selected : ForestSelection) (words : ForestWords) (fc : Nat → ℝ≥0∞) (hf : ∀ c, c < 9 → FacF z c (fc c))
    (cache : RCache) (hfresh : FreshF index (Above 0) cache) :
    V secret z (buildForest index selected words) cache ≤
      CB z true (fc 0) (CB z false (fc 1) (CB z true (fc 2) (CB z false (fc 3) (CB z true (fc 4)
        (CB z false (fc 5) (CB z true (fc 6) (CB z false (fc 7) (CB z false (fc 8) 1)))))))) := by
  rw [← bind_pure (buildForest index selected words)]
  unfold buildForest
  have hfr : List.finRange 4 = [0, 1, 2, 3] := by decide
  rw [hfr]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_assoc, pure_bind]
  refine V_buildPair secret z hz index 0 hidx (by decide) _ _ _ _ _ _ (hf 0 (by decide)) (hf 1 (by decide)) _ _
    (fun a c1 h1 => ?_) cache hfresh
  refine V_buildPair secret z hz index 1 hidx (by decide) _ _ _ _ _ _ (hf 2 (by decide)) (hf 3 (by decide)) _ _
    (fun a c2 h2 => ?_) c1 h1
  refine V_buildPair secret z hz index 2 hidx (by decide) _ _ _ _ _ _ (hf 4 (by decide)) (hf 5 (by decide)) _ _
    (fun a c3 h3 => ?_) c2 h2
  refine V_buildPair secret z hz index 3 hidx (by decide) _ _ _ _ _ _ (hf 6 (by decide)) (hf 7 (by decide)) _ _
    (fun a c4 h4 => ?_) c3 h3
  refine V_buildSingleton secret z (fc 8) hz index hidx _ _ _ (hf 8 (by decide)) _ 1 (fun _ _ => ?_) c4 h4
  simp only [V_pure, le_refl]

theorem CB_eq (z f B : ℝ≥0∞) (first : Bool) :
    CB z first f B = z ^ (if first then 3471 else 3473) * f ^ 8 * B := by
  unfold CB
  cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The forest moment in closed form: `z^31249 · Π_c f_c^8`. -/
theorem forestCB_eq (z : ℝ≥0∞) (fc : Nat → ℝ≥0∞) :
    CB z true (fc 0) (CB z false (fc 1) (CB z true (fc 2) (CB z false (fc 3) (CB z true (fc 4)
      (CB z false (fc 5) (CB z true (fc 6) (CB z false (fc 7) (CB z false (fc 8) 1)))))))) =
      z ^ 31249 * (fc 0 * fc 1 * fc 2 * fc 3 * fc 4 * fc 5 * fc 6 * fc 7 * fc 8) ^ 8 := by
  simp only [CB_eq, Bool.false_eq_true, ↓reduceIte]
  ring


/-! ## Freshness of the FTS trials before the forest (keygen, MAC, nonce, digest search) -/

open SigGolfCandidate.T3.Freshness (avoids_foldlM avoids_mapM avoids_map avoids_shortHash_of_ne
  avoids_privateHash_of_ne hasTag_privateNonce)
open SigGolfCandidate.T3.QuerySpace (queryHeader_leafInput)

/-- The input carries the FTS node header of `(coord, index, heap)`. -/
def FQ (coord index heap : Nat) (x : HashInput) : Prop :=
  queryHeader x = bytesLE 16 (wctNodeHeader coord index heap)

theorem fq_ne {input target : HashInput} {hdr : BitVec 128} {coord index heap : Nat}
    (h : queryHeader input = bytesLE 16 hdr) (hn : hdr ≠ wctNodeHeader coord index heap)
    (ht : FQ coord index heap target) : input ≠ target := by
  rintro rfl
  exact hn (bytesLE_injective (h.symm.trans ht))

theorem hasTag_ne_fts {tag : Nat} {input target : HashInput} (hi : HasTag tag input) {coord index heap : Nat}
    (hp : FP coord index heap) (ht : FQ coord index heap target) (htag : tag % 256 ≠ 254 := by decide) :
    input ≠ target := by
  obtain ⟨l, tr, p, ix, h⟩ := hi
  exact fq_ne h (fun he => ClaudeWCT.WCT9.wctNodeHeader_ne_header hp.1 index heap tag l tr p ix htag he.symm) ht

theorem chainHeader_ne_fts (l : Layer) (t lf i step : Nat) (_hs : step < 7) {coord index heap : Nat}
    (_hp : FP coord index heap) : chainHeader l t lf i step ≠ wctNodeHeader coord index heap :=
  fun he => ClaudeWCT.WCT9.wctNodeHeader_ne_chainHeader coord index heap l t lf i step he.symm

theorem leafTweak_ne_fts (l : Layer) (t lf : Nat) {coord index heap : Nat} (hp : FP coord index heap) :
    leafTweak l t lf ≠ wctNodeHeader coord index heap :=
  fun he => ClaudeWCT.WCT9.wctNodeHeader_ne_leafTweak hp.1 index heap l t lf he.symm

theorem digestHeader_ne_fts (c : BitVec 32) {coord index heap : Nat} (_hp : FP coord index heap) :
    digestHeader c ≠ wctNodeHeader coord index heap :=
  fun he => ClaudeWCT.WCT9.wctNodeHeader_ne_digestHeader coord index heap c he.symm

theorem topTweak_ne_fts (heap' : Nat) {coord index heap : Nat} (hp : FP coord index heap) :
    nodeTweak 3 0 0 heap' ≠ wctNodeHeader coord index heap := by
  intro he
  have hn : FtsNew heap := ⟨hp.2.2.1, by have := hp.2.2.2; omega⟩
  have ht := congrArg tweakTag he
  rw [nodeTweak_top_tag, ClaudeWCT.WCT9.wctNodeHeader_tweakTag hp.1, if_pos hn] at ht
  rcases topNodeWord_small_or_special heap' with hs | hs | hs
  · omega
  · rw [hs] at ht
    norm_num at ht
  · rw [hs] at ht
    norm_num at ht

section FAvoid
variable (secret : BitVec 256) (target : HashInput) (coord index heap : Nat) (ht : FQ coord index heap target)
  (hp : FP coord index heap)
include ht hp

theorem fav_privatePair (tag l t p i : Nat) (htag : tag % 256 ≠ 254 := by decide) :
    Avoids secret target (privatePair tag l t p i) := by
  unfold privatePair
  apply avoids_bind
  · exact avoids_privateHash_of_ne secret target _
      (hasTag_ne_fts (hasTag_privatePair ..) hp ht htag)
  · intro _; exact avoids_pure _ _ _

theorem fav_privateMac (region : Region) : Avoids secret target (privateMac region) := by
  unfold privateMac privateMacKey
  simp only [bind_assoc, pure_bind]
  exact avoids_bind (avoids_privateHash_of_ne secret target _
      (hasTag_ne_fts (hasTag_privatePair secret 14 0 0 0 0) hp ht)) fun _ =>
    avoids_bind (avoids_privateHash_of_ne secret target _
      (hasTag_ne_fts (hasTag_privatePair secret 14 0 0 0 1) hp ht)) fun _ =>
    avoids_pure _ _ _

theorem fav_privateNonce (message : Message) : Avoids secret target (privateNonce message) := by
  unfold privateNonce
  apply avoids_bind
  · exact avoids_privateHash_of_ne secret target _
      (hasTag_ne_fts (hasTag_privateNonce ..) hp ht)
  · intro _; exact avoids_pure _ _ _

theorem fav_topChain (leaf i start count : Nat) (value : Digest) (hs : start + count ≤ 7) :
    Avoids secret target (topChain leaf i start count value) := by
  unfold topChain
  refine ClaudeWCT.W9.T3.LayerBudget.Envelopes.avoids_foldlM_range'_inv _ (fun _ _ => True) count start
    (fun k a hk hk' _ => ⟨?_, fun _ _ => trivial⟩) value trivial
  unfold projHash
  apply avoids_bind
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    have hh : queryHeader (pad64 (topChainInput leaf i k a)) = bytesLE 16 (chainHeader 0 0 leaf i k) := by
      unfold topChainInput
      split
      · simpa only [List.append_assoc] using
          queryHeader_padded (bytesLE 16 a) (zero16 ++ zero16) (bytesLE_length ..) (chainHeader 0 0 leaf i k)
      · simpa only [SigGolfCandidate.T3.chainInput, List.append_assoc] using
          queryHeader_padded zero16 (zero16 ++ bytesLE 16 a) (by simp [zero16]) (chainHeader 0 0 leaf i k)
    exact fq_ne hh (chainHeader_ne_fts 0 0 leaf i k (by omega) hp) ht
  · intro _; exact avoids_pure _ _ _

theorem fav_leafHash (l : Layer) (t lf : Nat) (ends : List Digest) : Avoids secret target (SigGolfCandidate.T3.leafHash l t lf ends) := by
  unfold SigGolfCandidate.T3.leafHash
  apply avoids_shortHash_of_ne
  exact fq_ne (queryHeader_leafInput ..) (leafTweak_ne_fts l t lf hp) ht

theorem fav_topPairsFrom (first start : Nat) (init : List Digest) :
    Avoids secret target (topPairsFrom first start init) := by
  unfold topPairsFrom topSeedPair
  exact avoids_foldlM _ _ _ _ (fun acc j => avoids_bind (fav_privatePair secret target coord index heap ht hp 0 0 0 _ 0)
    (fun _ => avoids_pure _ _ _)) _

theorem fav_buildLeafTopC (leaf : Nat) (coefs : List Digest) (signatureOnly : Bool) :
    Avoids secret target (buildLeafTopC leaf coefs [] signatureOnly) := by
  have hmax : ∀ i, maxDigit 0 i ≤ 7 := fun i => by unfold maxDigit; split_ifs <;> omega
  unfold buildLeafTopC
  apply avoids_bind
  · apply avoids_foldlM
    intro state i
    refine avoids_bind (fav_topChain secret target coord index heap ht hp _ _ _ _ _ (by simp)) (fun value => ?_)
    split
    · exact avoids_pure _ _ _
    · exact avoids_bind (fav_topChain secret target coord index heap ht hp _ _ _ _ _ (by simp [hmax]))
        (fun _ => avoids_pure _ _ _)
  · intro state
    split
    · exact avoids_pure _ _ _
    · exact avoids_bind (fav_leafHash secret target coord index heap ht hp _ _ _ _) (fun _ => avoids_pure _ _ _)

theorem fav_topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) :
    Avoids secret target (topTreeStep st leaf) := by
  unfold topTreeStep topFamilyCoefs
  refine avoids_bind ?_ (fun cc => avoids_bind (fav_buildLeafTopC secret target coord index heap ht hp _ _ _)
    (fun _ => avoids_pure _ _ _))
  split
  · unfold topCoefsK
    exact avoids_bind (fav_topPairsFrom secret target coord index heap ht hp _ _ _) (fun _ => avoids_pure _ _ _)
  · exact avoids_pure _ _ _

theorem fav_topNodeHashN (heap' n : Nat) (left right : Digest) :
    Avoids secret target (topNodeHashN heap' n left right) := by
  unfold topNodeHashN projHash
  apply avoids_bind
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    apply fq_ne _ (topTweak_ne_fts heap' hp) ht
    simpa only [topNodeInput, List.append_assoc] using
      (queryHeader_padded (bytesLE 16 left) (nonceBytes n ++ bytesLE 16 right) (bytesLE_length ..)
        (nodeTweak 3 0 0 heap'))
  · intro _; exact avoids_pure _ _ _

theorem fav_topNonceSearch (h heap' : Nat) (left right : Digest) :
    ∀ fuel n, Avoids secret target (topNonceSearch h heap' left right fuel n)
  | 0, n => by
      unfold topNonceSearch
      exact avoids_bind (fav_topNodeHashN secret target coord index heap ht hp _ _ _ _) fun _ => avoids_pure _ _ _
  | fuel+1, n => by
      unfold topNonceSearch
      refine avoids_bind (fav_topNodeHashN secret target coord index heap ht hp _ _ _ _) fun _ => ?_
      split
      · exact avoids_pure _ _ _
      · exact fav_topNonceSearch h heap' left right fuel (n+1)

theorem fav_buildTopLevel (level : Nat) (nodes : List Digest) : Avoids secret target (buildTopLevel level nodes) := by
  unfold buildTopLevel
  refine avoids_mapM _ _ _ _ fun i => ?_
  split
  · unfold nodeHash projHash
    apply avoids_bind
    · apply (allQueriesSatisfy_query_iff _ _).mpr
      apply fq_ne _ (topTweak_ne_fts (2 ^ (12 - level) + i) hp) ht
      simpa only [List.append_assoc] using
        (queryHeader_padded (bytesLE 16 (nodes.getD (2*i) 0)) (zero16 ++ bytesLE 16 (nodes.getD (2*i+1) 0))
          (bytesLE_length ..) (nodeTweak 3 0 0 (2 ^ (12 - level) + i)))
    · intro _; exact avoids_pure _ _ _
  · exact avoids_map _ (fav_topNonceSearch secret target coord index heap ht hp _ _ _ _ _ _)

theorem fav_buildTopLevels (leaves : List Digest) : Avoids secret target (buildTopLevels leaves) := by
  unfold buildTopLevels
  exact avoids_foldlM _ _ _ _ (fun levels level => avoids_bind
    (fav_buildTopLevel secret target coord index heap ht hp _ _) fun _ => avoids_pure _ _ _) _

theorem fav_buildTopTree : Avoids secret target buildTopTree := by
  unfold buildTopTree
  exact avoids_bind (avoids_foldlM _ _ _ _ (fun st leaf => fav_topTreeStep secret target coord index heap ht hp st leaf) _)
    fun st => fav_buildTopLevels secret target coord index heap ht hp _

section
-- As in Merge054's `gav_keygen`: an opaque `maskedLevel` keeps the `refine` unification cheap (106 s → ~1 s).
attribute [local irreducible] SigGolfCandidate.T3.keygenPayload SigGolfCandidate.T3.maskedLevel
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 2000000 in
theorem fav_keygen : Avoids secret target SigGolfCandidate.T3.keygen := by
  unfold SigGolfCandidate.T3.keygen SigGolfCandidate.T3.keygenPayload
  refine avoids_bind (avoids_bind (fav_buildTopTree secret target coord index heap ht hp) fun levels =>
    avoids_bind (avoids_mapM _ _ _ _ fun level => ?_) fun _ => avoids_pure _ _ _) fun pr => ?_
  · unfold maskedLevel
    refine avoids_bind (avoids_mapM _ _ _ _ fun pair => ?_) fun _ => avoids_pure _ _ _
    unfold pairedMask
    exact avoids_bind (avoids_pure _ _ _) fun _ => avoids_pure _ _ _
  · exact avoids_bind (fav_privateMac secret target coord index heap ht hp _) fun _ => avoids_pure _ _ _
end

theorem fav_digestSearch (rho : Digest) (message : Message) :
    ∀ fuel counter, Avoids secret target
      (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message counter fuel)
  | 0, counter => by unfold SigGolfCandidate.Research.SharedForest.sharedDigestSearch; exact avoids_pure _ _ _
  | fuel+1, counter => by
      unfold SigGolfCandidate.Research.SharedForest.sharedDigestSearch
      refine avoids_bind ?_ fun output => ?_
      · unfold digest publicHash
        apply (allQueriesSatisfy_query_iff _ _).mpr
        change pad64 (digestInput rho message _) ≠ target
        exact fq_ne (queryHeader_padded _ _ (bytesLE_length ..) _)
          (digestHeader_ne_fts _ hp) ht
      · split
        · exact avoids_pure _ _ _
        · exact fav_digestSearch rho message fuel (counter+1)


end FAvoid

/-- Every FTS ground trial is fresh. -/
def AllFFresh (cache : RCache) : Prop :=
  ∀ coord index heap, FP coord index heap → ∀ n l r, cache (fTrial coord index heap n l r) = none

@[simp] theorem allFFresh_empty : AllFFresh ∅ := fun _ _ _ _ _ _ _ => rfl

theorem preserves_allF {α : Type} (secret : BitVec 256) (program : M α)
    (h : ∀ target coord index heap, FQ coord index heap target → FP coord index heap → Avoids secret target program)
    (cache : RCache) (hc : AllFFresh cache) (result : α × RCache)
    (hr : result ∈ support (roRun secret program cache)) : AllFFresh result.2 := by
  intro coord index heap hp n l r
  rw [preserves secret _ program (h _ coord index heap (fTrial_header coord index heap n l r) hp) cache result hr]
  exact hc coord index heap hp n l r

theorem keygen_allFFresh (secret : BitVec 256) (result : (Digest × Cache) × RCache)
    (hr : result ∈ support (roRun secret SigGolfCandidate.T3.keygen ∅)) : AllFFresh result.2 :=
  preserves_allF secret SigGolfCandidate.T3.keygen (fun target coord index heap ht hp => fav_keygen secret target coord index heap ht hp)
    ∅ allFFresh_empty result hr

theorem privateMac_allFFresh (secret : BitVec 256) (region : Region) (cache : RCache) (hc : AllFFresh cache)
    (result : _ × RCache) (hr : result ∈ support (roRun secret (privateMac region) cache)) : AllFFresh result.2 :=
  preserves_allF secret _ (fun target coord index heap ht hp => fav_privateMac secret target coord index heap ht hp region)
    cache hc result hr

theorem privateNonce_allFFresh (secret : BitVec 256) (message : Message) (cache : RCache) (hc : AllFFresh cache)
    (result : _ × RCache) (hr : result ∈ support (roRun secret (privateNonce message) cache)) : AllFFresh result.2 :=
  preserves_allF secret _ (fun target coord index heap ht hp => fav_privateNonce secret target coord index heap ht hp message)
    cache hc result hr

theorem digestSearch_allFFresh (secret : BitVec 256) (rho : Digest) (message : Message) (counter fuel : Nat)
    (cache : RCache) (hc : AllFFresh cache) (result : _ × RCache)
    (hr : result ∈ support (roRun secret
      (SigGolfCandidate.Research.SharedForest.sharedDigestSearch rho message counter fuel) cache)) :
    AllFFresh result.2 :=
  preserves_allF secret _ (fun target coord index heap ht hp =>
    fav_digestSearch secret target coord index heap ht hp rho message fuel counter) cache hc result hr

theorem freshF_of_all {index : Nat} (hidx : index < 2 ^ 31) {cache : RCache} (h : AllFFresh cache) :
    FreshF index (Above 0) cache :=
  fun c x hs n l r => h c index x ⟨hs.2.1, hidx, hs.2.2.1, hs.2.2.2⟩ n l r

end ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
