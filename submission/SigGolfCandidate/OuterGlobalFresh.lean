import SigGolfCandidate.OuterForestBudget
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterGlobalFresh
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness SigGolfCandidate.T3.QuerySpace
open ClaudeWCT.WCT9
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh (fTrial fTrial_header)
abbrev FP := OuterGroundAvoid.OP
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

theorem chainHeader_ne_fts (l : Layer) (t lf i step : Nat) (hs : step < 7) {coord index heap : Nat}
    (_hp : FP coord index heap) : chainHeader l t lf i step ≠ wctNodeHeader coord index heap :=
  fun he => ClaudeWCT.WCT9.wctNodeHeader_ne_chainHeader coord index heap l t lf i step hs he.symm

theorem leafTweak_ne_fts (l : Layer) (t lf : Nat) {coord index heap : Nat} (hp : FP coord index heap) :
    leafTweak l t lf ≠ wctNodeHeader coord index heap :=
  fun he => ClaudeWCT.WCT9.wctNodeHeader_ne_leafTweak hp.1 index heap l t lf he.symm

theorem digestHeader_ne_fts (c : BitVec 32) {coord index heap : Nat} (_hp : FP coord index heap) :
    digestHeader c ≠ wctNodeHeader coord index heap :=
  fun he => ClaudeWCT.WCT9.wctNodeHeader_ne_digestHeader coord index heap c he.symm

theorem topTweak_ne_fts {coord index heap : Nat} (heap' : Nat) (hp : FP coord index heap) :
    nodeTweak 3 0 0 heap'≠wctNodeHeader coord index heap :=
  OuterGroundFresh.header_ne_top coord index heap heap' hp.1

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

theorem freshF_of_all {index : Nat} (hi : index<2^31) {cache : RCache} (h : AllFFresh cache) :
    ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.FreshF index (OuterForestBudget.AllAbove 0) cache :=
  fun c x hs n l r => h c index x (OuterForestBudget.outerSet_above 0 index hi c x hs) n l r

#print axioms keygen_allFFresh
#print axioms digestSearch_allFFresh
#print axioms freshF_of_all
end OuterGlobalFresh
