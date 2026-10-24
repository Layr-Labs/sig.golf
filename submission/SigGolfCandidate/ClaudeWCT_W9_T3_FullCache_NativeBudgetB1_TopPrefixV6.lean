import SigGolfCandidate.ClaudeWCT_W9_T3_FullCache_NativeBudgetB1_ExpandExcess

/-! # `TopPrefixOK` for the img-v6 keygen spec (4-leaf top families, carry; r3-lean-topbytes)

The top-tree leaf loop (`topTreeStep`: family coefficients `topCoefsK`, then `buildLeafTopC`) makes only private pair,
chain and leaf-hash queries, so it avoids the root children's trials; its 4096 roots come from
`bound_topTreeStep` (keygen sub-porter, T3/Proofs). -/

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Freshness (Avoids avoids_pure avoids_bind avoids_foldlM)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

section V6Leaves
variable (secret : BitVec 256) (target : HashInput) (heap : Nat) (ht : TopQ heap target) (h23 : heap = 2 ∨ heap = 3)
include ht h23

theorem tav_topPairsFrom (first start : Nat) (init : List Digest) :
    Avoids secret target (topPairsFrom first start init) := by
  unfold topPairsFrom topSeedPair
  exact avoids_foldlM _ _ _ _ (fun acc j => avoids_bind (tav_privatePair secret target heap ht h23 0 0 0 _ 0)
    (fun _ => avoids_pure _ _ _)) _

theorem tav_topCoefsK (f : Nat) (carry : Digest) : Avoids secret target (topCoefsK f carry) := by
  unfold topCoefsK
  exact avoids_bind (tav_topPairsFrom secret target heap ht h23 _ _ _) (fun _ => avoids_pure _ _ _)

theorem tav_buildLeafTopC (leaf : Nat) (coefs : List Digest) (digits : List Nat) (signatureOnly : Bool) :
    Avoids secret target (buildLeafTopC leaf coefs digits signatureOnly) := by
  unfold buildLeafTopC
  apply avoids_bind
  · apply avoids_foldlM
    intro state i
    refine avoids_bind (tav_topChain secret target heap ht h23 _ _ _ _ _) (fun value => ?_)
    split
    · exact avoids_pure _ _ _
    · exact avoids_bind (tav_topChain secret target heap ht h23 _ _ _ _ _) (fun _ => avoids_pure _ _ _)
  · intro state
    split
    · exact avoids_pure _ _ _
    · exact avoids_bind (tav_leafHash secret target heap ht h23 _ _ _ _) (fun _ => avoids_pure _ _ _)

theorem tav_topTreeStep (st : List Digest × List Digest × Digest) (leaf : Nat) :
    Avoids secret target (topTreeStep st leaf) := by
  unfold topTreeStep topFamilyCoefs
  refine avoids_bind ?_ (fun cc => avoids_bind (tav_buildLeafTopC secret target heap ht h23 _ _ _ _)
    (fun _ => avoids_pure _ _ _))
  split
  · exact tav_topCoefsK secret target heap ht h23 _ _
  · exact avoids_pure _ _ _

end V6Leaves

theorem topPrefixOK (secret : BitVec 256) : SigGolfCandidate.Research.SharedExpansionV6.TopPrefixOK secret := by
  refine ⟨_, (List.range (2 ^ height 0)).foldlM topTreeStep ([], [], 0), Prod.fst, topLeavesCost, rfl, ?_⟩
  intro heap target ht h23
  refine Bound.and_of_allQueries
    (avoids_foldlM _ _ _ _ (fun st leaf => tav_topTreeStep secret target heap ht h23 st leaf) _) ?_
  refine ((Bound.foldlM_range 4096 _ (fun i (st : List Digest × List Digest × Digest) => st.1.length = i)
    topLeafCost ([], [], 0) rfl (fun leaf _ st hst => bound_topTreeStep st leaf hst)).mono
      (fun _ h => h) (fun st h => by simpa using h)).mono_k ?_
  rw [topLeaves_sum]

end ClaudeWCT.W9.T3.TopMoment
