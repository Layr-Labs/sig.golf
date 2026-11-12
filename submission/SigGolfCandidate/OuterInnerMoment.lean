import SigGolfCandidate.OuterGroundAvoid
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterInnerMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh

def innerHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) (leaves : List Digest) : M (Array Digest) :=
  (List.range' 4 124).reverse.foldlM (heapStep first index coord pads)
    ((List.replicate 128 (0 : Digest)++leaves).toArray)

theorem V_innerHeap {β : Type} (secret : BitVec 256) (z f g : ℝ≥0∞) (hz : 1 ≤ z) (first : Bool) (index coord : Nat)
    (hc : coord < 9) (hidx : index < 2 ^ 31) (pads : Nat → PairRoot) (hf : FacF z coord f) (hg : FacG z coord g)
    (leaves : List Digest)
    (S : Nat → Nat → Prop) (hS : GroundSet index S) (hin : ∀ h, ClaudeWCT.WCT9.ftsGround coord h → S coord h)
    (next : Array Digest → M β) (B : ℝ≥0∞)
    (hnext : ∀ a cache, FreshF index (fun c' x => S c' x ∧ c' ≠ coord) cache → V secret z (next a) cache ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    V secret z (innerHeap first index coord pads leaves >>= next) cache ≤
      z ^ 96 * (g ^ 16 * (f ^ 8 * (z ^ 4 * B))) := by
  have hhm : ∀ (a m : Nat), a + m = 8 → 2 ≤ a →
      (List.range' a (m + (8 + (16 + 96)))).reverse =
        (List.range' (8 + 8 + 16) 96).reverse ++ ((List.range' (8 + 8) 16).reverse ++
          ((List.range' 8 8).reverse ++ (List.range' a m).reverse)) := by
    intro a m ham _
    rw [← List.range'_append_1 (s := a) (m := m) (n := 8 + (16 + 96)), ham,
      ← List.range'_append_1 (s := 8) (m := 8) (n := 16 + 96),
      ← List.range'_append_1 (s := 8 + 8) (m := 16) (n := 96)]
    simp only [List.reverse_append, List.append_assoc]
  have ng : ∀ x, (32 ≤ x ∨ x < 8) → ¬ ClaudeWCT.WCT9.ftsGround coord x := fun x hx h => by
    unfold ClaudeWCT.WCT9.ftsGround at h; omega
  have key : ∀ (a m : Nat), a + m = 8 → 2 ≤ a → ∀ init : Array Digest,
      V secret z (((List.range' a (m + (8 + (16 + 96)))).reverse.foldlM (heapStep first index coord pads) init) >>= next)
        cache ≤ z ^ 96 * (g ^ 16 * (f ^ 8 * (z ^ m * B))) := by
    intro a m ham ha init
    rw [hhm a m ham ha]
    simp only [List.foldlM_append, bind_assoc]
    have mem0 : ∀ x ∈ (List.range' (8 + 8 + 16) 96).reverse, 32 ≤ x ∧ x < 128 := fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx; omega
    have mem1 : ∀ x ∈ (List.range' (8 + 8) 16).reverse, 16 ≤ x ∧ x < 32 := fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx; omega
    have mem2 : ∀ x ∈ (List.range' 8 8).reverse, 8 ≤ x ∧ x < 16 := fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx; omega
    have mem3 : ∀ x ∈ (List.range' a m).reverse, a ≤ x ∧ x < 8 := fun x hx => by
      rw [List.mem_reverse, List.mem_range'_1] at hx; omega
    have l0 : ((List.range' (8 + 8 + 16) 96).reverse).length = 96 := by simp
    have l1 : ((List.range' (8 + 8) 16).reverse).length = 16 := by simp
    have l2 : ((List.range' 8 8).reverse).length = 8 := by simp
    have l3 : ((List.range' a m).reverse).length = m := by simp
    refine V_heapSegN secret z hz first index coord hc hidx pads z _ _ l0
      (fun x hx => ⟨fun h => absurd h (ng x (by have := mem0 x hx; omega)), fun _ => le_rfl⟩)
      (fun x hx => by have := mem0 x hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..)) S init _ _ hS
      (fun x hx h => absurd h (ng x (by have := mem0 x hx; omega))) (fun nodes c1 h1 => ?_) cache hfresh
    refine V_heapSegN secret z hz first index coord hc hidx pads g _ _ l1
      (fun x hx => ⟨fun h => ?_, fun _ => hg.2⟩)
      (fun x hx => by have := mem1 x hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..))
      (fun c' x => S c' x ∧ ¬ (c' = coord ∧ x ∈ (List.range' (8 + 8 + 16) 96).reverse)) nodes _ _
      (fun c' x hx => hS c' x hx.1)
      (fun x hx hgx => ⟨hin x hgx, fun he => by have := mem0 x he.2; have := mem1 x hx; omega⟩)
      (fun nodes2 c2 h2 => ?_) c1 h1
    · have hm := mem1 x hx
      have hc4 : coord < 4 := by unfold ClaudeWCT.WCT9.ftsGround at h; omega
      rw [ftsZeroBits_ground16 hm]
      exact hg.1 hc4
    refine V_heapSegN secret z hz first index coord hc hidx pads f _ _ l2
      (fun x hx => ⟨fun _ => by rw [ftsZeroBits_ground (mem2 x hx)]; exact hf,
        fun h => absurd (ClaudeWCT.WCT9.ftsGround_of_low (mem2 x hx)) h⟩)
      (fun x hx => by have := mem2 x hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..))
      (fun c' x => (S c' x ∧ ¬ (c' = coord ∧ x ∈ (List.range' (8 + 8 + 16) 96).reverse)) ∧
        ¬ (c' = coord ∧ x ∈ (List.range' (8 + 8) 16).reverse)) nodes2 _ _
      (fun c' x hx => hS c' x hx.1.1)
      (fun x hx hgx => ⟨⟨hin x hgx, fun he => by have := mem0 x he.2; have := mem2 x hx; omega⟩,
        fun he => by have := mem1 x he.2; have := mem2 x hx; omega⟩) (fun nodes3 c3 h3 => ?_) c2 h2
    refine V_heapSegN secret z hz first index coord hc hidx pads z _ _ l3
      (fun x hx => ⟨fun h => absurd h (ng x (by have := mem3 x hx; omega)), fun _ => le_rfl⟩)
      (fun x hx => by have := mem3 x hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..))
      (fun c' x => ((S c' x ∧ ¬ (c' = coord ∧ x ∈ (List.range' (8 + 8 + 16) 96).reverse)) ∧
        ¬ (c' = coord ∧ x ∈ (List.range' (8 + 8) 16).reverse)) ∧ ¬ (c' = coord ∧ x ∈ (List.range' 8 8).reverse))
      nodes3 _ _
      (fun c' x hx => hS c' x hx.1.1.1)
      (fun x hx hgx => absurd hgx (ng x (by have := mem3 x hx; omega))) (fun nodes4 c4 h4 => ?_) c3 h3
    exact hnext nodes4 c4 (h4.mono fun c' x hx => ⟨⟨⟨⟨hx.1, fun he => hx.2 he.1⟩, fun he => hx.2 he.1⟩,
      fun he => hx.2 he.1⟩, fun he => hx.2 he.1⟩)
  unfold innerHeap
  rw [show (124 : Nat)=4+(8+(16+96)) from rfl]
  exact key 4 4 rfl (by omega) _

open SigGolfCandidate.T3M (allQ_pure allQ_bind)
theorem allQ_foldlM_mem {α β : Type} {P : Spec.Domain → Prop} (f : α → β → M α) :
    ∀ (l : List β) (init : α), (∀ a, ∀ b ∈ l, AllQueriesSatisfy (f a b) P) →
      AllQueriesSatisfy (l.foldlM f init) P
  | [], init, _ => by rw [List.foldlM_nil]; exact allQ_pure _
  | b :: l, init, h => by
      rw [List.foldlM_cons]
      exact allQ_bind (h init b (List.mem_cons_self ..)) fun a =>
        allQ_foldlM_mem f l a (fun a' b' hb' => h a' b' (List.mem_cons_of_mem _ hb'))

theorem notF_innerHeap (first : Bool) (index coord : Nat) (pads : Nat → PairRoot) (leaves : List Digest)
    (secret : BitVec 256) (S : Nat → Nat → Prop) (hS : OuterGroundAvoid.OuterSet index S)
    (hc : coord<9) (ho : ∀ c x,S c x→x<4) :
    AllQueriesSatisfy (innerHeap first index coord pads leaves) (NotF secret index S) := by
  unfold innerHeap
  apply allQ_foldlM_mem
  intro nodes heap hh
  have hm : 4≤heap ∧ heap<128 := by
    rw [List.mem_reverse,List.mem_range'_1] at hh
    omega
  unfold heapStep
  exact SigGolfCandidate.T3M.allQ_bind
    (OuterGroundAvoid.notF_sharedNode_external hS first coord heap pads _ _ hc hm.2
      (fun h => by have := ho coord heap h;omega)) (fun _ => SigGolfCandidate.T3M.allQ_pure _)

theorem inner_cost (secret : BitVec 256) (z f g : ℝ≥0∞) (hz : 1≤z) (first : Bool) (index coord : Nat)
    (hc : coord<9) (hi : index<2^31) (pads : Nat → PairRoot) (hf : FacF z coord f) (hg : FacG z coord g)
    (leaves : List Digest) (S : Nat → Nat → Prop) (hS : GroundSet index S)
    (hin : ∀ h,ftsGround coord h→S coord h) (cache : RCache) (hcache : FreshF index S cache) :
    V secret z (innerHeap first index coord pads leaves) cache≤z^96*(g^16*(f^8*z^4)) := by
  have h:=V_innerHeap secret z f g hz first index coord hc hi pads hf hg leaves S hS hin pure 1
    (fun _ _ _ => by simp [V_pure]) cache hcache
  simpa using h

#print axioms inner_cost
#print axioms notF_innerHeap
#print axioms V_innerHeap
end OuterInnerMoment
