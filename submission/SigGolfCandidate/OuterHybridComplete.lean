import SigGolfCandidate.OuterGroundFailure
import SigGolfCandidate.OuterInnerMoment
import SigGolfCandidate.FtsComplete
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridComplete
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
open ClaudeWCT.W9.T3.TopMoment (Ev Ev_bind Ev_pure Ev_le_of_support Ev_publicQuery_fresh Ev_mono Ev_const_le)

def HP (coord index heap : Nat) : Prop := coord<9 ∧ index<2^31 ∧
  (ftsGround coord heap ∨ (heap=2 ∨ heap=3))
theorem HP.heap {coord index heap : Nat} (h : HP coord index heap) : 2≤heap ∧ heap<128 := by
  rcases h.2.2 with hg | h
  · unfold ftsGround at hg;omega
  · omega

def HybridSet (index : Nat) (S : Nat → Nat → Prop) : Prop := ∀ c h,S c h→HP c index h

theorem outerSet_of_hybrid {index : Nat} {S : Nat → Nat → Prop} (hS : HybridSet index S) :
    OuterGroundAvoid.OuterSet index S := by
  intro c h hs
  have hp:=hS c h hs
  exact ⟨hp.1,hp.2.1,hp.heap⟩

theorem trial_ne_hybrid {coord index heap coord' heap' : Nat} (h : FP coord index heap) (h' : HP coord' index heap')
    (hne : ¬(coord'=coord ∧ heap'=heap)) (n m : Nat) (l r l' r' : Digest) :
    fTrial coord' index heap' m l' r'≠fTrial coord index heap n l r :=
  OuterGroundFresh.trial_ne ⟨h.1,h.2.1,by have := h.heap;omega⟩
    ⟨h'.1,h'.2.1,h'.heap.2⟩ hne n m l r l' r'

theorem notF_plain_inner {secret : BitVec 256} {index : Nat} {S : Nat → Nat → Prop}
    (hS : HybridSet index S) (first : Bool) (coord heap : Nat) (pads : Nat → PairRoot) (l r : Digest)
    (hc : coord<9) (hlo : 4≤heap) (hhi : heap<128) (hg : ¬ftsGround coord heap) :
    AllQueriesSatisfy (sharedNode first coord index heap pads l r) (NotF secret index S) := by
  apply OuterGroundAvoid.notF_sharedNode_external (outerSet_of_hybrid hS) first coord heap pads l r hc hhi
  intro hs
  rcases (hS coord heap hs).2.2 with hg' | hout
  · exact hg hg'
  · omega

theorem E_fnode {β : Type} (secret : BitVec 256) (coord index heap : Nat) (hp : FP coord index heap)
    (left right : Digest) (next : Digest → M β) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1)
    (S : Nat → Nat → Prop) (hS : HybridSet index S) (B : ℝ≥0∞)
    (hnext : ∀ v cache, ftsZeroOk coord heap v = true →
      FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) cache → Ev secret (next v) cache F ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) (hin : S coord heap) :
    Ev secret (ftsNodeG coord index heap left right >>= next) cache F ≤ B + fcap (ftsZeroBits coord heap) := by
  have hpres : ∀ (c : RCache) k ans, FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) c →
      FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap))
        (c.cacheQuery (fTrial coord index heap k left right) ans) := by
    intro c k ans hc x y hxy n l r
    exact (QueryCache.cacheQuery_of_ne (cache := c) ans
      (trial_ne_hybrid hp (hS x y hxy.1) hxy.2 k n left right l r)).trans (hc x y hxy n l r)
  have hb : ftsZeroBits coord heap ≠ 0 := ClaudeWCT.WCT9.ftsZeroBits_pos hp.2.2
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
    have he : (fun answer => if ftsZeroOk coord heap (fVal heap answer) = true then
        (if ftsZeroOk coord heap (fVal heap answer) = true then B else 1)
        else B + (1 - p) ^ (k + 1)) =
        fun a => if ftsZeroOk coord heap (fVal heap a) = true then B else B + (1 - p) ^ (k + 1) := by
      funext a; split <;> simp_all
    rw [he, expectedValue_uniform_ite_F (fun a => ftsZeroOk coord heap (fVal heap a) = true), prob_fAccept]
    exact capF_step p B hp1 k
  · have he : (fun answer => if ftsZeroOk coord heap (fVal heap answer) = true then B
        else (1 : ℝ≥0∞)) = fun a => if ftsZeroOk coord heap (fVal heap a) = true then B else 1 := rfl
    rw [he, expectedValue_uniform_ite_F (fun a => ftsZeroOk coord heap (fVal heap a) = true), prob_fAccept]
    exact capF_tail p B hp1

/-- Per-heap cap failure of a shared node (`0` off the ground). -/
noncomputable def gcap (coord heap : Nat) : ℝ≥0∞ :=
  if ClaudeWCT.WCT9.ftsGround coord heap then fcap (ftsZeroBits coord heap) else 0

theorem gcap_le (coord heap : Nat) : gcap coord heap ≤ cF := by
  unfold gcap
  split
  · rename_i hg
    exact fcap_le_of _ (by unfold ClaudeWCT.WCT9.ftsGround at hg; unfold ftsZeroBits; split_ifs <;> simp_all <;> omega)
  · exact bot_le

/-- **One shared node**: `B + gcap`. -/
theorem E_snode {β : Type} (secret : BitVec 256) (first : Bool) (coord index heap : Nat) (hc : coord < 9)
    (hidx : index < 2 ^ 31) (h2 : 4 ≤ heap) (hh : heap < 128) (pads : Nat → PairRoot) (left right : Digest)
    (next : Digest → M β) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1)
    (S : Nat → Nat → Prop) (hS : HybridSet index S) (B : ℝ≥0∞)
    (hnext : ∀ v cache, ftsZeroOk coord heap v = true →
      FreshF index (fun c x => S c x ∧ ¬ (c = coord ∧ x = heap)) cache → Ev secret (next v) cache F ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) (hin : ClaudeWCT.WCT9.ftsGround coord heap → S coord heap) :
    Ev secret (sharedNode first coord index heap pads left right >>= next) cache F ≤ B + gcap coord heap := by
  unfold gcap
  by_cases hg : ClaudeWCT.WCT9.ftsGround coord heap
  · have h8 := ClaudeWCT.WCT9.ftsGround_ge8 hg
    have e : sharedNode first coord index heap pads left right = ftsNodeG coord index heap left right := by
      simp only [sharedNode, if_neg (show ¬ heap < 4 by omega), if_neg (show ¬ heap < 8 by omega)]
    rw [e, if_pos hg]
    exact E_fnode secret coord index heap ⟨hc, hidx, hg⟩ left right next F hF S hS B hnext cache hfresh (hin hg)
  · rw [if_neg hg, add_zero, Ev_bind]
    refine Ev_le_of_support secret _ cache (fun r hr => hnext r.1 r.2 (ftsZeroOk_off hg _) ?_)
    exact (freshF_preserved secret (notF_plain_inner hS first coord heap pads left right hc h2 hh hg) cache hfresh
      r hr).mono fun x y hxy => hxy.1

/-- The ground nodes of the heaps `D` pass their zero tests. -/
def OKAt (coord : Nat) (D : Nat → Prop) (nodes : Array Digest) : Prop :=
  ∀ h, D h → 8 ≤ h → h < 32 → ftsZeroOk coord h (nodes.getD h 0) = true

/-- **A list of shared heap steps**: `B + Σ gcap`, the continuation seeing every ground node of the list pass. -/
theorem E_heapList {β : Type} (secret : BitVec 256) (first : Bool) (index coord : Nat) (hc : coord < 9)
    (hidx : index < 2 ^ 31) (pads : Nat → PairRoot) (F : β × RCache → ℝ≥0∞) (hF : ∀ r, F r ≤ 1) :
    ∀ (l : List Nat), (∀ h ∈ l, 4 ≤ h ∧ h < 128) → l.Nodup →
    ∀ (S : Nat → Nat → Prop) (D : Nat → Prop) (init : Array Digest) (next : Array Digest → M β) (B : ℝ≥0∞),
      HybridSet index S → (∀ h ∈ l, ClaudeWCT.WCT9.ftsGround coord h → S coord h) → (∀ h ∈ l, ¬ D h) →
      32 ≤ init.size →
      OKAt coord D init →
      (∀ a cache, 32≤a.size → OKAt coord (fun h => D h ∨ h ∈ l) a →
        FreshF index (fun c' x => S c' x ∧ ¬ (c' = coord ∧ x ∈ l)) cache → Ev secret (next a) cache F ≤ B) →
      ∀ cache, FreshF index S cache →
        Ev secret ((l.foldlM (heapStep first index coord pads) init) >>= next) cache F ≤
          B + (l.map (gcap coord)).sum := by
  intro l
  induction l with
  | nil =>
      intro _ _ S D init next B _ _ _ hsize hok hnext cache hfresh
      simp only [List.foldlM_nil, pure_bind, List.map_nil, List.sum_nil, add_zero]
      exact hnext init cache hsize (fun h hd => hok h (by simpa using hd)) (hfresh.mono fun x y h => h.1)
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
          (fun a cache'' hsz hok' hc'' => hnext a cache'' hsz
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


theorem E_inner {β : Type} (secret : BitVec 256) (first : Bool) (index coord : Nat) (hc : coord < 9)
    (hidx : index < 2 ^ 31) (pads : Nat → PairRoot) (leaves : List Digest) (F : β × RCache → ℝ≥0∞)
    (hF : ∀ r, F r ≤ 1) (S : Nat → Nat → Prop) (hS : HybridSet index S)
    (hin : ∀ h, ClaudeWCT.WCT9.ftsGround coord h → S coord h)
    (next : Array Digest → M β) (B : ℝ≥0∞)
    (hnext : ∀ a cache, 32≤a.size → ftsTreeOK coord a = true → FreshF index (fun c' x => S c' x ∧ ¬ (c' = coord ∧ 4 ≤ x)) cache →
      Ev secret (next a) cache F ≤ B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    Ev secret (OuterInnerMoment.innerHeap first index coord pads leaves >>= next) cache F ≤ B + 24 * cF := by
  have key : ∀ (a m : Nat), a + m = 8 → 4 ≤ a →
      Ev secret (((List.range' a (m + (24 + 96))).reverse.foldlM (heapStep first index coord pads)
        ((List.replicate 128 (0 : Digest) ++ leaves).toArray)) >>= next) cache F ≤
        B + 24 * cF := by
    intro a m ham ha
    have hmem : ∀ x, x ∈ (List.range' a (m + (24 + 96))).reverse ↔ a ≤ x ∧ x < 128 := by
      intro x; rw [List.mem_reverse, List.mem_range'_1]; omega
    refine le_trans ?_ (add_le_add le_rfl (heapList_sum_le coord a m ham))
    refine E_heapList secret first index coord hc hidx pads F hF _
      (fun x hx => by have := (hmem x).mp hx; omega) (List.nodup_reverse.mpr (List.nodup_range' ..))
      S (fun _ => False) _ next B hS (fun x _ hg => hin x hg) (fun _ _ h => h)
      (show 32 ≤ (List.replicate 128 (0 : Digest) ++ leaves).length by simp only [List.length_append, List.length_replicate]; omega)
      (fun _ h => h.elim)
      (fun nodes c hsz hok hc' => hnext nodes c hsz ?_ ?_) cache hfresh
    · unfold ftsTreeOK
      rw [List.all_eq_true]
      intro x hx
      rw [List.mem_range'_1] at hx
      exact hok x (Or.inr ((hmem x).mpr ⟨by omega, by omega⟩)) hx.1 (by omega)
    · exact hc'.mono fun c' x hx => ⟨hx.1, fun he => hx.2 ⟨he.1, (by have := (hmem x).mp he.2; omega)⟩⟩
  unfold OuterInnerMoment.innerHeap
  rw [show (124 : Nat) = 4 + (24 + 96) from rfl]
  exact key 4 4 rfl le_rfl

#print axioms E_inner
end OuterHybridComplete
