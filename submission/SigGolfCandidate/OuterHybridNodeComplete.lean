import SigGolfCandidate.OuterHybridComplete
import SigGolfCandidate.OuterHeapMoment
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterHybridNodeComplete
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
open ClaudeWCT.WCT9
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh
open ClaudeWCT.W9.T3.Freshness.Paired.FtsComplete
open ClaudeWCT.W9.T3.TopMoment (Ev Ev_bind Ev_pure Ev_le_of_support)
open OuterGroundCore OuterHybridComplete

theorem E_node {β : Type} (secret : BitVec 256) (coord index heap : Nat) (hp : HP coord index heap)
    (left right : Digest) (next : Nat × Digest → M β) (F : β × RCache → ℝ≥0∞) (hF : ∀ r,F r≤1)
    (S : Nat → Nat → Prop) (hS : HybridSet index S) (B : ℝ≥0∞)
    (hnext : ∀ v cache,zeroOk coord v.2=true →
      FreshF index (fun c x=>S c x ∧ ¬(c=coord ∧ x=heap)) cache → Ev secret (next v) cache F≤B)
    (cache : RCache) (hfresh : FreshF index S cache) (hin : S coord heap) :
    Ev secret (nodeAt coord index heap left right >>= next) cache F≤B+((2:ENNReal)^210)⁻¹ := by
  have hpres : ∀ (c : RCache) k (ans : HashOutput),FreshF index (fun c x=>S c x ∧ ¬(c=coord ∧ x=heap)) c →
      FreshF index (fun c x=>S c x ∧ ¬(c=coord ∧ x=heap))
        (c.cacheQuery (fTrial coord index heap k left right) ans) := by
    intro c k ans hc x y hxy n l r
    exact (QueryCache.cacheQuery_of_ne (cache:=c) ans
      (OuterGroundFresh.trial_ne ⟨hp.1,hp.2.1,hp.heap.2⟩
        ⟨(hS x y hxy.1).1,(hS x y hxy.1).2.1,(hS x y hxy.1).heap.2⟩ hxy.2 k n left right l r)).trans (hc x y hxy n l r)
  have hcap : cap coord-1<2^64 := by
    have hw:=width_bounds coord
    have hpow : 2^width coord≤2^4 := Nat.pow_le_pow_right (by decide) hw.2
    unfold cap;omega
  have hcap1 : cap coord-1+1=cap coord := by
    apply Nat.sub_add_cancel
    have hpos : 0<cap coord := by unfold cap;positivity
    exact hpos
  set p : ENNReal:=((2:ENNReal)^width coord)⁻¹ with hpdef
  have hp1 : p≤1 := by rw [hpdef,←prob_accept coord heap];exact probEvent_le_one
  unfold nodeAt
  have hres:=OuterGroundFailure.Ev_search_fuel secret coord index heap left right next F
    (FreshF index (fun c x=>S c x ∧ ¬(c=coord ∧ x=heap)))
    (fun v=>if zeroOk coord v then B else 1) (fun k=>B+(1-p)^(k+1))
    (fun c hc k a=>hpres c k a hc) ?_ ?_ ?_ (cap coord-1) 0 (by omega) cache
    (hfresh.mono (fun x y hxy=>hxy.1)) (fun k _ _=>hfresh coord heap hin k left right)
  · refine hres.trans ?_
    rw [hcap1]
    exact add_le_add_right (OuterGroundFailure.cap_bound coord) B
  · intro σ hσ k ans
    change Ev secret (next (k,value coord heap ans))
      (σ.cacheQuery (fTrial coord index heap k left right) ans) F ≤
      if zeroOk coord (value coord heap ans) then B else 1
    split
    · rename_i hok
      exact hnext _ _ hok (hpres σ k ans hσ)
    · exact Ev_le_of_support secret _ _ (fun r _=>hF r)
  · intro k
    have he : (fun answer=>if zeroOk coord (value coord heap answer)=true then
        (if zeroOk coord (value coord heap answer)=true then B else 1) else B+(1-p)^(k+1))=
        fun a=>if zeroOk coord (value coord heap a)=true then B else B+(1-p)^(k+1) := by
      funext a;split <;> simp_all
    rw [he,expectedValue_uniform_ite_F (fun a=>zeroOk coord (value coord heap a)=true),prob_accept]
    exact capF_step p B hp1 k
  · rw [expectedValue_uniform_ite_F (fun a=>zeroOk coord (value coord heap a)=true),prob_accept]
    exact capF_tail p B hp1


def outerOK (coord : Nat) (nodes : Array Digest) : Prop :=
  zeroOk coord (nodes.getD 2 0)=true ∧ zeroOk coord (nodes.getD 3 0)=true

theorem E_finish {β : Type} (secret : BitVec 256) (coord index : Nat) (hc : coord<9) (hi : index<2^31)
    (nodes : Array Digest) (hsize : 4≤nodes.size)
    (F : β × RCache → ENNReal) (hF : ∀ r,F r≤1)
    (S : Nat → Nat → Prop) (hS : HybridSet index S) (hin2 : S coord 2) (hin3 : S coord 3)
    (next : Array Digest → M β) (B : ENNReal)
    (hnext : ∀ a cache,ftsTreeOK coord a=ftsTreeOK coord nodes → outerOK coord a →
      FreshF index (fun c x=>S c x ∧ ¬(c=coord ∧ (x=2 ∨ x=3))) cache → Ev secret (next a) cache F≤B)
    (cache : RCache) (hfresh : FreshF index S cache) :
    Ev secret (OuterHeapMoment.finish coord index nodes >>= next) cache F≤B+2*((2:ENNReal)^210)⁻¹ := by
  unfold OuterHeapMoment.finish
  simp only [bind_assoc,pure_bind]
  refine le_trans (E_node secret coord index 3 ⟨hc,hi,Or.inr (Or.inr rfl)⟩ _ _ _ F hF S hS
    (B+((2:ENNReal)^210)⁻¹) (fun a c1 ha h1=>?_) cache hfresh hin3) (le_of_eq (by ring))
  refine E_node secret coord index 2 ⟨hc,hi,Or.inr (Or.inl rfl)⟩ _ _ _ F hF
    (fun c x=>S c x ∧ ¬(c=coord ∧ x=3)) (fun c x hx=>hS c x hx.1) B
    (fun b c2 hb h2=>?_) c1 h1 ⟨hin2,by omega⟩
  apply hnext _ c2
  · unfold ftsTreeOK
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro h x hx <;> have hh := (List.mem_range'_1.mp hx)
    · have hhx:=h x hx
      rw [getD_set_other _ 2 x _ (by omega),getD_set_other _ 3 x _ (by omega)] at hhx
      exact hhx
    · rw [getD_set_other _ 2 x _ (by omega),getD_set_other _ 3 x _ (by omega)]
      exact h x hx
  · constructor
    · rw [getD_set_self _ _ _ (by simp only [Array.size_set!];omega)]
      exact hb
    · rw [getD_set_other _ 2 3 _ (by decide),getD_set_self _ _ _ (by omega)]
      exact ha
  · exact h2.mono (fun c x hx=>⟨⟨hx.1,fun h=>hx.2 ⟨h.1,Or.inr h.2⟩⟩,
      fun h=>hx.2 ⟨h.1,Or.inl h.2⟩⟩)

#print axioms E_node
#print axioms E_finish
end OuterHybridNodeComplete
