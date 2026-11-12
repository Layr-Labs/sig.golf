import SigGolfCandidate.OuterForestBudget
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace OuterForestMoment
open OracleComp OracleSpec ENNReal OuterGroundCore OuterForestBudget
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh

def pair (index p : Nat) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank) (prev : PairRoot) : M (PairOpening × PairRoot) := do
  let a←buildCoord true index (2*p) (firstChild s) aWord (fun _ => prev)
  let b←buildCoord false index (2*p+1) (secondChild s) bWord (nodesPair a.1)
  pure (⟨fun i => a.2.getD i.val 0,fun i => authAt a.1 (firstChild s).val i.val,
    fun i => b.2.getD i.val 0,fun i => authAt b.1 (secondChild s).val i.val⟩,
    (b.1.getD 2 0,b.1.getD 3 0))

def singleton (index : Nat) (selected : Child) (word : Rank) (prev : PairRoot) : M (SingletonOpening × PairRoot) := do
  let built←buildCoord false index 8 selected word (fun _ => prev)
  pure (⟨fun i => built.2.getD i.val 0,fun i => authAt built.1 selected.val i.val⟩,
    (built.1.getD 2 0,built.1.getD 3 0))

def forest (index : Nat) (selected : ForestSelection) (words : ForestWords) : M (ForestOpening × PairRoot) := do
  let state←(List.finRange 4).foldlM (fun (state : List PairOpening × PairRoot) p => do
    let built←pair index p.val (selected.pairs p) (words.first p) (words.second p) state.2
    pure (state.1++[built.1],built.2)) ([],ftsStart)
  let last←singleton index selected.singleton words.singleton state.2
  pure (⟨fun p => state.1.getD p.val emptyPairOpening,last.1⟩,last.2)

noncomputable def CB (z : ENNReal) (first : Bool) (f g o B : ENNReal) : ENNReal := coordBound z f g o first*B

theorem V_pair {β : Type} (secret : BitVec 256) (z : ENNReal) (hz : 1≤z) (index p : Nat)
    (hi : index<2^31) (hp : p<4) (s : SigGolfCandidate.Research.SharedForest.Selection) (aWord bWord : Rank) (prev : PairRoot)
    (fa fb ga gb oa ob : ENNReal) (ha : FacF z (2*p) fa) (hb : FacF z (2*p+1) fb)
    (hga : FacG z (2*p) ga) (hgb : FacG z (2*p+1) gb)
    (hoa : FacFH z (width (2*p)) oa) (hob : FacFH z (width (2*p+1)) ob)
    (next : PairOpening × PairRoot → M β) (B : ENNReal)
    (hnext : ∀ a cache,FreshF index (AllAbove (2*p+2)) cache→V secret z (next a) cache≤B)
    (cache : RCache) (hs : FreshF index (AllAbove (2*p)) cache) :
    V secret z (pair index p s aWord bWord prev >>= next) cache≤CB z true fa ga oa (CB z false fb gb ob B) := by
  unfold pair CB
  simp only [bind_assoc]
  refine V_buildCoord_bind secret z fa ga oa _ hz true index (2*p) (by omega) hi (firstChild s) aWord
    (fun _ => prev) ha hga hoa (by simp) _ (fun a c1 h1 => ?_) cache hs
  refine V_buildCoord_bind secret z fb gb ob _ hz false index (2*p+1) (by omega) hi (secondChild s) bWord
    (nodesPair a.1) hb hgb hob (fun _ => Or.inl (by omega)) _ (fun b c2 h2 => ?_) c1 h1
  simp only [pure_bind]
  exact hnext _ c2 (by simpa [Nat.add_assoc] using h2)

theorem V_singleton {β : Type} (secret : BitVec 256) (z f g o : ENNReal) (hz : 1≤z) (index : Nat)
    (hi : index<2^31) (selected : Child) (word : Rank) (prev : PairRoot)
    (hf : FacF z 8 f) (hg : FacG z 8 g) (ho : FacFH z (width 8) o)
    (next : SingletonOpening × PairRoot → M β) (B : ENNReal)
    (hnext : ∀ a cache,V secret z (next a) cache≤B)
    (cache : RCache) (hs : FreshF index (AllAbove 8) cache) :
    V secret z (singleton index selected word prev >>= next) cache≤CB z false f g o B := by
  unfold singleton CB
  simp only [bind_assoc]
  refine V_buildCoord_bind secret z f g o B hz false index 8 (by decide) hi selected word
    (fun _ => prev) hf hg ho (fun _ => Or.inr rfl) _ (fun built c _ => ?_) cache hs
  simpa only [pure_bind] using hnext _ c

theorem V_forest (secret : BitVec 256) (z : ENNReal) (hz : 1≤z) (index : Nat) (hi : index<2^31)
    (selected : ForestSelection) (words : ForestWords) (fc gc oc : Nat → ENNReal)
    (hf : ∀ c,c<9→FacF z c (fc c)) (hg : ∀ c,c<9→FacG z c (gc c))
    (ho : ∀ c,c<9→FacFH z (width c) (oc c)) (cache : RCache) (hs : FreshF index (AllAbove 0) cache) :
    V secret z (forest index selected words) cache≤(CB z true (fc 0) (gc 0) (oc 0) (CB z false (fc 1) (gc 1) (oc 1) (CB z true (fc 2) (gc 2) (oc 2) (CB z false (fc 3) (gc 3) (oc 3) (CB z true (fc 4) (gc 4) (oc 4) (CB z false (fc 5) (gc 5) (oc 5) (CB z true (fc 6) (gc 6) (oc 6) (CB z false (fc 7) (gc 7) (oc 7) (CB z false (fc 8) (gc 8) (oc 8) 1))))))))) := by
  rw [←bind_pure (forest index selected words)]
  unfold forest
  have hfr : List.finRange 4=[0,1,2,3] := by decide
  rw [hfr]
  simp only [List.foldlM_cons,List.foldlM_nil,bind_assoc,pure_bind]
  refine V_pair secret z hz index 0 hi (by decide) _ _ _ _ (fc 0) (fc 1) (gc 0) (gc 1) (oc 0) (oc 1)
    (hf 0 (by decide)) (hf 1 (by decide)) (hg 0 (by decide)) (hg 1 (by decide))
    (ho 0 (by decide)) (ho 1 (by decide)) _ _ (fun a c1 h1 => ?_) cache hs
  refine V_pair secret z hz index 1 hi (by decide) _ _ _ _ (fc 2) (fc 3) (gc 2) (gc 3) (oc 2) (oc 3)
    (hf 2 (by decide)) (hf 3 (by decide)) (hg 2 (by decide)) (hg 3 (by decide))
    (ho 2 (by decide)) (ho 3 (by decide)) _ _ (fun a c2 h2 => ?_) c1 h1
  refine V_pair secret z hz index 2 hi (by decide) _ _ _ _ (fc 4) (fc 5) (gc 4) (gc 5) (oc 4) (oc 5)
    (hf 4 (by decide)) (hf 5 (by decide)) (hg 4 (by decide)) (hg 5 (by decide))
    (ho 4 (by decide)) (ho 5 (by decide)) _ _ (fun a c3 h3 => ?_) c2 h2
  refine V_pair secret z hz index 3 hi (by decide) _ _ _ _ (fc 6) (fc 7) (gc 6) (gc 7) (oc 6) (oc 7)
    (hf 6 (by decide)) (hf 7 (by decide)) (hg 6 (by decide)) (hg 7 (by decide))
    (ho 6 (by decide)) (ho 7 (by decide)) _ _ (fun a c4 h4 => ?_) c3 h3
  refine V_singleton secret z (fc 8) (gc 8) (oc 8) hz index hi _ _ _ (hf 8 (by decide))
    (hg 8 (by decide)) (ho 8 (by decide)) _ 1 (fun _ _ => ?_) c4 h4
  simp only [V_pure,le_refl]

theorem forestCB_eq (z : ENNReal) (fc gc oc : Nat → ENNReal) :
    (CB z true (fc 0) (gc 0) (oc 0) (CB z false (fc 1) (gc 1) (oc 1) (CB z true (fc 2) (gc 2) (oc 2) (CB z false (fc 3) (gc 3) (oc 3) (CB z true (fc 4) (gc 4) (oc 4) (CB z false (fc 5) (gc 5) (oc 5) (CB z true (fc 6) (gc 6) (oc 6) (CB z false (fc 7) (gc 7) (oc 7) (CB z false (fc 8) (gc 8) (oc 8) 1))))))))) = z^31041*(fc 0*fc 1*fc 2*fc 3*fc 4*fc 5*fc 6*fc 7*fc 8)^8*
      (gc 0*gc 1*gc 2*gc 3*gc 4*gc 5*gc 6*gc 7*gc 8)^16*(oc 1*oc 3*oc 5*oc 7*oc 8)^2 := by
  simp only [CB,coordBound,Bool.false_eq_true,↓reduceIte]
  ring

#print axioms V_forest
#print axioms forestCB_eq

#print axioms V_pair
#print axioms V_singleton
end OuterForestMoment
