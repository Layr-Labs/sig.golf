import SigGolfCandidate.OuterReadout
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterCoordinateModel
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3M W9Machine W9Drv.SharedCanonical
open SigGolfCandidate.Research.SharedForest

def coordinate (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank) (prev : PairRoot) :
    M (PairRoot×Nat×Nat×Nat) := do
  let ends←V3.chainProgram w index coord raw (ClaudeWCT.WCT9.embed word)
  let comp←OuterChildModel.child w index coord raw ends prev.1 prev.2
  pure (SharedV3.orderPair coord.val (SharedV3.physical coord.val raw.val) comp.1
    (SharedV3.topOther w coord.val (SharedV3.physical coord.val raw.val)),comp.2)

theorem canonical (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9)
    (raw : Child) (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) (p3 p2 : Digest)
    (hi : index<2^31) (hc : ChainReadout w coord word values) (hp : OuterReadout.Path w coord raw path p3 p2)
    (hp2 : 4≤coord.val → p2=0) (hf : SharedV3.first coord.val=false) :
    coordinate w index coord raw word prev=OuterCanonicalCoordinate.canonical index coord raw word values path prev := by
  unfold coordinate OuterCanonicalCoordinate.canonical OuterChildModel.child
  simp only [hf,Bool.false_eq_true,if_false]
  rw [chainProgram_zero _ _ _ _ _ _ hi hc]
  simp only [bind_assoc]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro ends hends
  have hlen : ends.length=6 := by simpa using length_of_support_mapM _ (List.finRange 6) ends hends
  rw [leafSel_eq _ _ _ _ (SharedV3.physical_lt _ _ raw.isLt) _ _ hlen]
  apply bind_congr
  intro leaf
  have h4:=lastLevel_ge4 coord.val
  have h5 : SharedV3.lastLevel coord.val=5 := by simp only [SharedV3.lastLevel,hf,Bool.false_eq_true,if_false]
  have hc':=SharedV3.physical_lt coord.val raw.val raw.isLt
  have hfold : (List.range 5).foldlM
      (SharedV3.childStepG w index coord.val (SharedV3.physical coord.val raw.val) prev.2) (leaf, 0, 0) =
      (List.range 5).foldlM
      (canonicalStepG false index coord.val (SharedV3.physical coord.val raw.val) path prev.2)
      (leaf, 0, 0) := by
    apply foldlM_congr_mem
    intro acc level hl
    have hll := List.mem_range.mp hl
    rw [←hf]
    unfold SharedV3.childStepG canonicalStepG
    by_cases h3 : level = 3
    · subst h3
      simp only [if_true]
      rw [hp.siblings 3 (by omega), hp.headerPads 3 (by omega)]
      have e := groundStep_canonical coord index ((128 + SharedV3.physical coord.val raw.val) / 2 ^ (3 + 1))
        (by norm_num; omega)
        (if SharedV3.physical coord.val raw.val / 2 ^ 3 % 2 = 0 then acc.1 else path 3)
        (if SharedV3.physical coord.val raw.val / 2 ^ 3 % 2 = 0 then path 3 else acc.1)
      have e' := congrArg (fun m => (fun p : Digest × Nat => (p.1, p.2, acc.2.2)) <$> m) e
      simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp] at e' ⊢
      exact e'
    · simp only [if_neg h3]
      by_cases h2 : level = 2 ∧ coord.val < 4
      · obtain ⟨rfl, hk⟩ := h2
        simp only [true_and, if_pos hk]
        rw [hp.siblings 2 (by omega), hp.headerPads 2 (by omega)]
        have hheap : 16 ≤ (128 + SharedV3.physical coord.val raw.val) / 2 ^ (2 + 1) ∧
            (128 + SharedV3.physical coord.val raw.val) / 2 ^ (2 + 1) < 32 := by norm_num; omega
        have e := groundStep_canonical16 coord hk index _ hheap _
          (hiOut_heap _ (2 + 1) hc' (by decide))
          (if SharedV3.physical coord.val raw.val / 2 ^ 2 % 2 = 0 then acc.1 else path 2)
          (if SharedV3.physical coord.val raw.val / 2 ^ 2 % 2 = 0 then path 2 else acc.1)
        have e' := congrArg (fun m => (fun p : Digest × Nat => (p.1, acc.2.1, p.2)) <$> m) e
        simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp] at e' ⊢
        exact e'
      · simp only [if_neg h2]
        have hnf : ¬ (level = 4 ∧ SharedV3.first coord.val = true) := by
          rintro ⟨rfl, hf⟩
          have : SharedV3.lastLevel coord.val = 4 := by unfold SharedV3.lastLevel; rw [hf]; rfl
          omega
        rw [if_neg hnf, OuterReadout.childInput _ _ _ _ _ _ _ _ _ _ hp (by omega) hll]
        have hpad : (if level = 2 then p2 else (0 : Digest)) = 0 := by
          split_ifs with hl2
          · exact hp2 (by omega)
          · rfl
        simp only [canonicalChildInput, if_neg h3, hpad, ite_self]
  rw [hfold]
  apply bind_congr
  intro acc
  rw [hp.siblings 5 (by omega),hp.topOther]
  split_ifs <;> simp only [h5,Nat.reduceAdd,bind_assoc,pure_bind] <;> rfl

theorem coordinate_first (w : SharedV3.WBytes) (index : Nat) (coord : Fin 9) (raw : Child) (word : Rank)
    (prev : PairRoot) (hf : SharedV3.first coord.val=true) :
    coordinate w index coord raw word prev=
      (fun r=>(r.1,r.2.1,r.2.2,0)) <$> SharedV3.coordinateG w index coord raw (ClaudeWCT.WCT9.embed word) prev := by
  unfold coordinate OuterChildModel.child SharedV3.coordinateG
  simp only [hf,if_true,map_bind,bind_map_left,Functor.map_map,Function.comp_def,map_pure,bind_assoc,pure_bind]

#print axioms coordinate_first

#print axioms canonical
end OuterCoordinateModel
