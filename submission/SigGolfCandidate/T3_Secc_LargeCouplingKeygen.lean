import SigGolfCandidate.T3_Secc_LargeCouplingInteraction

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_largeCouplingKeygen : DecidableEq T3.Cache := Classical.decEq _
noncomputable def keyValues (vals : Coord → Digest) : Coord → Digest :=
  lookupVal (keygenDisclosed.map fun c => (c, vals c))
theorem treeChild_top_some (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level)) :
    ∃ c, treeChild 0 0 level node = some c := by
  by_cases hz : level=0
  · subst level
    have hn' : node < 4096 := by simpa using hn
    simp only [treeChild,ite_true,dif_pos hn']
    exact ⟨_,rfl⟩
  unfold treeChild treeNodeAt
  rw [if_neg hz]
  have h1 : level - 1 < height 0 := by simp [height]; omega
  have h2 : node < 2 ^ (height 0 - (level - 1) - 1) := by
    have : height 0 - (level - 1) - 1 = 12 - level := by simp [height]; omega
    rw [this]; exact hn
  rw [dif_pos ⟨h1, h2⟩]
  exact ⟨_, rfl⟩
theorem treeChild_mem_keygen (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level))
    (c : Coord) (hc : treeChild 0 0 level node = some c) : c ∈ keygenDisclosed := by
  unfold keygenDisclosed
  simp only [List.mem_flatMap, List.mem_range'_1, List.mem_filterMap, List.mem_range]
  exact ⟨level, ⟨by omega, by omega⟩, node, hn, hc⟩
theorem cacheRegion_congr (f g : Nat → Nat → Digest)
    (h : ∀ level node, 0 ≤ level → level < 12 → node < 2 ^ (12 - level) → f level node = g level node) :
    Correctness.cacheRegion f = Correctness.cacheRegion g := by
  have hw : Correctness.cacheWordList f = Correctness.cacheWordList g := by
    unfold Correctness.cacheWordList
    apply List.flatMap_congr
    intro level hlevel
    rw [List.mem_range'_1] at hlevel
    apply List.map_congr_left
    intro node hnode
    exact h level node (by omega) (by omega) (List.mem_range.mp hnode)
  unfold Correctness.cacheRegion
  rw [hw]
section Keygen
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.private_header (hcoh : Coherent U T vals nv τ a)
    (tag level node : Nat) (h0 : tag%256 ≠ 0) (h8 : tag%256 ≠ 8) :
    T (.inr (.inl (header tag 0 0 level node))) = a.priv (.inl (header tag 0 0 level node)) := by
  apply hcoh.priv
  · intro i hi
    obtain ⟨s, hs⟩ := hi
    have hp := congrArg Prod.fst hs
    cases s with
    | inl x =>
        change Sum.inl (header 0 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h0) (Sum.inl.inj hp)
    | inr f =>
        change Sum.inl (header 8 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h8) (Sum.inl.inj hp)
  · intro m h
    cases h
theorem Coherent.mask_eq (hcoh : Coherent U T vals nv τ a) (level node : Nat) :
    maskOf a level node = evalWithAnswerFn T (T3.mask level node) := by
  have hp := hcoh.private_header 13 level (node/2) (by decide) (by decide)
  unfold maskOf T3.mask pairedMask privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [← hp]
  rfl
theorem Coherent.mac_eq (hcoh : Coherent U T vals nv τ a) (region : Region) :
    macOf a region = evalWithAnswerFn T (T3.privateMac region) := by
  have hk : (fun i : Fin 2 => a.priv (.inl (header 14 0 0 0 i.val))) =
      (fun i : Fin 2 => if i=0 then T (.inr (.inl (header 14 0 0 0 0)))
        else T (.inr (.inl (header 14 0 0 0 1)))) := by
    funext i
    fin_cases i <;> simp [hcoh.private_header 14 0 0 (by decide) (by decide),
      hcoh.private_header 14 0 1 (by decide) (by decide)]
  unfold macOf T3.privateMac T3.privateMacKey privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [hk]
  rfl
end Keygen
end SigGolfCandidate.T3.Security.LargeCoupling
