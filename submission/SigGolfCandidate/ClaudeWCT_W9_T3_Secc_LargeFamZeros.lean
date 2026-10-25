import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_CanonGraph

/-! # Large route, family level: zero sets of a family (r3-lean-seedfam, family port P7, additive)

The large route bounds, per seed family, the seeds the router can have disclosed (`FamOK`: at most `deg = size − 1`).
Today (one family per leaf) this is `LargeCouplingTable.lowerZeros_card`. For grouped families (v6 flip) the revealed
seeds of a family are the union of the revealed seeds of its REAL member leaves (`leaf < 2 ^ height`), so the bound is
`zcap · members + 3 ≤ famSize` with `members = min famGrp (2 ^ height − famGrp · f)` (short last family included).

`famZeros_card_le`: the counting step, for any per-address predicate `Z` with a per-leaf cap. -/

namespace ClaudeWCT.W9.T3.Security.CanonGraph
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-- Real member leaves of family `f` of layer `lay` (the last family of a tree may be short). -/
def famMembersL (lay : Layer) (f : Nat) : Nat := min (WCT9.famGrp lay) (2 ^ height lay - WCT9.famGrp lay * f)

/-- A real leaf of family `f` is `famGrp · f + r` with `r < famMembersL lay f`. -/
theorem leaf_decomp {lay : Layer} {leaf : Nat} (hreal : leaf < 2 ^ height lay) :
    leaf = WCT9.famGrp lay * WCT9.famOf lay leaf + leaf % WCT9.famGrp lay ∧
      leaf % WCT9.famGrp lay < famMembersL lay (WCT9.famOf lay leaf) := by
  have hg := WCT9.famGrp_pos lay
  have e := Nat.div_add_mod leaf (WCT9.famGrp lay)
  have hm : leaf % WCT9.famGrp lay < WCT9.famGrp lay := Nat.mod_lt _ hg
  refine ⟨by unfold WCT9.famOf; omega, ?_⟩
  unfold famMembersL
  refine lt_min hm ?_
  unfold WCT9.famOf
  omega

/-- **Family zero count.** If every set of addresses of one real leaf satisfying `Z` has at most `zcap lay` elements,
every set of addresses of family `f` (real leaves) satisfying `Z` has at most `zcap lay · famMembersL lay f`. -/
theorem famZeros_card_le (Z : ChainGraph.Address → Prop) (zcap : Layer → Nat)
    (hleaf : ∀ (lay : Layer) (tree : Fin (2 ^ 31)) (n : Nat), n < 2 ^ height lay → ∀ S : Finset ChainGraph.Address,
      (∀ a ∈ S, a.layer = lay ∧ a.tree = tree ∧ a.leaf.val = n ∧ Z a) → S.card ≤ zcap lay)
    (lay : Layer) (tree : Fin (2 ^ 31)) (f : Fin 4096) (S : Finset ChainGraph.Address)
    (hS : ∀ a ∈ S, (a.layer, a.tree, famSlot a.layer a.leaf) = (lay, tree, f) ∧ a.leaf.val < 2 ^ height a.layer ∧ Z a) :
    S.card ≤ zcap lay * famMembersL lay f.val := by
  classical
  set m := famMembersL lay f.val
  have hsub : S ⊆ (Finset.range m).biUnion fun r => S.filter fun a => a.leaf.val = WCT9.famGrp lay * f.val + r := by
    intro a ha
    obtain ⟨hlf, hreal, -⟩ := hS a ha
    simp only [Prod.mk.injEq] at hlf
    obtain ⟨hl, -, hf⟩ := hlf
    have hf' : WCT9.famOf a.layer a.leaf.val = f.val := congrArg Fin.val hf
    obtain ⟨e, hr⟩ := leaf_decomp hreal
    rw [hf', hl] at hr
    rw [hf', hl] at e
    rw [Finset.mem_biUnion]
    exact ⟨a.leaf.val % WCT9.famGrp lay, Finset.mem_range.mpr hr, Finset.mem_filter.mpr ⟨ha, e⟩⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ r ∈ Finset.range m, (S.filter fun a => a.leaf.val = WCT9.famGrp lay * f.val + r).card
      ≤ ∑ _r ∈ Finset.range m, zcap lay := by
        refine Finset.sum_le_sum fun r hr => hleaf lay tree (WCT9.famGrp lay * f.val + r) ?_ _ fun a ha => ?_
        · have hr' : r < m := Finset.mem_range.mp hr
          have : r < 2 ^ height lay - WCT9.famGrp lay * f.val := lt_of_lt_of_le hr' (min_le_right _ _)
          omega
        · obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
          obtain ⟨hlf, -, hz⟩ := hS a ha1
          simp only [Prod.mk.injEq] at hlf
          exact ⟨hlf.1, hlf.2.1, ha2, hz⟩
    _ = zcap lay * m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]

/-- Today: every family has exactly one real member when its leaf is real. -/
theorem famMembersL_le_grp (lay : Layer) (f : Nat) : famMembersL lay f ≤ WCT9.famGrp lay := min_le_left _ _

end ClaudeWCT.W9.T3.Security.CanonGraph
