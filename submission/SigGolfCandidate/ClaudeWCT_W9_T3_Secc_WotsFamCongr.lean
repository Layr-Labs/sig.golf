import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamProg

/-! # Family restart, step P1/P3a: the abstract family scheme and family agreement (r3-lean-seedfam)

`FamScheme`: the scheme-side interface of the family restart. Per layer, `grp lay` consecutive leaves share one family
of `cnt lay` coefficients; coefficient `j` of family `f` is the packed half `cnt·f + j` of `lowerSeedPair lay tree`, and
the WOTS seed of chain `i` of leaf `leaf` is the family of `leaf / grp` evaluated at `(leaf % grp)·chainCount + i + 1`.
Today's scheme is the instance `leafScheme` (`grp = 1`, `cnt = famCount`); the switched scheme will be lower
`grp = 7, cnt = 38` and top `grp = 4, cnt = 4 r + 3`.

`FamOut S F`: queries outside family `F`'s chain rows (all `grp` leaves, steps `< 7`) and coefficient cells;
`FamAgree S F T T'`: agreement there and on the other halves of `F`'s cells; `wotsSeed_outF`: seeds of leaves outside
`F` are unchanged under `FamAgree`. (Family analogues of `Leaf.LeafOut` / `LeafAgree` / `wotsSeed_out`.)
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam (FamAddr famLeaf)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The scheme-side interface of the family restart. Per layer: `grp` leaves per family, ordinal base `cnt` (family `f`
owns ordinals `cnt·f + j`, `j < size lay f ≤ cnt`; the last family of a tree may be shorter), point stride `stride`
(`≥ chainCount`; lower 43, top 64). -/
structure FamScheme where
  grp : Layer → Nat
  cnt : Layer → Nat
  size : Layer → Nat → Nat
  stride : Layer → Nat
  /-- Evaluation point of chain `i` of leaf `leaf` (chains `≥ chainCount` may use a separate junk region). -/
  point : Layer → Nat → Nat → Nat
  grp_pos : ∀ lay, 0 < grp lay
  cnt_le : ∀ lay, cnt lay ≤ 512
  size_le : ∀ lay f, size lay f ≤ cnt lay
  point_eq : ∀ lay leaf i, i < chainCount lay → point lay leaf i = (leaf % grp lay) * stride lay + i + 1
  seed : ∀ (T : Answers) (lay : Layer) (tree leaf i : Nat), WCT9.wotsSeed T lay tree leaf i =
    ClaudeWCT.Arith.familyEval (List.ofFn fun j : Fin (size lay (leaf / grp lay)) =>
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair lay tree ((cnt lay * (leaf / grp lay) + j) / 2)))
        (cnt lay * (leaf / grp lay) + j)) (point lay leaf i)

/-- The scheme of the `Correctness` layout (`famGrp`, `famBase`, `famSize`, `famStride`, `famPoint`); valid for any
layout, so after the v6 flip it is the v6 scheme. -/
def layoutScheme : FamScheme where
  grp := WCT9.famGrp
  cnt := WCT9.famBase
  size := WCT9.famSize
  stride := WCT9.famStride
  point := WCT9.famPoint
  grp_pos := WCT9.famGrp_pos
  cnt_le lay := (WCT9.famBase_le lay).trans (by norm_num)
  size_le := WCT9.famSize_le_base
  point_eq lay leaf i hi := by unfold WCT9.famPoint; rw [if_pos (Or.inr hi)]
  seed T lay tree leaf i := by
    rw [WCT9.wotsSeed_fam]
    rfl

variable (S : FamScheme)

/-- Ordinal of coefficient `j` of family `F`. -/
def ordS (F : FamAddr) (j : Nat) : Nat := S.cnt F.lay * F.fam + j

/-- Queries outside family `F`: its chain rows (every leaf of the family, steps `< 7`) and its coefficient cells. -/
def FamOut (F : FamAddr) : Spec.Domain → Prop
  | .inl (.inr input) => ∀ l : Fin (S.grp F.lay), ∀ c step value, c < chainCount F.lay → step < 7 →
      input ≠ chainRowW ⟨famLeaf (S.grp F.lay) F l, c⟩ step value
  | .inr (.inl tweak) => ∀ j, j < S.cnt F.lay → tweak ≠ WCT9.lowerSeedHeader F.lay F.tree (ordS S F j / 2)
  | _ => True

/-- Chain addresses whose `Untouched` classes cover `FamOut F`. -/
def coverAddrsF (F : FamAddr) : List ChainAddr :=
  (List.finRange (S.grp F.lay)).flatMap (fun l =>
      (List.range (chainCount F.lay)).map (fun c => (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr))) ++
    (List.range (S.cnt F.lay)).map (fun j => (⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩ : ChainAddr))

theorem famOut_of_cover {F : FamAddr} {q : Spec.Domain} (h : ∀ c ∈ coverAddrsF S F, Untouched c q) :
    FamOut S F q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro l c step value hc hs heq
    have hmem : (⟨famLeaf (S.grp F.lay) F l, c⟩ : ChainAddr) ∈ coverAddrsF S F :=
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨l, List.mem_finRange l,
        List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩⟩)
    have hu := h _ hmem step value (by omega)
    unfold chainRowW WCT9.chainInputW at heq
    split at heq
    · exact hu.2 heq
    · exact hu.1 heq
  · intro j hj heq
    apply h ⟨⟨F.lay, F.tree, 0⟩, 2 * (ordS S F j / 2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    show tweak = seedTweak _
    rw [heq]
    unfold seedTweak WCT9.lowerSeedHeader
    simp only
    rw [show 2 * (ordS S F j / 2) / 2 = ordS S F j / 2 by omega]
  · trivial

/-- A program respecting every chain's `Untouched` class respects `FamOut F`. -/
theorem respects_famOut {α : Type} {p : M α} (h : ∀ c, Respects (Untouched c) p) (F : FamAddr) :
    Respects (FamOut S F) p :=
  Respects.mono' (Leaf.respects_cover h (coverAddrsF S F)) fun _ hq => famOut_of_cover S hq

/-- `T'` agrees with `T` outside `F` and on the other halves of `F`'s coefficient cells. -/
structure FamAgree (F : FamAddr) (T T' : Answers) : Prop where
  out : ∀ q, FamOut S F q → T' q = T q
  half : ∀ o, (∃ j, j < S.cnt F.lay ∧ o / 2 = ordS S F j / 2) → (∀ j, j < S.cnt F.lay → o ≠ ordS S F j) →
    WCT9.seedHalf (evalWithAnswerFn T' (WCT9.lowerSeedPair F.lay F.tree (o / 2))) o =
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair F.lay F.tree (o / 2))) o

/-- `(lay, tree, leaf)` is a leaf of family `F` up to the header aliasing of the tree index. -/
def FamAlias (F : FamAddr) (lay : Layer) (tree leaf : Nat) : Prop :=
  lay = F.lay ∧ tree % 2 ^ 40 = F.tree % 2 ^ 40 ∧ leaf / S.grp F.lay = F.fam

/-- Ordinal pair indices stay below `2^32` for leaves below `2^24` (`cnt ≤ 512`). -/
theorem ord_pair_lt (S : FamScheme) (lay : Layer) {leaf j : Nat} (hleaf : leaf < 2 ^ 24) (hj : j < S.cnt lay) :
    (S.cnt lay * (leaf / S.grp lay) + j) / 2 < 2 ^ 32 := by
  have h1 := S.cnt_le lay
  have h2 : leaf / S.grp lay ≤ leaf := Nat.div_le_self _ _
  have h3 : S.cnt lay * (leaf / S.grp lay) ≤ 512 * leaf :=
    (Nat.mul_le_mul_right _ h1).trans (Nat.mul_le_mul_left _ h2)
  omega

section Agree
variable {S} {F : FamAddr} {T T' : Answers} (hC : FamAgree S F T T')
include hC

theorem eval_outF {α : Type} {p : M α} (h : Respects (FamOut S F) p) :
    evalWithAnswerFn T' p = evalWithAnswerFn T p :=
  h.eval_eq hC.out

/-- **Seeds of leaves outside `F` are unchanged** (they read other cells, or the other halves of `F`'s cells). -/
theorem wotsSeed_outF (hF : F.fam * S.grp F.lay < 2 ^ 24) {lay : Layer} {tree leaf : Nat} (hleaf : leaf < 2 ^ 24)
    (hna : ¬FamAlias S F lay tree leaf) (i : Nat) :
    WCT9.wotsSeed T' lay tree leaf i = WCT9.wotsSeed T lay tree leaf i := by
  rw [S.seed, S.seed]
  congr 2
  funext j
  set o := S.cnt lay * (leaf / S.grp lay) + j.val with ho
  have hj : j.val < S.cnt lay := lt_of_lt_of_le j.isLt (S.size_le _ _)
  have ho2 : o / 2 < 2 ^ 32 := ord_pair_lt S lay hleaf hj
  by_cases hcell : ∃ j', j' < S.cnt F.lay ∧ WCT9.lowerSeedHeader lay tree (o / 2) =
      WCT9.lowerSeedHeader F.lay F.tree (ordS S F j' / 2)
  · obtain ⟨j', hj', he⟩ := hcell
    unfold WCT9.lowerSeedHeader at he
    obtain ⟨-, hl, ht, hp, -⟩ := header_fields he
    have hlay : lay = F.lay := Fin.ext (by
      rwa [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
        Nat.mod_eq_of_lt (lt_trans F.lay.isLt (by decide))] at hl)
    have hFl : F.fam < 2 ^ 24 := by
      have := S.grp_pos F.lay
      have : F.fam ≤ F.fam * S.grp F.lay := Nat.le_mul_of_pos_right _ this
      omega
    have hoF : ordS S F j' / 2 < 2 ^ 32 := by
      have h1 := S.cnt_le F.lay
      have : S.cnt F.lay * F.fam ≤ 512 * F.fam := Nat.mul_le_mul_right _ h1
      unfold ordS; omega
    rw [Nat.mod_eq_of_lt ho2, Nat.mod_eq_of_lt hoF] at hp
    have hpair : WCT9.lowerSeedPair lay tree (o / 2) = WCT9.lowerSeedPair F.lay F.tree (o / 2) := by
      unfold WCT9.lowerSeedPair privatePair
      rw [header_congr (by rw [hlay]) ht rfl]
    rw [hpair]
    subst hlay
    apply hC.half o ⟨j', hj', hp⟩
    intro j'' hj'' hoe
    apply hna
    refine ⟨rfl, ht, ?_⟩
    -- equal ordinals: same family
    unfold ordS at hoe
    rw [ho] at hoe
    rcases Nat.lt_trichotomy (leaf / S.grp F.lay) F.fam with hlt | heq | hgt
    · exfalso
      have : S.cnt F.lay * (leaf / S.grp F.lay) + S.cnt F.lay ≤ S.cnt F.lay * F.fam := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · exact heq
    · exfalso
      have : S.cnt F.lay * F.fam + S.cnt F.lay ≤ S.cnt F.lay * (leaf / S.grp F.lay) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hgt
      omega
  · have hq : T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2)))) =
        T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2)))) :=
      hC.out _ (fun j' hj' he => hcell ⟨j', hj', he⟩)
    unfold WCT9.lowerSeedPair privatePair privateHash
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change WCT9.seedHalf ((T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 0 128,
        (T' (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 128 128) o =
      WCT9.seedHalf ((T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 0 128,
        (T (.inr (.inl (WCT9.lowerSeedHeader lay tree (o / 2))))).extractLsb' 128 128) o
    rw [hq]
end Agree

#print axioms respects_famOut
#print axioms wotsSeed_outF
end ClaudeWCT.W9.T3.Security.Wots.FamRestart
