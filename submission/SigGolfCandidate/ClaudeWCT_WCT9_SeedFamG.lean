import SigGolfCandidate.ClaudeWCT_WCT9_Core
import SigGolfCandidate.ClaudeWCT_WCT9_Correctness

/-!
# `g`-leaf lower seed families (opus-crumbs retune; g = 4..7 under study, 16 in the original plan), scheme side, additive

Every group of `g` consecutive leaves of a lower tree shares one GF(2^128) polynomial family of
`lowerFamCoefCount g = 5g + 3` coefficients. Coefficient `j` of family `f` has ordinal `(5g+3)·f + j` and is read with
the existing carry packing `packedSecret (lowerSeedPair lay tree)` (ordinal `k` is half `k % 2` of private pair
`k / 2`; the carry is threaded across families, so a family with an odd first ordinal starts with the high half left by
the previous one). The seed of chain `i` of leaf `L` is the family of `L / g` evaluated at
`groupedPoint g L i = (L % g)·43 + i + 1` (points `1 ..= 43 g`, `< 1024` for `g ≤ 23`, distinct within a family).

These definitions sit alongside `lowerCoefs` / `buildLeafPF` / `buildTreeP` (Core.lean); nothing existing is changed.
Installing them is the one-line switch `buildTreeP ↦ buildTreePG` in `signLayersBC` (see the porter notes).
-/

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness

/-- Point stride per leaf of a family (the lower chain count). -/
def lowerFamStride : Nat := 43
/-- Coefficients per lower family of `g` leaves: 5 revealed seeds per leaf, plus 3. -/
def lowerFamCoefCount (g : Nat) : Nat := 5 * g + 3
/-- The family of a lower leaf. -/
def lowerFamOf (g leaf : Nat) : Nat := leaf / g
/-- Ordinal of coefficient `j` of family `fam` (the packed-half index in `lowerSeedPair lay tree`). -/
def lowerFamCoefOrdinal (g fam j : Nat) : Nat := lowerFamCoefCount g * fam + j
/-- Evaluation point of chain `chain` of leaf `leaf` in its family. -/
def groupedPoint (g leaf chain : Nat) : Nat := leaf % g * lowerFamStride + chain + 1

/-- The `5g + 3` coefficients of family `fam` (carry threaded through `packedSecret`). -/
def lowerCoefsG (g : Nat) (lay : Layer) (tree fam : Nat) (carry : Digest) : M (List Digest × Digest) :=
  (List.range (lowerFamCoefCount g)).foldlM (fun (state : List Digest × Digest) j => do
    let (coef, carry) ← packedSecret (lowerSeedPair lay tree) (lowerFamCoefOrdinal g fam j) state.2
    pure (state.1 ++ [coef], carry)) ([], carry)

/-- The seed of chain `chain` of leaf `leaf` from its family's coefficients. -/
def lowerFamilySeedG (g : Nat) (coefs : List Digest) (leaf chain : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval coefs (groupedPoint g leaf chain)

/-- A lower leaf from its family's coefficients (no private query: the family is built once per `g` leaves). -/
def buildLeafPG (g : Nat) (lay : Layer) (tree leaf : Nat) (digits : List Nat) (coefs : List Digest) :
    M (Digest × List Digest) := do
  let state ← (List.range (chainCount lay)).foldlM
    (fun (state : List Digest × List Digest) i => do
      let digit := digits.getD i 0
      let value ← chainW lay tree leaf i 0 digit (lowerFamilySeedG g coefs leaf i)
      let last ← chainW lay tree leaf i digit (maxDigit lay i - digit) value
      pure (state.1 ++ [last], state.2 ++ [value])) ([], [])
  let root ← lowerLeafHash lay tree leaf state.1
  pure (root, state.2)

/-- Lower tree of layer `lay ≥ 1` with `g`-leaf families: the family is (re)built at every leaf `≡ 0 (mod g)`, the
coefficients are kept for the next `g - 1` leaves, and the packing carry is threaded across families. -/
def buildTreePG (g : Nat) (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    M (List (List Digest) × List Digest) := do
  let state ← (List.range (2 ^ height lay)).foldlM
    (fun (state : List Digest × List Digest × List Digest × Digest) leaf => do
      let (coefs, carry) ← if leaf % g = 0 then
          lowerCoefsG g lay tree (lowerFamOf g leaf) state.2.2.2
        else pure (state.2.2.1, state.2.2.2)
      let (root, values) ← buildLeafPG g lay tree leaf (if leaf = selected then digits else []) coefs
      pure (state.1 ++ [root], (if leaf = selected then values else state.2.1), coefs, carry)) ([], [], [], 0)
  let levels ← buildLevelsBelow 3 lay.val tree (height lay) state.1
  pure (levels, state.2.1)

/-- `signLayersBC` with `g`-leaf lower families (the only change: `buildTreePG g`). -/
def signLayersBCG (g : Nat) (cache : Cache) (index : Nat) : Nat → LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let found ← layerCounterSearch lay tree leaf msg 0 (searchLimit lay)
      if n = 0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_, digits) := found | pure none
        let (levels, values) ← buildTreePG g lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := topPair lay levels
        let some previous ← signLayersBCG g cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))

/-! ### Security-facing view (answers-level), alongside `famCoefN` / `wotsSeed` (Correctness.lean). -/

/-- Coefficient `j` of lower family `fam`: the packed half `(5g+3)·fam + j` of `lowerSeedPair lay tree`. -/
def lowerFamCoefNG (g : Nat) (answers : Answers) (lay : Layer) (tree fam j : Nat) : Digest :=
  seedHalf (evalWithAnswerFn answers (lowerSeedPair lay tree (lowerFamCoefOrdinal g fam j / 2)))
    (lowerFamCoefOrdinal g fam j)
/-- The lower WOTS seed of chain `i` of leaf `leaf` under `g`-leaf families. -/
def lowerSeedG (g : Nat) (answers : Answers) (lay : Layer) (tree leaf i : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval
    (List.ofFn fun j : Fin (lowerFamCoefCount g) => lowerFamCoefNG g answers lay tree (lowerFamOf g leaf) j.val)
    (groupedPoint g leaf i)

/-! ### Arithmetic facts -/

theorem groupedPoint_pos (g leaf chain : Nat) : 1 ≤ groupedPoint g leaf chain := by
  unfold groupedPoint; omega

/-- Points stay at most `43 g`. -/
theorem groupedPoint_le {g : Nat} (hg : 0 < g) (leaf chain : Nat) (hc : chain < lowerFamStride) :
    groupedPoint g leaf chain ≤ 43 * g := by
  have hm := Nat.mod_lt leaf hg
  unfold groupedPoint lowerFamStride at *
  have : leaf % g * 43 ≤ (g - 1) * 43 := Nat.mul_le_mul_right _ (by omega)
  have : (g - 1) * 43 + 43 = 43 * g := by
    rcases g with _ | g
    · omega
    · simp only [Nat.add_sub_cancel]; ring
  omega

/-- Points are below `1024` (the `gfMulPt` / `HornRun` domain `< 2^10`) for `g ≤ 23`. -/
theorem groupedPoint_lt_1024 {g : Nat} (hg : 0 < g) (hg23 : g ≤ 23) (leaf chain : Nat) (hc : chain < lowerFamStride) :
    groupedPoint g leaf chain < 1024 :=
  lt_of_le_of_lt (groupedPoint_le hg leaf chain hc) (by omega)

/-- Points are distinct within a family: equal family and equal point give equal leaf and chain. -/
theorem groupedPoint_inj {g leaf leaf' chain chain' : Nat} (hg : 0 < g) (hc : chain < lowerFamStride)
    (hc' : chain' < lowerFamStride) (hf : lowerFamOf g leaf = lowerFamOf g leaf')
    (hp : groupedPoint g leaf chain = groupedPoint g leaf' chain') : leaf = leaf' ∧ chain = chain' := by
  unfold groupedPoint lowerFamOf lowerFamStride at *
  have h1 := Nat.div_add_mod leaf g
  have h2 := Nat.div_add_mod leaf' g
  have hm := Nat.mod_lt leaf hg
  have hm' := Nat.mod_lt leaf' hg
  have hmod : leaf % g = leaf' % g := by omega
  refine ⟨?_, by omega⟩
  rw [← h1, ← h2, hf, hmod]

/-- Coefficient ordinals are distinct across families. -/
theorem lowerFamCoefOrdinal_inj {g f f' j j' : Nat} (hj : j < lowerFamCoefCount g) (hj' : j' < lowerFamCoefCount g)
    (h : lowerFamCoefOrdinal g f j = lowerFamCoefOrdinal g f' j') : f = f' ∧ j = j' := by
  unfold lowerFamCoefOrdinal at h
  rcases Nat.lt_or_ge f f' with hlt | hge
  · exfalso
    have : lowerFamCoefCount g * f + lowerFamCoefCount g ≤ lowerFamCoefCount g * f' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    omega
  · rcases Nat.lt_or_ge f' f with hlt' | hge'
    · exfalso
      have : lowerFamCoefCount g * f' + lowerFamCoefCount g ≤ lowerFamCoefCount g * f := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt'
      omega
    · have hff : f = f' := by omega
      subst hff
      exact ⟨rfl, by omega⟩

/-- A family's chain slots `(leaf in family, chain)` revealing at most 5 per leaf reveal at most `5g`, so `|S| + 3`
fits the `5g + 3` coefficients. -/
theorem lowerFam_revealed_card_le {g : Nat} (S : Finset (Fin g × Fin 43))
    (h : ∀ l : Fin g, (S.filter fun p => p.1 = l).card ≤ 5) : S.card + 3 ≤ lowerFamCoefCount g := by
  have hs : S.card = ∑ l : Fin g, (S.filter fun p => p.1 = l).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.1)
  have hle : ∑ l : Fin g, (S.filter fun p => p.1 = l).card ≤ ∑ _l : Fin g, 5 := Finset.sum_le_sum fun l _ => h l
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  unfold lowerFamCoefCount
  omega

/-- Private-pair queries of one lower tree with `g · nf` leaves: the even ordinals below `(5g+3)·nf`, i.e.
`⌈(5g+3)·nf / 2⌉`. For `g = 4`: L1 (32 families) 368 (was 512), L2/L3 (16) 184 (was 256). -/
theorem lowerFam_pairs_g4 : (23 * 32 + 1) / 2 = 368 ∧ (23 * 16 + 1) / 2 = 184 := by decide

#print axioms groupedPoint_le
#print axioms groupedPoint_inj
#print axioms lowerFamCoefOrdinal_inj
#print axioms lowerFam_revealed_card_le
end ClaudeWCT.WCT9
