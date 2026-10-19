import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsFamCaps
import SigGolfCandidate.ClaudeWCT_Arith_GroupedFamilyS

/-! # The v6 seed families as an interface (r3-lean-seedfam; for the scheme / top-bytes porters)

The family restart (WotsFam*.lean) is proved for any `FamScheme S` with reveal caps `FamCaps S`. For the v6 images
(opus-crumbs img-v6, `scripts/check_seeds_v6.py`) the scheme side must discharge exactly two statements:

* `V6SeedSpec` — the WOTS seeds are family evaluations:
  - TOP (layer 0): 4-leaf families, 39 coefficients at ordinals `39·(leaf/4) + i` (carry-packed halves of
    `lowerSeedPair 0 tree`), points `((leaf & 3) << 6) + j + 1 = (leaf % 4)·64 + j + 1 ≤ 256`;
  - LOWER: 7-leaf families, ordinals `38·(leaf/7) + i`, `5·r + 3` coefficients (`r = 7`, or the remainder `2` for L1 /
    `1` for L2, L3 in the last family), points `(leaf % 7)·43 + j + 1 ≤ 301`;
* `V6ZeroSpec` — every leaf's reference digits have at most 9 (top) / 5 (lower) zeros (`producerZeroCap`).

From them, `v6Scheme` / `v6Caps` are the `FamScheme` / `FamCaps` the port consumes. Facts used by the restart and the
closing are proved here: points distinct and `< 1024` (top `≤ 256`), per-test charge `4·54 = 216` (top) and
`7·43 = 301` (lower) `≤ 305` (the live closing bound, `FinalG`), degree `38` top (`39` coefficients), and the reveal budget
`9·4 + 3 = 39` (top), `5·r + 3` (lower).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.FamRestart.V6
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open ClaudeWCT.Arith.SideChannel.GroupedFamily (gptS gptS_injective gptS_lt)
attribute [local instance] Classical.propDecidable

/-- Leaves per family. -/
def grp (lay : Layer) : Nat := if lay = 0 then 4 else 7
/-- Ordinal base per family. -/
def cnt (lay : Layer) : Nat := if lay = 0 then 39 else 38
/-- Point stride. -/
def stride (lay : Layer) : Nat := if lay = 0 then 64 else 43
/-- Coefficients of family `f` (the last lower family is short). -/
def size (lay : Layer) (f : Nat) : Nat := if lay = 0 then 39 else 5 * min 7 (2 ^ height lay - 7 * f) + 3
/-- Evaluation point: chains below `chainCount` at `(leaf % grp)·stride + i + 1`; the unused address slots
`chainCount ≤ i < 58` in a separate junk region above `grp·stride` (lower `302 + l·15 + (i − 43)`), so all points of a
family are distinct and `< 1024`. The images never compute junk seeds. -/
def point (lay : Layer) (leaf i : Nat) : Nat :=
  if i < chainCount lay then (leaf % grp lay) * stride lay + i + 1
  else grp lay * stride lay + (leaf % grp lay) * (58 - chainCount lay) + (i - chainCount lay) + 1
/-- Zero-digit cap per leaf. -/
def zcap (lay : Layer) : Nat := if lay = 0 then 9 else 5

/-- **Scheme obligation 1**: WOTS seeds are v6 family evaluations. -/
def V6SeedSpec : Prop :=
  ∀ (T : Answers) (lay : Layer) (tree leaf i : Nat), WCT9.wotsSeed T lay tree leaf i =
    ClaudeWCT.Arith.familyEval (List.ofFn fun j : Fin (size lay (leaf / grp lay)) =>
      WCT9.seedHalf (evalWithAnswerFn T (WCT9.lowerSeedPair lay tree ((cnt lay * (leaf / grp lay) + j) / 2)))
        (cnt lay * (leaf / grp lay) + j)) (point lay leaf i)

/-- **Scheme obligation 2**: per-leaf zero-digit caps of the reference digits. -/
def V6ZeroSpec : Prop :=
  ∀ {U : Finset HashInput} (R : Tables U) (L : LeafAddr),
    (Finset.univ.filter fun c : Fin (chainCount L.lay) =>
      CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 0).card ≤ zcap L.lay

theorem size_le (lay : Layer) (f : Nat) : size lay f ≤ cnt lay := by
  unfold size cnt
  split_ifs
  · exact le_rfl
  · have : min 7 (2 ^ height lay - 7 * f) ≤ 7 := min_le_left _ _
    omega

/-- The v6 family scheme (given the seed obligation). -/
def v6Scheme (h : V6SeedSpec) : FamScheme where
  grp := grp
  cnt := cnt
  size := size
  stride := stride
  point := point
  grp_pos lay := by unfold grp; split_ifs <;> decide
  cnt_le lay := by unfold cnt; split_ifs <;> decide
  size_le := size_le
  point_eq lay leaf i hi := by unfold point; rw [if_pos hi]
  seed := h

/-- The v6 reveal caps (given the zero obligation). -/
def v6Caps (hs : V6SeedSpec) (hz : V6ZeroSpec) : FamCaps (v6Scheme hs) where
  zcap := zcap
  zeros_le R L := hz R L
  size_ge lay f := by
    show zcap lay * min (grp lay) (2 ^ height lay - grp lay * f) + 3 ≤ size lay f
    unfold zcap grp size
    split_ifs
    · have : min 4 (2 ^ height lay - 4 * f) ≤ 4 := min_le_left _ _
      omega
    · exact le_rfl

/-! ### Facts used by the restart and the closing -/

/-- Points of the family chains `(l, c)` are `gptS (stride lay) (l, c)`; top points stay `≤ 256`. -/
theorem top_point_le (l : Fin 4) (c : Fin 54) : gptS 64 (l, c) ≤ 256 := by
  unfold gptS; have := l.isLt; have := c.isLt; omega

theorem top_points_injective : Function.Injective (gptS 64 (g := 4) (w := 54)) := gptS_injective (by decide)
theorem lower_points_injective : Function.Injective (gptS 43 (g := 7) (w := 43)) := gptS_injective le_rfl
theorem top_points_lt (c : Fin 4 × Fin 54) : gptS 64 c < 1024 := gptS_lt (by decide) c
theorem lower_points_lt (c : Fin 7 × Fin 43) : gptS 43 c < 1024 := gptS_lt (by decide) c

/-- `((leaf & 3) << 6) + j + 1 = (leaf % 4)·64 + j + 1`. -/
theorem top_point_bits (leaf j : Nat) : ((leaf &&& 3) <<< 6) + j + 1 = (leaf % 4) * 64 + j + 1 := by
  rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod leaf 2]

/-- Per-test charges (chains per family) against the live closing bound `305` (`FinalG.seedErrorBound_of_charge`). -/
theorem charges : 4 * 54 = 216 ∧ 216 ≤ 305 ∧ 7 * 43 = 301 ∧ 301 ≤ 305 := by decide

/-- Top: 39 coefficients (degree 38) and the reveal budget `9·4 + 3 = 39`. -/
theorem top_budget : cnt 0 = 39 ∧ size 0 0 = 39 ∧ 9 * 4 + 3 = 39 := by decide

/-- Reveal bound of a top family: at most 9 revealed seeds per leaf leave 3 free degrees. -/
theorem top_revealed_card_le (Rev : Finset (Fin 4 × Fin 54)) (h : ∀ l : Fin 4, (Rev.filter fun c => c.1 = l).card ≤ 9) :
    Rev.card + 3 ≤ 39 := by
  have := ClaudeWCT.Arith.SideChannel.GroupedFamily.revealed_card_leW (g := 4) (w := 54) (r := 9) Rev h
  omega

#print axioms v6Scheme
#print axioms v6Caps
#print axioms top_point_bits
end ClaudeWCT.W9.T3.Security.Wots.FamRestart.V6
