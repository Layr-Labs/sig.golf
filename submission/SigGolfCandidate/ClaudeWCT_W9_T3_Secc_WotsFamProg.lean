import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafProg
import SigGolfCandidate.ClaudeWCT_WCT9_SeedFamG
import SigGolfCandidate.ClaudeWCT_Arith_GroupedFamily

/-! # Family decomposition of the rest tables, any layer and group size (r3-lean-seedfam, port step R1)

The family analogue of the leaf decomposition (`Normalized.RawLeaf.ovL` / `rdL` / `restLaw_resampleL`). A family of
shape `(g, w, n)` — `g` leaves of `w` chains, `n` coefficients — at `F = (lay, tree, fam)` covers the leaves `g·fam + l`
(`l < g`); its data are the `n` coefficient halves (ordinals `n·fam + j` of `lowerSeedPair lay tree`) and the used halves
of the step-0 rows of its `g w` chains (`GChainW g w = Fin g × Fin w`). `ovF F R (K, f)` overrides them, `rdF` reads
them back, and the rest-table law is invariant under resampling them (`restLaw_resampleF`).
Instances: lower 7-leaf families `(7, 43, 38)` (`5·7 + 3`), top 4-leaf families `(4, 54, 4 r + 3)` (`r` reveals per top
leaf); `(1, 43, 8)` and `(1, 54, 24)` are today's leaf families.

Hypothesis `FamOk g w b n F`: `0 < g`, `w < 2^24`, the leaves of `F` below `2^24`, its tree below `2^40`, its ordinals' pair
indices below `2^32` (header injectivity).
-/

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
open ClaudeWCT.Arith.SideChannel.GroupedFamily (GChainW)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype

/-- A lower seed family: layer, tree and family index (`leaf / g`). -/
structure FamAddr where
  lay : Layer
  tree : Nat
  fam : Nat
  deriving DecidableEq

/-- Leaf `l` of family `F`. -/
def famLeaf (g : Nat) (F : FamAddr) (l : Fin g) : LeafAddr := ⟨F.lay, F.tree, g * F.fam + l.val⟩
/-- Chain `c = (l, i)` of family `F`. -/
def chainOfF (g w : Nat) (F : FamAddr) (c : GChainW g w) : ChainAddr := ⟨famLeaf g F c.1, c.2.val⟩

/-- Admissible family: `n ≤ b` coefficients at ordinals `b·fam + j`. -/
structure FamOk (g w b n : Nat) (F : FamAddr) : Prop where
  pos : 0 < g
  width : w < 2 ^ 24
  leaf : g * F.fam + g ≤ 2 ^ 24
  tree : F.tree < 2 ^ 40
  pair : b * F.fam + b ≤ 2 ^ 33
  size : n ≤ b

/-- Ordinal of coefficient `j` of family `F` (ordinal base `b` per family). -/
def ordF (b : Nat) {n : Nat} (F : FamAddr) (j : Fin n) : Nat := b * F.fam + j
/-- Tweak of the cell holding coefficient `j` of `F`. -/
def cellHdrF (b : Nat) {n : Nat} (F : FamAddr) (j : Fin n) : BitVec 128 :=
  WCT9.lowerSeedHeader F.lay F.tree (ordF b F j / 2)

/-- Lower `g`-leaf families use the scheme's ordinals `WCT9.lowerFamCoefOrdinal`. -/
theorem ordF_lower (g : Nat) (F : FamAddr) (j : Fin (WCT9.lowerFamCoefCount g)) :
    ordF (WCT9.lowerFamCoefCount g) F j = WCT9.lowerFamCoefOrdinal g F.fam j := rfl

variable {g w b n : Nat} {F : FamAddr}

theorem ordF_pair_lt (hF : FamOk g w b n F) (j : Fin n) : ordF b F j / 2 < 2 ^ 32 := by
  have h1 := j.isLt
  have h2 := hF.pair
  have h3 := hF.size
  unfold ordF
  omega

theorem cellHdrF_inj (hF : FamOk g w b n F) {j j' : Fin n} (h : cellHdrF b F j = cellHdrF b F j') :
    ordF b F j / 2 = ordF b F j' / 2 := by
  unfold cellHdrF WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordF_pair_lt hF j), Nat.mod_eq_of_lt (ordF_pair_lt hF j')] at this

theorem ordF_inj {j j' : Fin n} (h1 : ordF b F j / 2 = ordF b F j' / 2)
    (h2 : ordF b F j % 2 = ordF b F j' % 2) : j = j' := by
  apply Fin.ext; unfold ordF at h1 h2; omega

/-- The coefficient of `F` stored in half `bit` of the cell with tweak `tw`, if any. -/
noncomputable def slotAtF (b n : Nat) (F : FamAddr) (tw : BitVec 128) (bit : Nat) : Option (Fin n) :=
  if h : ∃ j : Fin n, cellHdrF b F j = tw ∧ ordF b F j % 2 = bit then some (Classical.choose h)
  else none

theorem slotAtF_some {tw : BitVec 128} {bit : Nat} {j : Fin n} (h : slotAtF b n F tw bit = some j) :
    cellHdrF b F j = tw ∧ ordF b F j % 2 = bit := by
  unfold slotAtF at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem slotAtF_self (hF : FamOk g w b n F) (j : Fin n) :
    slotAtF b n F (cellHdrF b F j) (ordF b F j % 2) = some j := by
  have hex : ∃ j' : Fin n, cellHdrF b F j' = cellHdrF b F j ∧ ordF b F j' % 2 = ordF b F j % 2 :=
    ⟨j, rfl, rfl⟩
  unfold slotAtF
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  rw [ordF_inj (cellHdrF_inj hF h1) h2]

/-- `priv` with `F`'s coefficient halves replaced by `K`. -/
noncomputable def ovPrivF (b n : Nat) (F : FamAddr) (priv : FullGame.FullTable) (K : Fin n → Digest) :
    FullGame.FullTable
  | .inl tw => ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw))))
  | .inr x => priv (.inr x)

theorem ovPrivF_inl (priv : FullGame.FullTable) (K : Fin n → Digest) (tw : BitVec 128) :
    ovPrivF b n F priv K (.inl tw) = ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))) := rfl

theorem ovPrivF_cell (hF : FamOk g w b n F) (priv : FullGame.FullTable) (K : Fin n → Digest)
    (j : Fin n) : halfOf (ordF b F j % 2) (ovPrivF b n F priv K (.inl (cellHdrF b F j))) = K j := by
  rw [ovPrivF_inl]
  unfold halfOf
  by_cases h0 : ordF b F j % 2 = 0
  · rw [if_pos h0]
    have hs := slotAtF_self hF j
    rw [h0] at hs
    rw [hs, low, ChainGraph.joinOutput_low]
    rfl
  · rw [if_neg h0]
    have hs := slotAtF_self hF j
    rw [show ordF b F j % 2 = 1 by omega] at hs
    rw [hs, high, ChainGraph.joinOutput_high]
    rfl

/-! ### Step-0 rows of the family's chains -/

theorem famLeaf_lt (hF : FamOk g w b n F) (l : Fin g) : (famLeaf g F l).leaf < 2 ^ 24 := by
  have := l.isLt; have := hF.leaf
  unfold famLeaf; simp only; omega

/-- Step-0 rows of distinct family chains are distinct. -/
theorem chainRowF_zero_inj (hF : FamOk g w b n F) {c c' : GChainW g w} {v v' : Digest}
    (h : chainRowW (chainOfF g w F c) 0 v = chainRowW (chainOfF g w F c') 0 v') : c = c' ∧ v = v' := by
  have hc := c.2.isLt; have hc' := c'.2.isLt
  have hw := hF.width
  obtain ⟨hal, hcc, -, hv⟩ := chainInputW_eq_chainRowW (a := chainOfF g w F c')
    (by unfold chainOfF; simp only; omega) (by unfold chainOfF; simp only; omega) (by omega) (by omega) h
  have hL := hal.eq_of_lt hF.tree (lt_trans (famLeaf_lt hF c.1) (by norm_num)) hF.tree
    (lt_trans (famLeaf_lt hF c'.1) (by norm_num))
  have hleaf := congrArg LeafAddr.leaf hL
  unfold chainOfF famLeaf at hleaf hcc
  simp only at hleaf hcc
  have e1 : c.1 = c'.1 := Fin.ext (by omega)
  exact ⟨Prod.ext e1 (Fin.ext hcc), hv⟩

/-- If `input` is the step-0 row of a chain of `F` at `v`, that `(c, v)`. -/
noncomputable def zeroOfF (g w : Nat) (F : FamAddr) (input : HashInput) : Option (GChainW g w × Digest) :=
  if h : ∃ p : GChainW g w × Digest, input = chainRowW (chainOfF g w F p.1) 0 p.2 then some (Classical.choose h) else none

theorem zeroOfF_some {input : HashInput} {p : GChainW g w × Digest} (h : zeroOfF g w F input = some p) :
    input = chainRowW (chainOfF g w F p.1) 0 p.2 := by
  unfold zeroOfF at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem zeroOfF_chainRow (hF : FamOk g w b n F) (c : GChainW g w) (v : Digest) :
    zeroOfF g w F (chainRowW (chainOfF g w F c) 0 v) = some (c, v) := by
  cases h : zeroOfF g w F (chainRowW (chainOfF g w F c) 0 v) with
  | none =>
      unfold zeroOfF at h
      rw [dif_pos ⟨(c, v), rfl⟩] at h
      cases h
  | some p =>
      have he := zeroOfF_some h
      obtain ⟨h1, h2⟩ := chainRowF_zero_inj hF he
      rw [show p = (c, v) from Prod.ext h1.symm h2.symm]

/-- The used half of family chain `c`'s step-0 row. -/
def zhF (g w : Nat) (F : FamAddr) (c : GChainW g w) : Bool := zh (famLeaf g F c.1) c.2.val

/-! ### Override and readback in the normalized tables -/

variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse ⊆ U)

/-- Family data: the `5g + 3` coefficients and the step-0 row functions of the `43 g` chains. -/
abbrev FamData (g w n : Nat) := (Fin n → Digest) × (GChainW g w → Digest → Digest)

/-- `pub` with the used halves of `F`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubF (g w : Nat) (F : FamAddr) (pub : U → HashOutput) (f : GChainW g w → Digest → Digest) :
    U → HashOutput := fun x =>
  match zeroOfF g w F x.val with
  | some p => joinHalf (zhF g w F p.1) (f p.1 p.2) (WCT9.halfOf (!zhF g w F p.1) (pub x))
  | none => pub x

noncomputable def ovF (g w b n : Nat) (F : FamAddr) (R : Tables U) (y : FamData g w n) : Tables U :=
  (ovPrivF b n F R.1 y.1, ovPubF g w F R.2 y.2)

noncomputable def rdF (g w b n : Nat) (F : FamAddr) (R : Tables U) : FamData g w n :=
  (fun j => halfOf (ordF b F j % 2) (R.1 (.inl (cellHdrF b F j))),
    fun c v => WCT9.halfOf (zhF g w F c) (R.2 ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩))

include hU in
theorem ovPubF_zero (hF : FamOk g w b n F) (pub : U → HashOutput) (f : GChainW g w → Digest → Digest) (c : GChainW g w)
    (v : Digest) :
    ovPubF g w F pub f ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩ =
      joinHalf (zhF g w F c) (f c v)
        (WCT9.halfOf (!zhF g w F c) (pub ⟨chainRowW (chainOfF g w F c) 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩)) := by
  unfold ovPubF
  simp only [zeroOfF_chainRow hF]

include hU in
theorem rdF_ovF (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) : rdF hU g w b n F (ovF g w b n F R y) = y := by
  obtain ⟨K, f⟩ := y
  unfold rdF ovF
  refine Prod.ext ?_ ?_
  · funext j
    exact ovPrivF_cell hF R.1 K j
  · funext c v
    simp only
    rw [ovPubF_zero hU hF, halfOf_joinHalf]

include hU in
theorem ovF_ovF_rdF (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) :
    ovF g w b n F (ovF g w b n F R y) (rdF hU g w b n F R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨K, f⟩ := y
  unfold ovF rdF
  simp only
  refine Prod.ext ?_ ?_
  · funext coord
    rcases coord with tw | x
    · show ovPrivF b n F (ovPrivF b n F priv K) _ (.inl tw) = priv (.inl tw)
      rw [ovPrivF_inl, ovPrivF_inl]
      have e0 : ((slotAtF b n F tw 0).map (fun j => halfOf (ordF b F j % 2) (priv (.inl (cellHdrF b F j))))).getD
          (low (ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))))) = low (priv (.inl tw)) := by
        cases h : slotAtF b n F tw 0 with
        | none => simp only [Option.map_none, Option.getD_none, h, low, ChainGraph.joinOutput_low]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAtF_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1, if_true]
      have e1 : ((slotAtF b n F tw 1).map (fun j => halfOf (ordF b F j % 2) (priv (.inl (cellHdrF b F j))))).getD
          (high (ChainGraph.joinOutput (((slotAtF b n F tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAtF b n F tw 1).map K).getD (high (priv (.inl tw)))))) = high (priv (.inl tw)) := by
        cases h : slotAtF b n F tw 1 with
        | none => simp only [Option.map_none, Option.getD_none, h, high, ChainGraph.joinOutput_high]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAtF_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1]
            rfl
      rw [e0, e1]
      exact ChainGraph.joinOutput_parts _
    · rfl
  · funext x
    dsimp only
    unfold ovPubF
    cases hp : zeroOfF g w F x.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hx : x = ⟨chainRowW (chainOfF g w F p.1) 0 p.2, RawPrefix.chainRowW_mem hU _ _ _⟩ :=
          Subtype.ext (zeroOfF_some hp)
        subst hx
        simp only [halfOf_not_joinHalf, joinHalf_halfOf]

include hU in
/-- **Resampling a family's coefficients and step-0 rows preserves the rest-table law.** -/
theorem restLaw_resampleF (hF : FamOk g w b n F) {β : Type} (Φ : Tables U → PMF β) :
    (PMF.uniformOfFintype (Tables U)).bind Φ =
      (PMF.uniformOfFintype (Tables U)).bind
        (fun R => (PMF.uniformOfFintype (FamData g w n)).bind (fun y => Φ (ovF g w b n F R y))) := by
  have : Nonempty (FamData g w n) := ⟨(fun _ => 0, fun _ _ => 0)⟩
  have h := uniform_resample (Ω := Tables U) (X := fun _ => FamData g w n) (fun _ => 0)
    (fun _ R y => ovF g w b n F R y) (fun _ R => rdF hU g w b n F R) (fun R y => rdF_ovF hU hF R y)
    (fun R y => ovF_ovF_rdF hU hF R y) (fun _ _ => rfl)
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (Tables U)).bind
  funext R
  rw [PMF.bind_map]
  rfl

/-- After the override the coefficient cell half of `j` reads `K j`. -/
theorem raw_ovF_cell (hF : FamOk g w b n F) (R : Tables U) (y : FamData g w n) (j : Fin n) :
    halfOf (ordF b F j % 2) ((ovF g w b n F R y).1 (.inl (cellHdrF b F j))) = y.1 j :=
  ovPrivF_cell hF R.1 y.1 j

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawFam
