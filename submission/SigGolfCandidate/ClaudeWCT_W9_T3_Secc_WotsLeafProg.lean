import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsLeafCongr
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsPrefixGame

/-! # Leaf decomposition of the rest tables (campaign X1 stage B, step B3)

`ovL L R (K, f)` overrides leaf `L`'s family coefficient halves (24 top, 17 lower) by `K` and the low halves of the step-0
rows of `L`'s chains by `f`; `rdL` reads them back. The rest-table law is invariant under resampling this part
(`restLaw_resampleL`), and the decomposition leaves every query outside `L` unchanged (`leafAgree_ovL`). -/

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsLeafProg : Fintype Coordinate := coordinateFintype
namespace Leaf
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
variable {adversary : AdversaryP}

/-- Ordinal of coefficient `j` of leaf `L`. -/
def ordL (L : LeafAddr) (j : Fin (WCT9.famCount L.lay)) : Nat := WCT9.famOrdinal L.lay L.leaf j
/-- Tweak of the cell holding coefficient `j` of leaf `L`. -/
def cellHdr (L : LeafAddr) (j : Fin (WCT9.famCount L.lay)) : BitVec 128 := WCT9.lowerSeedHeader L.lay L.tree (ordL L j / 2)

theorem ordL_pair_lt {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (j : Fin (WCT9.famCount L.lay)) : ordL L j / 2 < 2 ^ 32 :=
  WCT9.famOrdinal_div_lt hL j.isLt
theorem cellHdr_inj {L : LeafAddr} (hL : L.leaf < 2 ^ 24) {j j' : Fin (WCT9.famCount L.lay)} (h : cellHdr L j = cellHdr L j') :
    ordL L j / 2 = ordL L j' / 2 := by
  unfold cellHdr WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordL_pair_lt hL j), Nat.mod_eq_of_lt (ordL_pair_lt hL j')] at this
theorem ordL_inj {L : LeafAddr} {j j' : Fin (WCT9.famCount L.lay)} (h1 : ordL L j / 2 = ordL L j' / 2)
    (h2 : ordL L j % 2 = ordL L j' % 2) : j = j' := by
  apply Fin.ext; unfold ordL WCT9.famOrdinal at h1 h2; omega

/-- The coefficient of `L` stored in half `b` (`0` low, `1` high) of the cell with tweak `tw`, if any. -/
noncomputable def slotAt (L : LeafAddr) (tw : BitVec 128) (b : Nat) : Option (Fin (WCT9.famCount L.lay)) :=
  if h : ∃ j : Fin (WCT9.famCount L.lay), cellHdr L j = tw ∧ ordL L j % 2 = b then some (Classical.choose h) else none
theorem slotAt_some {L : LeafAddr} {tw : BitVec 128} {b : Nat} {j : Fin (WCT9.famCount L.lay)} (h : slotAt L tw b = some j) :
    cellHdr L j = tw ∧ ordL L j % 2 = b := by
  unfold slotAt at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem slotAt_self {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (j : Fin (WCT9.famCount L.lay)) :
    slotAt L (cellHdr L j) (ordL L j % 2) = some j := by
  have hex : ∃ j' : Fin (WCT9.famCount L.lay), cellHdr L j' = cellHdr L j ∧ ordL L j' % 2 = ordL L j % 2 := ⟨j, rfl, rfl⟩
  unfold slotAt
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  rw [ordL_inj (cellHdr_inj hL h1) h2]
theorem slotAt_none {L : LeafAddr} {tw : BitVec 128} {b : Nat}
    (h : ∀ j : Fin (WCT9.famCount L.lay), cellHdr L j = tw → ordL L j % 2 ≠ b) : slotAt L tw b = none := by
  unfold slotAt
  rw [dif_neg]
  rintro ⟨j, h1, h2⟩
  exact h j h1 h2

/-- Low (`b = 0`) or high half of an output. -/
def halfOf (b : Nat) (output : HashOutput) : Digest := if b = 0 then low output else high output

/-- `priv` with `L`'s coefficient halves replaced by `K`. -/
noncomputable def ovPrivL (L : LeafAddr) (priv : FullGame.FullTable) (K : Fin (WCT9.famCount L.lay) → Digest) : FullGame.FullTable
  | .inl tw => ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAt L tw 1).map K).getD (high (priv (.inl tw))))
  | .inr x => priv (.inr x)

/-- If `input` is the step-0 row of chain `c < chainCount` of `L` at `v`, that `(c, v)`. -/
noncomputable def zeroOf (L : LeafAddr) (input : HashInput) : Option (Fin (chainCount L.lay) × Digest) :=
  if h : ∃ p : Fin (chainCount L.lay) × Digest, input = chainRowW ⟨L, p.1⟩ 0 p.2 then some (Classical.choose h)
  else none
theorem zeroOf_some {L : LeafAddr} {input : HashInput} {p : Fin (chainCount L.lay) × Digest}
    (h : zeroOf L input = some p) : input = chainRowW ⟨L, p.1⟩ 0 p.2 := by
  unfold zeroOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem chainRowW_zero_inj {L : LeafAddr} {c c' : Nat} {v v' : Digest} (hc : c < chainCount L.lay)
    (h : chainRowW ⟨L, c⟩ 0 v = chainRowW ⟨L, c'⟩ 0 v') (hc' : c' < chainCount L.lay) : c = c' ∧ v = v' := by
  have h1 : c < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  have h2 : c' < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  obtain ⟨-, hcc, -, hv⟩ := chainInputW_eq_chainRowW (a := ⟨L, c'⟩) h1 h2 (by omega) (by omega) h
  exact ⟨hcc, hv⟩
theorem zeroOf_chainRow (L : LeafAddr) (c : Fin (chainCount L.lay)) (v : Digest) :
    zeroOf L (chainRowW ⟨L, c⟩ 0 v) = some (c, v) := by
  cases h : zeroOf L (chainRowW ⟨L, c⟩ 0 v) with
  | none =>
      unfold zeroOf at h
      rw [dif_pos ⟨(c, v), rfl⟩] at h
      cases h
  | some p =>
      have he := zeroOf_some h
      obtain ⟨h1, h2⟩ := chainRowW_zero_inj c.isLt he p.1.isLt
      rw [show p = (c, v) from Prod.ext (Fin.ext h1.symm) h2.symm]
theorem zeroOf_none {L : LeafAddr} {input : HashInput} (h : zeroOf L input = none)
    (c : Fin (chainCount L.lay)) (v : Digest) : input ≠ chainRowW ⟨L, c⟩ 0 v := by
  rintro rfl
  rw [zeroOf_chainRow] at h
  cases h

/-- Pairing stage 1: the half of chain `c`'s step-0 row output that the chain uses (`chainHigh lay c 0`, the HIGH
half for a G chain of a lower layer, the low half otherwise). -/
def zh (L : LeafAddr) (c : Nat) : Bool := WCT9.chainHigh L.lay c 0
/-- `pub` with the used halves (`zh`) of `L`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubL (L : LeafAddr) (pub : referenceInputs adversary → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match zeroOf L x.val with
  | some p => joinHalf (zh L p.1) (f p.1 p.2) (WCT9.halfOf (!zh L p.1) (pub x))
  | none => pub x

/-- Leaf data: the 17 coefficients and the step-0 row functions of the chains. -/
abbrev LeafData (L : LeafAddr) := (Fin (WCT9.famCount L.lay) → Digest) × (Fin (chainCount L.lay) → Digest → Digest)
noncomputable def ovL (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) : RefTables adversary :=
  (ovPrivL L R.1 y.1, ovPubL L R.2 y.2)
noncomputable def rdL (L : LeafAddr) (R : RefTables adversary) : LeafData L :=
  (fun j => halfOf (ordL L j % 2) (R.1 (.inl (cellHdr L j))),
    fun c v => WCT9.halfOf (zh L c) (R.2 ⟨chainRowW ⟨L, c⟩ 0 v, PrefixGame.chainRowW_mem _ _ _⟩))

theorem ovPubL_zero (L : LeafAddr) (pub : referenceInputs adversary → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) (c : Fin (chainCount L.lay)) (v : Digest) :
    ovPubL L pub f ⟨chainRowW ⟨L, c⟩ 0 v, PrefixGame.chainRowW_mem _ _ _⟩ =
      joinHalf (zh L c) (f c v) (WCT9.halfOf (!zh L c) (pub ⟨chainRowW ⟨L, c⟩ 0 v, PrefixGame.chainRowW_mem _ _ _⟩)) := by
  unfold ovPubL
  simp only [zeroOf_chainRow]

theorem ovPrivL_inl (L : LeafAddr) (priv : FullGame.FullTable) (K : Fin (WCT9.famCount L.lay) → Digest) (tw : BitVec 128) :
    ovPrivL L priv K (.inl tw) = ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))) := rfl
theorem ovPrivL_cell {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (priv : FullGame.FullTable) (K : Fin (WCT9.famCount L.lay) → Digest)
    (j : Fin (WCT9.famCount L.lay)) : halfOf (ordL L j % 2) (ovPrivL L priv K (.inl (cellHdr L j))) = K j := by
  rw [ovPrivL_inl]
  unfold halfOf
  by_cases h0 : ordL L j % 2 = 0
  · rw [if_pos h0]
    have hs := slotAt_self hL j
    rw [h0] at hs
    rw [hs, low, ChainGraph.joinOutput_low]
    rfl
  · rw [if_neg h0]
    have hs := slotAt_self hL j
    rw [show ordL L j % 2 = 1 by omega] at hs
    rw [hs, high, ChainGraph.joinOutput_high]
    rfl

theorem rdL_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : RefTables adversary) (y : LeafData L) :
    rdL L (ovL L R y) = y := by
  obtain ⟨K, f⟩ := y
  unfold rdL ovL
  refine Prod.ext ?_ ?_
  · funext j
    exact ovPrivL_cell hL R.1 K j
  · funext c v
    simp only
    rw [ovPubL_zero, halfOf_joinHalf]

theorem ovL_ovL_rdL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : RefTables adversary) (y : LeafData L) :
    ovL L (ovL L R y) (rdL L R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨K, f⟩ := y
  unfold ovL rdL
  simp only
  refine Prod.ext ?_ ?_
  · funext coord
    rcases coord with tw | x
    · show ovPrivL L (ovPrivL L priv K) _ (.inl tw) = priv (.inl tw)
      rw [ovPrivL_inl, ovPrivL_inl]
      have e0 : ((slotAt L tw 0).map (fun j => halfOf (ordL L j % 2) (priv (.inl (cellHdr L j))))).getD
          (low (ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))))) = low (priv (.inl tw)) := by
        cases h : slotAt L tw 0 with
        | none => simp only [Option.map_none, Option.getD_none, h, low, ChainGraph.joinOutput_low]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAt_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1, if_true]
      have e1 : ((slotAt L tw 1).map (fun j => halfOf (ordL L j % 2) (priv (.inl (cellHdr L j))))).getD
          (high (ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))))) = high (priv (.inl tw)) := by
        cases h : slotAt L tw 1 with
        | none => simp only [Option.map_none, Option.getD_none, h, high, ChainGraph.joinOutput_high]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAt_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1]
            rfl
      rw [e0, e1]
      exact ChainGraph.joinOutput_parts _
    · rfl
  · funext x
    dsimp only
    unfold ovPubL
    cases hp : zeroOf L x.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hx : x = ⟨chainRowW ⟨L, p.1⟩ 0 p.2, PrefixGame.chainRowW_mem _ _ _⟩ := Subtype.ext (zeroOf_some hp)
        subst hx
        simp only [halfOf_not_joinHalf, joinHalf_halfOf]

noncomputable instance instFintypeLeafData (L : LeafAddr) : Fintype (LeafData L) := by
  unfold LeafData; infer_instance
instance instNonemptyLeafData (L : LeafAddr) : Nonempty (LeafData L) := ⟨(fun _ => 0, fun _ _ => 0)⟩

/-- Resampling `L`'s coefficients and step-0 rows preserves the rest-table law. -/
theorem restLaw_resampleL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) {β : Type} (F : RefTables adversary → PMF β) :
    (restLaw adversary).bind F =
      (restLaw adversary).bind (fun R => (PMF.uniformOfFintype (LeafData L)).bind (fun y => F (ovL L R y))) := by
  have h := uniform_resample (Ω := RefTables adversary) (X := fun _ => LeafData L) (fun _ => 0)
    (fun _ R y => ovL L R y) (fun _ R => rdL L R) (fun R y => rdL_ovL hL R y) (fun R y => ovL_ovL_rdL hL R y)
    (fun _ _ => rfl)
  unfold restLaw
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (RefTables adversary)).bind
  funext R
  rw [PMF.bind_map]
  rfl

theorem restTable_ovL_zero (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) (c : Fin (chainCount L.lay))
    (v : Digest) : restTable (ovL L R y) (.inl (.inr (chainRowW ⟨L, c⟩ 0 v))) =
      joinHalf (zh L c) (y.2 c v) (WCT9.halfOf (!zh L c) (restTable R (.inl (.inr (chainRowW ⟨L, c⟩ 0 v))))) := by
  rw [PrefixGame.restTable_mem _ _ (PrefixGame.chainRowW_mem _ _ _),
    PrefixGame.restTable_mem _ _ (PrefixGame.chainRowW_mem _ _ _)]
  exact ovPubL_zero L R.2 y.2 c v
theorem restTable_ovL_pub (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) (input : HashInput)
    (h : zeroOf L input = none) :
    restTable (ovL L R y) (.inl (.inr input)) = restTable R (.inl (.inr input)) := by
  by_cases hm : input ∈ referenceInputs adversary
  · rw [PrefixGame.restTable_mem _ _ hm, PrefixGame.restTable_mem _ _ hm]
    show ovPubL L R.2 y.2 ⟨input, hm⟩ = R.2 ⟨input, hm⟩
    unfold ovPubL
    simp only [h]
  · rw [PrefixGame.restTable_nonmem _ _ hm, PrefixGame.restTable_nonmem _ _ hm]
theorem restTable_ovL_tweak (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) (tw : BitVec 128)
    (h : ∀ j, cellHdr L j ≠ tw) : restTable (ovL L R y) (.inr (.inl tw)) = restTable R (.inr (.inl tw)) := by
  rw [PrefixGame.restTable_private, PrefixGame.restTable_private]
  show ovPrivL L R.1 y.1 (.inl tw) = R.1 (.inl tw)
  rw [ovPrivL_inl, slotAt_none (fun j hj => absurd hj (h j)), slotAt_none (fun j hj => absurd hj (h j))]
  exact ChainGraph.joinOutput_parts _
theorem eval_lowerSeedPair (T : Answers) (lay : Layer) (tree p : Nat) :
    evalWithAnswerFn T (WCT9.lowerSeedPair lay tree p) =
      ((T (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))).extractLsb' 0 128,
        (T (.inr (.inl (WCT9.lowerSeedHeader lay tree p)))).extractLsb' 128 128) := by
  unfold WCT9.lowerSeedPair privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl
/-! ### Programming uniform functions at a point -/

theorem uniform_map_equiv {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro x hx
    rw [if_neg]
    intro h
    apply hx
    rw [h]
    simp

/-- A uniform family of functions is a uniform family of functions programmed at fixed points `Y` with uniform
labels: `f c = update (g c) (Y c) (Lab c)`. -/
theorem uniform_program {ι : Type} [Fintype ι] [DecidableEq ι] (Y : ι → Digest) {β : Type}
    (G : (ι → Digest → Digest) → PMF β) :
    (PMF.uniformOfFintype (ι → Digest → Digest)).bind G =
      (PMF.uniformOfFintype ((ι → Digest → Digest) × (ι → Digest))).bind
        (fun p => G (fun c => Function.update (p.1 c) (Y c) (p.2 c))) := by
  let σ : (ι → Digest → Digest) × (ι → Digest) → (ι → Digest → Digest) × (ι → Digest) :=
    fun p => (fun c => Function.update (p.1 c) (Y c) (p.2 c), fun c => p.1 c (Y c))
  have hσ : ∀ p, σ (σ p) = p := by
    rintro ⟨g, z⟩
    refine Prod.ext ?_ ?_
    · funext c
      simp only [σ, Function.update_idem, Function.update_eq_self]
    · funext c
      simp only [σ, Function.update_self]
  let e : ((ι → Digest → Digest) × (ι → Digest)) ≃ ((ι → Digest → Digest) × (ι → Digest)) :=
    ⟨σ, σ, hσ, hσ⟩
  have h1 : (PMF.uniformOfFintype ((ι → Digest → Digest) × (ι → Digest))).bind
      (fun p => G (fun c => Function.update (p.1 c) (Y c) (p.2 c))) =
      ((PMF.uniformOfFintype ((ι → Digest → Digest) × (ι → Digest))).map e).bind (fun p => G p.1) := by
    rw [PMF.bind_map]
    rfl
  rw [h1, uniform_map_equiv, uniform_prod, PMF.bind_bind]
  congr 1
  funext g
  rw [PMF.bind_map]
  exact (PMF.bind_const _ _).symm

/-- The family seed of chain `c` for coefficients `K`. -/
noncomputable def seedOf {m : Nat} (K : Fin m → Digest) (c : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c)
/-- Step-0 rows programmed at the family seeds. -/
noncomputable def progF {n m : Nat} (g : Fin n → Digest → Digest) (Lab : Fin n → Digest) (K : Fin m → Digest) :
    Fin n → Digest → Digest :=
  fun c => Function.update (g c) (seedOf K c) (Lab c)

theorem restTable_ov_const (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (e s : Digest)
    (input : HashInput) :
    restTable (PrefixGame.ov a d R (fun _ _ => e, s)) (.inl (.inr input)) =
      match PrefixGame.rowOf a d input with
      | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) e
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (restTable R (.inl (.inr input))))
      | none => restTable R (.inl (.inr input)) := by
  cases hp : PrefixGame.rowOf a d input with
  | some p =>
      have hin := PrefixGame.rowOf_some hp
      simp only
      rw [hin, PrefixGame.restTable_ov_prefix a hd]
  | none =>
      simp only
      rw [PrefixGame.restTable_ov_nonprefix a _ _ _ hp]

/-! ### The honest table of the prefix game with the leaf overridden -/

theorem eval_chain_zero (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 0 v) = v := rfl

section Fill
variable {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
include hLleaf haL hac hd1

theorem fill_priv (X : LeafData L) (e : Digest) (coord : Coordinate) :
    PrefixGame.fillTable a (ovL L R X) e (.inr coord) = restTable (ovL L R X) (.inr coord) := by
  unfold PrefixGame.fillTable
  exact PrefixGame.restTable_ov_private a _ _ _

end Fill

end Leaf
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
/-- `pub` with the used halves (`zh`) of `L`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubL (L : LeafAddr) (pub : U → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) : U → HashOutput := fun x =>
  match zeroOf L x.val with
  | some p => joinHalf (zh L p.1) (f p.1 p.2) (WCT9.halfOf (!zh L p.1) (pub x))
  | none => pub x

/-- Leaf data: the 17 coefficients and the step-0 row functions of the chains. -/
noncomputable def ovL (L : LeafAddr) (R : Tables U) (y : LeafData L) : Tables U :=
  (ovPrivL L R.1 y.1, ovPubL L R.2 y.2)
noncomputable def rdL (L : LeafAddr) (R : Tables U) : LeafData L :=
  (fun j => halfOf (ordL L j % 2) (R.1 (.inl (cellHdr L j))),
    fun c v => WCT9.halfOf (zh L c) (R.2 ⟨chainRowW ⟨L, c⟩ 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩))

theorem ovPubL_zero (L : LeafAddr) (pub : U → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) (c : Fin (chainCount L.lay)) (v : Digest) :
    ovPubL L pub f ⟨chainRowW ⟨L, c⟩ 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩ =
      joinHalf (zh L c) (f c v) (WCT9.halfOf (!zh L c) (pub ⟨chainRowW ⟨L, c⟩ 0 v, RawPrefix.chainRowW_mem hU _ _ _⟩)) := by
  unfold ovPubL
  simp only [zeroOf_chainRow]

theorem rdL_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L) :
    rdL hU L (ovL L R y) = y := by
  obtain ⟨K, f⟩ := y
  unfold rdL ovL
  refine Prod.ext ?_ ?_
  · funext j
    exact ovPrivL_cell hL R.1 K j
  · funext c v
    simp only
    rw [ovPubL_zero hU, halfOf_joinHalf]

theorem ovL_ovL_rdL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L) :
    ovL L (ovL L R y) (rdL hU L R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨K, f⟩ := y
  unfold ovL rdL
  simp only
  refine Prod.ext ?_ ?_
  · funext coord
    rcases coord with tw | x
    · show ovPrivL L (ovPrivL L priv K) _ (.inl tw) = priv (.inl tw)
      rw [ovPrivL_inl, ovPrivL_inl]
      have e0 : ((slotAt L tw 0).map (fun j => halfOf (ordL L j % 2) (priv (.inl (cellHdr L j))))).getD
          (low (ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))))) = low (priv (.inl tw)) := by
        cases h : slotAt L tw 0 with
        | none => simp only [Option.map_none, Option.getD_none, h, low, ChainGraph.joinOutput_low]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAt_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1, if_true]
      have e1 : ((slotAt L tw 1).map (fun j => halfOf (ordL L j % 2) (priv (.inl (cellHdr L j))))).getD
          (high (ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
            (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))))) = high (priv (.inl tw)) := by
        cases h : slotAt L tw 1 with
        | none => simp only [Option.map_none, Option.getD_none, h, high, ChainGraph.joinOutput_high]
        | some j =>
            obtain ⟨h1, h2⟩ := slotAt_some h
            simp only [Option.map_some, Option.getD_some, halfOf, h2, h1]
            rfl
      rw [e0, e1]
      exact ChainGraph.joinOutput_parts _
    · rfl
  · funext x
    dsimp only
    unfold ovPubL
    cases hp : zeroOf L x.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hx : x = ⟨chainRowW ⟨L, p.1⟩ 0 p.2, RawPrefix.chainRowW_mem hU _ _ _⟩ := Subtype.ext (zeroOf_some hp)
        subst hx
        simp only [halfOf_not_joinHalf, joinHalf_halfOf]

include hU in
/-- Resampling `L`'s coefficients and step-0 rows preserves the rest-table law. -/
theorem restLaw_resampleL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) {β : Type} (F : Tables U → PMF β) :
    (PMF.uniformOfFintype (Tables U)).bind F =
      (PMF.uniformOfFintype (Tables U)).bind (fun R => (PMF.uniformOfFintype (LeafData L)).bind (fun y => F (ovL L R y))) := by
  have h := uniform_resample (Ω := Tables U) (X := fun _ => LeafData L) (fun _ => 0)
    (fun _ R y => ovL L R y) (fun _ R => rdL hU L R) (fun R y => rdL_ovL hU hL R y) (fun R y => ovL_ovL_rdL hU hL R y)
    (fun _ _ => rfl)
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (Tables U)).bind
  funext R
  rw [PMF.bind_map]
  rfl

include hU in
theorem raw_ovL_zero (L : LeafAddr) (R : Tables U) (y : LeafData L) (c : Fin (chainCount L.lay))
    (v : Digest) : raw (ovL L R y) (.inl (.inr (chainRowW ⟨L, c⟩ 0 v))) =
      joinHalf (zh L c) (y.2 c v) (WCT9.halfOf (!zh L c) (raw R (.inl (.inr (chainRowW ⟨L, c⟩ 0 v))))) := by
  rw [RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _),
    RawPrefix.raw_mem _ _ (RawPrefix.chainRowW_mem hU _ _ _)]
  exact ovPubL_zero hU L R.2 y.2 c v
theorem raw_ovL_pub (L : LeafAddr) (R : Tables U) (y : LeafData L) (input : HashInput)
    (h : zeroOf L input = none) :
    raw (ovL L R y) (.inl (.inr input)) = raw R (.inl (.inr input)) := by
  by_cases hm : input ∈ U
  · rw [RawPrefix.raw_mem _ _ hm, RawPrefix.raw_mem _ _ hm]
    show ovPubL L R.2 y.2 ⟨input, hm⟩ = R.2 ⟨input, hm⟩
    unfold ovPubL
    simp only [h]
  · rw [RawPrefix.raw_nonmem _ _ hm, RawPrefix.raw_nonmem _ _ hm]
theorem raw_ovL_tweak (L : LeafAddr) (R : Tables U) (y : LeafData L) (tw : BitVec 128)
    (h : ∀ j, cellHdr L j ≠ tw) : raw (ovL L R y) (.inr (.inl tw)) = raw R (.inr (.inl tw)) := by
  rw [RawPrefix.raw_private, RawPrefix.raw_private]
  show ovPrivL L R.1 y.1 (.inl tw) = R.1 (.inl tw)
  rw [ovPrivL_inl, slotAt_none (fun j hj => absurd hj (h j)), slotAt_none (fun j hj => absurd hj (h j))]
  exact ChainGraph.joinOutput_parts _
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
noncomputable def fillTable (a : ChainAddr) (R : Tables U) (e : Digest) : Answers := raw (RawPrefix.fill a R e)
include hU
theorem raw_ov_const (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (e s : Digest)
    (input : HashInput) :
    raw (RawPrefix.ov a d R (fun _ _ => e, s)) (.inl (.inr input)) =
      match PrefixGame.rowOf a d input with
      | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) e
          (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (raw R (.inl (.inr input))))
      | none => raw R (.inl (.inr input)) := by
  -- C3 (#866): a prefix row keeps the half `chainHigh` of its step (`restTable_ov_const`).
  cases hp : PrefixGame.rowOf a d input with
  | some p =>
      have hin := PrefixGame.rowOf_some hp
      simp only
      rw [hin, RawPrefix.raw_ov_prefix hU a hd]
  | none =>
      simp only
      rw [RawPrefix.raw_ov_nonprefix a _ _ _ hp]

/-! ### The honest table of the prefix game with the leaf overridden -/

theorem eval_chain_zero (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 0 v) = v := rfl

section Fill
variable {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hLleaf haL hac hd1

theorem fill_priv (X : LeafData L) (e : Digest) (coord : Coordinate) :
    fillTable a (ovL L R X) e (.inr coord) = raw (ovL L R X) (.inr coord) := by
  unfold fillTable RawPrefix.fill
  exact RawPrefix.raw_ov_private a _ _ _

end Fill
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem respects_coverP {α : Type} {p : M α} (h : ∀ c, Respects (UntouchedP c) p) :
    ∀ cs : List ChainAddr, Respects (fun q => ∀ c ∈ cs, UntouchedP c q) p
  | [] => Respects.mono' (h ⟨⟨0,0,0⟩,0⟩) (fun _ _ c hc => absurd hc List.not_mem_nil)
  | c::cs => Respects.mono' (Respects.inter (h c) (respects_coverP h cs)) (fun _ hq c' hc' => by
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hq.1
      · exact hq.2 c' hc')

theorem leafOut_of_coverP {L : LeafAddr} {q : Spec.Domain} (h : ∀ c ∈ coverAddrs L, UntouchedP c q) :
    LeafOut L q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · intro c step value hc hs heq
    exact h ⟨L,c⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨c,List.mem_range.mpr hc,rfl⟩)) step value hs heq
  · intro j hj heq
    apply h ⟨⟨L.lay,L.tree,0⟩,2*(WCT9.famOrdinal L.lay L.leaf j/2)⟩
      (List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩))
    change tweak=seedTweakP _
    rw [heq]
    unfold seedTweakP seedSlot seedTweak WCT9.lowerOrdinal WCT9.lowerSeedHeader
    simp only
    split <;> simp [Nat.mul_div_cancel_left]
  · trivial

theorem respects_leafOutP {α : Type} {p : M α} (h : ∀ c, Respects (UntouchedP c) p) (L : LeafAddr) :
    Respects (LeafOut L) p :=
  Respects.mono' (respects_coverP h (coverAddrs L)) fun _ hq => leafOut_of_coverP hq

theorem buildForest_out {L : LeafAddr} {T T' : Answers} (hC : LeafAgree L T T')
    (index : Nat) (selected : ForestSelection) (words : ForestWords) :
    ExecEq T T' (buildForest index selected words) (buildForest index selected words) := by
  have h := respects_leafOutP (fun a => CanonicalRef.respectsP_buildForest a index selected words) L
  exact ⟨h.eval_eq hC.out, congrArg List.length (h.queried_eq hC.out)⟩

theorem forestCommitment_out {L : LeafAddr} {T T' : Answers} (hC : LeafAgree L T T') (index : Nat) :
    CanonicalRef.forestCommitment T' index=CanonicalRef.forestCommitment T index := by
  have h := congrArg Prod.snd (buildForest_out hC index (forestSelectionFromOutput 0) (forestWordsFromOutput 0)).1
  simpa only [buildForest_commitment] using h

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame (high uniform_resample uniform_prod Hidden)
open SphincsSecurity.Concrete.PartialChainEndpoint (evaluate)
open ClaudeWCT.W9.T3.Security.Wots.Leaf

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
section Program
variable {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hU hLleaf haL hac hd1
end Program
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {messages : LeafAddr → LayerMsg} {L : LeafAddr} {T T' : Answers}
variable (hC : Congr messages L T T') (hLleaf : L.leaf<2^24)
include hC
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.WCT9 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem execEq_out {T T' : Answers} {L : LeafAddr} (hC : LeafAgree L T T')
    {α : Type} {p : M α} (h : Respects (LeafOut L) p) : ExecEq T T' p p :=
  ⟨h.eval_eq hC.out,congrArg List.length (h.queried_eq hC.out)⟩
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Leaf

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

theorem leafOut_encoding (L : LeafAddr) (e : Wots.Enc.EncIndex) :
    LeafOut L (.inl (.inr (Wots.Enc.encInput e))) := by
  intro c step value _ _ he
  have hn := nonEnc_chainRow ⟨L,c⟩ step value
  apply hn
  rw [←he]
  exact Wots.Enc.encInput_encHeader e

theorem leafAgree_normalize {L : LeafAddr} {R R' : Tables U}
    (hC : LeafAgree L (raw R) (raw R')) (hm : sourceMessages (raw R')=sourceMessages (raw R)) :
    LeafAgree L (answers hU R) (answers hU R') := by
  refine ⟨?_,?_⟩
  · intro query hq
    rcases query with (coin | input) | coordinate
    · exact hC.out _ hq
    · by_cases hu : input∈U
      · rw [show answers hU R' (.inl (.inr input))=(normalize hU R').2 ⟨input,hu⟩ from RawPrefix.raw_mem _ _ hu,
          show answers hU R (.inl (.inr input))=(normalize hU R).2 ⟨input,hu⟩ from RawPrefix.raw_mem _ _ hu]
        change MessageSwap.table zeroMessages (sourceMessages (raw R')) _ _ hU R'.2 ⟨input,hu⟩=
          MessageSwap.table zeroMessages (sourceMessages (raw R)) _ _ hU R.2 ⟨input,hu⟩
        have ht : MessageSwap.table zeroMessages (sourceMessages (raw R')) zeroMessages_fit (sourceMessages_fit (raw R')) hU=
            MessageSwap.table zeroMessages (sourceMessages (raw R)) zeroMessages_fit (sourceMessages_fit (raw R)) hU := by
          congr 1
        rw [ht]
        by_cases he : ∃e,Wots.Enc.encInput e=input
        · obtain ⟨e,rfl⟩ := he
          rw [MessageSwap.table_at,MessageSwap.table_at]
          exact (RawPrefix.raw_mem _ _ _).symm.trans ((hC.out _ (leafOut_encoding L _)).trans (RawPrefix.raw_mem _ _ _))
        · push_neg at he
          rw [MessageSwap.table_other _ _ _ _ _ _ _ he,MessageSwap.table_other _ _ _ _ _ _ _ he]
          exact (RawPrefix.raw_mem _ _ _).symm.trans ((hC.out _ hq).trans (RawPrefix.raw_mem _ _ _))
      · rw [show answers hU R' (.inl (.inr input))=(0 : HashOutput) from RawPrefix.raw_nonmem _ _ hu,
          show answers hU R (.inl (.inr input))=(0 : HashOutput) from RawPrefix.raw_nonmem _ _ hu]
    · exact hC.out _ hq
  · intro o ho hno
    rw [Wots.Leaf.eval_lowerSeedPair,Wots.Leaf.eval_lowerSeedPair,
      nonEnc hU R' _ (by trivial),nonEnc hU R _ (by trivial)]
    simpa only [Wots.Leaf.eval_lowerSeedPair] using hC.half o ho hno

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3.Security.Wots.Leaf
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
