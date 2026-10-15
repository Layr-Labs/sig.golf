import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafCongr
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGame

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
  if h : ∃ p : Fin (chainCount L.lay) × Digest, input = chainRow ⟨L, p.1⟩ 0 p.2 then some (Classical.choose h)
  else none
theorem zeroOf_some {L : LeafAddr} {input : HashInput} {p : Fin (chainCount L.lay) × Digest}
    (h : zeroOf L input = some p) : input = chainRow ⟨L, p.1⟩ 0 p.2 := by
  unfold zeroOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem chainRow_zero_inj {L : LeafAddr} {c c' : Nat} {v v' : Digest} (hc : c < chainCount L.lay)
    (h : chainRow ⟨L, c⟩ 0 v = chainRow ⟨L, c'⟩ 0 v') (hc' : c' < chainCount L.lay) : c = c' ∧ v = v' := by
  have h1 : c < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  have h2 : c' < 2 ^ 24 := by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega
  obtain ⟨-, hcc, -, hv⟩ := chainInput_eq_chainRow (a := ⟨L, c'⟩) h1 h2 (by omega) (by omega) h
  exact ⟨hcc, hv⟩
theorem zeroOf_chainRow (L : LeafAddr) (c : Fin (chainCount L.lay)) (v : Digest) :
    zeroOf L (chainRow ⟨L, c⟩ 0 v) = some (c, v) := by
  cases h : zeroOf L (chainRow ⟨L, c⟩ 0 v) with
  | none =>
      unfold zeroOf at h
      rw [dif_pos ⟨(c, v), rfl⟩] at h
      cases h
  | some p =>
      have he := zeroOf_some h
      obtain ⟨h1, h2⟩ := chainRow_zero_inj c.isLt he p.1.isLt
      rw [show p = (c, v) from Prod.ext (Fin.ext h1.symm) h2.symm]
theorem zeroOf_none {L : LeafAddr} {input : HashInput} (h : zeroOf L input = none)
    (c : Fin (chainCount L.lay)) (v : Digest) : input ≠ chainRow ⟨L, c⟩ 0 v := by
  rintro rfl
  rw [zeroOf_chainRow] at h
  cases h

/-- `pub` with the low halves of `L`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubL (L : LeafAddr) (pub : referenceInputs adversary → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match zeroOf L x.val with
  | some p => ChainGraph.joinOutput (f p.1 p.2) (high (pub x))
  | none => pub x

/-- Leaf data: the 17 coefficients and the step-0 row functions of the chains. -/
abbrev LeafData (L : LeafAddr) := (Fin (WCT9.famCount L.lay) → Digest) × (Fin (chainCount L.lay) → Digest → Digest)
noncomputable def ovL (L : LeafAddr) (R : RefTables adversary) (y : LeafData L) : RefTables adversary :=
  (ovPrivL L R.1 y.1, ovPubL L R.2 y.2)
noncomputable def rdL (L : LeafAddr) (R : RefTables adversary) : LeafData L :=
  (fun j => halfOf (ordL L j % 2) (R.1 (.inl (cellHdr L j))),
    fun c v => low (R.2 ⟨chainRow ⟨L, c⟩ 0 v, PrefixGame.chainRow_mem _ _ _⟩))

theorem ovPubL_zero (L : LeafAddr) (pub : referenceInputs adversary → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) (c : Fin (chainCount L.lay)) (v : Digest) :
    ovPubL L pub f ⟨chainRow ⟨L, c⟩ 0 v, PrefixGame.chainRow_mem _ _ _⟩ =
      ChainGraph.joinOutput (f c v) (high (pub ⟨chainRow ⟨L, c⟩ 0 v, PrefixGame.chainRow_mem _ _ _⟩)) := by
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
    rw [ovPubL_zero, low, ChainGraph.joinOutput_low]

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
        have hx : x = ⟨chainRow ⟨L, p.1⟩ 0 p.2, PrefixGame.chainRow_mem _ _ _⟩ := Subtype.ext (zeroOf_some hp)
        subst hx
        simp only [high, low, ChainGraph.joinOutput_high, ChainGraph.joinOutput_parts]

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
    (v : Digest) : restTable (ovL L R y) (.inl (.inr (chainRow ⟨L, c⟩ 0 v))) =
      ChainGraph.joinOutput (y.2 c v) (high (restTable R (.inl (.inr (chainRow ⟨L, c⟩ 0 v))))) := by
  rw [PrefixGame.restTable_mem _ _ (PrefixGame.chainRow_mem _ _ _),
    PrefixGame.restTable_mem _ _ (PrefixGame.chainRow_mem _ _ _)]
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
theorem famCoef_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : RefTables adversary)
    (K : Fin (WCT9.famCount L.lay) → Digest) (f : Fin (chainCount L.lay) → Digest → Digest)
    (j : Fin (WCT9.famCount L.lay)) :
    WCT9.famCoef (restTable (ovL L R (K, f))) L.lay L.tree L.leaf j = K j := by
  unfold WCT9.famCoef WCT9.famCoefN
  rw [eval_lowerSeedPair]
  have hc := ovPrivL_cell hL R.1 K j
  rw [show ovPrivL L R.1 K (.inl (cellHdr L j)) = restTable (ovL L R (K, f)) (.inr (.inl (cellHdr L j))) from rfl]
    at hc
  unfold halfOf at hc
  unfold WCT9.seedHalf
  unfold cellHdr ordL at hc
  split_ifs with h1 h2 h2
  · rw [if_pos h1] at hc; exact hc
  · rw [if_neg h1] at hc; exact hc
theorem wotsSeed_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : RefTables adversary)
    (K : Fin (WCT9.famCount L.lay) → Digest) (f : Fin (chainCount L.lay) → Digest → Digest) (c : Nat) :
    WCT9.wotsSeed (restTable (ovL L R (K, f))) L.lay L.tree L.leaf c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c) := by
  rw [WCT9.wotsSeed_fam]
  congr 2
  funext j
  exact famCoef_ovL hL R K f j
/-- The leaf override changes nothing outside `L`'s own halves and step-0 rows. -/
theorem leafAgree_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : RefTables adversary) (y : LeafData L) :
    LeafAgree L (restTable R) (restTable (ovL L R y)) := by
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (n | input) | (tw | x)
    · rfl
    · apply restTable_ovL_pub
      cases hz : zeroOf L input with
      | none => rfl
      | some p => exact absurd (zeroOf_some hz) (hq p.1 0 p.2 p.1.isLt (by omega))
    · exact restTable_ovL_tweak L R y tw (fun j he => hq j j.isLt he.symm)
    · rfl
  · obtain ⟨j, hj, hoj⟩ := ho
    rw [eval_lowerSeedPair, eval_lowerSeedPair]
    have hhdr : WCT9.lowerSeedHeader L.lay L.tree (o / 2) = cellHdr L ⟨j, hj⟩ := by
      unfold cellHdr ordL; rw [hoj]
    have hnone : slotAt L (cellHdr L ⟨j, hj⟩) (o % 2) = none := by
      apply slotAt_none
      intro j' h1 h2
      have e1 := cellHdr_inj hL h1
      apply hno j' j'.isLt
      unfold ordL at e1 h2
      unfold WCT9.famOrdinal at e1 h2 hoj ⊢
      simp only at e1 hoj
      omega
    rw [hhdr, PrefixGame.restTable_private, PrefixGame.restTable_private]
    show WCT9.seedHalf ((ovPrivL L R.1 y.1 (.inl (cellHdr L ⟨j, hj⟩))).extractLsb' 0 128,
      (ovPrivL L R.1 y.1 (.inl (cellHdr L ⟨j, hj⟩))).extractLsb' 128 128) o = _
    rw [ovPrivL_inl]
    unfold WCT9.seedHalf
    split_ifs with h0
    · rw [h0] at hnone
      rw [hnone, ChainGraph.joinOutput_low]
      rfl
    · rw [show o % 2 = 1 by omega] at hnone
      rw [hnone, ChainGraph.joinOutput_high]
      rfl
theorem restDepth_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (a : ChainAddr) (ha : a.key = L)
    (R : RefTables adversary) (y : LeafData L) : restDepth a (ovL L R y) = restDepth a R := by
  rw [restDepth_eq, restDepth_eq]
  exact depth_lay (leafAgree_ovL hL R y) hL (by rw [ha])

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
      if ∃ step v, step < d ∧ input = chainRow a step v then
        ChainGraph.joinOutput e (high (restTable R (.inl (.inr input))))
      else restTable R (.inl (.inr input)) := by
  cases hp : PrefixGame.rowOf a d input with
  | some p =>
      have hin := PrefixGame.rowOf_some hp
      rw [if_pos ⟨p.1, p.2, p.1.isLt, hin⟩, hin, PrefixGame.restTable_ov_prefix a hd]
  | none =>
      rw [if_neg ((PrefixGame.rowOf_none_iff a input).mp hp), PrefixGame.restTable_ov_nonprefix a _ _ _ hp]

/-! ### The honest table of the prefix game with the leaf overridden -/

theorem eval_chain_zero (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 0 v) = v := rfl

section Fill
variable {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
include hLleaf haL hac hd1

theorem fill_pub (X : LeafData L) (e : Digest) (input : HashInput)
    (h : ∀ c : Fin (chainCount L.lay), c.val ≠ a.chain → ∀ v, input ≠ chainRow ⟨L, c⟩ 0 v) :
    PrefixGame.fillTable a (ovL L R X) e (.inl (.inr input)) =
      if ∃ step v, step < restDepth a R ∧ input = chainRow a step v then
        ChainGraph.joinOutput e (high (restTable R (.inl (.inr input))))
      else restTable R (.inl (.inr input)) := by
  have hdX := restDepth_ovL hLleaf a haL R X
  unfold PrefixGame.fillTable
  rw [restTable_ov_const a (by have := PrefixGame.restDepth_le a (ovL L R X); omega), hdX]
  split_ifs with hc
  · obtain ⟨step, v, hs, rfl⟩ := hc
    congr 1
    by_cases hz : step = 0
    · subst hz
      have hrow : chainRow a 0 v = chainRow ⟨L, (⟨a.chain, hac⟩ : Fin (chainCount L.lay))⟩ 0 v := by
        subst haL; rfl
      rw [hrow, restTable_ovL_zero, high, ChainGraph.joinOutput_high]
    · rw [restTable_ovL_pub]
      cases hzo : zeroOf L (chainRow a step v) with
      | none => rfl
      | some q =>
          have he := zeroOf_some hzo
          obtain ⟨-, -, hs', -⟩ := chainInput_eq_chainRow (a := ⟨L, q.1⟩)
            (by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega)
            (by have := chainCount_le L.lay; have := q.1.isLt; simp only [Nat.reducePow]; omega)
            (by have := PrefixGame.restDepth_le a R; omega) (by omega) he
          exact absurd hs' hz
  · apply restTable_ovL_pub
    cases hzo : zeroOf L input with
    | none => rfl
    | some q =>
        have he := zeroOf_some hzo
        by_cases hqa : q.1.val = a.chain
        · exfalso
          apply hc
          refine ⟨0, q.2, hd1, ?_⟩
          rw [he]
          subst haL
          rw [hqa]
        · exact absurd he (h q.1 hqa q.2)

theorem fill_pub_indep (X X' : LeafData L) (e : Digest) (input : HashInput)
    (h : ∀ c : Fin (chainCount L.lay), c.val ≠ a.chain → ∀ v, input ≠ chainRow ⟨L, c⟩ 0 v) :
    PrefixGame.fillTable a (ovL L R X) e (.inl (.inr input)) =
      PrefixGame.fillTable a (ovL L R X') e (.inl (.inr input)) := by
  rw [fill_pub hLleaf haL hac R hd1 X e input h, fill_pub hLleaf haL hac R hd1 X' e input h]

theorem fill_priv (X : LeafData L) (e : Digest) (coord : Coordinate) :
    PrefixGame.fillTable a (ovL L R X) e (.inr coord) = restTable (ovL L R X) (.inr coord) := by
  unfold PrefixGame.fillTable
  exact PrefixGame.restTable_ov_private a _ _ _

theorem fill_zero (X : LeafData L) (e : Digest) (c : Fin (chainCount L.lay)) (hca : c.val ≠ a.chain) (v : Digest) :
    PrefixGame.fillTable a (ovL L R X) e (.inl (.inr (chainRow ⟨L, c⟩ 0 v))) =
      ChainGraph.joinOutput (X.2 c v) (high (restTable R (.inl (.inr (chainRow ⟨L, c⟩ 0 v))))) := by
  have hdX := restDepth_ovL hLleaf a haL R X
  unfold PrefixGame.fillTable
  rw [PrefixGame.restTable_ov_nonprefix, restTable_ovL_zero]
  rw [PrefixGame.rowOf_none_iff]
  rintro ⟨step, value, hs, he⟩
  have h1 : (c : Nat) < 2 ^ 24 := by have := chainCount_le L.lay; have := c.isLt; simp only [Nat.reducePow]; omega
  obtain ⟨-, hc, -, -⟩ := chainInput_eq_chainRow (a := a) h1
    (by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega) (by omega)
    (by have := PrefixGame.restDepth_le a (ovL L R X); omega) he
  exact hca hc

theorem leafAgree_fill (X : LeafData L) (e : Digest) :
    LeafAgree L (restTable R) (PrefixGame.fillTable a (ovL L R X) e) := by
  have hA := leafAgree_ovL hLleaf R X
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (n | input) | coord
    · rfl
    · rw [fill_pub hLleaf haL hac R hd1 X e input (fun c _ v he => hq c 0 v c.isLt (by omega) he), if_neg]
      rintro ⟨step, v, hs, rfl⟩
      apply hq a.chain step v hac (by have := PrefixGame.restDepth_le a R; omega)
      subst haL; rfl
    · rw [fill_priv hLleaf haL hac R hd1]
      exact hA.out _ hq
  · rw [eval_lowerSeedPair, eval_lowerSeedPair] at *
    have := hA.half o ho hno
    rw [eval_lowerSeedPair, eval_lowerSeedPair] at this
    rw [fill_priv hLleaf haL hac R hd1]
    exact this
theorem depth_fill (X : LeafData L) (e : Digest) (b : ChainAddr) (hb : b.key = L) :
    depth (PrefixGame.fillTable a (ovL L R X) e) b = depth (restTable R) b :=
  depth_lay (leafAgree_fill hLleaf haL hac R hd1 X e) hLleaf (by rw [hb])

theorem wotsSeed_fill (K : Fin (WCT9.famCount L.lay) → Digest) (f : Fin (chainCount L.lay) → Digest → Digest) (e : Digest) (c : Nat) :
    WCT9.wotsSeed (PrefixGame.fillTable a (ovL L R (K, f)) e) L.lay L.tree L.leaf c = seedOf K c := by
  rw [show seedOf K c = ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c) from rfl,
    ← wotsSeed_ovL hLleaf R K f c]
  apply Mask.wotsSeed_congr_cells
  intro p
  exact fill_priv hLleaf haL hac R hd1 (K, f) e _

theorem fill_frontier_self (X : LeafData L) (e : Digest) :
    frontierValue (PrefixGame.fillTable a (ovL L R X) e) a = e := by
  have hdX := restDepth_ovL hLleaf a haL R X
  unfold PrefixGame.fillTable
  rw [PrefixGame.frontierValue_ov]
  obtain ⟨d', hd'⟩ : ∃ d', restDepth a (ovL L R X) = d' + 1 := ⟨restDepth a (ovL L R X) - 1, by omega⟩
  generalize PrefixGame.ovSeed a (ovL L R X) e = s0
  revert s0
  rw [hd']
  intro s0
  exact PrefixGame.evaluate_const_succ d' e s0

/-- **Programmed leaf congruence.** With the step-0 rows of `L`'s chains programmed at the family seeds
(`progF`), the honest tables for two coefficient vectors agreeing on the revealed (depth-0) chains are leaf
congruent. -/
theorem leafCongr_prog (g : Fin (chainCount L.lay) → Digest → Digest) (Lab : Fin (chainCount L.lay) → Digest)
    (K K' : Fin (WCT9.famCount L.lay) → Digest)
    (hKK : ∀ c : Fin (chainCount L.lay), depth (restTable R) ⟨L, c⟩ = 0 → seedOf K c = seedOf K' c) (e : Digest) :
    LeafCongr L (PrefixGame.fillTable a (ovL L R (K, progF g Lab K)) e)
      (PrefixGame.fillTable a (ovL L R (K', progF g Lab K')) e) := by
  set T := PrefixGame.fillTable a (ovL L R (K, progF g Lab K)) e with hT
  set T' := PrefixGame.fillTable a (ovL L R (K', progF g Lab K')) e with hT'
  have hA := leafAgree_fill hLleaf haL hac R hd1 (K, progF g Lab K) e
  have hA' := leafAgree_fill hLleaf haL hac R hd1 (K', progF g Lab K') e
  have hda : depth (restTable R) a = restDepth a R := (restDepth_eq a R).symm
  have hnz : ∀ (c : Nat) (s : Nat) (v : Digest), s ≠ 0 → s < 256 →
      ∀ c' : Fin (chainCount L.lay), c'.val ≠ a.chain → ∀ v', chainRow ⟨L, c⟩ s v ≠ chainRow ⟨L, c'⟩ 0 v' := by
    intro c s v hs hs256 c' _ v' he
    obtain ⟨-, hv⟩ := chainInput_fields he
    have := (chainHeader_fields (chainInput_fields he).1).2.2.2.2
    omega
  refine ⟨⟨fun q hq => (hA'.out q hq).trans (hA.out q hq).symm, fun o ho hno =>
    (hA'.half o ho hno).trans (hA.half o ho hno).symm⟩, ?_, ?_⟩
  · intro c hc s v hs hs256
    rw [depth_fill hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl] at hs
    by_cases hs0 : s = 0
    · subst hs0
      have hca : c ≠ a.chain := by
        intro hca
        have : depth (restTable R) ⟨L, c⟩ = restDepth a R := by
          rw [← hda]; subst haL; rw [hca]
        omega
      have hrev := hKK ⟨c, hc⟩ (by show depth (restTable R) ⟨L, c⟩ = 0; omega)
      rw [hT, hT', fill_zero hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca,
        fill_zero hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca]
      simp only [progF]
      rw [hrev]
    · exact fill_pub_indep hLleaf haL hac R hd1 _ _ e _ (hnz c s v hs0 hs256)
  · intro c hc
    by_cases hca : c = a.chain
    · have hb : (⟨L, c⟩ : ChainAddr) = a := by subst haL; rw [hca]
      rw [hb, fill_frontier_self hLleaf haL hac R hd1, fill_frontier_self hLleaf haL hac R hd1]
    · unfold frontierValue honestChainValue
      simp only
      rw [depth_fill hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl, depth_fill hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl,
        wotsSeed_fill hLleaf haL hac R hd1, wotsSeed_fill hLleaf haL hac R hd1]
      rcases Nat.eq_zero_or_pos (depth (restTable R) ⟨L, c⟩) with h0 | hpos
      · rw [h0, hKK ⟨c, hc⟩ h0, eval_chain_zero, eval_chain_zero]
      · obtain ⟨k, hk⟩ : ∃ k, depth (restTable R) ⟨L, c⟩ = 1 + k := ⟨depth (restTable R) ⟨L, c⟩ - 1, by omega⟩
        rw [hk, Correctness.eval_chain_add, Correctness.eval_chain_add T]
        have hlab : ∀ (X : Fin (WCT9.famCount L.lay) → Digest), evalWithAnswerFn (PrefixGame.fillTable a (ovL L R (X, progF g Lab X)) e)
            (chain L.lay L.tree L.leaf c 0 1 (seedOf X c)) = Lab ⟨c, hc⟩ := by
          intro X
          rw [eval_chain_one]
          rw [show chainInput L.lay L.tree L.leaf c 0 (seedOf X c) =
            chainRow ⟨L, (⟨c, hc⟩ : Fin (chainCount L.lay))⟩ 0 (seedOf X c)
            from rfl, fill_zero hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca, ChainGraph.joinOutput_low]
          simp only [progF, Function.update_self]
        rw [hlab K', hlab K]
        have hk256 : 0 + 1 + k ≤ 256 := by
          have := Mask.depth_le_seven (restTable R) ⟨L, c⟩; omega
        refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
        unfold chain
        refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
        rw [pad64_chainInput]
        obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hstep
        exact (fill_pub_indep hLleaf haL hac R hd1 _ _ e _ (hnz c step value (by omega) (by omega))).symm
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
/-- `pub` with the low halves of `L`'s step-0 rows replaced by `f`. -/
noncomputable def ovPubL (L : LeafAddr) (pub : U → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) : U → HashOutput := fun x =>
  match zeroOf L x.val with
  | some p => ChainGraph.joinOutput (f p.1 p.2) (high (pub x))
  | none => pub x

/-- Leaf data: the 17 coefficients and the step-0 row functions of the chains. -/
noncomputable def ovL (L : LeafAddr) (R : Tables U) (y : LeafData L) : Tables U :=
  (ovPrivL L R.1 y.1, ovPubL L R.2 y.2)
noncomputable def rdL (L : LeafAddr) (R : Tables U) : LeafData L :=
  (fun j => halfOf (ordL L j % 2) (R.1 (.inl (cellHdr L j))),
    fun c v => low (R.2 ⟨chainRow ⟨L, c⟩ 0 v, RawPrefix.chainRow_mem hU _ _ _⟩))

theorem ovPubL_zero (L : LeafAddr) (pub : U → HashOutput)
    (f : Fin (chainCount L.lay) → Digest → Digest) (c : Fin (chainCount L.lay)) (v : Digest) :
    ovPubL L pub f ⟨chainRow ⟨L, c⟩ 0 v, RawPrefix.chainRow_mem hU _ _ _⟩ =
      ChainGraph.joinOutput (f c v) (high (pub ⟨chainRow ⟨L, c⟩ 0 v, RawPrefix.chainRow_mem hU _ _ _⟩)) := by
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
    rw [ovPubL_zero hU, low, ChainGraph.joinOutput_low]

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
        have hx : x = ⟨chainRow ⟨L, p.1⟩ 0 p.2, RawPrefix.chainRow_mem hU _ _ _⟩ := Subtype.ext (zeroOf_some hp)
        subst hx
        simp only [high, low, ChainGraph.joinOutput_high, ChainGraph.joinOutput_parts]

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
    (v : Digest) : raw (ovL L R y) (.inl (.inr (chainRow ⟨L, c⟩ 0 v))) =
      ChainGraph.joinOutput (y.2 c v) (high (raw R (.inl (.inr (chainRow ⟨L, c⟩ 0 v))))) := by
  rw [RawPrefix.raw_mem _ _ (RawPrefix.chainRow_mem hU _ _ _),
    RawPrefix.raw_mem _ _ (RawPrefix.chainRow_mem hU _ _ _)]
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
theorem famCoef_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U)
    (K : Fin (WCT9.famCount L.lay) → Digest) (f : Fin (chainCount L.lay) → Digest → Digest)
    (j : Fin (WCT9.famCount L.lay)) :
    WCT9.famCoef (raw (ovL L R (K, f))) L.lay L.tree L.leaf j = K j := by
  unfold WCT9.famCoef WCT9.famCoefN
  rw [eval_lowerSeedPair]
  have hc := ovPrivL_cell hL R.1 K j
  rw [show ovPrivL L R.1 K (.inl (cellHdr L j)) = raw (ovL L R (K, f)) (.inr (.inl (cellHdr L j))) from rfl]
    at hc
  unfold halfOf at hc
  unfold WCT9.seedHalf
  unfold cellHdr ordL at hc
  split_ifs with h1 h2 h2
  · rw [if_pos h1] at hc; exact hc
  · rw [if_neg h1] at hc; exact hc
theorem wotsSeed_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U)
    (K : Fin (WCT9.famCount L.lay) → Digest) (f : Fin (chainCount L.lay) → Digest → Digest) (c : Nat) :
    WCT9.wotsSeed (raw (ovL L R (K, f))) L.lay L.tree L.leaf c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c) := by
  rw [WCT9.wotsSeed_fam]
  congr 2
  funext j
  exact famCoef_ovL hL R K f j
/-- The leaf override changes nothing outside `L`'s own halves and step-0 rows. -/
theorem leafAgree_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L) :
    LeafAgree L (raw R) (raw (ovL L R y)) := by
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (n | input) | (tw | x)
    · rfl
    · apply raw_ovL_pub
      cases hz : zeroOf L input with
      | none => rfl
      | some p => exact absurd (zeroOf_some hz) (hq p.1 0 p.2 p.1.isLt (by omega))
    · exact raw_ovL_tweak L R y tw (fun j he => hq j j.isLt he.symm)
    · rfl
  · obtain ⟨j, hj, hoj⟩ := ho
    rw [eval_lowerSeedPair, eval_lowerSeedPair]
    have hhdr : WCT9.lowerSeedHeader L.lay L.tree (o / 2) = cellHdr L ⟨j, hj⟩ := by
      unfold cellHdr ordL; rw [hoj]
    have hnone : slotAt L (cellHdr L ⟨j, hj⟩) (o % 2) = none := by
      apply slotAt_none
      intro j' h1 h2
      have e1 := cellHdr_inj hL h1
      apply hno j' j'.isLt
      unfold ordL at e1 h2
      unfold WCT9.famOrdinal at e1 h2 hoj ⊢
      simp only at e1 hoj
      omega
    rw [hhdr, RawPrefix.raw_private, RawPrefix.raw_private]
    show WCT9.seedHalf ((ovPrivL L R.1 y.1 (.inl (cellHdr L ⟨j, hj⟩))).extractLsb' 0 128,
      (ovPrivL L R.1 y.1 (.inl (cellHdr L ⟨j, hj⟩))).extractLsb' 128 128) o = _
    rw [ovPrivL_inl]
    unfold WCT9.seedHalf
    split_ifs with h0
    · rw [h0] at hnone
      rw [hnone, ChainGraph.joinOutput_low]
      rfl
    · rw [show o % 2 = 1 by omega] at hnone
      rw [hnone, ChainGraph.joinOutput_high]
      rfl

theorem search_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L)
    (K : LeafAddr) (remaining : Nat) :
    CanonicalRef.searchOf (raw (ovL L R y)) zeroMessages K remaining =
    CanonicalRef.searchOf (raw R) zeroMessages K remaining := by
  unfold CanonicalRef.searchOf
  exact Leaf.eval_out (leafAgree_ovL hL R y)
    (Leaf.respects_leafOut (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) L)

theorem referenceSearch_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L) (K : LeafAddr) :
    CanonicalRef.referenceSearch (raw (ovL L R y)) zeroMessages K =
    CanonicalRef.referenceSearch (raw R) zeroMessages K :=
  CanonicalRef.referenceSearch_congr (fun K remaining _ => search_ovL hL R y K remaining) K

theorem depth_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L) (a : ChainAddr) :
    CanonicalRef.depth (raw (ovL L R y)) zeroMessages a = CanonicalRef.depth (raw R) zeroMessages a := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_ovL hL]

theorem restDepth_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : Tables U) (y : LeafData L) (a : ChainAddr) :
    RawPrefix.restDepth a (ovL L R y) = RawPrefix.restDepth a R := by
  rw [RawPrefix.restDepth_eq, RawPrefix.restDepth_eq, depth_ovL hL]
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
      if ∃ step v, step < d ∧ input = chainRow a step v then
        ChainGraph.joinOutput e (high (raw R (.inl (.inr input))))
      else raw R (.inl (.inr input)) := by
  cases hp : PrefixGame.rowOf a d input with
  | some p =>
      have hin := PrefixGame.rowOf_some hp
      rw [if_pos ⟨p.1, p.2, p.1.isLt, hin⟩, hin, RawPrefix.raw_ov_prefix hU a hd]
  | none =>
      rw [if_neg ((PrefixGame.rowOf_none_iff a input).mp hp), RawPrefix.raw_ov_nonprefix a _ _ _ hp]

/-! ### The honest table of the prefix game with the leaf overridden -/

theorem eval_chain_zero (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 0 v) = v := rfl

section Fill
variable {L : LeafAddr} (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : Tables U) (hd1 : 1 ≤ RawPrefix.restDepth a R)
include hLleaf haL hac hd1

theorem fill_pub (X : LeafData L) (e : Digest) (input : HashInput)
    (h : ∀ c : Fin (chainCount L.lay), c.val ≠ a.chain → ∀ v, input ≠ chainRow ⟨L, c⟩ 0 v) :
    fillTable a (ovL L R X) e (.inl (.inr input)) =
      if ∃ step v, step < RawPrefix.restDepth a R ∧ input = chainRow a step v then
        ChainGraph.joinOutput e (high (raw R (.inl (.inr input))))
      else raw R (.inl (.inr input)) := by
  have hdX := restDepth_ovL hLleaf R X a
  unfold fillTable RawPrefix.fill
  rw [raw_ov_const hU a (by have := RawPrefix.restDepth_le a (ovL L R X); omega), hdX]
  split_ifs with hc
  · obtain ⟨step, v, hs, rfl⟩ := hc
    congr 1
    by_cases hz : step = 0
    · subst hz
      have hrow : chainRow a 0 v = chainRow ⟨L, (⟨a.chain, hac⟩ : Fin (chainCount L.lay))⟩ 0 v := by
        subst haL; rfl
      rw [hrow, raw_ovL_zero hU, high, ChainGraph.joinOutput_high]
    · rw [raw_ovL_pub]
      cases hzo : zeroOf L (chainRow a step v) with
      | none => rfl
      | some q =>
          have he := zeroOf_some hzo
          obtain ⟨-, -, hs', -⟩ := chainInput_eq_chainRow (a := ⟨L, q.1⟩)
            (by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega)
            (by have := chainCount_le L.lay; have := q.1.isLt; simp only [Nat.reducePow]; omega)
            (by have := RawPrefix.restDepth_le a R; omega) (by omega) he
          exact absurd hs' hz
  · apply raw_ovL_pub
    cases hzo : zeroOf L input with
    | none => rfl
    | some q =>
        have he := zeroOf_some hzo
        by_cases hqa : q.1.val = a.chain
        · exfalso
          apply hc
          refine ⟨0, q.2, hd1, ?_⟩
          rw [he]
          subst haL
          rw [hqa]
        · exact absurd he (h q.1 hqa q.2)

theorem fill_pub_indep (X X' : LeafData L) (e : Digest) (input : HashInput)
    (h : ∀ c : Fin (chainCount L.lay), c.val ≠ a.chain → ∀ v, input ≠ chainRow ⟨L, c⟩ 0 v) :
    fillTable a (ovL L R X) e (.inl (.inr input)) =
      fillTable a (ovL L R X') e (.inl (.inr input)) := by
  rw [fill_pub hU hLleaf haL hac R hd1 X e input h, fill_pub hU hLleaf haL hac R hd1 X' e input h]

theorem fill_priv (X : LeafData L) (e : Digest) (coord : Coordinate) :
    fillTable a (ovL L R X) e (.inr coord) = raw (ovL L R X) (.inr coord) := by
  unfold fillTable RawPrefix.fill
  exact RawPrefix.raw_ov_private a _ _ _

theorem fill_zero (X : LeafData L) (e : Digest) (c : Fin (chainCount L.lay)) (hca : c.val ≠ a.chain) (v : Digest) :
    fillTable a (ovL L R X) e (.inl (.inr (chainRow ⟨L, c⟩ 0 v))) =
      ChainGraph.joinOutput (X.2 c v) (high (raw R (.inl (.inr (chainRow ⟨L, c⟩ 0 v))))) := by
  have hdX := restDepth_ovL hLleaf R X a
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.raw_ov_nonprefix, raw_ovL_zero hU]
  rw [PrefixGame.rowOf_none_iff]
  rintro ⟨step, value, hs, he⟩
  have h1 : (c : Nat) < 2 ^ 24 := by have := chainCount_le L.lay; have := c.isLt; simp only [Nat.reducePow]; omega
  obtain ⟨-, hc, -, -⟩ := chainInput_eq_chainRow (a := a) h1
    (by have := chainCount_le L.lay; simp only [Nat.reducePow]; omega) (by omega)
    (by have := RawPrefix.restDepth_le a (ovL L R X); omega) he
  exact hca hc

theorem leafAgree_fill (X : LeafData L) (e : Digest) :
    LeafAgree L (raw R) (fillTable a (ovL L R X) e) := by
  have hA := leafAgree_ovL hLleaf R X
  refine ⟨fun q hq => ?_, fun o ho hno => ?_⟩
  · rcases q with (n | input) | coord
    · rfl
    · rw [fill_pub hU hLleaf haL hac R hd1 X e input (fun c _ v he => hq c 0 v c.isLt (by omega) he), if_neg]
      rintro ⟨step, v, hs, rfl⟩
      apply hq a.chain step v hac (by have := RawPrefix.restDepth_le a R; omega)
      subst haL; rfl
    · rw [fill_priv hU hLleaf haL hac R hd1]
      exact hA.out _ hq
  · rw [eval_lowerSeedPair, eval_lowerSeedPair] at *
    have := hA.half o ho hno
    rw [eval_lowerSeedPair, eval_lowerSeedPair] at this
    rw [fill_priv hU hLleaf haL hac R hd1]
    exact this
theorem depth_fill (X : LeafData L) (e : Digest) (b : ChainAddr) (hb : b.key = L) :
    CanonicalRef.depth (fillTable a (ovL L R X) e) zeroMessages b = CanonicalRef.depth (raw R) zeroMessages b := by
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.depth_ov _ (by have := RawPrefix.restDepth_le a (ovL L R X);omega),depth_ovL hLleaf]

theorem wotsSeed_fill (K : Fin (WCT9.famCount L.lay) → Digest) (f : Fin (chainCount L.lay) → Digest → Digest) (e : Digest) (c : Nat) :
    WCT9.wotsSeed (fillTable a (ovL L R (K, f)) e) L.lay L.tree L.leaf c = seedOf K c := by
  rw [show seedOf K c = ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c) from rfl,
    ← wotsSeed_ovL hLleaf R K f c]
  apply Mask.wotsSeed_congr_cells
  intro p
  exact fill_priv hU hLleaf haL hac R hd1 (K, f) e _

theorem fill_frontier_self (X : LeafData L) (e : Digest) :
    CanonicalRef.frontierValue (fillTable a (ovL L R X) e) zeroMessages a = e := by
  have hdX := restDepth_ovL hLleaf R X a
  unfold fillTable RawPrefix.fill
  rw [RawPrefix.frontierValue_ov hU]
  obtain ⟨d', hd'⟩ : ∃ d', RawPrefix.restDepth a (ovL L R X) = d' + 1 := ⟨RawPrefix.restDepth a (ovL L R X) - 1, by omega⟩
  generalize RawPrefix.ovSeed a (ovL L R X) e = s0
  revert s0
  rw [hd']
  intro s0
  exact PrefixGame.evaluate_const_succ d' e s0


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

theorem sourceMessages_congr {messages : LeafAddr → WCT9.LayerMsg} {L : LeafAddr} {T T' : Answers}
    (hC : Congr messages L T T') (hL : L.leaf<2^24) :
    CanonicalRef.sourceMessages T'=CanonicalRef.sourceMessages T := by
  funext K
  unfold CanonicalRef.sourceMessages
  split
  · unfold Extract.honestPair
    rw [wotsTree_congr hC hL]
  · rw [forestCommitment_out hC.toLeafAgree]
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
/-- **Programmed leaf congruence.** With the step-0 rows of `L`'s chains programmed at the family seeds
(`progF`), the honest tables for two coefficient vectors agreeing on the revealed (depth-0) chains are leaf
congruent. -/
theorem leafCongr_prog (g : Fin (chainCount L.lay) → Digest → Digest) (Lab : Fin (chainCount L.lay) → Digest)
    (K K' : Fin (WCT9.famCount L.lay) → Digest)
    (hKK : ∀ c : Fin (chainCount L.lay), CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 0 → seedOf K c = seedOf K' c) (e : Digest) :
    CanonicalRef.Leaf.Congr zeroMessages L (fillTable a (ovL L R (K, progF g Lab K)) e)
      (fillTable a (ovL L R (K', progF g Lab K')) e) := by
  set T := fillTable a (ovL L R (K, progF g Lab K)) e with hT
  set T' := fillTable a (ovL L R (K', progF g Lab K')) e with hT'
  have hA := leafAgree_fill hU hLleaf haL hac R hd1 (K, progF g Lab K) e
  have hA' := leafAgree_fill hU hLleaf haL hac R hd1 (K', progF g Lab K') e
  have hda : CanonicalRef.depth (raw R) zeroMessages a = RawPrefix.restDepth a R := (RawPrefix.restDepth_eq a R).symm
  have hnz : ∀ (c : Nat) (s : Nat) (v : Digest), s ≠ 0 → s < 256 →
      ∀ c' : Fin (chainCount L.lay), c'.val ≠ a.chain → ∀ v', chainRow ⟨L, c⟩ s v ≠ chainRow ⟨L, c'⟩ 0 v' := by
    intro c s v hs hs256 c' _ v' he
    obtain ⟨-, hv⟩ := chainInput_fields he
    have := (chainHeader_fields (chainInput_fields he).1).2.2.2.2
    omega
  refine ⟨⟨fun q hq => (hA'.out q hq).trans (hA.out q hq).symm, fun o ho hno =>
    (hA'.half o ho hno).trans (hA.half o ho hno).symm⟩, ?_, ?_⟩
  · intro c hc s v hs hs256
    rw [depth_fill hU hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl] at hs
    by_cases hs0 : s = 0
    · subst hs0
      have hca : c ≠ a.chain := by
        intro hca
        have : CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = RawPrefix.restDepth a R := by
          rw [← hda]; subst haL; rw [hca]
        omega
      have hrev := hKK ⟨c, hc⟩ (by show CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 0; omega)
      rw [hT, hT', fill_zero hU hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca,
        fill_zero hU hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca]
      simp only [progF]
      rw [hrev]
    · exact fill_pub_indep hU hLleaf haL hac R hd1 _ _ e _ (hnz c s v hs0 hs256)
  · intro c hc
    by_cases hca : c = a.chain
    · have hb : (⟨L, c⟩ : ChainAddr) = a := by subst haL; rw [hca]
      rw [hb, fill_frontier_self hU hLleaf haL hac R hd1, fill_frontier_self hU hLleaf haL hac R hd1]
    · unfold CanonicalRef.frontierValue honestChainValue
      simp only
      rw [depth_fill hU hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl, depth_fill hU hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl,
        wotsSeed_fill hU hLleaf haL hac R hd1, wotsSeed_fill hU hLleaf haL hac R hd1]
      rcases Nat.eq_zero_or_pos (CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩) with h0 | hpos
      · rw [h0, hKK ⟨c, hc⟩ h0, Leaf.eval_chain_zero, Leaf.eval_chain_zero]
      · obtain ⟨k, hk⟩ : ∃ k, CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ = 1 + k := ⟨CanonicalRef.depth (raw R) zeroMessages ⟨L, c⟩ - 1, by omega⟩
        rw [hk, Correctness.eval_chain_add, Correctness.eval_chain_add T]
        have hlab : ∀ (X : Fin (WCT9.famCount L.lay) → Digest), evalWithAnswerFn (fillTable a (ovL L R (X, progF g Lab X)) e)
            (chain L.lay L.tree L.leaf c 0 1 (seedOf X c)) = Lab ⟨c, hc⟩ := by
          intro X
          rw [eval_chain_one]
          rw [show chainInput L.lay L.tree L.leaf c 0 (seedOf X c) =
            chainRow ⟨L, (⟨c, hc⟩ : Fin (chainCount L.lay))⟩ 0 (seedOf X c)
            from rfl, fill_zero hU hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca, ChainGraph.joinOutput_low]
          simp only [progF, Function.update_self]
        rw [hlab K', hlab K]
        have hk256 : 0 + 1 + k ≤ 256 := by
          have := CanonicalRef.Mask.depth_le_seven (raw R) zeroMessages ⟨L, c⟩; omega
        refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
        unfold chain
        refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
        rw [pad64_chainInput]
        obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hstep
        exact (fill_pub_indep hU hLleaf haL hac R hd1 _ _ e _ (hnz c step value (by omega) (by omega))).symm
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
include hLleaf in
theorem eval_signTop_leaf (cache : Cache) (leaf : Nat) (hleaf : leaf < 2 ^ 24) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits)
    (halias : LeafAlias 0 0 leaf L → ∀ i, i < chainCount L.lay → CanonicalRef.depth T messages ⟨L, i⟩ ≤ digits.getD i 0) :
    evalWithAnswerFn T' (signTop cache leaf digits) = evalWithAnswerFn T (signTop cache leaf digits) := by
  have hv : (List.range (chainCount 0)).map (WCT9.wotsValue T' 0 0 leaf digits) =
      (List.range (chainCount 0)).map (WCT9.wotsValue T 0 0 leaf digits) := by
    apply List.map_congr_left
    intro i hi
    apply wotsValue_congr hC hLleaf hleaf digits i (List.mem_range.mp hi)
    · have := hvalid i (List.mem_range.mp hi)
      have := width_le 0 i
      omega
    · intro hal
      exact halias hal i (hal.1 ▸ List.mem_range.mp hi)
  rw [Mask.eval_signTop_wots T' cache leaf digits hvalid, Mask.eval_signTop_wots T cache leaf digits hvalid, hv,
    eval_out hC.toLeafAgree (respectsL_topPath L _ _)]

include hLleaf in
theorem wotsPieces_congr {lay : Layer} {tree leaf : Nat} (hleaf : leaf<2^24)
    (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (halias : LeafAlias lay tree leaf L → ∀i, i<chainCount L.lay → CanonicalRef.depth T messages ⟨L,i⟩≤digits.getD i 0) :
    wotsPieces T' lay tree leaf digits=wotsPieces T lay tree leaf digits := by
  unfold wotsPieces
  rw [wotsTree_congr hC hLleaf]
  congr 1
  apply List.map_congr_left
  intro i hi
  apply wotsValue_congr hC hLleaf hleaf digits i (List.mem_range.mp hi)
  · have := hvalid i (List.mem_range.mp hi);have := width_le lay i;omega
  · intro hal
    exact halias hal i (hal.1 ▸ List.mem_range.mp hi)

include hLleaf in
theorem fixedPrepared_pieces_congr (index : Nat) (hi : index<2^31) (lay : Layer) (hlay : lay≠0)
    {counter : BitVec 32} {digits : List Nat}
    (hsearch : CanonicalRef.referenceSearch T messages (sourceLeaf index lay)=some (counter,digits))
    (htree : L.tree<2^40) :
    preparedPieces lay (route index lay).1 (fixedPrepared T' index lay) digits=
      preparedPieces lay (route index lay).1 (fixedPrepared T index lay) digits := by
  have hv := CanonicalRef.Mask.source_digits_valid T messages lay hsearch rfl
  have hp (X : Answers) : preparedPieces lay (route index lay).1 (fixedPrepared X index lay) digits=
      wotsPieces X lay (route index lay).2 (route index lay).1 digits := by
    unfold fixedPrepared
    rw [←eval_buildTreePrefixes_result X hlay _ _ (route_leaf_bound index lay)]
    exact preparedPieces_result X hlay _ _ digits hv (route_leaf_bound index lay)
  rw [hp,hp]
  apply wotsPieces_congr hC hLleaf (by have := route_leaf_bound index lay;have := height_pow_le lay;omega) digits hv
  intro hal i _
  exact CanonicalRef.Mask.sourceLeaf_alias T messages ⟨L,i⟩ hi hsearch htree hLleaf hal
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
theorem searchPreparedLayers_leafEq {T T' : Answers} {L : LeafAddr}
    (hC : Congr (sourceMessages T) L T T') (htree : L.tree<2^40) (hleaf : L.leaf<2^24)
    (cache : SigGolfCandidate.T3.Cache) (index : Nat) (hi : index<2^31)
    (forest : PairRoot) (hforest : LayerMsg.pair forest.1 forest.2=sourceMessages T (sourceLeaf index 3)) :
    let prepared := (⟨fixedPrepared T index 1,fixedPrepared T index 2,fixedPrepared T index 3⟩ : PreparedRoots)
    let prepared' := (⟨fixedPrepared T' index 1,fixedPrepared T' index 2,fixedPrepared T' index 3⟩ : PreparedRoots)
    ExecEq T T' (searchPreparedLayers cache index prepared forest)
      (searchPreparedLayers cache index prepared' forest) := by
  let messages := sourceMessages T
  have hlevels (lay : Layer) : (fixedPrepared T' index lay).levels=(fixedPrepared T index lay).levels := by
    dsimp only [fixedPrepared]
    rw [wotsTree_congr hC hleaf]
  have hs (lay : Layer) (remaining : Nat)
      (_hc : referenceContext T messages (sourceLeaf index lay)=some remaining) :
      ExecEq T T' (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay))
        (WCT9.CanonicalPolicy.layerCounterSearchAt lay (CanonicalPolicy.threshold lay.val remaining)
        (sourceLeaf index lay).tree (sourceLeaf index lay).leaf (messages (sourceLeaf index lay)) 0 (searchLimit lay)) :=
    let h := respects_leafOut (fun a => CanonicalRef.Mask.respects_layerCounterSearchAt a _ _ _ _ _ _ _) L
    ⟨h.eval_eq hC.out,congrArg List.length (h.queried_eq hC.out)⟩
  have h0 : LayerMsg.pair (topPair 1 (fixedPrepared T index 1).levels).1
      (topPair 1 (fixedPrepared T index 1).levels).2=messages (sourceLeaf index 0) := by
    dsimp only [messages]
    rw [fixedPrepared_pair,sourceMessages_route_lower T index 0 (by decide)]; rfl
  have h1 : LayerMsg.pair (topPair 2 (fixedPrepared T index 2).levels).1
      (topPair 2 (fixedPrepared T index 2).levels).2=messages (sourceLeaf index 1) := by
    dsimp only [messages]
    rw [fixedPrepared_pair,sourceMessages_route_lower T index 1 (by decide)]; rfl
  have h2 : LayerMsg.pair (topPair 3 (fixedPrepared T index 3).levels).1
      (topPair 3 (fixedPrepared T index 3).levels).2=messages (sourceLeaf index 2) := by
    dsimp only [messages]
    rw [fixedPrepared_pair,sourceMessages_route_lower T index 2 (by decide)]; rfl
  have h3 : LayerMsg.pair forest.1 forest.2=messages (sourceLeaf index 3) := hforest
  have hc0 : referenceContext T messages (sourceLeaf index 0)=some 63 := rfl
  dsimp only
  unfold searchPreparedLayers
  dsimp only
  rw [hlevels 1,hlevels 2,hlevels 3,h0,h1,h2,h3]
  refine ExecEq.bind (hs 0 63 hc0) ?_
  intro found0 hr0
  cases found0 with
  | none => exact ExecEq.pure' _ _ _
  | some found0 =>
    rcases found0 with ⟨counter0,digits0⟩
    have href0 := referenceSearch_of_run hc0 hr0
    have hc1 : referenceContext T messages (sourceLeaf index 1)=
        some (CanonicalPolicy.nextResidual 63 0 digits0) := by
      apply context_parent_success (leaf:=sourceLeaf index 1) (by change 1 ≠ 0; decide)
      · rw [sourceLeaf_parent index 1 (by decide)]; exact hc0
      · rw [sourceLeaf_parent index 1 (by decide)]; exact href0
    dsimp only
    split
    · exact ExecEq.pure' _ _ _
    · refine ExecEq.bind (hs 1 _ hc1) ?_
      intro found1 hr1
      cases found1 with
      | none => exact ExecEq.pure' _ _ _
      | some found1 =>
        rcases found1 with ⟨counter1,digits1⟩
        have href1 := referenceSearch_of_run hc1 hr1
        have hc2 : referenceContext T messages (sourceLeaf index 2)=
            some (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 63 0 digits0) 1 digits1) := by
          apply context_parent_success (leaf:=sourceLeaf index 2) (by change 2 ≠ 0; decide)
          · rw [sourceLeaf_parent index 2 (by decide)]; exact hc1
          · rw [sourceLeaf_parent index 2 (by decide)]; exact href1
        dsimp only
        split
        · exact ExecEq.pure' _ _ _
        · refine ExecEq.bind (hs 2 _ hc2) ?_
          intro found2 hr2
          cases found2 with
          | none => exact ExecEq.pure' _ _ _
          | some found2 =>
            rcases found2 with ⟨counter2,digits2⟩
            have href2 := referenceSearch_of_run hc2 hr2
            have hc3 : referenceContext T messages (sourceLeaf index 3)=
                some (CanonicalPolicy.nextResidual
                  (CanonicalPolicy.nextResidual (CanonicalPolicy.nextResidual 63 0 digits0) 1 digits1) 2 digits2) := by
              apply context_parent_success (leaf:=sourceLeaf index 3) (by change 3 ≠ 0; decide)
              · rw [sourceLeaf_parent index 3 (by decide)]; exact hc2
              · rw [sourceLeaf_parent index 3 (by decide)]; exact href2
            dsimp only
            split
            · exact ExecEq.pure' _ _ _
            · refine ExecEq.bind (hs 3 _ hc3) ?_
              intro found3 hr3
              cases found3 with
              | none => exact ExecEq.pure' _ _ _
              | some found3 =>
                rcases found3 with ⟨counter3,digits3⟩
                have href3 := referenceSearch_of_run hc3 hr3
                have hv0 := CanonicalRef.Mask.source_digits_valid T messages 0 href0 rfl
                have ht : ExecEq T T' (signTop cache (route index 0).1 digits0)
                    (signTop cache (route index 0).1 digits0) := by
                  refine ⟨eval_signTop_leaf hC hleaf cache _ (by have := route_leaf_bound index (0:Layer);have := height_pow_le (0:Layer);omega) _ hv0 ?_,?_⟩
                  · intro hal i _
                    apply CanonicalRef.Mask.sourceLeaf_alias T messages ⟨L,i⟩ hi href0 htree hleaf
                    rw [route_top_tree index hi]
                    exact hal
                  · rw [SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop,
                      SigGolfCandidate.T3.Security.Wots.Mask.queried_length_signTop]
                refine ExecEq.bind ht ?_
                intro top _
                apply ExecEq.pure_eq
                rw [fixedPrepared_pieces_congr hC hleaf index hi 1 (by decide) href1 htree,
                  fixedPrepared_pieces_congr hC hleaf index hi 2 (by decide) href2 htree,
                  fixedPrepared_pieces_congr hC hleaf index hi 3 (by decide) href3 htree]

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
theorem signFromOutput_leafEq {T T' : Answers} {L : LeafAddr}
    (hC : Congr (sourceMessages T) L T T') (htree : L.tree<2^40) (hleaf : L.leaf<2^24)
    (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (counter : BitVec 32) (output : HashOutput) :
    ExecEq T T'
      (signFromOutput cache rho counter output) (signFromOutput cache rho counter output) := by
  unfold signFromOutput
  refine ExecEq.bind (buildForest_out hC.toLeafAgree _ _ _) ?_
  intro forest hforest
  refine ExecEq.bind_effect (Mask.queried_length_prepareRoots_congr _ _ _) ?_
  simp only [prepareRoots_result]
  refine ExecEq.bind (searchPreparedLayers_leafEq hC htree hleaf cache _ (digestIndex_lt output) forest.2 ?_) ?_
  · rw [←hforest,buildForest_commitment,sourceMessages_route_bottom T _ (digestIndex_lt output)]
  · intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem signPayload_leafEq {T T' : Answers} {L : LeafAddr}
    (hC : Congr (sourceMessages T) L T T') (htree : L.tree<2^40) (hleaf : L.leaf<2^24)
    (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    ExecEq T T'
      (SigGolfCandidate.Research.SharedForest.signPayload cache message)
      (SigGolfCandidate.Research.SharedForest.signPayload cache message) := by
  unfold SigGolfCandidate.Research.SharedForest.signPayload
  refine ExecEq.bind (execEq_out hC.toLeafAgree (respectsL_privateNonce L _)) ?_
  intro rho _
  refine ExecEq.bind (execEq_out hC.toLeafAgree (respects_leafOutP (fun a => CanonicalRef.respectsP_sharedDigestSearch a _ _ _ _) L)) ?_
  intro selected _
  cases selected with
  | none => exact ExecEq.pure' _ _ _
  | some selected =>
    rcases selected with ⟨counter,output⟩
    refine ExecEq.bind (signFromOutput_leafEq hC htree hleaf _ _ _ _) ?_
    intro result _
    cases result <;> exact ExecEq.pure' _ _ _

theorem authenticatedSign_leafEq {T T' : Answers} {L : LeafAddr}
    (hC : Congr (sourceMessages T) L T T') (htree : L.tree<2^40) (hleaf : L.leaf<2^24)
    (published : SigGolfCandidate.T3.Cache) (request : SigGolfCandidate.T3.Security.Request) :
    ExecEq T T'
      (PairedOuter.FullGame.authenticatedSign published request)
      (PairedOuter.FullGame.authenticatedSign published request) := by
  unfold PairedOuter.FullGame.authenticatedSign
  refine ExecEq.bind (execEq_out hC.toLeafAgree (respectsL_privateMac L _)) ?_
  intro tag _
  split
  · exact signPayload_leafEq hC htree hleaf _ _
  · exact ExecEq.pure' _ _ _

theorem keygen_leafEq {T T' : Answers} {L : LeafAddr}
    (hC : Congr (sourceMessages T) L T T') (hleaf : L.leaf<2^24) :
    ExecEq T T' SigGolfCandidate.T3.keygen SigGolfCandidate.T3.keygen := by
  have hp : ExecEq T T' keygenPayload keygenPayload := by
    refine ⟨?_,?_⟩
    · rw [Wots.Mask.eval_keygenPayload_wots,Wots.Mask.eval_keygenPayload_wots,wotsTree_congr hC hleaf]
      exact eval_out hC.toLeafAgree (respects_leafOut (fun c => Wots.Mask.respects_keygenRest c _) L)
    · exact queried_length_keygenPayload_congr _ _
  unfold SigGolfCandidate.T3.keygen
  refine ExecEq.bind hp ?_
  rintro ⟨pk,region⟩ _
  exact ExecEq.bind (execEq_out hC.toLeafAgree (respectsL_privateMac L _)) fun _ _ => ExecEq.pure' _ _ _

theorem referenceGame_leaf {T T' : Answers} {L : LeafAddr}
    (hC : Congr (sourceMessages T) L T T') (htree : L.tree<2^40) (hleaf : L.leaf<2^24)
    (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame T' adversary q=PairedReference.referenceGame T adversary q :=
  PairedReference.referenceGame_congr _ _ (keygen_leafEq hC hleaf).1 (keygen_leafEq hC hleaf).2
    (fun cache request => (authenticatedSign_leafEq hC htree hleaf cache request).1)
    (fun cache request => (authenticatedSign_leafEq hC htree hleaf cache request).2) adversary q

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

theorem leafCongr_normalize {L : LeafAddr} (hL : WotsExtract.SourceLeaf7 L) {R R' : Tables U}
    (hC : CanonicalRef.Leaf.Congr zeroMessages L (raw R) (raw R')) :
    CanonicalRef.Leaf.Congr (sourceMessages (answers hU R)) L (answers hU R) (answers hU R') := by
  have hl : L.leaf<2^24 := by
    have hh : ∀lay:Layer,2^height lay≤2^24 := by intro lay;fin_cases lay<;>decide
    exact hL.2.trans_le (hh L.lay)
  have hm := CanonicalRef.Leaf.sourceMessages_congr hC hl
  have hmn : sourceMessages (answers hU R')=sourceMessages (answers hU R) := by
    rw [messages,messages,hm]
  refine ⟨leafAgree_normalize hU hC.toLeafAgree hm,?_,?_⟩
  · intro c hc step value hs hstep
    rw [depth_eq hU R ⟨L,c⟩ hL] at hs
    rw [answers_chainRow,answers_chainRow]
    exact hC.rows c hc step value hs hstep
  · intro c hc
    rw [←hmn,frontier_eq hU R' ⟨L,c⟩ hL,hmn,frontier_eq hU R ⟨L,c⟩ hL]
    exact hC.front c hc
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

theorem referenceGame_programmed {L : LeafAddr} (hL : WotsExtract.SourceLeaf7 L)
    {a : ChainAddr} (ha : a.key=L) (hac : a.chain<chainCount L.lay) (R : Tables U)
    (hd : 1≤RawPrefix.restDepth a R)
    (g : Fin (chainCount L.lay) → Digest → Digest) (Lab : Fin (chainCount L.lay) → Digest)
    (K K' : Fin (WCT9.famCount L.lay) → Digest)
    (hKK : ∀c : Fin (chainCount L.lay), CanonicalRef.depth (raw R) zeroMessages ⟨L,c⟩=0 → seedOf K c=seedOf K' c)
    (e : Digest) (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) :
    PairedReference.referenceGame (answers hU (RawPrefix.fill a (ovL L R (K',progF g Lab K')) e)) adversary q=
      PairedReference.referenceGame (answers hU (RawPrefix.fill a (ovL L R (K,progF g Lab K)) e)) adversary q := by
  have hl : L.leaf<2^24 := by
    have hh : ∀lay:Layer,2^height lay≤2^24 := by intro lay;fin_cases lay<;>decide
    exact hL.2.trans_le (hh L.lay)
  have hC := leafCongr_prog hU hl ha hac R hd g Lab K K' hKK e
  exact CanonicalRef.Leaf.referenceGame_leaf (leafCongr_normalize hU hL hC)
    (hL.tree_lt.trans_le (by decide)) hl adversary q
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawLeaf
