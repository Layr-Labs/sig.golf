import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsLeafCongr
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGame

/-! # Leaf decomposition of the rest tables (campaign X1 stage B, step B3)

`ovL L R (K, f)` overrides lower leaf `L`'s 17 family coefficient halves by `K` and the low halves of the step-0
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
def ordL (L : LeafAddr) (j : Fin 17) : Nat := WCT9.lowerCoefOrdinal L.leaf j
/-- Tweak of the cell holding coefficient `j` of leaf `L`. -/
def cellHdr (L : LeafAddr) (j : Fin 17) : BitVec 128 := WCT9.lowerSeedHeader L.lay L.tree (ordL L j / 2)

theorem ordL_pair_lt {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (j : Fin 17) : ordL L j / 2 < 2 ^ 32 := by
  unfold ordL WCT9.lowerCoefOrdinal WCT9.lowerCoefCount; have := j.isLt; omega
theorem cellHdr_inj {L : LeafAddr} (hL : L.leaf < 2 ^ 24) {j j' : Fin 17} (h : cellHdr L j = cellHdr L j') :
    ordL L j / 2 = ordL L j' / 2 := by
  unfold cellHdr WCT9.lowerSeedHeader at h
  have := (header_fields h).2.2.2.1
  rwa [Nat.mod_eq_of_lt (ordL_pair_lt hL j), Nat.mod_eq_of_lt (ordL_pair_lt hL j')] at this
theorem ordL_inj {L : LeafAddr} {j j' : Fin 17} (h1 : ordL L j / 2 = ordL L j' / 2)
    (h2 : ordL L j % 2 = ordL L j' % 2) : j = j' := by
  apply Fin.ext; unfold ordL WCT9.lowerCoefOrdinal at h1 h2; omega

/-- The coefficient of `L` stored in half `b` (`0` low, `1` high) of the cell with tweak `tw`, if any. -/
noncomputable def slotAt (L : LeafAddr) (tw : BitVec 128) (b : Nat) : Option (Fin 17) :=
  if h : ∃ j : Fin 17, cellHdr L j = tw ∧ ordL L j % 2 = b then some (Classical.choose h) else none
theorem slotAt_some {L : LeafAddr} {tw : BitVec 128} {b : Nat} {j : Fin 17} (h : slotAt L tw b = some j) :
    cellHdr L j = tw ∧ ordL L j % 2 = b := by
  unfold slotAt at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem slotAt_self {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (j : Fin 17) :
    slotAt L (cellHdr L j) (ordL L j % 2) = some j := by
  have hex : ∃ j' : Fin 17, cellHdr L j' = cellHdr L j ∧ ordL L j' % 2 = ordL L j % 2 := ⟨j, rfl, rfl⟩
  unfold slotAt
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  rw [ordL_inj (cellHdr_inj hL h1) h2]
theorem slotAt_none {L : LeafAddr} {tw : BitVec 128} {b : Nat}
    (h : ∀ j : Fin 17, cellHdr L j = tw → ordL L j % 2 ≠ b) : slotAt L tw b = none := by
  unfold slotAt
  rw [dif_neg]
  rintro ⟨j, h1, h2⟩
  exact h j h1 h2

/-- Low (`b = 0`) or high half of an output. -/
def halfOf (b : Nat) (output : HashOutput) : Digest := if b = 0 then low output else high output

/-- `priv` with `L`'s coefficient halves replaced by `K`. -/
noncomputable def ovPrivL (L : LeafAddr) (priv : FullGame.FullTable) (K : Fin 17 → Digest) : FullGame.FullTable
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
abbrev LeafData (L : LeafAddr) := (Fin 17 → Digest) × (Fin (chainCount L.lay) → Digest → Digest)
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

theorem ovPrivL_inl (L : LeafAddr) (priv : FullGame.FullTable) (K : Fin 17 → Digest) (tw : BitVec 128) :
    ovPrivL L priv K (.inl tw) = ChainGraph.joinOutput (((slotAt L tw 0).map K).getD (low (priv (.inl tw))))
      (((slotAt L tw 1).map K).getD (high (priv (.inl tw)))) := rfl
theorem ovPrivL_inr (L : LeafAddr) (priv : FullGame.FullTable) (K : Fin 17 → Digest) (x : Message ⊕ Region) :
    ovPrivL L priv K (.inr x) = priv (.inr x) := rfl
theorem ovPrivL_cell {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (priv : FullGame.FullTable) (K : Fin 17 → Digest)
    (j : Fin 17) : halfOf (ordL L j % 2) (ovPrivL L priv K (.inl (cellHdr L j))) = K j := by
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
theorem lowerCoef_ovL {L : LeafAddr} (hL : L.leaf < 2 ^ 24) (R : RefTables adversary) (K : Fin 17 → Digest)
    (f : Fin (chainCount L.lay) → Digest → Digest) (j : Fin 17) :
    WCT9.lowerCoef (restTable (ovL L R (K, f))) L.lay L.tree L.leaf j = K j := by
  unfold WCT9.lowerCoef WCT9.lowerCoefN
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
theorem wotsSeed_ovL {L : LeafAddr} (hL0 : L.lay ≠ 0) (hL : L.leaf < 2 ^ 24) (R : RefTables adversary)
    (K : Fin 17 → Digest) (f : Fin (chainCount L.lay) → Digest → Digest) (c : Nat) :
    WCT9.wotsSeed (restTable (ovL L R (K, f))) L.lay L.tree L.leaf c =
      ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c) := by
  rw [WCT9.wotsSeed_lower _ hL0]
  unfold WCT9.lowerSeed
  congr 2
  funext j
  exact lowerCoef_ovL hL R K f j
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
      unfold WCT9.lowerCoefOrdinal at e1 h2 hoj ⊢
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
theorem restDepth_ovL {L : LeafAddr} (hL0 : L.lay ≠ 0) (hL : L.leaf < 2 ^ 24) (a : ChainAddr) (ha : a.key = L)
    (R : RefTables adversary) (y : LeafData L) : restDepth a (ovL L R y) = restDepth a R := by
  rw [restDepth_eq, restDepth_eq]
  exact depth_lay (leafAgree_ovL hL R y) hL0 hL (by rw [ha])

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
noncomputable def seedOf (K : Fin 17 → Digest) (c : Nat) : Digest :=
  ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c)
/-- Step-0 rows programmed at the family seeds. -/
noncomputable def progF {n : Nat} (g : Fin n → Digest → Digest) (Lab : Fin n → Digest) (K : Fin 17 → Digest) :
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
variable {L : LeafAddr} (hL0 : L.lay ≠ 0) (hLleaf : L.leaf < 2 ^ 24) {a : ChainAddr} (haL : a.key = L)
  (hac : a.chain < chainCount L.lay) (R : RefTables adversary) (hd1 : 1 ≤ restDepth a R)
include hL0 hLleaf haL hac hd1

theorem fill_pub (X : LeafData L) (e : Digest) (input : HashInput)
    (h : ∀ c : Fin (chainCount L.lay), c.val ≠ a.chain → ∀ v, input ≠ chainRow ⟨L, c⟩ 0 v) :
    PrefixGame.fillTable a (ovL L R X) e (.inl (.inr input)) =
      if ∃ step v, step < restDepth a R ∧ input = chainRow a step v then
        ChainGraph.joinOutput e (high (restTable R (.inl (.inr input))))
      else restTable R (.inl (.inr input)) := by
  have hdX := restDepth_ovL hL0 hLleaf a haL R X
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
  rw [fill_pub hL0 hLleaf haL hac R hd1 X e input h, fill_pub hL0 hLleaf haL hac R hd1 X' e input h]

theorem fill_priv (X : LeafData L) (e : Digest) (coord : Coordinate) :
    PrefixGame.fillTable a (ovL L R X) e (.inr coord) = restTable (ovL L R X) (.inr coord) := by
  unfold PrefixGame.fillTable
  exact PrefixGame.restTable_ov_private_lower a (by rw [haL]; exact hL0) _ _ _

theorem fill_zero (X : LeafData L) (e : Digest) (c : Fin (chainCount L.lay)) (hca : c.val ≠ a.chain) (v : Digest) :
    PrefixGame.fillTable a (ovL L R X) e (.inl (.inr (chainRow ⟨L, c⟩ 0 v))) =
      ChainGraph.joinOutput (X.2 c v) (high (restTable R (.inl (.inr (chainRow ⟨L, c⟩ 0 v))))) := by
  have hdX := restDepth_ovL hL0 hLleaf a haL R X
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
    · rw [fill_pub hL0 hLleaf haL hac R hd1 X e input (fun c _ v he => hq c 0 v c.isLt (by omega) he), if_neg]
      rintro ⟨step, v, hs, rfl⟩
      apply hq a.chain step v hac (by have := PrefixGame.restDepth_le a R; omega)
      subst haL; rfl
    · rw [fill_priv hL0 hLleaf haL hac R hd1]
      exact hA.out _ hq
  · rw [eval_lowerSeedPair, eval_lowerSeedPair] at *
    have := hA.half o ho hno
    rw [eval_lowerSeedPair, eval_lowerSeedPair] at this
    rw [fill_priv hL0 hLleaf haL hac R hd1]
    exact this
theorem depth_fill (X : LeafData L) (e : Digest) (b : ChainAddr) (hb : b.key = L) :
    depth (PrefixGame.fillTable a (ovL L R X) e) b = depth (restTable R) b :=
  depth_lay (leafAgree_fill hL0 hLleaf haL hac R hd1 X e) hL0 hLleaf (by rw [hb])

theorem wotsSeed_fill (K : Fin 17 → Digest) (f : Fin (chainCount L.lay) → Digest → Digest) (e : Digest) (c : Nat) :
    WCT9.wotsSeed (PrefixGame.fillTable a (ovL L R (K, f)) e) L.lay L.tree L.leaf c = seedOf K c := by
  rw [show seedOf K c = ClaudeWCT.Arith.familyEval (List.ofFn K) (WCT9.lowerPoint c) from rfl,
    ← wotsSeed_ovL hL0 hLleaf R K f c, WCT9.wotsSeed_lower _ hL0, WCT9.wotsSeed_lower _ hL0]
  apply lowerSeed_congr_cells
  intro p
  exact fill_priv hL0 hLleaf haL hac R hd1 (K, f) e _

theorem fill_frontier_self (X : LeafData L) (e : Digest) :
    frontierValue (PrefixGame.fillTable a (ovL L R X) e) a = e := by
  have hdX := restDepth_ovL hL0 hLleaf a haL R X
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
    (K K' : Fin 17 → Digest)
    (hKK : ∀ c : Fin (chainCount L.lay), depth (restTable R) ⟨L, c⟩ = 0 → seedOf K c = seedOf K' c) (e : Digest) :
    LeafCongr L (PrefixGame.fillTable a (ovL L R (K, progF g Lab K)) e)
      (PrefixGame.fillTable a (ovL L R (K', progF g Lab K')) e) := by
  set T := PrefixGame.fillTable a (ovL L R (K, progF g Lab K)) e with hT
  set T' := PrefixGame.fillTable a (ovL L R (K', progF g Lab K')) e with hT'
  have hA := leafAgree_fill hL0 hLleaf haL hac R hd1 (K, progF g Lab K) e
  have hA' := leafAgree_fill hL0 hLleaf haL hac R hd1 (K', progF g Lab K') e
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
    rw [depth_fill hL0 hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl] at hs
    by_cases hs0 : s = 0
    · subst hs0
      have hca : c ≠ a.chain := by
        intro hca
        have : depth (restTable R) ⟨L, c⟩ = restDepth a R := by
          rw [← hda]; subst haL; rw [hca]
        omega
      have hrev := hKK ⟨c, hc⟩ (by show depth (restTable R) ⟨L, c⟩ = 0; omega)
      rw [hT, hT', fill_zero hL0 hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca,
        fill_zero hL0 hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca]
      simp only [progF]
      rw [hrev]
    · exact fill_pub_indep hL0 hLleaf haL hac R hd1 _ _ e _ (hnz c s v hs0 hs256)
  · intro c hc
    by_cases hca : c = a.chain
    · have hb : (⟨L, c⟩ : ChainAddr) = a := by subst haL; rw [hca]
      rw [hb, fill_frontier_self hL0 hLleaf haL hac R hd1, fill_frontier_self hL0 hLleaf haL hac R hd1]
    · unfold frontierValue honestChainValue
      simp only
      rw [depth_fill hL0 hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl, depth_fill hL0 hLleaf haL hac R hd1 _ e ⟨L, c⟩ rfl,
        wotsSeed_fill hL0 hLleaf haL hac R hd1, wotsSeed_fill hL0 hLleaf haL hac R hd1]
      rcases Nat.eq_zero_or_pos (depth (restTable R) ⟨L, c⟩) with h0 | hpos
      · rw [h0, hKK ⟨c, hc⟩ h0, eval_chain_zero, eval_chain_zero]
      · obtain ⟨k, hk⟩ : ∃ k, depth (restTable R) ⟨L, c⟩ = 1 + k := ⟨depth (restTable R) ⟨L, c⟩ - 1, by omega⟩
        rw [hk, Correctness.eval_chain_add, Correctness.eval_chain_add T]
        have hlab : ∀ (X : Fin 17 → Digest), evalWithAnswerFn (PrefixGame.fillTable a (ovL L R (X, progF g Lab X)) e)
            (chain L.lay L.tree L.leaf c 0 1 (seedOf X c)) = Lab ⟨c, hc⟩ := by
          intro X
          rw [eval_chain_one]
          rw [show chainInput L.lay L.tree L.leaf c 0 (seedOf X c) =
            chainRow ⟨L, (⟨c, hc⟩ : Fin (chainCount L.lay))⟩ 0 (seedOf X c)
            from rfl, fill_zero hL0 hLleaf haL hac R hd1 _ e ⟨c, hc⟩ hca, ChainGraph.joinOutput_low]
          simp only [progF, Function.update_self]
        rw [hlab K', hlab K]
        have hk256 : 0 + 1 + k ≤ 256 := by
          have := Mask.depth_le_seven (restTable R) ⟨L, c⟩; omega
        refine Respects.eval_eq (S := fun q => T' q = T q) ?_ (fun q hq => hq)
        unfold chain
        refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
        rw [pad64_chainInput]
        obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hstep
        exact (fill_pub_indep hL0 hLleaf haL hac R hd1 _ _ e _ (hnz c step value (by omega) (by omega))).symm
end Fill

end Leaf
end ClaudeWCT.W9.T3.Security.Wots
