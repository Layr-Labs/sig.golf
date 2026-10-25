import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEncodingResample
import SigGolfCandidate.T3_Secc_WotsPrefixGameBase
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsMaskRef
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_SeccLaw
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsMaskRest

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsPrefixGameBase : Fintype Coordinate := coordinateFintype
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
end PrefixGame
abbrev RefTables (adversary : AdversaryP) := FullGame.FullTable × (referenceInputs adversary → HashOutput)
noncomputable instance instFintypeRefTables (adversary : AdversaryP) : Fintype (RefTables adversary) := by
  unfold RefTables FullGame.FullTable
  infer_instance
instance instNonemptyRefTables (adversary : AdversaryP) : Nonempty (RefTables adversary) := ⟨(fun _ => 0, fun _ => 0)⟩
noncomputable def restLaw (adversary : AdversaryP) : PMF (RefTables adversary) := PMF.uniformOfFintype _
noncomputable def restTable {adversary : AdversaryP} (R : RefTables adversary) : Answers :=
  eagerAnswers (referenceInputs adversary) R.1 R.2
@[irreducible] noncomputable def restDepth {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) : Nat :=
  depth (restTable R) a
theorem restDepth_eq {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) :
    restDepth a R = depth (restTable R) a := by
  unfold restDepth; rfl
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem chainRowW_mem (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRowW a step value ∈ referenceInputs adversary := by
  unfold referenceInputs
  apply Finset.mem_union_left
  apply SeccLaw.mem_publicUniverse
  rw [chainRowW_eq]
  have h : (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain step value).length = 64 := by
    simp [WCT9.chainInputW_length]
  rw [h]
  unfold SeccLaw.maxInputLength
  omega
theorem restTable_mem (R : RefTables adversary) (input : HashInput) (h : input ∈ referenceInputs adversary) :
    restTable R (.inl (.inr input)) = R.2 ⟨input, h⟩ := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ (referenceInputs adversary) R.2 input = R.2 ⟨input, h⟩
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_pos h]
  rfl
theorem restTable_nonmem (R : RefTables adversary) (input : HashInput) (h : input ∉ referenceInputs adversary) :
    restTable R (.inl (.inr input)) = (0 : HashOutput) := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ (referenceInputs adversary) R.2 input = (0 : HashOutput)
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_neg h]
  rfl
theorem restTable_private (R : RefTables adversary) (coordinate : Coordinate) :
    restTable R (.inr coordinate) = R.1 coordinate := rfl
/-- Pairing stage 1: the prefix row of chain `a` (current-scheme row `chainRowW`) that `input` is, if any. -/
noncomputable def rowOf (a : ChainAddr) (d : Nat) (input : HashInput) : Option (Fin d × Digest) :=
  if h : ∃ p : Fin d × Digest, input = chainRowW a p.1 p.2 then some (Classical.choose h) else none
theorem rowOf_some {a : ChainAddr} {d : Nat} {input : HashInput} {p : Fin d × Digest}
    (h : PrefixGame.rowOf a d input = some p) : input = chainRowW a p.1 p.2 := by
  unfold PrefixGame.rowOf at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h
theorem rowOf_none {a : ChainAddr} {d : Nat} {input : HashInput} (h : rowOf a d input = none) (p : Fin d × Digest) :
    input ≠ chainRowW a p.1 p.2 := by
  intro he
  unfold PrefixGame.rowOf at h
  rw [dif_pos ⟨p, he⟩] at h
  cases h
theorem rowOf_chainRow (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (i : Fin d) (v : Digest) :
    PrefixGame.rowOf a d (chainRowW a i v) = some (i, v) := by
  cases h : PrefixGame.rowOf a d (chainRowW a i v) with
  | none => exact absurd rfl (PrefixGame.rowOf_none h (i, v))
  | some p =>
      have he := PrefixGame.rowOf_some h
      obtain ⟨hs, hv⟩ := chainRowW_inj (by omega) (by have := p.1.isLt; omega) he
      rw [show p = (i, v) from Prod.ext (Fin.ext hs.symm) hv.symm]
theorem rowOf_none_iff (a : ChainAddr) {d : Nat} (input : HashInput) :
    PrefixGame.rowOf a d input = none ↔ ¬∃ step value, step < d ∧ input = chainRowW a step value := by
  constructor
  · rintro h ⟨step, value, hs, rfl⟩
    exact PrefixGame.rowOf_none h (⟨step, hs⟩, value) rfl
  · intro h
    cases hp : PrefixGame.rowOf a d input with
    | none => rfl
    | some p => exact absurd ⟨p.1.val, p.2, p.1.isLt, PrefixGame.rowOf_some hp⟩ h
noncomputable def ovPub (a : ChainAddr) (d : Nat) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match PrefixGame.rowOf a d x.val with
  | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) (tables p.1 p.2)
      (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (pub x))
  | none => pub x
/-- The seed of chain `a` in `ov a d R x`: its leaf-family evaluation (every layer: campaign X1 stage B, top leaves
since campaign T8D), unchanged by `ov`; the seed component of `Hidden` is a dummy. -/
noncomputable def ovSeed (a : ChainAddr) (R : RefTables adversary) (_seed : Digest) : Digest :=
  WCT9.wotsSeed (restTable R) a.key.lay a.key.tree a.key.leaf a.chain
/-- Override of chain `a`'s prefix rows (the private table is unchanged). -/
noncomputable def ov (a : ChainAddr) (d : Nat) (R : RefTables adversary) (x : Hidden d) : RefTables adversary :=
  (R.1, ovPub a d R.2 x.1)
noncomputable def rd (a : ChainAddr) (d : Nat) (R : RefTables adversary) : Hidden d :=
  (fun i v => WCT9.halfOf (WCT9.chainHigh a.key.lay a.chain i.val) (R.2 ⟨chainRowW a i v, chainRowW_mem a i v⟩), 0)
theorem ovPub_row (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) (i : Fin d) (v : Digest) :
    ovPub a d pub tables ⟨chainRowW a i v, chainRowW_mem a i v⟩ =
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (tables i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (pub ⟨chainRowW a i v, chainRowW_mem a i v⟩)) := by
  unfold ovPub
  rw [PrefixGame.rowOf_chainRow a hd i v]
theorem ovPub_none (a : ChainAddr) {d : Nat} (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) (x : referenceInputs adversary) (h : PrefixGame.rowOf a d x.val = none) :
    ovPub a d pub tables x = pub x := by
  unfold ovPub
  rw [h]
theorem rd_ov_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    (rd a d (ov a d R x)).1 = x.1 := by
  obtain ⟨tables, seed⟩ := x
  unfold rd ov
  funext i v
  simp only
  rw [ovPub_row a hd, halfOf_joinHalf]
/-- `ov` ignores the seed component. -/
theorem ov_seed_irrel (a : ChainAddr) {d : Nat} (R : RefTables adversary)
    (t : Fin d → Digest → Digest) (s s' : Digest) : ov a d R (t, s) = ov a d R (t, s') := rfl
theorem ov_ov_rd (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ov a d (ov a d R x) (rd a d R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨tables, seed⟩ := x
  unfold ov rd
  simp only
  refine Prod.ext rfl ?_
  · funext y
    unfold ovPub
    cases hp : PrefixGame.rowOf a d y.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hy : y = ⟨chainRowW a p.1 p.2, chainRowW_mem a p.1 p.2⟩ := Subtype.ext (PrefixGame.rowOf_some hp)
        subst hy
        rw [halfOf_not_joinHalf, joinHalf_halfOf]
theorem restTable_ov_untouched (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : RefTables adversary) (x : Hidden d)
    (query : T3.Spec.Domain) (hq : UntouchedP a query) : restTable (ov a d R x) query = restTable R query := by
  rcases query with (n | input) | (tweak | other)
  · rfl
  · by_cases h : input ∈ referenceInputs adversary
    · rw [restTable_mem _ _ h, restTable_mem _ _ h]
      unfold ov
      simp only
      rw [ovPub_none]
      cases hp : PrefixGame.rowOf a d input with
      | none => rfl
      | some p => exact absurd (PrefixGame.rowOf_some hp) (hq p.1 p.2 (by have := p.1.isLt; omega))
    · rw [restTable_nonmem _ _ h, restTable_nonmem _ _ h]
  · rfl
  · rfl
theorem restTable_ov_prefix (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d)
    (i : Fin d) (v : Digest) :
    restTable (ov a d R x) (.inl (.inr (chainRowW a i v))) =
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (x.1 i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (restTable R (.inl (.inr (chainRowW a i v))))) := by
  rw [restTable_mem _ _ (chainRowW_mem a i v), restTable_mem _ _ (chainRowW_mem a i v)]
  exact ovPub_row a hd R.2 x.1 i v
theorem restTable_ov_nonprefix (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d)
    (input : HashInput) (h : PrefixGame.rowOf a d input = none) :
    restTable (ov a d R x) (.inl (.inr input)) = restTable R (.inl (.inr input)) := by
  by_cases hm : input ∈ referenceInputs adversary
  · rw [restTable_mem _ _ hm, restTable_mem _ _ hm]
    exact ovPub_none a R.2 x.1 _ h
  · rw [restTable_nonmem _ _ hm, restTable_nonmem _ _ hm]
/-- `ov` leaves the private table alone. -/
theorem restTable_ov_private (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d)
    (coordinate : Coordinate) : restTable (ov a d R x) (.inr coordinate) = restTable R (.inr coordinate) := rfl
theorem depth_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : RefTables adversary) (x : Hidden d) (b : ChainAddr)
    (hb : b = a) : depth (restTable (ov a d R x)) b = depth (restTable R) b := by
  subst hb
  exact depth_congr b _ _ (restTable_ov_untouched b hd R x)
theorem restDepth_le (a : ChainAddr) (R : RefTables adversary) : restDepth a R ≤ 7 := by
  rw [restDepth_eq]; exact Mask.depth_le_seven _ a
theorem restDepth_ov (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    restDepth a (ov a (restDepth a R) R x) = restDepth a R := by
  have hd : restDepth a R ≤ 7 := restDepth_le a R
  calc restDepth a (ov a (restDepth a R) R x) = depth (restTable (ov a (restDepth a R) R x)) a := restDepth_eq _ _
    _ = depth (restTable R) a := depth_ov a hd R x a rfl
    _ = restDepth a R := (restDepth_eq a R).symm
theorem wotsSeed_ov (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d) :
    WCT9.wotsSeed (restTable (ov a d R x)) a.key.lay a.key.tree a.key.leaf a.chain = ovSeed a R x.2 :=
  Mask.wotsSeed_congr_private (fun c => restTable_ov_private a R x c) _ _ _ _
theorem eval_chain_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ∀ (n s : Nat) (hn : s + n ≤ d) (v : Digest),
      evalWithAnswerFn (restTable (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s n v) =
        SphincsSecurity.Concrete.PartialChainEndpoint.evaluate
          (fun (i : Fin n) => x.1 ⟨s + i.val, by omega⟩) v := by
  intro n
  induction n with
  | zero =>
      intro s hn v
      simp [WCT9.chainW, SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
  | succ n ih =>
      intro s hn v
      have hsplit : evalWithAnswerFn (restTable (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s (n + 1) v) =
          evalWithAnswerFn (restTable (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain (s + 1) n
            (evalWithAnswerFn (restTable (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s 1 v))) := by
        rw [show n + 1 = 1 + n by omega]
        exact eval_chainW_add' _ _ _ _ _ _ _ _ _
      rw [hsplit, eval_chainW_one', pad64_chainInputW]
      have hrow : WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain s v = chainRowW a (⟨s, by omega⟩ : Fin d) v := rfl
      rw [hrow, restTable_ov_prefix a hd R x]
      rw [show (⟨s, by omega⟩ : Fin d).val = s from rfl, halfOf_joinHalf, ih (s + 1) (by omega)]
      simp only [SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
      congr 1
      · funext i w
        unfold Fin.tail
        exact congrArg (fun j : Fin d => x.1 j w) (Fin.ext (by simp only [Fin.val_succ]; omega))
theorem frontierValue_ov (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    frontierValue (restTable (ov a (restDepth a R) R x)) a =
      SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 (ovSeed a R x.2) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hdepth : depth (restTable (ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  unfold frontierValue honestChainValueW
  rw [hdepth, wotsSeed_ov]
  rw [eval_chain_ov a hd R x (restDepth a R) 0 (by omega)]
  congr 1
  funext i
  exact congrArg x.1 (Fin.ext (by simp only [Nat.zero_add]))
end PrefixGame
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
namespace RawPrefix
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
include hU in
theorem chainRowW_mem (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRowW a step value ∈ U := by
  apply hU
  apply SeccLaw.mem_publicUniverse
  rw [chainRowW_eq]
  have h : (WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain step value).length = 64 := by
    simp [WCT9.chainInputW_length]
  rw [h]
  unfold SeccLaw.maxInputLength
  omega
theorem raw_mem (R : Tables U) (input : HashInput) (h : input ∈ U) :
    raw R (.inl (.inr input)) = R.2 ⟨input, h⟩ := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ U R.2 input = R.2 ⟨input, h⟩
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_pos h]
  rfl
theorem raw_nonmem (R : Tables U) (input : HashInput) (h : input ∉ U) :
    raw R (.inl (.inr input)) = (0 : HashOutput) := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ U R.2 input = (0 : HashOutput)
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_neg h]
  rfl
theorem raw_private (R : Tables U) (coordinate : Coordinate) :
    raw R (.inr coordinate) = R.1 coordinate := rfl
noncomputable def ovPub (a : ChainAddr) (d : Nat) (pub : U → HashOutput)
    (tables : Fin d → Digest → Digest) : U → HashOutput := fun x =>
  match PrefixGame.rowOf a d x.val with
  | some p => joinHalf (WCT9.chainHigh a.key.lay a.chain p.1.val) (tables p.1 p.2)
      (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain p.1.val) (pub x))
  | none => pub x
/-- The seed of chain `a` in `ov a d R x`: its leaf-family evaluation (every layer: campaign X1 stage B, top leaves
since campaign T8D), unchanged by `ov`; the seed component of `Hidden` is a dummy. -/
noncomputable def ovSeed (a : ChainAddr) (R : Tables U) (_seed : Digest) : Digest :=
  WCT9.wotsSeed (raw R) a.key.lay a.key.tree a.key.leaf a.chain
/-- Override of chain `a`'s prefix rows (the private table is unchanged). -/
noncomputable def ov (a : ChainAddr) (d : Nat) (R : Tables U) (x : Hidden d) : Tables U :=
  (R.1, ovPub a d R.2 x.1)
noncomputable def rd (a : ChainAddr) (d : Nat) (R : Tables U) : Hidden d :=
  (fun i v => WCT9.halfOf (WCT9.chainHigh a.key.lay a.chain i.val) (R.2 ⟨chainRowW a i v, chainRowW_mem hU a i v⟩), 0)
theorem ovPub_row (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (pub : U → HashOutput)
    (tables : Fin d → Digest → Digest) (i : Fin d) (v : Digest) :
    ovPub a d pub tables ⟨chainRowW a i v, chainRowW_mem hU a i v⟩ =
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (tables i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (pub ⟨chainRowW a i v, chainRowW_mem hU a i v⟩)) := by
  unfold ovPub
  rw [PrefixGame.rowOf_chainRow a hd i v]
theorem ovPub_none (a : ChainAddr) {d : Nat} (pub : U → HashOutput)
    (tables : Fin d → Digest → Digest) (x : U) (h : PrefixGame.rowOf a d x.val = none) :
    ovPub a d pub tables x = pub x := by
  unfold ovPub
  rw [h]
theorem rd_ov_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (x : Hidden d) :
    (rd hU a d (ov a d R x)).1 = x.1 := by
  obtain ⟨tables, seed⟩ := x
  unfold rd ov
  funext i v
  simp only
  rw [ovPub_row hU a hd, halfOf_joinHalf]
/-- `ov` ignores the seed component. -/
theorem ov_seed_irrel (a : ChainAddr) {d : Nat} (R : Tables U)
    (t : Fin d → Digest → Digest) (s s' : Digest) : ov a d R (t, s) = ov a d R (t, s') := rfl
theorem ov_ov_rd (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (x : Hidden d) :
    ov a d (ov a d R x) (rd hU a d R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨tables, seed⟩ := x
  unfold ov rd
  simp only
  refine Prod.ext rfl ?_
  · funext y
    unfold ovPub
    cases hp : PrefixGame.rowOf a d y.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hy : y = ⟨chainRowW a p.1 p.2, chainRowW_mem hU a p.1 p.2⟩ := Subtype.ext (PrefixGame.rowOf_some hp)
        subst hy
        rw [halfOf_not_joinHalf, joinHalf_halfOf]
theorem raw_ov_untouched (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : Tables U) (x : Hidden d)
    (query : T3.Spec.Domain) (hq : UntouchedP a query) : raw (ov a d R x) query = raw R query := by
  rcases query with (n | input) | (tweak | other)
  · rfl
  · by_cases h : input ∈ U
    · rw [raw_mem _ _ h, raw_mem _ _ h]
      unfold ov
      simp only
      rw [ovPub_none]
      cases hp : PrefixGame.rowOf a d input with
      | none => rfl
      | some p => exact absurd (PrefixGame.rowOf_some hp) (hq p.1 p.2 (by have := p.1.isLt; omega))
    · rw [raw_nonmem _ _ h, raw_nonmem _ _ h]
  · rfl
  · rfl
include hU in
theorem raw_ov_prefix (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (x : Hidden d)
    (i : Fin d) (v : Digest) :
    raw (ov a d R x) (.inl (.inr (chainRowW a i v))) =
      joinHalf (WCT9.chainHigh a.key.lay a.chain i.val) (x.1 i v)
        (WCT9.halfOf (!WCT9.chainHigh a.key.lay a.chain i.val) (raw R (.inl (.inr (chainRowW a i v))))) := by
  rw [raw_mem _ _ (chainRowW_mem hU a i v), raw_mem _ _ (chainRowW_mem hU a i v)]
  exact ovPub_row hU a hd R.2 x.1 i v
theorem raw_ov_nonprefix (a : ChainAddr) {d : Nat} (R : Tables U) (x : Hidden d)
    (input : HashInput) (h : PrefixGame.rowOf a d input = none) :
    raw (ov a d R x) (.inl (.inr input)) = raw R (.inl (.inr input)) := by
  by_cases hm : input ∈ U
  · rw [raw_mem _ _ hm, raw_mem _ _ hm]
    exact ovPub_none a R.2 x.1 _ h
  · rw [raw_nonmem _ _ hm, raw_nonmem _ _ hm]
/-- `ov` leaves the private table alone. -/
theorem raw_ov_private (a : ChainAddr) {d : Nat} (R : Tables U) (x : Hidden d)
    (coordinate : Coordinate) : raw (ov a d R x) (.inr coordinate) = raw R (.inr coordinate) := rfl

theorem search_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : Tables U) (x : Hidden d)
    (L : LeafAddr) (remaining : Nat) :
    searchOf (raw (ov a d R x)) zeroMessages L remaining=searchOf (raw R) zeroMessages L remaining := by
  unfold searchOf
  exact ((CanonicalRef.Mask.respectsP_layerCounterSearchAt a _ _ _ _ _ _ _)
    _ _ (raw_ov_untouched a hd R x)).1

theorem referenceSearch_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : Tables U) (x : Hidden d)
    (L : LeafAddr) :
    referenceSearch (raw (ov a d R x)) zeroMessages L=referenceSearch (raw R) zeroMessages L :=
  CanonicalRef.referenceSearch_congr (fun L remaining _ => search_ov a hd R x L remaining) L

theorem depth_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 7) (R : Tables U) (x : Hidden d) (b : ChainAddr) :
    CanonicalRef.depth (raw (ov a d R x)) zeroMessages b=CanonicalRef.depth (raw R) zeroMessages b := by
  unfold CanonicalRef.depth CanonicalRef.referenceDigits
  rw [referenceSearch_ov a hd R x]

end RawPrefix
end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized

namespace ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawPrefix
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3.Security.Wots.PrefixGame
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
variable {U : Finset HashInput} (hU : SeccLaw.publicUniverse⊆U)
@[irreducible] noncomputable def restDepth (a : ChainAddr) (R : Tables U) : Nat :=
  CanonicalRef.depth (raw R) zeroMessages a

theorem restDepth_eq (a : ChainAddr) (R : Tables U) :
    restDepth a R=CanonicalRef.depth (raw R) zeroMessages a := by unfold restDepth; rfl

theorem restDepth_le (a : ChainAddr) (R : Tables U) : restDepth a R≤7 := by
  rw [restDepth_eq]
  exact CanonicalRef.Mask.depth_le_seven _ _ _

theorem restDepth_ov (a : ChainAddr) (R : Tables U) (x : Hidden (restDepth a R)) :
    restDepth a (ov a (restDepth a R) R x)=restDepth a R := by
  rw [restDepth_eq,depth_ov a (by have := restDepth_le a R;omega),←restDepth_eq]

theorem wotsSeed_ov (a : ChainAddr) {d : Nat} (R : Tables U) (x : Hidden d) :
    WCT9.wotsSeed (raw (ov a d R x)) a.key.lay a.key.tree a.key.leaf a.chain = ovSeed a R x.2 :=
  Wots.Mask.wotsSeed_congr_private (fun c => raw_ov_private a R x c) _ _ _ _
include hU in
theorem eval_chain_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : Tables U) (x : Hidden d) :
    ∀ (n s : Nat) (hn : s + n ≤ d) (v : Digest),
      evalWithAnswerFn (raw (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s n v) =
        SphincsSecurity.Concrete.PartialChainEndpoint.evaluate
          (fun (i : Fin n) => x.1 ⟨s + i.val, by omega⟩) v := by
  intro n
  induction n with
  | zero =>
      intro s hn v
      simp [WCT9.chainW, SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
  | succ n ih =>
      intro s hn v
      have hsplit : evalWithAnswerFn (raw (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s (n + 1) v) =
          evalWithAnswerFn (raw (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain (s + 1) n
            (evalWithAnswerFn (raw (ov a d R x)) (WCT9.chainW a.key.lay a.key.tree a.key.leaf a.chain s 1 v))) := by
        rw [show n + 1 = 1 + n by omega]
        exact eval_chainW_add' _ _ _ _ _ _ _ _ _
      rw [hsplit, eval_chainW_one', pad64_chainInputW]
      have hrow : WCT9.chainInputW a.key.lay a.key.tree a.key.leaf a.chain s v = chainRowW a (⟨s, by omega⟩ : Fin d) v := rfl
      rw [hrow, raw_ov_prefix hU a hd R x]
      rw [show (⟨s, by omega⟩ : Fin d).val = s from rfl, halfOf_joinHalf, ih (s + 1) (by omega)]
      simp only [SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
      congr 1
      · funext i w
        unfold Fin.tail
        exact congrArg (fun j : Fin d => x.1 j w) (Fin.ext (by simp only [Fin.val_succ]; omega))
include hU in
theorem frontierValue_ov (a : ChainAddr) (R : Tables U) (x : Hidden (restDepth a R)) :
    CanonicalRef.frontierValue (raw (ov a (restDepth a R) R x)) zeroMessages a =
      SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 (ovSeed a R x.2) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hdepth : CanonicalRef.depth (raw (ov a (restDepth a R) R x)) zeroMessages a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  unfold CanonicalRef.frontierValue honestChainValueW
  rw [hdepth, wotsSeed_ov]
  rw [eval_chain_ov hU a hd R x (restDepth a R) 0 (by omega)]
  congr 1
  funext i
  exact congrArg x.1 (Fin.ext (by simp only [Nat.zero_add]))

end ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized.RawPrefix
