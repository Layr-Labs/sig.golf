import SigGolfCandidate.T3_Secc_LargeCouplingObserved
import SigGolfCandidate.T3_Secc_LargeCouplingSign
import SigGolfCandidate.T3_Secc_LargeCouplingTrace
import SigGolfCandidate.T3_Secc_WotsClasses
set_option Elab.async false

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingQuery : DecidableEq T3.Cache := Classical.decEq _
noncomputable def routerLabels (vals : Coord → Digest) (a : AuxData) : Labels :=
  joinLabels (fun N => vals (.inl N)) a.high
def HonestPrefix (vals : Coord → Digest) (a : AuxData) (X : HashInput) : Prop :=
  ∃ (L : EncLeaf) (ctr : BitVec 32), X = Wots.encodingRow L.toWots (vals (msgCoord L)) ctr ∧ PrefixRow a L ctr
structure Coherent (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) : Prop where
  agrees : Agrees T (routerLabels vals a)
  secrets : secretsOf T = fun s => vals (.inr s)
  residual : ∀ (X : HashInput) (hX : X ∈ U), (∀ N : CanonGraph.Node, X ≠ cell (secretsOf T) N (routerLabels vals a)) →
    ¬HonestPrefix vals a X → T (.inl (.inr X)) = τ ⟨X, hX⟩
  prefixRow : ∀ (L : EncLeaf) (ctr : BitVec 32), PrefixRow a L ctr →
    T (.inl (.inr (Wots.encodingRow L.toWots (vals (msgCoord L)) ctr))) = prefixValue a L ctr
  search : ∀ L : EncLeaf, Wots.referenceSearch T L.toWots =
    (a.sel L).bind fun r => (decode L.1.lay r.2).map fun d => (BitVec.ofNat 32 r.1.val, d)
  priv : ∀ c : Coordinate, (∀ i : Fin 2, (c, i) ∉ Set.range secretCoordinate) → (∀ m : Message, c ≠ .inr (.inl m)) →
    T (.inr c) = a.priv c
  outside : ∀ X, X ∉ U → T (.inl (.inr X)) = (0 : HashOutput)
  nonce : ∀ m : Message, (T (.inr (.inr (.inl m)))).extractLsb' 0 128 = nv m
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
end Coherent
theorem low_eq (y : HashOutput) : low y = y.extractLsb' 0 128 := rfl
theorem dummyDigest_decode' (lay : Layer) : decode lay (dummyDigest lay) = some (Wots.dummyDigits lay) :=
  Classical.choose_spec (Wots.dummyDigits_valid lay)
section Reference
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
theorem Coherent.referenceDigits (h : Coherent U T vals nv τ a) (L : EncLeaf) :
    Wots.referenceDigits T L.toWots = ((a.sel L).bind fun r => decode L.1.lay r.2).getD (Wots.dummyDigits L.1.lay) := by
  unfold Wots.referenceDigits
  rw [h.search]
  cases hs : a.sel L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases decode L.1.lay r.2 <;> rfl
end Reference
section Relation
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
end Relation
section Query
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem keep_guess_label {C : Type} (vals : C → Digest) (c p : C) (m : Digest) (y : HashOutput) :
    (⟨some (c, m), .label p⟩ : Probe C).keep vals y ↔ vals c ≠ m ∧ vals p ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_label {C : Type} (vals : C → Digest) (p : C) (y : HashOutput) :
    (⟨none, .label p⟩ : Probe C).keep vals y ↔ vals p ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_target {C : Type} (vals : C → Digest) (t : Digest) (y : HashOutput) :
    (⟨none, .target t⟩ : Probe C).keep vals y ↔ t ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
theorem keep_guess_target {C : Type} (vals : C → Digest) (c : C) (m t : Digest) (y : HashOutput) :
    (⟨some (c, m), .target t⟩ : Probe C).keep vals y ↔ vals c ≠ m ∧ t ≠ low y := by
  simp [Probe.keep, Probe.guessMiss, Hit.miss]
end Query
section Cases
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest} {τ : Cell U → HashOutput} {a : AuxData}
  {q : Nat} {st : RouterState} {ws : LargeResidual.State WCoord (Cell U)}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem lookupVal_map (f : Coord → Digest) (cs : List Coord) (c : Coord) (hc : c ∈ cs) :
    lookupVal (cs.map fun c => (c, f c)) c = f c := by
  induction cs with
  | nil => cases hc
  | cons d rest ih =>
      unfold lookupVal
      simp only [List.map_cons, List.find?_cons]
      by_cases hd : d = c
      · subst hd
        simp
      · simp only [hd, decide_false]
        exact ih ((List.mem_cons.mp hc).resolve_left (Ne.symm hd))
end Cases
end SigGolfCandidate.T3.Security.LargeCoupling
