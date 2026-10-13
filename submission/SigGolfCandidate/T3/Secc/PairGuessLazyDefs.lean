import SigGolfCandidate.T3.Secc.PairGuessFinal

section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
end SigGolfCandidate.T3.Security.BPair
end
section
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
set_option warn.classDefReducibility false in
noncomputable def digestKeyFintype : Fintype (Digest × Message × BitVec 32) := inferInstance
attribute [irreducible] digestKeyFintype
theorem digestInputs_exists :
    ∃ S : Finset HashInput, ∀ x, x ∈ S ↔ ∃ rho m ctr, x = pad64 (digestInput rho m ctr) := by
  refine ⟨(@Finset.univ _ digestKeyFintype).image fun k => pad64 (digestInput k.1 k.2.1 k.2.2), fun x => ?_⟩
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ⟨k.1, k.2.1, k.2.2, rfl⟩
  · rintro ⟨rho, m, ctr, rfl⟩
    exact ⟨(rho, m, ctr), @Finset.mem_univ _ digestKeyFintype _, rfl⟩
noncomputable def digestInputs : Finset HashInput := Classical.choose digestInputs_exists
attribute [irreducible] digestInputs
noncomputable instance (priority := high) digestInputs_decidable (x : HashInput) : Decidable (x ∈ digestInputs) :=
  Classical.propDecidable _
theorem mem_digestInputs {x : HashInput} : x ∈ digestInputs ↔ ∃ rho m ctr, x = pad64 (digestInput rho m ctr) := by
  rw [digestInputs]
  exact Classical.choose_spec digestInputs_exists x
theorem digestInput_mem (rho : Digest) (m : Message) (ctr : BitVec 32) : pad64 (digestInput rho m ctr) ∈ digestInputs :=
  mem_digestInputs.mpr ⟨rho, m, ctr, rfl⟩
theorem digestInput_length (rho : Digest) (m : Message) (ctr : BitVec 32) : (digestInput rho m ctr).length = 64 := by
  simp [digestInput, bytesLE_length]
theorem digestInputs_subset_publicUniverse : digestInputs ⊆ SeccLaw.publicUniverse := by
  intro x hx
  obtain ⟨rho, m, ctr, rfl⟩ := mem_digestInputs.mp hx
  apply SeccLaw.mem_publicUniverse
  rw [Cost.pad64_length, digestInput_length]
  unfold SeccLaw.maxInputLength
  omega
noncomputable def rowVal (D : digestInputs → HashOutput) (x : HashInput) : HashOutput :=
  if h : x ∈ digestInputs then D ⟨x, h⟩ else 0
inductive AuxL where
  | coin (n : Nat)
  | birth (x : HashInput)
  | trial (x : HashInput)
  | nonce (m : Message)
  | expose (o : Option HashOutput)
abbrev AuxSpecL : OracleSpec AuxL
  | .coin n => Fin (n + 1)
  | .birth _ => HashOutput
  | .trial _ => HashOutput
  | .nonce _ => Digest
  | .expose _ => Unit
abbrev WSpecL := SecretGuessObservation.World AuxSpecL FtsCoord Digest
structure LazyMem where
  rows : Sampling.RCache
  nonces : Message → Option Digest
  births : List HashOutput
  trials : List HashInput
  exposures : List HashOutput
def LazyMem.empty : LazyMem := ⟨∅, fun _ => none, [], [], []⟩
abbrev WStateL := SecretGuessObservation.State FtsCoord Digest LazyMem
def LazyMem.readRow (mem : LazyMem) (x : HashInput) (a : HashOutput) (isBirth : Bool) : LazyMem :=
  { mem with rows := mem.rows.cacheQuery x a,
             births := if isBirth then mem.births ++ [a] else mem.births,
             trials := if isBirth then mem.trials else mem.trials ++ [x] }
def LazyMem.replayRow (mem : LazyMem) (x : HashInput) (isBirth : Bool) : LazyMem :=
  if isBirth then mem else { mem with trials := mem.trials ++ [x] }
def LazyMem.drawNonce (mem : LazyMem) (m : Message) (v : Digest) : LazyMem :=
  { mem with nonces := Function.update mem.nonces m (some v) }
def LazyMem.expose (mem : LazyMem) (o : Option HashOutput) : LazyMem :=
  { mem with exposures := mem.exposures ++ o.toList }
noncomputable def rowStep (mem : LazyMem) (x : HashInput) (isBirth : Bool) (fresh : PMF HashOutput) :
    PMF (HashOutput × LazyMem) :=
  match mem.rows x with
  | some a => pure (a, mem.replayRow x isBirth)
  | none => if x ∈ digestInputs then (fun a => (a, mem.readRow x a isBirth)) <$> fresh
      else pure (0, mem.replayRow x isBirth)
noncomputable def nonceStep (mem : LazyMem) (m : Message) (fresh : PMF Digest) : PMF (Digest × LazyMem) :=
  match mem.nonces m with
  | some v => pure (v, mem)
  | none => (fun v => (v, mem.drawNonce m v)) <$> fresh
section World
noncomputable local instance instDecidableEqCache_pairGuessLazyDefs : DecidableEq T3.Cache := Classical.decEq _
end World
end SigGolfCandidate.T3.Security.BPair
end
