import SigGolfCandidate.T3.Secc.WotsPrefixGameBase
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixObservedRun
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCheckpoint

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsPrefixGameSim : Fintype Coordinate := coordinateFintype
open Mask
abbrev SeedResult := Option (Bool × Nat) × List RefWorld.Domain
namespace PrefixGame
variable {adversary : AdversaryP}
abbrev SeedSpec (d : Nat) := unifSpec + PrefixSpec d Digest
theorem evaluate_const : ∀ (n : Nat) (value : Digest),
    evaluate (fun (_ : Fin n) (_ : Digest) => value) value = value
  | 0, _ => rfl
  | n + 1, value => by
      simp only [evaluate]
      exact evaluate_const n value
end PrefixGame
namespace PrefixGame
variable {adversary : AdversaryP}
def PrefixQuery (a : ChainAddr) (d : Nat) (query : RefWorld.Domain) : Prop :=
  ∃ (i : Fin d) (v : Digest), query = .inl (.inr (chainRow a i v))
theorem observedRun_bind {d : Nat} {α β : Type} (tables : Fin d → Digest → Digest)
    (first : OracleComp (SeedSpec d) α) (next : α → OracleComp (SeedSpec d) β)
    (observed : Fin d → Digest → Option Digest) :
    observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (first >>= next) observed =
      (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables first observed).bind fun r =>
        observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (next r.1) r.2 := by
  simp only [observedRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
end PrefixGame
namespace PrefixGame
theorem lazyRun_mem_support {d : Nat} {β : Type} (computation : OracleComp (SeedSpec d) β) :
    ∀ (observed : Fin d → Digest → Option Digest) (result : β × (Fin d → Digest → Option Digest)),
      result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl computation observed).support →
        result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro observed result hr
      rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff] at hr
      subst hr
      exact (mem_support_pure_iff _ _).mpr rfl
  | query_bind input next ih =>
      intro observed result hr
      rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
      rw [mem_support_bind_iff]
      cases input with
      | inl input =>
          simp only [SphincsSecurity.Concrete.PartialChainEndpoint.lazyImpl, StateT.run_mk, PMF.bind_map,
            PMF.mem_support_bind_iff] at hr
          obtain ⟨answer, _, hr⟩ := hr
          exact ⟨answer, by simp only [support_query, Set.mem_univ], ih answer observed result hr⟩
      | inr query =>
          simp only [SphincsSecurity.Concrete.PartialChainEndpoint.lazyImpl, StateT.run_mk, PMF.bind_map,
            PMF.mem_support_bind_iff] at hr
          obtain ⟨answer, _, hr⟩ := hr
          exact ⟨answer, by simp only [support_query, Set.mem_univ], ih answer _ result hr⟩
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
