import SigGolfCandidate.FtsMoment
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000000
set_option linter.all false
namespace OuterGroundCore
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost
open ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh (expectedValue_uniform_ite_F)
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false

def width (coord : Nat) : Nat := if coord=8 then 4 else 3
def offset (coord heap : Nat) : Nat := if coord=8 ∧ heap=3 then 0 else 128
def value (coord heap : Nat) (a : HashOutput) : Digest := a.extractLsb' (offset coord heap) 128
def zeroOk (coord : Nat) (v : Digest) : Bool := v.toNat / 2^(128-width coord)==0
def cap (coord : Nat) : Nat := 256*2^width coord
abbrev trial := ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.fTrial
abbrev trial_length := ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.fTrial_length
abbrev trial_injective := ClaudeWCT.W9.T3.Freshness.Paired.FtsFresh.fTrial_injective

def hashN (coord index heap n : Nat) (left right : Digest) : M Digest :=
  publicQuery (trial coord index heap n left right) >>= fun a => pure (value coord heap a)

def search (coord index heap : Nat) (left right : Digest) : Nat → Nat → M (Nat × Digest)
  | 0,n => do
      let v ← hashN coord index heap n left right
      pure (n,v)
  | fuel+1,n => do
      let v ← hashN coord index heap n left right
      if zeroOk coord v then pure (n,v) else search coord index heap left right fuel (n+1)

def nodeAt (coord index heap : Nat) (left right : Digest) : M (Nat × Digest) :=
  search coord index heap left right (cap coord-1) 0

theorem width_bounds (coord : Nat) : 3≤width coord ∧ width coord≤4 := by unfold width;split_ifs <;> omega
theorem offset_bounds (coord heap : Nat) : offset coord heap+128≤256 := by unfold offset;split_ifs <;> omega

theorem search_zero_bind {β : Type} (coord index heap : Nat) (left right : Digest) (n : Nat)
    (next : Nat × Digest → M β) :
    (search coord index heap left right 0 n >>= next)=
      (publicQuery (trial coord index heap n left right) >>= fun a => next (n,value coord heap a)) := by
  simp only [search,hashN,bind_assoc,pure_bind]

theorem search_succ_bind {β : Type} (coord index heap : Nat) (left right : Digest) (fuel n : Nat)
    (next : Nat × Digest → M β) :
    (search coord index heap left right (fuel+1) n >>= next)=
      (publicQuery (trial coord index heap n left right) >>= fun a =>
        if zeroOk coord (value coord heap a) then next (n,value coord heap a)
        else search coord index heap left right fuel (n+1) >>= next) := by
  simp only [search,hashN,bind_assoc,pure_bind]
  congr 1
  funext a
  split <;> simp only [pure_bind]

theorem V_search_bind {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (coord index heap : Nat)
    (left right : Digest) (next : Nat × Digest → M β) (G : RCache → Prop) (B b : ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (trial coord index heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      V secret z (next (k, value coord heap answer)) (cache.cacheQuery (trial coord index heap k left right) answer) ≤ B)
    (hstep : z * expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if zeroOk coord (value coord heap answer) then B else b) ≤ b)
    (htail : z * B ≤ b) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (trial coord index heap k left right) = none) →
      V secret z (search coord index heap left right fuel n >>= next) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [search_zero_bind, V_publicQuery, trial_length]
      have hf := expectedValue_fresh (trial coord index heap n left right) cache (hfresh n le_rfl (by omega))
        (fun r => V secret z (next (n, value coord heap r.1)) r.2)
      refine le_trans (le_of_eq (congrArg (fun t => z ^ (64 / 64) * t) hf)) ?_
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      refine le_trans (mul_le_mul' le_rfl ?_) htail
      refine (expectedValue_mono _ fun answer => hnext cache hg n answer).trans ?_
      rw [expectedValue_const (by simp)]
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [search_succ_bind, V_publicQuery, trial_length]
      have hf := expectedValue_fresh (trial coord index heap n left right) cache (hfresh n le_rfl (by omega))
        (fun r => V secret z (if zeroOk coord (value coord heap r.1) then next (n, value coord heap r.1)
          else (search coord index heap left right fuel (n + 1) >>= next)) r.2)
      refine le_trans (le_of_eq (congrArg (fun t => z ^ (64 / 64) * t) hf)) ?_
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      refine le_trans (mul_le_mul' le_rfl (expectedValue_mono _ fun answer => ?_)) hstep
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : trial coord index heap k left right ≠ trial coord index heap n left right := by
          intro he
          have := trial_injective coord index heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))


theorem value_toNat (coord heap : Nat) (a : HashOutput) :
    (value coord heap a).toNat=a.toNat/2^offset coord heap%2^128 := by
  simp [value,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

theorem zeroOk_iff (coord heap : Nat) (a : HashOutput) : zeroOk coord (value coord heap a)=true ↔
    a.toNat/2^(offset coord heap+(128-width coord))%2^width coord=0 := by
  have hb := width_bounds coord
  have hv := (value coord heap a).isLt
  have hlt : (value coord heap a).toNat/2^(128-width coord)<2^width coord := by
    rw [Nat.div_lt_iff_lt_mul (by positivity),←pow_add]
    have he : width coord+(128-width coord)=128 := by omega
    simpa only [he] using hv
  unfold zeroOk
  rw [beq_iff_eq,←Nat.mod_eq_of_lt hlt,value_toNat,
    ClaudeWCT.W9.T3.TopMoment.window_of_half _ _ _ (by omega),Nat.div_div_eq_div_mul,←pow_add]

theorem prob_accept (coord heap : Nat) :
    Pr[fun a : HashOutput => zeroOk coord (value coord heap a)=true | ($ᵗ HashOutput : ProbComp HashOutput)]=
      ((2:ENNReal)^width coord)⁻¹ := by
  have hb := width_bounds coord
  simp only [zeroOk_iff]
  exact ClaudeWCT.W9.T3.TopMoment.prob_window _ _ _ (by have := offset_bounds coord heap;omega) (by positivity)

theorem V_nodeAt_bind {β : Type} (secret : BitVec 256) (z f B : ENNReal)
    (coord index heap : Nat) (left right : Digest) (next : Nat × Digest → M β) (G : RCache → Prop)
    (hG : ∀ cache,G cache → ∀ k answer,G (cache.cacheQuery (trial coord index heap k left right) answer))
    (hnext : ∀ cache,G cache → ∀ k answer,
      V secret z (next (k,value coord heap answer)) (cache.cacheQuery (trial coord index heap k left right) answer)≤B)
    (hfac : z*(((2:ENNReal)^width coord)⁻¹+(1-((2:ENNReal)^width coord)⁻¹)*f)≤f ∧ z≤f)
    (cache : RCache) (hg : G cache)
    (hfresh : ∀ k,cache (trial coord index heap k left right)=none) :
    V secret z (nodeAt coord index heap left right >>= next) cache≤f*B := by
  have hc : cap coord-1<2^64 := by
    have hb := width_bounds coord
    have hp : 2^width coord≤2^4 := Nat.pow_le_pow_right (by decide) hb.2
    unfold cap
    omega
  unfold nodeAt
  apply V_search_bind secret z coord index heap left right next G B (f*B) hG hnext
  · rw [expectedValue_uniform_ite_F (fun a => zeroOk coord (value coord heap a)=true),prob_accept]
    calc
      z*(((2:ENNReal)^width coord)⁻¹*B+(1-((2:ENNReal)^width coord)⁻¹)*(f*B))=
        (z*(((2:ENNReal)^width coord)⁻¹+(1-((2:ENNReal)^width coord)⁻¹)*f))*B := by ring
      _ ≤ f*B := mul_le_mul' hfac.1 le_rfl
  · exact mul_le_mul' hfac.2 le_rfl
  · simpa using hc
  · exact hg
  · intro k _ _
    exact hfresh k

theorem cap_failure3 : 7^2048*2^210≤8^2048 := by decide +kernel
theorem cap_failure4 : 15^4096*2^210≤16^4096 := by decide +kernel
theorem union_nodes_indices : 10*2^31≤2^40 := by decide
#print axioms V_search_bind
#print axioms prob_accept
#print axioms V_nodeAt_bind
#print axioms cap_failure4
end OuterGroundCore
