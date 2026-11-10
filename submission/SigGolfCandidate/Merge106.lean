import SigGolfCandidate.Merge057
import SigGolfCandidate.Merge098
import SigGolfCandidate.Merge105

-- ==== merged from T3_Secc_LargeContactEvents ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem slotValue_block4_three (a b c d : Digest) : slotValue (block4 a b c d) 3 = d := by
  unfold slotValue block4
  have ha := bytesLE_length 16 a
  have hb := bytesLE_length 16 b
  have hc := bytesLE_length 16 c
  have hd := bytesLE_length 16 d
  rw [show 16 * 3 = (bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c).length by simp [ha, hb, hc]]
  rw [List.drop_left]
  rw [show (bytesLE 16 d).take 16 = bytesLE 16 d from List.take_of_length_le (by rw [hd])]
  exact Correctness.readDigest_bytesLE d
theorem chainRow_block4 (a : Wots.ChainAddr) (s : Nat) (v : Digest) :
    Wots.chainRow a s v = block4 0 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) 0 v := by
  simp only [Wots.chainRow, chainInput, block4, show zero16 = bytesLE 16 (0 : Digest) by decide]
theorem slotValue_chainRow (a : Wots.ChainAddr) (s : Nat) (v : Digest) : slotValue (Wots.chainRow a s v) 3 = v := by
  rw [chainRow_block4, slotValue_block4_three]
theorem chainCount_le58 (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide
def gAddr (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) : ChainGraph.Address :=
  ⟨a.key.lay, ⟨a.key.tree, ha.1.1⟩,
    ⟨a.key.leaf, lt_of_lt_of_le ha.1.2 (by
      calc 2 ^ height a.key.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le _)
        _ = 4096 := by norm_num)⟩,
    ⟨a.chain, lt_of_lt_of_le ha.2 (chainCount_le58 _)⟩⟩
theorem wotsAddr_gAddr (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) : wotsAddr (gAddr a ha) = a := rfl
theorem honestChainValue_zero' (A : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) :
    honestChainValue A lay tree leaf i seed 0 = seed := by
  simp [honestChainValue, chain]
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeContactInputs ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem record_inputs (U : Finset HashInput) {α : Type} (program : M α) (state : LazyPrivate.State)
    (hin : Wots.Ref.InputsIn U program state) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program state)) :
    ∀ e ∈ result.events, ∀ x, e.input = .inl (.inr x) → x ∈ U := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at hr
      subst hr
      intro e he
      cases he
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last, hl, rfl⟩ := hr
      have hadv := FirstHit.query_advance state input middle hm
      rcases input with (n | y) | c
      · have hin' := Wots.Ref.InputsIn.coin hin middle.1
        intro e he x hx
        rcases List.mem_cons.mp he with rfl | he
        · cases hx
        · have hst : middle.2 = state := by rw [hadv]; rfl
          rw [hst] at hl
          exact ih middle.1 state hin' last hl e he x hx
      · obtain ⟨hy, hnext⟩ := Wots.Ref.InputsIn.public hin
        intro e he x hx
        rcases List.mem_cons.mp he with rfl | he
        · cases hx
          exact hy
        · rw [hadv] at hl
          exact ih middle.1 _ (hnext middle.1) last hl e he x hx
      · have hcached : ∀ v, state.1 c = some v → v = middle.1 := by
          intro v hv
          have hext := SourceReplay.query_extends (.inr c) state middle hm
          have h1 : SourceReplay.known middle.2 (.inr c) = some v :=
            SourceReplay.known_mono _ _ hext (show SourceReplay.known state (.inr c) = some v from hv)
          have h2 := SourceReplay.hash_query_caches (.inr c) trivial state middle hm
          rw [h1] at h2
          exact Option.some.inj h2
        have hin' := Wots.Ref.InputsIn.priv hin middle.1 hcached
        intro e he x hx
        rcases List.mem_cons.mp he with rfl | he
        · cases hx
        · rw [hadv] at hl
          exact ih middle.1 _ hin' last hl e he x hx
end SigGolfCandidate.T3.Security.LargeCoupling
end
-- ==== merged from T3_Secc_LargeContactCase ====
section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem record_events_known {α : Type} (program : M α) (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) :
    ∀ event ∈ result.events, SourceReplay.IsHash event.input →
      SourceReplay.known result.state event.input = some event.answer := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at hr
      subst hr
      intro event he; cases he
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last, hl, rfl⟩ := hr
      have hext := SourceReplay.run_extends (next middle.1) middle.2 (last.value, last.state)
        (FirstHit.recorded_support _ _ _ hl)
      intro event he hi
      rcases List.mem_cons.mp he with rfl | he
      · exact SourceReplay.known_mono middle.2 last.state hext
          (SourceReplay.hash_query_caches input hi before middle hm)
      · exact ih middle.1 middle.2 last hl event he hi
end SigGolfCandidate.T3.Security.LargeCoupling
end
