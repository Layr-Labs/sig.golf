import SigGolfCandidate.T3.Secc.LargeContactChain
import SigGolfCandidate.T3.Secc.LargeContactWalk

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
