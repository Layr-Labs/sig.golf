import SigGolfCandidate.T3.Secc.WotsSmallContract
import SigGolfCandidate.T3.Secc.WotsTwoEdge
import SigGolfCandidate.T3.Secc.WotsEncodingMatch
import SigGolfCandidate.T3.Secc.WotsStructural
import SigGolfCandidate.T3.Secc.WotsTransportCount

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallA
theorem hdrBlock_chainRow (a : ChainAddr) (s : Nat) (v : Digest) :
    Extract.hdrBlock (chainRow a s v) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
  chainInput_header _ _ _ _ _ _
theorem hdrBlock_digest (rho : Digest) (m : Message) (c : BitVec 32) :
    Extract.hdrBlock (pad64 (digestInput rho m c)) = bytesLE 16 (digestHeader c) := by
  unfold digestInput
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega), Extract.hdrBlock_prefix]
theorem chainRow_ne_digest (a : ChainAddr) (s : Nat) (v : Digest) (rho : Digest) (m : Message) (c : BitVec 32) :
    chainRow a s v ≠ pad64 (digestInput rho m c) := by
  intro h
  have hb := congrArg Extract.hdrBlock h
  rw [hdrBlock_chainRow, hdrBlock_digest] at hb
  exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hb)
theorem sourceChain_bounds {a : ChainAddr} (ha : WotsExtract.SourceChain a) :
    a.key.tree < 2 ^ 31 ∧ a.key.leaf < 4096 ∧ a.chain < 64 := by
  obtain ⟨⟨ht, hl⟩, hc⟩ := ha
  have hh : 2 ^ height a.key.lay ≤ 2 ^ 12 :=
    Nat.pow_le_pow_right (by norm_num) (by have := height_le a.key.lay; omega)
  have hcc := Mask.chainCount_le a.key.lay
  refine ⟨by omega, by omega, by omega⟩
end SmallA
open SmallA
end SigGolfCandidate.T3.Security.Wots
