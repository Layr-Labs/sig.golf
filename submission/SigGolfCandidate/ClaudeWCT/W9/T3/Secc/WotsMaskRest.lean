import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.T3.Secc.WotsMaskRest

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (a : ChainAddr)
theorem slotAddr_lay : (slotAddr a).key.lay = a.key.lay := by
  unfold slotAddr; split_ifs <;> rfl
theorem respectsP_chain_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i start count : Nat) (v : Digest) :
    Respects (UntouchedP a) (chain lay tree leaf i start count v) :=
  Respects.mono' (Respects.inter (respects_chain_of_lay a hl tree leaf i start count v)
    (respects_chain_of_lay (slotAddr a) (by rw [slotAddr_lay]; exact hl) tree leaf i start count v))
    fun _ hq => untouchedP_of_untouched a hq
theorem wotsTweak_ne_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i : Nat) :
    wotsTweak lay tree leaf i ≠ seedTweakP a := by
  intro h
  apply hl
  unfold wotsTweak seedTweakP seedTweak WCT9.lowerSeedHeader at h
  split_ifs at h <;> exact lay_eq_of_header a h
variable {T T' : Answers} (hT : ∀ q, UntouchedP a q → T q = T' q)
include hT
theorem wotsSeed_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i : Nat) :
    WCT9.wotsSeed T lay tree leaf i = WCT9.wotsSeed T' lay tree leaf i := by
  by_cases h0 : lay = 0
  · rw [wotsSeed_eq _ h0, wotsSeed_eq _ h0, hT (.inr (.inl _)) (wotsTweak_ne_of_lay a hl tree leaf i)]
  · rw [WCT9.wotsSeed_lower _ h0, WCT9.wotsSeed_lower _ h0]
    apply lowerSeed_congr_cells
    intro p
    apply hT (.inr (.inl _))
    intro h
    apply hl
    unfold seedTweakP seedTweak WCT9.lowerSeedHeader at h
    split_ifs at h <;> exact lay_eq_of_header a h
theorem wotsEnd_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i : Nat) :
    WCT9.wotsEnd T lay tree leaf i = WCT9.wotsEnd T' lay tree leaf i := by
  unfold WCT9.wotsEnd
  rw [wotsSeed_congr_of_lay a hT hl]
  exact (respectsP_chain_of_lay a hl _ _ _ _ _ _).eval_eq hT
theorem wotsRoot_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf : Nat) :
    WCT9.wotsRoot T lay tree leaf = WCT9.wotsRoot T' lay tree leaf := by
  unfold WCT9.wotsRoot
  rw [List.map_congr_left (fun i _ => wotsEnd_congr_of_lay a hT hl tree leaf i)]
  exact (respectsP_leafHash a _ _ _ _).eval_eq hT
theorem wotsTree_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree : Nat) :
    WCT9.wotsTree T lay tree = WCT9.wotsTree T' lay tree := by
  unfold WCT9.wotsTree
  have hr : WCT9.wotsRoot T lay tree = WCT9.wotsRoot T' lay tree :=
    funext (wotsRoot_congr_of_lay a hT hl tree)
  rw [hr]
  exact (respectsP_buildLevels a 3 _ _ _ _ (by decide)).eval_eq hT
theorem honestForest_congr (index : Nat) : Extract.honestForest T index = Extract.honestForest T' index := by
  rw [Extract.honestForest_eq_wct9, Extract.honestForest_eq_wct9]
  exact ClaudeWCT.WCT9.Wots.honestForest_congr (fun _ hq => hT _ (ftsQuery_untouchedP a hq))
theorem leafMsg_congr : leafMsg T a.key = leafMsg T' a.key := by
  unfold leafMsg
  split
  · rename_i h
    unfold Extract.honestPair
    rw [wotsTree_congr_of_lay a hT (fun he => by
      have := congrArg Fin.val he
      simp only at this
      omega)]
  · rw [honestForest_congr a hT _]
theorem referenceSearch_congr : referenceSearch T a.key = referenceSearch T' a.key := by
  unfold referenceSearch
  rw [leafMsg_congr a hT]
  exact (respectsP_layerCounterSearch a _ _ _ _ _ _).eval_eq hT
end Mask
theorem depth_congr (a : ChainAddr) (T T' : Answers) (hT : ∀ q, UntouchedP a q → T q = T' q) :
    depth T a = depth T' a := by
  unfold depth referenceDigits
  rw [Mask.referenceSearch_congr a hT]
theorem referenceDigits_congr (a : ChainAddr) (T T' : Answers) (hT : ∀ q, UntouchedP a q → T q = T' q) :
    referenceDigits T a.key = referenceDigits T' a.key := by
  unfold referenceDigits
  rw [Mask.referenceSearch_congr a hT]
end ClaudeWCT.W9.T3.Security.Wots
