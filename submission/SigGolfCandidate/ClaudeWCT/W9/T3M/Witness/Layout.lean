import SigGolfCandidate.T3M.Witness.Queries

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (sibOff chainP nodeHashP PubGood allQ_bind allQ_mapM allQ_foldlM pubGood_chainP
  pubGood_leafHash pubGood_nodeHashP)
open SigGolfCandidate.T3M.SecurityExtraction (hashPath merkleInput foldlM_finRange_eq_hashPath)
def wsize : Nat := 21488
abbrev WBytes := BitVec (8 * 21488)
def wbyte (w : WBytes) (i : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * i) 8)
def wdig (w : WBytes) (off : Nat) : Digest := w.extractLsb' (8 * off) 128
def wle32 (w : WBytes) (off : Nat) : BitVec 32 := w.extractLsb' (8 * off) 32
def rhoOff : Nat := 21456
def dcOff : Nat := 21480
def layerBase (lay : Layer) : Nat := (![8000, 12224, 15344, 18400] : Layer → Nat) lay
def pathSlots (lay : Layer) : Nat := (![48, 23, 19, 19] : Layer → Nat) lay
def lowerPlanL1 : List (List Nat) :=[[0,2,4,6,8,10,12],[19,0,2,4,6,8,10],[0,19,2,4,6,8,10],[19,16,0,2,4,6,8],[0,2,19,4,6,8,10],[19,0,16,2,4,6,8],[0,19,16,2,4,6,8],[19,16,13,0,2,4,6],[0,2,4,19,6,8,10],[19,0,2,16,4,6,8],[0,19,2,16,4,6,8],[19,16,0,13,2,4,6],[0,2,19,16,4,6,8],[19,0,16,13,2,4,6],[0,19,16,13,2,4,6],[19,16,13,10,0,2,4],[0,2,4,6,19,8,10],[19,0,2,4,16,6,8],[0,19,2,4,16,6,8],[19,16,0,2,13,4,6],[0,2,19,4,16,6,8],[19,0,16,2,13,4,6],[0,19,16,2,13,4,6],[19,16,13,0,10,2,4],[0,2,4,19,16,6,8],[19,0,2,16,13,4,6],[0,19,2,16,13,4,6],[19,16,0,13,10,2,4],[0,2,19,16,13,4,6],[19,0,16,13,10,2,4],[0,19,16,13,10,2,4],[19,16,13,10,7,0,2],[0,2,4,6,8,19,10],[19,0,2,4,6,16,8],[0,19,2,4,6,16,8],[19,16,0,2,4,13,6],[0,2,19,4,6,16,8],[19,0,16,2,4,13,6],[0,19,16,2,4,13,6],[19,16,13,0,2,10,4],[0,2,4,19,6,16,8],[19,0,2,16,4,13,6],[0,19,2,16,4,13,6],[19,16,0,13,2,10,4],[0,2,19,16,4,13,6],[19,0,16,13,2,10,4],[0,19,16,13,2,10,4],[19,16,13,10,0,7,2],[0,2,4,6,19,16,8],[19,0,2,4,16,13,6],[0,19,2,4,16,13,6],[19,16,0,2,13,10,4],[0,2,19,4,16,13,6],[19,0,16,2,13,10,4],[0,19,16,2,13,10,4],[19,16,13,0,10,7,2],[0,2,4,19,16,13,6],[19,0,2,16,13,10,4],[0,19,2,16,13,10,4],[19,16,0,13,10,7,2],[0,2,19,16,13,10,4],[19,0,16,13,10,7,2],[0,19,16,13,10,7,2],[19,16,13,10,7,4,0],[0,2,4,6,8,10,14],[19,0,2,4,6,8,16],[0,19,2,4,6,8,16],[19,16,0,2,4,6,13],[0,2,19,4,6,8,16],[19,0,16,2,4,6,13],[0,19,16,2,4,6,13],[19,16,13,0,2,4,10],[0,2,4,19,6,8,16],[19,0,2,16,4,6,13],[0,19,2,16,4,6,13],[19,16,0,13,2,4,10],[0,2,19,16,4,6,13],[19,0,16,13,2,4,10],[0,19,16,13,2,4,10],[19,16,13,10,0,2,7],[0,2,4,6,19,8,16],[19,0,2,4,16,6,13],[0,19,2,4,16,6,13],[19,16,0,2,13,4,10],[0,2,19,4,16,6,13],[19,0,16,2,13,4,10],[0,19,16,2,13,4,10],[19,16,13,0,10,2,7],[0,2,4,19,16,6,13],[19,0,2,16,13,4,10],[0,19,2,16,13,4,10],[19,16,0,13,10,2,7],[0,2,19,16,13,4,10],[19,0,16,13,10,2,7],[0,19,16,13,10,2,7],[19,16,13,10,7,0,4],[0,2,4,6,8,19,16],[19,0,2,4,6,16,13],[0,19,2,4,6,16,13],[19,16,0,2,4,13,10],[0,2,19,4,6,16,13],[19,0,16,2,4,13,10],[0,19,16,2,4,13,10],[19,16,13,0,2,10,7],[0,2,4,19,6,16,13],[19,0,2,16,4,13,10],[0,19,2,16,4,13,10],[19,16,0,13,2,10,7],[0,2,19,16,4,13,10],[19,0,16,13,2,10,7],[0,19,16,13,2,10,7],[19,16,13,10,0,7,4],[0,2,4,6,19,16,13],[19,0,2,4,16,13,10],[0,19,2,4,16,13,10],[19,16,0,2,13,10,7],[0,2,19,4,16,13,10],[19,0,16,2,13,10,7],[0,19,16,2,13,10,7],[19,16,13,0,10,7,4],[0,2,4,19,16,13,10],[19,0,2,16,13,10,7],[0,19,2,16,13,10,7],[19,16,0,13,10,7,4],[0,2,19,16,13,10,7],[19,0,16,13,10,7,4],[0,19,16,13,10,7,4],[19,16,13,10,7,4,1]]
def lowerPlanL32 : List (List Nat) :=[[0,2,4,6,8,10],[15,0,2,4,6,8],[0,15,2,4,6,8],[15,12,0,2,4,6],[0,2,15,4,6,8],[15,0,12,2,4,6],[0,15,12,2,4,6],[15,12,9,0,2,4],[0,2,4,15,6,8],[15,0,2,12,4,6],[0,15,2,12,4,6],[15,12,0,9,2,4],[0,2,15,12,4,6],[15,0,12,9,2,4],[0,15,12,9,2,4],[15,12,9,6,0,2],[0,2,4,6,15,8],[15,0,2,4,12,6],[0,15,2,4,12,6],[15,12,0,2,9,4],[0,2,15,4,12,6],[15,0,12,2,9,4],[0,15,12,2,9,4],[15,12,9,0,6,2],[0,2,4,15,12,6],[15,0,2,12,9,4],[0,15,2,12,9,4],[15,12,0,9,6,2],[0,2,15,12,9,4],[15,0,12,9,6,2],[0,15,12,9,6,2],[12,9,6,3,0,15],[0,2,4,6,8,15],[15,0,2,4,6,12],[0,15,2,4,6,12],[15,12,0,2,4,9],[0,2,15,4,6,12],[15,0,12,2,4,9],[0,15,12,2,4,9],[15,12,9,0,2,6],[0,2,4,15,6,12],[15,0,2,12,4,9],[0,15,2,12,4,9],[15,12,0,9,2,6],[0,2,15,12,4,9],[15,0,12,9,2,6],[0,15,12,9,2,6],[12,9,6,3,15,0],[0,2,4,6,15,12],[15,0,2,4,12,9],[0,15,2,4,12,9],[15,12,0,2,9,6],[0,2,15,4,12,9],[15,0,12,2,9,6],[0,15,12,2,9,6],[12,9,6,15,3,0],[0,2,4,15,12,9],[15,0,2,12,9,6],[0,15,2,12,9,6],[12,9,15,6,3,0],[0,2,15,12,9,6],[12,15,9,6,3,0],[15,12,9,6,3,0],[15,12,9,6,3,0]]
def lowerPlan (lay : Layer) (leaf : Nat) : List Nat :=
  if lay.val = 1 then lowerPlanL1.getD (leaf % 128) [] else lowerPlanL32.getD (leaf % 64) []
def merkleBlock (lay : Layer) (leaf j : Nat) : Nat :=
  layerBase lay + (if lay.val = 0 then 64 * (height lay - 1 - j) else 16 * (lowerPlan lay leaf).getD j 0)
def chainBlock (lay : Layer) (i : Nat) : Nat :=
  layerBase lay + 16 * pathSlots lay + 64 * (chainCount lay - 1 - i)
def wrho (w : WBytes) : Digest := wdig w rhoOff
def wdc (w : WBytes) : BitVec 32 := wle32 w dcOff
def wdcWord (w : WBytes) : BitVec 64 := w.extractLsb' (8 * dcOff) 64
theorem wdc_toNat_le (w : WBytes) : (wdc w).toNat ≤ (wdcWord w).toNat := by
  unfold wdc wle32 wdcWord
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  rw [show (2 : Nat) ^ 32 = 2 ^ 32 from rfl, ← Nat.mod_mod_of_dvd _ (show 2 ^ 32 ∣ 2 ^ 64 by norm_num)]
  exact Nat.mod_le _ _
def wvalue (w : WBytes) (lay : Layer) (i : Nat) : Digest := wdig w (chainBlock lay i + 48)
def wchainPads (w : WBytes) (lay : Layer) (i : Nat) : Digest × Digest :=
  (wdig w (chainBlock lay i), wdig w (chainBlock lay i + 32))
def wchainHeaderPad (w : WBytes) (lay : Layer) (i : Nat) : BitVec 64 :=
  (wdig w (chainBlock lay i + 16)).extractLsb' 64 64
def wpath (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest :=
  wdig w (merkleBlock lay leaf j + sibOff (leaf / 2 ^ j % 2))
def wmerklePad (w : WBytes) (lay : Layer) (leaf j : Nat) : Digest := wdig w (merkleBlock lay leaf j + 32)
theorem layerBase_values : List.ofFn (fun lay : Layer => layerBase lay) = [8000, 12224, 15344, 18400] := rfl
theorem layerBase_tiles : ∀ lay : Fin 3,
    layerBase lay.castSucc + 16 * pathSlots lay.castSucc + 64 * chainCount lay.castSucc = layerBase lay.succ := by
  decide
theorem layerBase_end : layerBase 3 + 16 * pathSlots 3 + 64 * chainCount 3 = rhoOff := rfl
theorem dcOff_end : dcOff + 8 = wsize := rfl
def layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalue w lay i.val)
  let value ← leafHash lay tree leaf ends
  (List.finRange (height lay)).foldlM (fun value j => do
    let other := wpath w lay leaf j.val
    let pair := if leaf / 2 ^ j.val % 2 = 0 then (value, other) else (other, value)
    nodeHashP 3 lay.val tree (2 ^ (height lay - j.val - 1) + leaf / 2 ^ (j.val + 1)) pair.1
      (wmerklePad w lay leaf j.val) pair.2) value
def layerLeafP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M Digest := do
  let (leaf, tree) := route index lay
  let ends ← (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wchainHeaderPad w lay i.val) (wvalue w lay i.val)
  leafHash lay tree leaf ends
theorem layerP_eq_hashPath (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerP w index lay digits = (layerLeafP w index lay digits >>= fun value =>
      hashPath (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerklePad w lay (route index lay).1)) (height lay) value) := by
  unfold layerP layerLeafP
  rcases route index lay with ⟨leaf, tree⟩
  dsimp only
  rw [bind_assoc]
  congr 1
  funext ends
  congr 1
  funext value
  exact foldlM_finRange_eq_hashPath
    (merkleInput 3 lay.val tree (height lay) leaf (wpath w lay leaf) (wmerklePad w lay leaf)) (height lay) value
theorem pubGood_layerP (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (layerP w index lay digits) PubGood := by
  unfold layerP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chainP _ _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHash _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => pubGood_nodeHashP _ _ _ _ _ _ _) _
end ClaudeWCT.W9.T3M
