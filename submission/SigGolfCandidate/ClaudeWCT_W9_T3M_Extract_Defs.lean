import SigGolfCandidate.ClaudeWCT_W9_T3M_Witness_Encode
import SigGolfCandidate.ClaudeWCT_W9_T3M_Extract_Basic

namespace ClaudeWCT.W9.T3M.WctExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
def HonestQ (answers : Answers) (N : HashOutput) (c : WCT9.Coord) (q : Spec.Domain) : Prop :=
  (∃ t : Fin 6, ∃ s, 4 - WCT9.wordDigit (WCT9.rank N c) t ≤ s ∧ s < 4 ∧
      q = .inl (.inr (Extract.honestInput answers
        (.wctChain (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val s)))) ∨
    q = .inl (.inr (Extract.honestInput answers (.wctLeaf (WCT9.digestIndex N) c.val (WCT9.child N c).val))) ∨
    ∃ l, l < 6 ∧ q = .inl (.inr (Extract.honestInput answers
      (.wctNode (WCT9.digestIndex N) c.val l ((WCT9.child N c).val / 2 ^ (l + 1)))))
/-- Honest coordinate (nested FTS r1-1): revealed values, chain pads, the Merkle siblings (including the supplied
top sibling) and the pads of the five low fold levels are honest. The leaf pad and the top fold's pad are not
witness data for coordinates 1..8: they are the previous coordinate's top pair (`WctHonest` pins coordinate 0's). -/
def CoordHonest (answers : Answers) (N : HashOutput) (w : WBytes) (c : WCT9.Coord) : Prop :=
  (∀ t : Fin 6, wreveal w c.val t.val (WCT9.wordDigit (WCT9.rank N c) t) =
      Extract.wctValue answers (WCT9.digestIndex N) c.val (WCT9.child N c).val t.val
        (4 - WCT9.wordDigit (WCT9.rank N c) t) ∧
    (0 < WCT9.wordDigit (WCT9.rank N c) t →
      wcpads w c.val t.val = (0, 0) ∧ wcHeaderPad w c.val t.val = 0)) ∧
  (∀ l, l < 7 → wsib w c.val (WCT9.child N c).val l =
      treeValue (Extract.ftsLevels answers (WCT9.digestIndex N) c.val) l ((WCT9.child N c).val / 2 ^ l ^^^ 1) ∧
    (l < 5 → wmpad w c.val (WCT9.child N c).val l = 0))
def WctHonest (answers : Answers) (N : HashOutput) (w : WBytes) : Prop :=
  (∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (WCT9.digestIndex N) N),
      ∃ c : WCT9.Coord, HonestQ answers N c q) ∧
    (∀ c : WCT9.Coord, CoordHonest answers N w c) ∧ wctStart w = (0, 0)
end ClaudeWCT.W9.T3M.WctExtract
namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open ClaudeWCT.WCT9 (wotsTree wotsValue)
def msgFits (lay : Layer) : WCT9.LayerMsg → Prop
  | .forest _ => False
  | .pair _ _ => True
def LayerShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : Prop :=
  (∀ j, j < height lay →
    wpath w lay (route index lay).1 j =
        treeValue (wotsTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
      (j + 1 < height lay ∨ lay.val = 0 → wmerklePad w lay (route index lay).1 j =
        WCT9.nonceDigest (WCT9.honestNonce answers lay (route index lay).2 j ((route index lay).1 / 2 ^ (j + 1)))) ∧
      (j + 1 < height lay ∨ lay.val = 0 → wmerkleHigh w lay (route index lay).1 j = 0)) ∧
  (∀ i, i < chainCount lay →
    wvalueFor w lay digits i = wotsValue answers lay (route index lay).2 (route index lay).1 digits i ∧
      (digits.getD i 0 < maxDigit lay i →
        wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
  wleafHigh w lay = 0
def Frame (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg) (digits : List Nat) :
    Prop :=
  (wbcCtr w index lay).toNat < WCT9.verifyWindow ∧
    decode lay (evalWithAnswerFn answers (ClaudeWCT.WCT9.encodingHash lay (layerEncodingInputP lay (route index lay).2 (route index lay).1
      msg (wbcCtr w index lay) (wbcPad w index lay) (wbcRight w) (wbcHigh w index lay)))) = some digits
def encodingQuery (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg) : Spec.Domain :=
  .inl (.inr (pad64 (layerEncodingInputP lay (route index lay).2 (route index lay).1 msg (wbcCtr w index lay)
    (wbcPad w index lay) (wbcRight w) (wbcHigh w index lay))))
def Good (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  ∃ digits, Frame answers w index lay (honestMsg answers index lay) digits ∧ LayerShaped answers w index lay digits
def Diverge (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (qs : List Spec.Domain) : Prop :=
  ∃ msg digits, msgFits lay msg ∧ msg ≠ honestMsg answers index lay ∧ Frame answers w index lay msg digits ∧
    LayerShaped answers w index lay digits ∧ encodingQuery w index lay msg ∈ qs
end ClaudeWCT.W9.T3M.Extract
