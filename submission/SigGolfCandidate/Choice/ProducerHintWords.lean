import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest
import SigGolfCandidate.T3M.Bytes

namespace SigGolfCandidate.Choice.ProducerHintWords
open SigGolfCandidate.T3 (HashOutput)
open SigGolfCandidate.T3M (zeros wordsOf wordsOf_append wordsOf_bytesLE length_wordsOf)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (witList headerBytes wctBytes layerRegion leafBuffersBytes tailBytes)
open ClaudeWCT
set_option Elab.async false
set_option maxRecDepth 10000

def leadBytes (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 1 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
    zeros 8 ++ bytesLE 8 1 ++ bytesLE 4 (w.counters 3) ++ zeros 68

def suffix (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  zeros 32 ++
    (if (WCT9.child N 8).val / 2 ^ 6 % 2 = 0 then bytesLE 16 ((w.signature.openings 8).path 6) else zeros 16) ++
    zeros 16 ++ wctBytes N w.signature ++ (List.finRange 4).flatMap (layerRegion N w) ++
    leafBuffersBytes w.signature ++ tailBytes w

theorem prefix_length (N : HashOutput) (w : WCT9.Witness) : (leadBytes N w).length=104 := by
  simp only [leadBytes,List.length_append,bytesLE_length,zeros,List.length_replicate]
  split <;> simp [bytesLE_length]

theorem split_hint (N : HashOutput) (w : WCT9.Witness) :
    witList N w=leadBytes N w ++ (bytesLE 8 w.topHint ++ suffix N w) := by
  simp only [witList,headerBytes,leadBytes,suffix,List.append_assoc]

theorem words_split (N : HashOutput) (w : WCT9.Witness) :
    wordsOf (witList N w)=wordsOf (leadBytes N w) ++ (w.topHint :: wordsOf (suffix N w)) := by
  rw [split_hint,wordsOf_append _ _ (by simp [prefix_length]),
    wordsOf_append _ _ (by simp [bytesLE_length])]
  have hw : wordsOf (bytesLE 8 w.topHint)=[w.topHint] := by
    simpa using wordsOf_bytesLE 1 w.topHint
  rw [hw]
  rfl

/-- Replacing the hint changes precisely witness word 13 (byte offset 104). -/
theorem word_update (N : HashOutput) (w : WCT9.Witness) (hint : BitVec 64) (i : Nat) :
    (wordsOf (witList N {w with topHint:=hint})).getD i 0=
      if i=13 then hint else (wordsOf (witList N w)).getD i 0 := by
  rw [words_split,words_split]
  change (wordsOf (leadBytes N w) ++ (hint :: wordsOf (suffix N w))).getD i 0=
    if i=13 then hint else (wordsOf (leadBytes N w) ++ (w.topHint :: wordsOf (suffix N w))).getD i 0
  have hp : (wordsOf (leadBytes N w)).length=13 := length_wordsOf 13 _ (prefix_length N w)
  by_cases hi : i<13
  · rw [if_neg (by omega),List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega),hp]
    by_cases he : i=13
    · subst he
      simp
    · rw [if_neg he,List.getD_append_right _ _ _ _ (by omega),hp]
      obtain ⟨j,hj⟩ : ∃ j, i-13=j+1 := ⟨i-14,by omega⟩
      rw [hj]
      rfl

end SigGolfCandidate.Choice.ProducerHintWords
#print axioms SigGolfCandidate.Choice.ProducerHintWords.word_update
