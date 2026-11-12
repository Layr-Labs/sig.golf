import SigGolfCandidate.OuterPairedFtsTrial
import SigGolfCandidate.OuterGroundDeterministic
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterPairedStructural
open ClaudeWCT
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.WCT9 ClaudeWCT.WCT9.Wots ClaudeWCT.W9.T3M
open SigGolfCandidate.Research SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
attribute [local instance] Classical.propDecidable
variable (T : Answers) (index : Nat) (hidx : index<2^31)
def HonestQuery (T : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x=none ∨ (∃ p : Extract.Pos, Extract.Paired.Bounded p ∧ x=OuterExtractModel.honestInput T p) ∨
      ClaudeWCT.W9.T3.Security.Wots.PairedStructural.TopTrial T x ∨ FtsTrial T x
  | _ => True
 include hidx in
theorem honest_sharedNode_input (coord : Coord) (heap : Nat)
    (hcut:SharedForest.heapCut (Extract.Paired.first coord.val) ≤ heap) (hh:heap<128) (hg : ¬ WCT9.ftsGround coord.val heap) (ho : ¬(Extract.Paired.first coord.val=false ∧ heap<4)) :
    HonestQuery T (.inl (.inr (pad64 (wctTopInput coord.val index heap
      ((OuterExtractModel.nodes T index coord.val).getD (2*heap) 0)
      (if 4≤heap ∧ heap<8 then (OuterExtractModel.pads T index coord.val (heap/2-2)).2 else 0)
      ((OuterExtractModel.nodes T index coord.val).getD (2*heap+1) 0))))) := by
  have h2:2≤heap := (SharedForest.heapCut_bounds _).1.trans hcut
  obtain ⟨hL,hN,hH⟩:=Extract.heap_decomp h2 hh
  have hused : Extract.Paired.first coord.val=true → Extract.heapLevel heap<5 := by
    intro hf
    have h4:4≤heap := by simpa only [SharedForest.heapCut,hf,if_true] using hcut
    have hlog:2≤Nat.log 2 heap := Nat.le_log_of_pow_le (by decide) h4
    unfold Extract.heapLevel;omega
  refine Or.inr (Or.inl ⟨.wctNode index coord.val (Extract.heapLevel heap) (Extract.heapNode heap),
    ⟨⟨hidx,coord.isLt,hL,hN⟩,hused⟩,?_⟩)
  have hsub:7-Extract.heapLevel heap-1=6-Extract.heapLevel heap := by omega
  rw [hsub] at hH hN
  have he : Extract.heapLevel heap=4 ↔ 4≤heap ∧ heap<8 := by
    have hlo:2^(6-Extract.heapLevel heap)≤heap := by omega
    have hhi:heap<2*2^(6-Extract.heapLevel heap) := by omega
    generalize Extract.heapLevel heap=L at hL hlo hhi ⊢
    interval_cases L <;> norm_num at hlo hhi ⊢ <;> omega
  have h3 : ¬ OuterExtractGround.ftsNonceLevel coord.val (Extract.heapLevel heap) := by
    intro hn
    rcases hn with hn|⟨hl,hf⟩
    · have hlo:2^(6-Extract.heapLevel heap)≤heap := by omega
      have hhi:heap<2*2^(6-Extract.heapLevel heap) := by omega
      exact hg ((Extract.Paired.ftsNonceLevel_iff (by omega) hlo hhi).mp hn)
    · have hh:heap<4 := by norm_num [hl] at hN hH;omega
      exact ho ⟨hf,hh⟩
  simp only [OuterExtractModel.honestInput,hH,he,if_neg h3]

theorem search_lower (coord index heap : Nat) (left right : Digest) :
    ∀ fuel n, n ≤ (evalWithAnswerFn T (OuterGroundCore.search coord index heap left right fuel n)).1
  | 0,n => by simp only [OuterGroundCore.search,evalWithAnswerFn_bind,evalWithAnswerFn_pure];exact le_rfl
  | fuel+1,n => by
      simp only [OuterGroundCore.search,evalWithAnswerFn_bind]
      split
      · exact le_rfl
      · exact Nat.le_trans (by omega) (search_lower coord index heap left right fuel (n+1))
theorem sat_outerSearch {Q : SigGolfCandidate.T3.Spec.Domain → Prop} (coord index heap : Nat) (left right : Digest) :
    ∀ fuel n, (∀ k, n ≤ k → k ≤ (evalWithAnswerFn T (OuterGroundCore.search coord index heap left right fuel n)).1 →
      Q (.inl (.inr (OuterGroundCore.trial coord index heap k left right)))) →
    QueriesSat T Q (OuterGroundCore.search coord index heap left right fuel n)
  | 0,n,hk => by
      have hq:=hk n le_rfl (search_lower T coord index heap left right 0 n)
      unfold OuterGroundCore.search OuterGroundCore.hashN
      exact QueriesSat.bind (QueriesSat.query hq) (QueriesSat.pure' _)
  | fuel+1,n,hk => by
      have hq:=hk n le_rfl (search_lower T coord index heap left right (fuel+1) n)
      have hr : ¬OuterGroundCore.zeroOk coord (evalWithAnswerFn T (OuterGroundCore.hashN coord index heap n left right))=true →
          QueriesSat T Q (OuterGroundCore.search coord index heap left right fuel (n+1)) := by
        intro hz
        apply sat_outerSearch (Q := Q) coord index heap left right fuel (n+1)
        intro k h1 h2
        apply hk k (by omega)
        simpa only [OuterGroundCore.search,evalWithAnswerFn_bind,if_neg hz] using h2
      unfold OuterGroundCore.search
      refine QueriesSat.bind (by unfold OuterGroundCore.hashN;exact QueriesSat.bind (QueriesSat.query hq) (QueriesSat.pure' _)) ?_
      split
      · exact QueriesSat.pure' _
      · next hz => exact hr hz
#print axioms honest_sharedNode_input
#print axioms sat_outerSearch
end OuterPairedStructural
