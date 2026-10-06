import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTopJoin

/- Cost transport on the SAME already-fused common54 baseline. The final
   return saving is never counted again: the sole new saving is entryJAL1.
   This is a source/native stage law, not a global or measured7531 claim. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.T3M.Nonbinary
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem tail_source_cost (c : NCtx) (hd : c.DigitsOk) :
    c.chainsCost 51 3=legacyThreeCost (c.kOf 17) := by
  have h0:=tail_digits c hd 0 (by decide)
  have h1:=tail_digits c hd 1 (by decide)
  have h2:=tail_digits c hd 2 (by decide)
  simp only [index,Nat.reduceAdd] at h0 h1 h2
  unfold NCtx.chainsCost
  change NCtx.chainCost 51 (c.dig 51)+(NCtx.chainCost 52 (c.dig 52)+
    (NCtx.chainCost 53 (c.dig 53)+0))=legacyThreeCost (c.kOf 17)
  rw [h0,h1,h2]
  unfold legacyThreeCost
  omega

theorem all54_cost_saved_one (c : NCtx) (hd : c.DigitsOk) :
    all54Cost c+1=c.chainsCost 0 54+67 := by
  have hr : c.kOf 17<64 := by
    have hh:=c.kOf_lt hd 17 (by decide)
    simpa only [mx,Nat.reduceLT,if_false,Nat.reduceAdd,Nat.reducePow] using hh
  have hs:=true_final3_saves_one c (c.kOf 17) hr (tail_digits c hd)
  have hc:=c.prefix_chainsCost_add 0 51 3
  norm_num only at hc
  rw [tail_source_cost c hd] at hc
  unfold all54Cost
  omega

#print axioms all54_cost_saved_one
end SigGolfCandidate.T3M.Nonbinary.InlineTail
