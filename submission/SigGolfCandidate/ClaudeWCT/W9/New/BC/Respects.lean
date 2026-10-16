import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskBase

namespace ClaudeWCT.W9.T3.Security.Wots.Mask
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Mask
set_option maxHeartbeats 1000000
theorem untouched_layerEncoding (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    Untouched a (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg counter)))) :=
  untouched_of_hdr a _ (rowTweak lay tree leaf)
    (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInput lay tree leaf msg counter)
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_rowTweak _ _ _ _ _ _ _ _))
/-- C2/C3 (FULL): a chain header (marker at least 128) is no encoding row tweak, whatever its witness high word. -/
theorem chainHeader_ne_rowTweakW (lay : Layer) (tree leaf i step : Nat) (up : Layer) (tree' leaf' : Nat)
    (hi : BitVec 64) : chainHeader lay tree leaf i step ≠ WCT9.rowTweakW up tree' leaf' hi := by
  intro h
  have hc := chainHeader_tweakMarker lay tree leaf i step
  rw [h] at hc
  unfold WCT9.rowTweakW at hc
  rw [append64_marker, hyperWord_toNat] at hc
  omega
theorem untouched_layerEncodingP (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) (pad : BitVec 96) (padR : Digest) (hi : BitVec 64) :
    Untouched a (.inl (.inr (pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay tree leaf msg counter pad padR hi)))) :=
  untouched_of_hdr a _ (WCT9.rowTweakW lay tree leaf hi)
    (ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP lay tree leaf msg counter pad padR hi)
    (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_rowTweakW _ _ _ _ _ _ _ _ _))
theorem respects_layerEncoding (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (counter : BitVec 32) :
    Respects (Untouched a) (ClaudeWCT.WCT9.encodingHash lay (WCT9.layerEncodingInput lay tree leaf msg counter)) :=
  Respects.map (WCT9.encodingAnswer lay) (Respects.publicHash _ (untouched_layerEncoding a lay tree leaf msg counter))
theorem respects_layerCounterSearch (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel counter, Respects (Untouched a) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact Respects.pure' _
  | succ fuel ih =>
      intro counter
      simp only [WCT9.layerCounterSearch]
      refine Respects.bind (respects_layerEncoding a _ _ _ _ _) fun answer => ?_
      split
      · exact ih _
      · exact Respects.pure' _
theorem respectsP_layerCounterSearch (a : ChainAddr) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg)
    (fuel counter : Nat) :
    Respects (UntouchedP a) (WCT9.layerCounterSearch lay tree leaf msg counter fuel) :=
  Respects.untouchedP (fun c => respects_layerCounterSearch c lay tree leaf msg fuel counter) a
end ClaudeWCT.W9.T3.Security.Wots.Mask
namespace ClaudeWCT.W9.T3.Security.Wots.Ref
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Ref
theorem shortRespects_encodingHash (lay : Layer) (input : HashInput)
    (h : (pad64 input).length ≤ SeccLaw.maxInputLength) : ShortRespects (WCT9.encodingHash lay input) := by
  intro A T hAT
  rw [WCT9.eval_encodingHash, WCT9.eval_encodingHash, hAT.public _ h]
theorem layerCounterSearch_respects (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    ShortRespects (WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => exact ShortRespects.pure' _
  | succ fuel ih =>
      unfold WCT9.layerCounterSearch
      refine ShortRespects.bind (shortRespects_encodingHash lay _ ?_) fun answer => ?_
      · rw [← ClaudeWCT.W9.T3M.BC.pad64_layerEncodingInputP_zero, ClaudeWCT.W9.T3M.BC.layerEncodingRow_length]
        unfold SeccLaw.maxInputLength
        omega
      · split
        · exact ih _
        · exact ShortRespects.pure' _
end ClaudeWCT.W9.T3.Security.Wots.Ref
