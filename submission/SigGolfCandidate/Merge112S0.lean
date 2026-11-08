import SigGolfCandidate.Merge112
set_option linter.all false

/-! # Z5: pre/post-marker split of the WOTS union bound, shared definitions

For a source chain `a`, the first marker of `a` (`Restart.MarkerAt`, an encoding row decoding to a unit neighbour
of the reference word at chain `a`) splits the trace. `stopIdx` is the least `k` with a marker in `trace.take k`
(the whole trace when there is none), `preTrace` the trace up to and including the first marker, `preCount a s`
the chain-`a` prefix rows of the pre-marker trace (`CanonicalRef.Normalized.prefixCount a s` restricted to it). Pre-marker events of `a`
hold on some prefix `trace.take k` that has no marker of `a` yet. -/

namespace ClaudeWCT.W9.T3.Security.Wots.Z5
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.Wots.CanonicalRef ClaudeWCT.W9.T3.Security.Wots.CanonicalRef.Normalized
attribute [local instance] Classical.propDecidable

/-- Index of the first marker of chain `a` (`trace.length` when the trace has none). -/
noncomputable def stopIdx (T : Answers) (trace : List Entry) (a : ChainAddr) : Nat :=
  if h : ∃ k, Restart.MarkerAt T (trace.take k) a then Nat.find h else trace.length

/-- The trace up to the first marker of chain `a`. -/
noncomputable def preTrace (s : RefSample) (a : ChainAddr) : List Entry :=
  s.trace.take (stopIdx s.answers s.trace a)

/-- Chain-`a` prefix rows before the first marker of `a`. -/
noncomputable def preCount (a : ChainAddr) (s : RefSample) : Nat :=
  ((preTrace s a).filter fun e => decide (CanonicalRef.Normalized.PrefixRowAt s.answers a e.1)).length

/-- Some marker of chain `a` occurs in the trace. -/
def Marked (a : ChainAddr) (s : RefSample) : Prop := ∃ k, Restart.MarkerAt s.answers (s.trace.take k) a

/-- A contact of chain `a` before its first marker. -/
def PreContact (a : ChainAddr) (s : RefSample) : Prop :=
  ∃ k, CanonicalRef.ContactAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
    ¬CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) (s.trace.take k) a

/-- A two-edge of chain `a` before its first marker. -/
def PreTwoEdge (a : ChainAddr) (s : RefSample) : Prop :=
  ∃ k, CanonicalRef.TwoEdgeAt s.answers (sourceMessages s.answers) (s.trace.take k) a ∧
    ¬CanonicalRef.MarkerAt s.answers (sourceMessages s.answers) (s.trace.take k) a

/-- Source chains contacted before their first marker. -/
noncomputable def preContactCount (s : RefSample) : Nat :=
  (Contacts.sourceChains7.filter fun a => PreContact a s).card

theorem preTrace_prefix (s : RefSample) (a : ChainAddr) : preTrace s a <+: s.trace :=
  List.take_prefix _ _

theorem preCount_le_prefixCount (a : ChainAddr) (s : RefSample) : preCount a s ≤ CanonicalRef.Normalized.prefixCount a s := by
  unfold preCount CanonicalRef.Normalized.prefixCount
  exact (((preTrace_prefix s a).sublist).filter _).length_le

theorem preCount_of_not_marked (a : ChainAddr) (s : RefSample) (h : ¬Marked a s) :
    preCount a s = CanonicalRef.Normalized.prefixCount a s := by
  have h' : ¬∃ k, Restart.MarkerAt s.answers (s.trace.take k) a := h
  unfold preCount preTrace stopIdx CanonicalRef.Normalized.prefixCount
  rw [dif_neg h', List.take_length]

end ClaudeWCT.W9.T3.Security.Wots.Z5
