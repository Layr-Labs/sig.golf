import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsContacts
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsStructuralFinal
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsTwoEdge
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsEncodingMatch
import SigGolfCandidate.ClaudeWCT_W9_T3_Secc_WotsTransportCount
import SigGolfCandidate.T3_Secc_WotsClasses

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace SmallA
theorem hdrBlock_chainRowW (a : ChainAddr) (s : Nat) (v : Digest) :
    Extract.hdrBlock (chainRowW a s v) = bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
  WCT9.chainInputW_header _ _ _ _ _ _
theorem posOf_chainRow (a : ChainAddr) (s : Nat) (v : Digest) (htree : a.key.tree < 2 ^ 31)
    (hleaf : a.key.leaf < 4096) (hc : a.chain < 64) (hs : s < 7) :
    Extract.posOf (chainRowW a s v) = some (.chain a.key.lay a.key.tree a.key.leaf a.chain s) :=
  Extract.posOf_eq ⟨htree, hleaf, hc, hs⟩ (chainRowW_length a s v)
    (hdrBlock_chainRowW a s v)
/-- Pairing stage 1: no chain row of the current scheme (F or G) is a digest query (header block). -/
theorem chainRowW_ne_digest (a : ChainAddr) (s : Nat) (v : Digest) (rho : Digest) (m : Message) (c : BitVec 32) :
    chainRowW a s v ≠ pad64 (digestInput rho m c) := by
  intro h
  have hb := congrArg Extract.hdrBlock h
  rw [hdrBlock_chainRowW] at hb
  change _ = SigGolfCandidate.T3M.Extract.hdrBlock _ at hb
  rw [SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest] at hb
  exact chainHeader_ne_digestHeader _ _ _ _ _ _ (bytesLE_injective hb)
end SmallA
open SigGolfCandidate.T3.Security.Wots.SmallA (sourceChain_bounds)
open ClaudeWCT.W9.T3.Security.Wots.SmallA (chainRowW_ne_digest)
namespace SmallA
theorem chainRowW_ne_encRow (a : ChainAddr) (s : Nat) (v : Digest) (L : LeafAddr) (m : WCT9.LayerMsg)
    (c : BitVec 32) (pad : RowPad) : chainRowW a s v ≠ encRow L m c pad := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h1 : ClaudeWCT.W9.T3M.Extract.hdrBlock (chainRowW a s v) =
      bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) :=
    hdrBlock_chainRowW a s v
  rw [h1, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2.1 (pad.2.2 ^^^ 1)) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  have hm := congrArg tweakMarker (bytesLE_injective hb)
  unfold WCT9.rowTweakW at hm
  rw [append64_marker, hyperWord_marker] at hm
  have := chainHeader_firstByte a.key.lay a.key.tree a.key.leaf a.chain s
  unfold tweakMarker at hm
  omega
theorem encRow_ne_digest (L : LeafAddr) (m : WCT9.LayerMsg) (c : BitVec 32) (pad : RowPad) (rho : Digest)
    (m' : Message) (c' : BitVec 32) : encRow L m c pad ≠ pad64 (digestInput rho m' c') := by
  intro h
  have hb := congrArg ClaudeWCT.W9.T3M.Extract.hdrBlock h
  have h2 : ClaudeWCT.W9.T3M.Extract.hdrBlock (pad64 (digestInput rho m' c')) =
      bytesLE 16 (digestHeader c') :=
    SigGolfCandidate.T3.Security.Wots.SmallA.hdrBlock_digest rho m' c'
  rw [h2, show encRow L m c pad = pad64 (layerEncodingInputP L.lay L.tree L.leaf m c pad.1 pad.2.1 (pad.2.2 ^^^ 1)) from rfl,
    ClaudeWCT.W9.T3M.BC.hdrBlock_layerEncodingInputP] at hb
  have hm := congrArg tweakMarker (bytesLE_injective hb)
  unfold WCT9.rowTweakW at hm
  rw [append64_marker, hyperWord_marker, digestHeader_marker] at hm
  exact absurd hm (by decide)
end SmallA
theorem prefixRow_encodingRow_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ EncodingRow T input) := by
  rintro ⟨hP, hE⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, -, s, v, -, rfl⟩ := hP
    obtain ⟨L, m, c, pad, -, hx⟩ := hE
    exact SmallA.chainRowW_ne_encRow a s v L m c pad hx
  · exact hP
theorem prefixRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hP, rho, m, c, rfl⟩
  obtain ⟨a, -, s, v, -, hx⟩ := hP
  exact chainRowW_ne_digest a s v rho m c hx.symm
theorem encodingRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ OtherQuery T input) := by
  rintro ⟨hE, hO⟩
  rcases input with (n | x) | c
  · exact hE
  · obtain ⟨L, m, c, pad, -, rfl⟩ := hE
    obtain ⟨position, hpos, -⟩ := hO
    have hnone : Extract.posOf (encRow L m c pad) = none := Structural.posOf_layerEncodingP _ _ _ _ _ _ _ _
    rw [hnone] at hpos
    cases hpos
  · exact hE
theorem otherQuery_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(OtherQuery T input ∧ IsDigestQuery input) := by
  rintro ⟨hO, rho, m, c, rfl⟩
  obtain ⟨position, hpos, -⟩ := hO
  rw [Structural.posOf_digest] at hpos
  cases hpos
theorem prefixRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(PrefixRow T input ∧ OtherQuery T input) := by
  rintro ⟨hP, hO⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, ha, s, v, hs, rfl⟩ := hP
    obtain ⟨position, hpos, -, -, hcls⟩ := hO
    obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds ha
    have h7 := Mask.depth_le_seven T a
    have hrow := SmallA.posOf_chainRow a s v htree hleaf hc (by omega)
    rw [hrow] at hpos
    cases hpos
    change OtherChainRow T (chainRowW a s v) at hcls
    obtain ⟨a', s', hpos', hcase⟩ := hcls
    rw [hrow] at hpos'
    simp only [Option.some.injEq, Extract.Pos.chain.injEq] at hpos'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpos'
    have ha' : a' = a := by
      obtain ⟨⟨l, t, f⟩, i⟩ := a
      obtain ⟨⟨l', t', f'⟩, i'⟩ := a'
      simp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
    subst ha' h5
    rcases hcase with hpad | hge
    · exact hpad v rfl
    · omega
  · exact hP
theorem encodingRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hE, rho, m, c, rfl⟩
  obtain ⟨L, m', c', pad, -, hx⟩ := hE
  exact SmallA.encRow_ne_digest L m' c' pad rho m c hx.symm
theorem shortCongruent_encodingRow : ShortCongruent EncodingRow := by
  intro A T _ input
  rcases input with (n | x) | c <;> exact Iff.rfl
theorem shortCongruent_prefixRow : ShortCongruent PrefixRow := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [PrefixRow, PrefixRowAt, hdepth]
  · exact Iff.rfl
theorem shortCongruent_otherQuery : ShortCongruent OtherQuery := by
  intro A T hAT input
  have hdepth : depth A = depth T := funext (Ref.depth_short hAT)
  have hcls : ∀ x p, StructuralClass A x p ↔ StructuralClass T x p := by
    intro x p
    cases p <;> simp only [StructuralClass, OtherChainRow, hdepth]
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [OtherQuery, OtherInput, hcls]
  · exact Iff.rfl
noncomputable def refExpect (adversary : AdversaryP) (q : Nat) (f : RefSample → Nat) : ENNReal :=
  ∑' s, referenceExperiment adversary q s * (f s : ENNReal)
theorem reference_class_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    refExpect adversary q prefixClassCount + refExpect adversary q encodingCount + refExpect adversary q otherCount +
      SeccLaw.expectedCharge adversary q hq digestClass ≤ q :=
  reference_shared_budget adversary q hq PrefixRow EncodingRow OtherQuery digestClass shortCongruent_prefixRow
    shortCongruent_encodingRow shortCongruent_otherQuery prefixRow_encodingRow_disjoint prefixRow_otherQuery_disjoint
    encodingRow_otherQuery_disjoint (fun z input => prefixRow_digest_disjoint z.2 input)
    (fun z input => encodingRow_digest_disjoint z.2 input) (fun z input => otherQuery_digest_disjoint z.2 input)
end ClaudeWCT.W9.T3.Security.Wots

namespace ClaudeWCT.W9.T3.Security.Wots.PairedReference.Classes
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.Wots.SmallA (sourceChain_bounds)
open ClaudeWCT.W9.T3.Security.Wots.SmallA (chainRowW_ne_digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
theorem prefixRow_encodingRow_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ EncodingRow T input) := by
  rintro ⟨hP, hE⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, -, s, v, -, rfl⟩ := hP
    obtain ⟨L, m, c, pad, -, hx⟩ := hE
    exact SmallA.chainRowW_ne_encRow a s v L m c pad hx
  · exact hP
theorem prefixRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hP, rho, m, c, rfl⟩
  obtain ⟨a, -, s, v, -, hx⟩ := hP
  exact chainRowW_ne_digest a s v rho m c hx.symm
theorem encodingRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ OtherQuery T input) := by
  rintro ⟨hE, hO⟩
  rcases input with (n | x) | c
  · exact hE
  · obtain ⟨L, m, c, pad, -, rfl⟩ := hE
    obtain ⟨position, hpos, -⟩ := hO
    have hnone : Extract.posOf (encRow L m c pad) = none := Structural.posOf_layerEncodingP _ _ _ _ _ _ _ _
    rw [hnone] at hpos
    cases hpos
  · exact hE
theorem otherQuery_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(OtherQuery T input ∧ IsDigestQuery input) := by
  rintro ⟨hO, rho, m, c, rfl⟩
  obtain ⟨position, hpos, -⟩ := hO
  rw [Structural.posOf_digest] at hpos
  cases hpos
theorem prefixRow_otherQuery_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(CanonicalRef.Normalized.Contacts.PrefixRow T input ∧ OtherQuery T input) := by
  rintro ⟨hP, hO⟩
  rcases input with (n | x) | c
  · exact hP
  · obtain ⟨a, ha, s, v, hs, rfl⟩ := hP
    obtain ⟨position, hpos, -, -, hcls⟩ := hO
    have hlegacy : SigGolfCandidate.T3.Security.WotsExtract.SourceChain a := ⟨⟨ha.1.tree_lt,ha.1.2⟩,ha.2⟩
    obtain ⟨htree, hleaf, hc⟩ := sourceChain_bounds hlegacy
    have h7 := (CanonicalRef.depth_le T (CanonicalRef.sourceMessages T) a ha.2).trans
      (SigGolfCandidate.T3.Security.Wots.Mask.width_le _ _)
    have hrow := SmallA.posOf_chainRow a s v htree hleaf hc (by omega)
    rw [hrow] at hpos
    cases hpos
    change CanonicalRef.OtherChainRow T (CanonicalRef.sourceMessages T) (chainRowW a s v) at hcls
    obtain ⟨a', s', hpos', hcase⟩ := hcls
    rw [hrow] at hpos'
    simp only [Option.some.injEq, Extract.Pos.chain.injEq] at hpos'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpos'
    have ha' : a' = a := by
      obtain ⟨⟨l, t, f⟩, i⟩ := a
      obtain ⟨⟨l', t', f'⟩, i'⟩ := a'
      simp only at h1 h2 h3 h4
      subst h1 h2 h3 h4
      rfl
    subst ha' h5
    rcases hcase with hpad | hge
    · exact hpad v rfl
    · omega
  · exact hP
theorem encodingRow_digest_disjoint (T : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    ¬(EncodingRow T input ∧ IsDigestQuery input) := by
  rintro ⟨hE, rho, m, c, rfl⟩
  obtain ⟨L, m', c', pad, -, hx⟩ := hE
  exact SmallA.encRow_ne_digest L m' c' pad rho m c hx.symm
theorem shortCongruent_encodingRow : ShortCongruent EncodingRow := by
  intro A T _ input
  rcases input with (n | x) | c <;> exact Iff.rfl
theorem shortCongruent_prefixRow : ShortCongruent CanonicalRef.Normalized.Contacts.PrefixRow := by
  intro A T hAT input
  have hdepth : CanonicalRef.depth A (CanonicalRef.sourceMessages A) = CanonicalRef.depth T (CanonicalRef.sourceMessages T) := funext (CanonicalRef.depth_short hAT)
  rcases input with (n | x) | c
  · exact Iff.rfl
  · simp only [CanonicalRef.Normalized.Contacts.PrefixRow, CanonicalRef.Normalized.PrefixRowAt, hdepth]
  · exact Iff.rfl

def digestClass : PairedSeccLaw.SampleClass := fun _ input=>IsDigestQuery input
theorem sample_class_budget (q : Nat)
    (z : PairedOuter.PaddedGame.TraceResult × Answers) :
    PairedSeccLaw.sampleCharge (fun z input=>CanonicalRef.Normalized.Contacts.PrefixRow z.2 input) q z +
    PairedSeccLaw.sampleCharge (fun z input=>EncodingRow z.2 input) q z +
    PairedSeccLaw.sampleCharge (fun z input=>OtherQuery z.2 input) q z +
    PairedSeccLaw.sampleCharge digestClass q z ≤ q := by
  let A := CanonicalRef.Normalized.Contacts.PrefixRow z.2
  let B := EncodingRow z.2
  let C := OtherQuery z.2
  let D := IsDigestQuery
  have hab : ∀input,¬(A input ∧ B input) := prefixRow_encodingRow_disjoint z.2
  have hac : ∀input,¬(A input ∧ C input) := prefixRow_otherQuery_disjoint z.2
  have had : ∀input,¬(A input ∧ D input) := prefixRow_digest_disjoint z.2
  have hbc : ∀input,¬(B input ∧ C input) := encodingRow_otherQuery_disjoint z.2
  have hbd : ∀input,¬(B input ∧ D input) := encodingRow_digest_disjoint z.2
  have hcd : ∀input,¬(C input ∧ D input) := otherQuery_digest_disjoint z.2
  have h1 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or A B hab q (QueryRecorded.recordedTrace z.1).events
  have h2 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or (fun input=>A input ∨ B input) C
    (fun input h=>h.1.elim (fun ha=>hac input ⟨ha,h.2⟩) (fun hb=>hbc input ⟨hb,h.2⟩)) q
    (QueryRecorded.recordedTrace z.1).events
  have h3 := SigGolfCandidate.T3.Security.SeccLaw.classCharge_or (fun input=>(A input ∨ B input) ∨ C input) D
    (fun input h=>h.1.elim (fun h'=>h'.elim (fun ha=>had input ⟨ha,h.2⟩)
      (fun hb=>hbd input ⟨hb,h.2⟩)) (fun hc=>hcd input ⟨hc,h.2⟩)) q
    (QueryRecorded.recordedTrace z.1).events
  have hle := SigGolfCandidate.T3.Security.SeccLaw.classCharge_le (fun input=>((A input ∨ B input) ∨ C input) ∨ D input) q
    (QueryRecorded.recordedTrace z.1).events
  change SigGolfCandidate.T3.Security.SeccLaw.classCharge A q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge B q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge C q _ + SigGolfCandidate.T3.Security.SeccLaw.classCharge D q _ ≤ q
  omega

noncomputable def refExpect (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat)
    (f : RefSample → Nat) : ENNReal := ∑'s,referenceExperiment adversary q s*(f s : ENNReal)

theorem prefix_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>CanonicalRef.Normalized.Contacts.PrefixRow z.2 input) :=
  reference_count_le adversary q hq CanonicalRef.Normalized.Contacts.PrefixRow shortCongruent_prefixRow

theorem encoding_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q encodingCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>EncodingRow z.2 input) :=
  reference_count_le adversary q hq EncodingRow shortCongruent_encodingRow

theorem other_count_le (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q otherCount ≤ PairedSeccLaw.expectedCharge adversary q hq
      (fun z input=>OtherQuery z.2 input) :=
  reference_count_le adversary q hq OtherQuery otherQuery_short

theorem reference_class_budget (adversary : ClaudeWCT.W9.T3M.Final.Paired.AdversaryP) (q : Nat) (hq:q ≤ 2^127) :
    refExpect adversary q CanonicalRef.Normalized.Contacts.prefixClassCount+refExpect adversary q encodingCount+refExpect adversary q otherCount+
      PairedSeccLaw.expectedCharge adversary q hq digestClass ≤ q :=
  reference_shared_budget adversary q hq CanonicalRef.Normalized.Contacts.PrefixRow EncodingRow OtherQuery digestClass shortCongruent_prefixRow
    shortCongruent_encodingRow otherQuery_short prefixRow_encodingRow_disjoint prefixRow_otherQuery_disjoint
    encodingRow_otherQuery_disjoint (fun z input=>prefixRow_digest_disjoint z.2 input)
    (fun z input=>encodingRow_digest_disjoint z.2 input) (fun z input=>otherQuery_digest_disjoint z.2 input)

end ClaudeWCT.W9.T3.Security.Wots.PairedReference.Classes
