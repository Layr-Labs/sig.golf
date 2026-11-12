import SigGolfCandidate.OuterSecurityCodec
import SigGolfCandidate.OuterCompactCounts
import SigGolfCandidate.OuterKeygenRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterSecurityBridge
open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec keygen Cache Digest)
open SigGolfCandidate.Research.SharedForest (Signature)
open SigGolfCandidate.T3M (mrealize countBoth cacheB cacheDec isHash isPublic toQ)
open SigGolfCandidate.T3M.Final ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3M (Images)

abbrev submission (_ : Images) : Submission:=OuterImageValidity.sub
abbrev WBytes:=ClaudeWCT.W9.T3M.WBytes
abbrev sign:=OuterSigning.sign
abbrev sigBC:=OuterSecurityGame.signedWire
abbrev sigDecC:=OuterSecurityCodec.decode
abbrev verifyP:=ClaudeWCT.W9.T3M.Paired.verifyP
abbrev Requests:=OuterSecurityGame.Requests
abbrev ForgeryP:=OuterSecurityGame.Forgery
abbrev AdversaryP:=OuterSecurityGame.Adversary
abbrev signingOracle:=OuterSecurityGame.signingOracle
noncomputable abbrev checkForgeryP:=OuterSecurityGame.checkForgery
noncomputable abbrev gameP:=OuterSecurityGame.game
noncomputable abbrev realExperimentP:=OuterSecurityGame.experiment
abbrev SecurityP:=OuterSecurityGame.Secure

abbrev expandB:=OuterRawExpand.expandB

set_option allowUnsafeReducibility true in
attribute [local reducible] OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local irreducible] SigGolfCandidate.Legacy.Submission.run

structure Pending (_ : Images) : Prop where
  keygen_run_counts : ∀sk : SecretKey,
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> OuterImageValidity.sub.run .keygen sk=
      (fun p=>(some ((p.1.1 : PublicKey),cacheB p.1.2),p.2.1,p.2.2)) <$> countBoth (mrealize sk keygen)
  sign_refines : ∀(sk : SecretKey)(cache : Bytes 131072)(m : Message),
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> OuterImageValidity.sub.run .sign (sk,cache,m)=
      (fun p=>(p.1.map sigBC,p.2.1,p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m))
  verify_refines : ∀(m : Message)(pk : PublicKey)(w : Bytes 21756),
    (fun r=>(r.value,r.hashCalls)) <$> OuterImageValidity.sub.run .verify (m,pk,w)=
      (fun p=>(if p.1 then some () else none,p.2)) <$> SigGolfCandidate.T3M.countCalls (mrealize 0 (verifyP m pk w))

theorem pending (I : Images) : Pending I where
  keygen_run_counts:=OuterKeygenRun.counts
  sign_refines:=OuterSignRun.refines
  verify_refines:=OuterVerifyRun.refines

structure QueryFactsData
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 : Prop) : Prop where
  hashOnly_keygen : p0
  hashOnly_sign : p1
  hashOnly_expandB : p2
  hashOnly_verifyP : p3
  public_expandB : p4
  public_verifyP : p5
  good_keygen : p6
  good_sign : p7
  good_expandB : p8
  good_verifyP : p9
abbrev QFacts : Prop :=
  QueryFactsData
    (AllQueriesSatisfy keygen isHash)
    (∀ (c : Cache) (m : SigGolfCandidate.T3.Message), AllQueriesSatisfy (sign c m) isHash)
    (∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : Signature),
      AllQueriesSatisfy (expandB m pk σ) isHash)
    (∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes),
      AllQueriesSatisfy (verifyP m pk w) isHash)
    (∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : Signature),
      AllQueriesSatisfy (expandB m pk σ) isPublic)
    (∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes),
      AllQueriesSatisfy (verifyP m pk w) isPublic)
    (AllQueriesSatisfy keygen SigGolfCandidate.T3.Cost.GoodQuery)
    (∀ (c : Cache) (m : SigGolfCandidate.T3.Message),
      AllQueriesSatisfy (sign c m) SigGolfCandidate.T3.Cost.GoodQuery)
    (∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : Signature),
      AllQueriesSatisfy (expandB m pk σ) SigGolfCandidate.T3.Cost.GoodQuery)
    (∀ (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes),
      AllQueriesSatisfy (verifyP m pk w) SigGolfCandidate.T3.Cost.GoodQuery)

theorem qFacts : QFacts := by
  refine ⟨SigGolfCandidate.T3.SourceReplay.hashOnly_keygen,OuterHashOnly.sign,
    OuterRawExpand.hashOnly,?_,OuterRawExpand.publicOnly,
    ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP,SigGolfCandidate.T3M.goodQ_keygen,OuterGoodQueries.sign,
    OuterRawExpand.good,ClaudeWCT.W9.T3M.Paired.goodQ_verifyP⟩
  intro m pk w
  exact SigGolfCandidate.T3M.allQ_mono (ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP m pk w)
    (by rintro ((tag|input)|coord) h <;> first | exact h.elim | trivial)

section eqs
variable {I : Images}
theorem keygen_eq (P : Pending I) (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .keygen sk =
      (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2)) <$>
        SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize sk keygen)) := by
  have h := calls_of_counts (F := fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2))
    (P.keygen_run_counts sk)
  rw [mrealize_eq_relabel] at h
  exact h
set_option maxRecDepth 100000 in
theorem sign_eq (P : Pending I) (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .sign (sk, cache, m) =
      (fun p => (p.1.map sigBC, p.2)) <$>
        SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize sk (sign (cacheDec cache) m))) := by
  have h := calls_of_counts (F := Option.map sigBC) (P.sign_refines sk cache m)
  rw [mrealize_eq_relabel] at h
  exact h
theorem expand_eq (P : Pending I) (m : Message) (pk : PublicKey) (s : Bytes 5184) :
    (fun r=>(r.value,r.hashCalls)) <$> (submission I).run .expand (m,pk,s)=
      SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize 0 (expandB m pk (sigDecC s)))) := by
  have h:=calls_of_counts (F:=id) (OuterCompactCounts.expand m pk s)
  rw [mrealize_eq_relabel] at h
  have he : expandB m pk (sigDecC s)=OuterExpand.expandCompact m pk s := OuterRawExpand.expand_wire m pk s
  rw [he]
  have hi : (fun p : Option WBytes×Nat=>(id p.1,p.2))=id := by funext p;rfl
  simp only [hi,id_map] at h
  exact h
set_option maxRecDepth 100000 in
theorem verify_eq (P : Pending I) (m : Message) (pk : PublicKey) (w : Bytes 21756) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
      (fun p => (if p.1 then some () else none, p.2)) <$>
        SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize 0 (verifyP m pk w))) := by
  rw [P.verify_refines m pk w, SigGolfCandidate.T3M.Final.countCalls_eq, mrealize_eq_relabel]

end eqs
#print axioms pending
#print axioms qFacts
#print axioms expand_eq
end OuterSecurityBridge
