import SigGolfCandidate.OuterSecurityBridgeBase
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge
open ClaudeWCT.W9.T3M.Final
namespace OuterSecurityBridge
open SigGolfCandidate.T3 (keygen Cache Digest)
open SigGolfCandidate.Research.SharedForest (Signature)
open SigGolfCandidate.Research.SharedForest (sign)
open SigGolfCandidate.T3M (cacheB cacheDec toQ ofQ)
open SigGolfCandidate.T3M.Final (AW AHash hrealize allQ_hrealize)
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits OuterRuntime.runtimeSub SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
section
variable (I : Images) (A : Adversary (submission I).sizes) (sk : SecretKey) (pk : PublicKey)
def orgK (n : ℕ) (s : A.State) (T : Transcript (submission I).sizes) : OracleComp AW AttackResult :=
  relabelW ofQ ((submission I).interact A sk pk n s T)
variable {I A sk pk}
lemma orgK_zero (s : A.State) (T : Transcript (submission I).sizes) :
    orgK I A sk pk 0 s T = pure ⟨false, T.hashCalls⟩ := rfl
lemma orgK_hash {n : ℕ} {s : A.State} {T : Transcript (submission I).sizes} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    orgK I A sk pk (n + 1) s T =
      (AW.query (Sum.inr (ofQ y)) : OracleComp AW _) >>= fun a =>
        orgK I A sk pk n (resume a) { T with hashCalls := T.hashCalls + 1 } := by
  simp only [orgK, Submission.interact, h]
  rw [relabelW_bind]
  rfl
lemma orgK_sample {n : ℕ} {s : A.State} {T : Transcript (submission I).sizes} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    orgK I A sk pk (n + 1) s T =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        orgK I A sk pk n (resume a) T := by
  simp only [orgK, Submission.interact, h]
  rw [relabelW_bind]
  rfl
lemma orgK_step {n : ℕ} {s s' : A.State} {T : Transcript (submission I).sizes} (h : A.step s = .step s') :
    orgK I A sk pk (n + 1) s T = orgK I A sk pk n s' T := by
  simp only [orgK, Submission.interact, h]
lemma orgK_sign_ge {n : ℕ} {s : A.State} {T : Transcript (submission I).sizes}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : ¬ T.signingRequests < LIFETIME) :
    orgK I A sk pk (n + 1) s T = pure ⟨false, T.hashCalls⟩ := by
  simp only [orgK, Submission.interact, h, hk, if_false]
  rfl
lemma orgK_sign_lt (F : QFacts) (P : Pending I) {n : ℕ} {s : A.State} {T : Transcript (submission I).sizes}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : T.signingRequests < LIFETIME) :
    orgK I A sk pk (n + 1) s T =
      (liftM (SigGolfCandidate.Bridge.countCalls (hrealize sk (sign (cacheDec req.cache) req.message))) :
          OracleComp AW _) >>= fun p =>
        orgK I A sk pk n (resume (p.1.map sigBC))
          (recordVC T req.message (p.1.map sigBC) p.2) := by
  simp only [orgK, Submission.interact, h, hk, if_true, Submission.signingOracle, record_eq_recordVC]
  refine (relabelW_liftM_proj ((submission I).run .sign (sk, req.cache, req.message))
    (fun r => (r.value, r.hashCalls))
    (fun p => (submission I).interact A sk pk n (resume p.1) (recordVC T req.message p.1 p.2))
    _ (fun _ => rfl)).trans ?_
  rw [sign_eq P sk req.cache req.message]
  erw [relabel_map]
  rw [relabel_ofQ_countCalls _ (allQ_hrealize sk (F.good_sign _ _))]
  erw [liftM_map, bind_map_left]
lemma relabel_verify (F : QFacts) (P : Pending I) (m : Message) (w : Bytes (submission I).sizes.witness)
    (fresh : Bool) (calls : ℕ) :
    relabel ofQ (((submission I).run .verify (m, pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp HashSpec AttackResult)) =
      (fun p => (⟨p.1 && fresh, calls + p.2⟩ : AttackResult)) <$>
        SigGolfCandidate.Bridge.countCalls (hrealize 0 (verifyP m pk w)) := by
  have e : (((submission I).run .verify (m, pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp HashSpec AttackResult)) =
      (fun p => (⟨p.1.isSome && fresh, calls + p.2⟩ : AttackResult)) <$>
        ((fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w)) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]
    rfl
  rw [e, verify_eq P m pk w]
  erw [Functor.map_map, relabel_map]
  erw [relabel_ofQ_countCalls _ (allQ_hrealize 0 (F.good_verifyP m pk w))]
  refine congrArg (· <$> _) ?_
  funext a
  rcases a with ⟨b, c⟩
  cases b <;> rfl
lemma orgK_submit_witness (F : QFacts) (P : Pending I) {n : ℕ} {s : A.State}
    {T : Transcript (submission I).sizes} {m : Message} {w : Bytes (submission I).sizes.witness}
    (h : A.step s = .submit (.witness m w)) :
    orgK I A sk pk (n + 1) s T =
      (liftM ((fun p => (⟨p.1 && T.freshMessage m, T.hashCalls + p.2⟩ : AttackResult)) <$>
        SigGolfCandidate.Bridge.countCalls (hrealize 0 (verifyP m pk w))) : OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash]
  rw [← relabel_verify F P m w]
  rfl
lemma orgK_submit_signature (F : QFacts) (P : Pending I) {n : ℕ} {s : A.State}
    {T : Transcript (submission I).sizes} {m : Message} {σ : Bytes (submission I).sizes.signature}
    (h : A.step s = .submit (.signature m σ)) :
    orgK I A sk pk (n + 1) s T =
      (liftM (SigGolfCandidate.Bridge.countCalls (hrealize 0 (expandB m pk (sigDecC σ)))) : OracleComp AW _) >>=
        fun p =>
        match p.1 with
        | none => pure ⟨false, T.hashCalls + p.2⟩
        | some w =>
          (liftM ((fun q => (⟨q.1 && T.freshSignature m σ, T.hashCalls + p.2 + q.2⟩ :
              AttackResult)) <$> SigGolfCandidate.Bridge.countCalls (hrealize 0 (verifyP m pk w))) :
            OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash, Submission.checkForgery]
  have hE : relabel ofQ ((fun r => (r.value, r.hashCalls)) <$>
      (submission I).run .expand (m, pk, σ)) =
        SigGolfCandidate.Bridge.countCalls (hrealize 0 (expandB m pk (sigDecC σ))) := by
    erw [expand_eq P m pk σ]
    exact relabel_ofQ_countCalls _ (allQ_hrealize 0 (F.good_expandB _ _ _))
  refine (congrArg (fun X => (liftM (relabel ofQ X) : OracleComp AW AttackResult))
    (bind_eq_of_proj ((submission I).run .expand (m, pk, σ)) (fun r => (r.value, r.hashCalls))
      (fun (p : Option (Output (submission I).sizes .expand) × ℕ) =>
          (match p.1 with
          | none => pure ⟨false, T.hashCalls + p.2⟩
          | some witness => (do
              let verify ← (submission I).run .verify (m, pk, witness)
              pure ⟨verify.value.isSome && T.freshSignature m σ,
                T.hashCalls + p.2 + verify.hashCalls⟩) : OracleComp HashSpec AttackResult))
      _ (fun r => by rcases r with ⟨v, f, c, h, hc⟩; cases v <;> rfl))).trans ?_
  refine (congrArg liftM (relabel_bind ofQ _ _)).trans ?_
  refine (liftM_bind _ _).trans ?_
  rw [hE]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | w, c⟩
  · rfl
  · exact congrArg _ (relabel_verify F P m w _ _)
variable (I A)
noncomputable def orgGame (rounds : ℕ) : OracleComp AW AttackResult := do
  let sk ← (liftM sampleSecretKey : OracleComp AW _)
  let p ← (liftM (SigGolfCandidate.Bridge.countCalls (hrealize sk keygen)) : OracleComp AW _)
  orgK I A sk (p.1.1 : PublicKey) rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) { hashCalls := p.2 }
set_option maxRecDepth 100000 in
theorem securityExperiment_eq (F : QFacts) (P : Pending I) (rounds : ℕ) :
    (submission I).securityExperiment A rounds =
      (simulateQ (roImpl (List UInt8) (BitVec 256)) (orgGame I A rounds)).run' ∅ := by
  unfold Submission.securityExperiment withRandomness
  refine (run'_relabelW (R := BitVec 256) ofQ ofQ_injective _ ∅ ∅ (fun _ => rfl)).trans ?_
  refine congrArg (fun P => (simulateQ (roImpl (List UInt8) (BitVec 256)) P).run' ∅) ?_
  unfold orgGame
  rw [relabelW_bind, relabelW_liftM_unif]
  refine bind_congr fun sk => ?_
  refine (relabelW_liftM_proj ((submission I).run .keygen sk) (fun r => (r.value, r.hashCalls))
    (fun (p : Option (PublicKey × Bytes (submission I).sizes.cache) × ℕ) =>
      (match p.1 with
      | some (pk, cache) => (submission I).interact A sk pk rounds (A.initial pk cache) { hashCalls := p.2 }
      | none => pure ⟨false, p.2⟩ : OracleComp World AttackResult)) _ ?hK).trans ?_
  case hK =>
    intro r
    rcases r with ⟨v, f, c, h, hc⟩
    rcases v with _ | ⟨pk, cache⟩ <;> rfl
  rw [keygen_eq P sk]
  erw [relabel_map]
  rw [relabel_ofQ_countCalls _ (allQ_hrealize sk F.good_keygen)]
  refine (liftM_map_bind _ _ _).trans ?_
  refine bind_congr fun p => ?_
  rfl
end
end OuterSecurityBridge
