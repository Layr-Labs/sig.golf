import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge056
import SigGolfCandidate.Merge057

-- ==== merged from ClaudeWCT_W9_T3M_Final_BridgeAbs ====
section

section
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec keygen Cache Digest privateInput realize)
open ClaudeWCT.WCT9 (Signature)
open ClaudeWCT.WCT9.Rev3 (sign)
open SigGolfCandidate.T3M (mrealize countBoth cacheB cacheDec isHash isPublic toQ)
open SigGolfCandidate.T3M.Final (hrealize mrealize_eq_relabel hrealize_map)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
-- Keep the record generic so its kernel-generated eliminators do not reduce programs.
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

section eqs
variable {I : Images}
set_option maxRecDepth 100000 in
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
set_option maxRecDepth 100000 in
theorem expand_eq (P : Pending I) (m : Message) (pk : PublicKey) (s : Bytes 5310) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .expand (m, pk, s) =
      SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize 0 (expandB m pk (sigDecC s)))) := by
  have h := calls_of_counts
    (F := Option.map (fun x : SigGolfCandidate.T3.HashOutput × ClaudeWCT.WCT9.Witness => witEnc x.1 x.2))
    (P.expand_refines m pk s)
  rw [mrealize_eq_relabel] at h
  refine h.trans ?_
  rw [expandB, hrealize_map, relabel_map]
  unfold SigGolfCandidate.Bridge.countCalls
  rw [countFrom_map]
set_option maxRecDepth 100000 in
theorem verify_eq (P : Pending I) (m : Message) (pk : PublicKey) (w : Bytes 22012) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
      (fun p => (if p.1 then some () else none, p.2)) <$>
        SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize 0 (verifyP m pk w))) := by
  rw [P.verify_refines m pk w, SigGolfCandidate.T3M.Final.countCalls_eq, mrealize_eq_relabel]
end eqs
end ClaudeWCT.W9.T3M.Final
end
section
open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3 (keygen Cache Digest)
open ClaudeWCT.WCT9 (Signature)
open ClaudeWCT.WCT9.Rev3 (sign)
open SigGolfCandidate.T3M (cacheB cacheDec toQ ofQ)
open SigGolfCandidate.T3M.Final (AW AHash hrealize allQ_hrealize)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
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
  rfl
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
end ClaudeWCT.W9.T3M.Final
end
section
open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize)
open SigGolfCandidate.T3.Security (Request forwardWorld)
open ClaudeWCT.W9.T3.Security (Requests signingOracle)
open ClaudeWCT.WCT9 (Signature)
open ClaudeWCT.WCT9.Rev3 (sign)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open SigGolfCandidate.T3M (cacheB cacheDec toQ ofQ)
open SigGolfCandidate.T3M.Final (AW AHash hrealize realize_eq_liftM)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local instance] instDecidableEqSignature_securityP
abbrev SSpec := OracleWorld + Requests
variable (I : Images) (A : Adversary (submission I).sizes)
def advLoop : ℕ → A.State → ℕ → OracleComp SSpec (Option ForgeryP)
  | 0, _, _ => pure none
  | n + 1, s, k =>
    match A.step s with
    | .submit (.witness m w) => pure (some (.witness m w))
    | .submit (.signature m σ) => pure (some (.signature m (sigDecC σ)))
    | .hash y resume => do
        let a ← (liftM (SSpec.query (Sum.inl (Sum.inr (ofQ y)))) : OracleComp SSpec (BitVec 256))
        advLoop n (resume a) k
    | .sign req resume =>
        if k < LIFETIME then do
          let r ← (liftM (SSpec.query (Sum.inr ⟨req.message, cacheDec req.cache⟩)) :
            OracleComp SSpec (Option Signature))
          advLoop n (resume (r.map sigBC)) (k + 1)
        else pure none
    | .sample m resume => do
        let u ← (liftM (SSpec.query (Sum.inl (Sum.inl m))) : OracleComp SSpec (Fin (m + 1)))
        advLoop n (resume u) k
    | .step next => advLoop n next k
def reductionP (rounds : ℕ) : AdversaryP :=
  fun pk cache => advLoop I A rounds (A.initial (pk : PublicKey) (cacheB cache)) 0
noncomputable def srcImpl : QueryImpl SSpec (WriterT (QueryLog Requests) M) :=
  (fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
    signingOracle
noncomputable def runA {α : Type} (X : OracleComp SSpec α) : M (α × QueryLog Requests) :=
  (simulateQ srcImpl X).run
noncomputable def srcRest (pk : Digest) (X : OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    M Bool := do
  let (forgery, log) ← runA X
  let some forgery := forgery | return false
  let verified ← checkForgeryP pk (lg ++ log) forgery
  pure (decide ((lg ++ log).length ≤ 2^32) && verified)
theorem gameP_eq (adversary : AdversaryP) :
    gameP adversary = keygen >>= fun kp => srcRest kp.1 (adversary kp.1 kp.2) [] := by
  unfold gameP srcRest runA srcImpl
  rfl
noncomputable def absK (secret : SecretKey) (pk : Digest) (n : ℕ) (s : A.State) (k : ℕ)
    (lg : QueryLog Requests) (c : ℕ) : OracleComp AW (Bool × ℕ) :=
  countFrom costW (realize secret (srcRest pk (advLoop I A n s k) lg)) c
theorem runA_pure {α : Type} (x : α) : runA (pure x : OracleComp SSpec α) = pure (x, []) := rfl
theorem runA_inl_bind {α : Type} (t : OracleWorld.Domain) (f : OracleWorld.Range t → OracleComp SSpec α) :
    runA ((liftM (SSpec.query (Sum.inl t)) : OracleComp SSpec _) >>= f) =
      (forwardWorld t : M _) >>= fun a => runA (f a) := by
  simp only [runA, srcImpl, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
  have e : (((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) + signingOracle) (Sum.inl t)).run =
      (fun a => (a, [])) <$> (forwardWorld t : M _) := rfl
  rw [e, bind_map_left]
  simp
theorem runA_inr_bind {α : Type} (req : Request) (f : Option Signature → OracleComp SSpec α) :
    runA ((liftM (SSpec.query (Sum.inr req)) : OracleComp SSpec _) >>= f) =
      (sign req.cache req.message : M _) >>= fun u =>
        (fun p => (p.1, [⟨req, u⟩] ++ p.2)) <$> runA (f u) := by
  simp [runA, srcImpl, signingOracle, WriterT.run_bind]
theorem srcRest_inl_bind (pk : Digest) (t : OracleWorld.Domain)
    (f : OracleWorld.Range t → OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    srcRest pk ((liftM (SSpec.query (Sum.inl t)) : OracleComp SSpec _) >>= f) lg =
      (forwardWorld t : M _) >>= fun a => srcRest pk (f a) lg := by
  unfold srcRest
  rw [runA_inl_bind, bind_assoc]
theorem srcRest_inr_bind (pk : Digest) (req : Request)
    (f : Option Signature → OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    srcRest pk ((liftM (SSpec.query (Sum.inr req)) : OracleComp SSpec _) >>= f) lg =
      (sign req.cache req.message : M _) >>= fun u => srcRest pk (f u) (lg ++ [⟨req, u⟩]) := by
  unfold srcRest
  rw [runA_inr_bind, bind_assoc]
  refine bind_congr fun u => ?_
  rw [bind_map_left]
  simp only [List.append_assoc]
theorem srcRest_none (pk : Digest) (lg : QueryLog Requests) :
    srcRest pk (pure none) lg = pure false := rfl
theorem srcRest_some (pk : Digest) (f : ForgeryP) (lg : QueryLog Requests) :
    srcRest pk (pure (some f)) lg =
      checkForgeryP pk lg f >>= fun v => pure (decide (lg.length ≤ 2^32) && v) := by
  unfold srcRest
  rw [runA_pure, pure_bind]
  simp only [List.append_nil]
noncomputable def freshW (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) : Bool := by
  classical
  exact decide (¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.isSome = true)
noncomputable def freshS (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) (σ : Signature) : Bool := by
  classical
  exact decide (¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.map ClaudeWCT.WCT9.proj = some (ClaudeWCT.WCT9.proj σ))
theorem freshW_iff (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) :
    freshW log m = true ↔ ¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.isSome = true := by
  classical
  unfold freshW; exact decide_eq_true_iff
theorem freshS_iff (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) (σ : Signature) :
    freshS log m σ = true ↔
      ¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.map ClaudeWCT.WCT9.proj = some (ClaudeWCT.WCT9.proj σ) := by
  classical
  unfold freshS; exact decide_eq_true_iff
theorem checkForgeryP_witness (pk : Digest) (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message)
    (wb : WBytes) :
    checkForgeryP pk log (.witness m wb) = verifyP m pk wb >>= fun v => pure (freshW log m && v) := rfl
theorem checkForgeryP_signature (pk : Digest) (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message)
    (σ : Signature) :
    checkForgeryP pk log (.signature m σ) = (do
      let wb ← expandB m pk σ
      let some wb := wb | return false
      let verified ← verifyP m pk wb
      pure (freshS log m σ && verified)) := rfl
variable {I A}
set_option maxRecDepth 100000 in
theorem src_top (F : QFacts) (secret : SecretKey) (rounds : ℕ) :
    countFrom costW (realize secret (gameP (reductionP I A rounds))) 0 =
      (liftM (countFrom (fun _ => 1) (hrealize secret keygen) 0) : OracleComp AW _) >>= fun p =>
        absK I A secret p.1.1 rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) 0 [] p.2 := by
  rw [gameP_eq, SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret F.hashOnly_keygen, countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl)]
  rfl
theorem absK_zero (secret : SecretKey) (pk : Digest) (s : A.State) (k : ℕ) (lg : QueryLog Requests) (c : ℕ) :
    absK I A secret pk 0 s k lg c = pure (false, c) := rfl
variable {secret : SecretKey} {pk : Digest}
theorem absK_hash {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    absK I A secret pk (n + 1) s k lg c =
      (AW.query (Sum.inr (ofQ y)) : OracleComp AW _) >>= fun a =>
        absK I A secret pk n (resume a) k lg (c + 1) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_inl_bind, realize_forward_bind, countFrom_query_bind]
  rfl
theorem absK_sample {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    absK I A secret pk (n + 1) s k lg c =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        absK I A secret pk n (resume a) k lg c := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_inl_bind, realize_forward_bind, countFrom_query_bind]
  rfl
theorem absK_step {n : ℕ} {s s' : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (h : A.step s = .step s') :
    absK I A secret pk (n + 1) s k lg c = absK I A secret pk n s' k lg c := by
  unfold absK
  simp only [advLoop, h]
theorem absK_sign_ge {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : ¬ k < LIFETIME) :
    absK I A secret pk (n + 1) s k lg c = pure (false, c) := by
  unfold absK
  simp only [advLoop, h, hk, if_false]
  rfl
theorem absK_sign_lt (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : k < LIFETIME) :
    absK I A secret pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (hrealize secret (sign (cacheDec req.cache) req.message)) c) :
          OracleComp AW _) >>= fun p =>
        absK I A secret pk n (resume (p.1.map sigBC)) (k + 1)
          (lg ++ [⟨⟨req.message, cacheDec req.cache⟩, p.1⟩]) p.2 := by
  unfold absK
  simp only [advLoop, h, hk, if_true]
  rw [srcRest_inr_bind, SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_sign _ _),
    countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
theorem absK_submit_witness (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {m : Message} {w : Bytes (submission I).sizes.witness} (h : A.step s = .submit (.witness m w)) :
    absK I A secret pk (n + 1) s k lg c =
      (fun p => (decide (lg.length ≤ 2^32) && (freshW lg m && p.1), p.2)) <$>
        (liftM (countFrom (fun _ => 1) (hrealize secret (verifyP m pk w)) c) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_some, checkForgeryP_witness, bind_assoc]
  simp only [pure_bind]
  rw [SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_verifyP _ _ _), countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl), map_eq_bind_pure_comp]
  rfl
theorem absK_submit_signature (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {m : Message} {σ : Bytes (submission I).sizes.signature} (h : A.step s = .submit (.signature m σ)) :
    absK I A secret pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (hrealize secret (expandB m pk (sigDecC σ))) c) : OracleComp AW _) >>=
        fun p =>
          match p.1 with
          | none => pure (decide (lg.length ≤ 2^32) && false, p.2)
          | some wb => (fun q => (decide (lg.length ≤ 2^32) && (freshS lg m (sigDecC σ) && q.1), q.2)) <$>
              (liftM (countFrom (fun _ => 1) (hrealize secret (verifyP m pk wb)) p.2) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_some, checkForgeryP_signature, bind_assoc, SigGolfCandidate.T3.Cost.realize_bind,
    realize_eq_liftM secret (F.hashOnly_expandB _ _ _), countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | wb, e⟩
  · rfl
  · simp only [bind_assoc, pure_bind]
    rw [SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_verifyP _ _ _), countFrom_bind,
      countFrom_liftM_hash _ (fun _ => rfl), map_eq_bind_pure_comp]
    rfl
end ClaudeWCT.W9.T3M.Final
end

section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section
namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.Legacy OracleComp OracleSpec SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec keygen Cache Digest privateInput realize)
open SigGolfCandidate.Research.SharedForest (Signature)
open SigGolfCandidate.Research.SharedForest (sign)
open SigGolfCandidate.T3M (mrealize countBoth cacheB cacheDec isHash isPublic toQ)
open SigGolfCandidate.T3M.Final (hrealize mrealize_eq_relabel hrealize_map)
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
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

theorem qFacts (F : SourceQueries) : QFacts := by
  refine ⟨SigGolfCandidate.T3.SourceReplay.hashOnly_keygen, ?_, F.hashOnly_expandB,
    F.hashOnly_verifyP, F.public_expandB, F.public_verifyP,
    SigGolfCandidate.T3M.goodQ_keygen, F.good_sign, ?_, F.good_verifyP⟩
  · intro cache message
    unfold SigGolfCandidate.Research.SharedForest.sign
    apply SigGolfCandidate.T3.SourceReplay.hashOnly_bind
      (SigGolfCandidate.T3.SourceReplay.hashOnly_privateMac _)
    intro tag
    split
    · exact SigGolfCandidate.T3.SourceReplay.hashOnly_pure _
    · exact ClaudeWCT.W9.T3.Security.Wots.PairedReference.Ref.shared_signPayload_hashOnly cache message
  · intro message pk sig
    exact SigGolfCandidate.T3M.allQ_map _ (F.good_expandN message pk sig)

section eqs
variable {I : Images}
set_option maxRecDepth 100000 in
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
set_option maxRecDepth 100000 in
theorem expand_eq (P : Pending I) (m : Message) (pk : PublicKey) (s : Bytes 5195) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .expand (m, pk, s) =
      SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize 0 (expandB m pk (sigDecC s)))) := by
  have h := calls_of_counts
    (F := Option.map (fun x : SigGolfCandidate.T3.HashOutput × SigGolfCandidate.Research.SharedForest.Witness => ClaudeWCT.W9.T3M.Paired.witEncN x.1 x.2))
    (P.expand_refines m pk s)
  rw [mrealize_eq_relabel] at h
  refine h.trans ?_
  rw [expandB, ClaudeWCT.W9.T3M.Paired.expandB, hrealize_map, relabel_map]
  unfold SigGolfCandidate.Bridge.countCalls
  rw [countFrom_map]
set_option maxRecDepth 100000 in
theorem verify_eq (P : Pending I) (m : Message) (pk : PublicKey) (w : Bytes 22012) :
    (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
      (fun p => (if p.1 then some () else none, p.2)) <$>
        SigGolfCandidate.Bridge.countCalls (relabel toQ (hrealize 0 (verifyP m pk w))) := by
  rw [P.verify_refines m pk w, SigGolfCandidate.T3M.Final.countCalls_eq, mrealize_eq_relabel]
end eqs
end ClaudeWCT.W9.T3M.Final.Paired
end
section
open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge
namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3 (keygen Cache Digest)
open SigGolfCandidate.Research.SharedForest (Signature)
open SigGolfCandidate.Research.SharedForest (sign)
open SigGolfCandidate.T3M (cacheB cacheDec toQ ofQ)
open SigGolfCandidate.T3M.Final (AW AHash hrealize allQ_hrealize)
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
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
end ClaudeWCT.W9.T3M.Final.Paired
end
section
open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge
namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize)
open SigGolfCandidate.T3.Security (Request forwardWorld)

open SigGolfCandidate.Research.SharedForest (Signature)
open SigGolfCandidate.Research.SharedForest (sign)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open SigGolfCandidate.T3M (cacheB cacheDec toQ ofQ)
open SigGolfCandidate.T3M.Final (AW AHash hrealize realize_eq_liftM)
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.Paired.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.Research.SharedForest.sign

abbrev SSpec := OracleWorld + Requests
variable (I : Images) (A : Adversary (submission I).sizes)
def advLoop : ℕ → A.State → ℕ → OracleComp SSpec (Option ForgeryP)
  | 0, _, _ => pure none
  | n + 1, s, k =>
    match A.step s with
    | .submit (.witness m w) => pure (some (.witness m w))
    | .submit (.signature m σ) => pure (some (.signature m (sigDecC σ)))
    | .hash y resume => do
        let a ← (liftM (SSpec.query (Sum.inl (Sum.inr (ofQ y)))) : OracleComp SSpec (BitVec 256))
        advLoop n (resume a) k
    | .sign req resume =>
        if k < LIFETIME then do
          let r ← (liftM (SSpec.query (Sum.inr ⟨req.message, cacheDec req.cache⟩)) :
            OracleComp SSpec (Option Signature))
          advLoop n (resume (r.map sigBC)) (k + 1)
        else pure none
    | .sample m resume => do
        let u ← (liftM (SSpec.query (Sum.inl (Sum.inl m))) : OracleComp SSpec (Fin (m + 1)))
        advLoop n (resume u) k
    | .step next => advLoop n next k
def reductionP (rounds : ℕ) : AdversaryP :=
  fun pk cache => advLoop I A rounds (A.initial (pk : PublicKey) (cacheB cache)) 0
noncomputable def srcImpl : QueryImpl SSpec (WriterT (QueryLog Requests) M) :=
  (fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
    signingOracle
private noncomputable def runAWith (handler : QueryImpl Requests M) {α : Type}
    (X : OracleComp SSpec α) : M (α × QueryLog Requests) :=
  (simulateQ ((fun input => liftM (forwardWorld input) :
    QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
    QueryImpl.withLogging handler) X).run
private theorem runAWith_inr (handler : QueryImpl Requests M) {α : Type}
    (req : Request) (f : Option Signature → OracleComp SSpec α) :
    runAWith handler ((SSpec.query (.inr req)) >>= f) =
      handler req >>= fun u => (fun p => (p.1,[⟨req,u⟩] ++ p.2)) <$> runAWith handler (f u) := by
  simp [runAWith, QueryImpl.withLogging, WriterT.run_bind]

noncomputable def runA {α : Type} (X : OracleComp SSpec α) : M (α × QueryLog Requests) :=
  runAWith (fun request => sign request.cache request.message) X
noncomputable def srcRest (pk : Digest) (X : OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    M Bool := do
  let (forgery, log) ← runA X
  let some forgery := forgery | return false
  let verified ← checkForgeryP pk (lg ++ log) forgery
  pure (decide ((lg ++ log).length ≤ 2^32) && verified)
theorem gameP_eq (adversary : AdversaryP) :
    gameP adversary = keygen >>= fun kp => srcRest kp.1 (adversary kp.1 kp.2) [] := by
  unfold gameP srcRest runA runAWith
  rfl
noncomputable def absK (secret : SecretKey) (pk : Digest) (n : ℕ) (s : A.State) (k : ℕ)
    (lg : QueryLog Requests) (c : ℕ) : OracleComp AW (Bool × ℕ) :=
  countFrom costW (realize secret (srcRest pk (advLoop I A n s k) lg)) c
theorem runA_pure {α : Type} (x : α) : runA (pure x : OracleComp SSpec α) = pure (x, []) := rfl
theorem runA_inl_bind {α : Type} (t : OracleWorld.Domain) (f : OracleWorld.Range t → OracleComp SSpec α) :
    runA ((liftM (SSpec.query (Sum.inl t)) : OracleComp SSpec _) >>= f) =
      (forwardWorld t : M _) >>= fun a => runA (f a) := by
  simp only [runA, runAWith, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
  have e : (((fun input => liftM (forwardWorld input) :
      QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
      (QueryImpl.withLogging (fun (request : Request) => sign request.cache request.message) :
        QueryImpl Requests (WriterT (QueryLog Requests) M))) (Sum.inl t)).run =
      (fun a => (a, [])) <$> (forwardWorld t : M _) := rfl
  rw [e, bind_map_left]
  simp
theorem runA_inr_bind {α : Type} (req : Request) (f : Option Signature → OracleComp SSpec α) :
    runA ((liftM (SSpec.query (Sum.inr req)) : OracleComp SSpec _) >>= f) =
      (sign req.cache req.message : M _) >>= fun u =>
        (fun p => (p.1, [⟨req, u⟩] ++ p.2)) <$> runA (f u) :=
  runAWith_inr (fun request => sign request.cache request.message) req f
theorem srcRest_inl_bind (pk : Digest) (t : OracleWorld.Domain)
    (f : OracleWorld.Range t → OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    srcRest pk ((liftM (SSpec.query (Sum.inl t)) : OracleComp SSpec _) >>= f) lg =
      (forwardWorld t : M _) >>= fun a => srcRest pk (f a) lg := by
  unfold srcRest
  rw [runA_inl_bind, bind_assoc]
theorem srcRest_inr_bind (pk : Digest) (req : Request)
    (f : Option Signature → OracleComp SSpec (Option ForgeryP)) (lg : QueryLog Requests) :
    srcRest pk ((liftM (SSpec.query (Sum.inr req)) : OracleComp SSpec _) >>= f) lg =
      (sign req.cache req.message : M _) >>= fun u => srcRest pk (f u) (lg ++ [⟨req, u⟩]) := by
  unfold srcRest
  rw [runA_inr_bind, bind_assoc]
  refine bind_congr fun u => ?_
  rw [bind_map_left]
  simp only [List.append_assoc]
theorem srcRest_none (pk : Digest) (lg : QueryLog Requests) :
    srcRest pk (pure none) lg = pure false := rfl
theorem srcRest_some (pk : Digest) (f : ForgeryP) (lg : QueryLog Requests) :
    srcRest pk (pure (some f)) lg =
      checkForgeryP pk lg f >>= fun v => pure (decide (lg.length ≤ 2^32) && v) := by
  unfold srcRest
  rw [runA_pure, pure_bind]
  simp only [List.append_nil]
noncomputable def freshW (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) : Bool := by
  classical
  exact decide (¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.isSome = true)
noncomputable def freshS (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) (σ : Signature) : Bool := by
  classical
  exact decide (¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.map sigBC = some (sigBC σ))
theorem freshW_iff (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) :
    freshW log m = true ↔ ¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.isSome = true := by
  classical
  unfold freshW; exact decide_eq_true_iff
theorem freshS_iff (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message) (σ : Signature) :
    freshS log m σ = true ↔
      ¬∃ entry ∈ log, entry.1.message = m ∧ entry.2.map sigBC = some (sigBC σ) := by
  classical
  unfold freshS; exact decide_eq_true_iff
theorem checkForgeryP_witness (pk : Digest) (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message)
    (wb : WBytes) :
    checkForgeryP pk log (.witness m wb) = verifyP m pk wb >>= fun v => pure (freshW log m && v) := rfl
theorem checkForgeryP_signature (pk : Digest) (log : QueryLog Requests) (m : SigGolfCandidate.T3.Message)
    (σ : Signature) :
    checkForgeryP pk log (.signature m σ) = (do
      let wb ← expandB m pk σ
      let some wb := wb | return false
      let verified ← verifyP m pk wb
      pure (freshS log m σ && verified)) := rfl
variable {I A}
set_option maxRecDepth 100000 in
theorem src_top (F : QFacts) (secret : SecretKey) (rounds : ℕ) :
    countFrom costW (realize secret (gameP (reductionP I A rounds))) 0 =
      (liftM (countFrom (fun _ => 1) (hrealize secret keygen) 0) : OracleComp AW _) >>= fun p =>
        absK I A secret p.1.1 rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) 0 [] p.2 := by
  rw [gameP_eq, SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret F.hashOnly_keygen, countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl)]
  rfl
theorem absK_zero (secret : SecretKey) (pk : Digest) (s : A.State) (k : ℕ) (lg : QueryLog Requests) (c : ℕ) :
    absK I A secret pk 0 s k lg c = pure (false, c) := rfl
variable {secret : SecretKey} {pk : Digest}
theorem absK_hash {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    absK I A secret pk (n + 1) s k lg c =
      (AW.query (Sum.inr (ofQ y)) : OracleComp AW _) >>= fun a =>
        absK I A secret pk n (resume a) k lg (c + 1) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_inl_bind, realize_forward_bind, countFrom_query_bind]
  rfl
theorem absK_sample {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    absK I A secret pk (n + 1) s k lg c =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        absK I A secret pk n (resume a) k lg c := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_inl_bind, realize_forward_bind, countFrom_query_bind]
  rfl
theorem absK_step {n : ℕ} {s s' : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (h : A.step s = .step s') :
    absK I A secret pk (n + 1) s k lg c = absK I A secret pk n s' k lg c := by
  unfold absK
  simp only [advLoop, h]
theorem absK_sign_ge {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : ¬ k < LIFETIME) :
    absK I A secret pk (n + 1) s k lg c = pure (false, c) := by
  unfold absK
  simp only [advLoop, h, hk, if_false]
  rfl
theorem absK_sign_lt (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {req : SigningRequest (submission I).sizes}
    {resume : Option (Bytes (submission I).sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : k < LIFETIME) :
    absK I A secret pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (hrealize secret (sign (cacheDec req.cache) req.message)) c) :
          OracleComp AW _) >>= fun p =>
        absK I A secret pk n (resume (p.1.map sigBC)) (k + 1)
          (lg ++ [⟨⟨req.message, cacheDec req.cache⟩, p.1⟩]) p.2 := by
  unfold absK
  simp only [advLoop, h, hk, if_true]
  rw [srcRest_inr_bind, SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_sign _ _),
    countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
theorem absK_submit_witness (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {m : Message} {w : Bytes (submission I).sizes.witness} (h : A.step s = .submit (.witness m w)) :
    absK I A secret pk (n + 1) s k lg c =
      (fun p => (decide (lg.length ≤ 2^32) && (freshW lg m && p.1), p.2)) <$>
        (liftM (countFrom (fun _ => 1) (hrealize secret (verifyP m pk w)) c) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_some, checkForgeryP_witness, bind_assoc]
  simp only [pure_bind]
  rw [SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_verifyP _ _ _), countFrom_bind,
    countFrom_liftM_hash _ (fun _ => rfl), map_eq_bind_pure_comp]
  rfl
theorem absK_submit_signature (F : QFacts) {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    {m : Message} {σ : Bytes (submission I).sizes.signature} (h : A.step s = .submit (.signature m σ)) :
    absK I A secret pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (hrealize secret (expandB m pk (sigDecC σ))) c) : OracleComp AW _) >>=
        fun p =>
          match p.1 with
          | none => pure (decide (lg.length ≤ 2^32) && false, p.2)
          | some wb => (fun q => (decide (lg.length ≤ 2^32) && (freshS lg m (sigDecC σ) && q.1), q.2)) <$>
              (liftM (countFrom (fun _ => 1) (hrealize secret (verifyP m pk wb)) p.2) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [srcRest_some, checkForgeryP_signature, bind_assoc, SigGolfCandidate.T3.Cost.realize_bind,
    realize_eq_liftM secret (F.hashOnly_expandB _ _ _), countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | wb, e⟩
  · rfl
  · simp only [bind_assoc, pure_bind]
    rw [SigGolfCandidate.T3.Cost.realize_bind, realize_eq_liftM secret (F.hashOnly_verifyP _ _ _), countFrom_bind,
      countFrom_liftM_hash _ (fun _ => rfl), map_eq_bind_pure_comp]
    rfl
end ClaudeWCT.W9.T3M.Final.Paired
end


end
end
-- ==== merged from ClaudeWCT_W9_T3M_Witness_HonestN ====
section

/-! # Honest acceptance of the nonce-carrying expand output (`Paired.witEncN`, r3h HonestN)
img-v6: the scheme verifier reads the top node nonces (`verifyTopN w.topNonces`), so the honest expand output is
`witEncN` (nonce pads filled). Main results: `Paired.layersCanonicalBC_witEncN` (retained layer program on
`witEncN` = the scheme's `verifyLayers`), `W9Drv.SharedCanonical.forest_witEncN`, and the read-backs
`Paired.wrho_witEncN` / `wdc_witEncN` / `wtopHigh_witEncN`. -/

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem expandN_fillTopSignature (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (c : Nat) :
    expandN message pk (fillTopSignature sig c)=expandN message pk sig := by
  simp only [expandN,hints_retained,fillTopSignature_fillTopSignature]

theorem expandB_fillTopSignature (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (c : Nat) :
    expandB message pk (fillTopSignature sig c)=expandB message pk sig := by
  rw [expandB,expandB,expandN_fillTopSignature]
end ClaudeWCT.W9.T3M.Paired

/-! The read-back lemmas of the top node nonces (`PairedNonce.noncePos_*`, `witEncN_extract_*`, `wmerklePad_witEncN_*`)
live in `Witness/Honest.lean` (needed there by `Paired.expandN_nonce`). -/


/-! ### HonestN 1: bit-level agreement of `witEncN` with `witEnc` away from the nonce words -/
namespace ClaudeWCT.W9.T3M.PairedNonce
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem witEncN_getLsbD_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (i : Nat)
    (h : ∀ j, j < 11 → i / 8 < noncePos output j ∨ noncePos output j + 8 ≤ i / 8) :
    (witEncN output w).getLsbD i = (Paired.witEnc output w).getLsbD i := by
  by_cases hlt : i < 8 * 22012
  · have e : ∀ x : WBytes, x.getLsbD i = (x.extractLsb' (8 * (i / 8)) (8 * 1)).getLsbD (i % 8) := by
      intro x
      rw [BitVec.getLsbD_extractLsb']
      simp [show i % 8 < 8 * 1 by omega, show 8 * (i / 8) + i % 8 = i by omega]
    rw [e (witEncN output w), e (Paired.witEnc output w), witEncN_extract_free output w (i / 8) 1 (by omega) (by
      intro i' hi1 hi2 j hj
      have := h j hj
      omega)]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]

/-- Any window `[off, off + k)` avoiding the 11 nonce words reads the same in `witEncN` and `witEnc`. -/
theorem extract_witEncN_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k m : Nat) (hm : m ≤ 8 * k)
    (h : ∀ j, j < 11 → off + k ≤ noncePos output j ∨ noncePos output j + 8 ≤ off) :
    (witEncN output w).extractLsb' (8 * off) m = (Paired.witEnc output w).extractLsb' (8 * off) m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  simp only [hi, decide_true, Bool.true_and]
  apply witEncN_getLsbD_free
  intro j hj
  have := h j hj
  omega

theorem extract_witEncN_out (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off k m : Nat) (hm : m ≤ 8 * k) (h : off + k ≤ 7696 ∨ 8320 ≤ off) :
    (witEncN output w).extractLsb' (8 * off) m = (Paired.witEnc output w).extractLsb' (8 * off) m := by
  apply extract_witEncN_free output w off k m hm
  intro j hj
  have := noncePos_bounds output j hj
  omega

theorem wdig_witEncN_out (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (h : off + 16 ≤ 7696 ∨ 8320 ≤ off) :
    wdig (witEncN output w) off = wdig (Paired.witEnc output w) off :=
  extract_witEncN_out output w off 16 128 (by omega) h

theorem wdig_witEncN_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (h : ∀ j, j < 11 → off + 16 ≤ noncePos output j ∨ noncePos output j + 8 ≤ off) :
    wdig (witEncN output w) off = wdig (Paired.witEnc output w) off :=
  extract_witEncN_free output w off 16 128 (by omega) h

theorem wdig_witEnc_legacy (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (ho : 7664 ≤ off) (hc : off + 16 ≤ choiceOff ∨ choiceOff < off) :
    wdig (Paired.witEnc output w) off = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) off := by
  rw [PairedReadout.wdig_witEnc_base output w off hc]
  exact PairedReadout.wdig_prefixEnc (forestBytes output w) (forestBytes_length output w)
    output (mainWitness w) off ho

theorem wdig_N_legacy_free (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (ho : 7664 ≤ off) (hc : off + 16 ≤ choiceOff ∨ choiceOff < off)
    (h : ∀ j, j < 11 → off + 16 ≤ noncePos output j ∨ noncePos output j + 8 ≤ off) :
    wdig (witEncN output w) off = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) off := by
  rw [wdig_witEncN_free output w off h, wdig_witEnc_legacy output w off ho hc]

theorem wdig_N_legacy_hi (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (ho : 8320 ≤ off) (hc : off + 16 ≤ choiceOff ∨ choiceOff < off) :
    wdig (witEncN output w) off = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) off := by
  rw [wdig_witEncN_out output w off (Or.inr ho), wdig_witEnc_legacy output w off (by omega) hc]
end ClaudeWCT.W9.T3M.PairedNonce

/-! ### HonestN 2: read-backs outside the nonce area -/
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.PairedNonce
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

@[simp] theorem wtopHigh_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wtopHigh (witEncN output w) = w.topHigh := by
  rw [← PairedReadout.wtopHigh_witEnc output w]
  unfold wtopHigh wchoice
  rw [extract_witEncN_out output w choiceOff 1 8 (by omega) (Or.inr (by unfold choiceOff; omega))]
end ClaudeWCT.W9.T3M.Paired

/-! ### HonestN 3: the top path windows avoid the nonce words
Slots of one leaf's top plan: a level-`j` window occupies slots `s_j .. s_j + 3` (`left | tweak | Z pad | right`);
the nonce of level `j'` is the low half of slot `s_j' + 2`. Only the level-`j` Z pad (`j < 11`) meets a nonce. -/
namespace ClaudeWCT.W9.T3M.PairedNonce
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem topPlanA_free0 : ∀ r, r < 64 → ∀ j, j < 6 → ∀ j', j' < 6 →
    (topPlanA.getD r []).getD j 0 ≠ (topPlanA.getD r []).getD j' 0 + 2 := by decide
theorem topPlanA_free1 : ∀ r, r < 64 → ∀ j, j < 6 → ∀ j', j' < 6 →
    (topPlanA.getD r []).getD j 0 + 1 ≠ (topPlanA.getD r []).getD j' 0 + 2 := by decide
theorem topPlanA_free3 : ∀ r, r < 64 → ∀ j, j < 6 → ∀ j', j' < 6 →
    (topPlanA.getD r []).getD j 0 + 3 ≠ (topPlanA.getD r []).getD j' 0 + 2 := by decide
theorem topPlanB_free0 : ∀ r, r < 64 → ∀ k, k < 6 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 ≠ (topPlanB.getD r []).getD k' 0 + 2 := by decide
theorem topPlanB_free1 : ∀ r, r < 64 → ∀ k, k < 6 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 + 1 ≠ (topPlanB.getD r []).getD k' 0 + 2 := by decide
theorem topPlanB_free3 : ∀ r, r < 64 → ∀ k, k < 6 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 + 3 ≠ (topPlanB.getD r []).getD k' 0 + 2 := by decide
theorem topPlanB_inj6 : ∀ r, r < 64 → ∀ k, k < 6 → ∀ k', k' < 5 →
    (topPlanB.getD r []).getD k 0 = (topPlanB.getD r []).getD k' 0 → k = k' := by decide
theorem topPlanA_free (r : Nat) (hr : r < 64) (j : Nat) (hj : j < 6) (j' : Nat) (hj' : j' < 6) (s : Nat) (hs : s < 4)
    (h : (topPlanA.getD r []).getD j 0 + s = (topPlanA.getD r []).getD j' 0 + 2) : j = j' ∧ s = 2 := by
  have h0 := topPlanA_free0 r hr j hj j' hj'
  have h1 := topPlanA_free1 r hr j hj j' hj'
  have h3 := topPlanA_free3 r hr j hj j' hj'
  have hs2 : s = 2 := by omega
  subst hs2
  exact ⟨topPlanA_inj r hr j hj j' hj' (by omega), rfl⟩
theorem topPlanB_free (r : Nat) (hr : r < 64) (k : Nat) (hk : k < 6) (k' : Nat) (hk' : k' < 5) (s : Nat) (hs : s < 4)
    (h : (topPlanB.getD r []).getD k 0 + s = (topPlanB.getD r []).getD k' 0 + 2) : k = k' ∧ s = 2 := by
  have h0 := topPlanB_free0 r hr k hk k' hk'
  have h1 := topPlanB_free1 r hr k hk k' hk'
  have h3 := topPlanB_free3 r hr k hk k' hk'
  have hs2 : s = 2 := by omega
  subst hs2
  exact ⟨topPlanB_inj6 r hr k hk k' hk' (by omega), rfl⟩
theorem topPlanB_bounds6 : ∀ r, r < 64 → ∀ k, k < 6 → (topPlanB.getD r []).getD k 0 ≤ 16 := by decide

theorem slot_free (leaf j j' s : Nat) (hj : j < 12) (hj' : j' < 11) (hs : s < 4)
    (h : topPlanSlot leaf j + s = topPlanSlot leaf j' + 2) : j = j' ∧ s = 2 := by
  have hr1 : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr2 : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  unfold topPlanSlot at h
  by_cases h6 : j < 6 <;> by_cases h6' : j' < 6
  · rw [if_pos h6, if_pos h6'] at h
    exact topPlanA_free _ hr1 j h6 j' h6' s hs h
  · rw [if_pos h6, if_neg h6'] at h
    have := (topPlanA_bounds _ hr1 j h6).1
    have := topPlanB_bounds _ hr2 (j' - 6) (by omega)
    omega
  · rw [if_neg h6, if_pos h6'] at h
    have := (topPlanA_bounds _ hr1 j' h6').1
    have := topPlanB_bounds6 _ hr2 (j - 6) (by omega)
    omega
  · rw [if_neg h6, if_neg h6'] at h
    have := topPlanB_free _ hr2 (j - 6) (by omega) (j' - 6) (by omega) s hs h
    omega

theorem merkleBlock_top (leaf j : Nat) : merkleBlock 0 leaf j = 7664 + 16 * topPlanSlot leaf j := by
  unfold merkleBlock
  rw [if_pos (show (0 : Layer).val = 0 from rfl)]
  rfl

/-- Slot `s` (`< 4`) of the level-`j` top window is nonce-free unless it is a nonce-carrying Z pad. -/
theorem top_window_free (output : HashOutput) (j s : Nat) (hj : j < 12) (hs : s < 4) (hne : ¬ (j < 11 ∧ s = 2)) :
    ∀ j', j' < 11 → merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 16 * s + 16 ≤ noncePos output j' ∨
      noncePos output j' + 8 ≤ merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 16 * s := by
  intro j' hj'
  rw [noncePos_eq, merkleBlock_top]
  by_cases he : topPlanSlot (route (WCT9.digestIndex output) 0).1 j + s =
      topPlanSlot (route (WCT9.digestIndex output) 0).1 j' + 2
  · obtain ⟨h1, h2⟩ := slot_free _ j j' s hj hj' hs he
    exact absurd ⟨by omega, h2⟩ hne
  · omega

theorem topPlanSlot_le (leaf j : Nat) (hj : j < 12) : topPlanSlot leaf j ≤ 38 := by
  have hr1 : leaf % 64 < 64 := Nat.mod_lt _ (by decide)
  have hr2 : leaf / 64 % 64 < 64 := Nat.mod_lt _ (by decide)
  unfold topPlanSlot
  split_ifs with h6
  · exact (topPlanA_bounds _ hr1 j h6).2
  · have := topPlanB_bounds6 _ hr2 (j - 6) (by omega); omega

/-- The reads of a top window slot agree with the legacy encoding. -/
theorem top_slot_legacy (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (j s : Nat) (hj : j < 12) (hs : s < 4) (hne : ¬ (j < 11 ∧ s = 2)) :
    wdig (witEncN output w) (merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 16 * s) =
      wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (merkleBlock 0 (route (WCT9.digestIndex output) 0).1 j + 16 * s) := by
  have hb := topPlanSlot_le (route (WCT9.digestIndex output) 0).1 j hj
  have hm := merkleBlock_top (route (WCT9.digestIndex output) 0).1 j
  apply wdig_N_legacy_free output w _ (by omega) (Or.inl (by unfold choiceOff; omega))
  have := top_window_free output j s hj hs hne
  intro j' hj'
  have := this j' hj'
  omega

theorem wpath_top_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (j : Nat) (hj : j < 12) :
    wpath (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j =
      wpath (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) 0 (route (WCT9.digestIndex output) 0).1 j := by
  unfold wpath SigGolfCandidate.T3M.sibOff
  split_ifs
  · have := top_slot_legacy output w j 0 hj (by decide) (by omega)
    simpa using this
  · have := top_slot_legacy output w j 3 hj (by decide) (by omega)
    simpa using this

theorem wmerkleHigh_top_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (j : Nat)
    (hj : j < 12) :
    wmerkleHigh (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j =
      wmerkleHigh (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) 0 (route (WCT9.digestIndex output) 0).1 j := by
  unfold wmerkleHigh
  have := top_slot_legacy output w j 1 hj (by decide) (by omega)
  simp only [Nat.mul_one] at this
  rw [this]

theorem wmerklePad_root_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wmerklePad (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 11 =
      wmerklePad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) 0 (route (WCT9.digestIndex output) 0).1 11 := by
  unfold wmerklePad
  have := top_slot_legacy output w 11 2 (by decide) (by decide) (by omega)
  simpa using this

/-- The level-`j` (`j < 11`) top Z pad of `witEncN` is the nonce `nonces.getD j 0 mod 2^64`. -/
theorem wmerklePad_top_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (j : Nat)
    (hj : j < 11) :
    wmerklePad (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j =
      BitVec.ofNat 128 (w.topNonces.getD j 0 % 2 ^ 64) := by
  have hlo := wmerklePad_witEncN_lo output w j hj
  have hhi := wmerklePad_witEncN_hi output w j hj
  generalize wmerklePad (witEncN output w) 0 (route (WCT9.digestIndex output) 0).1 j = d at hlo hhi ⊢
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hlo
  have h2 := congrArg BitVec.toNat hhi
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero,
    Nat.div_one, BitVec.toNat_zero] at h1 h2
  have hd := d.isLt
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at h1 h2 hd hz ⊢
  omega

/-! ### HonestN 4: retained layer reads away from the top path windows -/

theorem chainBlock_ge (lay : Layer) (i : Nat) : 8336 ≤ chainBlock lay i := by
  have : 8336 ≤ layerBase lay + 16 * pathSlots lay := by fin_cases lay <;> decide
  unfold chainBlock; omega

theorem chain_fields_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    (∀ i, wchainPads (witEncN output w) lay i = wchainPads (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay i) ∧
    (∀ i, wchainHeaderPad (witEncN output w) lay i = wchainHeaderPad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay i) ∧
    (∀ i, wvalue (witEncN output w) lay i = wvalue (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay i) ∧
    (∀ i, i < chainCount lay →
      wdig (witEncN output w) (leafBufferSlot lay i) = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (leafBufferSlot lay i)) ∧
    (∀ digits i, i < chainCount lay →
      wvalueFor (witEncN output w) lay digits i = wvalueFor (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay digits i) := by
  have hc : ∀ i x, x ≤ 48 → wdig (witEncN output w) (chainBlock lay i + x) =
      wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (chainBlock lay i + x) := by
    intro i x hx
    have := chainBlock_le lay i
    have := chainBlock_ge lay i
    exact wdig_N_legacy_hi output w _ (by omega) (Or.inl (by unfold choiceOff; omega))
  have hb : ∀ i, i < chainCount lay →
      wdig (witEncN output w) (leafBufferSlot lay i) = wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (leafBufferSlot lay i) := by
    intro i hi
    have hch := leafBufferSlot_choice lay i hi
    have h8 : 8320 ≤ leafBufferSlot lay i := by
      have : 8320 ≤ leafBufferBase lay := by fin_cases lay <;> decide
      unfold leafBufferSlot; split_ifs <;> omega
    exact wdig_N_legacy_hi output w _ h8 hch.1
  have hv : ∀ i, wvalue (witEncN output w) lay i = wvalue (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay i := by
    intro i
    unfold wvalue
    exact hc i _ (by unfold valueOff; split_ifs <;> omega)
  refine ⟨?_, ?_, hv, hb, ?_⟩
  · intro i
    unfold wchainPads
    rw [hc i _ (by unfold pad0Off; split_ifs <;> omega), hc i _ (by unfold pad1Off; split_ifs <;> omega)]
  · intro i
    unfold wchainHeaderPad
    rw [hc i 16 (by omega)]
  · intro digits i hi
    unfold wvalueFor
    split
    · exact hb i hi
    · exact hv i

theorem merkleBlock_lower_ge (lay : Layer) (hl : lay ≠ 0) (leaf j : Nat) : 11144 ≤ merkleBlock lay leaf j := by
  have : 11144 ≤ layerBase lay := by
    fin_cases lay
    · exact absurd rfl hl
    all_goals decide
  unfold merkleBlock; omega

theorem merkle_fields_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer)
    (hl : lay ≠ 0) :
    (∀ leaf j, wpath (witEncN output w) lay leaf j = wpath (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay leaf j) ∧
    (∀ leaf j, wmerklePad (witEncN output w) lay leaf j = wmerklePad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay leaf j) ∧
    (∀ leaf j, wmerkleHigh (witEncN output w) lay leaf j = wmerkleHigh (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay leaf j) := by
  have hm : ∀ leaf j x, x ≤ 48 → wdig (witEncN output w) (merkleBlock lay leaf j + x) =
      wdig (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) (merkleBlock lay leaf j + x) := by
    intro leaf j x hx
    have := PairedReadout.merkleBlock_le lay leaf j
    have := merkleBlock_lower_ge lay hl leaf j
    exact wdig_N_legacy_hi output w _ (by omega) (Or.inl (by unfold choiceOff; omega))
  refine ⟨?_, ?_, ?_⟩
  · intro leaf j
    unfold wpath
    exact hm leaf j _ (by unfold SigGolfCandidate.T3M.sibOff; split_ifs <;> omega)
  · intro leaf j
    unfold wmerklePad
    exact hm leaf j 32 (by omega)
  · intro leaf j
    unfold wmerkleHigh
    rw [hm leaf j 16 (by omega)]

theorem wtopLeafPad_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    wtopLeafPad (witEncN output w) = wtopLeafPad (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) := by
  unfold wtopLeafPad
  exact wdig_N_legacy_hi output w _ (by decide) (Or.inl (by decide))

theorem wleafHigh_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    wleafHigh (witEncN output w) lay = wleafHigh (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay := by
  have hl : 8320 ≤ leafBufferBase lay := by fin_cases lay <;> decide
  have hw : leafBufferBase lay + 16 + 8 + 8 ≤ choiceOff ∨ choiceOff < leafBufferBase lay + 16 + 8 := by
    fin_cases lay <;> decide
  unfold wleafHigh
  rw [PairedReadout.wdig_hi_extract, PairedReadout.wdig_hi_extract,
    extract_witEncN_out output w (leafBufferBase lay + 16 + 8) 8 (8 * 8) le_rfl (Or.inr (by omega)),
    PairedReadout.witEnc_extract output w _ _ hw]
  exact PairedReadout.word_prefixEnc (forestBytes output w) (forestBytes_length output w)
    output (mainWitness w) _ (by omega)

theorem layerPairP_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (index : Nat)
    (lay : Layer) (hl : lay ≠ 0) (digits : List Nat) :
    layerPairP (witEncN output w) index lay digits = layerPairP (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) index lay digits := by
  obtain ⟨hcp, hh, -, -, hvf⟩ := chain_fields_N output w lay
  obtain ⟨hp, hm, hmh⟩ := merkle_fields_N output w lay hl
  have hv : ∀ i : Fin (chainCount lay), wvalueFor (witEncN output w) lay digits i.val =
      wvalueFor (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) lay digits i.val := fun i => hvf digits i.val i.isLt
  simp only [layerPairP, hcp, hh, hv, hp, hm, hmh, wtopLeafPad_N, wleafHigh_N]

theorem layerGuardedPairP_N (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (lay : Layer) (hl : lay ≠ 0) (answer : Digest) (digits : List Nat) :
    layerGuardedPairP (witEncN output w) index lay answer digits =
      layerGuardedPairP (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) index lay answer digits := by
  obtain ⟨hcp, hh, -, -, hvf⟩ := chain_fields_N output w lay
  have hpos : 0 < chainCount lay := by fin_cases lay <;> decide
  have hc : layerChainP (witEncN output w) index lay digits = layerChainP (ClaudeWCT.W9.T3M.witEnc output (mainWitness w)) index lay digits := by
    funext i
    simp only [layerChainP, hcp, hh, hvf digits (i % chainCount lay) (Nat.mod_lt _ hpos)]
  simp only [layerGuardedPairP, hc, layerPairP_N output w index lay hl]

theorem rowBlock_out (index : Nat) (lay : Layer) : rowBlock index lay = 0 ∨ 11144 ≤ rowBlock index lay := by
  unfold rowBlock
  split
  · exact Or.inl rfl
  · rename_i h3
    right
    apply merkleBlock_lower_ge
    revert h3
    fin_cases lay <;> decide

theorem wbcCtr_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    wbcCtr (witEncN output w) (WCT9.digestIndex output) lay = w.counters lay := by
  rw [← Paired.wbcCtr_witEnc output w lay]
  unfold wbcCtr wle32 bcCounterOff
  exact extract_witEncN_out output w _ 4 32 (by omega) (by
    rcases rowBlock_out (WCT9.digestIndex output) lay with h | h <;> omega)
theorem wbcPad_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    wbcPad (witEncN output w) (WCT9.digestIndex output) lay = 0 := by
  rw [← Paired.wbcPad_witEnc output w lay]
  unfold wbcPad bcCounterOff
  exact extract_witEncN_out output w _ 12 96 (by omega) (by
    rcases rowBlock_out (WCT9.digestIndex output) lay with h | h <;> omega)
theorem wbcHigh_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (lay : Layer) :
    wbcHigh (witEncN output w) (WCT9.digestIndex output) lay = 1 := by
  rw [← Paired.wbcHigh_witEnc output w lay]
  unfold wbcHigh
  rw [wdig_witEncN_out output w (rowBlock (WCT9.digestIndex output) lay + 16)
    (by rcases rowBlock_out (WCT9.digestIndex output) lay with h | h <;> omega)]
end ClaudeWCT.W9.T3M.PairedNonce

/-! ### HonestN 5: the top layer on nonce pads is `verifyTopN` -/
namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Honest pads of a nonce-carrying witness: all zero except the top Z pads of levels `< 11` (the nonces). -/
def noncePads (nonces : List Nat) : Pads :=
  { (0 : Pads) with merkle := fun lay j =>
      if lay.val = 0 ∧ j.val < 11 then BitVec.ofNat 128 (nonces.getD j.val 0 % 2 ^ 64) else 0 }

@[simp] theorem noncePads_chain (n : List Nat) (lay : Layer) (i : Fin (chainCount lay)) :
    (noncePads n).chain lay i = (0, 0) := rfl
@[simp] theorem noncePads_chainHeader (n : List Nat) (lay : Layer) (i : Fin (chainCount lay)) :
    (noncePads n).chainHeader lay i = 0 := rfl
@[simp] theorem noncePads_endpointMask (n : List Nat) (lay : Layer) (i : Fin (chainCount lay)) :
    (noncePads n).endpointMask lay i = 0 := rfl
@[simp] theorem noncePads_merkleHigh (n : List Nat) (lay : Layer) (j : Fin (height lay)) :
    (noncePads n).merkleHigh lay j = 0 := rfl
@[simp] theorem noncePads_topLeaf (n : List Nat) : (noncePads n).topLeaf = 0 := rfl
@[simp] theorem noncePads_leafHigh (n : List Nat) (lay : Layer) : (noncePads n).leafHigh lay = 0 := rfl
theorem noncePads_merkle (n : List Nat) (lay : Layer) (j : Fin (height lay)) :
    (noncePads n).merkle lay j =
      if lay.val = 0 ∧ j.val < 11 then BitVec.ofNat 128 (n.getD j.val 0 % 2 ^ 64) else 0 := rfl

theorem valueP_noncePads (sig : WCT9.Signature) (n : List Nat) (lay : Layer) (digits : List Nat)
    (i : Fin (chainCount lay)) : valueP sig (noncePads n) lay digits i = (sig.layers lay).values i := by
  unfold valueP
  split
  · rw [noncePads_endpointMask]; exact BitVec.xor_zero
  · rfl

/-- A top node hash with the nonce in its Z pad is `T3.topNodeHashN`. -/
theorem lowerNodeHashP_nonce (heap n : Nat) (left right : Digest) :
    WCT9.lowerNodeHashP 0 0 heap left 0 (BitVec.ofNat 128 (n % 2 ^ 64)) right =
      SigGolfCandidate.T3.topNodeHashN heap n left right := by
  unfold WCT9.lowerNodeHashP WCT9.lowerHash WCT9.lowerNodeInputP SigGolfCandidate.T3.topNodeHashN
    SigGolfCandidate.T3.topNodeInput SigGolfCandidate.T3.nonceBytes
  rw [WCT9.lowerHigh_top_eq_nodeHalfHigh, WCT9.halfHash_eq_projHash,
    show ((0 : BitVec 64) ++ WCT9.merkleWord 0 0 heap) = WCT9.merkleTweak 0 0 heap from
      (WCT9.merkleTweak_eq_word 0 0 heap).symm, WCT9.merkleTweak_top]

theorem route_top_tree (index : Nat) (hindex : index < 2 ^ 31) : (route index 0).2 = 0 := by
  simp only [route, height, Matrix.cons_val_zero]
  exact Nat.div_eq_of_lt (lt_of_lt_of_eq hindex (by norm_num))

theorem topFold_noncePads (n : List Nat) (index : Nat) (hindex : index < 2 ^ 31) (j : Fin (height 0))
    (heap : Nat) (left right : Digest) :
    WCT9.lowerNodeHashP (0 : Layer).val (route index 0).2 heap left ((noncePads n).merkleHigh 0 j)
        ((noncePads n).merkle 0 j) right =
      if j.val < 11 then SigGolfCandidate.T3.topNodeHashN heap (n.getD j.val 0) left right
      else SigGolfCandidate.T3.nodeHash 3 (0 : Layer).val (route index 0).2 heap left right := by
  rw [noncePads_merkleHigh, noncePads_merkle]
  by_cases h2 : j.val < 11
  · rw [if_pos ⟨rfl, h2⟩, if_pos h2, route_top_tree index hindex]
    exact lowerNodeHashP_nonce heap _ left right
  · rw [if_neg (fun h => h2 h.2), if_neg h2]
    exact (WCT9.lowerNodeHash_eqP' 0 _ heap left right).symm.trans (WCT9.lowerNodeHash_top _ heap left right)

theorem verifyTopP_noncePads (sig : WCT9.Signature) (n : List Nat) (index : Nat) (answer : Digest)
    (hindex : index < 2 ^ 31) :
    verifyTopP sig (noncePads n) index answer = WCT9.verifyTopN sig n index answer := by
  simp only [verifyTopP, WCT9.verifyTopN, noncePads_chain, noncePads_chainHeader, valueP_noncePads,
    chainPW_zero_top _ _ _ _ hindex, noncePads_topLeaf, noncePads_leafHigh, leafHashW_zero,
    WCT9.lowerLeafHash_top, topFold_noncePads n index hindex]

/-- `verifyTopP` reads only the top layer's signature part and the top pads. -/
theorem verifyTopP_congr (sig sig' : WCT9.Signature) (pads pads' : Pads) (index : Nat) (answer : Digest)
    (hl : sig.layers 0 = sig'.layers 0)
    (hc : ∀ i, pads.chain 0 i = pads'.chain 0 i)
    (hch : ∀ i, pads.chainHeader 0 i = pads'.chainHeader 0 i)
    (hm : ∀ i, pads.endpointMask 0 i = pads'.endpointMask 0 i)
    (ht : pads.topLeaf = pads'.topLeaf)
    (hlh : pads.leafHigh 0 = pads'.leafHigh 0)
    (hmh : ∀ j, pads.merkleHigh 0 j = pads'.merkleHigh 0 j)
    (hmk : ∀ j, pads.merkle 0 j = pads'.merkle 0 j) :
    verifyTopP sig pads index answer = verifyTopP sig' pads' index answer := by
  simp only [verifyTopP, valueP, hl, hc, hch, hm, ht, hlh, hmh, hmk]

/-- Interface for the security side (r3-lean-nonsec, any witness bytes): a top verifier whose pads are zero except the
level-`j < 11` Z pads `BitVec.ofNat 128 (n_j % 2^64)` (= `WCT9.nonceDigest n_j`) is the nonce-reading `verifyTopN`. -/
theorem verifyTopP_eq_verifyTopN (sig : WCT9.Signature) (pads : Pads) (n : List Nat) (index : Nat) (answer : Digest)
    (hindex : index < 2 ^ 31)
    (hc : ∀ i, pads.chain 0 i = (0, 0)) (hch : ∀ i, pads.chainHeader 0 i = 0) (hm : ∀ i, pads.endpointMask 0 i = 0)
    (ht : pads.topLeaf = 0) (hlh : pads.leafHigh 0 = 0) (hmh : ∀ j, pads.merkleHigh 0 j = 0)
    (hmk : ∀ j : Fin (height 0), pads.merkle 0 j =
      if j.val < 11 then BitVec.ofNat 128 (n.getD j.val 0 % 2 ^ 64) else 0) :
    verifyTopP sig pads index answer = WCT9.verifyTopN sig n index answer := by
  rw [← verifyTopP_noncePads sig n index answer hindex]
  apply verifyTopP_congr sig sig pads (noncePads n) index answer rfl hc hch hm ht hlh hmh
  intro j
  rw [hmk j, noncePads_merkle]
  simp only [Fin.val_zero, true_and]

/-- The same on witness bytes: the retained top layer of any witness whose decoded top pads are the nonce pads. -/
theorem topLayerP_eq_verifyTopN (N : HashOutput) (w : WBytes) (n : List Nat) (answer : Digest)
    (hc : ∀ i, (padDecP N w).chain 0 i = (0, 0)) (hch : ∀ i, (padDecP N w).chainHeader 0 i = 0)
    (hm : ∀ i, (padDecP N w).endpointMask 0 i = 0) (ht : (padDecP N w).topLeaf = 0)
    (hlh : (padDecP N w).leafHigh 0 = 0) (hmh : ∀ j, (padDecP N w).merkleHigh 0 j = 0)
    (hmk : ∀ j : Fin (height 0), (padDecP N w).merkle 0 j =
      if j.val < 11 then BitVec.ofNat 128 (n.getD j.val 0 % 2 ^ 64) else 0) :
    topLayerP w (WCT9.digestIndex N) answer =
      WCT9.verifyTopN (witDecP N w).signature n (WCT9.digestIndex N) answer := by
  rw [topLayerP_dec N w]
  exact verifyTopP_eq_verifyTopN _ _ n _ answer (WCT9.digestIndex_lt N) hc hch hm ht hlh hmh hmk
end ClaudeWCT.W9.T3M

namespace ClaudeWCT.W9.T3M.PairedNonce
open OracleComp OracleSpec SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layerSig_ext {lay : Layer} (s t : SigGolfCandidate.T3.LayerSignature lay) (h1 : s.values = t.values)
    (h2 : s.path = t.path) : s = t := by
  cases s; cases t; cases h1; cases h2; rfl

/-- The retained top layer on `witEncN` is the scheme's nonce-reading top verifier. -/
theorem topLayerP_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (answer : Digest) :
    topLayerP (witEncN output w) (WCT9.digestIndex output) answer =
      WCT9.verifyTopN (mainWitness w).signature w.topNonces (WCT9.digestIndex output) answer := by
  have hz := ClaudeWCT.W9.T3M.padDecP_witEnc output (mainWitness w)
  have hd := ClaudeWCT.W9.T3M.witDecP_witEnc output (mainWitness w)
  obtain ⟨hcp, hh, hv, hb, -⟩ := chain_fields_N output w 0
  have hj12 : ∀ j : Fin (height (0 : Layer)), j.val < 12 := fun j => j.isLt
  rw [topLayerP_dec output, ← verifyTopP_noncePads _ w.topNonces _ answer (WCT9.digestIndex_lt output)]
  apply verifyTopP_congr
  · rw [← hd]
    apply layerSig_ext
    · funext i; simp only [witDecP]; exact hv i.val
    · funext j; simp only [witDecP]; exact wpath_top_N output w j.val (hj12 j)
  · intro i
    rw [show (noncePads w.topNonces).chain 0 i = (0 : Pads).chain 0 i from rfl, ← hz]
    simp only [padDecP]
    exact hcp i.val
  · intro i
    rw [show (noncePads w.topNonces).chainHeader 0 i = (0 : Pads).chainHeader 0 i from rfl, ← hz]
    simp only [padDecP]
    exact hh i.val
  · intro i
    rw [show (noncePads w.topNonces).endpointMask 0 i = (0 : Pads).endpointMask 0 i from rfl, ← hz]
    simp only [padDecP]
    rw [hv i.val, hb i.val i.isLt]
  · rw [show (noncePads w.topNonces).topLeaf = (0 : Pads).topLeaf from rfl, ← hz]
    simp only [padDecP]
  · rw [show (noncePads w.topNonces).leafHigh 0 = (0 : Pads).leafHigh 0 from rfl, ← hz]
    simp only [padDecP]
    exact wleafHigh_N output w 0
  · intro j
    rw [show (noncePads w.topNonces).merkleHigh 0 j = (0 : Pads).merkleHigh 0 j from rfl, ← hz]
    simp only [padDecP]
    rw [wmerkleHigh_top_N output w j.val (hj12 j)]
  · intro j
    rw [noncePads_merkle]
    simp only [padDecP]
    by_cases hj : j.val < 11
    · simp only [Fin.val_zero, or_true, true_and, hj, ↓reduceIte]
      exact wmerklePad_top_N output w j.val hj
    · have hj11 : j.val = 11 := by have := hj12 j; omega
      have h0 := congrArg (fun p : Pads => p.merkle 0 j) hz
      simp only [padDecP] at h0
      simp only [Fin.val_zero, or_true, true_and, hj, ↓reduceIte] at h0 ⊢
      rw [hj11, wmerklePad_root_N output w, ← hj11]
      exact h0

end ClaudeWCT.W9.T3M.PairedNonce

/-! ### HonestN 6: the retained layers on `witEncN` are the scheme's `verifyLayers` -/
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.PairedNonce
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem layersCanonicalBCH_witEncN (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) : ∀ n, n ≤ 4 → ∀ left right,
    layersCanonicalBCH w.topHigh (witEncN output w) (WCT9.digestIndex output) n (.pair left right) =
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) n (.pair left right) := by
  intro n
  induction n with
  | zero => intro _ left right; rfl
  | succ n ih =>
    intro hn left right
    have hguard : n ≠ 0 → ∀ answer digits,
        layerGuardedPairP (witEncN output w) (WCT9.digestIndex output) (Fin.ofNat 4 n) answer digits =
        WCT9.recoverLayerPairGuard (mainWitness w).signature (WCT9.digestIndex output)
          (Fin.ofNat 4 n) answer digits := by
      intro h0 answer digits
      have hlay : (Fin.ofNat 4 n : Layer) ≠ 0 := by
        intro e; have := congrArg Fin.val e; simp [Fin.val_ofNat] at this; omega
      rw [layerGuardedPairP_N output w _ _ hlay, layerGuardedPairP_dec output,
        ClaudeWCT.W9.T3M.witDecP_witEnc, ClaudeWCT.W9.T3M.padDecP_witEnc]
      exact recoverLayerPairGuardP_zero _ _ _ _ _ (WCT9.digestIndex_lt output) hlay
    by_cases h0 : n = 0
    · simp only [layersCanonicalBCH, SigGolfCandidate.Research.SharedForest.verifyLayers,
        wbcCtr_witEncN, wbcPad_witEncN, wbcHigh_witEncN, topLayerP_witEncN,
        layerEncodingInputP, WCT9.layerEncodingInput, WCT9.pairEncodingInputH_one, h0, ↓reduceIte]
      rfl
    · simp only [layersCanonicalBCH, SigGolfCandidate.Research.SharedForest.verifyLayers,
        wbcCtr_witEncN, wbcPad_witEncN, wbcHigh_witEncN, hguard h0,
        ih (by omega), layerEncodingInputP, WCT9.layerEncodingInput, WCT9.pairEncodingInputH_one, h0, ↓reduceIte]
      rfl

/-- Honest acceptance on the nonce-carrying encoding: the retained layer program on `witEncN` is the scheme's. -/
theorem layersCanonicalBC_witEncN (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (n : Nat) (left right : Digest) (hn : n ≤ 4) :
    layersCanonicalBC (witEncN output w) (WCT9.digestIndex output) n (.pair left right) =
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) n (.pair left right) := by
  rw [layersCanonicalBC_eq_H, wtopHigh_witEncN]
  exact layersCanonicalBCH_witEncN output w n hn left right
end ClaudeWCT.W9.T3M.Paired

/-! ### HonestN 7: the FTS forest reads only bytes below 7696 -/
namespace W9Drv.SharedCanonical
open W9Machine SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M
open ClaudeWCT.W9.T3M.PairedNonce
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem wdigM_witEncN_low (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (off : Nat) (h : off + 16 ≤ 7696) :
    W9Machine.wdig (Paired.witEncN output w) off = W9Machine.wdig (Paired.witEnc output w) off :=
  wdig_witEncN_out output w off (Or.inl h)

theorem regionOffset_le (k : Fin 9) : V3.regionOffset k.val ≤ 6864 := by
  have := k.isLt; unfold V3.regionOffset; omega

theorem chainReadout_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (word : Rank) (values : Fin 6 → Digest)
    (h : ChainReadout (Paired.witEnc output w) k word values) :
    ChainReadout (Paired.witEncN output w) k word values := by
  have hr := regionOffset_le k
  refine ⟨fun i => Eq.trans ?_ (h.padA i), fun i => Eq.trans ?_ (h.padB i), fun i => Eq.trans ?_ (h.padC i),
    fun i => Eq.trans ?_ (h.reveal i)⟩
  · have hb := PairedReadout.chain_field_bound i
    unfold V3.chainPadA V3.chainOffset
    exact wdigM_witEncN_low output w _ (by omega)
  · have hb := PairedReadout.chain_field_bound i
    unfold V3.chainPadB V3.chainOffset
    exact extract_witEncN_out output w _ 8 64 le_rfl (Or.inl (by omega))
  · have hb := PairedReadout.chain_field_bound i
    unfold V3.chainPadC V3.chainOffset
    exact wdigM_witEncN_low output w _ (by omega)
  · have hb := PairedReadout.chain_field_bound i
    have hi := i.isLt
    unfold V3.reveal V3.chainOffset
    split_ifs
    · exact wdigM_witEncN_low output w _ (by unfold V3.leafSlot; split_ifs <;> omega)
    · exact wdigM_witEncN_low output w _ (by
        have : ClaudeWCT.W9.T3M.wctValueOff i.val ≤ 48 := by
          unfold ClaudeWCT.W9.T3M.wctValueOff; split_ifs <;> omega
        omega)

theorem blkOff_bound (k : Fin 9) (c : Nat) (hc : c < 128) (l : Nat) (hl : l ≤ SharedV3.lastLevel k.val) :
    V3.regionOffset k.val + SharedV3.blkOff c l + 64 ≤ 7696 := by
  have hr := regionOffset_le k
  unfold SharedV3.blkOff
  split_ifs with h5
  · have : SigGolfCandidate.Research.SharedPathPacking.block c l + 64 ≤ 640 := PairedReadout.block_bound ⟨c, hc⟩ l h5
    omega
  · have hl5 : l = 5 := by unfold SharedV3.lastLevel at hl; split_ifs at hl <;> omega
    have hk : k.val ≠ 0 := by
      intro hk; rw [hk] at hl; unfold SharedV3.lastLevel SharedV3.first at hl; simp at hl; omega
    have := k.isLt
    unfold V3.regionOffset at hr ⊢
    omega

theorem pathReadout_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (raw : Child) (path : Nat → Digest)
    (h : PathReadout (Paired.witEnc output w) k raw path) :
    PathReadout (Paired.witEncN output w) k raw path := by
  have hc := SharedV3.physical_lt k.val raw.val raw.isLt
  have hr := regionOffset_le k
  refine ⟨fun l hl => Eq.trans ?_ (h.headerPads l hl), fun l hl hne => Eq.trans ?_ (h.nodePads l hl hne),
    fun l hl => Eq.trans ?_ (h.siblings l hl), Eq.trans ?_ h.topOther⟩
  · unfold SharedV3.nodeHPad SharedV3.nodeTw
    have := blkOff_bound k _ hc l hl
    split_ifs
    all_goals first
      | exact congrArg (fun d : Digest => d.extractLsb' 64 64) (wdigM_witEncN_low output w _ (by omega))
      | rfl
  · unfold SharedV3.nodePad
    have := blkOff_bound k _ hc l hl
    exact wdigM_witEncN_low output w _ (by omega)
  · unfold SharedV3.sibling SharedV3.sibOff
    have := blkOff_bound k _ hc l hl
    exact wdigM_witEncN_low output w _ (by
      have : 48 * (1 - SharedV3.physical k.val raw.val / 2 ^ l % 2) ≤ 48 := by omega
      omega)
  · unfold SharedV3.topOther SharedV3.topOtherOff SharedV3.handR SharedV3.handL
    exact wdigM_witEncN_low output w _ (by split_ifs <;> omega)

theorem initialPair_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) :
    SharedV3.initialPair (Paired.witEncN output w) = SharedV3.initialPair (Paired.witEnc output w) := by
  unfold SharedV3.initialPair SharedV3.leafPad V3.leafPad
  rw [wdigM_witEncN_low output w (V3.regionOffset 0 + 672) (by unfold V3.regionOffset; omega),
    wdigM_witEncN_low output w (V3.regionOffset 0 + 160) (by unfold V3.regionOffset; omega)]

theorem forest_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (index : Nat) (hi : index < 2 ^ 31) :
    SharedV3.forest (Paired.witEncN output witness) index (rawChildFromOutput output)
      (fun k => ClaudeWCT.WCT9.embed (forestRank output k.val)) =
      recoverForest index (forestSelectionFromOutput output) (forestWordsFromOutput output)
        witness.signature.forest := by
  have hp : ∀ k, PathReadout (Paired.witEncN output witness) k
      (coordinateRaw (forestSelectionFromOutput output) k) (coordinatePath witness.signature.forest k) := by
    intro k; rw [coordinateRaw_output]
    exact pathReadout_witEncN output witness k _ _ (pathReadout_witEnc output witness k)
  have h := forest_canonical (Paired.witEncN output witness) index hi
    (forestSelectionFromOutput output) (forestWordsFromOutput output) witness.signature.forest
    ((initialPair_witEncN output witness).trans (PairedReadout.initialPair_witEnc output witness))
    (fun k => chainReadout_witEncN output witness k _ _ (chainReadout_witEnc output witness k _)) hp
  simpa only [coordinateRaw_output, coordinateWord_output] using h
end W9Drv.SharedCanonical

/-! ### HonestN 8: the expander's re-derived top nonces are the keygen nonces (interface with r3-lean-nonsec)
`topHonestNonce answers index k` is r3n's `WCT9.honestNonce answers 0 (route index 0).2 k ((route index 0).1 / 2^(k+1))`
unfolded at `lay = 0, k < 11` (`unfold honestNonce; rw [if_pos ⟨rfl, hk⟩]`). -/
namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The keygen (nonce-searched) nonce of the level-`k + 1` top node on the path of `index`'s top leaf. -/
noncomputable def topHonestNonce (answers : Answers) (index k : Nat) : Nat :=
  (evalWithAnswerFn answers (topNodeAt (k + 1) (2 ^ (height (0 : Layer) - k - 1) + (route index 0).1 / 2 ^ (k + 1))
    (treeValue (wotsTree answers 0 (route index 0).2) k (2 * ((route index 0).1 / 2 ^ (k + 1))))
    (treeValue (wotsTree answers 0 (route index 0).2) k (2 * ((route index 0).1 / 2 ^ (k + 1)) + 1)))).1

/-- Fold invariant: value on the honest path, and the honest nonces of the levels passed so far. -/
theorem eval_topFoldN_nonces_steps (answers : Answers) (sig : Signature) (index : Nat)
    (levels : List (List Digest)) (leaves : List Digest) (htree : TopTreeLevels answers leaves 12 levels)
    (hleaf : (route index 0).1 < 2 ^ 12)
    (hpath : ∀ j : Fin (height 0), j.val < 11 → (sig.layers 0).path j =
      treeValue levels j.val ((route index 0).1 / 2 ^ j.val ^^^ 1)) :
    let R := evalWithAnswerFn answers (((List.finRange (height 0)).take 11).foldlM (topStepN sig index)
      (treeValue levels 0 (route index 0).1, []))
    R.2.length = 11 ∧ ∀ k, k < 11 → R.2.getD k 0 =
      (evalWithAnswerFn answers (topNodeAt (k + 1) (2 ^ (12 - (k + 1)) + (route index 0).1 / 2 ^ (k + 1))
        (treeValue levels k (2 * ((route index 0).1 / 2 ^ (k + 1))))
        (treeValue levels k (2 * ((route index 0).1 / 2 ^ (k + 1)) + 1)))).1 := by
  intro R
  have hi := eval_foldlM_list_inv answers ((List.finRange (height 0)).take 11) (topStepN sig index)
    (fun i (st : Digest × List Nat) => st.1 = treeValue levels i ((route index 0).1 / 2 ^ i) ∧ st.2.length = i ∧
      ∀ k, k < i → st.2.getD k 0 =
        (evalWithAnswerFn answers (topNodeAt (k + 1) (2 ^ (12 - (k + 1)) + (route index 0).1 / 2 ^ (k + 1))
          (treeValue levels k (2 * ((route index 0).1 / 2 ^ (k + 1))))
          (treeValue levels k (2 * ((route index 0).1 / 2 ^ (k + 1)) + 1)))).1)
    (treeValue levels 0 (route index 0).1, []) ⟨by simp, rfl, fun k hk => absurd hk (by omega)⟩
    (fun i hi st hv => ?_)
  · have hl : ((List.finRange (height 0)).take 11).length = 11 := by decide
    rw [hl] at hi
    exact ⟨hi.2.1, hi.2.2⟩
  · have hi' : i < 11 := by
      have h' := hi
      simp only [List.length_take, List.length_finRange] at h'
      change i < min 11 12 at h'
      omega
    generalize hj : ((List.finRange (height 0)).take 11)[i]'hi = j
    have hjv : j.val = i := by
      subst hj
      simp [List.getElem_take]
    obtain ⟨hv1, hv2, hv3⟩ := hv
    have hp := hpath j (by omega)
    simp only [topStepN, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [hp, hv1, hjv, sibling_pair (fun k => treeValue levels i k), div_pow_succ]
    have hh : height (0 : Layer) - i - 1 = 12 - (i + 1) := by
      change 12 - i - 1 = 12 - (i + 1); omega
    rw [hh]
    refine ⟨?_, ?_, ?_⟩
    · have hn := htree.2.2 i (by omega) ((route index 0).1 / 2 ^ (i + 1))
        (by simpa only [Nat.zero_add] using
          div_pow_bound (height := 12) (start := 0) (level := i + 1) (by omega) (by simpa using hleaf))
      rw [topLevelNode_lt answers (level := i + 1) (by omega)] at hn
      simpa only [treeValue] using hn.symm
    · simp [hv2]
    · intro k hk
      by_cases hki : k < i
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hv3 k hki
      · have hk' : k = i := by omega
        subst hk'
        rw [List.getD_append_right _ _ _ _ (by omega), hv2, Nat.sub_self]
        rfl

/-- Honest top layer (honest chain values for `digits`, honest path below the root): the expander's re-derived
nonces are the keygen nonces, `topHonestNonce`. -/
theorem topFoldN_nonces_honest (answers : Answers) (sig : Signature) (index : Nat) (hindex : index < 2 ^ 31)
    (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (hvalues : ∀ i : Fin (chainCount 0), (sig.layers 0).values i =
      wotsValue answers 0 (route index 0).2 (route index 0).1 digits i.val)
    (hpath : ∀ j : Fin (height 0), j.val < 11 → (sig.layers 0).path j =
      treeValue (wotsTree answers 0 (route index 0).2) j.val ((route index 0).1 / 2 ^ j.val ^^^ 1)) :
    (evalWithAnswerFn answers (topFoldN sig index digits)).2.length = 11 ∧
      ∀ k, k < 11 → (evalWithAnswerFn answers (topFoldN sig index digits)).2.getD k 0 = topHonestNonce answers index k := by
  have ht : (route index 0).2 = 0 := route_top_tree index hindex
  have hleaf : (route index 0).1 < 2 ^ 12 := route_leaf_bound index 0
  have htree := builtTopTree_correct answers 0
  have hvalues' : ∀ i : Fin (chainCount 0), (sig.layers 0).values i =
      leafValue answers 0 0 (route index 0).1 digits i.val := by
    intro i; rw [hvalues i, ht, wotsValue_top]
  have hpath' : ∀ j : Fin (height 0), j.val < 11 → (sig.layers 0).path j =
      treeValue (builtTree answers 0 0) j.val ((route index 0).1 / 2 ^ j.val ^^^ 1) := by
    intro j hj; rw [hpath j hj, ht, wotsTree_top]
  have hends : evalWithAnswerFn answers (topEnds sig index digits) =
      (List.range (chainCount 0)).map (leafEnd answers 0 0 (route index 0).1) := by
    unfold topEnds
    rw [ht]
    exact eval_chains_honest answers 0 0 _ digits hvalid _ hvalues'
  have hroot : evalWithAnswerFn answers (SigGolfCandidate.T3.leafHash 0 (route index 0).2 (route index 0).1
      (evalWithAnswerFn answers (topEnds sig index digits))) =
      treeValue (builtTree answers 0 0) 0 (route index 0).1 := by
    rw [hends, ht, builtTree_leaf answers 0 0 _ hleaf]
    rfl
  have hs := eval_topFoldN_nonces_steps answers sig index _ _ htree hleaf hpath'
  have hf : evalWithAnswerFn answers (topFoldN sig index digits) =
      evalWithAnswerFn answers (((List.finRange (height 0)).take 11).foldlM (topStepN sig index)
        (treeValue (builtTree answers 0 0) 0 (route index 0).1, [])) := by
    unfold topFoldN
    simp only [evalWithAnswerFn_bind]
    rw [hroot]
  rw [hf]
  refine ⟨hs.1, fun k hk => ?_⟩
  rw [hs.2 k hk]
  unfold topHonestNonce
  rw [ht, wotsTree_top]
  have hh : height (0 : Layer) - k - 1 = 12 - (k + 1) := by change 12 - k - 1 = 12 - (k + 1); omega
  rw [hh]
end ClaudeWCT.WCT9

namespace SigGolfCandidate.Research.SharedForest
open OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The recovered top nonces are the nonce fold of the recovered top digits. -/
theorem recoverHintedLayers_nonces_at (answers : Answers) (sig : Signature) (index : Nat)
    (other : Digest) (topFloor : Nat) :
    ∀ n, ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index other n msg topFloor) = some result →
      result.digits ≠ [] ∧
      result.nonces = (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (result.digits.getD 0 []))).2 := by
  intro n
  induction n with
  | zero => intro msg result he; simp [recoverHintedLayers] at he
  | succ n ih =>
      intro msg result he
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      · rename_i counter digits low _
        by_cases hn0 : n = 0
        · subst n
          simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst result
          exact ⟨List.cons_ne_nil _ _, rfl⟩
        · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
          split at he
          · rename_i previous hr
            simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            obtain ⟨hne, hn⟩ := ih _ _ hr
            have hlen : 0 < previous.digits.length := List.length_pos_of_ne_nil hne
            refine ⟨List.append_ne_nil_of_left_ne_nil hne _, ?_⟩
            show previous.nonces = _
            rw [List.getD_append _ _ _ _ hlen]
            exact hn
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
      · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he

theorem recoverHintedLayers_nonces (answers : Answers) (sig : Signature) (index : Nat) (other : Digest) :
    ∀ n, ∀ msg result,
      evalWithAnswerFn answers (recoverHintedLayers sig index other n msg) = some result →
      result.digits ≠ [] ∧
      result.nonces = (evalWithAnswerFn answers (topFoldN (mainSignature sig) index (result.digits.getD 0 []))).2 :=
  recoverHintedLayers_nonces_at answers sig index other CanonicalPolicy.topFloor
end SigGolfCandidate.Research.SharedForest

/-! ### HonestN 9: the `Paired.witEnc` read lemmas used by the security side, for `witEncN` -/
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.PairedNonce
open W9Drv.SharedCanonical (wdigM_witEncN_low regionOffset_le blkOff_bound)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem wvalueFor_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (digits : List Nat) (i : Fin (chainCount lay)) :
    wvalueFor (witEncN output w) lay digits i.val = (w.signature.layers lay).values i := by
  rw [← wvalueFor_witEnc output w lay digits i]
  unfold wvalueFor
  split
  · have h8 : 8320 ≤ leafBufferSlot lay i.val := by
      have : 8320 ≤ leafBufferBase lay := by fin_cases lay <;> decide
      unfold leafBufferSlot; split_ifs <;> omega
    exact wdig_witEncN_out output w _ (Or.inr h8)
  · unfold wvalue
    have := chainBlock_ge lay i.val
    exact wdig_witEncN_out output w _ (Or.inr (by omega))

theorem wpath_witEncN (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (lay : Layer) (j : Fin (height lay)) :
    wpath (witEncN output w) lay (route (WCT9.digestIndex output) lay).1 j.val = (w.signature.layers lay).path j := by
  rw [← wpath_witEnc output w lay j]
  by_cases hl : lay = 0
  · subst hl
    have hj : j.val < 12 := j.isLt
    unfold wpath SigGolfCandidate.T3M.sibOff
    split_ifs
    · have := top_window_free output j.val 0 hj (by decide) (by omega)
      exact wdig_witEncN_free output w _ (fun j' hj' => by have := this j' hj'; omega)
    · have := top_window_free output j.val 3 hj (by decide) (by omega)
      exact wdig_witEncN_free output w _ (fun j' hj' => by have := this j' hj'; omega)
  · unfold wpath
    have := merkleBlock_lower_ge lay hl (route (WCT9.digestIndex output) lay).1 j.val
    exact wdig_witEncN_out output w _ (Or.inr (by omega))

theorem wleafValue_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) :
    wdig (witEncN output witness) (W9Machine.V3.regionOffset k.val + W9Machine.V3.leafSlot i.val) =
      coordinateValues witness.signature.forest k i := by
  have hr := regionOffset_le k
  have hi := i.isLt
  refine Eq.trans ?_ (wleafValue_witEnc output witness k i)
  exact wdigM_witEncN_low output witness _ (by unfold W9Machine.V3.leafSlot; split_ifs <;> omega)

theorem wchainValue_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (i : Fin 6) :
    wdig (witEncN output witness) (W9Machine.V3.chainOffset k.val i.val + ClaudeWCT.W9.T3M.wctValueOff i.val) =
      coordinateValues witness.signature.forest k i := by
  have hr := regionOffset_le k
  have hb := PairedReadout.chain_field_bound i
  have hv : ClaudeWCT.W9.T3M.wctValueOff i.val ≤ 48 := by
    unfold ClaudeWCT.W9.T3M.wctValueOff; split_ifs <;> omega
  refine Eq.trans ?_ (wchainValue_witEnc output witness k i)
  exact wdigM_witEncN_low output witness _ (by unfold W9Machine.V3.chainOffset; omega)

theorem wsibling_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) (level : Nat) (hl : level < W9Machine.SharedV3.lastLevel k.val + 1) :
    W9Machine.SharedV3.sibling (witEncN output witness) k.val
      (W9Machine.SharedV3.physical k.val (rawChildFromOutput output k).val) level =
      coordinatePath witness.signature.forest k level := by
  have hc := W9Machine.SharedV3.physical_lt k.val (rawChildFromOutput output k).val
    (rawChildFromOutput output k).isLt
  have hb := blkOff_bound k _ hc level (by omega)
  refine Eq.trans ?_ (wsibling_witEnc output witness k level hl)
  unfold W9Machine.SharedV3.sibling W9Machine.SharedV3.sibOff
  exact wdigM_witEncN_low output witness _ (by
    have : 48 * (1 - W9Machine.SharedV3.physical k.val (rawChildFromOutput output k).val / 2 ^ level % 2) ≤ 48 := by
      omega
    omega)

theorem wtopOther_witEncN (output : HashOutput) (witness : SigGolfCandidate.Research.SharedForest.Witness)
    (k : Fin 9) :
    W9Machine.SharedV3.topOther (witEncN output witness) k.val
      (W9Machine.SharedV3.physical k.val (rawChildFromOutput output k).val) =
      coordinatePath witness.signature.forest k (W9Machine.SharedV3.lastLevel k.val + 1) := by
  have hr := regionOffset_le k
  refine Eq.trans ?_ (wtopOther_witEnc output witness k)
  unfold W9Machine.SharedV3.topOther W9Machine.SharedV3.topOtherOff W9Machine.SharedV3.handR
    W9Machine.SharedV3.handL
  exact wdigM_witEncN_low output witness _ (by split_ifs <;> omega)
end ClaudeWCT.W9.T3M.Paired

/-! ### HonestN 10: the witness nonces are the nonce fold of the expander's top digits -/
namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem expandN_nonces_raw (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    ∃ result c,
      evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0) (WCT9.digestIndex output)
        (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)
        (conditionalTopFloor output)) = some result ∧
      w.signature = fillTopSignature sig c ∧ w.topNonces = result.nonces := by
  unfold expandN at he
  simp only [show (fillTopSignature sig 0).rho = sig.rho from rfl,
    show (fillTopSignature sig 0).forest = sig.forest from rfl,
    show (fillTopSignature sig 0).policyHints = sig.policyHints from rfl] at he
  by_cases hh : sig.policyHints.toNat ≥ 7744
  · simp only [hh, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he
  · simp only [hh, if_false, evalWithAnswerFn_bind] at he
    cases hd : evalWithAnswerFn answers (sharedDigestSearch sig.rho message 0 WCT9.digestAttemptLimit) with
    | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
    | some found =>
        obtain ⟨counter, N⟩ := found
        simp only [hd, evalWithAnswerFn_bind] at he
        let forest := evalWithAnswerFn answers (recoverForest (WCT9.digestIndex N)
          (forestSelectionFromOutput N) (forestWordsFromOutput N) sig.forest)
        cases hr : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0)
          (WCT9.digestIndex N) (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
          (.pair forest.1 forest.2) (conditionalTopFloor N)) with
        | none =>
            dsimp only [forest] at hr
            simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at he
        | some result =>
            dsimp only [forest] at hr
            simp only [hr] at he
            by_cases hp : policyHintsValid sig.policyHints result.digits result.lows
                (conditionalCredit N) = true
            · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at he
              by_cases hk : result.root = pk
              · simp only [hk, if_true, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                exact ⟨result, 0, (by first | exact hr | rfl), rfl, rfl⟩
              · simp only [hk, if_false, evalWithAnswerFn_bind] at he
                cases hc : evalWithAnswerFn answers (WCT9.searchTop (WCT9.digestIndex N) result.foldedTop
                  (((fillTopSignature sig 0).layers 0).path WCT9.topJ) pk WCT9.searchFuel 1) with
                | none => simp only [hc, evalWithAnswerFn_pure, reduceCtorEq] at he
                | some c =>
                    simp only [hc, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                    obtain ⟨rfl, rfl⟩ := he
                    exact ⟨result, c, (by first | exact hr | rfl), fillTopSignature_fillTopSignature sig 0 c, rfl⟩
            · have hp0 := Bool.eq_false_of_not_eq_true hp
              simp only [hp0, Bool.not_false, if_true, evalWithAnswerFn_pure, reduceCtorEq] at he

/-- img-v6: the expanded witness's top nonces are the expander's nonce fold (`topFoldN`) of its top digits, on the
witness's own signature. With `ClaudeWCT.WCT9.topFoldN_nonces_honest` they are the keygen nonces on an honest top. -/
theorem expandN_topNonces (answers : Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig) = some (output,w)) :
    ∃ result,
      evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig 0) (WCT9.digestIndex output)
        (((fillTopSignature sig 0).layers 0).path WCT9.topJ) 4
        (.pair (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).1
          (evalWithAnswerFn answers (recoverForest (WCT9.digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) sig.forest)).2)
        (conditionalTopFloor output)) = some result ∧
      w.topNonces = (evalWithAnswerFn answers
        (ClaudeWCT.WCT9.topFoldN (mainSignature w.signature) (WCT9.digestIndex output) (result.digits.getD 0 []))).2 := by
  obtain ⟨result, c, hr, hsig, hn⟩ := expandN_nonces_raw answers message pk sig output w he
  refine ⟨result, hr, ?_⟩
  rw [hn, (recoverHintedLayers_nonces_at answers _ _ _ (conditionalTopFloor output)
    4 _ result hr).2, hsig, topFoldN_fill_signature,
    topFoldN_fill_signature]
end ClaudeWCT.W9.T3M.Paired
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_Budgets ====
section

/-! r3h HonestN: the legacy (WCT9, 5310-byte) pipeline section of this file was removed: its codec round trip
(`sigDecC (sigBC s) = WCT9.proj s`) no longer holds with the v6 19-bit top split, and `Packaging.Ready` only uses the
`Final.Paired` route. Removed block saved in research/agents/r3-lean-honestn/orig/Budgets_legacy_removed.lean. -/

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ftsP_accepted (w : WBytes) (output : HashOutput)
    (hg : output.toNat/2^242%16384<791)
    (hr : ∀ k : Fin 9,rawForestRank output k.val<563) :
    ftsP w output = (do
      let p ← SharedV3.forest w (WCT9.digestIndex output) (rawChildFromOutput output)
        (fun k=>WCT9.embed (forestRank output k.val))
      pure (some p)) := by
  have hs : ftsStep w output = W9Drv.SharedAcceptedFold.step (SharedV3.initialPair w)
      (fun prev k=>SharedV3.coordinate w (WCT9.digestIndex output) k (rawChildFromOutput output k)
        (WCT9.embed (forestRank output k.val)) prev)
      (fun k=>decide (rawForestRank output k.val<563)) := by
    funext state k
    cases state <;> simp [ftsStep,W9Drv.SharedAcceptedFold.step,hr k]
  have h := W9Drv.SharedAcceptedFold.accepted (m:=M) (SharedV3.initialPair w)
    (fun prev k=>SharedV3.coordinate w (WCT9.digestIndex output) k (rawChildFromOutput output k)
      (WCT9.embed (forestRank output k.val)) prev)
    (fun k=>decide (rawForestRank output k.val<563)) (List.finRange 9)
    (fun k _=>by simp[hr k]) []
  have he : ftsP w output =
      ((List.finRange 9).foldlM (ftsStep w output) (some []) >>=
        W9Drv.SharedAcceptedFold.finish (SharedV3.initialPair w)) := by
    unfold ftsP
    simp only [hg,decide_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
    congr 1
    funext state
    cases state <;> rfl
  rw [he,hs]
  simpa only [List.getLastD_nil,SharedV3.forest] using h

theorem verifyP_source_of (answers : SigGolfCandidate.T3.Correctness.Answers)
    (message : Message) (pk : Digest) (wb : WBytes)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hrho : wrho wb=w.signature.rho) (hdc : wdc wb=w.digestCounter)
    (hd : evalWithAnswerFn answers (digest w.signature.rho message w.digestCounter)=output)
    (hbound : w.digestCounter.toNat<WCT9.digestVerifyWindow)
    (hg : output.toNat/2^242%16384<791)
    (hr : ∀ k : Fin 9,rawForestRank output k.val<563)
    (hf : SharedV3.forest wb (WCT9.digestIndex output) (rawChildFromOutput output)
      (fun k=>WCT9.embed (forestRank output k.val)) =
      recoverForest (WCT9.digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) w.signature.forest)
    (hl : ∀left right,layersCanonicalBC wb (WCT9.digestIndex output) 4 (.pair left right)=
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) 4 (.pair left right)) :
    evalWithAnswerFn answers (verifyP message pk wb)=
      evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.verify message pk w) := by
  have hd' : evalWithAnswerFn answers (digestP message wb)=some output := by
    simp only [digestP,hdc,hrho,show ¬w.digestCounter.toNat≥WCT9.digestVerifyWindow by omega,
      ↓reduceIte,evalWithAnswerFn_map,hd]
  have ha : verifyDigestAccepted output=true := by
    simp only [verifyDigestAccepted,hg,decide_true,Bool.true_and]
    exact (ranksAccepted_iff output).mpr hr
  rw [verifyP,evalWithAnswerFn_bind,hd']
  simp only [ftsP_accepted wb output hg hr,hf,evalWithAnswerFn_bind,evalWithAnswerFn_pure,hl]
  simp only [SigGolfCandidate.Research.SharedForest.verify,
    show ¬w.digestCounter.toNat≥WCT9.digestVerifyWindow by omega,↓reduceIte,
    evalWithAnswerFn_bind,hd,ha,Bool.not_true,Bool.false_eq_true,hl]
  rfl

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
open W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem verifyP_witEncN_eval (answers : SigGolfCandidate.T3.Correctness.Answers)
    (message : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature)
    (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig)=some (output,w)) :
    evalWithAnswerFn answers (verifyP message pk (witEncN output w))=
      evalWithAnswerFn answers (SigGolfCandidate.Research.SharedForest.verify message pk w) := by
  obtain ⟨_,counter,result,c,hs,_,_,hw,hc,_⟩ := expandN_selections answers message pk sig output w he
  have hsearch := sharedDigestSearch_some answers sig.rho message WCT9.digestAttemptLimit 0
    counter output (by decide) hs
  obtain ⟨hg,hr,_⟩ := accepted_conditions output hsearch.2.2.1
  have hd : evalWithAnswerFn answers (digest w.signature.rho message w.digestCounter)=output := by
    rw [hw,hc,nonce_retained]
    exact hsearch.2.2.2
  have hb : w.digestCounter.toNat<WCT9.digestVerifyWindow := by
    rw [hc]
    have hlt := hsearch.2.1
    unfold WCT9.digestAttemptLimit WCT9.digestVerifyWindow at *
    omega
  exact verifyP_source_of answers message pk _ output w
    (ClaudeWCT.W9.T3M.Paired.wrho_witEncN output w)
    (ClaudeWCT.W9.T3M.Paired.wdc_witEncN output w) hd hb hg hr
    (W9Drv.SharedCanonical.forest_witEncN output w _ (WCT9.digestIndex_lt output))
    (fun left right=>layersCanonicalBC_witEncN output w 4 left right (by decide))

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest (Signature Witness)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def honestProgramCore (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← SigGolfCandidate.Research.SharedForest.sign keys.2 message
  match sig with
  | none=>pure false
  | some sig=>
    let witness ← SigGolfCandidate.Research.SharedForest.expand message keys.1 sig
    match witness with
    | none=>pure false
    | some witness=>SigGolfCandidate.Research.SharedForest.verify message keys.1 witness

def honestProgramB (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← SigGolfCandidate.Research.SharedForest.sign keys.2 message
  match sig with
  | none=>pure false
  | some sig=>
    let witness ← expandB message keys.1 (SigGolfCandidate.Research.SharedForest.normTop sig)
    match witness with
    | none=>pure false
    | some witness=>verifyP message keys.1 witness

/-- img-v6: `expand = expandFill ∘ normTop`, and `expandN` mirrors `expandFill` (r3w: `expandN_snd` is stated for
`SharedForest.expandFill`). -/
theorem expand_eq_expandN (m : Message) (pk : Digest) (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    SigGolfCandidate.Research.SharedForest.expand m pk sig=Option.map Prod.snd <$> expandN m pk (SigGolfCandidate.Research.SharedForest.normTop sig) :=
  (expandN_snd m pk (SigGolfCandidate.Research.SharedForest.normTop sig)).symm

theorem eval_expandB (answers : Correctness.Answers) (m : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) :
    evalWithAnswerFn answers (expandB m pk sig)=
      (evalWithAnswerFn answers (expandN m pk sig)).map (fun p=>witEncN p.1 p.2) := by
  rw [expandB,evalWithAnswerFn_map]

theorem honestB_eval (answers : Correctness.Answers) (m : Message) :
    evalWithAnswerFn answers (honestProgramB m)=evalWithAnswerFn answers (honestProgramCore m) := by
  unfold honestProgramB honestProgramCore
  simp only [evalWithAnswerFn_bind]
  cases hs : evalWithAnswerFn answers
      (SigGolfCandidate.Research.SharedForest.sign (evalWithAnswerFn answers keygen).2 m) with
  | none=>rfl
  | some sig=>
    simp only []
    rw [expand_eq_expandN,evalWithAnswerFn_bind,evalWithAnswerFn_bind,evalWithAnswerFn_map,eval_expandB]
    cases hx : evalWithAnswerFn answers (expandN m (evalWithAnswerFn answers keygen).1 (SigGolfCandidate.Research.SharedForest.normTop sig)) with
    | none=>rfl
    | some x=>
      obtain ⟨output,w⟩:=x
      simp only [Option.map_some]
      exact verifyP_witEncN_eval answers m _ (SigGolfCandidate.Research.SharedForest.normTop sig) output w hx

end ClaudeWCT.W9.T3M.Paired

namespace ClaudeWCT.W9.T3M.Final.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest (Signature Witness fillTopSignature)

structure EncodingFactsData (p0 p1 p2 : Prop) : Prop where
  sig_roundtrip : p0
  expandN_fill : p1
  honest_eval : p2

abbrev EncodingFacts : Prop := EncodingFactsData
  (∀sig : SigGolfCandidate.Research.SharedForest.Signature,sigDecC (sigBC sig)=SigGolfCandidate.Research.SharedForest.normTop sig)
  (∀(m : Message)(pk : Digest)(sig : SigGolfCandidate.Research.SharedForest.Signature)(c : Nat),
    expandN m pk (fillTopSignature sig c)=expandN m pk sig)
  (∀(answers : Correctness.Answers)(m : Message),
    evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.honestProgramB m)=
      evalWithAnswerFn answers (ClaudeWCT.W9.T3M.Paired.honestProgramCore m))

theorem EncodingFacts.expandB_fill (E : EncodingFacts) (m : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (c : Nat) :
    expandB m pk (fillTopSignature sig c)=expandB m pk sig := by
  simp only [expandB,ClaudeWCT.W9.T3M.Paired.expandB,E.expandN_fill]
end ClaudeWCT.W9.T3M.Final.Paired


section
open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge
namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand verify)
open SigGolfCandidate.T3M (mrealize mrealize_bind mrealize_map cacheB cacheDec cacheDec_cacheB isHash toQ toQ_injOn
  Aligned)
open SigGolfCandidate.T3M.Final (successPipe success_honest_eq foldAll foldAll_cons evalWithAnswerFn_foldAll
  randomOracle_congr probOutput_congr_evalSPMF mrealize_public mrealize_eq_relabel run'_relabel_on allQ_hrealize
  realize_eq_liftM)
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.Paired.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
variable {I : Images}
set_option maxRecDepth 100000 in
theorem keygen_value (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) :
    (fun r => r.value) <$> (submission I).run .keygen sk =
      (fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2)) <$> mrealize sk keygen :=
  value_of_counts (F := fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2)) (P.keygen_run_counts sk)
set_option maxRecDepth 100000 in
theorem sign_value (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (fun r => r.value) <$> (submission I).run .sign (sk, cache, m) =
      Option.map sigBC <$> mrealize sk (sign (cacheDec cache) m) :=
  value_of_counts (F := Option.map sigBC) (P.sign_refines sk cache m)
set_option maxRecDepth 100000 in
theorem expand_value (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (m : Message) (pk : PublicKey) (s : Bytes 5195) :
    (fun r => r.value) <$> (submission I).run .expand (m, pk, s) = mrealize 0 (expandB m pk (sigDecC s)) := by
  rw [value_of_counts (F := Option.map (fun x : SigGolfCandidate.T3.HashOutput × Witness => witEncN x.1 x.2))
    (P.expand_refines m pk s), expandB, ClaudeWCT.W9.T3M.Paired.expandB, mrealize_map]
set_option maxRecDepth 100000 in
theorem verify_value (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (m : Message) (pk : PublicKey) (w : Bytes 22012) :
    (fun r => r.value.isSome) <$> (submission I).run .verify (m, pk, w) = mrealize 0 (verifyP m pk w) := by
  have h := congrArg (fun x => (fun p : Option Unit × Nat => p.1.isSome) <$> x) (P.verify_refines m pk w)
  simp only [Functor.map_map] at h
  refine h.trans ?_
  have e : (fun p : Bool × Nat => ((if p.1 then some () else none : Option Unit)).isSome) = Prod.fst := by
    funext p; rcases p with ⟨_ | _, n⟩ <;> rfl
  rw [e, SigGolfCandidate.T3M.fst_countCalls]
set_option maxRecDepth 100000 in
theorem successPipe_eq (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (m : Message) :
    successPipe (submission I) sk m = mrealize sk (ClaudeWCT.W9.T3M.Paired.honestProgramB m) := by
  unfold successPipe ClaudeWCT.W9.T3M.Paired.honestProgramB
  rw [keygen_value E F P, bind_map_left, mrealize_bind]
  refine bind_congr fun kp => ?_
  simp only
  rw [sign_value E F P, bind_map_left, cacheDec_cacheB, mrealize_bind]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · rfl
  · simp only [Option.map_some]
    rw [expand_value E F P, E.sig_roundtrip, mrealize_bind,
      mrealize_public 0 sk (F.public_expandB m kp.1 (SigGolfCandidate.Research.SharedForest.normTop σ))]
    refine bind_congr fun e => ?_
    rcases e with _ | w
    · rfl
    · exact (verify_value E F P m _ w).trans (mrealize_public 0 sk (F.public_verifyP m kp.1 w))
noncomputable def foldB : M Bool := foldAll msgs ClaudeWCT.W9.T3M.Paired.honestProgramB true
noncomputable def foldC : M Bool := foldAll msgs ClaudeWCT.W9.T3M.Paired.honestProgramCore true
theorem allSucceed_eq (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) :
    HonestSummary.allSucceed <$> (submission I).allMessages sk = mrealize sk foldB := by
  rw [allSucceed_allMessages, foldB, mrealize_foldAll]
  exact congrArg (fun F => foldAll msgs F true) (funext fun m => by rw [success_honest_eq, successPipe_eq E F P])
theorem eval_foldAll_B (E : EncodingFacts) (F : SourceQueries) (L : List SigGolfCandidate.T3.Message) (sk : SecretKey) (hash : Hash) :
    evalWithAnswerFn hash (mrealize sk (foldAll L ClaudeWCT.W9.T3M.Paired.honestProgramB true)) =
      evalWithAnswerFn hash (mrealize sk (foldAll L ClaudeWCT.W9.T3M.Paired.honestProgramCore true)) := by
  rw [eval_mrealize, eval_mrealize, evalWithAnswerFn_foldAll, evalWithAnswerFn_foldAll]
  simp only [E.honest_eval]
theorem eval_foldB (E : EncodingFacts) (F : SourceQueries) (sk : SecretKey) (hash : Hash) :
    evalWithAnswerFn hash (mrealize sk foldB) = evalWithAnswerFn hash (mrealize sk foldC) :=
  eval_foldAll_B E F msgs sk hash
theorem everyMessageProgram_eq (E : EncodingFacts) (F : SourceQueries) : ClaudeWCT.W9.T3.Completeness.Paired.everyMessageProgram = foldC := by
  unfold ClaudeWCT.W9.T3.Completeness.Paired.everyMessageProgram foldC foldAll msgs
  refine congrArg (fun f => List.foldlM f true (Finset.univ : Finset SigGolfCandidate.T3.Message).toList) ?_
  funext b m
  rw [map_eq_bind_pure_comp]
  rfl
set_option maxRecDepth 100000 in
theorem allQ_honestProgramCore (E : EncodingFacts) (F : SourceQueries) {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (he : ∀ m pk σ, AllQueriesSatisfy (expand m pk σ) Q)
    (hv : ∀ m pk w, AllQueriesSatisfy (verify m pk w) Q) (m : SigGolfCandidate.T3.Message) :
    AllQueriesSatisfy (ClaudeWCT.W9.T3M.Paired.honestProgramCore m) Q := by
  unfold ClaudeWCT.W9.T3M.Paired.honestProgramCore
  refine SigGolfCandidate.T3M.allQ_bind hk fun keys => SigGolfCandidate.T3M.allQ_bind (hs _ _) fun sig => ?_
  rcases sig with _ | sig
  · exact SigGolfCandidate.T3M.allQ_pure _
  refine SigGolfCandidate.T3M.allQ_bind (he _ _ _) fun w => ?_
  rcases w with _ | w
  · exact SigGolfCandidate.T3M.allQ_pure _
  exact hv _ _ _
set_option maxRecDepth 100000 in
theorem withRandomOracle_core (E : EncodingFacts) (F : SourceQueries) (S : SourceFacts) (sk : SecretKey) :
    withRandomOracle (mrealize sk foldC) =
      (simulateQ SphincsSecurity.romImpl (realize sk ClaudeWCT.W9.T3.Completeness.Paired.everyMessageProgram)).run' ∅ := by
  have hgood : AllQueriesSatisfy foldC SigGolfCandidate.T3.Cost.GoodQuery := by
    unfold foldC
    exact allQ_foldAll' msgs ClaudeWCT.W9.T3M.Paired.honestProgramCore (allQ_honestProgramCore E F (Q := SigGolfCandidate.T3.Cost.GoodQuery)
      SigGolfCandidate.T3M.goodQ_keygen F.good_sign F.good_expand F.good_verify) true
  have hhash : AllQueriesSatisfy foldC isHash := by
    unfold foldC
    exact allQ_foldAll' msgs ClaudeWCT.W9.T3M.Paired.honestProgramCore (allQ_honestProgramCore E F (Q := isHash) S.hashOnly_keygen
      S.hashOnly_sign S.hashOnly_expand S.hashOnly_verify) true
  unfold withRandomOracle
  rw [mrealize_eq_relabel, ← run'_relabel_on toQ {l | Aligned l} toQ_injOn _ (allQ_hrealize sk hgood) ∅ ∅
    (fun _ _ => rfl), everyMessageProgram_eq E F, realize_eq_liftM sk hhash, SphincsSecurity.romImpl,
    QueryImpl.simulateQ_add_liftM_right]
theorem submission_complete (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (S : SourceFacts) : (submission I).Complete := by
  intro sk
  have hP : Pr[fun summary => summary.allSucceed = true | withRandomOracle ((submission I).allMessages sk)] =
      Pr[= true | withRandomOracle (mrealize sk foldB)] := by
    rw [← allSucceed_eq E F P sk, withRandomOracle_map', ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  have hB : Pr[= true | withRandomOracle (mrealize sk foldB)] =
      Pr[= true | withRandomOracle (mrealize sk foldC)] :=
    probOutput_congr_evalSPMF (randomOracle_congr _ _ (eval_foldB E F sk)) true
  rw [hP, hB, withRandomOracle_core E F S sk]
  exact S.source_completeness sk
end ClaudeWCT.W9.T3M.Final.Paired
end
section
set_option Elab.async false
open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal OracleComp.EvalDist
namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize privateInput)
open SigGolfCandidate.Research.SharedForest (Signature Witness sign expand verify)
open SigGolfCandidate.T3M (mrealize cacheB cacheDec cacheDec_cacheB isHash isPublic)
open SigGolfCandidate.T3M.Final (mrealize_public randomOracle_congr expectedValue_congr_evalSPMF)
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.Paired.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local irreducible] SigGolfCandidate.T3.keygen SigGolfCandidate.T3.keygenPayload
  SigGolfCandidate.T3.privateMac SigGolfCandidate.Research.SharedForest.sign cacheB cacheDec SigGolfCandidate.T3.cacheBytes
set_option maxRecDepth 100000 in
theorem allQ_honestSignCount (E : EncodingFacts) (F : SourceQueries) {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (m : SigGolfCandidate.T3.Message) :
    AllQueriesSatisfy (SigGolfCandidate.Research.SharedSigningBudget.honestSignCount m) Q :=
  SigGolfCandidate.T3M.allQ_bind hk fun _ => allQ_countWith _ (hs _ _)
set_option maxRecDepth 100000 in
theorem allQ_honestJointCounts (E : EncodingFacts) (F : SourceQueries) {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (he : ∀ m pk σ, AllQueriesSatisfy (expand m pk σ) Q)
    (m : SigGolfCandidate.T3.Message) :
    AllQueriesSatisfy (SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts m) Q := by
  unfold SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts SigGolfCandidate.T3.ExpansionClosure.jointCounts
  refine SigGolfCandidate.T3M.allQ_bind hk fun keys =>
    SigGolfCandidate.T3M.allQ_bind (allQ_countWith _ (hs _ _)) fun signed => ?_
  rcases signed with ⟨_ | sig, n⟩
  · exact SigGolfCandidate.T3M.allQ_pure _
  · exact SigGolfCandidate.T3M.allQ_bind (allQ_countWith _ (he _ _ _)) fun _ => SigGolfCandidate.T3M.allQ_pure _
variable {I : Images}
theorem abstract_sign_raw (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (cache : Bytes 131072)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .sign (sk,cache,m))).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign (cacheDec cache) m)))).2 := by
  exact abstract_count_refinement sk hash (sign (cacheDec cache) m)
    ((submission I).run .sign (sk,cache,m)) (Option.map sigBC)
    (P.sign_refines sk cache m) (F.good_sign _ _)
theorem abstract_sign_encoded (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .sign (sk,cacheB cache,m))).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign cache m)))).2 := by
  have h := abstract_sign_raw E F P sk (cacheB cache) m hash
  rw [cacheDec_cacheB] at h
  exact h
theorem abstract_sign_raw_value (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (cache : Bytes 131072)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .sign (sk,cache,m))).value =
      Option.map sigBC (evalWithAnswerFn hash (mrealize sk (sign (cacheDec cache) m))) := by
  exact (eval_of_counts (F := Option.map sigBC) (P.sign_refines sk cache m) hash).1
theorem abstract_sign_encoded_value (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .sign (sk,cacheB cache,m))).value =
      Option.map sigBC (evalWithAnswerFn hash (mrealize sk (sign cache m))) := by
  have h := abstract_sign_raw_value E F P sk (cacheB cache) m hash
  rw [cacheDec_cacheB] at h
  exact h
theorem abstract_expand_raw_cost (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (m : Message) (pk : PublicKey)
    (sig : Bytes 5195) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .expand (m,pk,sig))).hashCompressions =
      (evalWithAnswerFn hash (mrealize 0 (SigGolfCandidate.T3.Cost.countBlocks (expandN m pk (sigDecC sig))))).2 := by
  exact abstract_count_refinement 0 hash (expandN m pk (sigDecC sig))
    ((submission I).run .expand (m,pk,sig))
    (Option.map (fun x : SigGolfCandidate.T3.HashOutput × Witness => witEncN x.1 x.2))
    (P.expand_refines m pk sig) (F.good_expandN _ _ _)
theorem abstract_expand_encoded_cost (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (m : Message) (pk : PublicKey)
    (sig : Signature) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .expand (m,pk,sigBC sig))).hashCompressions =
      (evalWithAnswerFn hash (mrealize 0 (SigGolfCandidate.T3.Cost.countBlocks (expandN m pk (SigGolfCandidate.Research.SharedForest.normTop sig))))).2 := by
  have h := abstract_expand_raw_cost E F P m pk (sigBC sig) hash
  rw [E.sig_roundtrip] at h
  exact h
theorem eval_expand_blocks (E : EncodingFacts) (F : SourceQueries) (answers : SigGolfCandidate.T3.Correctness.Answers) (m : SigGolfCandidate.T3.Message)
    (pk : Digest) (σ : Signature) :
    (evalWithAnswerFn answers (SigGolfCandidate.T3.Cost.countBlocks (expand m pk σ))).2 =
      (evalWithAnswerFn answers (SigGolfCandidate.T3.Cost.countBlocks (expandN m pk (SigGolfCandidate.Research.SharedForest.normTop σ)))).2 := by
  unfold SigGolfCandidate.T3.Cost.countBlocks
  rw [ClaudeWCT.W9.T3M.Paired.expand_eq_expandN, countWith_map', evalWithAnswerFn_map]
set_option maxRecDepth 100000 in
theorem sign_count_value (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    ((submission I).runWith hash .sign (sk,cacheB cache,m)).value =
      Option.map sigBC (evalWithAnswerFn hash
        (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign cache m)))).1 := by
  have h := abstract_sign_encoded_value E F P sk cache m hash
  rw [eval_mrealize hash sk (SigGolfCandidate.T3.Cost.countBlocks (sign cache m)), SigGolfCandidate.T3.Cost.countBlocks,
    eval_cost_fst, ← eval_mrealize hash sk (sign cache m)]
  exact h
set_option maxRecDepth 100000 in
theorem expand_count_cost (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (m : Message)
    (pk : PublicKey) (sig : Signature) (hash : Hash) :
    ((submission I).runWith hash .expand (m,pk,sigBC sig)).hashCompressions =
      evalWithAnswerFn hash (Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (expand m pk sig))) := by
  have h := abstract_expand_encoded_cost E F P m pk sig hash
  have hp : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countBlocks (expandN m pk (SigGolfCandidate.Research.SharedForest.normTop sig))) isPublic :=
    allQ_countWith SigGolfCandidate.T3.Cost.weight (F.public_expandN m pk (SigGolfCandidate.Research.SharedForest.normTop sig))
  rw [mrealize_public 0 sk hp, eval_mrealize] at h
  rw [evalWithAnswerFn_map, eval_mrealize, eval_expand_blocks E F]
  exact h
/-- The keygen cost of the honest pipeline is the keygen run's compression count (stated for an arbitrary submission so
the kernel never unfolds the concrete images; r3h). -/
theorem costs_keygen_generic (S : SigGolfCandidate.Legacy.Submission) (hash : Hash) (sk : SecretKey) (m : Message)
    (X : Nat) (h : (S.runWith hash .keygen sk).hashCompressions = X) :
    evalWithAnswerFn hash ((fun r => r.costs .keygen) <$> S.honest sk m) = X := by
  rw [evalWithAnswerFn_map, SigGolfCandidate.T3M.Final.eval_costs_keygen, h]
/-- Generic in the program (instantiating it at `keygen` keeps the kernel from evaluating keygen; r3h). -/
theorem countBoth_tail {α : Type} (sk : SecretKey) (hash : Hash) (p : M α)
    (hp : AllQueriesSatisfy p SigGolfCandidate.T3.Cost.GoodQuery) :
    (evalWithAnswerFn hash (SigGolfCandidate.T3M.countBoth (mrealize sk p))).2.2 =
      evalWithAnswerFn hash ((fun r => r.2) <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks p)) := by
  rw [evalWithAnswerFn_map, ← mrealize_countBlocks sk hp,
    ← SigGolfCandidate.T3M.countBoth_blocks, evalWithAnswerFn_map]
set_option maxRecDepth 100000 in
/-- img-v6: keygen's honest cost is the spec count `countBlocks keygen` (data dependent). -/
theorem costs_keygen_eval (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .keygen) <$> (submission I).honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks keygen)) :=
  (costs_keygen_generic (submission I) hash sk m _ (P.keygen_runWith hash sk).2.2.2.2).trans
    (countBoth_tail sk hash keygen SigGolfCandidate.T3M.goodQ_keygen)
set_option maxRecDepth 100000 in
theorem costs_sign_eval (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .sign) <$> (submission I).honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$> mrealize sk (SigGolfCandidate.Research.SharedSigningBudget.honestSignCount m)) := by
  have hk : ((submission I).runWith hash .keygen sk).value =
      some ((evalWithAnswerFn hash (mrealize sk keygen)).1,
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) :=
    (P.keygen_runWith hash sk).1
  have h := generic_outer_sign_cost (submission I) hash sk m (mrealize sk keygen)
    (fun key => (key.1, cacheB key.2))
    (fun key => Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign key.2 m))) hk
    (fun key => (abstract_sign_encoded E F P sk key.2 m hash).trans
      (evalWithAnswerFn_map hash Prod.snd _).symm)
  exact h.trans (congrArg (evalWithAnswerFn hash)
    (generic_count_pipeline sk keygen (fun key => SigGolfCandidate.T3.Cost.countBlocks (sign key.2 m)) Prod.snd))
set_option maxRecDepth 100000 in
theorem costs_expand_eval (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .expand) <$> (submission I).honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$>
        mrealize sk (SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts m)) := by
  have hk : ((submission I).runWith hash .keygen sk).value =
      some ((evalWithAnswerFn hash (mrealize sk keygen)).1,
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) :=
    (P.keygen_runWith hash sk).1
  have h := generic_outer_expand_cost (submission I) hash sk m (mrealize sk keygen)
    (fun key => (key.1, cacheB key.2))
    (fun key => mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign key.2 m))) Prod.fst sigBC
    (fun key sig => Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (expand m key.1 sig)))
    hk (fun key => sign_count_value E F P sk key.2 m hash)
    (fun key sig => expand_count_cost E F P sk m key.1 sig hash)
  exact h.trans (congrArg (evalWithAnswerFn hash)
    (generic_joint_count_pipeline sk keygen (fun key => sign key.2 m)
      (fun key sig => expand m key.1 sig)))
theorem keygen_bound (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (S : SourceFacts) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countBlocks keygen) SigGolfCandidate.T3.Cost.GoodQuery :=
    allQ_countWith SigGolfCandidate.T3.Cost.weight SigGolfCandidate.T3M.goodQ_keygen
  have hhash : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countBlocks keygen) isHash :=
    allQ_countWith SigGolfCandidate.T3.Cost.weight S.hashOnly_keygen
  have h := randomOracle_congr _ _ (costs_keygen_eval E F P sk m)
  calc expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .keygen) <$> (submission I).honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.keygen.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$>
          mrealize sk (SigGolfCandidate.T3.Cost.countBlocks keygen)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.keygen.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (SigGolfCandidate.T3.Sampling.roRun sk (SigGolfCandidate.T3.Cost.countBlocks keygen) ∅)
          (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.keygen.budget = 2 ^ 20 from rfl]
        norm_num
    _ ≤ 2 := S.honest_keygen_exponential_budget sk
set_option maxRecDepth 100000 in
theorem sign_bound (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (S : SourceFacts) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (SigGolfCandidate.Research.SharedSigningBudget.honestSignCount m)
      SigGolfCandidate.T3.Cost.GoodQuery :=
    allQ_honestSignCount E F SigGolfCandidate.T3M.goodQ_keygen F.good_sign m
  have hhash : AllQueriesSatisfy (SigGolfCandidate.Research.SharedSigningBudget.honestSignCount m) isHash :=
    allQ_honestSignCount E F S.hashOnly_keygen S.hashOnly_sign m
  have h := randomOracle_congr _ _ (costs_sign_eval E F P sk m)
  calc expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .sign) <$> (submission I).honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.sign.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$>
          mrealize sk (SigGolfCandidate.Research.SharedSigningBudget.honestSignCount m)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.sign.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (SigGolfCandidate.T3.Sampling.roRun sk (SigGolfCandidate.Research.SharedSigningBudget.honestSignCount m) ∅)
          (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.sign.budget = 2 ^ 17 from rfl]
        norm_num
    _ ≤ 2 := S.honest_sign_exponential_budget sk m
set_option maxRecDepth 100000 in
theorem expand_bound (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (S : SourceFacts) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts m)
      SigGolfCandidate.T3.Cost.GoodQuery :=
    allQ_honestJointCounts E F SigGolfCandidate.T3M.goodQ_keygen F.good_sign F.good_expand m
  have hhash : AllQueriesSatisfy (SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts m) isHash :=
    allQ_honestJointCounts E F S.hashOnly_keygen S.hashOnly_sign S.hashOnly_expand m
  have h := randomOracle_congr _ _ (costs_expand_eval E F P sk m)
  calc expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .expand) <$> (submission I).honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.expand.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$>
          mrealize sk (SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts m)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.expand.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (SigGolfCandidate.T3.Sampling.roRun sk
          (SigGolfCandidate.Research.SharedExpansionClosure.honestJointCounts m) ∅)
          (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.expand.budget = 2 ^ 20 from rfl]
        norm_num
    _ ≤ 2 := S.honest_expand_exponential_budget sk m
theorem submission_compressionBounds (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (S : SourceFacts) : (submission I).CompressionBounds := by
  intro sk phase hphase
  unfold Submission.honestWorkload
  refine expectedValue_bind_le_of_le fun m => ?_
  simp only [Phase.budgeted, List.mem_cons, List.not_mem_nil, or_false] at hphase
  rcases hphase with rfl | rfl | rfl
  · exact keygen_bound E F P S sk m
  · exact sign_bound E F P S sk m
  · exact expand_bound E F P S sk m
end ClaudeWCT.W9.T3M.Final.Paired
end

namespace ClaudeWCT.W9.T3M.Final.Paired

theorem encodingFacts : EncodingFacts where
  sig_roundtrip := ClaudeWCT.W9.T3M.SharedCodec.sigDecC_sigBC_normTop
  expandN_fill := ClaudeWCT.W9.T3M.Paired.expandN_fillTopSignature
  honest_eval := ClaudeWCT.W9.T3M.Paired.honestB_eval
end ClaudeWCT.W9.T3M.Final.Paired

namespace ClaudeWCT.W9.T3M.Paired
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Research.SharedForest
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def recoveredWitness (w : SigGolfCandidate.Research.SharedForest.Witness) (output : HashOutput) :
    M (Option RecoveredLayers) := do
  let forest ← recoverForest (WCT9.digestIndex output) (forestSelectionFromOutput output)
    (forestWordsFromOutput output) w.signature.forest
  recoverHintedLayers w.signature (WCT9.digestIndex output) ((w.signature.layers 0).path WCT9.topJ)
    4 (.pair forest.1 forest.2) (conditionalTopFloor output)

theorem expandN_recovered (answers : Correctness.Answers) (message : Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn answers (expandN message pk sig)=some (output,w)) :
    ∃ result,evalWithAnswerFn answers (recoveredWitness w output)=some result ∧
      policyHintsValid w.signature.policyHints result.digits result.lows
        (conditionalCredit output)=true ∧
      (∀lay,w.counters lay=result.counters.getD lay.val 0) ∧
      evalWithAnswerFn answers (digest w.signature.rho message w.digestCounter)=output ∧
      digestAccepted output=true ∧ w.topHigh = !(result.lows.getD 0 true) := by
  obtain ⟨_,counter,result,c,hs,hr,hh,hw,hc,hcs,htop⟩ := expandN_selections answers message pk sig output w he
  let index := WCT9.digestIndex output
  let forest := evalWithAnswerFn answers (recoverForest index (forestSelectionFromOutput output)
    (forestWordsFromOutput output) sig.forest)
  let other := ((fillTopSignature sig 0).layers 0).path WCT9.topJ
  let other' := ((fillTopSignature sig c).layers 0).path WCT9.topJ
  let result' : RecoveredLayers := {result with root:=evalWithAnswerFn answers (WCT9.topNode index result.foldedTop other')}
  have hr0 : evalWithAnswerFn answers (recoverHintedLayers sig index other 4 (.pair forest.1 forest.2)
      (conditionalTopFloor output))=some result := by
    rw [recoverHintedLayers_fill_at _ _ _ _ (conditionalTopFloor output) _ (by decide)] at hr
    exact hr
  have hr1 := eval_recoverHintedLayers_other_at answers sig index other other'
    (conditionalTopFloor output) 4 (.pair forest.1 forest.2)
  rw [hr0] at hr1
  have hr2 : evalWithAnswerFn answers (recoverHintedLayers (fillTopSignature sig c) index other'
      4 (.pair forest.1 forest.2) (conditionalTopFloor output))=some result' := by
    rw [recoverHintedLayers_fill_at _ _ _ _ (conditionalTopFloor output) _ (by decide)]
    exact hr1
  have hs' := sharedDigestSearch_some answers sig.rho message WCT9.digestAttemptLimit 0
    counter output (by decide) hs
  refine ⟨result',?_,?_,?_,?_,hs'.2.2.1,htop⟩
  · rw [recoveredWitness,evalWithAnswerFn_bind,hw]
    exact hr2
  · rw [hw,hints_retained]
    exact hh
  · exact hcs
  · rw [hw,hc,nonce_retained]
    exact hs'.2.2.2
end ClaudeWCT.W9.T3M.Paired
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_BridgeMain ====
section

open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal
-- r3h HonestN: legacy (5310) bridge removed with the legacy Budgets pipeline (uses the deleted legacy codec).

section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open OracleSpec OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal
namespace ClaudeWCT.W9.T3M.Final.Paired
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize)
open SigGolfCandidate.T3.Security (Request)

open SigGolfCandidate.Research.SharedForest (Signature)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open SigGolfCandidate.T3M (cacheB cacheDec toQ ofQ)
open SigGolfCandidate.T3M.Final (AW AHash hrealize hrealize_public)
open ClaudeWCT.W9.T3M (Images)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.Paired.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local instance] Classical.propDecidable
variable {I : Images}
def Inv (T : Transcript (submission I).sizes) (k : ℕ) (lg : QueryLog Requests) (c : ℕ) : Prop :=
  T.hashCalls = c ∧ T.signingRequests = k ∧ lg.length = k ∧ k ≤ LIFETIME ∧
    ∀ e ∈ lg, ∀ σ : Signature, e.2 = some σ → (e.1.message, sigBC σ) ∈ T.signed
lemma length_of_inv {T : Transcript (submission I).sizes} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (hI : Inv T k lg c) : decide (lg.length ≤ 2 ^ 32) = true := by
  obtain ⟨-, -, hlen, hk, -⟩ := hI
  exact decide_eq_true (hlen ▸ hk)
lemma freshW_of_inv {T : Transcript (submission I).sizes} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (hI : Inv T k lg c) {m : Message} (hfresh : T.freshMessage m = true) : freshW lg m = true := by
  rw [freshW_iff]
  rintro ⟨e, he, h1, h2⟩
  rcases hs : e.2 with _ | σ
  · rw [hs] at h2; cases h2
  · have hmem := hI.2.2.2.2 e he σ hs
    rw [h1] at hmem
    unfold Transcript.freshMessage at hfresh
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hfresh
    exact hfresh _ hmem rfl
lemma freshS_of_inv {T : Transcript (submission I).sizes} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (hI : Inv T k lg c) {m : Message} {s : Bytes (submission I).sizes.signature}
    (hfresh : T.freshSignature m s = true) : freshS lg m (sigDecC s) = true := by
  rw [freshS_iff]
  rintro ⟨e, he, h1, h2⟩
  obtain ⟨σ', hσ', hp⟩ := ClaudeWCT.WCT9.map_some_inv h2
  have hmem := hI.2.2.2.2 e he σ' hσ'
  have hs : sigBC σ' = s := hp.trans (ClaudeWCT.W9.T3M.SharedCodec.sigBC_sigDecC s)
  rw [h1, hs] at hmem
  unfold Transcript.freshSignature at hfresh
  simp only [Bool.not_eq_true'] at hfresh
  have : T.signed.contains (m, s) = true := List.contains_iff_mem.mpr hmem
  rw [this] at hfresh
  cases hfresh
lemma inv_record {T : Transcript (submission I).sizes} {k : ℕ} {lg : QueryLog Requests} {c : ℕ}
    (hI : Inv T k lg c) (hk : k < LIFETIME) (m : Message) (cache : Cache)
    (r : Option Signature) (calls : ℕ) :
    Inv (recordVC T m (r.map sigBC) calls) (k + 1)
      (lg ++ [⟨⟨m, cache⟩, r⟩]) (c + calls) := by
  obtain ⟨hc, hs, hlen, -, hent⟩ := hI
  refine ⟨by simp [recordVC, hc], by simp [recordVC, hs], by simp [hlen], hk, ?_⟩
  intro e he σ hσ
  rw [List.mem_append] at he
  rcases he with he | he
  · have hmem := hent e he σ hσ
    cases r <;> simp [recordVC, hmem]
  · rw [List.mem_singleton] at he
    subst he
    change r = some σ at hσ
    subst hσ
    simp [recordVC]
variable (I) (A : Adversary (submission I).sizes)
theorem rel_main (F : QFacts) (P : Pending I) (sk : SecretKey) (pk : Digest) :
    ∀ (n : ℕ) (s : A.State) (T : Transcript (submission I).sizes) (k : ℕ) (lg : QueryLog Requests) (c : ℕ),
      Inv T k lg c → Rel (orgK I A sk (pk : PublicKey) n s T) (absK I A sk pk n s k lg c) RFin := by
  intro n
  induction n with
  | zero =>
    intro s T k lg c _
    rw [orgK_zero]
    exact Rel.pure_left _ _ (rfin_false _)
  | succ n ih =>
    intro s T k lg c hI
    cases hstep : A.step s with
    | submit f =>
      cases f with
      | witness m w =>
        rw [orgK_submit_witness F P hstep, absK_submit_witness F hstep, liftM_countFrom_shift,
          hrealize_public 0 sk (F.public_verifyP _ _ _), Functor.map_map, liftM_map]
        refine Rel.of_map _ _ _ fun z => ?_
        intro hwon
        simp only [Bool.and_eq_true] at hwon
        refine ⟨?_, ?_⟩
        · simp only [length_of_inv hI, freshW_of_inv hI hwon.2, hwon.1, Bool.true_and]
        · simp [hI.1]
      | signature m σ =>
        rw [orgK_submit_signature F P hstep, absK_submit_signature F hstep, liftM_countFrom_shift,
          hrealize_public 0 sk (F.public_expandB _ _ _), bind_map_left]
        refine Rel.bind_eq _ fun p => ?_
        rcases p with ⟨_ | w, e⟩
        · exact Rel.pure_left _ _ (rfin_false _)
        · simp only
          rw [liftM_countFrom_shift, hrealize_public 0 sk (F.public_verifyP _ _ _), Functor.map_map,
            liftM_map]
          refine Rel.of_map _ _ _ fun z => ?_
          intro hwon
          simp only [Bool.and_eq_true] at hwon
          refine ⟨?_, ?_⟩
          · simp only [length_of_inv hI, freshS_of_inv hI hwon.2, hwon.1, Bool.true_and]
          · simp [hI.1, Nat.add_assoc]
    | hash y resume =>
      rw [orgK_hash hstep, absK_hash hstep]
      refine Rel.bind_eq _ fun a => ih _ _ _ _ _ ?_
      obtain ⟨hc, hs, hlen, hk, hent⟩ := hI
      exact ⟨by simp [hc], hs, hlen, hk, hent⟩
    | sample m resume =>
      rw [orgK_sample hstep, absK_sample hstep]
      exact Rel.bind_eq _ fun a => ih _ _ _ _ _ hI
    | step next =>
      rw [orgK_step hstep, absK_step hstep]
      exact ih _ _ _ _ _ hI
    | sign req resume =>
      by_cases hk : T.signingRequests < LIFETIME
      · have hk' : k < LIFETIME := hI.2.1 ▸ hk
        rw [orgK_sign_lt F P hstep hk, absK_sign_lt F hstep hk', liftM_countFrom_shift, bind_map_left]
        refine Rel.bind_eq _ fun p => ih _ _ _ _ _ ?_
        exact inv_record hI hk' req.message _ p.1 p.2
      · rw [orgK_sign_ge hstep hk]
        exact Rel.pure_left _ _ (rfin_false _)
theorem realExperimentP_eq (F : QFacts) (rounds : ℕ) :
    realExperimentP (reductionP I A rounds) =
      SphincsSecurity.sampleMasterSeed >>= fun secret =>
        (simulateQ (roImpl (List UInt8) (BitVec 256))
          ((liftM (countFrom (fun _ => 1) (hrealize secret keygen) 0) : OracleComp AW _) >>= fun p =>
            absK I A secret p.1.1 rounds (A.initial (p.1.1 : PublicKey) (cacheB p.1.2)) 0 [] p.2)).run' ∅ := by
  unfold realExperimentP
  refine bind_congr fun secret => ?_
  rw [derivation_realize, countHashQueries_eq, src_top F secret rounds]
  rfl
theorem probEvent_le (F : QFacts) (P : Pending I) (rounds Q : ℕ) :
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ Q | (submission I).securityExperiment A rounds] ≤
      Pr[fun r => r.1 = true ∧ r.2 ≤ Q | realExperimentP (reductionP I A rounds)] := by
  rw [securityExperiment_eq I A F P rounds, realExperimentP_eq I A F rounds]
  unfold orgGame
  rw [simulateQ_bind, roSim.run'_liftM_bind, ← sampleSecretKey_eq]
  refine probEvent_bind_le' _ fun sk => ?_
  refine Rel.probEvent_le (R := RFin) (roImpl (List UInt8) (BitVec 256)) ?_ _ _ ?_ ∅
  · refine Rel.bind_eq _ fun a => ?_
    exact rel_main I A F P sk a.1.1 rounds _ _ 0 [] a.2 ⟨rfl, rfl, rfl, Nat.zero_le _, by simp⟩
  · intro r b hR hE
    obtain ⟨h1, h2⟩ := hR hE.1
    exact ⟨h1, h2 ▸ hE.2⟩
variable {I}
theorem submission_secure (E : EncodingFacts) (F : SourceQueries) (P : Pending I) (hS : SecurityP) : (submission I).Secure := by
  intro A rounds Q hQ
  calc _ ≤ _ := probEvent_le I A (qFacts F) P rounds Q
    _ ≤ (Q : ℝ≥0∞) / 2 ^ 127 := hS _ Q hQ
    _ = (Q : ℝ≥0∞) / 2 ^ SECURITY_BITS := rfl
end ClaudeWCT.W9.T3M.Final.Paired

end
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_CompletenessV6 ====
section

/-! # img-v6 source completeness with the 5,239-byte codec (r3-lean-topbytes)

`expand` normalizes the top path, so an honest signature expands only if every keygen top node passed its zero test
(`TopTreeOK`). The check `topCheck` runs first (it does not change the distribution of `everyMessageProgram`,
`evalDist_presample_computation`); then

`Pr[everyMessageProgram = false] ≤ Pr[checkedOK = false] + Pr[topCheck = false] ≤ 2^-138 + 2^-135 ≤ 2^-128`,

where `checkedOK = (!topCheck || everyMessageProgram)` is handled by the presampled-table argument (as before) and
`topCheck` by the cap-exhaustion bound `TopMoment.Ev_buildTopTree_bad`. -/

namespace ClaudeWCT.W9.T3.Completeness.Paired
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload
open SigGolfCandidate.T3.Correctness
open SigGolfCandidate.T3.SourceReplay
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity.Completeness
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler

open Classical in
/-- Did every keygen top node pass its zero test? -/
noncomputable def topCheck : M Bool := do
  let levels ← buildTopTree
  pure (decide (ClaudeWCT.W9.T3.TopMoment.TopLevelsOK levels))

noncomputable def checkedProgram : M (Bool × Bool) := do
  let g ← topCheck
  let b ← everyMessageProgram
  pure (g, b)

noncomputable def checkedOK : M Bool := (fun p : Bool × Bool => !p.1 || p.2) <$> checkedProgram

theorem hashOnly_topCheck : HashOnly topCheck :=
  hashOnly_bind hashOnly_buildTopTree fun _ => hashOnly_pure _

theorem hashOnly_checkedOK : HashOnly checkedOK :=
  hashOnly_map _ (hashOnly_bind hashOnly_topCheck fun _ =>
    hashOnly_bind hashOnly_everyMessageProgram fun _ => hashOnly_pure _)

open Classical in
theorem eval_topCheck (answers : Answers) :
    evalWithAnswerFn answers topCheck = decide (TopTreeOK answers) := by
  unfold topCheck
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_buildTopTree]
  rfl

theorem checkedOK_true_of_complete (answers : Answers)
    (hcomplete : SigningComplete answers (evalWithAnswerFn answers keygen).2) :
    evalWithAnswerFn answers checkedOK = true := by
  classical
  unfold checkedOK checkedProgram
  simp only [evalWithAnswerFn_map, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_topCheck]
  by_cases htree : TopTreeOK answers
  · simp [htree, everyMessageProgram_true_of_complete answers hcomplete htree]
  · simp [htree]

theorem checked_prepared_failure_zero (secret : BitVec 256)
    (nonces : NonceSampling.NonceOutputs) (outputs : NonceSampling.SearchOutputs)
    (hgood : TableGoodForNonces (fun message => (nonces message).extractLsb' 0 128) outputs) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret checkedOK)).run'
        (NonceSampling.preparedCache secret nonces outputs)]=0 := by
  refine SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret checkedOK _ ?_
  intro hash hagree
  have hsearch : Budgets.SearchAgreement outputs (fixedAnswers secret hash) := by
    intro key
    change hash (searchQuery key)=outputs key
    exact hagree (NonceSampling.preparedCache_search secret nonces outputs key)
  have hnonce : ∀ message, evalWithAnswerFn (fixedAnswers secret hash) (privateNonce message)=
      (nonces message).extractLsb' 0 128 := by
    intro message
    have h := hagree (NonceSampling.preparedCache_nonce secret nonces outputs message)
    exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) h
  have hcomplete := tableGoodForNonces_signing outputs (fixedAnswers secret hash)
    (fun message => (nonces message).extractLsb' 0 128) hgood hsearch hnonce
  exact (fixed_replay secret hash _ hashOnly_checkedOK).trans
    (congrArg (pure : Bool → ProbComp Bool) (checkedOK_true_of_complete _ hcomplete))

theorem checked_failure_small (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret checkedOK)).run' ∅]≤
        1/(2:ENNReal)^138 := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false))
    (NonceSampling.presample_source secret checkedOK)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_of_forall_le
  intro nonces _
  refine (probEvent_bind_le_probEvent
    (p:=fun outputs => ¬TableGoodForNonces (fun message => (nonces message).extractLsb' 0 128) outputs)
    (fun outputs _ hgood => checked_prepared_failure_zero secret nonces outputs (not_not.mp hgood))).trans ?_
  exact tableGoodForNonces_failure _

/-- The top check fails with probability at most `2^-135` (cap exhaustion). -/
theorem topCheck_failure_small (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret topCheck)).run' ∅] ≤ ENNReal.ofReal (1 / 2 ^ 135) := by
  classical
  refine le_trans (le_of_eq ?_) (ClaudeWCT.W9.T3.TopMoment.Ev_buildTopTree_bad secret)
  rw [StateT.run'_eq]
  change Pr[fun value => value = false | Prod.fst <$> Sampling.roRun secret topCheck ∅] = _
  unfold topCheck
  rw [Sampling.roRun_bind, map_bind, probEvent_bind_eq_tsum]
  unfold ClaudeWCT.W9.T3.TopMoment.Ev
  rw [expectedValue_def]
  refine tsum_congr fun r => ?_
  rw [Sampling.roRun_pure, map_pure, probEvent_pure]
  congr 1
  by_cases h : ClaudeWCT.W9.T3.TopMoment.TopLevelsOK r.1 <;> simp [h]

/-- Running the top check first does not change the law of `everyMessageProgram`; on the joint run a failure of
`everyMessageProgram` is a failure of `checkedOK` or of `topCheck`. -/
theorem everyMessage_failure_le (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] ≤
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret checkedOK)).run' ∅] +
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret topCheck)).run' ∅] := by
  classical
  -- the joint law
  set A := Sampling.roRun secret topCheck ∅ with hA
  set J : ProbComp (Bool × Bool) := A >>= fun r =>
    (fun b => (r.1, b)) <$> (Prod.fst <$> Sampling.roRun secret everyMessageProgram r.2) with hJ
  have hev : 𝒮[(simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] =
      𝒮[Prod.snd <$> J] := by
    rw [SphincsSecurity.Seeded.evalDist_presample_computation (realize secret everyMessageProgram)
      (realize secret topCheck) ∅]
    rw [hJ, map_bind]
    simp only [Functor.map_map]
    rfl
  have hck : (simulateQ SphincsSecurity.romImpl (realize secret checkedOK)).run' ∅ =
      (fun p : Bool × Bool => !p.1 || p.2) <$> J := by
    rw [StateT.run'_eq]
    change Prod.fst <$> Sampling.roRun secret checkedOK ∅ = _
    unfold checkedOK checkedProgram
    rw [Sampling.roRun_map, Sampling.roRun_bind, hJ]
    simp only [Sampling.roRun_pure, Sampling.roRun_map, map_bind, Functor.map_map,
      bind_pure_comp]
    rfl
  have htc : (simulateQ SphincsSecurity.romImpl (realize secret topCheck)).run' ∅ = Prod.fst <$> A := by
    rw [StateT.run'_eq]; rfl
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false)) hev
  simp only [probEvent_evalSPMF] at hp
  rw [hp, hck, htc, probEvent_map, probEvent_map, probEvent_map]
  refine le_trans (probEvent_mono'' (q := fun x : Bool × Bool => (!x.1 || x.2) = false ∨ x.1 = false)
    (fun x hx => by cases x.1 <;> simp_all)) ?_
  refine le_trans (probEvent_or_le _ _ _) (add_le_add le_rfl ?_)
  rw [hJ]
  refine probEvent_bind_le_probEvent (p := fun r : Bool × Sampling.RCache => r.1 = false) (fun r _ hr => ?_)
  rw [probEvent_map]
  have : r.1 = true := by simpa using hr
  simp [Function.comp_def, this]

theorem everyMessage_failure_small (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] ≤
        1/(2:ENNReal)^128 := by
  refine (everyMessage_failure_le secret).trans ?_
  refine le_trans (add_le_add (checked_failure_small secret) (topCheck_failure_small secret)) ?_
  have h135 : ENNReal.ofReal (1 / 2 ^ 135) = 1 / (2 : ENNReal) ^ 135 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [h135]
  have h1 : 1/(2:ENNReal)^138 ≤ 1/(2:ENNReal)^129 :=
    ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _
  have h2 : 1/(2:ENNReal)^135 ≤ 1/(2:ENNReal)^129 :=
    ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by norm_num)) _
  have h3 : 1/(2:ENNReal)^129 + 1/(2:ENNReal)^129 = 1/(2:ENNReal)^128 := by
    rw [← two_mul, pow_succ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, ← mul_assoc,
      mul_comm (2 : ENNReal) ((2 : ENNReal) ^ 128)⁻¹, mul_assoc ((2 : ENNReal) ^ 128)⁻¹ 2 2⁻¹,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  exact (add_le_add h1 h2).trans (le_of_eq h3)

theorem source_completeness (secret : BitVec 256) :
    1-1/(2:ENNReal)^128≤
      Pr[=true | (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] := by
  have hf := everyMessage_failure_small secret
  rw [probEvent_eq_eq_probOutput] at hf
  rw [probOutput_true_eq_sub]
  simp only [probFailure_eq_zero,tsub_zero]
  exact tsub_le_tsub_left hf 1
end ClaudeWCT.W9.T3.Completeness.Paired
end
-- ==== merged from T3M_Verify_HashAgree ====
section

namespace SigGolfCandidate.T3M.Verify
open OracleComp OracleSpec SigGolfCandidate.Legacy
def Agree (f g : Hash) {α : Type} (oa : OracleComp HashSpec α) : Prop :=
  OracleComp.recOn oa (fun _ => True) (fun t _ ih => f t = g t ∧ ih (f t))
variable {f g : Hash}
theorem agree_pure {α : Type} (a : α) : Agree f g (pure a : OracleComp HashSpec α) := trivial
theorem agree_query_bind {α : Type} (q : Query) (k : BitVec 256 → OracleComp HashSpec α) :
    Agree f g ((liftM (HashSpec.query q) : OracleComp HashSpec _) >>= k) ↔ f q = g q ∧ Agree f g (k (f q)) :=
  Iff.rfl
theorem eval_liftQ (h : Hash) (q : Query) :
    evalWithAnswerFn h (liftM (OracleSpec.query q) : OracleComp HashSpec _) = h q := by
  simp [evalWithAnswerFn]
theorem agree_eval {α : Type} {oa : OracleComp HashSpec α} (h : Agree f g oa) :
    evalWithAnswerFn f oa = evalWithAnswerFn g oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    obtain ⟨hq, hk⟩ : f q = g q ∧ Agree f g (k (f q)) := h
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_liftQ, eval_liftQ, ← hq]
    exact ih _ hk
theorem agree_bind_iff {α β : Type} (oa : OracleComp HashSpec α) (ob : α → OracleComp HashSpec β) :
    Agree f g (oa >>= ob) ↔ Agree f g oa ∧ Agree f g (ob (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind, evalWithAnswerFn_pure]
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | query_bind q k ih =>
    rw [bind_assoc]
    show (f q = g q ∧ Agree f g (k (f q) >>= ob)) ↔ (f q = g q ∧ Agree f g (k (f q))) ∧ _
    rw [ih, evalWithAnswerFn_bind, eval_liftQ]
    tauto
theorem agree_bind {α β : Type} {oa : OracleComp HashSpec α} {ob : α → OracleComp HashSpec β}
    (h1 : Agree f g oa) (h2 : Agree f g (ob (evalWithAnswerFn f oa))) : Agree f g (oa >>= ob) :=
  (agree_bind_iff oa ob).mpr ⟨h1, h2⟩
theorem agree_map_iff {α β : Type} (h : α → β) (oa : OracleComp HashSpec α) :
    Agree f g (h <$> oa) ↔ Agree f g oa := by
  rw [map_eq_bind_pure_comp, agree_bind_iff]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', trivial⟩⟩
theorem agree_of_allQ {α : Type} {oa : OracleComp HashSpec α} (h : AllQueriesSatisfy oa (fun q => f q = g q)) :
    Agree f g oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    exact ⟨h.1, ih _ (h.2 _)⟩
def BadAns (lay : T3.Layer) (a : BitVec 256) : Prop :=
  (∃ ds, T3.decode lay (ClaudeWCT.WCT9.encodingAnswer lay a) = some ds ∧
    ClaudeWCT.WCT9.wordCredit lay ds + 4 * ClaudeWCT.WCT9.savedCopies lay ds <
      ClaudeWCT.WCT9.producerFloor lay + ClaudeWCT.WCT9.dispatchPenalty lay ds)
open Classical in
noncomputable def okHash (hash : Hash) : Hash :=
  fun q => if ∃ lay : T3.Layer, EncQ lay.val q ∧ BadAns lay (hash q) then BitVec.allOnes 256 else hash q
theorem okHash_eq (hash : Hash) {q : Query} (h : ¬ ∃ lay : T3.Layer, EncQ lay.val q ∧ BadAns lay (hash q)) :
    okHash hash q = hash q := by
  unfold okHash
  rw [if_neg h]
theorem okHash_eq_of_not_enc (hash : Hash) {q : Query} (h : ∀ lay : T3.Layer, ¬ EncQ lay.val q) :
    okHash hash q = hash q :=
  okHash_eq hash (fun ⟨lay, h', _⟩ => h lay h')
theorem decode_allOnes (lay : T3.Layer) : T3.decode lay (ClaudeWCT.WCT9.encodingAnswer lay (BitVec.allOnes 256)) = none := by
  revert lay
  decide +kernel
theorem hashOk_okHash (hash : Hash) : HashOk (okHash hash) := by
  intro lay q hq ds hds
  by_cases hb : ∃ lay' : T3.Layer, EncQ lay'.val q ∧ BadAns lay' (hash q)
  · unfold okHash at hds
    rw [if_pos hb, decode_allOnes] at hds
    cases hds
  · rw [okHash_eq hash hb] at hds
    by_contra hc
    exact hb ⟨lay, hq, ds, hds, by omega⟩
end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open OracleComp OracleSpec SigGolfCandidate.Legacy
def BadAnsBy (floors : T3.Layer → Nat) (high : Bool) (lay : T3.Layer) (a : BitVec 256) : Prop :=
  (∃ ds, ClaudeWCT.WCT9.CanonicalPolicy.decode lay (ClaudeWCT.WCT9.verificationAnswer lay high a) = some ds ∧
    ClaudeWCT.WCT9.CanonicalPolicy.pathReward lay (ClaudeWCT.WCT9.verificationLow lay high a) ds <
      floors lay + ClaudeWCT.WCT9.dispatchPenalty lay ds)
open Classical in
/-- Replace every encoding answer whose verifier-read word (for the hint `high`) is below its floor. -/
noncomputable def okHashBy (floors : T3.Layer → Nat) (high : Bool) (hash : Hash) : Hash :=
  fun q => if ∃ lay : T3.Layer, EncQ lay.val q ∧ BadAnsBy floors high lay (hash q) then BitVec.allOnes 256 else hash q
theorem okHashBy_eq (floors : T3.Layer → Nat) (high : Bool) (hash : Hash) {q : Query}
    (h : ¬ ∃ lay : T3.Layer, EncQ lay.val q ∧ BadAnsBy floors high lay (hash q)) :
    okHashBy floors high hash q = hash q := by
  unfold okHashBy
  rw [if_neg h]
theorem okHashBy_eq_of_not_enc (floors : T3.Layer → Nat) (high : Bool) (hash : Hash) {q : Query}
    (h : ∀ lay : T3.Layer, ¬ EncQ lay.val q) :
    okHashBy floors high hash q = hash q :=
  okHashBy_eq floors high hash (fun ⟨lay, h', _⟩ => h lay h')
theorem canonical_decode_allOnes (lay : T3.Layer) (high : Bool) :
    ClaudeWCT.WCT9.CanonicalPolicy.decode lay (ClaudeWCT.WCT9.verificationAnswer lay high (BitVec.allOnes 256)) = none := by
  revert lay high
  decide +kernel
theorem hashOkBy_okHashBy (floors : T3.Layer → Nat) (high : Bool) (hash : Hash) :
    HashOkBy floors high (okHashBy floors high hash) := by
  intro lay q hq ds hds
  by_cases hb : ∃ lay' : T3.Layer, EncQ lay'.val q ∧ BadAnsBy floors high lay' (hash q)
  · unfold okHashBy at hds
    rw [if_pos hb, canonical_decode_allOnes] at hds
    cases hds
  · rw [okHashBy_eq floors high hash hb] at hds ⊢
    by_contra hc
    exact hb ⟨lay, hq, ds, hds, by omega⟩
end SigGolfCandidate.T3M.Verify
end
-- ==== merged from ClaudeWCT_W9_T3M_Final_CreditBridge ====
section

section
open OracleComp OracleSpec
namespace ClaudeWCT.W9.T3M.Final.Credit
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (M Spec Layer Digest HashOutput HashInput route counterLimit decode shortHash
  publicHash pad64 header chainCount height maxDigit rowTweak nodeTweak digestHeader)
open SigGolfCandidate.T3M (mrealize mrealize_bind mrealize_map mrealize_shortHash toQ toQ_injOn Aligned PubGood
  isPublic allQ_pure allQ_bind allQ_map allQ_ite allQ_foldlM allQ_mapM)
open SigGolfCandidate.T3M.Verify (EncQ HashOk Agree agree_bind agree_bind_iff agree_map_iff agree_eval okHash
  okHash_eq okHash_eq_of_not_enc hashOk_okHash BadAns eval_liftQ)
open SigGolfCandidate.T3.Security.Wots.Enc (NonEnc nonEnc_prefixed nonEnc_chainInput nonEnc_of_hdr
  nodeTweak_ne_row rowTweak_layer hyperH_layer NotHyper notHyper_of_marker nonEnc_pad64_long leafInput_long
  chainCount_ge4)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
def NotEncS : Spec.Domain → Prop
  | .inl (.inr input) => ∀ lay : Layer, ¬ EncQ lay.val (toQ input)
  | _ => False
/-- C2/C3 (FULL): an encoding query has any row-tweak high word (EncQ), so a non-encoding query is told apart by its
length or a non-hyper 16-byte header (`NonEnc`, S23b). Adapted from b3cc11b. -/
theorem notEncS_of {input : HashInput} (hal : Aligned input) (hn : NonEnc (.inl (.inr input))) :
    NotEncS (.inl (.inr input)) := by
  rintro lay ⟨i, hi, hq, routed, hp, hb⟩
  have hi' : Aligned i := ⟨by omega, by omega⟩
  have e : input = i := toQ_injOn hal hi' hq
  refine hn ⟨by rw [e]; exact hi, lay, routed / 2 ^ height lay, routed % 2 ^ height lay, hp, ?_⟩
  rw [e, Nat.div_add_mod']
  exact hb
theorem pad64_aligned' (y : HashInput) (hy : 0 < y.length) : Aligned (pad64 y) :=
  ⟨SigGolfCandidate.T3.Cost.pad64_positive y hy, SigGolfCandidate.T3.Cost.pad64_aligned y⟩
theorem notEnc_publicHash (y : HashInput) (hy : 0 < y.length) (hn : NonEnc (.inl (.inr (pad64 y)))) :
    AllQueriesSatisfy (publicHash y) NotEncS :=
  (allQueriesSatisfy_query_iff _ _).mpr (notEncS_of (pad64_aligned' y hy) hn)
theorem notEnc_shortHash (y : HashInput) (hy : 0 < y.length) (hn : NonEnc (.inl (.inr (pad64 y)))) :
    AllQueriesSatisfy (shortHash y) NotEncS := by
  unfold shortHash
  exact allQ_bind (notEnc_publicHash y hy hn) fun _ => allQ_pure _
theorem notEnc_halfHash (high : Bool) (y : HashInput) (hy : 0 < y.length) (hn : NonEnc (.inl (.inr (pad64 y)))) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.halfHash high y) NotEncS := by
  rw [ClaudeWCT.WCT9.halfHash_eq]
  exact allQ_bind (notEnc_publicHash y hy hn) fun _ => allQ_pure _
theorem allQ_bind_support {α β : Type} {P : Spec.Domain → Prop} {p : M α} {f : α → M β}
    (hp : AllQueriesSatisfy p P) (hf : ∀ a ∈ support p, AllQueriesSatisfy (f a) P) :
    AllQueriesSatisfy (p >>= f) P := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind]
    exact hf a (by simp)
  | query_bind t mx ih =>
    rw [bind_assoc]
    rw [allQueriesSatisfy_query_bind_iff] at hp ⊢
    refine ⟨hp.1, fun u => ih u (hp.2 u) fun a ha => hf a ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩
theorem allQ_and {α : Type} {P P' : Spec.Domain → Prop} {p : M α} (h : AllQueriesSatisfy p P)
    (h' : AllQueriesSatisfy p P') : AllQueriesSatisfy p (fun q => P q ∧ P' q) := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h h' ⊢
    exact ⟨⟨h.1, h'.1⟩, fun u => ih u (h.2 u) (h'.2 u)⟩
theorem allQ_mono' {α : Type} {P P' : Spec.Domain → Prop} {p : M α} (h : AllQueriesSatisfy p P)
    (hP : ∀ q, P q → P' q) : AllQueriesSatisfy p P' := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h ⊢
    exact ⟨hP _ h.1, fun u => ih u (h.2 u)⟩
theorem notEnc_digest (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    AllQueriesSatisfy (SigGolfCandidate.T3.digest rho m c) NotEncS := by
  unfold SigGolfCandidate.T3.digest
  apply notEnc_publicHash _ (by simp [SigGolfCandidate.T3.digestInput, bytesLE_length])
  apply nonEnc_of_hdr _ (digestHeader c) _
    (notHyper_of_marker (by rw [SigGolfCandidate.T3.digestHeader_marker]; decide))
  unfold SigGolfCandidate.T3.digestInput
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
theorem notEnc_recoverFts (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (output : HashOutput) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.recoverFts sig index output) NotEncS := by
  have h1 : AllQueriesSatisfy (ClaudeWCT.WCT9.recoverFts sig index output) (ClaudeWCT.WCT9.FtsQuery index) :=
    ClaudeWCT.WCT9.allQueriesSatisfy_of_bound (ClaudeWCT.WCT9.ftsBound_recoverFts index sig output)
  have h2 := ClaudeWCT.W9.T3M.pubGood_recoverFts sig index output
  refine allQ_mono' (allQ_and h1 h2) ?_
  rintro ((n | input) | c) ⟨hf, hg⟩
  · exact hg.1.elim
  · exact notEncS_of ⟨hg.2.1, hg.2.2⟩ (ClaudeWCT.WCT9.Wots.ftsQuery_nonEnc hf)
  · exact hg.1.elim
theorem notEnc_chain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.chain lay tree leaf i start count v) NotEncS :=
  allQ_foldlM _ _ (fun _ _ => notEnc_shortHash _
    (by simp [SigGolfCandidate.T3.chainInput, bytesLE_length, SigGolfCandidate.T3.zero16])
    (nonEnc_chainInput _ _ _ _ _ _)) _
/-- C3: a leaf block carries its leaf's hyper label; its length (at least 4 chain ends) keeps it apart. -/
theorem notEnc_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    AllQueriesSatisfy (SigGolfCandidate.T3.leafHash lay tree leaf ends) NotEncS := by
  unfold SigGolfCandidate.T3.leafHash
  have hl := leafInput_long lay tree leaf ends hlen
  exact notEnc_shortHash _ (by omega) (nonEnc_pad64_long _ hl)
/-- Pairing stage 1: a chain row of the current scheme (F or G format) is no encoding row (header marker). -/
theorem nonEnc_chainInputW (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    NonEnc (.inl (.inr (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i s v)))) := by
  apply nonEnc_of_hdr _ (SigGolfCandidate.T3.chainHeader lay tree leaf i s) _
    (notHyper_of_marker (by
      unfold SigGolfCandidate.T3.tweakMarker
      have := SigGolfCandidate.T3.chainHeader_firstByte lay tree leaf i s; omega))
  rw [ClaudeWCT.WCT9.chainInputW_padded]
  exact ClaudeWCT.WCT9.chainInputW_header _ _ _ _ _ _
theorem notEnc_chainW (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.chainW lay tree leaf i start count v) NotEncS :=
  allQ_foldlM _ _ (fun _ _ => notEnc_halfHash _ _
    (by rw [ClaudeWCT.WCT9.chainInputW_length]; omega)
    (nonEnc_chainInputW _ _ _ _ _ _)) _
/-- Witness stack: the WOTS chain of the T3 text (`topChain = chainW 0 0` on the top, `chain` below). -/
theorem notEnc_layChain (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.layChain lay tree leaf i start count v) NotEncS := by
  unfold SigGolfCandidate.T3.layChain
  split
  · rw [← ClaudeWCT.WCT9.chainW_top_eq]; exact notEnc_chainW _ _ _ _ _ _ _
  · exact notEnc_chain _ _ _ _ _ _ _
theorem notEnc_lowerLeafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : 4 ≤ ends.length) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.lowerLeafHash lay tree leaf ends) NotEncS := by
  have hl := leafInput_long lay tree leaf ends hlen
  have e := ClaudeWCT.W9.T3M.leafInputW_length lay tree leaf 0 0 ends
  unfold ClaudeWCT.WCT9.lowerLeafHash ClaudeWCT.WCT9.leafHashW ClaudeWCT.WCT9.lowerHash
  exact notEnc_halfHash _ _ (by rw [e]; omega) (nonEnc_pad64_long _ (by rw [e]; exact hl))
/-- C2: a packed lower node word has marker `128 + heap`, so it is no hyper word. -/
theorem lowerTweak_notHyper (lay tree heap : Nat) (hh : heap < 128) :
    NotHyper (ClaudeWCT.WCT9.lowerTweak lay tree heap) := by
  apply notHyper_of_marker
  unfold ClaudeWCT.WCT9.lowerTweak ClaudeWCT.WCT9.lowerNodeWord ClaudeWCT.WCT9.lowerK
  rw [SigGolfCandidate.T3.append64_marker, BitVec.toNat_add, BitVec.toNat_ofNat, SigGolfCandidate.T3.hyperWord_toNat]
  omega
theorem notEnc_lowerNodeHash (lay tree heap : Nat) (left right : Digest) (hh : lay ≠ 0 → heap < 128) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.lowerNodeHash lay tree heap left right) NotEncS := by
  unfold ClaudeWCT.WCT9.lowerNodeHash ClaudeWCT.WCT9.lowerHash ClaudeWCT.WCT9.merkleNodeInput
  rw [List.append_assoc (bytesLE 16 left ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay tree heap))]
  refine notEnc_halfHash _ _ (by simp [bytesLE_length])
    (nonEnc_of_hdr _ (ClaudeWCT.WCT9.merkleTweak lay tree heap) ?_ ?_)
  · rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
      SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
  · by_cases h0 : lay = 0
    · subst h0; rw [ClaudeWCT.WCT9.merkleTweak_top]; exact nodeTweak_ne_row 3 0 tree heap (by decide) (fun _ _ => rfl)
    · rw [ClaudeWCT.WCT9.merkleTweak_lower h0]; exact lowerTweak_notHyper _ _ _ (hh h0)
theorem mapM_support_length {α β : Type} (f : α → M β) :
    ∀ (xs : List α) (ys : List β), ys ∈ support (xs.mapM f) → ys.length = xs.length
  | [], ys, h => by simpa using h
  | x :: xs, ys, h => by
    rw [List.mapM_cons, mem_support_bind_iff] at h
    obtain ⟨y, -, h⟩ := h
    rw [mem_support_bind_iff] at h
    obtain ⟨zs, hzs, h⟩ := h
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst h
    simp [mapM_support_length f xs zs hzs]
/-- Legacy node hash, top tree only (C2/C3: a legacy lower node tweak is a hyper word with high word `heap`, which
`EncQ` no longer tells apart by its header). -/
theorem notEnc_nodeHash (lay tree heap : Nat) (left right : Digest)
    (hroot : lay < 4 → lay = 0) :
    AllQueriesSatisfy (SigGolfCandidate.T3.nodeHash 3 lay tree heap left right) NotEncS := by
  unfold SigGolfCandidate.T3.nodeHash
  rw [List.append_assoc (bytesLE 16 left ++ bytesLE 16 (nodeTweak 3 lay tree heap))]
  refine notEnc_shortHash _ (by simp [bytesLE_length]) (nonEnc_of_hdr _ _ ?_
    (nodeTweak_ne_row 3 lay tree heap (by decide) (fun _ => hroot)))
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
theorem notEnc_recoverLayer (sig : SigGolfCandidate.T3.Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hlay : lay.val = 0) :
    AllQueriesSatisfy (SigGolfCandidate.T3.recoverLayer sig index lay digits) NotEncS := by
  unfold SigGolfCandidate.T3.recoverLayer
  exact allQ_bind_support (allQ_mapM _ _ fun _ => notEnc_layChain _ _ _ _ _ _ _) fun _ hends =>
    allQ_bind (notEnc_leafHash _ _ _ _ (by
      rw [mapM_support_length _ _ _ hends, List.length_finRange]; exact chainCount_ge4 _)) fun _ =>
      allQ_foldlM _ _ (fun _ _ => notEnc_nodeHash _ _ _ _ _ (fun _ => hlay)) _
/-- img-v6: a top node hash with a nonce pad is a node row (node tweak header), never an encoding row. -/
theorem notEnc_topNodeHashN (heap n : Nat) (left right : Digest) :
    AllQueriesSatisfy (SigGolfCandidate.T3.topNodeHashN heap n left right) NotEncS := by
  unfold SigGolfCandidate.T3.topNodeHashN SigGolfCandidate.T3.topNodeInput SigGolfCandidate.T3.nonceBytes
  rw [← ClaudeWCT.WCT9.halfHash_eq_projHash,
    List.append_assoc (bytesLE 16 left ++ bytesLE 16 (nodeTweak 3 0 0 heap))]
  refine notEnc_halfHash _ _ (by simp [bytesLE_length]) (nonEnc_of_hdr _ _ ?_
    (nodeTweak_ne_row 3 0 0 heap (by decide) (fun _ _ => rfl)))
  rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
/-- img-v6: the nonce-reading top verifier makes no encoding query once its answer decodes. -/
theorem notEnc_verifyTopN (sig : ClaudeWCT.WCT9.Signature) (nonces : List Nat) (index : Nat) {answer : Digest}
    {digits : List Nat} (h : decode 0 answer = some digits) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.verifyTopN sig nonces index answer) NotEncS := by
  unfold ClaudeWCT.WCT9.verifyTopN
  rw [ClaudeWCT.WCT9.topDecodeRun_of_decode h]
  refine allQ_map _ (allQ_bind_support (allQ_mapM _ _ fun _ => notEnc_layChain _ _ _ _ _ _ _) fun _ hends =>
    allQ_bind (notEnc_leafHash _ _ _ _ (by
      rw [mapM_support_length _ _ _ hends, List.length_finRange]; exact chainCount_ge4 _)) fun _ =>
      allQ_foldlM _ _ (fun _ _ => ?_) _)
  dsimp only
  split
  · exact notEnc_topNodeHashN _ _ _ _
  · exact notEnc_nodeHash _ _ _ _ _ (fun _ => rfl)
theorem heap_ne_one {h j x : Nat} (hj : j + 1 < h) (hh : h ≤ 12) (hx : x < 2 ^ h) :
    (2 ^ (h - j - 1) + x / 2 ^ (j + 1)) % 2 ^ 64 ≠ 1 := by
  have h2 : 2 ≤ 2 ^ (h - j - 1) :=
    (show 2 = 2 ^ 1 by norm_num).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have h3 : 2 ^ (h - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) hh
  have h5 : x / 2 ^ (j + 1) ≤ x := Nat.div_le_self _ _
  have h6 : 2 ≤ 2 ^ (h - j - 1) + x / 2 ^ (j + 1) := le_trans h2 (Nat.le_add_right _ _)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
theorem heap_lt128 {h j x : Nat} (hj : j + 1 < h) (hh : h ≤ 7) (hx : x < 2 ^ h) :
    2 ^ (h - j - 1) + x / 2 ^ (j + 1) < 128 := by
  have h5 : x / 2 ^ (j + 1) < 2 ^ (h - j - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show h - j - 1 + (j + 1) = h by omega]
    exact hx
  have h3 : 2 ^ (h - j - 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
  have h64 : (2 : Nat) ^ 6 = 64 := by norm_num
  omega
theorem notEnc_recoverLayerPair (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    AllQueriesSatisfy (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) NotEncS := by
  have hh : lay.val ≠ 0 → height lay ≤ 7 := by fin_cases lay <;> decide
  unfold ClaudeWCT.WCT9.recoverLayerPair
  exact allQ_bind_support (allQ_mapM _ _ fun _ => notEnc_chainW _ _ _ _ _ _ _) fun _ hends =>
    allQ_bind (notEnc_lowerLeafHash _ _ _ _ (by
      rw [mapM_support_length _ _ _ hends, List.length_finRange]; exact chainCount_ge4 _)) fun _ =>
      allQ_bind (allQ_foldlM _ _ (fun _ j => notEnc_lowerNodeHash _ _ _ _ _ (fun h0 =>
        heap_lt128 (by have := j.isLt; omega) (hh h0) (Nat.mod_lt _ (Nat.two_pow_pos _)))) _) fun _ => allQ_pure _
theorem encInput_hdr (lay : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32) :
    ((pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)).drop 16).take 16 =
      bytesLE 16 (rowTweak lay tree leaf) := by
  cases msg with
  | forest root =>
    change SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (bytesLE 16 root ++ bytesLE 16 (rowTweak lay tree leaf) ++
      bytesLE 4 c)) = _
    rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [bytesLE_length]),
      SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
  | pair left right =>
    change SigGolfCandidate.T3M.Extract.hdrBlock (pad64 (bytesLE 16 left ++ bytesLE 16 (rowTweak lay tree leaf) ++
      bytesLE 4 c ++ bytesLE 12 (0 : BitVec 96) ++ bytesLE 16 right)) = _
    simp only [List.append_assoc]
    rw [← List.append_assoc (bytesLE 16 left)]
    rw [SigGolfCandidate.T3M.Extract.hdrBlock_pad64 _ (by simp [bytesLE_length]),
      SigGolfCandidate.T3M.Extract.hdrBlock_prefix]
theorem encInput_pos (lay : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32) :
    0 < (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c).length := by
  cases msg <;> simp [ClaudeWCT.WCT9.layerEncodingInput, SigGolfCandidate.T3.encodingInput,
    ClaudeWCT.WCT9.pairEncodingInputP, bytesLE_length]
theorem encQ_layer (lay lay' : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32)
    (h : EncQ lay'.val (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))) : lay' = lay := by
  obtain ⟨i, hi, hq, routed, hp, hb⟩ := h
  have hi' : Aligned i := ⟨by omega, by omega⟩
  have e := toQ_injOn (pad64_aligned' _ (encInput_pos lay tree leaf msg c)) hi' hq
  rw [← e, encInput_hdr] at hb
  have hb' := bytesLE_injective hb
  unfold rowTweak at hb'
  exact (hyperH_layer hb').symm
variable {f g : Hash}
theorem agree_mrealize {α : Type} {p : M α} (hp : AllQueriesSatisfy p NotEncS)
    (hfg : ∀ q, (∀ lay : Layer, ¬ EncQ lay.val q) → f q = g q) : Agree f g (mrealize 0 p) := by
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp
    rw [mrealize_bind]
    rcases q with (n | input) | c
    · exact hp.1.elim
    · have e : mrealize 0 (liftM (Spec.query (.inl (.inr input))) : M _) =
          (liftM (OracleSpec.query (spec := HashSpec) (toQ input)) : OracleComp HashSpec _) := by
        simp [mrealize, SigGolfCandidate.T3M.machineHandler]; exact id_map _
      rw [e]
      exact agree_bind ⟨hfg _ hp.1, trivial⟩ (ih _ (hp.2 _))
    · exact hp.1.elim
theorem agree_mrealize_bind {α β : Type} (p : M α) (k : α → M β) :
    Agree f g (mrealize 0 (p >>= k)) ↔
      Agree f g (mrealize 0 p) ∧
        Agree f g (mrealize 0 (k (evalWithAnswerFn (machineAnswers f 0) p))) := by
  rw [mrealize_bind, agree_bind_iff, eval_mrealize]
theorem eval_shortHash (hash : Hash) (y : HashInput) :
    evalWithAnswerFn (machineAnswers hash 0) (shortHash y) =
      (hash (toQ (pad64 y))).extractLsb' 0 128 := by
  rw [← eval_mrealize, mrealize_shortHash, evalWithAnswerFn_map, eval_liftQ]
theorem mrealize_encodingHash (lay : Layer) (y : HashInput) :
    mrealize 0 (ClaudeWCT.WCT9.encodingHash lay y) =
      ClaudeWCT.WCT9.encodingAnswer lay <$> (liftM (HashSpec.query (toQ (pad64 y))) : OracleComp HashSpec _) := by
  rw [ClaudeWCT.WCT9.encodingHash, mrealize_map, SigGolfCandidate.T3M.mrealize_publicHash]
theorem eval_encodingHash (hash : Hash) (lay : Layer) (y : HashInput) :
    evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.WCT9.encodingHash lay y) =
      ClaudeWCT.WCT9.encodingAnswer lay (hash (toQ (pad64 y))) := by
  rw [← eval_mrealize, mrealize_encodingHash, evalWithAnswerFn_map, eval_liftQ]
theorem hfg_ok (hash : Hash) : ∀ q, (∀ lay : Layer, ¬ EncQ lay.val q) → hash q = okHash hash q :=
  fun _ h => (okHash_eq_of_not_enc hash h).symm
theorem okHash_producer (hash : Hash) (lay : Layer) (tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg)
    (c : BitVec 32) {digits : List Nat}
    (hp : ClaudeWCT.WCT9.producerDecode lay
      (ClaudeWCT.WCT9.encodingAnswer lay (hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))))) =
        some digits) :
    hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))) =
      okHash hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))) := by
  refine (okHash_eq hash ?_).symm
  rintro ⟨lay', hq, ds, hds, hlow⟩
  obtain rfl := encQ_layer lay lay' tree leaf msg c hq
  rw [ClaudeWCT.WCT9.producerDecode_decode hp] at hds
  cases hds
  have := ClaudeWCT.WCT9.producerDecode_credit hp
  omega
theorem agree_layers (hash : Hash) (sig : ClaudeWCT.WCT9.Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg root counters,
      evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.WCT9.expandLayersBC sig index n msg) =
        some (root, counters) →
      ∀ w : ClaudeWCT.WCT9.Witness, w.signature = sig →
        (∀ lay : Layer, lay.val < n → w.counters lay = counters.getD lay.val 0) →
        Agree hash (okHash hash) (mrealize 0 (ClaudeWCT.WCT9.verifyLayersBC w index n msg)) := by
  intro n
  induction n with
  | zero =>
      intro _ msg root counters he
      simp [ClaudeWCT.WCT9.expandLayersBC] at he
  | succ n ih =>
      intro hn msg root counters he w hw hc
      simp only [ClaudeWCT.WCT9.expandLayersBC, evalWithAnswerFn_bind] at he
      split at he
      next counter digits hs =>
          have hlim := ClaudeWCT.WCT9.searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hsd⟩ := ClaudeWCT.WCT9.layerCounterSearch_some_search (machineAnswers hash 0)
            _ _ _ _ _ 0 counter digits
            (by unfold counterLimit at hlim; omega) hs
          have hdecode := ClaudeWCT.WCT9.producerDecode_decode hsd
          have hnot : ¬counter.toNat ≥ ClaudeWCT.WCT9.verifyWindow := ClaudeWCT.WCT9.ctr_not_ge_verifyWindow counter
          have hlay := ClaudeWCT.WCT9.ofNat_layer_val n (by omega)
          have hproducerRaw := hsd
          rw [eval_encodingHash] at hsd
          have hq := okHash_producer hash _ _ _ msg counter hsd
          by_cases hn0 : n = 0
          · subst hn0
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq,
              Prod.mk.injEq] at he
            obtain ⟨-, rfl⟩ := he
            have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
              rw [hc _ (by rw [hlay]; omega), hlay]; rfl
            simp only [ClaudeWCT.WCT9.verifyLayersBC, hcounter, hnot, ite_false]
            refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
            · rw [mrealize_encodingHash, agree_map_iff]
              exact ⟨hq, trivial⟩
            · simp only [if_true, ↓reduceIte]
              rw [ClaudeWCT.WCT9.verifyTop_of_decode _ _ hdecode, mrealize_map, agree_map_iff]
              exact agree_mrealize (notEnc_recoverLayer _ _ _ _ (by rfl)) (hfg_ok hash)
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            split at he
            next previousRoot previousCounters hr =>
                simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨-, rfl⟩ := he
                have hlen := (ClaudeWCT.WCT9.expandLayersBC_verified _ sig index n (by omega) _ _ _ hr).1
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previousCounters [counter] 0 n (by omega), hlen]
                  simp
                simp only [ClaudeWCT.WCT9.verifyLayersBC, hcounter, hnot, ite_false]
                refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
                · rw [mrealize_encodingHash, agree_map_iff]
                  exact ⟨hq, trivial⟩
                · rw [hdecode]
                  have hgood := ClaudeWCT.WCT9.producerDecode_lowerRankGood
                    (lay := Fin.ofNat 4 n) (by intro h; have := congrArg Fin.val h; rw [hlay] at this; exact hn0 this) hproducerRaw
                  simp only [hn0, if_false,
                    ClaudeWCT.WCT9.recoverLayerPairGuard_of_good _ _ _ _ _ hgood, bind_map_left]
                  refine (agree_mrealize_bind _ _).mpr
                    ⟨agree_mrealize (notEnc_recoverLayerPair _ _ _ _) (hfg_ok hash), ?_⟩
                  rw [hw]
                  refine ih (by omega) _ _ _ hr w hw (fun lay hsmall => ?_)
                  rw [hc lay (by omega), List.getD_append previousCounters [counter] 0 lay.val (by omega)]
            next => simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
      next => simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
theorem expandN_layers (A : SigGolfCandidate.T3.Correctness.Answers) (m : SigGolfCandidate.T3.Message) (pk : Digest)
    (σ : ClaudeWCT.WCT9.Signature) (N : HashOutput) (wt : ClaudeWCT.WCT9.Witness)
    (he : evalWithAnswerFn A (ClaudeWCT.W9.T3M.expandN0 m pk σ) = some (N, wt)) :
    ∃ root counters, evalWithAnswerFn A (ClaudeWCT.WCT9.expandLayersBC σ (ClaudeWCT.WCT9.digestIndex N) 4
        (.pair (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex N) N)).1
          (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex N) N)).2)) = some (root, counters) ∧
      ∀ lay : Layer, wt.counters lay = counters.getD lay.val 0 := by
  simp only [ClaudeWCT.W9.T3M.expandN0, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn A (ClaudeWCT.WCT9.digestSearch σ.rho m 0 ClaudeWCT.WCT9.digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn A (ClaudeWCT.WCT9.expandLayersBC σ (ClaudeWCT.WCT9.digestIndex output) 4
          (.pair (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex output) output)).1
            (evalWithAnswerFn A (ClaudeWCT.WCT9.recoverFts σ (ClaudeWCT.WCT9.digestIndex output) output)).2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some layers =>
          obtain ⟨root, counters⟩ := layers
          simp only [hl] at he
          split at he
          · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
          · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact ⟨root, counters, hl, fun _ => rfl⟩
theorem agree_verifyP (hash : Hash) (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : ClaudeWCT.WCT9.Signature)
    (N : HashOutput) (wt : ClaudeWCT.WCT9.Witness)
    (hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.expandN0 m pk σ) = some (N, wt)) :
    Agree hash (okHash hash) (mrealize 0 (ClaudeWCT.W9.T3M.verifyP m pk (ClaudeWCT.W9.T3M.witEnc N wt))) := by
  have F := ClaudeWCT.W9.T3M.expandN0_facts _ m pk σ N wt hx
  obtain ⟨root, counters, hl, hcs⟩ := expandN_layers _ m pk σ N wt hx
  have hv : ClaudeWCT.W9.T3M.verifyP m pk (ClaudeWCT.W9.T3M.witEnc N wt) =
      SigGolfCandidate.T3.digest wt.signature.rho m wt.digestCounter >>=
        ClaudeWCT.W9.T3M.verifyTailP pk (ClaudeWCT.W9.T3M.witEnc N wt) := by
    rw [ClaudeWCT.W9.T3M.verifyP_eq_tail]
    unfold ClaudeWCT.W9.T3M.digestP
    rw [ClaudeWCT.W9.T3M.wdc_witEnc, ClaudeWCT.W9.T3M.wrho_witEnc,
      if_neg (by have := wt.digestCounter.isLt; unfold ClaudeWCT.WCT9.digestVerifyWindow; omega), bind_map_left]
  rw [hv, agree_mrealize_bind]
  refine ⟨agree_mrealize (notEnc_digest _ _ _) (hfg_ok hash), ?_⟩
  rw [F.sig, F.digest, ClaudeWCT.W9.T3M.verifyTailP_shaped pk N _ F.adm, ClaudeWCT.W9.T3M.witDecP_witEnc,
    ClaudeWCT.W9.T3M.padDecP_witEnc]
  have hidx : ClaudeWCT.WCT9.digestIndex N < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt N
  unfold ClaudeWCT.W9.T3M.verifyPadsTail
  simp only [F.adm, Bool.not_true, Bool.false_eq_true, if_false, ClaudeWCT.W9.T3M.recoverFtsP_zero,
    ClaudeWCT.W9.T3M.verifyLayersBCP_zero _ _ hidx]
  refine (agree_mrealize_bind _ _).mpr ⟨agree_mrealize (notEnc_recoverFts _ _ _) (hfg_ok hash), ?_⟩
  refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
  · rw [F.sig, ClaudeWCT.W9.T3M.verifyLayersBCP_zero _ _ hidx 4 le_rfl]
    exact agree_layers hash σ _ 4 le_rfl _ root counters hl wt F.sig (fun lay _ => hcs lay)
  · split <;> trivial
theorem digestCap_okHash (hash : Hash) (m : SigGolfCandidate.T3.Message) (pk : Digest)
    (σ : ClaudeWCT.WCT9.Signature) (N : HashOutput) (wt : ClaudeWCT.WCT9.Witness)
    (hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.expandN0 m pk σ) = some (N, wt)) :
    DigestCapOk (okHash hash) m (ClaudeWCT.W9.T3M.witEnc N wt) := by
  have F := ClaudeWCT.W9.T3M.expandN0_facts _ m pk σ N wt hx
  have hd : ClaudeWCT.W9.T3M.digestP m (ClaudeWCT.W9.T3M.witEnc N wt) =
      some <$> SigGolfCandidate.T3.digest wt.signature.rho m wt.digestCounter := by
    unfold ClaudeWCT.W9.T3M.digestP
    rw [ClaudeWCT.W9.T3M.wdc_witEnc, ClaudeWCT.W9.T3M.wrho_witEnc,
      if_neg (by have := wt.digestCounter.isLt; unfold ClaudeWCT.WCT9.digestVerifyWindow; omega)]
  have hag : Agree hash (okHash hash) (mrealize 0 (ClaudeWCT.W9.T3M.digestP m (ClaudeWCT.W9.T3M.witEnc N wt))) := by
    rw [hd, mrealize_map, agree_map_iff]
    exact agree_mrealize (notEnc_digest _ _ _) (hfg_ok hash)
  intro N' hN'
  rw [← agree_eval hag, eval_mrealize, hd, evalWithAnswerFn_map, F.sig, F.digest] at hN'
  cases hN'
  exact F.cap
variable {I : ClaudeWCT.W9.T3M.Images}
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
set_option maxRecDepth 100000 in
-- r3h HonestN: legacy (5310) expand_witness / verify_run_ok removed (legacy Budgets pipeline removed).
theorem honest_success_verify_cf (sub : Submission) (hash : Hash) (sk : SecretKey) (m : Message)
    (h : (evalWithAnswerFn hash (sub.honest sk m)).success = true) :
    ∃ pk σ w, (sub.runWith hash .expand (m, pk, σ)).value = some w ∧
      (sub.runWith hash .verify (m, pk, w)).value.isSome = true ∧
      (evalWithAnswerFn hash (sub.honest sk m)).verificationCycles =
        (sub.runWith hash .verify (m, pk, w)).cycles + witnessCycles sub.sizes.witness := by
  unfold Submission.honest at h ⊢
  simp only [evalWithAnswerFn_bind] at h ⊢
  generalize evalWithAnswerFn hash (sub.run .keygen sk) = k at h ⊢
  rcases hk : k.value with _ | ⟨pk, cache⟩
  · simp [hk] at h
  simp only [hk, evalWithAnswerFn_bind] at h ⊢
  generalize evalWithAnswerFn hash (sub.run .sign (sk, cache, m)) = s at h ⊢
  rcases hs : s.value with _ | σ
  · simp [hs] at h
  simp only [hs, evalWithAnswerFn_bind] at h ⊢
  generalize he : evalWithAnswerFn hash (sub.run .expand (m, pk, σ)) = e at h ⊢
  rcases he' : e.value with _ | w
  · simp [he'] at h
  simp only [he', evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h ⊢
  refine ⟨pk, σ, w, ?_, h, rfl⟩
  unfold Submission.runWith
  rw [he, he']
end ClaudeWCT.W9.T3M.Final.Credit
end

namespace ClaudeWCT.W9.T3M.Final.Credit
open OracleComp OracleSpec
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Layer Digest HashInput pad64)
open SigGolfCandidate.T3M (toQ mrealize mrealize_map)
open SigGolfCandidate.T3M.Verify

theorem hfg_okBy (floors : Layer → Nat) (high : Bool) (hash : Hash) :
    ∀ q, (∀ lay : Layer, ¬ EncQ lay.val q) → hash q = okHashBy floors high hash q :=
  fun _ h => (okHashBy_eq_of_not_enc floors high hash h).symm

theorem mrealize_verificationHash (lay : Layer) (high : Bool) (y : HashInput) :
    mrealize 0 (ClaudeWCT.WCT9.verificationHash lay high y) =
      ClaudeWCT.WCT9.verificationAnswer lay high <$>
        (liftM (HashSpec.query (toQ (pad64 y))) : OracleComp HashSpec _) := by
  rw [ClaudeWCT.WCT9.verificationHash, mrealize_map, SigGolfCandidate.T3M.mrealize_publicHash]

/-- An encoding answer accepted by the canonical producer (with the honest hint on the top) is not replaced by
`okHashBy` once its path-aware credit reaches the floor. -/
theorem okHashBy_accepted_credit (floors : Layer → Nat) (high : Bool) (hash : Hash) (lay : Layer)
    (floor tree leaf : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) (c : BitVec 32)
    {digits : List Nat} {low : Bool}
    (hhigh : lay = 0 → high = ClaudeWCT.WCT9.encodingHigh 0
      (hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))))
    (hf : floors lay ≤ ClaudeWCT.WCT9.CanonicalPolicy.credit lay low digits)
    (hp : ClaudeWCT.WCT9.CanonicalPolicy.producerDecodeOut lay floor
        (hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))) = some (digits, low)) :
    hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))) =
      okHashBy floors high hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c))) := by
  refine (okHashBy_eq floors high hash ?_).symm
  rintro ⟨lay', hq, ds, hds, hlow⟩
  have hll := encQ_layer lay lay' tree leaf msg c hq
  subst lay'
  obtain ⟨hl, hpd⟩ := ClaudeWCT.WCT9.CanonicalPolicy.producerDecodeOut_spec hp
  have hs := ClaudeWCT.WCT9.CanonicalPolicy.producerDecodeAt_spec hpd
  set a := hash (toQ (pad64 (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg c)))
  have hva : ClaudeWCT.WCT9.verificationAnswer lay high a = ClaudeWCT.WCT9.encodingAnswer lay a ∧
      ClaudeWCT.WCT9.verificationLow lay high a = low := by
    by_cases h0 : lay = 0
    · subst h0
      rw [hhigh rfl, ClaudeWCT.WCT9.verificationAnswer_honest, ClaudeWCT.WCT9.verificationLow_honest, hl]
      exact ⟨rfl, rfl⟩
    · rw [ClaudeWCT.WCT9.verificationAnswer_lower lay h0, ClaudeWCT.WCT9.verificationLow_lower lay h0, hl]
      exact ⟨rfl, rfl⟩
  rw [hva.1, hs.1] at hds
  cases hds
  rw [hva.2] at hlow
  have hc := hs.2.1
  unfold ClaudeWCT.WCT9.CanonicalPolicy.credit at hf
  omega
end ClaudeWCT.W9.T3M.Final.Credit

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Layer Digest route counterLimit)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem agree_layers_at (floors : Layer → Nat) (hash : Hash)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (index topFloor : Nat) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn (machineAnswers hash 0)
        (recoverHintedLayers sig index ((sig.layers 0).path topJ) n msg topFloor) = some result →
      (∀ lay : Layer, lay.val < n →
        floors lay ≤ CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val [])) →
      ∀ w : SigGolfCandidate.Research.SharedForest.Witness, w.signature = sig →
        (∀ lay : Layer, lay.val < n → w.counters lay = result.counters.getD lay.val 0) →
        w.topHigh = !(result.lows.getD 0 true) →
        Agree hash (okHashBy floors w.topHigh hash) (mrealize 0 (verifyLayers w index n msg)) := by
  intro n
  induction n with
  | zero =>
      intro _ msg result he
      simp [recoverHintedLayers] at he
  | succ n ih =>
      intro hn msg result he hf w hw hc hh
      simp only [recoverHintedLayers, evalWithAnswerFn_bind] at he
      split at he
      next counter digits low hs =>
          have hlim := searchLimit_le (Fin.ofNat 4 n)
          obtain ⟨_, hbound, hproducer⟩ := canonical_search_some (machineAnswers hash 0) _
            _ _ _ _
            _ 0 counter digits low (by unfold counterLimit at hlim; omega) hs
          have hpd := (CanonicalPolicy.producerDecodeOut_spec hproducer)
          have hdecode := (CanonicalPolicy.producerDecodeAt_spec hpd.2).1
          have hnot : ¬counter.toNat ≥ verifyWindow := ctr_not_ge_verifyWindow counter
          have hlay := ofNat_layer_val n (by omega)
          have hevp : evalWithAnswerFn (machineAnswers hash 0)
              (SigGolfCandidate.T3.publicHash (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                (route index (Fin.ofNat 4 n)).1 msg counter)) =
              hash (SigGolfCandidate.T3M.toQ (SigGolfCandidate.T3.pad64 (layerEncodingInput (Fin.ofNat 4 n)
                (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg counter))) := by
            rw [← eval_mrealize, SigGolfCandidate.T3M.mrealize_publicHash, eval_liftQ]
          rw [hevp] at hproducer
          by_cases hn0 : n = 0
          · subst n
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at he
            subst result
            have hfloor : floors (Fin.ofNat 4 0) ≤ CanonicalPolicy.credit (Fin.ofNat 4 0) low digits :=
              hf _ (by decide)
            have hhigh : w.topHigh = encodingHigh 0 (hash (SigGolfCandidate.T3M.toQ (SigGolfCandidate.T3.pad64
                (layerEncodingInput (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
                  (route index (Fin.ofNat 4 0)).1 msg counter)))) := by
              rw [hh, encodingHigh_top]
              simp only [List.getD_cons_zero]
              rw [hpd.1, hevp]
              rfl
            have hq := okHashBy_accepted_credit floors w.topHigh hash _ _ _ _ msg counter
              (fun _ => hhigh) hfloor hproducer
            have hcounter : w.counters (Fin.ofNat 4 0) = counter := by
              rw [hc _ (by rw [hlay]; omega), hlay]; rfl
            simp only [verifyLayers, hcounter, hnot, ite_false]
            refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
            · rw [mrealize_verificationHash, agree_map_iff]
              exact ⟨hq, trivial⟩
            · simp only [if_true, ↓reduceIte]
              have hva : evalWithAnswerFn (machineAnswers hash 0) (verificationHash (Fin.ofNat 4 0) w.topHigh
                  (layerEncodingInput (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 (route index (Fin.ofNat 4 0)).1
                    msg counter)) =
                  evalWithAnswerFn (machineAnswers hash 0) (encodingHash (Fin.ofNat 4 0)
                    (layerEncodingInput (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 (route index (Fin.ofNat 4 0)).1
                      msg counter)) := by
                rw [← eval_mrealize, ← eval_mrealize, mrealize_verificationHash, mrealize_encodingHash,
                  evalWithAnswerFn_map, evalWithAnswerFn_map, eval_liftQ, hhigh]
                exact verificationAnswer_honest 0 _
              have hdec' : CanonicalPolicy.decode (Fin.ofNat 4 0) (evalWithAnswerFn (machineAnswers hash 0)
                  (encodingHash (Fin.ofNat 4 0) (layerEncodingInput (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2
                    (route index (Fin.ofNat 4 0)).1 msg counter))) = some digits := hdecode
              rw [hva]
              exact agree_mrealize (notEnc_verifyTopN _ _ _ hdec') (hfg_okBy floors w.topHigh hash)
          · simp only [hn0, if_false, evalWithAnswerFn_bind] at he
            split at he
            next previous hr =>
                simp only [evalWithAnswerFn_pure, Option.some.injEq] at he
                subst result
                obtain ⟨hlen, hdlen, hllen, _⟩ :=
                  recoverHintedLayers_verified_at (machineAnswers hash 0) sig index topFloor
                    n (by omega) _ _ hr
                have hfloor : floors (Fin.ofNat 4 n) ≤ CanonicalPolicy.credit (Fin.ofNat 4 n) low digits := by
                  have h := hf (Fin.ofNat 4 n) (by rw [hlay]; omega)
                  simpa only [hlay, List.getD_append_right previous.digits [digits] [] n (by omega),
                    List.getD_append_right previous.lows [low] true n (by omega),
                    hdlen, hllen, Nat.sub_self, List.getD_cons_zero] using h
                have hnonzero : (Fin.ofNat 4 n : Layer) ≠ 0 := by
                  intro h; have := congrArg Fin.val h; rw [hlay] at this; exact hn0 this
                have hq := okHashBy_accepted_credit floors w.topHigh hash _ _ _ _ msg counter
                  (fun h0 => absurd h0 hnonzero) hfloor hproducer
                have hcounter : w.counters (Fin.ofNat 4 n) = counter := by
                  rw [hc _ (by rw [hlay]; omega), hlay,
                    List.getD_append_right previous.counters [counter] 0 n (by omega), hlen]
                  simp
                simp only [verifyLayers, hcounter, hnot, ite_false,
                  verificationHash_lower (Fin.ofNat 4 n) hnonzero]
                refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
                · rw [mrealize_encodingHash, agree_map_iff]
                  exact ⟨hq, trivial⟩
                · have hgood := (CanonicalPolicy.producerDecodeAt_spec hpd.2).2.2.2.resolve_left hnonzero
                  have hdecode' : CanonicalPolicy.decode (Fin.ofNat 4 n) (evalWithAnswerFn (machineAnswers hash 0)
                      (encodingHash (Fin.ofNat 4 n) (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                        (route index (Fin.ofNat 4 n)).1 msg counter))) = some digits := by
                    rw [eval_encodingHash]; rw [hevp] at hdecode; exact hdecode
                  have hgood' : lowerRankGood (evalWithAnswerFn (machineAnswers hash 0)
                      (encodingHash (Fin.ofNat 4 n) (layerEncodingInput (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
                        (route index (Fin.ofNat 4 n)).1 msg counter))) := by
                    rw [eval_encodingHash]; rw [hevp] at hgood; exact hgood
                  simp only [hn0, if_false, hdecode',
                    recoverLayerPairGuard_of_good _ _ _ _ _ hgood', bind_map_left]
                  refine (agree_mrealize_bind _ _).mpr
                    ⟨agree_mrealize (notEnc_recoverLayerPair _ _ _ _) (hfg_okBy floors w.topHigh hash), ?_⟩
                  rw [hw]
                  refine ih (by omega) _ _ hr (fun lay hsmall => ?_) w hw (fun lay hsmall => ?_) ?_
                  · have h := hf lay (by omega)
                    simpa only [List.getD_append previous.digits [digits] [] lay.val (by omega),
                      List.getD_append previous.lows [low] true lay.val (by omega)] using h
                  · rw [hc lay (by omega), List.getD_append previous.counters [counter] 0 lay.val (by omega)]
                  · rw [hh, List.getD_append previous.lows [low] true 0 (by omega)]
            next => simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
      next => simp only [evalWithAnswerFn_pure, reduceCtorEq] at he

theorem agree_layers (floors : Layer → Nat) (hash : Hash)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (index : Nat) :
    ∀ n, n ≤ 4 → ∀ msg result,
      evalWithAnswerFn (machineAnswers hash 0)
        (recoverHintedLayers sig index ((sig.layers 0).path topJ) n msg) = some result →
      (∀ lay : Layer, lay.val < n →
        floors lay ≤ CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val [])) →
      ∀ w : SigGolfCandidate.Research.SharedForest.Witness, w.signature = sig →
        (∀ lay : Layer, lay.val < n → w.counters lay = result.counters.getD lay.val 0) →
        w.topHigh = !(result.lows.getD 0 true) →
        Agree hash (okHashBy floors w.topHigh hash) (mrealize 0 (verifyLayers w index n msg)) :=
  agree_layers_at floors hash sig index CanonicalPolicy.topFloor
end ClaudeWCT.W9.T3M.Final.Credit.Paired

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec
open SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Layer Digest HashOutput HashInput pad64 shortHash)
open SigGolfCandidate.T3M (mrealize allQ_bind allQ_mapM allQ_foldlM allQ_pure)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.WCT9
open SigGolfCandidate.T3.Security.Wots.Enc (nonEnc_of_hdr notHyper_of_marker notHyper_of_tag)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem notEnc_ftsChain (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) NotEncS := by
  unfold WCT9.chain
  refine allQ_foldlM _ _ (fun v step => ?_) _
  rw [← WCT9.halfHash_eq_projHash]
  refine notEnc_halfHash _ _ (by rw [WCT9.ftsChainInputW_length]; omega) ?_
  -- witness stack: G chains 1, 3 (`value | header | 0 | 0`) carry the same header block
  unfold WCT9.ftsChainInputW
  split
  · rw [List.append_assoc (bytesLE 16 v ++ _)]
    exact nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _))
      (notHyper_of_marker
        (ne_of_gt (lt_of_lt_of_le (by decide) (ftsChainHeaderP_tweakMarker _ _ _ _ _ 0))))
  · unfold WCT9.chainInput
    rw [List.append_assoc (SigGolfCandidate.T3.zero16 ++ _)]
    -- C2/C3 (#866): `NonEnc` excludes every hyper tweak whatever its high word (`NotHyper`).
    exact nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (by simp [SigGolfCandidate.T3.zero16]))
      (notHyper_of_marker
        (ne_of_gt (lt_of_lt_of_le (by decide) (ftsChainHeaderP_tweakMarker _ _ _ _ _ 0))))

theorem notEnc_ftsLeaf (index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (leafHashP index coord selected pad ends) NotEncS := by
  unfold leafHashP
  apply notEnc_shortHash _ (by simp [leafInputP, bytesLE_length])
  unfold leafInputP
  rw [List.append_assoc (bytesLE 16 _ ++ _)]
  exact nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _))
    (notHyper_of_tag (by rw [ftsLeafHeader_tweakTag]; decide))

/-- C1: the paired leaf of heap `heap` (either half) makes the same non-encoding query. -/
theorem notEnc_ftsLeafH (heap index coord selected : Nat) (pad : Digest) (ends : List Digest) :
    AllQueriesSatisfy (leafHashH heap index coord selected pad ends) NotEncS :=
  allQ_ftsHash_of_shortHash _ _ (notEnc_ftsLeaf index coord selected pad ends)

theorem notEnc_topLow (coord index heap : Nat) (hcoord : coord < 9) (left pad right : Digest) :
    AllQueriesSatisfy (shortHash (wctTopInput coord index heap left pad right)) NotEncS := by
  apply notEnc_shortHash _ (by simp [wctTopInput, bytesLE_length])
  apply nonEnc_of_hdr _ (wctNodeHeader coord index heap) ?_
    (notHyper_of_tag (by rw [wctNodeHeader_tweakTag hcoord]; split <;> decide))
  unfold wctTopInput
  rw [List.append_assoc (bytesLE 16 left ++ bytesLE 16 _)]
  exact hdrBlock_pad64_prefix _ _ _ (bytesLE_length _ _)

theorem notEnc_outer (coord index heap : Nat) (hcoord : coord < 9) (left right : Digest) :
    AllQueriesSatisfy (sharedOuterHash coord index heap left right) NotEncS := by
  unfold sharedOuterHash
  split
  · exact notEnc_topLow _ _ _ hcoord _ _ _
  · exact allQ_highHash_of_shortHash _ (notEnc_topLow _ _ _ hcoord _ _ _)

theorem notEnc_node (first : Bool) (coord index heap : Nat) (hcoord : coord < 9)
    (pads : Nat → PairRoot) (left right : Digest) :
    AllQueriesSatisfy (sharedNode first coord index heap pads left right) NotEncS := by
  unfold sharedNode
  split
  · exact notEnc_outer _ _ _ hcoord _ _
  · split
    · split
      · exact allQ_highHash_of_shortHash _ (notEnc_topLow _ _ _ hcoord _ _ _)
      · exact notEnc_topLow _ _ _ hcoord _ _ _
    · change AllQueriesSatisfy (ftsHash heap (wctTopInput coord index heap left 0 right)) NotEncS
      exact allQ_ftsHash_of_shortHash _ _ (notEnc_topLow _ _ _ hcoord _ _ _)

theorem notEnc_inner (first : Bool) (index coord : Nat) (hcoord : coord < 9) (selected : Child)
    (word : Rank) (values : Fin 6 → Digest) (path : Nat → Digest) (prev : PairRoot) :
    AllQueriesSatisfy (recoverSharedInner first index coord selected word values path prev) NotEncS := by
  unfold recoverSharedInner
  exact allQ_bind (allQ_mapM _ _ fun _ => notEnc_ftsChain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (notEnc_ftsLeafH _ _ _ _ _ _) fun _ =>
      allQ_foldlM _ _ (fun _ _ => notEnc_node _ _ _ _ hcoord _ _ _) _

theorem notEnc_pair (index : Nat) (pair : Fin 4) (selected : Selection) (aWord bWord : Rank)
    (opened : PairOpening) (prev : PairRoot) :
    AllQueriesSatisfy (recoverPair index pair.val selected aWord bWord opened prev) NotEncS := by
  unfold recoverPair
  have hpair := pair.isLt
  exact allQ_bind (notEnc_inner _ _ _ (by omega) _ _ _ _ _) fun _ =>
    allQ_bind (notEnc_inner _ _ _ (by omega) _ _ _ _ _) fun _ =>
      allQ_bind (notEnc_outer _ _ _ (by omega) _ _) fun _ => allQ_pure _

theorem notEnc_singleton (index : Nat) (selected : Child) (word : Rank) (opened : SingletonOpening)
    (prev : PairRoot) : AllQueriesSatisfy (recoverSingleton index selected word opened prev) NotEncS := by
  unfold recoverSingleton
  exact allQ_bind (notEnc_inner _ _ _ (by decide) _ _ _ _ _) fun _ =>
    allQ_bind (notEnc_outer _ _ _ (by decide) _ _) fun _ => allQ_pure _

theorem notEnc_forest (index : Nat) (selected : ForestSelection) (words : ForestWords) (opened : ForestOpening) :
    AllQueriesSatisfy (recoverForest index selected words opened) NotEncS := by
  unfold recoverForest
  exact allQ_bind (allQ_foldlM _ _ (fun _ _ => notEnc_pair _ _ _ _ _ _ _) _) fun _ =>
    notEnc_singleton _ _ _ _ _

theorem canonical_credit_le_301 (lay : Layer) (low : Bool) (digits : List Nat) :
    CanonicalPolicy.credit lay low digits ≤ 301 := by
  have hw : wordCredit lay digits ≤ SigGolfCandidate.T3.chainCount lay := by
    simpa only [wordCredit, List.length_range] using
      List.length_filter_le (fun i => decide (digits.getD i 0 + 1 = SigGolfCandidate.T3.maxDigit lay i))
        (List.range (SigGolfCandidate.T3.chainCount lay))
  have hs : savedCopies lay digits ≤ SigGolfCandidate.T3.chainCount lay := by
    simpa only [savedCopies, List.length_range] using
      List.length_filter_le (fun i => decide (safeZeroCopy lay digits i))
        (List.range (SigGolfCandidate.T3.chainCount lay))
  have hc : SigGolfCandidate.T3.chainCount lay ≤ 54 := by fin_cases lay <;> decide
  have hb := CanonicalPolicy.pathBonus_le lay low
  unfold CanonicalPolicy.credit CanonicalPolicy.pathReward CanonicalPolicy.reward
  omega

theorem recovered_tier_floors (answers : SigGolfCandidate.T3.Correctness.Answers)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (index : Nat)
    (output : HashOutput) (other : Digest) (msg : LayerMsg) (result : RecoveredLayers)
    (he : evalWithAnswerFn answers (recoverHintedLayers sig index other 4 msg
      (conditionalTopFloor output)) = some result)
    (hh : policyHintsValid sig.policyHints result.digits result.lows
      (conditionalCredit output) = true) :
    (∀ lay, CanonicalPolicy.credit lay (result.lows.getD lay.val true)
      (result.digits.getD lay.val []) ≤ 301) ∧
    69 + conditionalExtra output ≤ ((List.finRange 4).map fun lay =>
      CanonicalPolicy.credit lay (result.lows.getD lay.val true)
        (result.digits.getD lay.val [])).sum := by
  constructor
  · intro lay
    exact canonical_credit_le_301 lay _ _
  · have hsum := policyHints_credit_sum_at sig.policyHints result.digits result.lows
      (conditionalCredit output) (conditionalTopFloor output) (conditional_credit_floor output)
      hh (fun lay =>
        (recoverHintedLayers_credit_at answers sig index other (conditionalTopFloor output)
          4 le_rfl msg result he).2.2 lay lay.isLt)
    simpa only [conditionalCredit, CanonicalPolicy.totalCredit] using hsum

theorem recovered_credit_floors (answers : SigGolfCandidate.T3.Correctness.Answers)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (index : Nat)
    (output : HashOutput) (other : Digest)
    (msg : LayerMsg) (result : RecoveredLayers)
    (he : evalWithAnswerFn answers (recoverHintedLayers sig index other 4 msg
      (conditionalTopFloor output)) = some result)
    (hh : policyHintsValid sig.policyHints result.digits result.lows
      (conditionalCredit output) = true) :
    CreditFloors (fun lay => min 69
      (CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val []))) := by
  apply creditFloors_clip
  have hsum := policyHints_credit_sum_at sig.policyHints result.digits result.lows
    (conditionalCredit output) (conditionalTopFloor output) (conditional_credit_floor output)
    hh (fun lay =>
      (recoverHintedLayers_credit_at answers sig index other (conditionalTopFloor output)
        4 le_rfl msg result he).2.2 lay lay.isLt)
  unfold conditionalCredit CanonicalPolicy.totalCredit at hsum
  omega

theorem agree_verify_of_floors (floors : Layer → Nat) (hash : Hash)
    (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn (machineAnswers hash 0) (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter) = output)
    (hr : evalWithAnswerFn (machineAnswers hash 0)
      (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn (machineAnswers hash 0) (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
          (evalWithAnswerFn (machineAnswers hash 0) (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)
        (conditionalTopFloor output)) = some result)
    (hh : policyHintsValid w.signature.policyHints result.digits result.lows
      (conditionalCredit output) = true)
    (hc : ∀ lay, w.counters lay = result.counters.getD lay.val 0)
    (htop : w.topHigh = !(result.lows.getD 0 true))
    (hfloor : ∀ lay, floors lay ≤ CanonicalPolicy.credit lay
      (result.lows.getD lay.val true) (result.digits.getD lay.val [])) :
    Agree hash (okHashBy floors w.topHigh hash)
      (mrealize 0 (SigGolfCandidate.Research.SharedForest.verify message pk w)) := by
  unfold SigGolfCandidate.Research.SharedForest.verify
  split
  · trivial
  · refine (agree_mrealize_bind _ _).mpr ⟨agree_mrealize (notEnc_digest _ _ _) (hfg_okBy floors w.topHigh hash), ?_⟩
    rw [hd]
    split
    · trivial
    · refine (agree_mrealize_bind _ _).mpr
        ⟨agree_mrealize (notEnc_forest _ _ _ _) (hfg_okBy floors w.topHigh hash), ?_⟩
      refine (agree_mrealize_bind _ _).mpr ⟨?_, ?_⟩
      · exact agree_layers_at floors hash w.signature (digestIndex output)
          (conditionalTopFloor output) 4 le_rfl _ result hr
          (fun lay _ => hfloor lay) w rfl (fun lay _ => hc lay) htop
      · split <;> trivial

theorem agree_verify_tier (hash : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (output : HashOutput)
    (result : RecoveredLayers)
    (hd : evalWithAnswerFn (machineAnswers hash 0)
      (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter) = output)
    (hr : evalWithAnswerFn (machineAnswers hash 0)
      (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn (machineAnswers hash 0) (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
          (evalWithAnswerFn (machineAnswers hash 0) (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)
        (conditionalTopFloor output)) = some result)
    (hh : policyHintsValid w.signature.policyHints result.digits result.lows
      (conditionalCredit output) = true)
    (hc : ∀ lay, w.counters lay = result.counters.getD lay.val 0)
    (htop : w.topHigh = !(result.lows.getD 0 true)) :
    ∃ floors : Layer → Nat,
      (∀ lay, floors lay ≤ 301) ∧
      69 + conditionalExtra output ≤ ((List.finRange 4).map floors).sum ∧
      Agree hash (okHashBy floors w.topHigh hash)
        (mrealize 0 (SigGolfCandidate.Research.SharedForest.verify message pk w)) := by
  let floors : Layer → Nat := fun lay =>
    CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val [])
  obtain ⟨hbound, hsum⟩ := recovered_tier_floors (machineAnswers hash 0) w.signature
    (digestIndex output) output ((w.signature.layers 0).path topJ) _ result hr hh
  refine ⟨floors, hbound, hsum, ?_⟩
  exact agree_verify_of_floors floors hash message pk w output result hd hr hh hc htop
    (fun _ => le_rfl)

theorem agree_verify (hash : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (w : SigGolfCandidate.Research.SharedForest.Witness) (output : HashOutput) (result : RecoveredLayers)
    (hd : evalWithAnswerFn (machineAnswers hash 0) (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter) = output)
    (hr : evalWithAnswerFn (machineAnswers hash 0)
      (recoverHintedLayers w.signature (digestIndex output) ((w.signature.layers 0).path topJ) 4
        (.pair (evalWithAnswerFn (machineAnswers hash 0) (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).1
          (evalWithAnswerFn (machineAnswers hash 0) (recoverForest (digestIndex output)
          (forestSelectionFromOutput output) (forestWordsFromOutput output) w.signature.forest)).2)
        (conditionalTopFloor output)) = some result)
    (hh : policyHintsValid w.signature.policyHints result.digits result.lows
      (conditionalCredit output) = true)
    (hc : ∀ lay, w.counters lay = result.counters.getD lay.val 0)
    (htop : w.topHigh = !(result.lows.getD 0 true)) :
    ∃ floors : Layer → Nat, CreditFloors floors ∧
      Agree hash (okHashBy floors w.topHigh hash)
        (mrealize 0 (SigGolfCandidate.Research.SharedForest.verify message pk w)) := by
  let floors : Layer → Nat := fun lay =>
    min 69 (CanonicalPolicy.credit lay (result.lows.getD lay.val true) (result.digits.getD lay.val []))
  refine ⟨floors, recovered_credit_floors _ _ _ output _ _ result hr hh, ?_⟩
  exact agree_verify_of_floors floors hash message pk w output result hd hr hh hc htop
    (fun lay => Nat.min_le_right _ _)
end ClaudeWCT.W9.T3M.Final.Credit.Paired

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.T3M.Final.Paired
variable {I : ClaudeWCT.W9.T3M.Images}
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.Paired.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem expand_witness (E : EncodingFacts) (F : SourceQueries) (P : Final.Paired.Pending I)
    (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5195) (w : Bytes 22012)
    (he : ((Final.Paired.submission I).runWith hash .expand (m,pk,s)).value=some w) :
    ∃sig output wt,evalWithAnswerFn (machineAnswers hash 0)
      (ClaudeWCT.W9.T3M.Paired.expandN m pk sig)=some (output,wt) ∧
      w=ClaudeWCT.W9.T3M.Paired.witEncN output wt := by
  have h := congrArg (evalWithAnswerFn hash) (Final.Paired.expand_value E F P m pk s)
  rw [evalWithAnswerFn_map,eval_mrealize hash 0 (ClaudeWCT.W9.T3M.Paired.expandB m pk (Final.Paired.sigDecC s)),
    ClaudeWCT.W9.T3M.Paired.eval_expandB] at h
  unfold Submission.runWith at he
  rw [h] at he
  cases hx : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.Paired.expandN m pk (Final.Paired.sigDecC s)) with
  | none => rw [hx] at he; cases he
  | some x =>
    rw [hx] at he
    obtain ⟨output,wt⟩ := x
    exact ⟨_,output,wt,hx,(Option.some.inj he).symm⟩

theorem verify_run_agree (E : EncodingFacts) (F : SourceQueries) (P : Final.Paired.Pending I)
    (f g : Hash) (m : Message) (pk : PublicKey) (w : Bytes 22012)
    (hagree : Agree f g (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP m pk w))) :
    (Final.Paired.submission I).runWith f .verify (m,pk,w)=
      (Final.Paired.submission I).runWith g .verify (m,pk,w) := by
  have ha : Agree f g ((Final.Paired.submission I).run .verify (m,pk,w)) := by
    rw [←agree_map_iff (fun r=>r.value.isSome),Final.Paired.verify_value E F P m pk w]
    exact hagree
  exact agree_eval ha
end ClaudeWCT.W9.T3M.Final.Credit.Paired

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M (mrealize)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.Paired (ftsP_accepted)
open W9Machine
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem agree_verifyP_source_of (f g : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (wb : WBytes) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hrho : wrho wb=w.signature.rho) (hdc : wdc wb=w.digestCounter)
    (hd : evalWithAnswerFn (machineAnswers f 0)
      (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter)=output)
    (hg : output.toNat/2^242%16384<791)
    (hr : ∀ k : Fin 9,rawForestRank output k.val<563)
    (hf : SharedV3.forest wb (WCT9.digestIndex output) (rawChildFromOutput output)
      (fun k=>WCT9.embed (forestRank output k.val)) =
      recoverForest (WCT9.digestIndex output) (forestSelectionFromOutput output)
        (forestWordsFromOutput output) w.signature.forest)
    (hl : ∀left right,layersCanonicalBC wb (WCT9.digestIndex output) 4 (.pair left right)=
      SigGolfCandidate.Research.SharedForest.verifyLayers w (WCT9.digestIndex output) 4 (.pair left right))
    (hagree : Agree f g (mrealize 0 (SigGolfCandidate.Research.SharedForest.verify message pk w))) :
    Agree f g (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP message pk wb)) := by
  have hb : ¬w.digestCounter.toNat≥WCT9.digestVerifyWindow := by
    exact Nat.not_le.mpr w.digestCounter.isLt
  have ha : verifyDigestAccepted output=true := by
    simp only [verifyDigestAccepted,hg,decide_true,Bool.true_and]
    exact (ranksAccepted_iff output).mpr hr
  simp only [SigGolfCandidate.Research.SharedForest.verify,hb,↓reduceIte] at hagree
  rw [agree_mrealize_bind] at hagree
  obtain ⟨hDigest,hNext⟩ := hagree
  rw [hd] at hNext
  simp only [ha,Bool.not_true,Bool.false_eq_true,↓reduceIte] at hNext
  unfold ClaudeWCT.W9.T3M.Paired.verifyP digestP
  rw [hdc,hrho,if_neg hb,bind_map_left,agree_mrealize_bind]
  refine ⟨hDigest,?_⟩
  rw [hd]
  dsimp only
  rw [ftsP_accepted wb output hg hr,hf]
  simp only [bind_map_left,bind_assoc,pure_bind,hl]
  convert hNext using 1
  rfl
end ClaudeWCT.W9.T3M.Final.Credit.Paired

namespace ClaudeWCT.W9.T3M.Final.Credit.Paired
open OracleComp OracleSpec SigGolfCandidate.Legacy
open SigGolfCandidate.T3 (Digest HashOutput Layer)
open SigGolfCandidate.T3M (mrealize mrealize_publicHash)
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research.SharedForest
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem agree_verifyP_tier (hash : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn (machineAnswers hash 0)
      (ClaudeWCT.W9.T3M.Paired.expandN message pk sig)=some (output,w)) :
    ∃ floors : Layer → Nat,
      (∀ lay, floors lay ≤ 301) ∧
      69 + conditionalExtra output ≤ ((List.finRange 4).map floors).sum ∧
      Agree hash (okHashBy floors w.topHigh hash)
        (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP message pk
          (ClaudeWCT.W9.T3M.Paired.witEncN output w))) := by
  obtain ⟨result,hr,hh,hc,hd,ha,htop⟩ :=
    ClaudeWCT.W9.T3M.Paired.expandN_recovered _ message pk sig output w he
  simp only [ClaudeWCT.W9.T3M.Paired.recoveredWitness,evalWithAnswerFn_bind] at hr
  obtain ⟨floors,hbound,hsum,hagree⟩ := agree_verify_tier hash message pk w output result
    hd hr hh hc htop
  obtain ⟨hg,hrank,_⟩ := accepted_conditions output ha
  refine ⟨floors,hbound,hsum,agree_verifyP_source_of hash
    (okHashBy floors w.topHigh hash) message pk _ output w
    (ClaudeWCT.W9.T3M.Paired.wrho_witEncN output w)
    (ClaudeWCT.W9.T3M.Paired.wdc_witEncN output w) hd hg hrank
    (W9Drv.SharedCanonical.forest_witEncN output w _ (WCT9.digestIndex_lt output))
    (fun left right=>ClaudeWCT.W9.T3M.Paired.layersCanonicalBC_witEncN output w
      4 left right (by decide)) hagree⟩

theorem agree_verifyP (hash : Hash) (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.Paired.expandN message pk sig)=some (output,w)) :
    ∃ floors : Layer → Nat,CreditFloors floors ∧
      Agree hash (okHashBy floors w.topHigh hash)
        (mrealize 0 (ClaudeWCT.W9.T3M.Paired.verifyP message pk (ClaudeWCT.W9.T3M.Paired.witEncN output w))) := by
  obtain ⟨result,hr,hh,hc,hd,ha,htop⟩ := ClaudeWCT.W9.T3M.Paired.expandN_recovered _ message pk sig output w he
  simp only [ClaudeWCT.W9.T3M.Paired.recoveredWitness,evalWithAnswerFn_bind] at hr
  obtain ⟨floors,hfloors,hagree⟩ := agree_verify hash message pk w output result hd hr hh hc htop
  obtain ⟨hg,hrank,_⟩ := accepted_conditions output ha
  refine ⟨floors,hfloors,agree_verifyP_source_of hash (okHashBy floors w.topHigh hash) message pk _ output w
    (ClaudeWCT.W9.T3M.Paired.wrho_witEncN output w)
    (ClaudeWCT.W9.T3M.Paired.wdc_witEncN output w) hd hg hrank
    (W9Drv.SharedCanonical.forest_witEncN output w _ (WCT9.digestIndex_lt output))
    (fun left right=>ClaudeWCT.W9.T3M.Paired.layersCanonicalBC_witEncN output w 4 left right (by decide)) hagree⟩

theorem digestCap_okHashBy (floors : Layer → Nat) (high : Bool) (hash : Hash)
    (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn (machineAnswers hash 0) (ClaudeWCT.W9.T3M.Paired.expandN message pk sig)=some (output,w)) :
    Final.Paired.DigestCapOk (okHashBy floors high hash) message (ClaudeWCT.W9.T3M.Paired.witEncN output w) := by
  obtain ⟨_,_,_,_,hd,ha,_⟩ := ClaudeWCT.W9.T3M.Paired.expandN_recovered _ message pk sig output w he
  have hagree := agree_mrealize (notEnc_digest w.signature.rho message w.digestCounter) (hfg_okBy floors high hash)
  have hd' : evalWithAnswerFn (machineAnswers (okHashBy floors high hash) 0)
      (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter)=output := by
    rw [←eval_mrealize,←agree_eval hagree,eval_mrealize,hd]
  rw [←eval_mrealize] at hd'
  unfold SigGolfCandidate.T3.digest at hd'
  rw [mrealize_publicHash,eval_liftQ] at hd'
  unfold Final.Paired.DigestCapOk
  rw [ClaudeWCT.W9.T3M.Paired.wrho_witEncN,ClaudeWCT.W9.T3M.Paired.wdc_witEncN,hd']
  exact (accepted_conditions output ha).2.2.trans (by norm_num)

theorem digestTier_okHashBy (floors : Layer → Nat) (high : Bool) (hash : Hash)
    (message : SigGolfCandidate.T3.Message) (pk : Digest)
    (sig : SigGolfCandidate.Research.SharedForest.Signature) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (he : evalWithAnswerFn (machineAnswers hash 0)
      (ClaudeWCT.W9.T3M.Paired.expandN message pk sig) = some (output,w)) :
    conditionalExtra output ≤ 4 ∧
      jointAccountingCost ((okHashBy floors high hash)
        (SigGolfCandidate.T3M.toQ (SigGolfCandidate.T3.pad64
          (SigGolfCandidate.T3.digestInput
            (ClaudeWCT.W9.T3M.wrho (ClaudeWCT.W9.T3M.Paired.witEncN output w))
            message
            (ClaudeWCT.W9.T3M.wdc (ClaudeWCT.W9.T3M.Paired.witEncN output w)))))) ≤
        773 + conditionalExtra output := by
  obtain ⟨_,_,_,_,hd,ha,_⟩ :=
    ClaudeWCT.W9.T3M.Paired.expandN_recovered _ message pk sig output w he
  have hextra := (conditional_bounds_of_accepted output ha).1
  have hagree := agree_mrealize (notEnc_digest w.signature.rho message w.digestCounter)
    (hfg_okBy floors high hash)
  have hd' : evalWithAnswerFn (machineAnswers (okHashBy floors high hash) 0)
      (SigGolfCandidate.T3.digest w.signature.rho message w.digestCounter) = output := by
    rw [←eval_mrealize,←agree_eval hagree,eval_mrealize,hd]
  rw [←eval_mrealize] at hd'
  unfold SigGolfCandidate.T3.digest at hd'
  rw [mrealize_publicHash,eval_liftQ] at hd'
  refine ⟨hextra, ?_⟩
  rw [ClaudeWCT.W9.T3M.Paired.wrho_witEncN,
    ClaudeWCT.W9.T3M.Paired.wdc_witEncN,hd']
  unfold conditionalExtra
  omega
end ClaudeWCT.W9.T3M.Final.Credit.Paired
end
