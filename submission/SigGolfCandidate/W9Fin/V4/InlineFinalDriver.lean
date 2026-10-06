/- Native-image final verification composition. This keeps HashOk in the
   acceptance judgment and selects Native.submission explicitly. -/
import SigGolfCandidate.T3M.InlineSubmission
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineBudgetJudg
import SigGolfCandidate.T3M.Verify.HashAgree
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending
import SigGolfCandidate.T3M.Verify.Init
import SigGolfCandidate.W9Drv.GateDefs

section




namespace W9Fin.V4.Inline
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
def digestQ (m : SigGolfCandidate.T3.Message) (w : WBytes) : Query :=
  toQ (pad64 (digestInput (wrho w) m (wdc w)))
def selectedRank (field : HashOutput → Fin 9 → Nat) (a : HashOutput) (k : Fin 9) : Fin 600 :=
  ⟨field a k % 600, Nat.mod_lt _ (by decide)⟩
def routineSum (field : HashOutput → Fin 9 → Nat) (rankCost : Fin 600 → Nat) (a : HashOutput) : Nat :=
  ((List.finRange 9).map fun k => rankCost (selectedRank field a k)).sum
def ftsAcceptCost (overhead : Nat) (field : HashOutput → Fin 9 → Nat) (rankCost : Fin 600 → Nat)
    (a : HashOutput) : Nat :=
  overhead + routineSum field rankCost a
theorem routineSum_c1 (a : HashOutput) :
    routineSum ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost a = ClaudeWCT.WCT9.jointCost a := rfl
def afterFts (pk : Digest) (w : WBytes) (index : Nat) (r : Option Digest) : SigGolfCandidate.T3.M Bool :=
  match r with
  | some root => do
      let __x ← ClaudeWCT.W9.T3M.layersBC w index 4 (.forest root)
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false
def FtsGoodByCost (GatePre : Digest → WBytes → HashOutput → MachineState → Prop)
    (FtsOut : Digest → WBytes → HashOutput → Digest → MachineState → Prop)
    (acceptCost : HashOutput → Nat) : Prop :=
  ∀ (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs),
    GatePre pk w a u →
    K none = pure (false, 0) →
    (∀ root t, FtsOut pk w a root t → SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQ Images.InlineNative.image t N C Q A (K (some root))) →
    SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQ Images.InlineNative.image u (N + 2023) (C + 2023) Q (A + acceptCost a)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none) K)
def AfterGoodBudget (FtsOut : Digest → WBytes → HashOutput → Digest → MachineState → Prop)
    (acceptCycles : Nat) : Prop :=
  ∀ (pk : Digest) (w : WBytes) (Q : Prop), Q →
    ∀ (a : HashOutput) (root : Digest) (u : MachineState),
      FtsOut pk w a root u →
      SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQ Images.InlineNative.image u 8050 8050 Q acceptCycles (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb)
def PrefixGood (GatePre : Digest → WBytes → HashOutput → MachineState → Prop) : Prop :=
  ∀ (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState),
    initialState Native.submission .verify (m, pk, w) = some s →
    ∀ (P : Hash → Prop) (N C A : Nat) (Q : Prop) (K : Option HashOutput → OracleComp HashSpec Obs),
      K none = pure (false, 0) →
      (∀ a u, (wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit → GatePre pk w a u →
        SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP Images.InlineNative.image (fun hash => hash (digestQ m w) = a ∧ P hash) u N C Q A (K (some a))) →
      SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP Images.InlineNative.image P s (N + 16) (C + 23) Q (A + 23) (ccM (ClaudeWCT.W9.T3M.digestP m w) K)
theorem digestP_eval (hash : Hash) (m : SigGolfCandidate.T3.Message) (w : WBytes)
    (hdc : (wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit) :
    evalWithAnswerFn hash (mrealize 0 (ClaudeWCT.W9.T3M.digestP m w)) = some (hash (digestQ m w)) := by
  unfold ClaudeWCT.W9.T3M.digestP
  rw [if_neg (by omega), mrealize_map]
  unfold SigGolfCandidate.T3.digest
  rw [mrealize_publicHash, evalWithAnswerFn_map, eval_liftQ]
  rfl
theorem capOk_of_pre {hash : Hash} {m : SigGolfCandidate.Legacy.Message} {w : Bytes 22984} {a : HashOutput}
    (hdc : (wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit) (hq : hash (digestQ m w) = a)
    (hcap : ClaudeWCT.W9.T3M.Final.DigestCapOk hash m w) : ClaudeWCT.WCT9.capOk a = true :=
  hcap a ((digestP_eval hash m w hdc).trans (congrArg some hq))
theorem jointCost_le_of_capOk {a : HashOutput} (h : ClaudeWCT.WCT9.capOk a = true) :
    ClaudeWCT.WCT9.jointCost a ≤ 699 := by
  unfold ClaudeWCT.WCT9.capOk ClaudeWCT.WCT9.jointCap at h
  exact of_decide_eq_true h
structure Inputs (GatePre : Digest → WBytes → HashOutput → MachineState → Prop)
    (FtsOut : Digest → WBytes → HashOutput → Digest → MachineState → Prop) (ovh aG : Nat) : Prop where
  prefixGood : PrefixGood GatePre
  fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost)
  after : AfterGoodBudget FtsOut aG
  hnum : 23 + aG + ovh + 699 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound
section
variable {GatePre : Digest → WBytes → HashOutput → MachineState → Prop}
  {FtsOut : Digest → WBytes → HashOutput → Digest → MachineState → Prop} {ovh aG : Nat}
def afterDigest (pk : Digest) (w : WBytes) (N : HashOutput) : SigGolfCandidate.T3.M Bool :=
  (if ClaudeWCT.W9.T3M.gateOk N then ClaudeWCT.W9.T3M.wctP w N else pure none) >>=
    afterFts pk w (N.toNat % 2 ^ 31)
theorem verifyP_eq (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) :
    ClaudeWCT.W9.T3M.verifyP m pk w = (ClaudeWCT.W9.T3M.digestP m w >>= fun o => match o with
      | some N => afterDigest pk w N
      | none => pure false) := by
  unfold ClaudeWCT.W9.T3M.verifyP afterDigest
  congr 1; funext o
  rcases o with _ | N
  · rfl
  · cases hg : ClaudeWCT.W9.T3M.gateOk N
    · simp only [hg, Bool.not_false, if_true, if_false, Bool.false_eq_true, pure_bind, afterFts]
    · simp only [hg, Bool.not_true, if_true, if_false, Bool.false_eq_true]
      rfl
abbrev Pre (m : SigGolfCandidate.Legacy.Message) (w : Bytes 22984) (hash : Hash) : Prop :=
  HashOk hash ∧ ClaudeWCT.W9.T3M.Final.DigestCapOk hash m w
theorem afterDigest_good (fts : FtsGoodByCost GatePre FtsOut
      (ftsAcceptCost ovh ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost))
    (after : AfterGoodBudget FtsOut aG)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (a : HashOutput) (u : MachineState)
    (hdc : (wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit) (hu : GatePre pk w a u) :
    SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP Images.InlineNative.image (fun hash => hash (digestQ m w) = a ∧ Pre m w hash) u (8050 + 2023) (8050 + 2023) True
      (aG + (ovh + 699)) (ccM (afterDigest pk w a) Kb) := by
  have h := fts pk w a u 8050 8050 aG True (fun r => ccM (afterFts pk w (a.toNat % 2 ^ 31) r) Kb) hu
    (by simp only [afterFts, ccM_pure, Kb])
    (fun root t ht => after pk w True trivial a root t ht)
  have e : ccM (afterDigest pk w a) Kb =
      ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none)
        (fun r => ccM (afterFts pk w (a.toNat % 2 ^ 31) r) Kb) := by
    unfold afterDigest
    rw [ccM_bind]
  rw [e]
  by_cases hcap : ClaudeWCT.WCT9.capOk a = true
  · have hj := jointCost_le_of_capOk hcap
    have h' : SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQ Images.InlineNative.image u (8050 + 2023) (8050 + 2023) True (aG + (ovh + 699))
        (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none)
          (fun r => ccM (afterFts pk w (a.toNat % 2 ^ 31) r) Kb)) :=
      h.mono (le_refl _) (le_refl _) (fun hq => ⟨hq, by simp only [ftsAcceptCost, routineSum_c1]; omega⟩)
    exact (SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQ.toP h').pre_mono (fun hash hp => hp.2.1)
  · exact SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP.of_false h (fun hash hp => hcap (capOk_of_pre hdc hp.1 hp.2.2))
def fuelBound : Nat := 16 + (8050 + 2023)
def cycleBoundAll : Nat := 23 + (8050 + 2023)
theorem fuelBound_eq : fuelBound = 10089 := rfl
theorem cycleBoundAll_eq : cycleBoundAll = 10096 := rfl
theorem fuelBound_le : fuelBound ≤ CYCLE_LIMIT := by rw [fuelBound_eq]; unfold CYCLE_LIMIT; norm_num
theorem verify_good (prefixGood : PrefixGood GatePre)
    (fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost))
    (after : AfterGoodBudget FtsOut aG)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (hs : initialState Native.submission .verify (m, pk, w) = some s) :
    SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP Images.InlineNative.image (Pre m w) s fuelBound cycleBoundAll True (aG + (ovh + 699) + 23)
      (ccM (ClaudeWCT.W9.T3M.verifyP m pk w) Kb) := by
  rw [verifyP_eq, ccM_bind]
  exact prefixGood m pk w s hs (Pre m w) (8050 + 2023) (8050 + 2023) (aG + (ovh + 699)) True
    (fun o => ccM (match o with
      | some N => afterDigest pk w N
      | none => pure false) Kb) (by simp only [ccM_pure, Kb])
    (fun a u hdc hu => afterDigest_good fts after m pk w a u hdc hu)
set_option maxRecDepth 100000 in
theorem init_mk (sI eI : Riscv.Image) (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) :
    initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.InlineNative.image⟩) .verify (m, pk, w) =
      initialState Native.submission .verify (m, pk, w) :=
  rfl
theorem mk_verify (sI eI : Riscv.Image) :
    (⟨sI, eI, Images.InlineNative.image⟩ : ClaudeWCT.W9.T3M.Images).verify = Images.InlineNative.image := rfl
theorem init_exists (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) :
    ∃ s, initialState Native.submission .verify (m, pk, w) = some s := by
  unfold initialState
  simp only [Native.submission_admissible.2 .verify, if_true]
  exact ⟨_, rfl⟩
theorem verify_refines_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.InlineNative.image)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyRefines I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.InlineNative.image at hI
  subst hI
  intro m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.InlineNative.image⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).1
  rw [ccM_Kb] at hg
  rw [run_eq _ .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, Functor.map_map]
  change _ = (fun p => (if p.1 then some () else none, p.2)) <$>
    countCalls (mrealize 0 (ClaudeWCT.W9.T3M.verifyP m pk w))
  rw [← hg, Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT Images.InlineNative.image s) ?_
  funext e
  simp only [toRunResult, obs]
  by_cases h : e.exit = .success
  · simp only [h, decide_true, if_true]; rfl
  · simp only [h, decide_false, if_false, Bool.false_eq_true]; rfl
theorem verify_terminates_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.InlineNative.image)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyTerminates I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.InlineNative.image at hI
  subst hI
  intro hash m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.InlineNative.image⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, mk_verify]
  simp only [toRunResult]
  refine ⟨?_, lt_of_le_of_lt hg.2.1 (by rw [cycleBoundAll_eq]; unfold CYCLE_LIMIT; norm_num)⟩
  simpa using hg.1
set_option maxRecDepth 100000 in
theorem verify_accept_cycles_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.InlineNative.image)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.InlineNative.image at hI
  subst hI
  intro hash m pk w hok hcap h
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.InlineNative.image⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, mk_verify] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT Images.InlineNative.image s)).exit = .success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  have h1 := (hg.2.2 hsucc ⟨hok, hcap⟩).2
  have h2 : aG + (ovh + 699) + 23 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound := by have := H.hnum; omega
  exact le_trans h1 h2
theorem verify_inputs_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.InlineNative.image)
    (H : Inputs GatePre FtsOut ovh aG) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I :=
  ⟨verify_refines_of I hI H, verify_terminates_of I hI H, verify_accept_cycles_of I hI H⟩
end
def I1 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.InlineNative.image⟩
theorem I1_verify : I1.verify = Images.InlineNative.image := rfl
theorem verify_inputs {GatePre : Digest → WBytes → HashOutput → MachineState → Prop}
    {FtsOut : Digest → WBytes → HashOutput → Digest → MachineState → Prop} {ovh aG : Nat}
    (H : Inputs GatePre FtsOut ovh aG) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I1 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I1 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I1 :=
  verify_inputs_of I1 I1_verify H
end W9Fin.V4.Inline
#print axioms W9Fin.V4.Inline.verify_inputs_of
#print axioms W9Fin.V4.Inline.verify_inputs
end
