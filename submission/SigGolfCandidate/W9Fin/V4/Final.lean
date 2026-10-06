import SigGolfCandidate.T3M.Verify.HashAgree
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending
import SigGolfCandidate.T3M.Verify.Init
import SigGolfCandidate.W9Drv.GateDefs

section




namespace W9Fin.V4
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
    (∀ root t, FtsOut pk w a root t → GoodQ t N C Q A (K (some root))) →
    GoodQ u (N + 2023) (C + 2023) Q (A + acceptCost a)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none) K)
def AfterGoodBudget (FtsOut : Digest → WBytes → HashOutput → Digest → MachineState → Prop)
    (acceptCycles : Nat) : Prop :=
  ∀ (pk : Digest) (w : WBytes) (Q : Prop), Q →
    ∀ (a : HashOutput) (root : Digest) (u : MachineState),
      FtsOut pk w a root u →
      GoodQ u 8050 8050 Q acceptCycles (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb)
def PrefixGood (GatePre : Digest → WBytes → HashOutput → MachineState → Prop) : Prop :=
  ∀ (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState),
    initialState submission .verify (m, pk, w) = some s →
    ∀ (P : Hash → Prop) (N C A : Nat) (Q : Prop) (K : Option HashOutput → OracleComp HashSpec Obs),
      K none = pure (false, 0) →
      (∀ a u, (wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit → GatePre pk w a u →
        GoodQP (fun hash => hash (digestQ m w) = a ∧ P hash) u N C Q A (K (some a))) →
      GoodQP P s (N + 16) (C + 23) Q (A + 23) (ccM (ClaudeWCT.W9.T3M.digestP m w) K)
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
    ClaudeWCT.WCT9.jointCost a ≤ 698 := by
  unfold ClaudeWCT.WCT9.capOk ClaudeWCT.WCT9.jointCap at h
  exact of_decide_eq_true h
structure Inputs (GatePre : Digest → WBytes → HashOutput → MachineState → Prop)
    (FtsOut : Digest → WBytes → HashOutput → Digest → MachineState → Prop) (ovh aG : Nat) : Prop where
  prefixGood : PrefixGood GatePre
  fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost)
  after : AfterGoodBudget FtsOut aG
  hnum : 23 + aG + ovh + 698 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound
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
    GoodQP (fun hash => hash (digestQ m w) = a ∧ Pre m w hash) u (8050 + 2023) (8050 + 2023) True
      (aG + (ovh + 698)) (ccM (afterDigest pk w a) Kb) := by
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
    have h' : GoodQ u (8050 + 2023) (8050 + 2023) True (aG + (ovh + 698))
        (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none)
          (fun r => ccM (afterFts pk w (a.toNat % 2 ^ 31) r) Kb)) :=
      h.mono (le_refl _) (le_refl _) (fun hq => ⟨hq, by simp only [ftsAcceptCost, routineSum_c1]; omega⟩)
    exact (GoodQ.toP h').pre_mono (fun hash hp => hp.2.1)
  · exact GoodQP.of_false h (fun hash hp => hcap (capOk_of_pre hdc hp.1 hp.2.2))
def fuelBound : Nat := 16 + (8050 + 2023)
def cycleBoundAll : Nat := 23 + (8050 + 2023)
theorem fuelBound_eq : fuelBound = 10089 := rfl
theorem cycleBoundAll_eq : cycleBoundAll = 10096 := rfl
theorem fuelBound_le : fuelBound ≤ CYCLE_LIMIT := by rw [fuelBound_eq]; unfold CYCLE_LIMIT; norm_num
theorem verify_good (prefixGood : PrefixGood GatePre)
    (fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost))
    (after : AfterGoodBudget FtsOut aG)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (hs : initialState submission .verify (m, pk, w) = some s) :
    GoodQP (Pre m w) s fuelBound cycleBoundAll True (aG + (ovh + 698) + 23)
      (ccM (ClaudeWCT.W9.T3M.verifyP m pk w) Kb) := by
  rw [verifyP_eq, ccM_bind]
  exact prefixGood m pk w s hs (Pre m w) (8050 + 2023) (8050 + 2023) (aG + (ovh + 698)) True
    (fun o => ccM (match o with
      | some N => afterDigest pk w N
      | none => pure false) Kb) (by simp only [ccM_pure, Kb])
    (fun a u hdc hu => afterDigest_good fts after m pk w a u hdc hu)
set_option maxRecDepth 100000 in
theorem init_mk (sI eI : Riscv.Image) (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) :
    initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) =
      initialState submission .verify (m, pk, w) :=
  rfl
theorem mk_verify (sI eI : Riscv.Image) :
    (⟨sI, eI, Images.verifyImage⟩ : ClaudeWCT.W9.T3M.Images).verify = Images.verifyImage := rfl
theorem init_exists (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) :
    ∃ s, initialState submission .verify (m, pk, w) = some s := by
  unfold initialState
  simp only [submission_admissible.2 .verify, if_true]
  exact ⟨_, rfl⟩
theorem verify_refines_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyRefines I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).1
  rw [ccM_Kb] at hg
  rw [run_eq _ .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, Functor.map_map]
  change _ = (fun p => (if p.1 then some () else none, p.2)) <$>
    countCalls (mrealize 0 (ClaudeWCT.W9.T3M.verifyP m pk w))
  rw [← hg, Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT Verify.image s) ?_
  funext e
  simp only [toRunResult, obs]
  by_cases h : e.exit = .success
  · simp only [h, decide_true, if_true]; rfl
  · simp only [h, decide_false, if_false, Bool.false_eq_true]; rfl
theorem verify_terminates_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyTerminates I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro hash m pk w
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, mk_verify]
  simp only [toRunResult]
  refine ⟨?_, lt_of_le_of_lt hg.2.1 (by rw [cycleBoundAll_eq]; unfold CYCLE_LIMIT; norm_num)⟩
  simpa using hg.1
set_option maxRecDepth 100000 in
theorem verify_accept_cycles_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) : ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I := by
  obtain ⟨sI, eI, vI⟩ := I
  change vI = Images.verifyImage at hI
  subst hI
  intro hash m pk w hok hcap h
  obtain ⟨s, hs⟩ := init_exists m pk w
  have hs' : initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) = some s :=
    (init_mk sI eI m pk w).trans hs
  have hg := (verify_good H.prefixGood H.fts H.after m pk w s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq _ hash .verify _ s hs', ClaudeWCT.W9.T3M.submission_verify, mk_verify] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT Images.verifyImage s)).exit = .success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  have h1 := (hg.2.2 hsucc ⟨hok, hcap⟩).2
  have h2 : aG + (ovh + 698) + 23 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound := by have := H.hnum; omega
  exact le_trans h1 h2
theorem verify_inputs_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I :=
  ⟨verify_refines_of I hI H, verify_terminates_of I hI H, verify_accept_cycles_of I hI H⟩
end
def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
theorem I0_verify : I0.verify = Images.verifyImage := rfl
theorem verify_inputs {GatePre : Digest → WBytes → HashOutput → MachineState → Prop}
    {FtsOut : Digest → WBytes → HashOutput → Digest → MachineState → Prop} {ovh aG : Nat}
    (H : Inputs GatePre FtsOut ovh aG) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs_of I0 I0_verify H
end W9Fin.V4
#print axioms W9Fin.V4.verify_inputs_of
#print axioms W9Fin.V4.verify_inputs
end

section




set_option linter.unusedSimpArgs false
namespace W9Fin.V4
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
theorem GoodQP.mono' {P : Hash → Prop} {s : MachineState} {N C A N' C' A' : Nat} {Q : Prop}
    {X : OracleComp HashSpec Obs} (h : GoodQP P s N C Q A X) (hN : N ≤ N') (hC : C ≤ C') (hA : A ≤ A') :
    GoodQP P s N' C' Q A' X := by
  intro F hF
  obtain ⟨h1, h2⟩ := h F (by omega)
  refine ⟨h1, fun hash => ⟨(h2 hash).1, by have := (h2 hash).2.1; omega, fun hs hp => ?_⟩⟩
  obtain ⟨hq, ha⟩ := (h2 hash).2.2 hs hp
  exact ⟨hq, by omega⟩
theorem GoodQP.reject {P : Hash → Prop} {s : MachineState} {Q : Prop} {A : Nat}
    (hf : fetch image s = some (.base .ECALL)) (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) :
    GoodQP P s 1 1 Q A (pure (false, 0)) := by
  have h := GoodQ.reject (Q := Q) (A := A) hf h5 h10
  intro F hF
  obtain ⟨h1, h2⟩ := h F hF
  refine ⟨h1, fun hash => ⟨(h2 hash).1, (h2 hash).2.1, fun hs _ => ?_⟩⟩
  have e := congrArg (evalWithAnswerFn hash) h1
  rw [evalWithAnswerFn_map, evalWithAnswerFn_pure] at e
  simp only [obs, Prod.mk.injEq] at e
  exact absurd (decide_eq_true hs) (by rw [e.1]; decide)
theorem GoodQP.publicHash_bind_pre {P : Hash → Prop} {β : Type} {s : MachineState} {N C A : Nat} {Q : Prop}
    {input : List UInt8} {f : HashOutput → SigGolfCandidate.T3.M β} {K : β → OracleComp HashSpec Obs}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, GoodQP (fun hash => hash (toQ (pad64 input)) = a ∧ P hash) (writeHash s a) N C Q A
      (ccM (f a) K)) :
    GoodQP P s (N + 1) (C + 8 * (toQ (pad64 input)).blocks) Q (A + 8 * (toQ (pad64 input)).blocks)
      (ccM (SigGolfCandidate.T3.publicHash input >>= f) K) := by
  have := GoodQP.query_pre (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]
def Bank (u : MachineState) : Prop :=
  W9Drv.HeaderBank u ∧ W9Drv.SetupMask u ∧ u.getMem (BitVec.ofNat 64 VERIFY_DATA) = BitVec.ofNat 64 0xfff
theorem Bank.congr {s t : MachineState} (h : Bank s)
    (hm : ∀ A, VERIFY_DATA ≤ A → A < VERIFY_DATA + 608 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : Bank t := by
  refine ⟨⟨?_, fun k hk => ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hm _ (by unfold VERIFY_DATA; omega) (by unfold VERIFY_DATA; omega)]
    exact h.1.node
  · rw [hm _ (by unfold TOPLOAD VERIFY_DATA; omega) (by unfold TOPLOAD VERIFY_DATA; omega)]
    exact h.1.top k hk
  · rw [hm _ (by unfold TOPLOAD VERIFY_DATA; omega) (by unfold TOPLOAD VERIFY_DATA; omega)]
    exact h.1.top8
  · rw [hm _ (by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega)
      (by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega)]
    exact h.2.1.child
  · rw [hm _ (by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega)
      (by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega)]
    exact h.2.1.jt
  · rw [hm _ (by omega) (by unfold VERIFY_DATA; omega)]
    exact h.2.2
theorem init_word (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) (j : Nat) (hj : j < 2072) :
    s.getMem (BitVec.ofNat 64 (VERIFY_DATA + 8 * j)) =
      bytesToWordLE (((submission.image .verify).data.drop (8 * j)).take 8) := by
  unfold initialState at h
  simp only [submission_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have hl : inputBuffers submission.sizes submission.layout .verify (m, pk, w) =
      [(0x40, bytes m), (0xA0, bytes pk), (0x800, bytes w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil]
  have lm : (bytes m).length = 32 := length_bytes m
  have lp : (bytes pk).length = 16 := length_bytes pk
  have lw : (bytes w).length = 22984 := length_bytes w
  have lD := verifyData_length
  have eD := dataBase_verify
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set s0 := blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase (submission.image .verify)))
    (submission.image .verify).data
  set s1 := s0.writeBytesAsWords (BitVec.ofNat 64 0x40) (bytes m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x800) (bytes w)
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getMem A =
      s3.getMem A := fun A => by simp [MachineState.setReg, MachineState.getMem]
  have g0 : ∀ A, A < 2 ^ 64 → s0.getMem (BitVec.ofNat 64 A) =
      if VERIFY_DATA ≤ A ∧ A < VERIFY_DATA + 8 * ((17104 + 7) / 8) ∧ (A - VERIFY_DATA) % 8 = 0 then
        bytesToWordLE ((((submission.image .verify).data).drop (A - VERIFY_DATA)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords (submission.image .verify).data blank (dataBase (submission.image .verify)) A
      (by rw [lD, eD]; unfold VERIFY_DATA; omega) hA, lD, eD]; rfl
  have g1 : ∀ A, A < 2 ^ 64 → s1.getMem (BitVec.ofNat 64 A) =
      if 0x40 ≤ A ∧ A < 0x40 + 8 * ((32 + 7) / 8) ∧ (A - 0x40) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 0x40)).take 8) else s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s0 0x40 A (by rw [lm]; omega) hA, lm]
  have g2 : ∀ A, A < 2 ^ 64 → s2.getMem (BitVec.ofNat 64 A) =
      if 0xA0 ≤ A ∧ A < 0xA0 + 8 * ((16 + 7) / 8) ∧ (A - 0xA0) % 8 = 0 then
        bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8) else s1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s1 0xA0 A (by rw [lp]; omega) hA, lp]
  have g3 : ∀ A, A < 2 ^ 64 → s3.getMem (BitVec.ofNat 64 A) =
      if 0x800 ≤ A ∧ A < 0x800 + 8 * ((22984 + 7) / 8) ∧ (A - 0x800) % 8 = 0 then
        bytesToWordLE (((bytes w).drop (A - 0x800)).take 8) else s2.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s2 0x800 A (by rw [lw]; omega) hA, lw]
  rw [gm, g3 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g2 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g1 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g0 _ (by unfold VERIFY_DATA; omega), if_pos (by unfold VERIFY_DATA; omega),
    show VERIFY_DATA + 8 * j - VERIFY_DATA = 8 * j by omega]
set_option maxRecDepth 200000 in
theorem init_bank (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : Bank s := by
  refine ⟨⟨?_, fun k hk => ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [show 0xffbf40 + 8 = VERIFY_DATA + 8 * 67 by unfold VERIFY_DATA; omega, init_word m pk w s h 67 (by omega)]
    decide +kernel
  · rw [show TOPLOAD + 8 * k = VERIFY_DATA + 8 * (71 + k) by unfold TOPLOAD VERIFY_DATA; omega,
      init_word m pk w s h (71 + k) (by omega)]
    interval_cases k <;> decide +kernel
  · rw [show TOPLOAD - 8 = VERIFY_DATA + 8 * 70 by unfold TOPLOAD VERIFY_DATA; omega,
      init_word m pk w s h 70 (by omega)]
    decide +kernel
  · rw [show W9Drv.setupMaskAddr + 16 = VERIFY_DATA + 8 * 68 by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega,
      init_word m pk w s h 68 (by omega)]
    decide +kernel
  · rw [show W9Drv.setupMaskAddr + 24 = VERIFY_DATA + 8 * 69 by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega,
      init_word m pk w s h 69 (by omega)]
    decide +kernel
  · rw [show VERIFY_DATA = VERIFY_DATA + 8 * 0 by rfl, init_word m pk w s h 0 (by omega)]
    decide +kernel
abbrev cw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def rejectPc : Nat := 743
def rejSpec (steps : Nat) (brs : List Br) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], rejectPc, true, steps, brs, none, steps⟩
def lwuDc : E := .un (.ld .wu 0) (.ld (cw 0x810))
def proBr (d : Bool) : Br := ⟨.ne, .bin .srl lwuDc (cw 21), .c 0, d⟩
def proSpec : Spec :=
  ⟨[(.x4, cw 3073)],
    [(⟨none, BitVec.ofNat 64 0x28⟩, .ld (cw 0x808)), (⟨none, BitVec.ofNat 64 0x20⟩, .ld (cw 0x800)),
      (⟨none, BitVec.ofNat 64 0x30⟩, cw 0xc01), (⟨none, BitVec.ofNat 64 0x38⟩, .bin (.st .w 4) (.ld (cw 0x38)) lwuDc)],
    14, true, 13, [proBr false], none, 13⟩
def kMask0 : List (Reg × Word) := k0.map fun p => if p.1 = .x18 then (.x18, 0xfff) else p
def proPost : List (Reg × Word) := baseK ++ [(.x10, 32), (.x11, 64), (.x12, 96)]
theorem proCheck : specB [] [] baseK (runAt kMask0 [] 1 [.br false]) proSpec [] proPost [.x2] = true := by
  decide +kernel
theorem proRejCheck : specB [] [] [] (runAt kMask0 [] 1 [.br true]) (rejSpec 6 [proBr true]) [] [] [] = true := by
  decide +kernel
theorem lwuDc_eval (w : WBytes) (s : MachineState) (hW : WitAll w s) :
    lwuDc.eval s = BitVec.ofNat 64 (wdc w).toNat := by
  have h2 : s.getMem (BitVec.ofNat 64 0x810) = wword w 2 := hW 2 (by unfold WX; omega)
  apply BitVec.eq_of_toNat_eq
  show (LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 0x810)) 0).toNat = _
  rw [h2]
  simp only [LoadKind.fromWord, extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, wword_toNat, wdc, wle32, dcOff,
    BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
  have : (w.toNat / 2 ^ (64 * 2) % 2 ^ 64 / 2 ^ (0 / 4 * 32) % 2 ^ 32) = w.toNat / 2 ^ 128 % 2 ^ 32 := by
    rw [show 0 / 4 * 32 = 0 by rfl, pow_zero, Nat.div_one, show 64 * 2 = 128 by rfl,
      Nat.mod_mod_of_dvd _ (by norm_num)]
  rw [this]
theorem dc_lt (w : WBytes) : (wdc w).toNat < 2 ^ 32 := (wdc w).isLt
theorem proBr_iff (w : WBytes) (s : MachineState) (hW : WitAll w s) (d : Bool) :
    Br.holds s (proBr d) ↔ d = decide ((wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit) := by
  have hd := dc_lt w
  simp only [proBr, Br.holds, CmpOp.eval, E.eval, BinOp.eval, lwuDc_eval w s hW]
  have e : (BitVec.ofNat 64 (wdc w).toNat >>> ((BitVec.ofNat 64 21).toNat % 64)) =
      BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 21) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show (wdc w).toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (wdc w).toNat / 2 ^ 21 < 2 ^ 64 by omega)]
  rw [e]
  by_cases h : (wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit
  · have hne : BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 21) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [toNat_ofNat_lt (by omega)] at this
      unfold ClaudeWCT.WCT9.digestAttemptLimit at h
      simp at this; omega
    rw [show (BitVec.ofNat 64 ((wdc w).toNat / 2 ^ 21) != (0 : Word)) = true from bne_iff_ne.mpr hne,
      decide_eq_true h]
    exact eq_comm
  · have h0 : (wdc w).toNat / 2 ^ 21 = 0 := by unfold ClaudeWCT.WCT9.digestAttemptLimit at h; omega
    rw [h0, decide_eq_false h, show (BitVec.ofNat 64 0 != (0 : Word)) = false by decide]
    exact eq_comm
structure DgPre (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (t : MachineState) : Prop where
  pc : t.pc = pcOf 14
  known : KnownOK proPost t
  wit : WitAll w t
  pk : PkOK pk t
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → t.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK t
  sp : t.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
  bank : Bank t
structure DgOut (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState) :
    Prop where
  pc : u.pc = pcOf 15
  known : KnownOK proPost u
  wit : WitAll w u
  pk : PkOK pk u
  nwords : ∀ k, k < 4 → u.getMem (BitVec.ofNat 64 (0x60 + 8 * k)) = a.extractLsb' (64 * k) 64
  zero : ∀ A, A < WIT → (A < 0x20 ∨ (0x80 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → u.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK u
  sp : u.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
  bank : Bank u
structure ProInit (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) : Prop where
  known : KnownOK kMask0 s
  pc : s.pc = pcOf 1
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (0x40 + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0x40 ∨ (0x60 ≤ A ∧ A < 0xA0) ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  sp : s.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
theorem digest_tail (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (s : MachineState)
    (hs : ProInit m pk w s) (hb : Bank s) :
    ((wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit → ∃ u, Steps image s 6 6 u ∧
        fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit → ∃ t, Steps image s 13 13 t ∧
        fetch image t = some (.base .ECALL) ∧
        hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (digestInput (wrho w) m (wdc w))) ∧
        DgPre m pk w t) := by
  have hk : KnownOK kMask0 s := hs.known
  constructor
  · intro hge
    obtain ⟨u, hu⟩ := spec_run proRejCheck s hs.pc hk (by
      intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
      exact (proBr_iff w s hs.wit true).mpr (by simp [hge])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
      hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · intro hlt
    obtain ⟨t, ht⟩ := spec_run proCheck s hs.pc hk (by
      intro b hb; simp only [proSpec, List.mem_singleton] at hb; subst hb
      exact (proBr_iff w s hs.wit false).mpr (by simp; omega)) (by simp)
    have hm : ∀ A, t.getMem A = memEval s proSpec.mem A := ht.mem
    have hkt : KnownOK proPost t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 32 := hkt (.x10, 32) (by simp [proPost])
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by simp [proPost])
    have h12 : t.getReg .x12 = BitVec.ofNat 64 96 := hkt (.x12, 96) (by simp [proPost])
    have frame : ∀ A, A < 2 ^ 64 → A ≠ 0x20 → A ≠ 0x28 → A ≠ 0x30 → A ≠ 0x38 →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [proSpec, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simpa using fun h => by omega⟩
    refine ⟨t, ht.steps, ht.ecall rfl, ?_, ?_, ?_⟩
    · exact hashArgs_of t 32 64 96 h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hl := digestInput_length (wrho w) m (wdc w)
      rw [pad64_digestInput]
      apply hashInput_words8 t _ 32 hl h10 (by decide) (by decide) h11
      rw [wordsOf_digestInput]
      have e20 : t.getMem (BitVec.ofNat 64 32) = dlo (wrho w) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 32 = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 32 = BitVec.ofNat 64 0x20) = True by decide, if_true, if_false, E.eval]
        have h0 : s.getMem (BitVec.ofNat 64 0x800) = wword w 0 := hs.wit 0 (by unfold WX; omega)
        rw [h0]
        exact (Verify.wdig_lo w 0).symm
      have e28 : t.getMem (BitVec.ofNat 64 (32 + 8)) = dhi (wrho w) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 8) = BitVec.ofNat 64 0x28) = True by decide, if_true, E.eval]
        have h1 : s.getMem (BitVec.ofNat 64 0x808) = wword w 1 := hs.wit 1 (by unfold WX; omega)
        rw [h1]
        exact (Verify.wdig_hi w 0).symm
      have e30 : t.getMem (BitVec.ofNat 64 (32 + 16)) = BitVec.ofNat 64 (hdr0 12 0 0 0) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x20) = False by decide,
          show (BitVec.ofNat 64 (32 + 16) = BitVec.ofNat 64 0x30) = True by decide, if_true, if_false, E.eval]
        rfl
      have e38 : t.getMem (BitVec.ofNat 64 (32 + 24)) = BitVec.ofNat 64 (hdr1 0 (wdc w).toNat) := by
        rw [hm]; simp only [proSpec, memEval, Addr.eval]
        simp only [show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x28) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x20) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x30) = False by decide,
          show (BitVec.ofNat 64 (32 + 24) = BitVec.ofNat 64 0x38) = True by decide, if_true, if_false]
        show StoreKind.merge .w (s.getMem (BitVec.ofNat 64 0x38)) 4 (lwuDc.eval s) = _
        rw [hs.zero 0x38 (by unfold WIT; omega) (by omega), lwuDc_eval w s hs.wit]
        exact merge_hi 0 (wdc w).toNat
      have em : ∀ k, k < 4 → t.getMem (BitVec.ofNat 64 (32 + 32 + 8 * k)) = m.extractLsb' (64 * k) 64 := by
        intro k hk
        rw [frame _ (by omega) (by omega) (by omega) (by omega) (by omega), ← hs.msg k hk]
      rw [e20, e28, e30, e38, show 32 + 32 = 32 + 32 + 8 * 0 by rfl, em 0 (by omega),
        show 32 + 40 = 32 + 32 + 8 * 1 by rfl, em 1 (by omega), show 32 + 48 = 32 + 32 + 8 * 2 by rfl,
        em 2 (by omega), show 32 + 56 = 32 + 32 + 8 * 3 by rfl, em 3 (by omega)]
    · refine ⟨ht.pc rfl, hkt, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [frame _ (by unfold WIT WX at *; omega) (by unfold WIT; omega) (by unfold WIT; omega)
          (by unfold WIT; omega) (by unfold WIT; omega)]
        exact hs.wit j hj
      · exact ⟨(frame 0xA0 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hs.pk.1,
          (frame 0xA8 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hs.pk.2⟩
      · intro A hA hz
        unfold WIT at hA
        rw [frame A (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hs.zero A hA (by omega)
      · apply hs.data.congr
        intro A hA hEnd
        exact frame A (by omega) (by unfold TAB at hA; omega)
          (by unfold TAB at hA; omega) (by unfold TAB at hA; omega)
          (by unfold TAB at hA; omega)
      · rw [ht.keep .x2 (by simp)]; exact hs.sp
      · exact hb.congr (fun A hA _ => frame A (by unfold VERIFY_DATA at *; omega)
          (by unfold VERIFY_DATA at hA; omega) (by unfold VERIFY_DATA at hA; omega)
          (by unfold VERIFY_DATA at hA; omega) (by unfold VERIFY_DATA at hA; omega))
def maskObl : Oblig := .valid ⟨some (.reg .x2), 0⟩ 8
def maskSpec : Spec := ⟨[(.x18, .ld (.reg .x2))], [], 1, false, 1, [], none, 1⟩
def k0m : List (Reg × Word) := k0.filter fun p => p.1 ≠ .x18
theorem maskCheck : specB [] [] [] (runAt k0 [1] 0 []) maskSpec [maskObl] k0m [.x2] = true := by
  decide +kernel
theorem mask_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) :
    ∃ s1, Steps image s 1 1 s1 ∧ ProInit m pk w s1 ∧ Bank s1 := by
  obtain ⟨s1, h1⟩ := spec_run maskCheck s hs.pc hs.known (by simp [maskSpec]) (by
    intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    show accessValid (s.getReg .x2 + 0) 8 = true
    rw [hs.sp]
    decide +kernel)
  have hm : ∀ A, s1.getMem A = s.getMem A := fun A => h1.mem A
  have h18 : s1.getReg .x18 = 0xfff := by
    rw [h1.regs (.x18, .ld (.reg .x2)) (by simp [maskSpec])]
    show s.getMem (s.getReg .x2) = _
    rw [hs.sp]
    exact hb.2.2
  have hknown : KnownOK kMask0 s1 := by
    intro p hp
    simp only [kMask0, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    split
    · rename_i heq
      simpa only [heq] using h18
    · rename_i hne
      exact h1.known q (List.mem_filter.mpr ⟨hq, by simpa using hne⟩)
  refine ⟨s1, h1.steps, ⟨hknown, h1.pc rfl, fun k hk => (hm _).trans (hs.msg k hk),
    ⟨(hm _).trans hs.pk.1, (hm _).trans hs.pk.2⟩, fun j hj => (hm _).trans (hs.wit j hj),
    fun A hA hz => (hm _).trans (hs.zero A hA hz), hs.data.congr (fun A _ _ => hm _),
    (h1.keep .x2 (by simp)).trans hs.sp⟩, hb.congr (fun A _ _ => hm _)⟩
theorem digest_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) :
    ((wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit → ∃ u, Steps image s 7 7 u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit → ∃ t, Steps image s 14 14 t ∧
      fetch image t = some (.base .ECALL) ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (pad64 (digestInput (wrho w) m (wdc w))) ∧ DgPre m pk w t) := by
  obtain ⟨s0, st, hs0, hb0⟩ := mask_step m pk w s hs hb
  obtain ⟨hr, ha⟩ := digest_tail m pk w s0 hs0 hb0
  constructor
  · intro h
    obtain ⟨u, stu, hf, h5, h10⟩ := hr h
    exact ⟨u, st.trans stu, hf, h5, h10⟩
  · intro h
    obtain ⟨t, stt, hf, hv, hin, hp⟩ := ha h
    exact ⟨t, st.trans stt, hf, hv, hin, hp⟩
theorem digest_out (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (t : MachineState)
    (ht : DgPre m pk w t) (a : HashOutput) : DgOut m pk w a (writeHash t a) := by
  have h12 : t.getReg .x12 = BitVec.ofNat 64 96 := ht.known (.x12, 96) (by simp [proPost])
  refine ⟨?_, ht.known.writeHash a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, ht.pc]; rfl
  · intro j hj
    rw [writeHash_frame t a 96 _ h12 (by unfold WIT WX at *; omega) (by omega) (Or.inr (by unfold WIT; omega))]
    exact ht.wit j hj
  · exact ⟨(writeHash_frame t a 96 0xA0 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.1,
      (writeHash_frame t a 96 0xA8 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.2⟩
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact writeHash_at0 t a 96 h12 (by omega)
    · exact writeHash_at8 t a 96 h12 (by omega)
    · exact writeHash_at16 t a 96 h12 (by omega)
    · exact writeHash_at24 t a 96 h12 (by omega)
  · intro A hA hz
    unfold WIT at hA
    rw [writeHash_frame t a 96 A h12 (by omega) (by omega) (by omega)]
    exact ht.zero A (by unfold WIT; omega) (by omega)
  · apply ht.data.congr
    intro A hA hEnd
    exact writeHash_frame t a 96 A h12 (by omega) (by omega)
      (Or.inr (by unfold TAB at hA; omega))
  · rw [writeHash_getReg]; exact ht.sp
  · exact ht.bank.congr (fun A hA _ => writeHash_frame t a 96 A h12 (by unfold VERIFY_DATA at *; omega) (by omega)
      (Or.inr (by unfold VERIFY_DATA at hA; omega)))
theorem digestP_good (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) {P : Hash → Prop} {N C A : Nat} {Q : Prop}
    (K : Option HashOutput → OracleComp HashSpec Obs) (hK : K none = pure (false, 0))
    (hcont : ∀ a u, (wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit → DgOut m pk w a u →
      GoodQP (fun hash => hash (digestQ m w) = a ∧ P hash) u N C Q A (K (some a))) :
    GoodQP P s (N + 15) (C + 22) Q (A + 22) (ccM (ClaudeWCT.W9.T3M.digestP m w) K) := by
  obtain ⟨hrej, hacc⟩ := digest_step m pk w s hs hb
  unfold ClaudeWCT.W9.T3M.digestP
  by_cases hdc : (wdc w).toNat ≥ ClaudeWCT.WCT9.digestAttemptLimit
  · rw [if_pos hdc, ccM_pure, hK]
    obtain ⟨u, hst, hf, h5, h10⟩ := hrej hdc
    exact GoodQP.steps' hst (GoodQP.reject (P := P) (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega)
      (by omega)
  · rw [if_neg hdc, ccM_map]
    obtain ⟨t, hst, hf, hv, hin, hpre⟩ := hacc (by omega)
    unfold SigGolfCandidate.T3.digest
    have h5 : t.getReg .x5 = 0 := hpre.known (.x5, 0) (by simp [proPost, baseK])
    have := GoodQP.publicHash_bind_pre (P := P) (f := pure) (K := fun a => K (some a)) hf h5 hv hin (fun a => by
      rw [ccM_pure]; exact hcont a _ (by omega) (digest_out m pk w t hpre a))
    rw [bind_pure, blocks_digestInput] at this
    exact GoodQP.steps' hst this (by omega) (by omega) (by omega)
def hookSpec : Spec := ⟨[(.x16, .ld (cw 0x60))], [], 16, false, 1, [], none, 1⟩
theorem hookCheck : specB [] [] baseK (runAt proPost [16] 15 []) hookSpec [] proPost [.x2] = true := by
  decide +kernel
theorem gatePre_of_hook (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (a : HashOutput)
    (u : MachineState) (hu : DgOut m pk w a u) :
    ∃ t, Steps image u 1 1 t ∧ W9Drv.GatePre pk w a t := by
  have h5 : u.getReg .x5 = 0 := hu.known (.x5, 0) (by simp [proPost, baseK])
  have h18 : u.getReg .x18 = 0xFFF := hu.known (.x18, 0xFFF) (by simp [proPost, baseK])
  have hglob : Glob baseK w pk u := by
    refine ⟨?_, hu.wit.hdr, hu.pk, ?_, ?_, hu.data⟩
    · intro p hp
      simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact h5
      · exact h18
    · intro A hA
      simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl <;> exact hu.zero _ (by unfold WIT; omega) (by omega)
    · show (u.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hu.zero CTRW (by unfold CTRW WIT; omega) (by unfold CTRW; omega)]
      rfl
  obtain ⟨t, ht⟩ := spec_run hookCheck u hu.pc hu.known (by simp [hookSpec]) (by simp)
  have e : ∀ A, t.getMem A = u.getMem A := fun A => ht.mem A
  have h16 : t.getReg .x16 = a.extractLsb' 0 64 := by
    rw [ht.regs (.x16, .ld (cw 0x60)) (by simp [hookSpec])]
    show u.getMem (BitVec.ofNat 64 0x60) = _
    simpa using hu.nwords 0 (by decide)
  refine ⟨t, ht.steps, ⟨ht.pc rfl, ht.glob baseK w pk hglob (RelOK.nil u), h16,
    ht.known (.x11, 64) (by simp [proPost]),
    ⟨(e _).trans (hu.zero 1024 (by unfold WIT; omega) (by omega)),
      (e _).trans (hu.zero 1032 (by unfold WIT; omega) (by omega))⟩,
    fun k hk => (e _).trans (hu.nwords k hk),
    ⟨(e _).trans hu.bank.1.node, fun k hk => (e _).trans (hu.bank.1.top k hk), (e _).trans hu.bank.1.top8⟩,
    fun j hj => (e _).trans (hu.wit j hj),
    ⟨(e _).trans hu.bank.2.1.child, (e _).trans hu.bank.2.1.jt⟩,
    by rw [ht.keep .x2 (by simp), hu.sp]; rfl⟩⟩
theorem prefixGood : PrefixGood W9Drv.GatePre := by
  intro m pk w s hs P N C A Q K hK hcont
  have h := digestP_good m pk w s (init_ok m pk w s hs) (init_bank m pk w s hs) (P := P) (N := N + 1)
    (C := C + 1) (A := A + 1) (Q := Q) K hK (fun a u hdc hu => by
      obtain ⟨t, hst, hpre⟩ := gatePre_of_hook m pk w a u hu
      exact GoodQP.steps' hst (hcont a t hdc hpre) le_rfl le_rfl le_rfl)
  exact GoodQP.mono' h (by omega) (by omega) (by omega)
end W9Fin.V4
#print axioms W9Fin.V4.prefixGood
end

section

namespace W9Fin.V4
theorem verify_inputs_x {FtsOut : SigGolfCandidate.T3.Digest → SigGolfCandidate.T3M.WBytes →
      SigGolfCandidate.T3.HashOutput → SigGolfCandidate.T3.Digest → RiscvZkvm.Rv64.MachineState → Prop}
    {ovh aG : Nat}
    (fts : FtsGoodByCost W9Drv.GatePre FtsOut
      (ftsAcceptCost ovh ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost))
    (after : AfterGoodBudget FtsOut aG)
    (hnum : 23 + aG + ovh + 698 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs ⟨prefixGood, fts, after, hnum⟩
end W9Fin.V4
#print axioms W9Fin.V4.verify_inputs_x
end
