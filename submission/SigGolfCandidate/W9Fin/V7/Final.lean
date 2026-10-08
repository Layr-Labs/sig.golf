import SigGolfCandidate.T3M.Verify.Init
import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.T3M.Verify.HashAgree
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending

section



namespace W9Fin.V7
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
abbrev WB := ClaudeWCT.W9.T3M.WBytes
def digestQ (m : SigGolfCandidate.T3.Message) (w : WB) : Query :=
  toQ (pad64 (digestInput (ClaudeWCT.W9.T3M.wrho w) m (ClaudeWCT.W9.T3M.wdc w)))
def ftsAcceptCost (overhead : Nat) (a : HashOutput) : Nat :=
  overhead + ClaudeWCT.WCT9.jointCost a
def FtsGoodByCost (GatePre : Digest → WB → HashOutput → MachineState → Prop)
    (FtsOut : Digest → WB → HashOutput → Digest → MachineState → Prop)
    (acceptCost : HashOutput → Nat) : Prop :=
  ∀ (pk : Digest) (w : WB) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs),
    GatePre pk w a u →
    K none = pure (false, 0) →
    (∀ root t, FtsOut pk w a root t → GoodQ t N C Q A (K (some root))) →
    GoodQ u (N + 2023) (C + 2023) Q (A + acceptCost a)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none) K)
def afterFts (pk : Digest) (w : WB) (index : Nat) (r : Option Digest) : SigGolfCandidate.T3.M Bool :=
  match r with
  | some root => do
      let __x ← ClaudeWCT.W9.T3M.layersBC w index 4 (.forest root)
      match __x with
      | some root => pure (root == pk)
      | _ => pure false
  | _ => pure false
def AfterGoodBudget (FtsOut : Digest → WB → HashOutput → Digest → MachineState → Prop)
    (acceptCycles : Nat) : Prop :=
  ∀ (pk : Digest) (w : WB) (Q : Prop), Q →
    ∀ (a : HashOutput) (root : Digest) (u : MachineState),
      FtsOut pk w a root u →
      GoodQ u 8050 8050 Q acceptCycles (ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) (some root)) Kb)
def PrefixGood (GatePre : Digest → WB → HashOutput → MachineState → Prop) : Prop :=
  ∀ (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 21484) (s : MachineState),
    initialState submission .verify (m, pk, w) = some s →
    ∀ (P : Hash → Prop) (N C A : Nat) (Q : Prop) (K : Option HashOutput → OracleComp HashSpec Obs),
      K none = pure (false, 0) →
      (∀ a u, (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow → GatePre pk w a u →
        GoodQP (fun hash => hash (digestQ m w) = a ∧ P hash) u N C Q A (K (some a))) →
      GoodQP P s (N + 10) (C + 14) Q (A + 14) (ccM (ClaudeWCT.W9.T3M.digestP m w) K)
end W9Fin.V7
end

section




set_option linter.unusedSimpArgs false
namespace W9Fin.V7
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
  W9Drv.ForestData u ∧ W9Drv.HeaderBank u ∧ W9Drv.SetupMask u ∧
    u.getMem (BitVec.ofNat 64 VERIFY_DATA) = BitVec.ofNat 64 0xfff ∧
    u.getMem (BitVec.ofNat 64 (VERIFY_DATA + 8)) = BitVec.ofNat 64 23504
theorem Bank.congr {s t : MachineState} (h : Bank s)
    (hm : ∀ A, VERIFY_DATA ≤ A → A < VERIFY_DATA + 472 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : Bank t := by
  obtain ⟨⟨f0, f1, f2⟩, ⟨htop, htop8⟩, ⟨mc, mj, mk⟩, d0, d8⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ⟨fun k hk => ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact f0
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact f1
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact f2
  · rw [hm _ (by unfold TOPLOAD VERIFY_DATA; omega) (by unfold TOPLOAD VERIFY_DATA; omega)]
    exact htop k hk
  · rw [hm _ (by unfold TOPLOAD VERIFY_DATA; omega) (by unfold TOPLOAD VERIFY_DATA; omega)]
    exact htop8
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact mc
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact mj
  · rw [hm _ (by unfold W9Drv.dataBase7 VERIFY_DATA; omega) (by unfold W9Drv.dataBase7 VERIFY_DATA; omega)]
    exact mk
  · rw [hm _ (le_refl _) (by unfold VERIFY_DATA; omega)]
    exact d0
  · rw [hm _ (by omega) (by omega)]
    exact d8
theorem init_word (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 21484) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) (j : Nat) (hj : j < 2116) :
    s.getMem (BitVec.ofNat 64 (VERIFY_DATA + 8 * j)) =
      bytesToWordLE (((submission.image .verify).data.drop (8 * j)).take 8) := by
  unfold initialState at h
  simp only [submission_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have hl : inputBuffers submission.sizes submission.layout .verify (m, pk, w) =
      [(0x5BF0, bytes m), (0xA0, bytes pk), (0x800, bytes w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil]
  have lm : (bytes m).length = 32 := length_bytes m
  have lp : (bytes pk).length = 16 := length_bytes pk
  have lw : (bytes w).length = 21484 := length_bytes w
  have lD := verifyData_length
  have eD := dataBase_verify
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set s0 := blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase (submission.image .verify)))
    (submission.image .verify).data
  set s1 := s0.writeBytesAsWords (BitVec.ofNat 64 0x5BF0) (bytes m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x800) (bytes w)
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getMem A =
      s3.getMem A := fun A => by simp [MachineState.setReg, MachineState.getMem]
  have g0 : ∀ A, A < 2 ^ 64 → s0.getMem (BitVec.ofNat 64 A) =
      if VERIFY_DATA ≤ A ∧ A < VERIFY_DATA + 8 * ((16928 + 7) / 8) ∧ (A - VERIFY_DATA) % 8 = 0 then
        bytesToWordLE ((((submission.image .verify).data).drop (A - VERIFY_DATA)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords (submission.image .verify).data blank (dataBase (submission.image .verify)) A
      (by rw [lD, eD]; unfold VERIFY_DATA; omega) hA, lD, eD]; rfl
  have g1 : ∀ A, A < 2 ^ 64 → s1.getMem (BitVec.ofNat 64 A) =
      if 0x5BF0 ≤ A ∧ A < 0x5BF0 + 8 * ((32 + 7) / 8) ∧ (A - 0x5BF0) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 0x5BF0)).take 8) else s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s0 0x5BF0 A (by rw [lm]; omega) hA, lm]
  have g2 : ∀ A, A < 2 ^ 64 → s2.getMem (BitVec.ofNat 64 A) =
      if 0xA0 ≤ A ∧ A < 0xA0 + 8 * ((16 + 7) / 8) ∧ (A - 0xA0) % 8 = 0 then
        bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8) else s1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s1 0xA0 A (by rw [lp]; omega) hA, lp]
  have g3 : ∀ A, A < 2 ^ 64 → s3.getMem (BitVec.ofNat 64 A) =
      if 0x800 ≤ A ∧ A < 0x800 + 8 * ((21484 + 7) / 8) ∧ (A - 0x800) % 8 = 0 then
        bytesToWordLE (((bytes w).drop (A - 0x800)).take 8) else s2.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s2 0x800 A (by rw [lw]; omega) hA, lw]
  rw [gm, g3 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g2 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g1 _ (by unfold VERIFY_DATA; omega), if_neg (by unfold VERIFY_DATA; omega),
    g0 _ (by unfold VERIFY_DATA; omega), if_pos (by unfold VERIFY_DATA; omega),
    show VERIFY_DATA + 8 * j - VERIFY_DATA = 8 * j by omega]
set_option maxRecDepth 200000 in
theorem init_bank (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 21484) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : Bank s := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨fun k hk => ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [show W9Drv.dataBase7 + 16 = VERIFY_DATA + 8 * 2 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 2 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 24 = VERIFY_DATA + 8 * 3 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 3 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 32 = VERIFY_DATA + 8 * 4 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 4 (by omega)]
    decide +kernel
  · rw [show TOPLOAD + 8 * k = VERIFY_DATA + 8 * (49 + k) by unfold TOPLOAD VERIFY_DATA; omega,
      init_word m pk w s h (49 + k) (by omega)]
    interval_cases k <;> decide +kernel
  · rw [show TOPLOAD - 8 = VERIFY_DATA + 8 * 48 by unfold TOPLOAD VERIFY_DATA; omega,
      init_word m pk w s h 48 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 368 = VERIFY_DATA + 8 * 46 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 46 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 376 = VERIFY_DATA + 8 * 47 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 47 (by omega)]
    decide +kernel
  · rw [show W9Drv.dataBase7 + 464 = VERIFY_DATA + 8 * 58 by unfold W9Drv.dataBase7 VERIFY_DATA; omega,
      init_word m pk w s h 58 (by omega)]
    decide +kernel
  · rw [show VERIFY_DATA = VERIFY_DATA + 8 * 0 by rfl, init_word m pk w s h 0 (by omega)]
    decide +kernel
  · rw [show VERIFY_DATA + 8 = VERIFY_DATA + 8 * 1 by rfl, init_word m pk w s h 1 (by omega)]
    decide +kernel
theorem extract_top_word {n : Nat} (w : BitVec (8 * n)) (j : Nat) (h : 8 * n ≤ 64 * j + 32) :
    w.extractLsb' (64 * j) 64 = BitVec.ofNat 64 (w.extractLsb' (64 * j) 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hw : w.toNat / 2 ^ (64 * j) < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    exact lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (lt_trans hw (by norm_num))]
/-- The witness ends with the 32-bit digest counter at byte 21480, so the last loaded word is that
counter zero-extended: the loader pads the half-filled word with zeros. -/
theorem wword_dc (w : WB) : wword w 2685 = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wdc w).toNat := by
  unfold wword ClaudeWCT.W9.T3M.wdc ClaudeWCT.W9.T3M.wle32 ClaudeWCT.W9.T3M.dcOff
  exact extract_top_word w 2685 (by norm_num)
theorem wdc_eq_of_lt (w : WB) (h : (ClaudeWCT.W9.T3M.wdcWord w).toNat < 2 ^ 32) :
    (ClaudeWCT.W9.T3M.wdc w).toNat = (ClaudeWCT.W9.T3M.wdcWord w).toNat := by
  simp only [ClaudeWCT.W9.T3M.wdc, ClaudeWCT.W9.T3M.wle32, ClaudeWCT.W9.T3M.wdcWord, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow] at h ⊢
  rw [← Nat.mod_mod_of_dvd (w.toNat / 2 ^ (8 * ClaudeWCT.W9.T3M.dcOff)) (show 2 ^ 32 ∣ 2 ^ 64 by norm_num),
    Nat.mod_eq_of_lt h]
theorem digest_words (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    wordsOf (digestInput rho m c) =
      [dlo rho, dhi rho, 0, BitVec.ofNat 64 c.toNat,
        m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64, m.extractLsb' 192 64] :=
  wordsOf_digestInput rho m c
abbrev cw (k : Nat) : E := .c (BitVec.ofNat 64 k)
def entrySpec : Spec := ⟨[], [], 32771, false, 1, [], none, 1⟩
theorem entryCheck : specB [] [] [] (runAt k0 [32771] 0 []) entrySpec [] k0 [.x2] = true := by
  decide +kernel
structure EntOK (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState) : Prop where
  known : KnownOK k0 s
  pc : s.pc = pcOf 32771
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (MSGADDR + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0xA0 ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  sp : s.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
theorem entry_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) :
    ∃ s1, Steps image s 1 1 s1 ∧ EntOK m pk w s1 ∧ Bank s1 := by
  obtain ⟨s1, h1⟩ := spec_run entryCheck s hs.pc hs.known (by simp [entrySpec]) (by simp)
  have hm : ∀ A, s1.getMem A = s.getMem A := fun A => h1.mem A
  refine ⟨s1, h1.steps, ⟨h1.known, h1.pc rfl, fun k hk => (hm _).trans (hs.msg k hk),
    ⟨(hm _).trans hs.pk.1, (hm _).trans hs.pk.2⟩, fun j hj => (hm _).trans (hs.wit j hj),
    fun A hA hz => (hm _).trans (hs.zero A hA hz), hs.data.congr (fun A _ _ => hm _),
    (h1.keep .x2 (by simp)).trans hs.sp⟩, hb.congr (fun A _ _ => hm _)⟩
def kSp : List (Reg × Word) := k0 ++ [(.x2, BitVec.ofNat 64 VERIFY_DATA)]
def ldSpec : Spec :=
  ⟨[(.x18, .ld (cw VERIFY_DATA)), (.x10, .ld (cw (VERIFY_DATA + 8)))], [], 32773, false, 2, [], none, 2⟩
def kLd : List (Reg × Word) := kSp.filter fun p => p.1 ≠ .x18 ∧ p.1 ≠ .x10
theorem ldCheck : specB [] [] [] (runAt kSp [32773] 32771 []) ldSpec [] kLd [] = true := by
  decide +kernel
def kPro : List (Reg × Word) :=
  kSp.map fun p => if p.1 = .x18 then (.x18, 0xfff) else if p.1 = .x10 then (.x10, 23504) else p
structure ProInit (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState) : Prop where
  known : KnownOK kPro s
  pc : s.pc = pcOf 32773
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (MSGADDR + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0xA0 ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  sp : s.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
theorem kSp_ok {m : SigGolfCandidate.T3.Message} {pk : Digest} {w : WB} {s : MachineState} (hs : EntOK m pk w s) :
    KnownOK kSp s := by
  intro p hp
  simp only [kSp, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact hs.known p hp
  · exact hs.sp
theorem ld_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : EntOK m pk w s) (hb : Bank s) :
    ∃ s1, Steps image s 2 2 s1 ∧ ProInit m pk w s1 ∧ Bank s1 := by
  obtain ⟨s1, h1⟩ := spec_run ldCheck s hs.pc (kSp_ok hs) (by simp [ldSpec]) (by simp)
  have hm : ∀ A, s1.getMem A = s.getMem A := fun A => h1.mem A
  have h18 : s1.getReg .x18 = 0xfff := by
    rw [h1.regs (.x18, .ld (cw VERIFY_DATA)) (by simp [ldSpec])]
    exact hb.2.2.2.1
  have h10 : s1.getReg .x10 = 23504 := by
    rw [h1.regs (.x10, .ld (cw (VERIFY_DATA + 8))) (by simp [ldSpec])]
    exact hb.2.2.2.2
  have hknown : KnownOK kPro s1 := by
    intro p hp
    simp only [kPro, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    split
    · rename_i heq
      simpa only [heq] using h18
    · split
      · rename_i _ heq
        simpa only [heq] using h10
      · rename_i hne1 hne2
        exact h1.known q (List.mem_filter.mpr ⟨hq, by simp only [decide_eq_true_eq]; exact ⟨hne1, hne2⟩⟩)
  refine ⟨s1, h1.steps, ⟨hknown, h1.pc rfl, fun k hk => (hm _).trans (hs.msg k hk),
    ⟨(hm _).trans hs.pk.1, (hm _).trans hs.pk.2⟩, fun j hj => (hm _).trans (hs.wit j hj),
    fun A hA hz => (hm _).trans (hs.zero A hA hz), hs.data.congr (fun A _ _ => hm _),
    h1.known (.x2, BitVec.ofNat 64 VERIFY_DATA) (by decide +kernel)⟩, hb.congr (fun A _ _ => hm _)⟩
def rejectPc : Nat := 33511
def rejSpec (steps : Nat) (brs : List Br) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], rejectPc, true, steps, brs, none, steps⟩
def proSpec : Spec :=
  ⟨[(.x11, cw 64)], [(⟨none, BitVec.ofNat 64 23520⟩, cw 0)], 32775, true, 2, [], none, 2⟩
def proPost : List (Reg × Word) :=
  (kPro.filter fun p => p.1 ≠ .x3 ∧ p.1 ≠ .x4 ∧ p.1 ≠ .x11) ++ [(.x11, 64)]
theorem proCheck : specB [23520] [] [] (runAt kPro [] 32773 []) proSpec [] proPost [] = true := by
  decide +kernel
structure DgPre (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (t : MachineState) : Prop where
  pc : t.pc = pcOf 32775
  known : KnownOK proPost t
  wit : Orig w (fun o => o ≠ 21472 ∧ o ≠ 21480) t
  zw : t.getMem (BitVec.ofNat 64 23520) = 0
  msg : ∀ k, k < 4 → t.getMem (BitVec.ofNat 64 (MSGADDR + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk t
  zero : ∀ A, A < WIT → (A < 0xA0 ∨ 0xB0 ≤ A) → t.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK t
  sp : t.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
  bank : Bank t
structure DgOut (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (a : HashOutput) (u : MachineState) :
    Prop where
  pc : u.pc = pcOf 32776
  known : KnownOK proPost u
  wit : Orig w (fun o => o ≠ 21472 ∧ o ≠ 21480) u
  digest : W9Drv.DigestAt a u
  pk : PkOK pk u
  zero : ∀ A, A < WIT → 32 ≤ A → (A < 0xA0 ∨ 0xB0 ≤ A) → u.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK u
  sp : u.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
  bank : Bank u
theorem digest_tail (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : ProInit m pk w s) (hb : Bank s) :
    ((ClaudeWCT.W9.T3M.wdc w).toNat ≥ ClaudeWCT.WCT9.digestVerifyWindow → ∃ u, Steps image s 6 6 u ∧
        fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow → ∃ t, Steps image s 2 2 t ∧
        fetch image t = some (.base .ECALL) ∧ hashArgumentsValid t = true ∧
        hashInput t = toQ (pad64 (digestInput (ClaudeWCT.W9.T3M.wrho w) m (ClaudeWCT.W9.T3M.wdc w))) ∧
        DgPre m pk w t) := by
  constructor
  · intro hge
    exact False.elim ((Nat.not_le.mpr (ClaudeWCT.W9.T3M.wdc w).isLt) hge)
  · intro hlt
    obtain ⟨t, ht⟩ := spec_run proCheck s hs.pc hs.known (by simp [proSpec]) (by simp)
    have hm : ∀ A, t.getMem A = memEval s proSpec.mem A := ht.mem
    have hkt : KnownOK proPost t := ht.known
    have h10 : t.getReg .x10 = BitVec.ofNat 64 23504 := hkt (.x10, 23504) (by decide +kernel)
    have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := hkt (.x11, 64) (by decide +kernel)
    have h12 : t.getReg .x12 = BitVec.ofNat 64 0 := hkt (.x12, 0) (by decide +kernel)
    have frame : ∀ A, A < 2 ^ 64 → A ≠ 23520 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1
      rw [hm]
      apply memEval_frame_ofNat s _ A hA
      intro p hp
      simp only [proSpec, List.mem_singleton] at hp
      subst hp
      exact ⟨rfl, by simpa using fun h => h1 (by omega)⟩
    have hz : t.getMem (BitVec.ofNat 64 23520) = 0 := by
      rw [hm]; simp [proSpec, memEval, Addr.eval, E.eval]
    refine ⟨t, ht.steps, ht.ecall rfl, ?_, ?_, ?_⟩
    · exact hashArgs_of t 23504 64 0 h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · have hl := digestInput_length (ClaudeWCT.W9.T3M.wrho w) m (ClaudeWCT.W9.T3M.wdc w)
      rw [pad64_digestInput]
      apply hashInput_words8 t _ 23504 hl h10 (by decide +kernel) (by decide +kernel) h11
      rw [digest_words]
      have e0 : t.getMem (BitVec.ofNat 64 23504) = dlo (ClaudeWCT.W9.T3M.wrho w) := by
        rw [frame _ (by omega) (by omega), show (23504 : Nat) = WIT + 8 * 2682 by unfold WIT; omega,
          hs.wit 2682 (by unfold WX; omega)]
        exact (wdig_lo w 2682).symm
      have e1 : t.getMem (BitVec.ofNat 64 (23504 + 8)) = dhi (ClaudeWCT.W9.T3M.wrho w) := by
        rw [frame _ (by omega) (by omega), show (23504 + 8 : Nat) = WIT + 8 * 2683 by unfold WIT; omega,
          hs.wit 2683 (by unfold WX; omega)]
        exact (wdig_hi w 2682).symm
      have e3 : t.getMem (BitVec.ofNat 64 (23504 + 24)) = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wdc w).toNat := by
        rw [frame _ (by omega) (by omega), show (23504 + 24 : Nat) = WIT + 8 * 2685 by unfold WIT; omega,
          hs.wit 2685 (by unfold WX; omega), wword_dc]
      have em : ∀ k, k < 4 → t.getMem (BitVec.ofNat 64 (23504 + 32 + 8 * k)) = m.extractLsb' (64 * k) 64 := by
        intro k hk
        rw [frame _ (by omega) (by omega), show 23504 + 32 + 8 * k = MSGADDR + 8 * k by unfold MSGADDR; omega,
          hs.msg k hk]
      rw [e0, e1, show 23504 + 16 = 23520 by rfl, hz, e3, show 23504 + 32 = 23504 + 32 + 8 * 0 by rfl,
        em 0 (by omega), show 23504 + 40 = 23504 + 32 + 8 * 1 by rfl, em 1 (by omega),
        show 23504 + 48 = 23504 + 32 + 8 * 2 by rfl, em 2 (by omega), show 23504 + 56 = 23504 + 32 + 8 * 3 by rfl,
        em 3 (by omega)]
    · refine ⟨ht.pc rfl, hkt, ?_, hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj hp
        rw [frame _ (by unfold WIT WX at *; omega) (by unfold WIT; omega)]
        exact hs.wit j hj
      · intro k hk
        rw [frame _ (by unfold MSGADDR; omega) (by unfold MSGADDR; omega)]
        exact hs.msg k hk
      · exact ⟨(frame 0xA0 (by omega) (by omega)).trans hs.pk.1, (frame 0xA8 (by omega) (by omega)).trans hs.pk.2⟩
      · intro A hA hz'
        unfold WIT at hA
        rw [frame A (by omega) (by omega)]
        exact hs.zero A (by unfold WIT; omega) hz'
      · apply hs.data.congr
        intro A hA hEnd
        exact frame A (by omega) (by unfold TAB at hA; omega)
      · exact hkt (.x2, BitVec.ofNat 64 VERIFY_DATA) (by decide +kernel)
      · exact hb.congr (fun A hA _ => frame A (by unfold VERIFY_DATA at *; omega)
          (by unfold VERIFY_DATA at hA; omega))
theorem digest_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) :
    ((ClaudeWCT.W9.T3M.wdc w).toNat ≥ ClaudeWCT.WCT9.digestVerifyWindow → ∃ u, Steps image s 9 9 u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    ((ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow → ∃ t, Steps image s 5 5 t ∧
      fetch image t = some (.base .ECALL) ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (pad64 (digestInput (ClaudeWCT.W9.T3M.wrho w) m (ClaudeWCT.W9.T3M.wdc w))) ∧
      DgPre m pk w t) := by
  obtain ⟨se, ste, hse, hbe⟩ := entry_step m pk w s hs hb
  obtain ⟨s0, st, hs0, hb0⟩ := ld_step m pk w se hse hbe
  obtain ⟨hr, ha⟩ := digest_tail m pk w s0 hs0 hb0
  constructor
  · intro h
    obtain ⟨u, stu, hf, h5, h10⟩ := hr h
    exact ⟨u, ste.trans (st.trans stu), hf, h5, h10⟩
  · intro h
    obtain ⟨t, stt, hf, hv, hin, hp⟩ := ha h
    exact ⟨t, ste.trans (st.trans stt), hf, hv, hin, hp⟩
theorem digest_out (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (t : MachineState)
    (ht : DgPre m pk w t) (a : HashOutput) : DgOut m pk w a (writeHash t a) := by
  have h12 : t.getReg .x12 = BitVec.ofNat 64 0 := ht.known (.x12, 0) (by decide +kernel)
  refine ⟨?_, ht.known.writeHash a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, ht.pc]; rfl
  · intro j hj hp
    rw [writeHash_frame t a 0 _ h12 (by unfold WIT WX at *; omega) (by omega) (Or.inr (by unfold WIT; omega))]
    exact ht.wit j hj hp
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact writeHash_at0 t a 0 h12 (by omega)
    · exact writeHash_at8 t a 0 h12 (by omega)
    · exact writeHash_at16 t a 0 h12 (by omega)
    · exact writeHash_at24 t a 0 h12 (by omega)
  · exact ⟨(writeHash_frame t a 0 0xA0 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.1,
      (writeHash_frame t a 0 0xA8 h12 (by omega) (by omega) (Or.inr (by omega))).trans ht.pk.2⟩
  · intro A hA h32 hz
    unfold WIT at hA
    rw [writeHash_frame t a 0 A h12 (by omega) (by omega) (Or.inr (by omega))]
    exact ht.zero A (by unfold WIT; omega) hz
  · apply ht.data.congr
    intro A hA hEnd
    exact writeHash_frame t a 0 A h12 (by omega) (by omega) (Or.inr (by unfold TAB at hA; omega))
  · rw [writeHash_getReg]; exact ht.sp
  · exact ht.bank.congr (fun A hA _ => writeHash_frame t a 0 A h12 (by unfold VERIFY_DATA at *; omega) (by omega)
      (Or.inr (by unfold VERIFY_DATA at hA; omega)))
theorem digestP_good (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) {P : Hash → Prop} {N C A : Nat} {Q : Prop} (hN : 1 ≤ N)
    (K : Option HashOutput → OracleComp HashSpec Obs) (hK : K none = pure (false, 0))
    (hcont : ∀ a u, (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow → DgOut m pk w a u →
      GoodQP (fun hash => hash (digestQ m w) = a ∧ P hash) u N C Q A (K (some a))) :
    GoodQP P s (N + 8) (C + 13) Q (A + 13) (ccM (ClaudeWCT.W9.T3M.digestP m w) K) := by
  obtain ⟨hrej, hacc⟩ := digest_step m pk w s hs hb
  unfold ClaudeWCT.W9.T3M.digestP
  by_cases hdc : (ClaudeWCT.W9.T3M.wdc w).toNat ≥ ClaudeWCT.WCT9.digestVerifyWindow
  · exact False.elim ((Nat.not_le.mpr (ClaudeWCT.W9.T3M.wdc w).isLt) hdc)
  · rw [if_neg hdc, ccM_map]
    obtain ⟨t, hst, hf, hv, hin, hpre⟩ := hacc (by omega)
    unfold SigGolfCandidate.T3.digest
    have h5 : t.getReg .x5 = 0 := hpre.known (.x5, 0) (by decide +kernel)
    have := GoodQP.publicHash_bind_pre (P := P) (f := pure) (K := fun a => K (some a)) hf h5 hv hin (fun a => by
      rw [ccM_pure]; exact hcont a _ (by omega) (digest_out m pk w t hpre a))
    rw [bind_pure, blocks_digestInput] at this
    exact GoodQP.steps' hst this (by omega) (by omega) (by omega)
def hookSpec : Spec := ⟨[(.x16, .ld (cw 0))], [], 32777, false, 1, [], none, 1⟩
def hookPost : List (Reg × Word) := proPost.filter fun p => p.1 ≠ .x16
theorem hookCheck : specB [] [] baseK (runAt proPost [32777] 32776 []) hookSpec [] hookPost [] = true := by
  decide +kernel
theorem gatePre_of_hook (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) (a : HashOutput)
    (u : MachineState) (hu : DgOut m pk w a u) :
    ∃ t, Steps image u 1 1 t ∧ W9Drv.GatePre pk w a t := by
  have h5 : u.getReg .x5 = 0 := hu.known (.x5, 0) (by decide +kernel)
  have h18 : u.getReg .x18 = 0xFFF := hu.known (.x18, 0xFFF) (by decide +kernel)
  have hglob : Glob baseK w pk u := by
    refine ⟨?_, fun j hj hj' => hu.wit j (by unfold WX; omega) (by omega), hu.pk, ?_, ?_, hu.data⟩
    · intro p hp
      simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact h5
      · exact h18
    · intro A hA
      simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl <;> exact hu.zero _ (by unfold WIT; omega) (by omega) (by omega)
    · show (u.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hu.zero CTRW (by unfold CTRW WIT; omega) (by unfold CTRW; omega) (by unfold CTRW; omega)]
      rfl
  obtain ⟨t, ht⟩ := spec_run hookCheck u hu.pc hu.known (by simp [hookSpec]) (by simp)
  have e : ∀ A, t.getMem A = u.getMem A := fun A => ht.mem A
  have h16 : t.getReg .x16 = a.extractLsb' 0 64 := by
    rw [ht.regs (.x16, .ld (cw 0)) (by simp [hookSpec])]
    show u.getMem (BitVec.ofNat 64 0) = _
    simpa using hu.digest 0 (by decide +kernel)
  refine ⟨t, ht.steps, ⟨ht.pc rfl, ht.glob baseK w pk hglob (RelOK.nil u), h16,
    ht.known (.x11, 64) (by decide +kernel),
    ⟨(e _).trans hu.bank.1.zero0, (e _).trans hu.bank.1.zero1, (e _).trans hu.bank.1.header⟩,
    fun k hk => (e _).trans (hu.digest k hk),
    ⟨fun k hk => (e _).trans (hu.bank.2.1.top k hk), (e _).trans hu.bank.2.1.top8⟩,
    fun j hj hp => (e _).trans (hu.wit j hj hp),
    ⟨(e _).trans hu.bank.2.2.1.child, (e _).trans hu.bank.2.2.1.jt, (e _).trans hu.bank.2.2.1.coord⟩,
    ht.known (.x2, BitVec.ofNat 64 VERIFY_DATA) (by decide +kernel)⟩⟩
theorem prefixGood : PrefixGood W9Drv.GatePre := by
  intro m pk w s hs P N C A Q K hK hcont
  have h := digestP_good m pk w s (init_ok m pk w s hs) (init_bank m pk w s hs) (P := P) (N := N + 1)
    (C := C + 1) (A := A + 1) (Q := Q) (by omega) K hK (fun a u hdc hu => by
      obtain ⟨t, hst, hpre⟩ := gatePre_of_hook m pk w a u hu
      exact GoodQP.steps' hst (hcont a t hdc hpre) le_rfl le_rfl le_rfl)
  exact GoodQP.mono' h (by omega) (by omega) (by omega)
end W9Fin.V7
#print axioms W9Fin.V7.prefixGood
end

section



namespace W9Fin.V7
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
theorem digestP_eval (hash : Hash) (m : SigGolfCandidate.T3.Message) (w : WB)
    (hdc : (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow) :
    evalWithAnswerFn hash (mrealize 0 (ClaudeWCT.W9.T3M.digestP m w)) = some (hash (digestQ m w)) := by
  unfold ClaudeWCT.W9.T3M.digestP
  rw [if_neg (by omega), mrealize_map]
  unfold SigGolfCandidate.T3.digest
  rw [mrealize_publicHash, evalWithAnswerFn_map, eval_liftQ]
  rfl
theorem capOk_of_pre {hash : Hash} {m : SigGolfCandidate.Legacy.Message} {w : Bytes 21484} {a : HashOutput}
    (hdc : (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow) (hq : hash (digestQ m w) = a)
    (hcap : ClaudeWCT.W9.T3M.Final.DigestCapOk hash m w) : ClaudeWCT.WCT9.capOk a = true :=
  hcap a ((digestP_eval hash m w hdc).trans (congrArg some hq))
theorem jointCost_le_of_capOk {a : HashOutput} (h : ClaudeWCT.WCT9.capOk a = true) :
    ClaudeWCT.WCT9.jointCost a ≤ 710 := by
  unfold ClaudeWCT.WCT9.capOk ClaudeWCT.WCT9.jointCap at h
  exact of_decide_eq_true h
structure Inputs (GatePre : Digest → WB → HashOutput → MachineState → Prop)
    (FtsOut : Digest → WB → HashOutput → Digest → MachineState → Prop) (ovh aG : Nat) : Prop where
  prefixGood : PrefixGood GatePre
  fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh)
  after : AfterGoodBudget FtsOut aG
  hnum : 14 + aG + ovh + 710 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound
section
variable {GatePre : Digest → WB → HashOutput → MachineState → Prop}
  {FtsOut : Digest → WB → HashOutput → Digest → MachineState → Prop} {ovh aG : Nat}
def afterDigest (pk : Digest) (w : WB) (N : HashOutput) : SigGolfCandidate.T3.M Bool :=
  (if ClaudeWCT.W9.T3M.gateOk N then ClaudeWCT.W9.T3M.wctP w N else pure none) >>=
    afterFts pk w (ClaudeWCT.WCT9.digestIndex N)
theorem verifyP_eq (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WB) :
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
abbrev Pre (m : SigGolfCandidate.Legacy.Message) (w : Bytes 21484) (hash : Hash) : Prop :=
  HashOk hash ∧ ClaudeWCT.W9.T3M.Final.DigestCapOk hash m w
theorem afterDigest_good (fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh))
    (after : AfterGoodBudget FtsOut aG)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 21484) (a : HashOutput) (u : MachineState)
    (hdc : (ClaudeWCT.W9.T3M.wdc w).toNat < ClaudeWCT.WCT9.digestVerifyWindow) (hu : GatePre pk w a u) :
    GoodQP (fun hash => hash (digestQ m w) = a ∧ Pre m w hash) u (8050 + 2023) (8050 + 2023) True
      (aG + (ovh + 710)) (ccM (afterDigest pk w a) Kb) := by
  have h := fts pk w a u 8050 8050 aG True (fun r => ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) r) Kb) hu
    (by simp only [afterFts, ccM_pure, Kb])
    (fun root t ht => after pk w True trivial a root t ht)
  have e : ccM (afterDigest pk w a) Kb =
      ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none)
        (fun r => ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) r) Kb) := by
    unfold afterDigest
    rw [ccM_bind]
  rw [e]
  by_cases hcap : ClaudeWCT.WCT9.capOk a = true
  · have hj := jointCost_le_of_capOk hcap
    have h' : GoodQ u (8050 + 2023) (8050 + 2023) True (aG + (ovh + 710))
        (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none)
          (fun r => ccM (afterFts pk w (ClaudeWCT.WCT9.digestIndex a) r) Kb)) :=
      h.mono (le_refl _) (le_refl _) (fun hq => ⟨hq, by simp only [ftsAcceptCost]; omega⟩)
    exact (GoodQ.toP h').pre_mono (fun hash hp => hp.2.1)
  · exact GoodQP.of_false h (fun hash hp => hcap (capOk_of_pre hdc hp.1 hp.2.2))
def fuelBound : Nat := 10 + (8050 + 2023)
def cycleBoundAll : Nat := 14 + (8050 + 2023)
theorem fuelBound_eq : fuelBound = 10083 := rfl
theorem cycleBoundAll_eq : cycleBoundAll = 10087 := rfl
theorem fuelBound_le : fuelBound ≤ CYCLE_LIMIT := by rw [fuelBound_eq]; unfold CYCLE_LIMIT; norm_num
theorem verify_good (prefixGood : PrefixGood GatePre)
    (fts : FtsGoodByCost GatePre FtsOut (ftsAcceptCost ovh))
    (after : AfterGoodBudget FtsOut aG)
    (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 21484) (s : MachineState)
    (hs : initialState submission .verify (m, pk, w) = some s) :
    GoodQP (Pre m w) s fuelBound cycleBoundAll True (aG + (ovh + 710) + 14)
      (ccM (ClaudeWCT.W9.T3M.verifyP m pk w) Kb) := by
  rw [verifyP_eq, ccM_bind]
  exact prefixGood m pk w s hs (Pre m w) (8050 + 2023) (8050 + 2023) (aG + (ovh + 710)) True
    (fun o => ccM (match o with
      | some N => afterDigest pk w N
      | none => pure false) Kb) (by simp only [ccM_pure, Kb])
    (fun a u hdc hu => afterDigest_good fts after m pk w a u hdc hu)
set_option maxRecDepth 100000 in
theorem init_mk (sI eI : Riscv.Image) (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 21484) :
    initialState (ClaudeWCT.W9.T3M.submission ⟨sI, eI, Images.verifyImage⟩) .verify (m, pk, w) =
      initialState submission .verify (m, pk, w) :=
  rfl
theorem mk_verify (sI eI : Riscv.Image) :
    (⟨sI, eI, Images.verifyImage⟩ : ClaudeWCT.W9.T3M.Images).verify = Images.verifyImage := rfl
theorem init_exists (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 21484) :
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
  have h2 : aG + (ovh + 710) + 14 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound := by have := H.hnum; omega
  exact le_trans h1 h2
theorem verify_inputs_of (I : ClaudeWCT.W9.T3M.Images) (hI : I.verify = Images.verifyImage)
    (H : Inputs GatePre FtsOut ovh aG) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I :=
  ⟨verify_refines_of I hI H, verify_terminates_of I hI H, verify_accept_cycles_of I hI H⟩
end
def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
theorem I0_verify : I0.verify = Images.verifyImage := rfl
theorem verify_inputs {GatePre : Digest → WB → HashOutput → MachineState → Prop}
    {FtsOut : Digest → WB → HashOutput → Digest → MachineState → Prop} {ovh aG : Nat}
    (H : Inputs GatePre FtsOut ovh aG) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs_of I0 I0_verify H
end W9Fin.V7
#print axioms W9Fin.V7.verify_inputs_of
#print axioms W9Fin.V7.verify_inputs
end

section


namespace W9Fin.V7
theorem verify_inputs_x {FtsOut : SigGolfCandidate.T3.Digest → ClaudeWCT.W9.T3M.WBytes →
      SigGolfCandidate.T3.HashOutput → SigGolfCandidate.T3.Digest → RiscvZkvm.Rv64.MachineState → Prop}
    {ovh aG : Nat}
    (fts : FtsGoodByCost W9Drv.GatePre FtsOut (ftsAcceptCost ovh))
    (after : AfterGoodBudget FtsOut aG)
    (hnum : 14 + aG + ovh + 710 ≤ ClaudeWCT.W9.T3M.Final.verifyCycleBound) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs ⟨prefixGood, fts, after, hnum⟩
end W9Fin.V7
#print axioms W9Fin.V7.verify_inputs_x
end
