/- Actual unchanged-prefix execution on the independently selected inline
   native image. Attributed source: original W9Fin.V4.Final second section.
   All four guards read prefixRunAt; original pure initialization proof bodies are
   reused only after equality of initialized states, never image equality. -/
import SigGolfCandidate.T3M.InlineSubmission
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineBudgetJudg
import SigGolfCandidate.T3M.Verify.Init
import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP
import SigGolfCandidate.T3M.Verify.Nonbinary.InlinePrefixSpec

namespace W9Fin.V4.Inline.Prefix
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput pad64 digestInput)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
set_option maxErrors 5
set_option linter.unusedSimpArgs false
def digestQ (m : SigGolfCandidate.T3.Message) (w : WBytes) : Query :=
  toQ (pad64 (digestInput (wrho w) m (wdc w)))
abbrev image := Images.InlineNative.image
abbrev GoodQ := SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQ image
abbrev GoodQP := SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP image

structure NativePrefixSpecRes (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word)) (sp : Spec)
    (post : List (Reg × Word)) (keep : List Reg) (s t : MachineState) : Prop where
  steps : Steps image s sp.steps sp.cycles t
  ecall : sp.ecall = true → fetch image t = some (.base .ECALL)
  glob : ∀ gk0 w pk, Glob gk0 w pk s → RelOK rel s → Glob gk w pk t
  known : KnownOK post t
  keep : ∀ x ∈ keep, t.getReg x = s.getReg x
  regs : ∀ p ∈ sp.regs, t.getReg p.1 = p.2.eval s
  mem : ∀ A, t.getMem A = memEval s sp.mem A
  memc : memOKA allow rel sp.mem = true
  pc : sp.spc = none → t.pc = pcOf sp.pc
  spc : ∀ e, sp.spc = some e → t.pc = e.eval s

theorem spec_run {allow : List Nat} {rel : List Reg} {gk known post : List (Reg × Word)} {stops : List Nat}
    {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : specB allow rel gk (SigGolfCandidate.T3M.Nonbinary.InlineTail.prefixRunAt known stops n dirs)
      sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, NativePrefixSpecRes allow rel gk sp post keep s t := by
  obtain ⟨t, ht⟩ := SigGolfCandidate.T3M.Nonbinary.InlineTail.prefix_spec_run h s hpc hk hbr hob
  refine ⟨t, ⟨SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.steps ht.steps,
    ?_, ht.glob, ht.known, ht.keep, ht.regs, ht.mem, ht.memc, ht.pc, ht.spc⟩⟩
  intro he
  rw [← SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.fetch]
  exact ht.ecall he

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
  have h := SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQ.reject (Q := Q) (A := A) hf h5 h10
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
  have := SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP.query_pre (K := fun a => ccM (f a) K) hf ht0 hv hin h
  rw [cc_query] at this
  rwa [ccM_publicHash_bind]
def Bank (u : MachineState) : Prop :=
  W9Drv.HeaderBank u ∧ W9Drv.SetupMask u ∧ u.getMem (BitVec.ofNat 64 W9Drv.setupMaskAddr) = BitVec.ofNat 64 0xfff
theorem Bank.congr {s t : MachineState} (h : Bank s)
    (hm : ∀ A, VERIFY_DATA ≤ A → A < VERIFY_DATA + 336 →
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
  · rw [hm _ (by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega) (by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega)]
    exact h.2.2
private theorem original_init_word (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) (j : Nat) (hj : j < 2104) :
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
      if VERIFY_DATA ≤ A ∧ A < VERIFY_DATA + 8 * ((16832 + 7) / 8) ∧ (A - VERIFY_DATA) % 8 = 0 then
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
private theorem original_init_bank (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : Bank s := by
  refine ⟨⟨?_, fun k hk => ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [show 0xffbf40 + 8 = VERIFY_DATA + 8 * 33 by unfold VERIFY_DATA; omega, original_init_word m pk w s h 33 (by omega)]
    decide +kernel
  · rw [show TOPLOAD + 8 * k = VERIFY_DATA + 8 * (37 + k) by unfold TOPLOAD VERIFY_DATA; omega,
      original_init_word m pk w s h (37 + k) (by omega)]
    interval_cases k <;> decide +kernel
  · rw [show TOPLOAD - 8 = VERIFY_DATA + 8 * 36 by unfold TOPLOAD VERIFY_DATA; omega,
      original_init_word m pk w s h 36 (by omega)]
    decide +kernel
  · rw [show W9Drv.setupMaskAddr + 16 = VERIFY_DATA + 8 * 34 by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega,
      original_init_word m pk w s h 34 (by omega)]
    decide +kernel
  · rw [show W9Drv.setupMaskAddr + 24 = VERIFY_DATA + 8 * 35 by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega,
      original_init_word m pk w s h 35 (by omega)]
    decide +kernel
  · rw [show W9Drv.setupMaskAddr = VERIFY_DATA + 8 * 32 by unfold W9Drv.setupMaskAddr VERIFY_DATA; omega, original_init_word m pk w s h 32 (by omega)]
    decide +kernel

theorem initialState_eq (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) :
    initialState Native.submission .verify (m, pk, w) =
      initialState SigGolfCandidate.T3M.submission .verify (m, pk, w) := by
  unfold initialState
  simp only [Native.submission_admissible.2 .verify,
    SigGolfCandidate.T3M.submission_admissible.2 .verify, if_true]
  simp only [Native.submission_sizes, Native.submission_layout, Native.submission_verify,
    SigGolfCandidate.T3M.submission_verify, Riscv.dataBase,
    SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.data_eq_original]

theorem init_ok (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (h : initialState Native.submission .verify (m, pk, w) = some s) : InitOK m pk w s :=
  SigGolfCandidate.T3M.Verify.init_ok m pk w s ((initialState_eq m pk w).symm.trans h)

/- These three adapters use only the copied pure initial-state memory facts
   of the original Final module. No old-image execution judgment is transported. -/
theorem init_word (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (h : initialState Native.submission .verify (m, pk, w) = some s) (j : Nat) (hj : j < 2104) :
    s.getMem (BitVec.ofNat 64 (VERIFY_DATA + 8 * j)) =
      bytesToWordLE (((Native.submission.image .verify).data.drop (8 * j)).take 8) := by
  rw [Native.submission_verify, SigGolfCandidate.T3M.Nonbinary.InlineNativeBinding.data_eq_original]
  exact original_init_word m pk w s ((initialState_eq m pk w).symm.trans h) j hj

theorem init_bank (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState)
    (h : initialState Native.submission .verify (m, pk, w) = some s) : Bank s :=
  original_init_bank m pk w s ((initialState_eq m pk w).symm.trans h)

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
theorem proCheck : specB [] [] baseK (SigGolfCandidate.T3M.Nonbinary.InlineTail.prefixRunAt kMask0 [] 1 [.br false]) proSpec [] proPost [.x2] = true := by
  decide +kernel
theorem proRejCheck : specB [] [] [] (SigGolfCandidate.T3M.Nonbinary.InlineTail.prefixRunAt kMask0 [] 1 [.br true]) (rejSpec 6 [proBr true]) [] [] [] = true := by
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
def maskObl : Oblig := .valid ⟨some (.reg .x2), 256⟩ 8
def maskSpec : Spec := ⟨[(.x18, .ld (addC (.reg .x2) 256))], [], 1, false, 1, [], none, 1⟩
def k0m : List (Reg × Word) := k0.filter fun p => p.1 ≠ .x18
theorem maskCheck : specB [] [] [] (SigGolfCandidate.T3M.Nonbinary.InlineTail.prefixRunAt k0 [1] 0 []) maskSpec [maskObl] k0m [.x2] = true := by
  decide +kernel
theorem mask_step (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : WBytes) (s : MachineState)
    (hs : InitOK m pk w s) (hb : Bank s) :
    ∃ s1, Steps image s 1 1 s1 ∧ ProInit m pk w s1 ∧ Bank s1 := by
  obtain ⟨s1, h1⟩ := spec_run maskCheck s hs.pc hs.known (by simp [maskSpec]) (by
    intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    show accessValid (s.getReg .x2 + 256) 8 = true
    rw [hs.sp]
    decide +kernel)
  have hm : ∀ A, s1.getMem A = s.getMem A := fun A => h1.mem A
  have h18 : s1.getReg .x18 = 0xfff := by
    rw [h1.regs (.x18, .ld (addC (.reg .x2) 256)) (by simp [maskSpec])]
    show s.getMem (s.getReg .x2 + 256) = _
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
    exact SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP.steps' hst (GoodQP.reject (P := P) (Q := Q) (A := 0) hf h5 h10) (by omega) (by omega)
      (by omega)
  · rw [if_neg hdc, ccM_map]
    obtain ⟨t, hst, hf, hv, hin, hpre⟩ := hacc (by omega)
    unfold SigGolfCandidate.T3.digest
    have h5 : t.getReg .x5 = 0 := hpre.known (.x5, 0) (by simp [proPost, baseK])
    have := GoodQP.publicHash_bind_pre (P := P) (f := pure) (K := fun a => K (some a)) hf h5 hv hin (fun a => by
      rw [ccM_pure]; exact hcont a _ (by omega) (digest_out m pk w t hpre a))
    rw [bind_pure, blocks_digestInput] at this
    exact SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP.steps' hst this (by omega) (by omega) (by omega)
def hookSpec : Spec := ⟨[(.x16, .ld (cw 0x60))], [], 16, false, 1, [], none, 1⟩
theorem hookCheck : specB [] [] baseK (SigGolfCandidate.T3M.Nonbinary.InlineTail.prefixRunAt proPost [16] 15 []) hookSpec [] proPost [.x2] = true := by
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
theorem prefixGood :
    ∀ (m : SigGolfCandidate.Legacy.Message) (pk : PublicKey) (w : Bytes 22984) (s : MachineState),
      initialState Native.submission .verify (m, pk, w) = some s →
      ∀ (P : Hash → Prop) (N C A : Nat) (Q : Prop) (K : Option HashOutput → OracleComp HashSpec Obs),
        K none = pure (false, 0) →
        (∀ a u, (wdc w).toNat < ClaudeWCT.WCT9.digestAttemptLimit → W9Drv.GatePre pk w a u →
          GoodQP (fun hash => hash (digestQ m w) = a ∧ P hash) u N C Q A (K (some a))) →
        GoodQP P s (N + 16) (C + 23) Q (A + 23) (ccM (ClaudeWCT.W9.T3M.digestP m w) K) := by
  intro m pk w s hs P N C A Q K hK hcont
  have h := digestP_good m pk w s (init_ok m pk w s hs) (init_bank m pk w s hs) (P := P) (N := N + 1)
    (C := C + 1) (A := A + 1) (Q := Q) K hK (fun a u hdc hu => by
      obtain ⟨t, hst, hpre⟩ := gatePre_of_hook m pk w a u hu
      exact SigGolfCandidate.T3M.Nonbinary.InlineBudget.Judg.GoodQP.steps' hst (hcont a t hdc hpre) le_rfl le_rfl le_rfl)
  exact GoodQP.mono' h (by omega) (by omega) (by omega)

#print axioms prefixGood
end W9Fin.V4.Inline.Prefix
