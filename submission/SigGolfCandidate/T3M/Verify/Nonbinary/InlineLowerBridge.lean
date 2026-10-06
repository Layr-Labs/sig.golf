import SigGolfCandidate.T3M.Verify.Nonbinary.InlinePrefixSpec
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineNativeBinding
import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.T3M.Verify.ChainGood

/- Actual instruction bridge for the unchanged lower BC and WCT600 code.
   The lookup excludes every changed inline-tail word. In particular, this
   module does not transport an old completed GoodQ judgment. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail.Lower
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.T3 (Digest)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- After row754 the row factory is literally the original one, including
-- the short final row. No 256-word assumption is made about that final row.
theorem mapRows_after (rows : List (List (BitVec 32))) (start : Nat)
    (hstart : 755 ≤ start) : mapRows start rows = rows := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    simp only [mapRows, if_neg (by omega : ¬ (691 ≤ start ∧ start < 755))]
    rw [ih (start + 1) (by omega)]

theorem suffix_code_equal : code.drop 193280 = Images.verifyCode.drop 193280 := by
  have hn : 755 < chunks.length := by rw [chunks_length]; decide
  have ho : 755 < lChunks.length := by rw [lChunks_length]; decide
  change chunks.flatten.drop (256 * 755) = Images.verifyCode.drop (256 * 755)
  rw [drop_chunks' chunks 755 chunkLengthsOK hn, lChunks_flatten,
    drop_chunks' lChunks 755 lChunks_ok ho]
  rw [chunks, mapRows_drop]
  simp only [Nat.zero_add]
  rw [mapRows_after _ 755 (by decide)]

theorem suffix_drop_equal (p : Nat) (hp : 193280 ≤ p) :
    code.drop p = Images.verifyCode.drop p := by
  have h : p = 193280 + (p - 193280) := by omega
  rw [h, ← List.drop_drop, ← List.drop_drop, suffix_code_equal]

-- The exclusion is a physical lookup restriction, not a source acceptance
-- or stage-result premise. Ordinary lower code lies below176896; WCT600
-- routines/JT and the actual appended final leaves lie above193280.
def safePC (n : Nat) : Prop := n < 176896 ∨ 193280 ≤ n
instance (n : Nat) : Decidable (safePC n) := inferInstanceAs (Decidable (n < 176896 ∨ 193280 ≤ n))
def look (n : Nat) : Option (BitVec 32) := if safePC n then vlook n else none

theorem safe_word_equal (n : Nat) (hn : safePC n) : code[n]? = Images.verifyCode[n]? := by
  have hd : ((code.drop n).take 1)[0]? = ((Images.verifyCode.drop n).take 1)[0]? := by
    rcases hn with hn | hn
    · exact congrArg (fun ws : List (BitVec 32) => ws[0]?) (prefix_window_equal n 1 (by omega))
    · exact congrArg (fun ws : List (BitVec 32) => (ws.take 1)[0]?) (suffix_drop_equal n hn)
  simpa only [List.getElem?_take, List.getElem?_drop, Nat.add_zero,
    show (0 < 1 : Prop) from by decide, if_true] using hd

theorem look_ok : LookOK InlineTail.image look := by
  intro n w hw
  unfold look at hw
  split at hw
  · rename_i hn
    exact (safe_word_equal n hn).trans (vlook_ok n w hw)
  · cases hw

theorem look_eq (n : Nat) (hn : safePC n) : look n = vlook n := by
  simp only [look, if_pos hn]

theorem prefix_codeAt_transfer (p : Nat) (ws : List (BitVec 32))
    (hold : CodeAt Images.verifyImage (pcOf p) ws) (hb : p + ws.length ≤ 176896) :
    CodeAt InlineTail.image (pcOf p) ws := by
  have hp : (pcOf p).toNat = 0x1000 + 4*p := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  refine ⟨hold.1, hold.2.1, hold.2.2.1, ?_⟩
  have ho := hold.2.2.2
  rw [hp, show (0x1000+4*p-0x1000)/4=p by omega] at ho ⊢
  change ws <+: code.drop p
  have he := prefix_window_equal p ws.length hb
  obtain ⟨tail, ht⟩ := ho
  have hw : (Images.verifyCode.drop p).take ws.length = ws := by
    rw [← ht, List.take_left]
  rw [← hw, ← he]
  exact List.take_prefix _ _

theorem suffix_codeAt (p n : Nat) (hp : 193280 ≤ p) (hmax : p + n ≤ 251927) :
    CodeAt InlineTail.image (pcOf p) ((lcode p).take n) := by
  have hpc : (pcOf p).toNat = 0x1000 + 4 * p := by
    simp only [pcOf, BitVec.toNat_ofNat]; omega
  have hl : ((lcode p).take n).length ≤ n := List.length_take_le ..
  refine ⟨by rw [hpc]; omega, by rw [hpc]; omega, by rw [hpc]; omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * p - 0x1000) / 4 = p by omega]
  change (lcode p).take n <+: code.drop p
  rw [lcode_eq p (by omega), suffix_drop_equal p hp]
  exact List.take_prefix _ _

-- Actual lower43 geometry is narrower than the historical209920 bound.
-- The 512-way lower JT ends before the first changed row691; ordinary
-- lower chain bodies and the checksum routine are below82200.
theorem lower_start_bound (c : LCtx) (i : Nat) (hi : i ≤ 42) (hck : c.ck ≤ 8) :
    c.startPc i + 8 ≤ 176896 := by
  unfold LCtx.startPc
  split_ifs with h42 h0 h1
  · unfold ctabIdx; omega
  · have hk := c.kOf_lt (i / 3) (by omega)
    unfold entW ttabIdx
    omega
  · have hb := LCtx.triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
    unfold LCtx.tB pcB
    omega
  · have hb := LCtx.triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
    have hl := partLen_le (c.dig (3 * (i / 3) + 1))
    unfold LCtx.tC pcC pcB
    omega

theorem lower_rung_bound (c : LCtx) (i m : Nat) (hm : m ≤ 6) :
    c.rungPc i m + landOff m + 8 ≤ 176896 := by
  have hb := LCtx.triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
  have hl := partLen_le (c.dig (3 * (i / 3) + 1))
  unfold LCtx.rungPc LCtx.tb LCtx.tB LCtx.tC pcC pcB landOff
  split_ifs <;> (try unfold ckR0) <;> omega

theorem lower_end_bound (c : LCtx) (i : Nat) : c.endPc i + 5 ≤ 176896 := by
  have hb := LCtx.triBase_lt (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
  have hl := partLen_le (c.dig (3 * (i / 3) + 1))
  have hx := c.tX_lt i
  unfold LCtx.endPc LCtx.tB LCtx.tC pcC pcB
  split_ifs <;> (try unfold ckDone) <;> omega

theorem lower_start_codeAt (c : LCtx) (i f : Nat) (hi : i ≤ 42) (hck : c.ck ≤ 8) (hf : f ≤ 8) :
    CodeAt InlineTail.image (pcOf (c.startPc i)) ((lcode (c.startPc i)).take f) :=
  prefix_codeAt _ _ (by have h := lower_start_bound c i hi hck; omega)

theorem lower_rung_codeAt (c : LCtx) (i m f : Nat) (hm : m ≤ 6) (hf : f ≤ 8) :
    CodeAt InlineTail.image (pcOf (c.rungPc i m)) ((lcode (c.rungPc i m)).take f) :=
  prefix_codeAt _ _ (by have h := lower_rung_bound c i m hm; unfold landOff at h; split_ifs at h <;> omega)

theorem lower_end_codeAt (c : LCtx) (i f : Nat) (hf : f ≤ 5) :
    CodeAt InlineTail.image (pcOf (c.endPc i)) ((lcode (c.endPc i)).take f) :=
  prefix_codeAt _ _ (by have h := lower_end_bound c i; omega)

def runAt (known : List (Reg × Word)) (stops : List Nat)
    (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 look (stops.map pcOf) 2000 (pcOf n) dirs (σK known) []

theorem path_sound {known : List (Reg × Word)} {stops : List Nat}
    {n : Nat} {dirs : List Dir} {r : PRes}
    (hr : runAt known stops n dirs = some r)
    (s : MachineState) (hp : s.pc = pcOf n) (hk : KnownOK known s)
    (ho : ∀ o ∈ r.st.obl, o.holds s) (hb : ∀ b ∈ r.brs, b.holds s) :
    Steps InlineTail.image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch InlineTail.image (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound hr look_ok s hp hk ho hb

-- Reuse the attributed pure postconditions of Verify.SpecRes while deriving
-- the new physical execution separately from the same symbolic result.
-- Both run equalities are actual symbolic execution checks. Neither is a
-- chosen HASH answer, accepted source event, or completed layer outcome.
theorem paired_run {known : List (Reg × Word)} {stops : List Nat}
    {n : Nat} {dirs : List Dir} {r : PRes}
    (hold : Verify.runAt known stops n dirs = some r)
    (hnew : runAt known stops n dirs = some r)
    (s : MachineState) (hp : s.pc = pcOf n) (hk : KnownOK known s)
    (ho : ∀ o ∈ r.st.obl, o.holds s) (hb : ∀ b ∈ r.brs, b.holds s) :
    (Steps Images.verifyImage s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch Images.verifyImage (r.toState s) = some (.base .ECALL))) ∧
    (Steps InlineTail.image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch InlineTail.image (r.toState s) = some (.base .ECALL))) := by
  exact ⟨pathRun_sound hold vlook_ok s hp hk ho hb, path_sound hnew s hp hk ho hb⟩

-- The pure memory/register postcondition has the attributed old type so
-- that setup_post, pair_setup_hash and the BC/LCtx invariant lemmas can be
-- used without copying their algebra. Its physical steps are also proved
-- on the new image, at exactly the same final MachineState.
structure DualSpecRes (allow : List Nat) (rel : List Reg) (gk : List (Reg × Word))
    (sp : Spec) (post : List (Reg × Word)) (keep : List Reg)
    (s t : MachineState) : Prop extends PrefixSpecRes allow rel gk sp post keep s t where
  oldSteps : Steps Images.verifyImage s sp.steps sp.cycles t
  oldEcall : sp.ecall = true → fetch Images.verifyImage t = some (.base .ECALL)

def DualSpecRes.toOld {allow : List Nat} {rel : List Reg} {gk : List (Reg × Word)}
    {sp : Spec} {post : List (Reg × Word)} {keep : List Reg} {s t : MachineState}
    (h : DualSpecRes allow rel gk sp post keep s t) :
    Verify.SpecRes allow rel gk sp post keep s t :=
  ⟨h.oldSteps, h.oldEcall, h.glob, h.known, h.keep, h.regs, h.mem, h.memc, h.pc, h.spc⟩

theorem dual_spec_run {allow : List Nat} {rel : List Reg}
    {gk known post : List (Reg × Word)} {stops : List Nat}
    {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : specB allow rel gk (runAt known stops n dirs) sp obl post keep = true)
    (heq : Verify.runAt known stops n dirs = runAt known stops n dirs)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, DualSpecRes allow rel gk sp post keep s t := by
  unfold specB at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hregs, hmem⟩, hpc'⟩, hec⟩, hst⟩, hcy⟩, hbrs⟩, hspc⟩, hobl⟩, hmok⟩, hrok⟩, hkn⟩,
    hkeep⟩ := h
  have hbrs' := listBeq_eq (fun _ _ => Br.beq_eq) hbrs
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  have hspc' := optEBeq_eq hspc
  have hobl' := listBeq_eq (fun _ _ => Oblig.beq_eq) hobl
  have hold : Verify.runAt known stops n dirs = some r := heq.trans hr
  obtain ⟨⟨host, hoec⟩, hnst, hnec⟩ := paired_run hold hr s hpc hk
    (by rw [hobl']; exact hob) (by rw [hbrs']; exact hbr)
  refine ⟨r.toState s, ⟨⟨?_, ?_, ?_, knownB_ok hkn s, keepB_ok hkeep s,
    ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [hcy, hst] at hnst; exact hnst
  · intro he; exact hnec (hec.trans he)
  · intro gk0 w pk hG hrel
    exact Glob_toState_allow hG r.st _ hmok hrel hrok
  · intro p hp
    rw [PRes.toState_getReg, E.beq_eq (List.all_eq_true.mp hregs p hp)]
  · intro A; rw [PRes.toState_getMem, hmem']
  · rw [← hmem']; exact hmok
  · intro hn
    rw [hn] at hpc'
    simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at hpc'
    rw [PRes.toState_pc _ _ (hspc'.trans hn), BitVec.eq_of_toNat_eq hpc']
  · intro e he; simp [PRes.toState, PRes.finalPc, hspc'.trans he]
  · rw [hcy, hst] at host; exact host
  · intro he; exact hoec (hec.trans he)

theorem window_steps {p fuel : Nat} {r : Result}
    (hr : vrun p fuel = some r) (hb : p + fuel ≤ 176896)
    (s : MachineState) (hp : s.pc = pcOf p) (ho : ∀ o ∈ r.st.obl, o.holds s) :
    Steps InlineTail.image s r.steps r.cycles (r.toState s) :=
  prefix_piece_steps hr hb s hp ((Oblig.all_iff s _).mpr ho)

-- Genuine lower-chain rung: original pure register/memory algebra, with
-- both Steps and the HASH fetch rebound through the real prefix CodeAt.
theorem rung_piece (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i ≤ 42) (hm : m ≤ 6) (hp : p + 3 ≤ 176896)
    (hrun : vrun p 3 = some (rungR m (if m = 6 then some (slotL i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps InlineTail.image s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ fetch InlineTail.image t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = 6 → t.getReg .x12 = BitVec.ofNat 64 (slotL i)) ∧ (m < 6 → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 256 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = 6 then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  set r := rungR m (if m = 6 then some (slotL i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 17⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (17 : Word) = BitVec.ofNat 64 17 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := prefix_piece_steps hrun hp s hpc ((Oblig.all_iff s _).mpr hobl)
  have hec := prefix_piece_ecall hrun hp s ((Oblig.all_iff s _).mpr hobl) (by simp [hr, rungR])
  have hn : r.steps = (if m = 6 then 2 else 1) ∧ r.cycles = (if m = 6 then 2 else 1) := by
    simp only [hr, rungR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = 6 then some (slotL i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 1 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h6 => ?_, fun h6 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_pos h6]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ 6 by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have := c.lay.isLt
    have hkoff := hc.2.2.1
    rw [stepByte _ _ _ _ (by omega) (by omega) (packedHi_lt _ _ _) hl hj]
    congr 1; unfold w0 packedPrefix; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h6 : m = 6 <;> simp [h6, E.eval]

-- Accepting cost may depend on the actual answer to this same query.
-- This is the conditional HashOk transport required by the top-credit law.
-- No fresh answer or chosen output is substituted into the execution.
theorem hash_accept {s : MachineState} {N C A : Nat} {Q : Prop} {q : Query}
    {K : BitVec 256 → OracleComp HashSpec Verify.Obs} (budget : BitVec 256 → Nat)
    (hf : fetch InlineTail.image s = some (.base .ECALL)) (h5 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hin : hashInput s = q)
    (h : ∀ a, W9Machine.GoodQFor InlineTail.image (writeHash s a) N C Q (budget a) (K a))
    (hb : ∀ hash : Hash, HashOk hash → budget (hash q) + 8 * q.blocks ≤ A) :
    W9Machine.GoodQFor InlineTail.image s (N + 1) (C + 8 * q.blocks) Q A
      (cc (liftM (HashSpec.query q) : OracleComp HashSpec _) K) := by
  intro F hF
  have hF' : F = (F - 1) + 1 := by omega
  refine ⟨?_, fun hash => ?_⟩
  · rw [hF', execute_hash (F - 1) hf h5 hv, cc_query, map_bind, hin]
    congr 1; funext a
    rw [Functor.map_map, ← (h a (F - 1) (by omega)).1, Functor.map_map]
    congr 1
  · rw [hF', evalWith_hash hash (F - 1) hf h5 hv, hin]
    obtain ⟨hn, hc, ha⟩ := (h (hash q) (F - 1) (by omega)).2 hash
    simp only [Execution.charge_exit, Execution.charge_cycles]
    refine ⟨hn, by omega, fun hs hok => ?_⟩
    obtain ⟨hq, hca⟩ := ha hs hok
    exact ⟨hq, by have hba := hb hash hok; omega⟩

theorem judged_native {s : MachineState} {N C A : Nat} {Q : Prop}
    {X : OracleComp HashSpec Judg.Obs}
    (h : Judg.GoodQ InlineTail.image s N C Q A X) :
    W9Machine.GoodQFor Images.InlineNative.image s N C Q A X := by
  rw [← InlineNativeBinding.image_eq]
  intro F hF
  obtain ⟨hx, he⟩ := h F hF
  exact ⟨hx, fun hash => ⟨(he hash).1, (he hash).2.1,
    fun hs _ => (he hash).2.2 hs⟩⟩

#print axioms suffix_code_equal
#print axioms look_ok
#print axioms lower_start_codeAt
#print axioms lower_rung_codeAt
#print axioms lower_end_codeAt
#print axioms path_sound
#print axioms paired_run
#print axioms dual_spec_run
#print axioms rung_piece
#print axioms judged_native
end SigGolfCandidate.T3M.Nonbinary.InlineTail.Lower

/- Execution-only lower43 replay. Pure source/invariant definitions remain
   the original Core700 ones. No completed old GoodQ is used as evidence. -/
namespace SigGolfCandidate.T3M.LCtx
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Nonbinary.InlineTail
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem inline_headJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 209920) (hp1 : c.rungPc i (c.dig i) + landOff (c.dig i) < 209920)
    (hrun1 : vrun (c.startPc i) 7 = some (headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i
      (c.dig i) (hSlot i (c.dig i))))
    (hrun2 : vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 =
      some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 5 5 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  have hs := slotL_props i hi.2
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  have keyE : ∀ k, k ≤ 80 → (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
    intro k hk'
    simp only [kAt, Addr.eval, E.eval, h22]
    exact c.base_off hc i hi.2 k hk'
  set r := headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i)) with hr
  have htable := c.header_load i (c.dig i)
    (kr _ _ (by simp [known]) (by decide))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := Lower.window_steps hrun1 (by have hb := Lower.lower_start_bound c i hi.2 hc.2.2.2.2.2.2.1; omega) s hpc hobl
  have hn : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headJH_keeps .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i))
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i hi.2
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 256 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headJH]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA, htable]
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hp24 := padHeader_at hc h0 hi hF
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  have hpcT : (r.toState s).pc = pcOf (c.rungPc i (c.dig i) + landOff (c.dig i)) := by
    rw [Result.toState_pc]; simp only [hr, headJH, E.eval]
  have hec : fetch vimage (r.toState s) = some (.base .ECALL) := by
    have hE := piece_ecall hrun2 hp1 (r.toState s) (by simp [ecallR, SymState.init]) rfl
    rw [← hE]
    apply fetch_pc_congr
    rw [hpcT, Result.toState_pc]; simp only [ecallR, E.eval]
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega)]; exact hp24
  · rw [Result.toState_getReg]; simp only [hr, headJH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headJH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    by_cases h6 : c.dig i = 6
    · simp only [hSlot, h6, if_true, E.eval]
    · simp only [hSlot, h6, if_false]
      rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · rw [hpcT]; simp only [landOff]

theorem inline_copyJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (first : Bool)
    (hfirst : first = true → i = 0 ∧ c.koff = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 209920)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x22 (offL i) (slotL i) (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x22 (offL i) (slotL i) (c.endPc i) with hr
  have hst := Lower.window_steps hrun (by have hb := Lower.lower_start_bound c i (by omega) hc.2.2.2.2.2.2.1; omega) s hpc (by simpa [hr, copyN] using c.copy_obl hc h22 i (by omega))
  have hkeep := copyN_keeps .x22 (offL i) (slotL i) (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; rfl

theorem inline_copyF_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (hi0 : i ≠ 0) (hp0 : c.startPc i < 209920)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x22 (offL i) (slotL i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyFH .x22 (offL i) (slotL i) (c.startPc i) with hr
  have hst := Lower.window_steps hrun (by have hb := Lower.lower_start_bound c i (by omega) hc.2.2.2.2.2.2.1; omega) s hpc (by simpa [hr, copyFH] using c.copy_obl hc h22 i (by omega))
  have hkeep := copyFH_keeps .x22 (offL i) (slotL i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, E.eval]; rw [hend]

theorem inline_copyN_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hi : c.i0 ≤ 42) (hp0 : c.startPc 42 < 209920)
    (hrun : vrun (c.startPc 42) 6 = some (copyN .x22 (offL 42) (slotL 42) (c.endPc 42)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 42 acc s) :
    ∃ t, Steps InlineTail.image s 5 5 t ∧ c.EndInv s0 42 (acc ++ [c.val 42]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x22 (offL 42) (slotL 42) (c.endPc 42) with hr
  have hst := Lower.window_steps hrun (by have hb := Lower.lower_start_bound c 42 (by omega) hc.2.2.2.2.2.2.1; omega) s hpc (by simpa [hr, copyN] using c.copy_obl hc h22 42 (by omega))
  have hkeep := copyN_keeps .x22 (offL 42) (slotL 42) (c.endPc 42)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 42 ⟨hi, le_refl _⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; rfl

theorem inline_headR_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (hi0 : i ≠ 0) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 209920) (hrp : c.rungPc i (c.dig i) = c.startPc i + 3)
    (hrun : vrun (c.startPc i) 8 =
      some (headRH .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps InlineTail.image s (if c.dig i = 6 then 5 else 4) (if c.dig i = 6 then 5 else 4) t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i (by omega)
  have hs := slotL_props i (by omega)
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h22 i (by omega)
  set r := headRH .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i with hr
  have htable := c.header_load i (c.dig i)
    (kr _ _ (by simp [known]) (by decide))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o rfl
    show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
    rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := Lower.window_steps hrun (by have hb := Lower.lower_start_bound c i (by omega) hc.2.2.2.2.2.2.1; omega) s hpc hobl
  have hec := piece_ecall hrun hp0 s hobl (by simp [hr, headRH])
  have hn : r.steps = (if c.dig i = 6 then 5 else 4) ∧ r.cycles = (if c.dig i = 6 then 5 else 4) := by
    simp only [hr, headRH]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := headRH_keeps .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i (by omega)
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 256 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRH]
    rw [memEval_one s _ _ (c.blk i + 16) A (keyE 16 (by omega)) (by omega) hA, htable]
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg hn]
  have hp24 := padHeader_at hc h0 ⟨hi.1, by omega⟩ hF
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 ⟨hi.1, by omega⟩ hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega)]; exact hp24
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    by_cases h6 : c.dig i = 6
    · simp only [h6, if_true, E.eval]
    · simp only [h6, if_false]
      rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · rw [Result.toState_pc]; simp only [hr, headRH, hrp]
    by_cases h6 : c.dig i = 6 <;> simp [h6, E.eval]

theorem inline_x_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (t : Nat) (ht : t < 13) (hi : c.i0 ≤ 3 * t + 2) (hp : c.tX (3 * t + 2) < 209920)
    (hrun : vrun (c.tX (3 * t + 2)) 5 = some (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
      (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760)))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3 * t + 2) acc s) :
    ∃ u, Steps InlineTail.image s (if 9 * ((t + 1) % 7) = 9 then 3 else 4)
      (if 9 * ((t + 1) % 7) = 9 then 3 else 4) u ∧ c.ChainIn s0 (3 * t + 3) acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX (3 * t + 2)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  set r := xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
    (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760) with hr
  have hst := Lower.window_steps hrun (by have hb := c.tX_lt (3 * t + 2); omega) s hpc' (by simp [hr, xJ])
  have hkeep := xJ_keeps (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
    (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760)
  have hW : s.getReg (if t + 1 < 7 then .x16 else .x17) = (if t + 1 < 7 then c.d0 else c.d1) := by
    split
    · exact kr .x16 c.d0 (by simp [known]) (by decide)
    · exact kr .x17 c.d1 (by simp [known]) (by decide)
  have h2 : s.getReg .x2 = BitVec.ofNat 64 (512 * (2 ^ 9 - 1)) := kr .x2 0x3fe00 (by simp [known]) (by decide)
  have h15 : s.getReg .x15 = BitVec.ofNat 64 0x6e000 := kr .x15 0x6e000 (by simp [known]) (by decide)
  have hm := shE_mask s _ _ hW (9 * ((t + 1) % 7)) 9 (by omega) (le_refl _)
  have hk1 := c.kOf_lt (t + 1) (by omega)
  have hrow : ((if t + 1 < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * ((t + 1) % 7)) % 2 ^ 9) = c.kOf (t + 1) := by
    rw [c.kOf_eq (t + 1) (by omega)]; rfl
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr at h ⊢; rcases h with h | h
      · exact Or.inl h
      · right; refine ⟨?_, h.2⟩; omega), hS⟩, by omega, h25, ?_⟩⟩
  · rw [Result.toState_pc]
    simp only [hr, xJ, E.eval, BinOp.eval]
    rw [h2, h15]
    have e : ((shE (if t + 1 < 7 then Reg.x16 else Reg.x17) (9 * ((t + 1) % 7))).eval s &&&
        BitVec.ofNat 64 (512 * (2 ^ 9 - 1))) = BitVec.ofNat 64 (512 * c.kOf (t + 1)) := by
      apply BitVec.eq_of_toNat_eq; rw [hm, hrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have e2 : BitVec.ofNat 64 (512 * c.kOf (t + 1)) + BitVec.ofNat 64 0x6e000 +
        (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760) =
        BitVec.ofNat 64 (0x1000 + 4 * entW (t + 1) (c.kOf (t + 1))) := by
      rw [tab_target _ _ _ _ (by omega) (by omega)]
      congr 1
      unfold entW ttabIdx; omega
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc
    rw [if_neg (by omega), if_pos (by omega), show (3 * t + 3) / 3 = t + 1 by omega]

theorem inline_x13_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (_hi : c.i0 ≤ 41) (hp : c.tX 41 < 209920) (hrun : vrun (c.tX 41) 4 = some ctabX)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 41 acc s) :
    ∃ u, Steps InlineTail.image s 3 3 u ∧ c.ChainIn s0 42 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX 41) := by rw [hpc]; unfold endPc; simp
  have hst := Lower.window_steps hrun (by have hb := c.tX_lt 41; omega) s hpc' (by simp [ctabX])
  have h15 : s.getReg .x15 = BitVec.ofNat 64 0x6e000 := kr .x15 0x6e000 (by simp [known]) (by decide)
  have h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 c.ck := kr .x29 _ (by simp [known]) (by decide)
  have hck := hc.2.2.2.2.2.2.1
  refine ⟨ctabX.toState s, hst, ⟨⟨fun x hx => (ctabX_keeps.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr at h ⊢; rcases h with h | h
      · exact Or.inl h
      · right; refine ⟨?_, h.2⟩; omega), hS⟩, by omega, h25, ?_⟩⟩
  · rw [Result.toState_pc]
    simp only [ctabX, E.eval, BinOp.eval, h15, h29]
    have e2 : BitVec.ofNat 64 0x6e000 - (7#64 - BitVec.ofNat 64 c.ck) <<< ((5 : Word).toNat % 64) + (-1824 : Word) =
        BitVec.ofNat 64 (0x1000 + 4 * (ctabIdx + 8 * c.ck)) := by
      have hk : c.ck ≤ 8 := hck
      generalize c.ck = k at hk ⊢
      unfold ctabIdx
      interval_cases k <;> decide
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc; simp

theorem inline_ret_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (p : Nat)
    (hp : p + 2 ≤ 176896) (hrun : vrun p 2 = some retR) (s : MachineState) (hpc : s.pc = pcOf p)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) :
    ∃ u, Steps InlineTail.image s 1 1 u ∧ (∀ x, u.getReg x = s.getReg x) ∧ (∀ A, u.getMem A = s.getMem A) ∧
      u.pc = pcOf c.ret := by
  have hst := Lower.window_steps hrun hp s hpc (by simp [retR])
  have h1 : s.getReg .x1 = pcOf c.ret := (hR .x1 (by decide)).trans (hk (.x1, pcOf c.ret) (by simp [known]))
  refine ⟨retR.toState s, hst, fun x => retR_keeps.reg s (by simp), fun A => rfl, ?_⟩
  rw [Result.toState_pc]
  simp only [retR, E.eval, BinOp.eval, h1]
  exact even_andNot1' _ (by have := hc.2.2.2.2.2.2.2.1; omega)

theorem inline_ckdone_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hrun : vrun ckDone 2 = some retR) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 42 acc s) :
    ∃ u, Steps InlineTail.image s 1 1 u ∧ c.ChainOut s0 43 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, -, hpc⟩ := hs
  obtain ⟨u, hst, hreg, hmem, hpcu⟩ := c.inline_ret_step hc hk ckDone (by decide) hrun s (by rw [hpc]; rfl) hR
  refine ⟨u, hst, ⟨⟨fun x hx => (hreg x).trans (hR x hx), fun A hA hn => (hmem _).trans (hF A hA hn),
    fun j hj => ?_⟩, hlen, hpcu⟩⟩
  exact ⟨(hmem _).trans (hS j hj).1, (hmem _).trans (hS j hj).2⟩

theorem inline_ck8_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h8 : c.ck = 8) (hrun : vrun (ctabIdx + 64) 2 = some retR) (acc : List Digest) (s : MachineState)
    (hs : c.ChainIn s0 42 acc s) : ∃ u, Steps InlineTail.image s 1 1 u ∧ c.ChainOut s0 42 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, -, hpc⟩ := hs
  obtain ⟨u, hst, hreg, hmem, hpcu⟩ := c.inline_ret_step hc hk (ctabIdx + 64) (by decide) hrun s
    (by rw [hpc]; unfold startPc; simp [h8]) hR
  refine ⟨u, hst, ⟨⟨fun x hx => (hreg x).trans (hR x hx), fun A hA hn => (hmem _).trans (hF A hA hn),
    fun j hj => ?_⟩, hlen, hpcu⟩⟩
  exact ⟨(hmem _).trans (hS j hj).1, (hmem _).trans (hS j hj).2⟩

theorem inline_rung_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hp : c.rungPc i m < 209920)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = 6 then some (slotL i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps InlineTail.image s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    Lower.rung_piece c hc hk i m (c.rungPc i m) hi.2 hm (by have hb := Lower.lower_rung_bound c i m hm; unfold landOff at hb; split_ifs at hb <;> omega) hrun s hpc hR h10 hH
  have hecOld : fetch vimage t = some (.base .ECALL) := by
    have hf := prefix_fetch_equal (c.rungPc i m + (if m = 6 then 2 else 1))
      (by have hb := Lower.lower_rung_bound c i m hm; unfold landOff at hb; split_ifs at hb <;> split_ifs <;> omega)
      t hpc'
    exact hf.symm.trans hec
  have hs := slotL_props i hi.2
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16, ?_, ?_, ?_, ?_, ?_, hecOld⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h10
  · by_cases h6 : m = 6
    · rw [h12a h6, if_pos h6]
    · rw [h12b (by omega), h12, if_neg h6]
  · rw [hpc']

theorem inline_end_next (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (i : Nat)
    (hi : c.i0 ≤ i ∧ i ≤ 42) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) :
    ∃ u, Steps InlineTail.image s (xCost i) (xCost i) u ∧ c.ChainNext s0 (i + 1) acc u := by
  by_cases h42 : i = 42
  · subst h42
    obtain ⟨u, hst, hu⟩ := c.inline_ckdone_step hc hk ck_parts.2.2.2.2 acc s hs
    refine ⟨u, by simpa [xCost] using hst, ?_⟩
    unfold ChainNext; rw [if_neg (by omega)]; exact hu
  · by_cases h2 : i % 3 = 2
    · by_cases h41 : i = 41
      · subst h41
        have hx := c.blk_at 41 (by omega)
        unfold blkCheck xOK at hx
        simp only [Bool.and_eq_true] at hx
        have hrun : vrun (c.tX 41) 4 = some ctabX := by
          have := rOK_eq hx.2; exact this
        obtain ⟨u, hst, hu⟩ := c.inline_x13_step hc hk (by omega) (by have := c.tX_lt 41; omega) hrun acc s hs
        refine ⟨u, by simpa [xCost] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega)]; exact hu
      · obtain ⟨t, rfl⟩ : ∃ t, i = 3 * t + 2 := ⟨i / 3, by omega⟩
        have hx := c.blk_at (3 * t + 2) (by omega)
        rw [show (3 * t + 2) / 3 = t by omega] at hx
        unfold blkCheck xOK at hx
        simp only [Bool.and_eq_true] at hx
        rw [if_neg (by omega)] at hx
        have hrun := rOK_eq hx.2
        have htx : c.tX (3 * t + 2) = pcX t (c.dig (3 * t + 1)) (c.dig (3 * t + 2)) := by
          unfold tX; rw [show (3 * t + 2) / 3 = t by omega]
        rw [← htx] at hrun
        obtain ⟨u, hst, hu⟩ := c.inline_x_step hc hk t (by omega) hi.1 (by have := c.tX_lt (3 * t + 2); omega) hrun acc s hs
        have he : (9 * ((t + 1) % 7) = 9) ↔ (3 * t + 2 = 2 ∨ 3 * t + 2 = 23) := by omega
        refine ⟨u, by simpa [xCost, h42, h41, he] using hst, ?_⟩
        unfold ChainNext; rw [if_pos (by omega), show 3 * t + 2 + 1 = 3 * t + 3 by ring]; exact hu
    · refine ⟨s, by simpa [xCost, h42, h2] using Steps.refl s, ?_⟩
      unfold ChainNext; rw [if_pos (by omega)]
      exact c.next_inline s0 i (by omega) h2 acc s hs

theorem inline_steps_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8) (acc : List Digest)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → W9Machine.GoodQFor InlineTail.image t N C Q A (K (acc ++ [v]))) :
    ∀ k m, m + k = 6 → c.dig i ≤ m → ∀ v s, c.PreHash s0 i acc m v s →
      W9Machine.GoodQFor InlineTail.image s (N + 3 * (7 - m) + 4) (C + preCost m + xCost i) Q (A + preCost m + xCost i)
        (Verify.ccM (c.rest i m v) (fun v => K (acc ++ [v]))) := by
  have hrc : ∀ m, m ≤ 6 → c.rungPc i m < 209920 := fun m hm => c.rungPc_lt i m hm
  have hx4 := xCost_le i
  intro k
  induction k with
  | zero =>
    intro m hm hd v s hs
    obtain rfl : m = 6 := by omega
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i 6 hi (le_refl _) hd acc v s hs
    rw [rest_succ c i 6 (le_refl _)]
    have hfOld := hs.2.2.2.2.2.2.2.2.2
    have hf : fetch InlineTail.image s = some (.base .ECALL) := by
      have hp := hs.2.2.2.2.2.2.2.2.1
      have hb := Lower.lower_rung_bound c i m (by omega)
      exact (prefix_fetch_equal _ (by unfold landOff at hb; split_ifs at hb <;> split_ifs <;> omega) s hp).trans hfOld
    have H : ∀ a : BitVec 256, W9Machine.GoodQFor InlineTail.image (writeHash s a) (N + xCost i) (C + xCost i) Q (A + xCost i)
        (Verify.ccM (c.rest i 7 (a.extractLsb' 0 128)) (fun v => K (acc ++ [v]))) := by
      intro a
      rw [rest_7, Verify.ccM_pure]
      obtain ⟨u, hu, hn⟩ := c.inline_end_next hc hk i hi _ _ ((hpost a).2 rfl)
      exact W9Machine.GoodQFor.steps' hu (hK _ _ hn) (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := W9Machine.GoodQFor.shortHash_bind (f := c.rest i 7) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [chainInputP_pad]; exact hin) H
    rw [chainInputP_pad, chainInputP_blocks] at h3
    exact h3.mono (by omega) (by simp [preCost]; omega) (fun hq => ⟨hq, by simp [preCost]; omega⟩)
  | succ k ih =>
    intro m hm hd v s hs
    obtain ⟨h5, hv, hin, hpost⟩ := c.prehash_step hc s0 hk h0 i m hi (by omega) hd acc v s hs
    rw [rest_succ c i m (by omega)]
    have hfOld := hs.2.2.2.2.2.2.2.2.2
    have hf : fetch InlineTail.image s = some (.base .ECALL) := by
      have hp := hs.2.2.2.2.2.2.2.2.1
      have hb := Lower.lower_rung_bound c i m (by omega)
      exact (prefix_fetch_equal _ (by unfold landOff at hb; split_ifs at hb <;> split_ifs <;> omega) s hp).trans hfOld
    have H : ∀ a : BitVec 256, W9Machine.GoodQFor InlineTail.image (writeHash s a) (N + 3 * (7 - (m + 1)) + 4 + 2)
        (C + preCost (m + 1) + xCost i + (if m + 1 = 6 then 2 else 1)) Q
        (A + preCost (m + 1) + xCost i + (if m + 1 = 6 then 2 else 1))
        (Verify.ccM (c.rest i (m + 1) (a.extractLsb' 0 128)) (fun v => K (acc ++ [v]))) := by
      intro a
      have hrun := c.chk_rung' i (m + 1) hi.2 (by omega) (by omega) (by omega) hck
      obtain ⟨u, hu, hp⟩ := c.inline_rung_step hc hk i (m + 1) hi (by omega) (hrc _ (by omega)) hrun acc _ _
        ((hpost a).1 (by omega))
      have := ih (m + 1) (by omega) (by omega) _ _ hp
      exact W9Machine.GoodQFor.steps' hu this (by split <;> omega) (by omega) (fun hq => ⟨hq, by omega⟩)
    have h3 := W9Machine.GoodQFor.shortHash_bind (f := c.rest i (m + 1)) (K := fun v => K (acc ++ [v])) hf h5 hv
      (by rw [chainInputP_pad]; exact hin) H
    rw [chainInputP_pad, chainInputP_blocks] at h3
    refine h3.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · unfold preCost
      by_cases h6 : m + 1 = 6
      · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega
    · unfold preCost
      by_cases h6 : m + 1 = 6
      · rw [if_pos h6, if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h6, if_pos (by omega), if_pos (by omega)]; omega

theorem inline_chain_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hck : i = 42 → c.ck < 8)
    (acc : List Digest) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, c.ChainNext s0 (i + 1) (acc ++ [v]) t → W9Machine.GoodQFor InlineTail.image t N C Q A (K (acc ++ [v])))
    (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    W9Machine.GoodQFor InlineTail.image s (N + 40) (C + chainCost i (c.dig i)) Q (A + chainCost i (c.dig i))
      (Verify.ccM (chainP c.lay c.tree c.leaf (i + c.koff) (c.dig i) (7 - c.dig i) (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i))
        (fun v => K (acc ++ [v]))) := by
  have hx4 := xCost_le i
  have hdl : c.dig i < 8 := by
    by_cases h42 : i = 42
    · subst h42; rw [dig42]; exact hck rfl
    · exact c.dig_lt8 i (by omega)
  have hsp := c.startPc_lt i hi.2 hc.2.2.2.2.2.2.1
  by_cases h7 : c.dig i = 7
  ·
    rw [h7, show 7 - 7 = 0 from rfl]
    have hspec : chainP c.lay c.tree c.leaf (i + c.koff) 7 0 (c.pad0 i) (c.pad1 i) (c.padHeader i) (c.val i) = pure (c.val i) := rfl
    rw [hspec, Verify.ccM_pure]
    by_cases h42 : i = 42
    · subst h42
      have hrun : vrun (c.startPc 42) 6 = some (copyN .x22 (offL 42) (slotL 42) (c.endPc 42)) := by
        have := ck_parts.2.1
        rw [dig42] at h7
        unfold startPc endPc; simp only [if_true, h7]; exact this
      obtain ⟨t, hst, hE⟩ := c.inline_copyN_step hc hk h0 hi.1 hsp hrun acc s hs
      obtain ⟨u, hu, hn⟩ := c.inline_end_next hc hk 42 hi _ _ hE
      refine W9Machine.GoodQFor.steps' hst (W9Machine.GoodQFor.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
        (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp; omega) (fun hq => ⟨hq, by unfold chainCost; simp; omega⟩)
    · by_cases h0' : i % 3 = 0
      · have hrun := c.chk_copyJ i (by omega) h0' h7
        obtain ⟨t, hst, hE⟩ := c.inline_copyJ_step hc hk h0 i ⟨hi.1, by omega⟩ (i / 3 == 0)
          (fun h => by
            have : i = 0 := by simp at h; omega
            exact ⟨this, hko (by omega)⟩)
          (fun h => by simp at h; omega) hsp hrun acc s hs
        obtain ⟨u, hu, hn⟩ := c.inline_end_next hc hk i hi _ _ hE
        refine W9Machine.GoodQFor.steps' hst (W9Machine.GoodQFor.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
          (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp [h0', h7, h42]; omega)
          (fun hq => ⟨hq, by unfold chainCost; simp [h0', h7, h42]; omega⟩)
      · have hrun := c.chk_copyF i (by omega) h0' h7
        have hend : c.startPc i + 4 = c.endPc i := by
          simp only [startPc, endPc, if_neg h42, if_neg h0']
          by_cases h1 : i % 3 = 1
          · have e1 : c.dig (3 * (i / 3) + 1) = 7 := by rw [show 3 * (i / 3) + 1 = i by omega, h7]
            rw [if_pos h1, if_pos h1]; unfold tB tC pcC; rw [e1]; rfl
          · have e2 : c.dig (3 * (i / 3) + 2) = 7 := by rw [show 3 * (i / 3) + 2 = i by omega, h7]
            rw [if_neg h1, if_neg h1]; unfold tC tX pcX; rw [e2]; rfl
        obtain ⟨t, hst, hE⟩ := c.inline_copyF_step hc hk h0 i ⟨hi.1, by omega⟩ (by omega) hsp hend hrun acc s hs
        obtain ⟨u, hu, hn⟩ := c.inline_end_next hc hk i hi _ _ hE
        refine W9Machine.GoodQFor.steps' hst (W9Machine.GoodQFor.steps' hu (hK _ u hn) (le_refl _) (le_refl _)
          (fun hq => ⟨hq, le_refl _⟩)) (by omega) (by unfold chainCost; simp [h0', h7]; omega)
          (fun hq => ⟨hq, by unfold chainCost; simp [h0', h7]; omega⟩)
  ·
    have hd : c.dig i < 7 := by omega
    rw [chainP_rest]
    have hsteps := c.inline_steps_good hc hk h0 i hi hck acc K N C A Q hK (6 - c.dig i) (c.dig i) (by omega) (le_refl _)
    have hrp := c.rungPc_lt i (c.dig i) (by omega)
    by_cases h0' : i % 3 = 0
    · have hruns : vrun (c.startPc i) 7 = some (headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i
            (c.dig i) (hSlot i (c.dig i))) ∧
          vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 =
            some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))) := by
        by_cases h42 : i = 42
        · subst h42
          have := ck_parts.1 c.ck (by rw [dig42] at hd; exact hd)
          have hst42 : c.startPc 42 = ctabIdx + 8 * c.ck := by unfold startPc; simp
          have hrp42 : c.rungPc 42 (c.dig 42) = ckR0 + 2 * c.ck := by unfold rungPc; simp [dig42]
          rw [hst42, hrp42, dig42]; exact this
        · exact c.chk_headJ i (by omega) h0' hd
      obtain ⟨t, hst, hP⟩ := c.inline_headJ_step hc hk h0 i hi hd hsp (c.rungPc_land_lt i (c.dig i) (by omega))
        hruns.1 hruns.2 acc s hs
      refine W9Machine.GoodQFor.steps' hst (hsteps _ _ hP) (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost; rw [if_pos h0', if_neg h7]
        split_ifs <;> omega
      · unfold chainCost preCost; rw [if_pos h0', if_neg h7]
        split_ifs <;> omega
    · have hrun := c.chk_headR i (by omega) h0' hd
      obtain ⟨t, hst, hP⟩ := c.inline_headR_step hc hk h0 i ⟨hi.1, by omega⟩ (by omega) hd hsp
        (c.rungPc_inline i (by omega) h0') hrun acc s hs
      refine W9Machine.GoodQFor.steps' hst (hsteps _ _ hP) (by split <;> omega) ?_ (fun hq => ⟨hq, ?_⟩)
      · unfold chainCost preCost; rw [if_neg h0', if_neg h7]
        by_cases h6 : c.dig i = 6
        · rw [if_pos h6, h6]; norm_num; omega
        · rw [if_neg h6, if_pos (by omega)]; omega
      · unfold chainCost preCost; rw [if_neg h0', if_neg h7]
        by_cases h6 : c.dig i = 6
        · rw [if_pos h6, h6]; norm_num; omega
        · rw [if_neg h6, if_pos (by omega)]; omega

theorem inline_chains_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs)
    (N C A : Nat) (Q : Prop) (hK : ∀ ends t, c.ChainIn s0 42 ends t → W9Machine.GoodQFor InlineTail.image t N C Q A (K ends)) :
    ∀ k i, i + k = 42 → c.i0 ≤ i → ∀ acc s, c.ChainIn s0 i acc s →
      W9Machine.GoodQFor InlineTail.image s (N + 40 * k) (C + c.chainsCost i k) Q (A + c.chainsCost i k)
        (Verify.ccM ((List.range' i k).foldlM c.chainF acc) K) := by
  intro k
  induction k with
  | zero =>
    intro i hik _ acc s hs
    obtain rfl : i = 42 := by omega
    simpa [chainsCost] using hK acc s hs
  | succ k ih =>
    intro i hik hi0 acc s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, Verify.ccM_bind]
    have := c.inline_chain_good hc hk h0 hko i ⟨hi0, by omega⟩ (fun h => absurd h (by omega)) acc
      (fun ends => Verify.ccM ((List.range' (i + 1) k).foldlM c.chainF ends) K)
      (N + 40 * k) (C + c.chainsCost (i + 1) k) (A + c.chainsCost (i + 1) k) Q
      (fun v t ht => by
        have ht' : c.ChainIn s0 (i + 1) (acc ++ [v]) t := by
          unfold ChainNext at ht; rwa [if_pos (by omega)] at ht
        exact ih (i + 1) (by omega) (by omega) (acc ++ [v]) t ht') s hs
    refine this.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega
    · simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]; omega

theorem inline_ck_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hko : c.i0 = 0 → c.koff = 0) (hck : c.ck < 8)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → W9Machine.GoodQFor InlineTail.image t N C Q A (K ends))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 42 acc s) :
    W9Machine.GoodQFor InlineTail.image s (N + 40) (C + chainCost 42 c.ck) Q (A + chainCost 42 c.ck)
      (Verify.ccM (c.chainF acc 42) K) := by
  have := c.inline_chain_good hc hk h0 hko 42 ⟨hc.2.2.2.2.2.2.2.2.1, le_refl _⟩ (fun _ => hck) acc K N C A Q
    (fun v t ht => by
      have ht' : c.ChainOut s0 43 (acc ++ [v]) t := by unfold ChainNext at ht; rwa [if_neg (by omega)] at ht
      exact hK _ t ht') s hs
  simp only [chainF, Verify.ccM_bind, Verify.ccM_pure]
  rw [dig42] at this ⊢
  exact this

theorem inline_ck8_good (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h8 : c.ck = 8) (X : OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop) (acc : List Digest)
    (hK : ∀ t, c.ChainOut s0 42 acc t → W9Machine.GoodQFor InlineTail.image t N C Q A X)
    (s : MachineState) (hs : c.ChainIn s0 42 acc s) : W9Machine.GoodQFor InlineTail.image s (N + 1) (C + 1) Q (A + 1) X := by
  obtain ⟨u, hst, hu⟩ := c.inline_ck8_step hc hk h8 ck_parts.2.2.1 acc s hs
  exact W9Machine.GoodQFor.steps hst (hK u hu)

-- The literal source/count expressions below are exactly the canonical
-- LeafSem.lowP/lowCost definitions. Spelling them here avoids importing a
-- completed leaf/layer judgment into this focused physical lower module;
-- no new definition, premise, or duplicate proof body is introduced.
theorem inline_lower_good (c : LCtx) (hc : c.ok) (hi0 : c.i0 = 0) (hko : c.koff = 0) (hck : c.ck < 8) {s0 : MachineState}
    (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (h0 : c.Orig0 s0)
    (K : List Digest → OracleComp Legacy.HashSpec Verify.Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ ends t, c.ChainOut s0 43 ends t → W9Machine.GoodQFor InlineTail.image t N C Q A (K ends))
    (s : MachineState) (hs : c.ChainIn s0 0 [] s) :
    W9Machine.GoodQFor InlineTail.image s (N + 1720)
      (C + (c.chainsCost 0 42 + chainCost 42 c.ck)) Q
      (A + (c.chainsCost 0 42 + chainCost 42 c.ck))
      (Verify.ccM ((List.range' 0 42).foldlM c.chainF [] >>= fun ends => c.chainF ends 42) K) := by
  rw [Verify.ccM_bind]
  have H := c.inline_chains_good hc hk h0 (fun _ => hko) (fun e => Verify.ccM (c.chainF e 42) K)
    (N + 40) (C + chainCost 42 c.ck) (A + chainCost 42 c.ck) Q
    (fun ends t ht => c.inline_ck_good hc hk h0 (fun _ => hko) hck K N C A Q hK ends t ht) 42 0 (by omega) (by omega) [] s hs
  refine H.mono (by omega) ?_ (fun hq => ⟨hq, ?_⟩)
  · omega
  · omega

#print axioms inline_lower_good
end SigGolfCandidate.T3M.LCtx
