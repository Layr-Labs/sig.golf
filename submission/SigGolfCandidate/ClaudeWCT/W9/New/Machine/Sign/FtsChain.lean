import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsTable
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Search

section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
theorem run_pres {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {regs : List (Reg × E)} {mem : SymMem} {obl : List Oblig} {pc : Nat} {ec : Bool}
    {k : Nat} {brs : List Br} (h : run look stops n dirs = some (pres regs mem obl pc ec k brs)) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ obl, o.holds s) (hbr : ∀ b ∈ brs, b.holds s) :
    Steps im s k k ((pres regs mem obl pc ec k brs).toState s) ∧
      (ec = true → fetch im ((pres regs mem obl pc ec k brs).toState s) = some (.base .ECALL)) :=
  run_sound hl h s hpc hobl hbr
theorem runA_pres {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {regs : List (Reg × E)} {mem : SymMem} {obl : List Oblig} {pc : Nat} {ec : Bool}
    {k : Nat} {brs : List Br} (h : runA look stops n dirs = some (pres regs mem obl pc ec k brs)) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ obl, o.holds s) (hbr : ∀ b ∈ brs, b.holds s) :
    Steps im s k k ((pres regs mem obl pc ec k brs).toState s) ∧
      (ec = true → fetch im ((pres regs mem obl pc ec k brs).toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h hl s hpc (by intro p hp; cases hp) hobl hbr
theorem no_obl (s : MachineState) : ∀ o ∈ ([] : List Oblig), o.holds s := by intro o ho; cases ho
theorem runA_pres2 {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {regs : List (Reg × E)} {mem : SymMem} {obl : List Oblig} {pc : Nat} {ec : Bool}
    {k cyc : Nat} {brs : List Br} (h : runA look stops n dirs = some (pres2 regs mem obl pc ec k cyc brs))
    (s : MachineState) (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ obl, o.holds s) (hbr : ∀ b ∈ brs, b.holds s) :
    Steps im s k cyc ((pres2 regs mem obl pc ec k cyc brs).toState s) ∧
      (ec = true → fetch im ((pres2 regs mem obl pc ec k cyc brs).toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h hl s hpc (by intro p hp; cases hp) hobl hbr
theorem no_br (s : MachineState) : ∀ b ∈ ([] : List Br), b.holds s := by intro b hb; cases hb
theorem valid_ofNat {s : MachineState} {b : E} {B off w : Nat} (hb : b.eval s = BitVec.ofNat 64 B)
    (hal : (B + off) % w = 0) (hhi : B + off + w ≤ MEMORY_BYTES) :
    (Oblig.valid ⟨some b, BitVec.ofNat 64 off⟩ w).holds s := by
  unfold MEMORY_BYTES at hhi
  simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat, accessValid, rangeValid, Bool.and_eq_true,
    decide_eq_true_eq, toNat_ofNat_lt (show B + off < 2 ^ 64 by omega), MEMORY_BYTES]
  exact ⟨hhi, hal⟩
theorem ne_ofNat {s : MachineState} {b : E} {B off K : Nat} (hb : b.eval s = BitVec.ofNat 64 B)
    (hlt : B + off < 2 ^ 64) (hk : K < 2 ^ 64) (hne : B + off ≠ K) :
    (Oblig.ne ⟨some b, BitVec.ofNat 64 off⟩ ⟨none, BitVec.ofNat 64 K⟩).holds s := by
  simp only [Oblig.holds, Addr.eval, hb, ofNat_add_ofNat]
  intro h
  exact hne ((ofNat_inj hlt hk).mp h)
theorem br_ne_holds (s : MachineState) (x y : E) (d : Bool) :
    Br.holds s ⟨.ne, x, y, d⟩ ↔ ((x.eval s != y.eval s) = d) := Iff.rfl
theorem br_ltu_holds (s : MachineState) (x y : E) (d : Bool) :
    Br.holds s ⟨.ltu, x, y, d⟩ ↔ (BitVec.ult (x.eval s) (y.eval s) = d) := Iff.rfl
theorem ofNat_bne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he => h ((ofNat_inj ha hb).mp he)
    simp [h, this]
theorem ofNat_ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, toNat_ofNat_lt ha, toNat_ofNat_lt hb]
theorem frame_of_memEval {s t : MachineState} {ws : SymMem} (ht : ∀ a, t.getMem a = memEval s ws a)
    (W : Nat → Prop) (hW : ∀ p ∈ ws, p.1.base = none ∧ W p.1.off.toNat) : Frame s t W := by
  intro A hA hn
  rw [ht, memEval_frame_ofNat s ws A hA (fun p hp => ⟨(hW p hp).1, fun he => hn (he ▸ (hW p hp).2)⟩)]
theorem off_mwc (a : Nat) (e : E) (ha : a < 2 ^ 64) : (mwc a e).1.off.toNat = a := toNat_ofNat_lt ha
theorem memEval_mwc_self (s : MachineState) (a : Nat) (e : E) (ws : SymMem) (ha : a < 2 ^ 64) :
    memEval s (mwc a e :: ws) (BitVec.ofNat 64 a) = e.eval s := by
  rw [memEval_mwc s a a e ws ha ha, if_pos rfl]
theorem memEval_mwc_ne (s : MachineState) {a A : Nat} (e : E) (ws : SymMem) (hA : A < 2 ^ 64) (ha : a < 2 ^ 64)
    (hne : A ≠ a) : memEval s (mwc a e :: ws) (BitVec.ofNat 64 A) = memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_mwc s a A e ws hA ha, if_neg hne]
macro "ao" : tactic => `(tactic| ((try simp only [SK, SIG, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, PAIRW, CHAINW, LEAFW,
  NODEW, FORW, NOUTW, HEAPW, SCREND, slotV, slotP, hdr6, hdr8, chainK, nodeK, true_or, or_true,
  and_true, true_and]) <;> omega))
macro "aoh" : tactic => `(tactic| ((try simp only [SK, SIG, DIG, NBUF, FOUT, IDXV, TBL, PRIVW, PAIRW, CHAINW, LEAFW,
  NODEW, FORW, NOUTW, HEAPW, SCREND, slotV, slotP, hdr6, hdr8, chainK, nodeK, true_or, or_true,
  and_true, true_and] at *) <;> omega))
section pieces
variable {im : Image}
theorem step_SK (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 11175) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf (cbase 0) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 8 * k))) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 32 + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 16 + 8 * k))) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = PRIVW + 40 ∨ A = PRIVW + 32 ∨ A = PRIVW + 8 ∨ A = PRIVW) := by
  obtain ⟨hst, -⟩ := run_pres (headLook_ok hcode) runSK_eq s hpc (no_obl s) (no_br s)
  have hm : ∀ a, ((expSK).toState s).getMem a = memEval s expSK.st.mem a := fun a => rfl
  refine ⟨_, hst, rfl, fun k hk => ?_, fun k hk => ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · refine frame_of_memEval hm _ (fun p hp => ?_)
    simp only [expSK, pres, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [mwc, PRIVW, BitVec.toNat_ofNat] <;> decide
def fk (c : Nat) : Nat := if fhas c then 13 else 12
theorem fsrcE_eq (c : Nat) : fsrcE c = SearchM.grpE c := rfl
theorem fieldE_eq (c : Nat) : fieldE c = SearchM.fieldEOld c := rfl
theorem fchildE_eq (c : Nat) : fchildE c = SearchM.childE c := rfl
theorem childE_eval (s : MachineState) (N : BitVec 256) (hN : OutAt s NBUF N) (c : Nat) (hc : c < 9) :
    (fchildE c).eval s = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase c % 128) := by
  rw [fchildE_eq]; exact SearchM.childE_eval s N hN c hc
theorem step_F (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (cbase c))
    {N : BitVec 256} (hN : OutAt s NBUF N) :
    ∃ t, Steps im s (fk c) (fk c) t ∧ t.pc = pcOf (lwuI c) ∧
      t.getReg .x24 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.childBase c % 128) ∧
      t.getReg .x28 = BitVec.ofNat 64 (TBL + 4 * (N.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runF_eq hc) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
  · rw [pres_getReg]; exact childE_eval s N hN c hc
  · rw [pres_getReg]
    show BinOp.eval .add (BinOp.eval .sll ((fieldE c).eval s) (BitVec.ofNat 64 2)) (BitVec.ofNat 64 TBL) = _
    rw [fieldE_eq, SearchM.fieldEOld_eval s N hN c hc, binop_sll _ _ (by norm_num), ofNat_shl]
    simp only [BinOp.eval, ofNat_add_ofNat]
    congr 1; ring
theorem eval_orIdx (s : MachineState) {index : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index) :
    orIdx.eval s = BitVec.ofNat 64 (index + 2 ^ 32 * 0) := by
  show BitVec.ofNat 64 0 ||| s.getReg .x22 = _
  rw [h22, Nat.mul_zero, Nat.add_zero]
  exact BitVec.zero_or
theorem step_Z (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (lwuI c + 1))
    {index : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 14 14 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ecI c) ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 (COEF + 32 * 0) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * 0) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = PRIVW + 16 ∨ A = PRIVW + 24) := by
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runZ_eq hc) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_orIdx s h22
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expZ, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem eval_x7p1 (s : MachineState) {j : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) :
    x7p1.eval s = BitVec.ofNat 64 (j + 1) := by
  show s.getReg .x7 + BitVec.ofNat 64 1 = _; rw [h7, ofNat_add_ofNat]
theorem eval_pairWE (s : MachineState) {j index : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    pairWE.eval s = BitVec.ofNat 64 (index + 2 ^ 32 * (j + 1)) := by
  show BinOp.eval .or (BinOp.eval .sll (x7p1.eval s) (BitVec.ofNat 64 32)) (s.getReg .x22) = _
  rw [eval_x7p1 s h7, binop_sll _ _ (by norm_num), ofNat_shl, h22]
  exact ofNat_or_hi index (j + 1) hidx
theorem step_CLc (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (paI c))
    {j index B : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) (hj : j + 1 < 27)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 B) (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hidx : index < 2 ^ 32) :
    ∃ t, Steps im s 10 10 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ecI c) ∧
      t.getReg .x7 = BitVec.ofNat 64 (j + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 (B + 32) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * (j + 1)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = PRIVW + 24) := by
  have hb : ∀ b ∈ (expCL c true).brs, b.holds s := by
    intro b hb
    simp only [expCL, if_true, pres, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_x7p1 s h7, eval_cE, ofNat_bne (by omega) (by norm_num)]
    simp; omega
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runCL_eq hc true) s hpc (no_obl s) hb
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; exact eval_x7p1 s h7, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_⟩
  · rw [pres_getReg]; show s.getReg .x12 + BitVec.ofNat 64 32 = _; rw [h12, ofNat_add_ofNat]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_pairWE s h7 h22 hidx
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expCL, if_true, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; exact ⟨rfl, by rw [off_mwc _ _ (by ao)]⟩
theorem step_CLx (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (paI c))
    {j : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) (hj : j + 1 = 27) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x6, .x7, .x12, .x18] ∧ Frame s t (fun _ => False) := by
  have hb : ∀ b ∈ (expCL c false).brs, b.holds s := by
    intro b hb
    simp only [expCL, Bool.false_eq_true, if_false, pres, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_x7p1 s h7, eval_cE, ofNat_bne (by omega) (by norm_num)]
    simp; omega
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runCL_eq hc false) s hpc (no_obl s) hb
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp),
    fun A _ _ => rfl⟩
theorem eval_ptE (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (_hj : j < 2 ^ 32)
    (i : Nat) : (ptE i).eval s = BitVec.ofNat 64 (6 * j + i + 1) := by
  show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .add (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 1))
    (s.getReg .x18)) (BitVec.ofNat 64 1)) (BitVec.ofNat 64 (i + 1)) = _
  have e1 : BinOp.eval .add (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 1)) (s.getReg .x18) =
      BitVec.ofNat 64 (3 * j) := by
    rw [binop_sll _ _ (by norm_num), h18, ofNat_shl]; simp only [BinOp.eval]; rw [ofNat_add_ofNat]; congr 1; ring
  rw [e1, binop_sll _ _ (by norm_num), ofNat_shl]; simp only [BinOp.eval]; rw [ofNat_add_ofNat]; congr 1; ring
theorem step_Q (hcode : NewCodeAt im) {c i j : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (qI c i)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (hj : j < 128) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf hornI ∧ t.getReg .x1 = pcOf (qI c i + 5) ∧
      t.getReg .x6 = BitVec.ofNat 64 (6 * j + i + 1) ∧ RegsExcept s t [.x1, .x6] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runQ_eq hc hi) s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; exact eval_ptE s h18 (by omega) i,
    pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
def chainW0 (c i j index p : Nat) : Nat := index * 2 ^ 27 + j * 2 ^ 20 + chainK c i + 256 * p
theorem chainW0_merge (c i j index p q : Nat) (hc : c < 9) (hi : i < 6) (hp : p < 4) (hq : q < 4) :
    StoreKind.merge .b (BitVec.ofNat 64 (chainW0 c i j index p)) 1 (BitVec.ofNat 64 q) =
      BitVec.ofNat 64 (chainW0 c i j index q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat8 _ _ (by omega)]
  simp only [chainW0, chainK, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem step_S (hcode : NewCodeAt im) {c i j index w : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (qI c i + 5)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) (hd : w / 8 ^ i % 8 ≤ 4) :
    ∃ t, Steps im s (if c = 0 then 14 else 15) (if c = 0 then 14 else 15) t ∧ t.pc = pcOf (chkI c i 0) ∧
      t.getReg .x26 = BitVec.ofNat 64 (4 - w / 8 ^ i % 8) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index 0) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0 ∧
      RegsExcept s t [.x6, .x7, .x26, .x29] ∧ Frame s t (fun A => A = CHAINW + 24 ∨ A = CHAINW + 16) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runS_eq hc hi) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]; exact eval_dE s i h25 hw (by omega) hd
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao),
      eval_qE s h18 h22 hj (chainK_lt c i hc hi)]
    simp only [chainW0, Nat.mul_zero, Nat.add_zero]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expS, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_Chk (hcode : NewCodeAt im) {c i st j sel e : Nat} (hc : c < 9) (hi : i < 6) (hst : st < 5)
    (s : MachineState) (hpc : s.pc = pcOf (chkI c i st)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (h26 : s.getReg .x26 = BitVec.ofNat 64 e) (hj : j < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (he : e < 2 ^ 64) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t k, Steps im s k k t ∧ k ≤ 11 ∧ t.pc = pcOf (skipI c i st) ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = slotV c i + 8 ∨ A = slotV c i) ∧ (j = sel → e = st → DigAt t (slotV c i) v) ∧
      (¬ (j = sel ∧ e = st) → Frame s t (fun _ => False)) := by
  have hl := coordLook_ok hcode hc
  by_cases hjs : j = sel
  · subst hjs
    by_cases hes : e = st
    · subst hes
      obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 2 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      refine ⟨_, 11, hst', le_rfl, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_, fun _ _ => ⟨?_, ?_⟩, ?_⟩
      · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
        simp only [expChk, pres, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false,
          List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
      · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
      · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
      · intro h; exact absurd ⟨rfl, rfl⟩ h
    · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 1 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp [hes]
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      exact ⟨_, 3, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
        fun _ h => absurd h hes, fun _ A _ _ => rfl⟩
  · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 0 < 3)) s hpc (no_obl s) (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hsel]; simp [hjs])
    exact ⟨_, 1, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
      fun h => absurd h hjs, fun _ A _ _ => rfl⟩
theorem step_Stp (hcode : NewCodeAt im) {c i st j index : Nat} (hc : c < 9) (hi : i < 6) (h1 : 1 ≤ st) (h4 : st < 5)
    (s : MachineState) (hpc : s.pc = pcOf (skipI c i (st - 1))) {pv : Nat} (hpv : pv < 4)
    (h16 : s.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index pv)) :
    ∃ t, Steps im s 9 9 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (chkI c i st - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAINW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAINW + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (st - 1)) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = CHAINW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (coordLook_ok hcode hc) (runStp_eq hc hi h1 h4) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]
    show StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 1 (BitVec.ofNat 64 (st - 1)) = _
    rw [h16, chainW0_merge c i j index pv (st - 1) hc hi hpv (by omega)]
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expStp, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; refine ⟨rfl, ?_⟩; rw [off_mwc _ _ (by ao)]
theorem step_Lc (hcode : NewCodeAt im) {c i : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (skipI c i 4)) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) v ∧
      t.getReg .x29 = BitVec.ofNat 64 LEAFW ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFW + leafOff i + 8 ∨ A = LEAFW + leafOff i) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runLc_eq hc hi) s hpc (no_obl s) (no_br s)
  have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
  refine ⟨_, hst', rfl, ⟨?_, ?_⟩, rfl, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expLc, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem padE_eval (s : MachineState) (c off : Nat) :
    (padE c off).eval s = if c = 0 then 0 else s.getMem (BitVec.ofNat 64 (FORW + forOff (c - 1) + off)) := by
  unfold padE; split_ifs <;> rfl
/-- The leaf header block (nested FTS r1-1): for `c >= 1` the pad slot `LEAFW + 32` gets `L_{c-1}` from the previous
forest pair (`padE`), for `c = 0` it is zero. -/
theorem step_L (hcode : NewCodeAt im) {c j index : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (lI c))
    (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 LEAFW) :
    ∃ t, Steps im s (if c = 0 then 17 else 23) (if c = 0 then 17 else 23) t ∧ fetch im t = some (.base .ECALL) ∧
      t.pc = pcOf (tI c - 1) ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFW ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 (HEAPW + 16 * (j + 128)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW + 16)) = BitVec.ofNat 64 (leafLo7 c index j) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW + 24)) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFW + 32)) = (padE c 0).eval s ∧
      t.getMem (BitVec.ofNat 64 (LEAFW + 40)) = (padE c 8).eval s ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12] ∧
      Frame s t (fun A => A = LEAFW + 24 ∨ A = LEAFW + 16 ∨ A = LEAFW + 40 ∨ A = LEAFW + 32) := by
  have hx : ∀ a, memEval s [(x29A 24, cE 0), (x29A 16, leafLoE c), (x29A 40, padE c 8), (x29A 32, padE c 0)] a =
      memEval s [mwc (LEAFW + 24) (cE 0), mwc (LEAFW + 16) (leafLoE c), mwc (LEAFW + 40) (padE c 8),
        mwc (LEAFW + 32) (padE c 0)] a := by
    intro a
    simp only [memEval, Addr.eval, x29A, mwc, E.eval, h29, ofNat_add_ofNat]
    rfl
  have hv : ∀ off, off % 8 = 0 → off ≤ 120 → (Oblig.valid (x29A off) 8).holds s := fun off h1 h2 =>
    valid_ofNat (b := .reg .x29) (B := LEAFW) (by simp only [E.eval]; exact h29) (by ao) (by unfold MEMORY_BYTES; ao)
  obtain ⟨hst', hec⟩ := runA_pres (coordLook_ok hcode hc) (runL_eq hc) s hpc (by
    intro o ho
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with ((rfl | rfl | rfl) | ho) | rfl
    · exact hv 24 (by norm_num) (by norm_num)
    · exact hv 16 (by norm_num) (by norm_num)
    · exact hv 40 (by norm_num) (by norm_num)
    · split_ifs at ho with hc0
      · simp at ho
      · simp only [List.mem_singleton] at ho
        subst ho
        simp only [Oblig.holds, Addr.eval, x29A, E.eval, h29, ofNat_add_ofNat]
        intro he
        have hfo : forOff (c - 1) ≤ 288 := by unfold forOff; omega
        have := (ofNat_inj (by ao) (by ao)).mp he
        unfold forOff at this; aoh
    · exact hv 32 (by norm_num) (by norm_num)) (no_br s)
  have ht : ∀ a, ((expL c).toState s).getMem a = memEval s [mwc (LEAFW + 24) (cE 0), mwc (LEAFW + 16) (leafLoE c),
      mwc (LEAFW + 40) (padE c 8), mwc (LEAFW + 32) (padE c 0)] a :=
    fun a => hx a
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]
    show BinOp.eval .add (heapLeafE.eval s) (BitVec.ofNat 64 HEAPW) = _
    rw [eval_heapLeafE s h18]; simp only [BinOp.eval, ofNat_add_ofNat]
    rw [Nat.add_comm]
  · refine (ht _).trans ?_
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    exact eval_leafLoE s h22 h18 hc hj
  · refine (ht _).trans ?_
    rw [memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine (ht _).trans ?_
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
  · refine (ht _).trans ?_
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]
  · refine frame_of_memEval ht _ (fun q hq => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_T (hcode : NewCodeAt im) {c j : Nat} (hc : c < 9) (hj : j < 128) (s : MachineState)
    (hpc : s.pc = pcOf (tI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j) :
    ∃ t k, Steps im s k k t ∧ k ≤ 4 ∧ (j + 1 < 128 → t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 (j + 1)) ∧
      (j + 1 = 128 → t.pc = pcOf (nodeI c) ∧ t.getReg .x18 = BitVec.ofNat 64 127) ∧
      RegsExcept s t [.x6, .x18] ∧ Frame s t (fun _ => False) := by
  have hl := coordLook_ok hcode hc
  by_cases hb : j + 1 < 128
  · obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc true) s hpc (no_obl s) (by
      intro b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      subst hb'
      rw [br_ltu_holds, eval_x18p1 s h18, eval_cE, ofNat_ult (by omega) (by omega)]; simp [hb])
    exact ⟨_, 3, hst', by norm_num, fun _ => ⟨rfl, by rw [pres_getReg]; exact eval_x18p1 s h18⟩,
      fun h => absurd h (by omega), pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
  · obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc false) s hpc (no_obl s) (by
      intro b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      subst hb'
      rw [br_ltu_holds, eval_x18p1 s h18, eval_cE, ofNat_ult (by omega) (by omega)]; simp [hb])
    exact ⟨_, 4, hst', le_rfl, fun h => absurd h hb, fun _ => ⟨rfl, rfl⟩, pres_regsExcept _ _ _ _ _ _ _ s,
      fun A _ _ => rfl⟩
theorem eval_nodeLd (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (off : Nat) :
    (nodeLd off).eval s = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + off)) := by
  show s.getMem (sh5.eval s + BitVec.ofNat 64 (HEAPW + off)) = _
  rw [eval_sh5 s h18, ofNat_add_ofNat]; congr 2; ring
theorem step_N (hcode : NewCodeAt im) {c h index : Nat} (hc : c < 9) (hh1 : 1 ≤ h) (hh : h < 128)
    (s : MachineState) (hpc : s.pc = pcOf (nodeI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 h)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 31) :
    ∃ t, Steps im s 25 28 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ntI c - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODEW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUTW ∧
      t.getMem (BitVec.ofNat 64 NODEW) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 8)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 48)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 56)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32 * h + 24)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 16)) = BitVec.ofNat 64 (nodeLoN c index h) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 24)) = BitVec.ofNat 64 (if 8 ≤ h then 0 else h) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29] ∧
      Frame s t (fun A => A = NODEW + 24 ∨ A = NODEW + 16 ∨ A = NODEW + 56 ∨ A = NODEW + 48 ∨ A = NODEW + 8 ∨
        A = NODEW) := by
  have hb := eval_sh5 s h18
  obtain ⟨hst', hec⟩ := runA_pres2 (coordLook_ok hcode hc) (runN_eq hc) s hpc (by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact ne_ofNat hb (by ao) (by ao) (by ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)) (no_br s)
  have m : ∀ A, A < 2 ^ 64 → ((expN c).toState s).getMem (BitVec.ofNat 64 A) =
      memEval s (expN c).st.mem (BitVec.ofNat 64 A) := fun A _ => rfl
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, pres2_regsExcept _ _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres2_getMem]; simp only [memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 24 < 2 ^ 64 by ao)
      (by ao), memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 16 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 56 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 48 < 2 ^ 64 by ao) (by ao),
      memEval_mwc_ne _ _ _ (show NODEW < 2 ^ 64 by ao) (show NODEW + 8 < 2 ^ 64 by ao) (by ao)]
    rw [memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18, Nat.add_zero]
  · rw [pres2_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres2_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres2_getMem]
    rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao), eval_nodeLd s h18]
  · rw [pres2_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]
    exact eval_nodeLoNE s h22 h18 hc hidx hh
  · rw [pres2_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_nodeHiE s h18 hh
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expN, pres2, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
/-- Nested FTS (r1-1): the fold output half kept for heap `h` (HIGH half for heaps 2 and 3). -/
def hiOff (h : Nat) : Nat := if h < 4 then 16 else 0
/-- Cycles of the fold post-hash block (nested FTS r1-1). -/
def ntC (c h : Nat) : Nat := if c = 0 then 18 else if h = 4 ∨ h = 2 then 25 else 22
/-- The fold pad word `NODEW + 32 + off` after the post-hash block of heap `h` (nested FTS r1-1): `R_{c-1}` after
heap 4, zero after heap 2 (coordinates `c >= 1`), unchanged otherwise. -/
def ntPad (c h off : Nat) (s : MachineState) : Word :=
  if 1 ≤ c ∧ h = 4 then s.getMem (BitVec.ofNat 64 (FORW + forOff (c - 1) + 16 + off))
  else if 1 ≤ c ∧ h = 2 then 0 else s.getMem (BitVec.ofNat 64 (NODEW + 32 + off))
theorem eval_hiSelE (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (hh : h < 128) :
    hiSelE.eval s = BitVec.ofNat 64 (hiOff h) := by
  show BinOp.eval .sll (BinOp.eval .sltu (s.getReg .x18) (BitVec.ofNat 64 4)) (BitVec.ofNat 64 4) = _
  rw [h18]
  unfold hiOff
  simp only [BinOp.eval, ofNat_ult (show h < 2 ^ 64 by omega) (show 4 < 2 ^ 64 by norm_num)]
  by_cases h4 : h < 4 <;> simp [h4] <;> rfl
theorem step_NT (hcode : NewCodeAt im) {c h : Nat} (hc : c < 9) (hh1 : 2 ≤ h) (hh : h < 128) (s : MachineState)
    (hpc : s.pc = pcOf (ntI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s (ntC c h) (ntC c h) t ∧ (3 ≤ h → t.pc = pcOf (nodeI c)) ∧ (h = 2 → t.pc = pcOf (rI c)) ∧
      t.getReg .x18 = BitVec.ofNat 64 (h - 1) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h)) = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h)) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h + 8)) = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 32)) = ntPad c h 0 s ∧
      t.getMem (BitVec.ofNat 64 (NODEW + 40)) = ntPad c h 8 s ∧
      RegsExcept s t [.x6, .x7, .x18, .x28, .x29] ∧
      Frame s t (fun A => A = HEAPW + 16 * h + 8 ∨ A = HEAPW + 16 * h ∨ A = NODEW + 32 ∨ A = NODEW + 40) := by
  have hl := coordLook_ok hcode hc
  have hb := eval_sh4 s h18
  have hm1 := eval_x18m1 s h18 (by omega) (by omega)
  have hsel := eval_hiSelE s h18 hh
  have hho : hiOff h ≤ 16 := by unfold hiOff; split_ifs <;> omega
  have hea : ∀ off, Addr.eval s (heapAddr off) = BitVec.ofNat 64 (HEAPW + 16 * h + off) := by
    intro off
    show sh4.eval s + BitVec.ofNat 64 (HEAPW + off) = _
    rw [hb, ofNat_add_ofNat]; congr 1; ring
  have hout : ∀ off, (outLd off).eval s = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h + off)) := by
    intro off
    show s.getMem (hiSelE.eval s + BitVec.ofNat 64 (NOUTW + off)) = _
    rw [hsel, ofNat_add_ofNat]; congr 2; ring
  have hfo : ∀ c', c' < 9 → forOff c' ≤ 288 := fun c' hc' => by unfold forOff; omega
  -- one symbolic result covers each (kind, direction) pair; the caller picks the consistent ones
  have post : ∀ (kd : Nat) (b : Bool), (b = true ↔ 3 ≤ h) →
      (1 ≤ c → (kd = 1 ↔ h = 4) ∧ (kd = 2 ↔ h = 2) ∧ kd < 3) →
      runNT c kd b = some (expNT c kd b) →
      ∃ t, Steps im s (if c = 0 then 18 else if kd = 0 then 22 else 25)
          (if c = 0 then 18 else if kd = 0 then 22 else 25) t ∧ t.pc = pcOf (if b then nodeI c else rI c) ∧
        t.getReg .x18 = BitVec.ofNat 64 (h - 1) ∧
        t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h)) = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h)) ∧
        t.getMem (BitVec.ofNat 64 (HEAPW + 16 * h + 8)) = s.getMem (BitVec.ofNat 64 (NOUTW + hiOff h + 8)) ∧
        t.getMem (BitVec.ofNat 64 (NODEW + 32)) = ntPad c h 0 s ∧
        t.getMem (BitVec.ofNat 64 (NODEW + 40)) = ntPad c h 8 s ∧
        RegsExcept s t [.x6, .x7, .x18, .x28, .x29] ∧
        Frame s t (fun A => A = HEAPW + 16 * h + 8 ∨ A = HEAPW + 16 * h ∨ A = NODEW + 32 ∨ A = NODEW + 40) := by
    intro kd b hbh hkd hrun
    have hva : ∀ off, off = 0 ∨ off = 8 → (Oblig.valid (outAddr off) 8).holds s := fun off hoff =>
      valid_ofNat hsel (by unfold hiOff at *; split_ifs <;> rcases hoff with rfl | rfl <;> ao)
        (by unfold MEMORY_BYTES; rcases hoff with rfl | rfl <;> ao)
    have hne : ∀ off K, off ≤ 8 → (K = NODEW + 32 ∨ K = NODEW + 40) →
        (Oblig.ne (outAddr off) ⟨none, BitVec.ofNat 64 K⟩).holds s := fun off K hoff hK =>
      ne_ofNat hsel (by ao) (by rcases hK with rfl | rfl <;> ao) (by rcases hK with rfl | rfl <;> ao)
    obtain ⟨hst', -⟩ := runA_pres hl hrun s hpc (by
      intro o ho
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with (rfl | rfl) | ho
      · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
      · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
      · unfold ntOutObl at ho
        split_ifs at ho
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl
          · exact hva 8 (Or.inr rfl)
          · exact hva 0 (Or.inl rfl)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hne 8 _ (by norm_num) (Or.inl rfl)
          · exact hne 8 _ (by norm_num) (Or.inr rfl)
          · exact hva 8 (Or.inr rfl)
          · exact hne 0 _ (by norm_num) (Or.inl rfl)
          · exact hne 0 _ (by norm_num) (Or.inr rfl)
          · exact hva 0 (Or.inl rfl)) (by
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · rw [br_ne_holds, hm1, eval_cE, ofNat_bne (by omega) (by norm_num)]
        cases b <;> simp_all <;> omega
      · unfold ntBrs at hq
        have e4 : ∀ d, Br.holds s ⟨.ne, .reg .x18, cE 4, d⟩ ↔ (decide (h ≠ 4) = d) := fun d => by
          rw [br_ne_holds]; simp only [E.eval, h18, eval_cE]; rw [ofNat_bne (by omega) (by norm_num)]
        have e2 : ∀ d, Br.holds s ⟨.ne, .reg .x18, cE 2, d⟩ ↔ (decide (h ≠ 2) = d) := fun d => by
          rw [br_ne_holds]; simp only [E.eval, h18, eval_cE]; rw [ofNat_bne (by omega) (by norm_num)]
        split_ifs at hq with c0 k1 k2
        · simp at hq
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq
          rw [e4]; have := (hkd (by omega)).1.mp k1; simp [this]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          have := (hkd (by omega)).2.1.mp k2
          rcases hq with rfl | rfl
          · rw [e2]; simp [this]
          · rw [e4]; simp [this]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          have hk := hkd (by omega)
          have n4 : h ≠ 4 := fun e => k1 (hk.1.mpr e)
          have n2 : h ≠ 2 := fun e => k2 (hk.2.1.mpr e)
          rcases hq with rfl | rfl
          · rw [e2]; simp [n2]
          · rw [e4]; simp [n4])
    have hpad0 : memEval s (ntPadMem c kd) (BitVec.ofNat 64 (NODEW + 32)) = ntPad c h 0 s := by
      simp only [ntPad, Nat.add_zero]
      by_cases c0 : c = 0
      · have n4 : ¬ (1 ≤ c ∧ h = 4) := fun h' => by omega
        have n2 : ¬ (1 ≤ c ∧ h = 2) := fun h' => by omega
        simp only [ntPadMem, if_pos c0, if_neg n4, if_neg n2]; rfl
      have hk := hkd (by omega)
      by_cases k1 : kd = 1
      · have p4 : 1 ≤ c ∧ h = 4 := ⟨by omega, hk.1.mp k1⟩
        simp only [ntPadMem, if_neg c0, if_pos k1, if_pos p4]
        rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
      · have n4 : ¬ (1 ≤ c ∧ h = 4) := fun h' => k1 (hk.1.mpr h'.2)
        by_cases k2 : kd = 2
        · have p2 : 1 ≤ c ∧ h = 2 := ⟨by omega, hk.2.1.mp k2⟩
          simp only [ntPadMem, if_neg c0, if_neg k1, if_pos k2, if_neg n4, if_pos p2]
          rw [memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
        · have n2 : ¬ (1 ≤ c ∧ h = 2) := fun h' => k2 (hk.2.1.mpr h'.2)
          simp only [ntPadMem, if_neg c0, if_neg k1, if_neg k2, if_neg n4, if_neg n2]; rfl
    have hpad8 : memEval s (ntPadMem c kd) (BitVec.ofNat 64 (NODEW + 40)) = ntPad c h 8 s := by
      simp only [ntPad]
      by_cases c0 : c = 0
      · have n4 : ¬ (1 ≤ c ∧ h = 4) := fun h' => by omega
        have n2 : ¬ (1 ≤ c ∧ h = 2) := fun h' => by omega
        simp only [ntPadMem, if_pos c0, if_neg n4, if_neg n2]; rfl
      have hk := hkd (by omega)
      by_cases k1 : kd = 1
      · have p4 : 1 ≤ c ∧ h = 4 := ⟨by omega, hk.1.mp k1⟩
        simp only [ntPadMem, if_neg c0, if_pos k1, if_pos p4]
        rw [memEval_mwc_self _ _ _ _ (by ao), show FORW + forOff (c - 1) + 16 + 8 = FORW + forOff (c - 1) + 24 by omega]
        rfl
      · have n4 : ¬ (1 ≤ c ∧ h = 4) := fun h' => k1 (hk.1.mpr h'.2)
        by_cases k2 : kd = 2
        · have p2 : 1 ≤ c ∧ h = 2 := ⟨by omega, hk.2.1.mp k2⟩
          simp only [ntPadMem, if_neg c0, if_neg k1, if_pos k2, if_neg n4, if_pos p2]
          rw [memEval_mwc_self _ _ _ _ (by ao)]; rfl
        · have n2 : ¬ (1 ≤ c ∧ h = 2) := fun h' => k2 (hk.2.1.mpr h'.2)
          simp only [ntPadMem, if_neg c0, if_neg k1, if_neg k2, if_neg n4, if_neg n2]; rfl
    have hmem : ∀ A, A < 2 ^ 64 → A ≠ HEAPW + 16 * h + 8 → A ≠ HEAPW + 16 * h →
        memEval s ((heapAddr 8, outLd 8) :: (heapAddr 0, outLd 0) :: ntPadMem c kd) (BitVec.ofNat 64 A) =
          memEval s (ntPadMem c kd) (BitVec.ofNat 64 A) := by
      intro A hA h1 h2
      rw [memEval_cons, memEval_cons, hea, hea, if_neg (fun he => h1 ((ofNat_inj hA (by ao)).mp he)),
        if_neg (fun he => h2 (by rw [(ofNat_inj hA (by ao)).mp he, Nat.add_zero]))]
    refine ⟨_, hst', rfl, by rw [pres_getReg]; exact hm1, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
    · rw [pres_getMem]
      show memEval s ((heapAddr 8, outLd 8) :: (heapAddr 0, outLd 0) :: ntPadMem c kd) _ = _
      rw [memEval_cons, memEval_cons, hea, hea, if_neg (by
        intro he; have := (ofNat_inj (by ao) (by ao)).mp he; omega), if_pos (by rw [Nat.add_zero])]
      rw [hout 0, Nat.add_zero]
    · rw [pres_getMem]
      show memEval s ((heapAddr 8, outLd 8) :: (heapAddr 0, outLd 0) :: ntPadMem c kd) _ = _
      rw [memEval_cons, hea, if_pos rfl, hout 8]
    · rw [pres_getMem]; exact (hmem _ (by ao) (by ao) (by ao)).trans hpad0
    · rw [pres_getMem]; exact (hmem _ (by ao) (by ao) (by ao)).trans hpad8
    · intro A hA hn
      simp only [not_or] at hn
      rw [pres_getMem]
      show memEval s ((heapAddr 8, outLd 8) :: (heapAddr 0, outLd 0) :: ntPadMem c kd) _ = _
      rw [hmem A hA hn.1 hn.2.1]
      unfold ntPadMem
      split_ifs
      · rfl
      · rw [memEval_mwc_ne _ _ _ hA (by ao) hn.2.2.2, memEval_mwc_ne _ _ _ hA (by ao) hn.2.2.1]; rfl
      · rw [memEval_mwc_ne _ _ _ hA (by ao) hn.2.2.2, memEval_mwc_ne _ _ _ hA (by ao) hn.2.2.1]; rfl
      · rfl
  have hC : ∀ kd, (1 ≤ c → (kd = 1 ↔ h = 4) ∧ (kd = 2 ↔ h = 2) ∧ kd < 3) →
      (if c = 0 then 18 else if kd = 0 then 22 else 25) = ntC c h := by
    intro kd hk
    unfold ntC
    by_cases c0 : c = 0
    · simp [c0]
    · have := hk (by omega)
      simp only [c0, if_false]
      by_cases k0 : kd = 0
      · subst k0; simp only [if_true]; rw [if_neg (by omega)]
      · rw [if_neg k0, if_pos (by omega)]
  obtain ⟨kd, b, hbh, hk, hrun⟩ : ∃ kd b, (b = true ↔ 3 ≤ h) ∧
      (1 ≤ c → (kd = 1 ↔ h = 4) ∧ (kd = 2 ↔ h = 2) ∧ kd < 3) ∧ runNT c kd b = some (expNT c kd b) := by
    by_cases c0 : c = 0
    · subst c0
      by_cases h3 : 3 ≤ h
      · exact ⟨0, true, by simp [h3], fun h' => absurd h' (by norm_num), runNT_eq0 hc⟩
      · exact ⟨0, false, by simp [h3], fun h' => absurd h' (by norm_num), runNT_eqX hc⟩
    · by_cases e4 : h = 4
      · exact ⟨1, true, by simp; omega, fun _ => ⟨by simp [e4], by simp; omega, by norm_num⟩, runNT_eq1 hc⟩
      · by_cases e2 : h = 2
        · have := runNT_eqX hc; rw [if_neg c0] at this
          exact ⟨2, false, by simp; omega, fun _ => ⟨by simp; omega, by simp [e2], by norm_num⟩, this⟩
        · exact ⟨0, true, by simp; omega, fun _ => ⟨by simp; omega, by simp; omega, by norm_num⟩, runNT_eq0 hc⟩
  obtain ⟨t, h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩ := post kd b hbh hk hrun
  rw [hC kd hk] at h1'
  refine ⟨t, h1', fun h3 => ?_, fun h2 => ?_, h3', h4', h5', h6', h7', h8', h9'⟩
  · rw [h2', if_pos (hbh.mpr h3)]
  · rw [h2', if_neg (fun hb' => by have := hbh.mp hb'; omega)]
theorem step_R0 (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (rI c)) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf (pcI c 0) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c)) = s.getMem (BitVec.ofNat 64 (HEAPW + 32)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 8)) = s.getMem (BitVec.ofNat 64 (HEAPW + 40)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 16)) = s.getMem (BitVec.ofNat 64 (HEAPW + 48)) ∧
      t.getMem (BitVec.ofNat 64 (FORW + forOff c + 24)) = s.getMem (BitVec.ofNat 64 (HEAPW + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = FORW + forOff c + 24 ∨ A = FORW + forOff c + 16 ∨ A = FORW + forOff c + 8 ∨
        A = FORW + forOff c) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runR0_eq hc) s hpc (no_obl s) (no_br s)
  have hfo : forOff c ≤ 288 := by unfold forOff; omega
  refine ⟨_, hst', rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expR0, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem eval_pathLd (s : MachineState) {sel : Nat} (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (hsel : sel < 128)
    {l : Nat} (hl : l < 7) (off : Nat) :
    (pathLd l off).eval s = s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)) + off)) := by
  show s.getMem ((pathE l).eval s + BitVec.ofNat 64 (HEAPW + off)) = _
  rw [eval_pathE s h24 hsel l hl, ofNat_add_ofNat]; congr 2; ring
set_option maxRecDepth 100000 in
theorem pathHeap_lt_all : ∀ sel, sel < 128 → ∀ l, l < 7 → 2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1) < 256 := by
  decide +kernel
theorem pathHeap_lt (sel l : Nat) (hsel : sel < 128) (hl : l < 7) :
    2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1) < 256 := pathHeap_lt_all sel hsel l hl
theorem step_PC (hcode : NewCodeAt im) {c l sel : Nat} (hc : c < 9) (hl : l < 7) (hsel : sel < 128) (s : MachineState)
    (hpc : s.pc = pcOf (pcI c l)) (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf (pcI c (l + 1)) ∧
      t.getMem (BitVec.ofNat 64 (slotP c l)) =
        s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)))) ∧
      t.getMem (BitVec.ofNat 64 (slotP c l + 8)) =
        s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun A => A = slotP c l + 8 ∨ A = slotP c l) := by
  have hb := eval_pathE s h24 hsel l hl
  have hlt := pathHeap_lt sel l hsel hl
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runPC_eq hc hl) s hpc (by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES; ao)) (no_br s)
  refine ⟨_, hst', rfl, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao),
      eval_pathLd s h24 hsel hl, Nat.add_zero]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao), eval_pathLd s h24 hsel hl]
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expPC, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
/-- Nested FTS (r1-1): the forest hash is replaced by copying the last top pair `(L8, R8)` (forest-buffer slot 8) to
`FOUT` (the L3 message, copied to the encoding block at 370) and to the encoding R slot `0x20290`. -/
theorem step_For (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 20715) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 370 ∧
      t.getMem (BitVec.ofNat 64 FOUT) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8)) ∧
      t.getMem (BitVec.ofNat 64 (FOUT + 8)) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 8)) ∧
      t.getMem (BitVec.ofNat 64 0x20290) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 16)) ∧
      t.getMem (BitVec.ofNat 64 (0x20290 + 8)) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = 0x20290 + 8 ∨ A = 0x20290 ∨ A = FOUT + 8 ∨ A = FOUT) := by
  obtain ⟨hst', -⟩ := run_pres (forLook_ok hcode) runFor_eq s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expFor, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_J (hcode : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 20729) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 370 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst', -⟩ := run_pres (tailLook_ok hcode) runJ_eq s hpc (no_obl s) (no_br s)
  exact ⟨_, hst', rfl, pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
end pieces
end ClaudeWCT.W9.Machine.Sign
end
section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest header pad64 privateInput zero16)
open SphincsSecurity (bytesLE bytesLE_length)
theorem readWords_of_getD (t : MachineState) (A : Nat) :
    ∀ (m : Nat) (l : List Word), l.length = m →
      (∀ j < m, t.getMem (BitVec.ofNat 64 (A + 8 * j)) = l.getD j 0) → t.readWords (BitVec.ofNat 64 A) m = l
  | 0, l, hl, _ => by rw [List.length_eq_zero_iff] at hl; subst hl; rfl
  | m + 1, l, hl, h => by
    obtain ⟨l', d, rfl⟩ : ∃ l' d, l = l' ++ [d] := ⟨l.dropLast, l.getLast (by
      intro he; subst he; simp at hl), (List.dropLast_append_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    rw [readWords_add, readWords_of_getD t A m l' hl (fun j hj => by
      rw [h j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hj)]),
      readWords_one, h m (by omega)]
    simp [List.getD_eq_getElem?_getD, hl]
theorem hashInput_of_words (t : MachineState) (l : List UInt8) (n A : Nat) (hl : l.length = 64 * (n + 1))
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 * (n + 1) < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1)))
    (hw : ∀ j < 8 * (n + 1), t.getMem (BitVec.ofNat 64 (A + 8 * j)) = (wordsOf l).getD j 0) :
    hashInput t = toQ l :=
  hashInput_toQ t l n A hl h10 hA (by omega) h11 (by omega)
    (readWords_of_getD t A _ _ (length_wordsOf _ _ (by rw [hl]; ring)) hw)
theorem header_words (tag lay tree pos idx : Nat) (ht : ¬ SigGolfCandidate.T3.packedNodeTag tag) (htag : tag < 256)
    (hlay : lay < 256) (htree : tree < 2 ^ 32) (hpos : pos < 2 ^ 32) (hidx : idx < 2 ^ 32) :
    wordsOf (bytesLE 16 (header tag lay tree pos idx)) =
      [BitVec.ofNat 64 (1 + 256 * tag + 65536 * lay + 2 ^ 32 * pos), BitVec.ofNat 64 (tree + 2 ^ 32 * idx)] := by
  rw [wordsOf_header, if_neg ht, if_neg ht, hdr0_eq tag lay tree pos htag hlay htree hpos, hdr1_eq tree idx htree hidx]
theorem wordsOf_priv (sk : BitVec 256) (c index q : Nat) (hc : c < 256) (hidx : index < 2 ^ 32) (hq : q < 2 ^ 32) :
    wordsOf (privateInput sk (.inl (header 8 c index 0 q))) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, BitVec.ofNat 64 (hdr8 c), BitVec.ofNat 64 (index + 2 ^ 32 * q),
        sk.extractLsb' 128 64, sk.extractLsb' 192 64, 0, 0] := by
  rw [wordsOf_privateInput_tweak, header_lo, header_hi, if_neg (by decide), if_neg (by decide),
    hdr0_eq 8 c index 0 (by norm_num) hc hidx (by norm_num), hdr1_eq index q hidx hq]
  simp only [hdr8]; congr 3
theorem chainInput_len (index c j i st : Nat) (v : Digest) : (WCT9.chainInput index c j i st v).length = 64 := by
  simp only [WCT9.chainInput, zero16, List.length_append, bytesLE_length, List.length_replicate]
theorem ftsChainLow_eq (index c j i st : Nat) (hc : c < 9) (hidx : index < 2 ^ 31) (hst : st < 4) (hi : i < 6)
    (hj : j < 128) : WCT9.ftsChainLow index c j i st = chainW0 c i j index st := by
  unfold WCT9.ftsChainLow chainW0 chainK
  rw [Nat.mod_eq_of_lt (show i < 8 by omega), Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt (show c < 16 by omega),
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hidx]
  ring
theorem wordsOf_chain (index c j i st : Nat) (v : Digest) (hc : c < 9) (hidx : index < 2 ^ 31) (hst : st < 4)
    (hi : i < 6) (hj : j < 128) :
    wordsOf (pad64 (WCT9.chainInput index c j i st v)) =
      [0, 0, BitVec.ofNat 64 (chainW0 c i j index st), 0, 0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_len]), WCT9.chainInput_eq,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_zero16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  unfold WCT9.ftsChainHeader
  rw [WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high, ftsChainLow_eq index c j i st hc hidx hst hi hj]
  rfl
/-- FTS leaf input with the pad slot (nested FTS r1-1: `L_{c-1}`, zero for coordinate 0). -/
def leafIn (index c j : Nat) (pad : Digest) (ends : List Digest) : List UInt8 :=
  bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (WCT9.ftsLeafHeader index c j) ++ bytesLE 16 pad ++
    (ends.drop 1).flatMap (bytesLE 16)
theorem leafHashP_eq (index c j : Nat) (pad : Digest) (ends : List Digest) :
    WCT9.leafHashP index c j pad ends = SigGolfCandidate.T3.shortHash (leafIn index c j pad ends) := rfl
/-- C1: the paired leaf of heap `heap` hashes the same input; its half follows `ftsHighHeap heap`. -/
theorem leafHashH_eq' (heap index c j : Nat) (pad : Digest) (ends : List Digest) :
    WCT9.leafHashH heap index c j pad ends = WCT9.ftsHash heap (leafIn index c j pad ends) := rfl
theorem leafIn_len (index c j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) :
    (leafIn index c j pad ends).length = 128 := by
  have : ((ends.drop 1).flatMap (bytesLE 16)).length = 80 := by
    rw [List.length_flatMap]; simp [bytesLE_length, h]
  simp only [leafIn, List.length_append, bytesLE_length, this]
theorem ftsLeafHeader_words (index c j : Nat) (hc : c < 9) (hidx : index < 2 ^ 31) (hj : j < 128) :
    wordsOf (bytesLE 16 (WCT9.ftsLeafHeader index c j)) = [BitVec.ofNat 64 (leafLo7 c index j), 0] := by
  rw [wordsOf_bytesLE16]
  unfold WCT9.ftsLeafHeader
  rw [SigGolfCandidate.T3.append64_low]
  congr 1
  · unfold WCT9.ftsLeafLow leafLo7
    congr 1
    rw [Nat.mod_eq_of_lt (show c < 16 by omega), Nat.mod_eq_of_lt (show j < 128 from hj), Nat.mod_eq_of_lt hidx]
    ring
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, SigGolfCandidate.T3.append64_toNat]
    have := (BitVec.ofNat 64 (WCT9.ftsLeafLow index c j)).isLt
    have h0' : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0']
    omega
theorem wordsOf_leaf (index c j : Nat) (pad : Digest) (ends : List Digest) (h : ends.length = 6) (hc : c < 9)
    (hidx : index < 2 ^ 31) (hj : j < 128) :
    wordsOf (pad64 (leafIn index c j pad ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++ [BitVec.ofNat 64 (leafLo7 c index j), 0] ++
        [pad.extractLsb' 0 64, pad.extractLsb' 64 64] ++
        (ends.drop 1).flatMap fun d => [d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [leafIn_len _ _ _ _ _ h]), leafIn,
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]),
    ftsLeafHeader_words index c j hc hidx hj, wordsOf_bytesLE16 pad, wordsOf_flatMap16]
/-- FTS node input with the pad slot (nested FTS r1-1: `R_{c-1}` for heaps 2 and 3, zero otherwise). -/
def nodeIn (c index h : Nat) (pad L R : Digest) : List UInt8 :=
  bytesLE 16 L ++ bytesLE 16 (WCT9.wctNodeHeader c index h) ++ bytesLE 16 pad ++ bytesLE 16 R
theorem nodeHash_eq (c index h : Nat) (L R : Digest) :
    WCT9.wctNodeHash c index h L R = SigGolfCandidate.T3.shortHash (nodeIn c index h 0 L R) := by
  unfold nodeIn; rw [WCT9.bytesLE_zero16]; rfl
/-- C1: the paired node of heap `h ≥ 8` hashes the same input as the legacy node; its half follows `ftsHighHeap h`. -/
theorem nodeHashH_eq (c index h : Nat) (L R : Digest) :
    WCT9.wctNodeHashH c index h L R = WCT9.ftsHash h (nodeIn c index h 0 L R) := by
  unfold nodeIn WCT9.wctNodeHashH; rw [WCT9.bytesLE_zero16]
theorem topHash_eq (c index h : Nat) (L pad R : Digest) :
    WCT9.wctTopHash c index h L pad R =
      (SigGolfCandidate.T3.publicHash (nodeIn c index h pad L R) >>= fun o => pure (o.extractLsb' 128 128)) := rfl
theorem nodeIn_len (c index h : Nat) (pad L R : Digest) : (nodeIn c index h pad L R).length = 64 := by
  simp only [nodeIn, List.length_append, bytesLE_length]
theorem hdr0_node (c index : Nat) (hc : c < 9) (hidx : index < 2 ^ 32) :
    hdr0 3 (4 + c) index index = nodeK c + 2 ^ 32 * index := by
  unfold hdr0 nodeK
  rw [Nat.mod_eq_of_lt (show 3 < 256 by norm_num), Nat.mod_eq_of_lt (show 4 + c < 256 by omega),
    Nat.div_eq_of_lt hidx, Nat.mod_eq_of_lt hidx]
  ring
theorem wordsOf_node (c index h : Nat) (pad L R : Digest) (hc : c < 9) (hidx : index < 2 ^ 31) (hh : h < 128) :
    wordsOf (pad64 (nodeIn c index h pad L R)) =
      [L.extractLsb' 0 64, L.extractLsb' 64 64, BitVec.ofNat 64 (nodeLoN c index h),
        BitVec.ofNat 64 (if 8 ≤ h then 0 else h), pad.extractLsb' 0 64, pad.extractLsb' 64 64,
        R.extractLsb' 0 64, R.extractLsb' 64 64] := by
  have hlo : (WCT9.wctNodeHeader c index h).extractLsb' 0 64 = BitVec.ofNat 64 (nodeLoN c index h) := by
    rw [WCT9.wctNodeHeader_low hc]
    unfold nodeLoN
    by_cases h8 : 8 ≤ h
    · rw [if_pos (show SigGolfCandidate.T3.FtsNew h from ⟨h8, hh⟩), if_pos h8]
      unfold nodeLo7 WCT9.ftsNodeLowN
      rw [Nat.mod_eq_of_lt (show c < 16 by omega), Nat.mod_eq_of_lt hidx]
      congr 1; omega
    · rw [if_neg (show ¬ SigGolfCandidate.T3.FtsNew h from fun h' => h8 h'.1), if_neg h8]
      unfold nodeLo7 WCT9.ftsLeafLow
      rw [Nat.mod_eq_of_lt (show c < 16 by omega), Nat.mod_eq_of_lt hidx]
      congr 1; omega
  have hhi : (WCT9.wctNodeHeader c index h).extractLsb' 64 64 = BitVec.ofNat 64 (if 8 ≤ h then 0 else h) := by
    rw [WCT9.wctNodeHeader_high hc]
    by_cases h8 : 8 ≤ h
    · rw [if_pos (show SigGolfCandidate.T3.FtsNew h from ⟨h8, hh⟩), if_pos h8]
    · rw [if_neg (show ¬ SigGolfCandidate.T3.FtsNew h from fun h' => h8 h'.1), if_neg h8]
  rw [pad64_of_aligned _ (by rw [nodeIn_len]), nodeIn,
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16,
    wordsOf_bytesLE16, hlo, hhi]
  rfl
theorem forestPk_eq (index : Nat) (pairs : List (Digest × Digest)) :
    WCT9.forestPk index pairs = SigGolfCandidate.T3.shortHash (WCT9.forestInput index pairs) := rfl
def pairWords (p : Digest × Digest) : List Word :=
  [p.1.extractLsb' 0 64, p.1.extractLsb' 64 64, p.2.extractLsb' 0 64, p.2.extractLsb' 64 64]
theorem wordsOf_pairs (ps : List (Digest × Digest)) :
    wordsOf (ps.flatMap fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) = ps.flatMap pairWords := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by simp [bytesLE_length]),
      wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, ih]
    rfl
theorem pairs_bytes_len (ps : List (Digest × Digest)) :
    (ps.flatMap fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2).length = 32 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_append, bytesLE_length, bytesLE_length,
      List.length_cons]
    ring
theorem forestIn_len (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (WCT9.forestInput index pairs).length = 320 := by
  simp only [WCT9.forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length, pairs_bytes_len, h]
theorem wordsOf_forest (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9)
    (hidx : index < 2 ^ 32) :
    wordsOf (pad64 (WCT9.forestInput index pairs)) =
      [0, 0, BitVec.ofNat 64 3841, BitVec.ofNat 64 index] ++ pairs.flatMap pairWords := by
  rw [pad64_of_aligned _ (by rw [forestIn_len _ _ h]), WCT9.forestInput,
    wordsOf_append _ _ (by simp [zero16, bytesLE_length]), wordsOf_append _ _ (by simp [zero16, bytesLE_length]),
    wordsOf_zero16, header_words 15 0 index 0 0 (by decide) (by norm_num) (by norm_num) hidx (by norm_num)
      (by norm_num), wordsOf_pairs]
  rfl
end ClaudeWCT.W9.Machine.Sign
end
section
set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
open SphincsSecurity (bytesLE bytesLE_length)
def chainRest (index c j i d : Nat) : Nat → List Digest → M (Digest × Digest)
  | 0, L => pure (L.getD (4 - d) 0, L.getD 4 0)
  | r + 1, L => shortHash (WCT9.chainInput index c j i (3 - r) (L.getD (3 - r) 0)) >>= fun v =>
      chainRest index c j i d r (L ++ [v])
theorem chain4_eq (index c j i d : Nat) (hd : d ≤ 4) (seed : Digest) :
    (WCT9.chain index c j i 0 (4 - d) seed >>= fun value =>
      WCT9.chain index c j i (4 - d) d value >>= fun last => pure (value, last)) =
      chainRest index c j i d 4 [seed] := by
  interval_cases d <;>
    simp only [WCT9.chain, chainRest, show List.range' 0 4 = [0, 1, 2, 3] from rfl,
      show List.range' 0 3 = [0, 1, 2] from rfl,
      show List.range' 0 2 = [0, 1] from rfl, show List.range' 0 1 = [0] from rfl,
      show List.range' 0 0 = [] from rfl, show List.range' 4 0 = [] from rfl, show List.range' 3 1 = [3] from rfl,
      show List.range' 2 2 = [2, 3] from rfl, show List.range' 1 3 = [1, 2, 3] from rfl, List.foldlM_cons,
      List.foldlM_nil, bind_assoc, pure_bind, Nat.sub_self, Nat.sub_zero] <;> rfl
def chainW (c i : Nat) (A : Nat) : Prop :=
  (CHAINW + 16 ≤ A ∧ A < CHAINW + 32) ∨ (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) ∨ A = LEAFW + leafOff i ∨
    A = LEAFW + leafOff i + 8 ∨ A = slotV c i ∨ A = slotV c i + 8
def chainRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x26, .x28, .x29]
structure ChkSt (c i j index sel w d r : Nat) (L : List Digest) (s0 t : MachineState) : Prop where
  pc : t.pc = pcOf (chkI c i (4 - r))
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 j
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  x24 : t.getReg .x24 = BitVec.ofNat 64 sel
  x25 : t.getReg .x25 = BitVec.ofNat 64 w
  x26 : t.getReg .x26 = BitVec.ofNat 64 (4 - d)
  len : L.length = 5 - r
  val : DigAt t (CHAINW + 48) (L.getD (4 - r) 0)
  h16 : t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (4 - r - 1))
  h24 : t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0
  z0 : t.getMem (BitVec.ofNat 64 CHAINW) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAINW + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAINW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAINW + 40)) = 0
  op : j = sel → 4 - d < 4 - r → DigAt t (slotV c i) (L.getD (4 - d) 0)
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (chainW c i)
  nosel : j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
    t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)
def ChainPost (c i j sel : Nat) (s0 : MachineState) (r : Digest × Digest) (t : MachineState) : Prop :=
  t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) r.2 ∧ (j = sel → DigAt t (slotV c i) r.1) ∧
    RegsExcept s0 t chainRegs ∧ Frame s0 t (chainW c i) ∧
    (j ≠ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 6 →
      t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)) ∧
    t.getReg .x29 = BitVec.ofNat 64 LEAFW
theorem chkI_pos : ∀ c, c < 9 → ∀ i, i < 6 → ∀ st, st < 5 → 1 ≤ chkI c i st := by decide +kernel
theorem blocks64 (l : List UInt8) (hl : l.length = 64) : (toQ (pad64 l)).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; norm_num, by rw [hl]⟩, hl]
theorem pcOf_pred4 (n : Nat) (hn : 1 ≤ n) : pcOf (n - 1) + 4 = pcOf n := by
  rw [pcOf_add4, Nat.sub_add_cancel hn]
theorem DigAt.frame' {s t : MachineState} {W : Nat → Prop} {A : Nat} {d : Digest} (h : DigAt s A d)
    (hf : Frame s t W) (hA : A + 8 < 2 ^ 64) (h0 : ¬ W A) (h1 : ¬ W (A + 8)) : DigAt t A d :=
  h.frame hf hA h0 h1
section chain
variable {im : Image} {sk : BitVec 256}
theorem chain_from (hcode : NewCodeAt im) {c i j index sel w d : Nat} (hc : c < 9) (hi : i < 6) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hd : d ≤ 4) {s0 : MachineState} :
    ∀ r, r ≤ 4 → ∀ (L : List Digest) (t : MachineState), ChkSt c i j index sel w d r L s0 t →
      TBSim im sk t (11 + 28 * r + 8) (chainRest index c j i d r L) (ChainPost c i j sel s0) := by
  intro r
  induction r with
  | zero =>
    intro _ L t h
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by norm_num : 4 < 5) t h.pc h.x18 h.x24 h.x26 (by omega) (by omega) (by omega) h.val
    obtain ⟨t2, s2, p2, l2, x29_2, r2, f2⟩ := step_Lc hcode hc hi t1 p1 (h.val.frame f1 (by ao) (by ao) (by ao))
    have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
    refine (TBSim.pure_steps' (s1.trans s2) ⟨p2, l2, fun hjs => ?_, ?_, ?_, ?_, x29_2⟩).mono (by omega)
      (fun _ _ h => h)
    · by_cases hd0 : d = 0
      · subst hd0
        have := o1 hjs rfl
        exact this.frame f2 (by ao) (by ao) (by ao)
      · have := h.op hjs (by omega)
        exact (this.frame (n1 (fun h' => hd0 (by omega))) (by ao) (fun h => h) (fun h => h)).frame f2
          (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact ((h.regs.trans r1).trans r2).mono (by simp [chainRegs])
    · refine ((h.frame.trans f1).trans f2).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with (hA | hA) | hA <;> [exact hA; (rcases hA with rfl | rfl <;> simp); (rcases hA with rfl | rfl <;> simp)]
    · intro hjs A hA h1 h2
      rw [f2.get hA (by intro h'; unfold slotV at h1 h2; rcases h' with rfl | rfl <;> aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
  | succ r ih =>
    intro hr L t h
    have hpos := chkI_pos c hc i hi (4 - r) (by omega)
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by omega : 3 - r < 5) t (by rw [h.pc]; congr 2; omega) h.x18 h.x24 h.x26
        (by omega) (by omega) (by omega) h.val
    have h16 : t1.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (4 - (r + 1) - 1)) := by
      rw [f1.get (by ao) (by unfold slotV; ao)]; exact h.h16
    obtain ⟨t2, s2, e2, p2, x10, x11, x12, m16, r2, f2⟩ :=
      step_Stp hcode hc hi (by omega : 1 ≤ 4 - r) (by omega : 4 - r < 5) t1
        (by rw [p1]; congr 2; omega) (by omega : 4 - (r + 1) - 1 < 4) h16
    have g12 : ∀ A, A ≠ CHAINW + 16 → A ≠ slotV c i → A ≠ slotV c i + 8 → A < 2 ^ 64 →
        t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A h1 h2 h3 hA => by
      rw [f2.get hA (by simpa using h1), f1.get hA (by simp [h2, h3])]
    have hx5 : t2.getReg .x5 = 0 := by
      rw [r2.get (by simp), r1.get (by simp)]; exact h.x5
    have hv := h.val
    have hq : hashInput t2 = toQ (pad64 (WCT9.chainInput index c j i (3 - r) (L.getD (3 - r) 0))) := by
      refine hashInput_of_words t2 _ 0 CHAINW (by rw [pad64_of_aligned _ (by rw [chainInput_len]), chainInput_len])
        x10 (by ao) (by ao) x11 ?_
      rw [wordsOf_chain index c j i (3 - r) _ hc hidx (by omega) hi hj]
      intro k hk
      interval_cases k
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z0
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z8
      · rw [show CHAINW + 8 * 2 = CHAINW + 16 by ao, m16, show 4 - r - 1 = 3 - r by omega]; rfl
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.h24
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z32
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z40
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]
        rw [show 4 - (r + 1) = 3 - r by omega] at hv; exact hv.1
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]
        rw [show 4 - (r + 1) = 3 - r by omega] at hv; exact hv.2
    have hbl := blocks64 _ (chainInput_len index c j i (3 - r) (L.getD (3 - r) 0))
    refine (TBSim.steps (s1.trans s2) (TBSim.shortHash_bind' (W := 11 + 28 * r + 8) e2 hx5
      (hashArgs_const t2 CHAINW 64 (CHAINW + 48) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a => ih (by omega) (L ++ [a.extractLsb' 0 128]) (writeHash t2 a) ?_))).mono
      (by rw [hbl]; omega) (fun _ _ h => h)
    have fw := Frame.writeHash t2 a (CHAINW + 48) x12 (by ao)
    have g : ∀ A, A ≠ CHAINW + 16 → A ≠ slotV c i → A ≠ slotV c i + 8 → ¬ (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) →
        A < 2 ^ 64 → (writeHash t2 a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
      intro A h1 h2 h3 h4 hA
      rw [fw.get hA (by intro h; exact h4 ⟨h.1, by omega⟩), g12 A h1 h2 h3 hA]
    have hlen : L.length = 4 - r := by have := h.len; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p2, pcOf_pred4 _ hpos]
    · rw [getReg_writeHash]; exact hx5
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x18
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x22
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x24
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x25
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x26
    · simp [hlen]; omega
    · have := DigAt.writeHash_lo t2 a (CHAINW + 48) x12 (by ao)
      refine this.congr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), show 4 - r - L.length = 0 by omega]
      rfl
    · rw [fw.get (by ao) (by intro h; ao), m16]
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.h24
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z0
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z8
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z32
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z40
    · intro hjs hlt
      have e : (L ++ [a.extractLsb' 0 128]).getD (4 - d) 0 = L.getD (4 - d) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [e]
      have hslot : DigAt t2 (slotV c i) (L.getD (4 - d) 0) := by
        by_cases hlt' : 4 - d < 4 - (r + 1)
        · exact ((h.op hjs hlt').frame (n1 (fun h' => by omega)) (by unfold slotV; ao) (fun h => h)
            (fun h => h)).frame f2 (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
        · have heq : 4 - d = 3 - r := by omega
          have := o1 hjs heq
          rw [heq]
          rw [show 4 - (r + 1) = 3 - r by omega] at this
          exact this.frame f2 (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
      exact hslot.frame fw (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact (((h.regs.trans r1).trans r2).trans
        (fun x _ => getReg_writeHash t2 a x : RegsExcept t2 (writeHash t2 a) [])).mono (by simp [chainRegs])
    · refine (((h.frame.trans f1).trans f2).trans fw).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with ((hA | hA) | hA) | hA
      · exact hA
      · rcases hA with rfl | rfl <;> simp
      · subst hA; left; constructor <;> omega
      · right; left; constructor <;> omega
    · intro hjs A hA h1 h2
      have hs : slotV c 0 = SIG + 16 + 208 * c := by unfold slotV; omega
      rw [fw.get hA (by intro h'; unfold slotV at h1 h2; aoh), f2.get hA (by intro h'; unfold slotV at h1 h2; aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
end chain
end ClaudeWCT.W9.Machine.Sign
end

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def writes (A : Nat) : Prop := A=LEAFW+16 ∨ A=LEAFW+24 ∨ A=LEAFW+32 ∨ A=LEAFW+40

theorem leaf_obligations (s : MachineState) {c j : Nat} (hc:c<9) (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) : ∀ o∈leafObl c,o.holds s := by
  unfold leafObl
  split
  · intro o ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    have hb:=branchShift_eval s hj h18 5 (by decide)
    rcases ho with rfl|rfl
    · exact valid_ofNat hb (by omega) (by unfold MEMORY_BYTES; omega)
    · exact valid_ofNat hb (by omega) (by unfold MEMORY_BYTES; omega)
  · exact no_obl s

theorem leaf_mem16 (s : MachineState) (c : Nat) :
    memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+16)) = (headerE c).eval s := by
  simp [leafMem,memEval_mwc,LEAFW]
theorem leaf_mem24 (s : MachineState) (c : Nat) :
    memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+24)) = 0 := by
  simp [leafMem,memEval_mwc,LEAFW,cE,E.eval]
theorem leaf_mem32 (s : MachineState) (c : Nat) :
    memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+32)) = (padLoad c 0).eval s := by
  simp [leafMem,memEval_mwc,LEAFW]
theorem leaf_mem40 (s : MachineState) (c : Nat) :
    memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+40)) = (padLoad c 8).eval s := by
  simp [leafMem,memEval_mwc,LEAFW]

theorem step_leaf {im : Image} {c j index : Nat} {pad : Digest}
    (hlook:LookOK im (look c)) (hc:c<9) (hj:j<128)
    (s : MachineState) (hpc:s.pc=pcOf (entry c))
    (h18:s.getReg .x18=BitVec.ofNat 64 j) (h22:s.getReg .x22=BitVec.ofNat 64 index)
    (hp:PadAt c j pad s) :
    ∃t, Steps im s (cycles c) (cycles c) t ∧ fetch im t=some (.base .ECALL) ∧ t.pc=pcOf (hashPc c) ∧
      t.getReg .x10=BitVec.ofNat 64 LEAFW ∧ t.getReg .x11=BitVec.ofNat 64 128 ∧
      t.getReg .x12=BitVec.ofNat 64 (HEAPW+16*(128+physical c j)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW+16))=BitVec.ofNat 64 (leafLo7 c index j) ∧
      t.getMem (BitVec.ofNat 64 (LEAFW+24))=0 ∧
      DigAt t (LEAFW+32) pad ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x28,.x29] ∧ Frame s t writes := by
  obtain ⟨hst,hec⟩:=run_pres hlook (leaf_run hc) s hpc (leaf_obligations s hc hj h18) (no_br s)
  refine ⟨(expected c).toState s,hst,hec rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw[expected,pres_getReg];rfl
  · rw[expected,pres_getReg];rfl
  · rw[expected,pres_getReg]
    change BinOp.eval .add ((outOffset c).eval s) (BitVec.ofNat 64 HEAPW) = _
    rw[outOffset_eval s hj h18]
    change BitVec.ofNat 64 (16*(128+physical c j))+BitVec.ofNat 64 HEAPW = _
    rw[ofNat_add_ofNat]
    congr 1
    omega
  · rw[expected,pres_getMem,leaf_mem16,headerE_eval s h18 h22]
  · rw[expected,pres_getMem,leaf_mem24]
  · change memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+32)) = _ ∧
      memEval s (leafMem c) (BitVec.ofNat 64 (LEAFW+32+8)) = _
    rw[leaf_mem32,show LEAFW+32+8=LEAFW+40 by omega,leaf_mem40]
    exact padLoad_eval s hj h18 hp
  · exact (pres_regsExcept (leafRegs c) _ _ _ _ _ _ s).mono (by simp [leafRegs])
  · refine frame_of_memEval (ws := leafMem c) (fun a => (rfl : ((expected c).toState s).getMem a = memEval s (leafMem c) a)) _ (fun p hm => ?_)
    simp only [leafMem,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by decide)] <;> simp [writes]

end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash privatePair privateInput)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}
theorem step_Z (hcode : Fetch im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (lwuI c + 1))
    {index : Nat} (h22 : s.getReg .x22 = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 14 14 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ecI c) ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 (COEF + 32 * 0) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 16)) = BitVec.ofNat 64 (hdr8 c) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * 0) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = PRIVW + 16 ∨ A = PRIVW + 24) := by
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runZ_eq hc) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_orIdx s h22
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expZ, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem eval_x7p1 (s : MachineState) {j : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) :
    x7p1.eval s = BitVec.ofNat 64 (j + 1) := by
  show s.getReg .x7 + BitVec.ofNat 64 1 = _; rw [h7, ofNat_add_ofNat]
theorem eval_pairWE (s : MachineState) {j index : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hidx : index < 2 ^ 32) :
    pairWE.eval s = BitVec.ofNat 64 (index + 2 ^ 32 * (j + 1)) := by
  show BinOp.eval .or (BinOp.eval .sll (x7p1.eval s) (BitVec.ofNat 64 32)) (s.getReg .x22) = _
  rw [eval_x7p1 s h7, binop_sll _ _ (by norm_num), ofNat_shl, h22]
  exact ofNat_or_hi index (j + 1) hidx
theorem step_CLc (hcode : Fetch im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (paI c))
    {j index B : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) (hj : j + 1 < 27)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 B) (h22 : s.getReg .x22 = BitVec.ofNat 64 index)
    (hidx : index < 2 ^ 32) :
    ∃ t, Steps im s 10 10 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (ecI c) ∧
      t.getReg .x7 = BitVec.ofNat 64 (j + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 PRIVW ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 (B + 32) ∧
      t.getMem (BitVec.ofNat 64 (PRIVW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * (j + 1)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = PRIVW + 24) := by
  have hb : ∀ b ∈ (expCL c true).brs, b.holds s := by
    intro b hb
    simp only [expCL, if_true, pres, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_x7p1 s h7, eval_cE, ofNat_bne (by omega) (by norm_num)]
    simp; omega
  obtain ⟨hst, hec⟩ := run_pres (coordLook_ok hcode hc) (runCL_eq hc true) s hpc (no_obl s) hb
  refine ⟨_, hst, hec rfl, rfl, by rw [pres_getReg]; exact eval_x7p1 s h7, by rw [pres_getReg]; rfl,
    by rw [pres_getReg]; rfl, ?_, ?_, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_⟩
  · rw [pres_getReg]; show s.getReg .x12 + BitVec.ofNat 64 32 = _; rw [h12, ofNat_add_ofNat]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact eval_pairWE s h7 h22 hidx
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expCL, if_true, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; exact ⟨rfl, by rw [off_mwc _ _ (by ao)]⟩
theorem step_CLx (hcode : Fetch im) {c : Nat} (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (paI c))
    {j : Nat} (h7 : s.getReg .x7 = BitVec.ofNat 64 j) (hj : j + 1 = 27) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x6, .x7, .x12, .x18] ∧ Frame s t (fun _ => False) := by
  have hb : ∀ b ∈ (expCL c false).brs, b.holds s := by
    intro b hb
    simp only [expCL, Bool.false_eq_true, if_false, pres, List.mem_singleton] at hb
    subst hb
    rw [br_ne_holds, eval_x7p1 s h7, eval_cE, ofNat_bne (by omega) (by norm_num)]
    simp; omega
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runCL_eq hc false) s hpc (no_obl s) hb
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp),
    fun A _ _ => rfl⟩
theorem eval_ptE (s : MachineState) {j : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (_hj : j < 2 ^ 32)
    (i : Nat) : (ptE i).eval s = BitVec.ofNat 64 (6 * j + i + 1) := by
  show BinOp.eval .add (BinOp.eval .sll (BinOp.eval .add (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 1))
    (s.getReg .x18)) (BitVec.ofNat 64 1)) (BitVec.ofNat 64 (i + 1)) = _
  have e1 : BinOp.eval .add (BinOp.eval .sll (s.getReg .x18) (BitVec.ofNat 64 1)) (s.getReg .x18) =
      BitVec.ofNat 64 (3 * j) := by
    rw [binop_sll _ _ (by norm_num), h18, ofNat_shl]; simp only [BinOp.eval]; rw [ofNat_add_ofNat]; congr 1; ring
  rw [e1, binop_sll _ _ (by norm_num), ofNat_shl]; simp only [BinOp.eval]; rw [ofNat_add_ofNat]; congr 1; ring
theorem step_Q (hcode : Fetch im) {c i j : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (qI c i)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j) (hj : j < 128) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf hornI ∧ t.getReg .x1 = pcOf (qI c i + 5) ∧
      t.getReg .x6 = BitVec.ofNat 64 (6 * j + i + 1) ∧ RegsExcept s t [.x1, .x6] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runQ_eq hc hi) s hpc (no_obl s) (no_br s)
  exact ⟨_, hst, rfl, by rw [pres_getReg]; rfl, by rw [pres_getReg]; exact eval_ptE s h18 (by omega) i,
    pres_regsExcept _ _ _ _ _ _ _ s, fun A _ _ => rfl⟩
def chainW0 (c i j index p : Nat) : Nat := index * 2 ^ 27 + j * 2 ^ 20 + chainK c i + 256 * p
theorem chainW0_merge (c i j index p q : Nat) (hc : c < 9) (hi : i < 6) (hp : p < 4) (hq : q < 4) :
    StoreKind.merge .b (BitVec.ofNat 64 (chainW0 c i j index p)) 1 (BitVec.ofNat 64 q) =
      BitVec.ofNat 64 (chainW0 c i j index q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat8 _ _ (by omega)]
  simp only [chainW0, chainK, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega
theorem step_S (hcode : Fetch im) {c i j index w : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (qI c i + 5)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (hj : j < 128)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 w) (hw : w < 2 ^ 64) (hd : w / 8 ^ i % 8 ≤ 4) :
    ∃ t, Steps im s (if c = 0 then 14 else 15) (if c = 0 then 14 else 15) t ∧ t.pc = pcOf (chkI c i 0) ∧
      t.getReg .x26 = BitVec.ofNat 64 (4 - w / 8 ^ i % 8) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index 0) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 24)) = 0 ∧
      RegsExcept s t [.x6, .x7, .x26, .x29] ∧ Frame s t (fun A => A = CHAINW + 24 ∨ A = CHAINW + 16) := by
  obtain ⟨hst, -⟩ := run_pres (coordLook_ok hcode hc) (runS_eq hc hi) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst, rfl, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getReg]; exact eval_dE s i h25 hw (by omega) hd
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao),
      eval_qE s h18 h22 hj (chainK_lt c i hc hi)]
    simp only [chainW0, Nat.mul_zero, Nat.add_zero]
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expS, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem step_Chk (hcode : Fetch im) {c i st j sel e : Nat} (hc : c < 9) (hi : i < 6) (hst : st < 5)
    (s : MachineState) (hpc : s.pc = pcOf (chkI c i st)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 sel) (h26 : s.getReg .x26 = BitVec.ofNat 64 e) (hj : j < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (he : e < 2 ^ 64) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t k, Steps im s k k t ∧ k ≤ 11 ∧ t.pc = pcOf (skipI c i st) ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = slotV c i + 8 ∨ A = slotV c i) ∧ (j = sel → e = st → DigAt t (slotV c i) v) ∧
      (¬ (j = sel ∧ e = st) → Frame s t (fun _ => False)) := by
  have hl := coordLook_ok hcode hc
  by_cases hjs : j = sel
  · subst hjs
    by_cases hes : e = st
    · subst hes
      obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 2 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      refine ⟨_, 11, hst', le_rfl, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), ?_, fun _ _ => ⟨?_, ?_⟩, ?_⟩
      · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
        simp only [expChk, pres, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false,
          List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
      · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
      · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
      · intro h; exact absurd ⟨rfl, rfl⟩ h
    · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 1 < 3)) s hpc (no_obl s) (by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_holds]; simp only [E.eval, h26, eval_cE]; rw [ofNat_bne he (by omega)]; simp [hes]
        · rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hj]; simp)
      exact ⟨_, 3, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
        fun _ h => absurd h hes, fun _ A _ _ => rfl⟩
  · obtain ⟨hst', -⟩ := run_pres hl (runChk_eq hc hi hst (by norm_num : 0 < 3)) s hpc (no_obl s) (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      rw [br_ne_holds]; simp only [E.eval, h18, h24]; rw [ofNat_bne hj hsel]; simp [hjs])
    exact ⟨_, 1, hst', by norm_num, rfl, (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp), fun A _ _ => rfl,
      fun h => absurd h hjs, fun _ A _ _ => rfl⟩
theorem step_Stp (hcode : Fetch im) {c i st j index : Nat} (hc : c < 9) (hi : i < 6) (h1 : 1 ≤ st) (h4 : st < 5)
    (s : MachineState) (hpc : s.pc = pcOf (skipI c i (st - 1))) {pv : Nat} (hpv : pv < 4)
    (h16 : s.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index pv)) :
    ∃ t, Steps im s 9 9 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (chkI c i st - 1) ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAINW ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAINW + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (st - 1)) ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x29] ∧ Frame s t (fun A => A = CHAINW + 16) := by
  obtain ⟨hst', hec⟩ := run_pres (coordLook_ok hcode hc) (runStp_eq hc hi h1 h4) s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', hec rfl, rfl, rfl, rfl, rfl, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]
    show StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (CHAINW + 16))) 1 (BitVec.ofNat 64 (st - 1)) = _
    rw [h16, chainW0_merge c i j index pv (st - 1) hc hi hpv (by omega)]
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expStp, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; refine ⟨rfl, ?_⟩; rw [off_mwc _ _ (by ao)]
theorem step_Lc (hcode : Fetch im) {c i : Nat} (hc : c < 9) (hi : i < 6) (s : MachineState)
    (hpc : s.pc = pcOf (skipI c i 4)) {v : Digest} (hv : DigAt s (CHAINW + 48) v) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf (lcEnd c i) ∧ DigAt t (LEAFW + leafOff i) v ∧
      t.getReg .x29 = BitVec.ofNat 64 LEAFW ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFW + leafOff i + 8 ∨ A = LEAFW + leafOff i) := by
  obtain ⟨hst', -⟩ := run_pres (coordLook_ok hcode hc) (runLc_eq hc hi) s hpc (no_obl s) (no_br s)
  have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
  refine ⟨_, hst', rfl, ⟨?_, ?_⟩, rfl, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; exact hv.1
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; exact hv.2
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expLc, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao
theorem padE_eval (s : MachineState) (c off : Nat) :
    (padE c off).eval s = if c = 0 then 0 else s.getMem (BitVec.ofNat 64 (FORW + forOff (c - 1) + off)) := by
  unfold padE; split_ifs <;> rfl


variable {sk : BitVec 256}
theorem chain_from (hcode : Fetch im) {c i j index sel w d : Nat} (hc : c < 9) (hi : i < 6) (hj : j < 128)
    (hsel : sel < 128) (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hd : d ≤ 4) {s0 : MachineState} :
    ∀ r, r ≤ 4 → ∀ (L : List Digest) (t : MachineState), ChkSt c i j index sel w d r L s0 t →
      TBSim im sk t (11 + 28 * r + 8) (chainRest index c j i d r L) (ChainPost c i j sel s0) := by
  intro r
  induction r with
  | zero =>
    intro _ L t h
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by norm_num : 4 < 5) t h.pc h.x18 h.x24 h.x26 (by omega) (by omega) (by omega) h.val
    obtain ⟨t2, s2, p2, l2, x29_2, r2, f2⟩ := step_Lc hcode hc hi t1 p1 (h.val.frame f1 (by ao) (by ao) (by ao))
    have hlo : leafOff i ≤ 112 := by unfold leafOff; split_ifs <;> omega
    refine (TBSim.pure_steps' (s1.trans s2) ⟨p2, l2, fun hjs => ?_, ?_, ?_, ?_, x29_2⟩).mono (by omega)
      (fun _ _ h => h)
    · by_cases hd0 : d = 0
      · subst hd0
        have := o1 hjs rfl
        exact this.frame f2 (by ao) (by ao) (by ao)
      · have := h.op hjs (by omega)
        exact (this.frame (n1 (fun h' => hd0 (by omega))) (by ao) (fun h => h) (fun h => h)).frame f2
          (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact ((h.regs.trans r1).trans r2).mono (by simp [chainRegs])
    · refine ((h.frame.trans f1).trans f2).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with (hA | hA) | hA <;> [exact hA; (rcases hA with rfl | rfl <;> simp); (rcases hA with rfl | rfl <;> simp)]
    · intro hjs A hA h1 h2
      rw [f2.get hA (by intro h'; unfold slotV at h1 h2; rcases h' with rfl | rfl <;> aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
  | succ r ih =>
    intro hr L t h
    have hpos := chkI_pos c hc i hi (4 - r) (by omega)
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, o1, n1⟩ :=
      step_Chk hcode hc hi (by omega : 3 - r < 5) t (by rw [h.pc]; congr 2; omega) h.x18 h.x24 h.x26
        (by omega) (by omega) (by omega) h.val
    have h16 : t1.getMem (BitVec.ofNat 64 (CHAINW + 16)) = BitVec.ofNat 64 (chainW0 c i j index (4 - (r + 1) - 1)) := by
      rw [f1.get (by ao) (by unfold slotV; ao)]; exact h.h16
    obtain ⟨t2, s2, e2, p2, x10, x11, x12, m16, r2, f2⟩ :=
      step_Stp hcode hc hi (by omega : 1 ≤ 4 - r) (by omega : 4 - r < 5) t1
        (by rw [p1]; congr 2; omega) (by omega : 4 - (r + 1) - 1 < 4) h16
    have g12 : ∀ A, A ≠ CHAINW + 16 → A ≠ slotV c i → A ≠ slotV c i + 8 → A < 2 ^ 64 →
        t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A h1 h2 h3 hA => by
      rw [f2.get hA (by simpa using h1), f1.get hA (by simp [h2, h3])]
    have hx5 : t2.getReg .x5 = 0 := by
      rw [r2.get (by simp), r1.get (by simp)]; exact h.x5
    have hv := h.val
    have hq : hashInput t2 = toQ (pad64 (WCT9.chainInput index c j i (3 - r) (L.getD (3 - r) 0))) := by
      refine hashInput_of_words t2 _ 0 CHAINW (by rw [pad64_of_aligned _ (by rw [chainInput_len]), chainInput_len])
        x10 (by ao) (by ao) x11 ?_
      rw [wordsOf_chain index c j i (3 - r) _ hc hidx (by omega) hi hj]
      intro k hk
      interval_cases k
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z0
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z8
      · rw [show CHAINW + 8 * 2 = CHAINW + 16 by ao, m16, show 4 - r - 1 = 3 - r by omega]; rfl
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.h24
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z32
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]; exact h.z40
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]
        rw [show 4 - (r + 1) = 3 - r by omega] at hv; exact hv.1
      · rw [g12 _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao)]
        rw [show 4 - (r + 1) = 3 - r by omega] at hv; exact hv.2
    have hbl := blocks64 _ (chainInput_len index c j i (3 - r) (L.getD (3 - r) 0))
    refine (TBSim.steps (s1.trans s2) (TBSim.shortHash_bind' (W := 11 + 28 * r + 8) e2 hx5
      (hashArgs_const t2 CHAINW 64 (CHAINW + 48) x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
      (fun a => ih (by omega) (L ++ [a.extractLsb' 0 128]) (writeHash t2 a) ?_))).mono
      (by rw [hbl]; omega) (fun _ _ h => h)
    have fw := Frame.writeHash t2 a (CHAINW + 48) x12 (by ao)
    have g : ∀ A, A ≠ CHAINW + 16 → A ≠ slotV c i → A ≠ slotV c i + 8 → ¬ (CHAINW + 48 ≤ A ∧ A < CHAINW + 80) →
        A < 2 ^ 64 → (writeHash t2 a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
      intro A h1 h2 h3 h4 hA
      rw [fw.get hA (by intro h; exact h4 ⟨h.1, by omega⟩), g12 A h1 h2 h3 hA]
    have hlen : L.length = 4 - r := by have := h.len; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc_writeHash, p2, pcOf_pred4 _ hpos]
    · rw [getReg_writeHash]; exact hx5
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x18
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x22
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x24
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x25
    · rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h.x26
    · simp [hlen]; omega
    · have := DigAt.writeHash_lo t2 a (CHAINW + 48) x12 (by ao)
      refine this.congr ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), show 4 - r - L.length = 0 by omega]
      rfl
    · rw [fw.get (by ao) (by intro h; ao), m16]
      rfl
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.h24
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z0
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z8
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z32
    · rw [g _ (by ao) (by unfold slotV; ao) (by unfold slotV; ao) (by ao) (by ao)]; exact h.z40
    · intro hjs hlt
      have e : (L ++ [a.extractLsb' 0 128]).getD (4 - d) 0 = L.getD (4 - d) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [e]
      have hslot : DigAt t2 (slotV c i) (L.getD (4 - d) 0) := by
        by_cases hlt' : 4 - d < 4 - (r + 1)
        · exact ((h.op hjs hlt').frame (n1 (fun h' => by omega)) (by unfold slotV; ao) (fun h => h)
            (fun h => h)).frame f2 (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
        · have heq : 4 - d = 3 - r := by omega
          have := o1 hjs heq
          rw [heq]
          rw [show 4 - (r + 1) = 3 - r by omega] at this
          exact this.frame f2 (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
      exact hslot.frame fw (by unfold slotV; ao) (by unfold slotV; ao) (by unfold slotV; ao)
    · exact (((h.regs.trans r1).trans r2).trans
        (fun x _ => getReg_writeHash t2 a x : RegsExcept t2 (writeHash t2 a) [])).mono (by simp [chainRegs])
    · refine (((h.frame.trans f1).trans f2).trans fw).mono (fun A _ hA => ?_)
      unfold chainW
      rcases hA with ((hA | hA) | hA) | hA
      · exact hA
      · rcases hA with rfl | rfl <;> simp
      · subst hA; left; constructor <;> omega
      · right; left; constructor <;> omega
    · intro hjs A hA h1 h2
      have hs : slotV c 0 = SIG + 16 + 208 * c := by unfold slotV; omega
      rw [fw.get hA (by intro h'; unfold slotV at h1 h2; aoh), f2.get hA (by intro h'; unfold slotV at h1 h2; aoh),
        n1 (fun h' => hjs h'.1) A hA (fun h => h), h.nosel hjs A hA h1 h2]
end ClaudeWCT.W9.Machine.Sign.SharedReuse


namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem node_run {c m : Nat} (hc:c<9) (hm:m<3) : runNode c m=some (expected c m) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact node_run_0 m hm
  |1,_=>exact node_run_1 m hm
  |2,_=>exact node_run_2 m hm
  |3,_=>exact node_run_3 m hm
  |4,_=>exact node_run_4 m hm
  |5,_=>exact node_run_5 m hm
  |6,_=>exact node_run_6 m hm
  |7,_=>exact node_run_7 m hm
  |8,_=>exact node_run_8 m hm

theorem readObl_holds (s : MachineState) {h : Nat} (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀o∈readObl,o.holds s := by
  have hb:=eval_sh5 s h18
  intro o ho
  simp only[readObl,List.mem_cons,List.not_mem_nil,or_false]at ho
  rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ne_ofNat hb (by ao) (by ao) (by ao)
  · exact ne_ofNat hb (by ao) (by ao) (by ao)
  · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)
  · exact ne_ofNat hb (by ao) (by ao) (by ao)
  · exact ne_ofNat hb (by ao) (by ao) (by ao)
  · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)
  · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)
  · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)

theorem padReadObl_holds (s : MachineState) {c h off : Nat} (hc:c<9) (h4:4≤h) (h8:h<8)
    (ho:off=0 ∨ off=8) (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀o∈padReadObl c off,o.holds s := by
  have hb:=padShift_eval s h4 h8 h18
  intro o hm
  simp only[padReadObl,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]at hm
  rcases hm with hm|rfl
  · obtain ⟨n,hn,rfl⟩:=List.mem_map.mp hm
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hn
    rcases hn with rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact ne_ofNat hb (by rcases ho with rfl|rfl <;> ao) (by ao) (by rcases ho with rfl|rfl <;> ao)
  · exact valid_ofNat hb (by rcases ho with rfl|rfl <;> omega)
      (by unfold MEMORY_BYTES;rcases ho with rfl|rfl <;> omega)

theorem obligations_hold (s : MachineState) {c h : Nat} (hc:c<9) (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀o∈obligations c (mode h),o.holds s := by
  unfold obligations
  split_ifs with hp
  · intro o ho
    rcases List.mem_append.mp ho with ho|ho
    · rcases List.mem_append.mp ho with ho|ho
      · exact padReadObl_holds s hc (mode_one hp.1).1 (mode_one hp.1).2 (Or.inr rfl) h18 o ho
      · exact padReadObl_holds s hc (mode_one hp.1).1 (mode_one hp.1).2 (Or.inl rfl) h18 o ho
    · exact readObl_holds s hh h18 o ho
  · simpa only[List.nil_append] using readObl_holds s hh h18

theorem branches_hold (s : MachineState) {h : Nat} (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀b∈branches (mode h),b.holds s := by
  unfold branches mode
  by_cases h8:8≤h
  · simp only[if_pos h8,ite_true]
    intro b hb
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
    subst b
    rw[br_ltu_holds]
    change BitVec.ult (s.getReg .x18) (BitVec.ofNat 64 8)=false
    rw[h18,ofNat_ult (by omega) (by decide)]
    simp[show ¬h<8 by omega]
  · simp only[if_neg h8]
    by_cases h4:4≤h
    all_goals simp only[h4,↓reduceIte,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide]
    all_goals intro b hb
    all_goals simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
    all_goals rcases hb with rfl|rfl <;> rw[br_ltu_holds]
    all_goals change BitVec.ult (s.getReg .x18) (BitVec.ofNat 64 _) = _
    all_goals rw[h18,ofNat_ult (by omega) (by decide)]
    all_goals simp_all

def writes (A : Nat) : Prop := ∃k<8,A=NODEW+8*k

def value (c m off : Nat) : E :=
  if off=0 then nodeLd 0 else if off=8 then nodeLd 8 else if off=16 then hdrLo c m else
  if off=24 then hdrHi m else if off=32 then padWord c m 0 else if off=40 then padWord c m 8 else
  if off=48 then nodeLd 16 else nodeLd 24

theorem mem_read (s : MachineState) (c m : Nat) {k : Nat} (hk:k<8) :
    memEval s (mem c m) (BitVec.ofNat 64 (NODEW+8*k))=(value c m (8*k)).eval s := by
  interval_cases k <;> simp[mem,value,memEval_mwc,NODEW]

theorem step_node {im : Image} {c h index : Nat}
    (hlook:LookOK im (look c)) (hc:c<9) (hh:h<128)
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) (h18:s.getReg .x18=BitVec.ofNat 64 h)
    (h22:s.getReg .x22=BitVec.ofNat 64 index) :
    ∃t,Steps im s (cycles c (mode h)) (cycles c (mode h)) t ∧
      fetch im t=some (.base .ECALL) ∧ t.pc=pcOf (hashPc c) ∧
      t.getReg .x10=BitVec.ofNat 64 NODEW ∧ t.getReg .x11=BitVec.ofNat 64 64 ∧
      t.getReg .x12=BitVec.ofNat 64 NOUTW ∧
      (∀k,k<8 → t.getMem (BitVec.ofNat 64 (NODEW+8*k))=(value c (mode h) (8*k)).eval s) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x28] ∧ Frame s t writes := by
  obtain ⟨hs,he⟩:=runA_pres hlook (node_run hc (mode_lt h)) s hpc
    (obligations_hold s hc hh h18) (branches_hold s hh h18)
  refine ⟨(expected c (mode h)).toState s,hs,he rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · intro k hk
    rw[expected,pres_getMem,mem_read s c (mode h) hk]
  · exact (pres_regsExcept (regs c (mode h)) _ _ _ _ _ _ s).mono (by simp[regs])
  · refine frame_of_memEval (ws:=mem c (mode h)) (fun _=>rfl) _ (fun p hm=>?_)
    simp only[mem,List.mem_cons,List.not_mem_nil,or_false]at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by ao)]
    all_goals unfold writes
    · exact ⟨5,by omega,by omega⟩
    · exact ⟨4,by omega,by omega⟩
    · exact ⟨3,by omega,by omega⟩
    · exact ⟨2,by omega,by omega⟩
    · exact ⟨7,by omega,by omega⟩
    · exact ⟨6,by omega,by omega⟩
    · exact ⟨1,by omega,by omega⟩
    · exact ⟨0,by omega,by omega⟩

end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def raw (c p : Nat) : Nat := if first c then p else 2*(p%64)+p/64
def mode (c j : Nat) : Nat := if j=127 then 2 else if j=126 ∧ first c=false then 1 else 0
def advance (c j : Nat) : Nat := if first c then j+1 else if j=126 then 1 else j+2

theorem raw_lt (c : Nat) {p : Nat} (hp:p<128) : raw c p<128 := by unfold raw;split <;> omega
theorem raw_eq127 (c : Nat) {p : Nat} (hp:p<128) : raw c p=127 ↔ p=127 := by
  unfold raw
  split <;> omega
theorem raw_advance (c : Nat) {p : Nat} (hp:p+1<128) : advance c (raw c p)=raw c (p+1) := by
  unfold raw advance
  split_ifs <;> omega

theorem mode_lt (c j : Nat) : mode c j<3 := by unfold mode;split_ifs <;> omega

theorem next_run {c m : Nat} (hc:c<9) (hm:m<3) (odd : Bool) : runNext c m odd=some (expected c m odd) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact next_run_0 m hm odd
  |1,_=>exact next_run_1 m hm odd
  |2,_=>exact next_run_2 m hm odd
  |3,_=>exact next_run_3 m hm odd
  |4,_=>exact next_run_4 m hm odd
  |5,_=>exact next_run_5 m hm odd
  |6,_=>exact next_run_6 m hm odd
  |7,_=>exact next_run_7 m hm odd
  |8,_=>exact next_run_8 m hm odd

/-- C1: the leaf stub tests the parity of the physical child (raw bit 0 on A, raw bit 1 on B/C). -/
theorem parityE_eval (s : MachineState) {c j : Nat} (hj:j<128) (h18:s.getReg .x18=BitVec.ofNat 64 j) :
    (parityE c).eval s=BitVec.ofNat 64 (SharedLeaf.physical c j%2) := by
  have hfe:SharedLeaf.first c=first c:=rfl
  unfold parityE SharedLeaf.physical
  rw[hfe]
  by_cases hf:first c=true
  · rw[if_pos hf,if_pos hf]
    change s.getReg .x18 &&& BitVec.ofNat 64 1=_
    rw[h18]
    exact ofNat_and_one j (by omega)
  · rw[if_neg hf,if_neg hf]
    change BinOp.eval .srl (s.getReg .x18) (BitVec.ofNat 64 1) &&& BitVec.ofNat 64 1=_
    rw[binop_srl _ _ (by decide),h18,ofNat_shr _ _ (by omega),ofNat_and_one _ (by omega)]
    congr 1
    omega

theorem parity_holds (s : MachineState) {c j : Nat} (hj:j<128) (h18:s.getReg .x18=BitVec.ofNat 64 j) :
    Br.holds s ⟨.ne,parityE c,cE 0,decide (SharedLeaf.physical c j%2=1)⟩ := by
  rw[br_ne_holds,parityE_eval s hj h18,eval_cE,ofNat_bne (by omega) (by decide),
    show decide (SharedLeaf.physical c j%2≠0)=decide (SharedLeaf.physical c j%2=1) from
      decide_eq_decide.mpr (by omega)]

theorem stub_obligations (s : MachineState) {A : Nat} (h12:s.getReg .x12=BitVec.ofNat 64 A)
    (hal:A%16=0) (hA:A+32≤MEMORY_BYTES) (odd : Bool) : ∀o∈stubObl odd,o.holds s := by
  cases odd
  · intro o ho
    simp only[stubObl,Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false]at ho
    have hb:(E.reg .x12).eval s=BitVec.ofNat 64 A:=h12
    rcases ho with rfl|rfl|rfl|rfl <;> exact valid_ofNat hb (by omega) (by omega)
  · intro o ho
    simp only[stubObl,↓reduceIte,List.not_mem_nil]at ho

theorem memEval_stub (s : MachineState) {A : Nat} (h12:s.getReg .x12=BitVec.ofNat 64 A) (hA:A+32<2^64)
    (B : Nat) (hB:B<2^64) :
    memEval s (stubMem false) (BitVec.ofNat 64 B)=
      (if B=A+8 then s.getMem (BitVec.ofNat 64 (A+24))
       else if B=A then s.getMem (BitVec.ofNat 64 (A+16)) else s.getMem (BitVec.ofNat 64 B)) := by
  have ha:∀off,off<32 → Addr.eval s (a2A off)=BitVec.ofNat 64 (A+off):=by
    intro off _
    change s.getReg .x12+BitVec.ofNat 64 off=_
    rw[h12,ofNat_add_ofNat]
  have hl:∀off,off<32 → (a2Ld off).eval s=s.getMem (BitVec.ofNat 64 (A+off)):=by
    intro off _
    change s.getMem (s.getReg .x12+BitVec.ofNat 64 off)=_
    rw[h12,ofNat_add_ofNat]
  simp only[stubMem,Bool.false_eq_true,↓reduceIte,memEval]
  rw[ha 8 (by decide),ha 0 (by decide),hl 24 (by decide),hl 16 (by decide),Nat.add_zero]
  by_cases h8:B=A+8
  · subst h8;simp
  · have h8':BitVec.ofNat 64 B≠BitVec.ofNat 64 (A+8):=fun e=>h8 ((ofNat_inj hB (by omega)).mp e)
    rw[if_neg h8',if_neg h8]
    by_cases h0:B=A
    · subst h0;simp
    · have h0':BitVec.ofNat 64 B≠BitVec.ofNat 64 A:=fun e=>h0 ((ofNat_inj hB (by omega)).mp e)
      have h0'':BitVec.ofNat 64 B≠BitVec.ofNat 64 (A+0):=h0'
      first
      | rw[if_neg h0'',if_neg h0]
      | rw[if_neg h0',if_neg h0]

theorem branch_eq_holds (s : MachineState) {h k : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h)
    (hh:h<2^64) (hk:k<2^64) (b : Bool) :
    Br.holds s ⟨.eq,.reg .x18,cE k,b⟩ ↔ decide (h=k)=b := by
  change ((s.getReg .x18)==BitVec.ofNat 64 k)=b ↔ _
  rw[h18]
  have he:((BitVec.ofNat 64 h)==(BitVec.ofNat 64 k))=decide (h=k):=by
    by_cases he:h=k
    · subst k;simp
    · have hv:BitVec.ofNat 64 h≠BitVec.ofNat 64 k:=fun e=>he ((ofNat_inj hh hk).mp e)
      simp[he,hv]
  rw[he]

theorem branches_hold (s : MachineState) {c j : Nat} (hj:j<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 j) : ∀b∈branches c (mode c j),b.holds s := by
  unfold branches
  by_cases hf:first c=true
  · rw[if_pos hf]
    intro b hb
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
    subst b
    rw[br_ltu_holds,eval_x18p1 s h18,eval_cE,ofNat_ult (by omega) (by decide)]
    unfold mode
    split_ifs <;> simp_all <;> omega
  · have hf':first c=false:=Bool.eq_false_iff.mpr hf
    rw[if_neg hf]
    unfold mode
    by_cases h127:j=127
    · simp only[if_pos h127,ite_true]
      intro b hb
      simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
      subst b
      rw[branch_eq_holds s h18 (by omega) (by decide)]
      simp[h127]
    · simp only[if_neg h127]
      by_cases h126:j=126
      all_goals simp only[h126,hf',and_true,↓reduceIte,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (1:Nat)≠2 by decide,show (0:Nat)≠2 by decide]
      all_goals intro b hb
      all_goals simp only[List.mem_cons,List.not_mem_nil,or_false]at hb
      all_goals rcases hb with rfl|rfl <;> rw[branch_eq_holds s h18 (by omega) (by decide)]
      all_goals simp_all

theorem nextE_eval (s : MachineState) {c j : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 j) :
    (nextE c (mode c j)).eval s=BitVec.ofNat 64 (if j=127 then 127 else advance c j) := by
  unfold nextE mode advance
  by_cases h127:j=127
  · simp only[if_pos h127,ite_true]
    rfl
  · simp only[if_neg h127]
    by_cases hf:first c=true
    · have hm:¬(j=126 ∧ first c=false):=by simp[hf]
      rw[if_neg hm]
      simp only[show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (1:Nat)≠2 by decide,show (0:Nat)≠2 by decide,if_false,if_pos hf]
      exact eval_x18p1 s h18
    · have hf':first c=false:=Bool.eq_false_iff.mpr hf
      by_cases h126:j=126
      all_goals simp only[h126,hf',Bool.false_eq_true,and_true,↓reduceIte,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (1:Nat)≠2 by decide,show (0:Nat)≠2 by decide]
      · rfl
      · change s.getReg .x18+BitVec.ofNat 64 2=_
        rw[h18,ofNat_add_ofNat]

theorem step_next {im : Image} {c j : Nat} (hlook:LookOK im (look c)) (hc:c<9) (hj:j<128)
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) (h18:s.getReg .x18=BitVec.ofNat 64 j)
    {A : Nat} (h12:s.getReg .x12=BitVec.ofNat 64 A) (hal:A%16=0) (hA:A+32≤MEMORY_BYTES) :
    ∃t k,Steps im s k k t ∧ k≤16 ∧
      t.pc=pcOf (if j=127 then nodePc c else leafI c) ∧
      t.getReg .x18=BitVec.ofNat 64 (if j=127 then 127 else advance c j) ∧
      (SharedLeaf.physical c j%2=0 → t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 (A+16)) ∧
        t.getMem (BitVec.ofNat 64 (A+8))=s.getMem (BitVec.ofNat 64 (A+24))) ∧
      RegsExcept s t [.x6,.x18] ∧ Frame s t (fun B=>SharedLeaf.physical c j%2=0 ∧ (B=A ∨ B=A+8)) := by
  have hAl:A+32<2^64:=by unfold MEMORY_BYTES at hA;omega
  obtain ⟨hs,_⟩:=run_pres hlook (next_run hc (mode_lt c j) (decide (SharedLeaf.physical c j%2=1))) s hpc
    (stub_obligations s h12 hal hA _) (by
      intro b hb
      rcases List.mem_append.mp hb with hb|hb
      · exact branches_hold s hj h18 b hb
      · simp only[List.mem_singleton]at hb
        subst hb
        exact parity_holds s hj h18)
  refine ⟨(expected c (mode c j) (decide (SharedLeaf.physical c j%2=1))).toState s,
    cycles c (mode c j)+stubCycles c (decide (SharedLeaf.physical c j%2=1)),hs,?_,?_,?_,?_,
    pres_regsExcept _ _ _ _ _ _ _ s,?_⟩
  · unfold cycles stubCycles;split_ifs <;> omega
  · change pcOf (if mode c j=2 then nodePc c else leafI c)=_
    by_cases h127:j=127
    · have hm:mode c j=2:=by unfold mode;rw[if_pos h127]
      rw[if_pos hm,if_pos h127]
    · have hm:mode c j≠2:=by
        unfold mode
        rw[if_neg h127]
        split <;> decide
      rw[if_neg hm,if_neg h127]
  · rw[expected,pres_getReg]
    exact nextE_eval s h18
  · intro hev
    have ho:decide (SharedLeaf.physical c j%2=1)=false:=decide_eq_false (by omega)
    rw[ho,expected,pres_getMem,pres_getMem,memEval_stub s h12 hAl A (by omega),
      memEval_stub s h12 hAl (A+8) (by omega),if_neg (show ¬A=A+8 by omega),if_pos (rfl:A=A),
      if_pos (rfl:A+8=A+8)]
    exact ⟨rfl,rfl⟩
  · intro B hB hn
    rw[expected,pres_getMem]
    by_cases hev:SharedLeaf.physical c j%2=0
    · have ho:decide (SharedLeaf.physical c j%2=1)=false:=decide_eq_false (by omega)
      rw[ho,memEval_stub s h12 hAl B hB,if_neg (fun h=>hn ⟨hev,Or.inr h⟩),if_neg (fun h=>hn ⟨hev,Or.inl h⟩)]
    · have ho:decide (SharedLeaf.physical c j%2=1)=true:=decide_eq_true (by omega)
      rw[ho]
      rfl
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem tail_run {c k : Nat} (hc:c<9) (hk:k<4) (back : Bool) : runTail c k back=some (expected c k back) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact tail_run_0 k hk back
  |1,_=>exact tail_run_1 k hk back
  |2,_=>exact tail_run_2 k hk back
  |3,_=>exact tail_run_3 k hk back
  |4,_=>exact tail_run_4 k hk back
  |5,_=>exact tail_run_5 k hk back
  |6,_=>exact tail_run_6 k hk back
  |7,_=>exact tail_run_7 k hk back
  |8,_=>exact tail_run_8 k hk back

theorem cls_lt (c h : Nat) : cls c h<4 := by unfold cls;split_ifs <;> omega

theorem ltB_holds (s : MachineState) {h n : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h) (hh:h<2^64)
    (hn:n<2^64) (d : Bool) : (ltB n d).holds s ↔ decide (h<n)=d := by
  unfold ltB
  rw[br_ne_holds,eval_cE]
  change ((if BitVec.ult (s.getReg .x18) (BitVec.ofNat 64 n) then (1:Word) else 0) != BitVec.ofNat 64 0)=d ↔ _
  rw[h18,ofNat_ult hh hn]
  by_cases hl:h<n
  · rw[if_pos (decide_eq_true hl),show ((1:Word) != BitVec.ofNat 64 0)=true by decide,decide_eq_true hl]
  · rw[if_neg (show ¬decide (h<n)=true from fun hd=>hl (of_decide_eq_true hd)),
      show ((0:Word) != BitVec.ofNat 64 0)=false by decide,decide_eq_false hl]

theorem oddB_holds (s : MachineState) {h : Nat} (h18:s.getReg .x18=BitVec.ofNat 64 h) (hh:h<2^64) (d : Bool) :
    (oddB d).holds s ↔ decide (h%2=1)=d := by
  unfold oddB
  rw[br_ne_holds,eval_cE]
  change ((s.getReg .x18 &&& BitVec.ofNat 64 1) != BitVec.ofNat 64 0)=d ↔ _
  rw[h18,ofNat_and_one h hh,ofNat_bne (by omega) (by decide),
    show decide (h%2≠0)=decide (h%2=1) from decide_eq_decide.mpr (by omega)]

theorem stub_branches_hold (s : MachineState) {c h : Nat} (hh:h<128)
    (h18:s.getReg .x18=BitVec.ofNat 64 h) : ∀b∈stubBranches c (cls c h),b.holds s := by
  have hl:halfLimit c<2^64:=by unfold halfLimit;split <;> omega
  have hL:halfLimit c≤8:=by unfold halfLimit;split <;> omega
  have L16:=ltB_holds s h18 (show h<2^64 by omega) (show 16<2^64 by decide)
  have LH:=ltB_holds s h18 (show h<2^64 by omega) hl
  have O:=oddB_holds s h18 (show h<2^64 by omega)
  intro b hb
  unfold stubBranches cls at hb
  split_ifs at hb <;> simp only[List.mem_cons,List.not_mem_nil,or_false] at hb <;>
    (try rcases hb with rfl|rfl|rfl) <;>
    first
    | exact (L16 _).mpr (by simp;omega)
    | exact (LH _).mpr (by simp;omega)
    | exact (O _).mpr (by simp;omega)
    | contradiction
    | omega

theorem cycles_le (c k : Nat) : cycles c k≤22 := by unfold cycles;split_ifs <;> omega

theorem step_tail {im : Image} {c h : Nat} (hlook:LookOK im (look c)) (hc:c<9)
    (hh1:1≤h) (hh:h<128) (back : Bool) (hback:back=decide (h-1≠limit c))
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) (h18:s.getReg .x18=BitVec.ofNat 64 h) :
    ∃t,Steps im s (cycles c (cls c h)) (cycles c (cls c h)) t ∧ cycles c (cls c h)≤22 ∧
      t.pc=pcOf (if back then nodePc c else finishPc c) ∧ t.getReg .x18=BitVec.ofNat 64 (h-1) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW+16*h))=
        s.getMem (BitVec.ofNat 64 (NOUTW+halfOff (clsHigh c (cls c h)))) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW+16*h+8))=
        s.getMem (BitVec.ofNat 64 (NOUTW+halfOff (clsHigh c (cls c h))+8)) ∧
      RegsExcept s t [.x6,.x7,.x18,.x28,.x29] ∧
      Frame s t (fun A=>A=HEAPW+16*h+8 ∨ A=HEAPW+16*h) := by
  have hb:=eval_sh4 s h18
  have hm1:=eval_x18m1 s h18 hh1 (by omega)
  have hlim:limit c<2^64:=by unfold limit;split <;> omega
  obtain ⟨hs,_⟩:=run_pres hlook (tail_run hc (cls_lt c h) back) s hpc (by
    intro o ho
    simp only[List.mem_cons,List.not_mem_nil,or_false]at ho
    rcases ho with rfl|rfl <;> exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)) (by
    intro b hbm
    simp only[branches,List.mem_cons]at hbm
    rcases hbm with rfl|hbm
    · rw[br_ne_holds,hm1,eval_cE,ofNat_bne (by omega) hlim,hback]
    · exact stub_branches_hold s hh h18 b hbm)
  have hm:∀a,((expected c (cls c h) back).toState s).getMem a=
      memEval s [mwc (HEAPW+16*h+8) (outWord (clsHigh c (cls c h)) 8),
        mwc (HEAPW+16*h) (outWord (clsHigh c (cls c h)) 0)] a:=by
    intro a
    change memEval s [(heapAddr 8,outWord (clsHigh c (cls c h)) 8),(heapAddr 0,outWord (clsHigh c (cls c h)) 0)] a=_
    simp only[memEval,Addr.eval,heapAddr,mwc,hb,ofNat_add_ofNat]
    rw[show 16*h+(HEAPW+8)=HEAPW+16*h+8 by omega,show 16*h+(HEAPW+0)=HEAPW+16*h by omega]
    rfl
  refine ⟨(expected c (cls c h) back).toState s,hs,cycles_le c _,rfl,?_,?_,?_,pres_regsExcept _ _ _ _ _ _ _ s,?_⟩
  · rw[expected,pres_getReg]
    exact hm1
  · rw[hm,memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw[hm,memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · refine frame_of_memEval hm _ (fun p hp=>?_)
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hp
    rcases hp with rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by ao)] <;> simp
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem finish_run {c : Nat} (hc:c<9) : runFinish c=some (expected c) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact finish_run_0
  |1,_=>exact finish_run_1
  |2,_=>exact finish_run_2
  |3,_=>exact finish_run_3
  |4,_=>exact finish_run_4
  |5,_=>exact finish_run_5
  |6,_=>exact finish_run_6
  |7,_=>exact finish_run_7
  |8,_=>exact finish_run_8

def physical (c j : Nat) : Nat := if first c then j else j/2+64*(j%2)

theorem physical_eval (s : MachineState) {c j : Nat} (hj:j<128) (h24:s.getReg .x24=BitVec.ofNat 64 j) :
    (physicalE c).eval s=BitVec.ofNat 64 (physical c j) := by
  unfold physicalE physical
  split
  · exact h24
  · unfold loBit
    rw[eval_bin,eval_bin,eval_cE,binop_srl _ _ (by decide),eval_bin,eval_cE,binop_sll _ _ (by decide)]
    change ((s.getReg .x24 >>> 1) + ((s.getReg .x24 &&& BitVec.ofNat 64 1) <<< 6))=_
    rw[h24,ofNat_shr _ _ (by omega),ofNat_and_one j (by omega),ofNat_shl,ofNat_add_ofNat]
    congr 1
    ring

theorem target_bound {c : Nat} (hc:c<9) : target c+64<2^64 := by
  unfold target FORW;split <;> omega

theorem mem_read (s : MachineState) {c k : Nat} (hc:c<9) (hk:k<nwords c) :
    memEval s (mem c) (BitVec.ofNat 64 (target c+8*k))=s.getMem (BitVec.ofNat 64 (source c+8*k)) := by
  have hb:=target_bound hc
  unfold mem nwords at *
  split_ifs at hk ⊢ with hf
  all_goals interval_cases k
  all_goals simp (disch:=omega) [List.range_succ,memEval_mwc,memEval_nil'] <;> rfl

def writes (c A : Nat) : Prop := ∃k<nwords c,A=target c+8*k

theorem step_finish {im : Image} {c j : Nat} (hlook:LookOK im (look c)) (hc:c<9) (hj:j<128)
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) (h24:s.getReg .x24=BitVec.ofNat 64 j) :
    ∃t,Steps im s (words c).length (words c).length t ∧ (words c).length≤21 ∧
      t.pc=pcOf (pathPc c) ∧ t.getReg .x24=BitVec.ofNat 64 (128+physical c j) ∧
      (∀k,k<nwords c→t.getMem (BitVec.ofNat 64 (target c+8*k))=s.getMem (BitVec.ofNat 64 (source c+8*k))) ∧
      RegsExcept s t [.x6,.x7,.x24,.x28,.x29] ∧ Frame s t (writes c) := by
  obtain ⟨hs,_⟩:=runA_pres hlook (finish_run hc) s hpc (no_obl s) (no_br s)
  refine ⟨(expected c).toState s,hs,?_,rfl,?_,?_,pres_regsExcept _ _ _ _ _ _ _ s,?_⟩
  · have h:∀c,c<9→(words c).length≤21:=by decide +kernel
    exact h c hc
  · rw[expected,pres_getReg]
    change (physicalE c).eval s+BitVec.ofNat 64 128=_
    rw[physical_eval s hj h24,ofNat_add_ofNat,Nat.add_comm]
  · intro k hk
    rw[expected,pres_getMem,mem_read s hc hk]
  · refine frame_of_memEval (ws:=mem c) (fun _=>rfl) _ (fun p hp=>?_)
    obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hp
    have hk':k<nwords c:=List.mem_range.mp (List.mem_reverse.mp hk)
    have hb:=target_bound hc
    have hn:nwords c≤8:=by unfold nwords;split <;> omega
    refine ⟨rfl,?_⟩
    rw[off_mwc _ _ (by omega)]
    exact ⟨k,hk',rfl⟩
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem path_run {c level : Nat} (hc:c<9) (hl:level<levels c) : runPath c level=some (expected c level) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact path_run_0 level hl
  |1,_=>exact path_run_1 level hl
  |2,_=>exact path_run_2 level hl
  |3,_=>exact path_run_3 level hl
  |4,_=>exact path_run_4 level hl
  |5,_=>exact path_run_5 level hl
  |6,_=>exact path_run_6 level hl
  |7,_=>exact path_run_7 level hl
  |8,_=>exact path_run_8 level hl

theorem eval_offset (s : MachineState) {sel : Nat} (h24:s.getReg .x24=BitVec.ofNat 64 (128+sel)) (hsel:sel<128)
    (l : Nat) (hl:l<7) : (offsetE l).eval s=BitVec.ofNat 64 (16*(2^(7-l)+(sel/2^l ^^^1))) := by
  show BinOp.eval .sll (BinOp.eval .xor (BinOp.eval .srl (s.getReg .x24) (BitVec.ofNat 64 l))
    (BitVec.ofNat 64 1)) (BitVec.ofNat 64 4)=_
  rw[binop_sll _ _ (by norm_num),binop_srl _ _ (by omega),h24,ofNat_shr _ _ (by omega),Nat.add_comm 128 sel]
  simp only[BinOp.eval]
  rw[show BitVec.ofNat 64 ((sel+128)/2^l) ^^^ BitVec.ofNat 64 1=BitVec.ofNat 64 ((sel+128)/2^l ^^^1) by
    apply BitVec.eq_of_toNat_eq
    have h1:(sel+128)/2^l<2^64:=lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have h2:(sel+128)/2^l ^^^1<2^64:=Nat.xor_lt_two_pow h1 (by norm_num)
    simp only[BitVec.toNat_xor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2],
    pathIdx_eq sel hsel l hl,ofNat_shl]
  congr 1
  ring

theorem eval_word (s : MachineState) {sel l : Nat} (h24:s.getReg .x24=BitVec.ofNat 64 (128+sel))
    (hsel:sel<128) (hl:l<7) (off : Nat) :
    (word l off).eval s=s.getMem (BitVec.ofNat 64 (HEAPW+16*(2^(7-l)+(sel/2^l ^^^1))+off)) := by
  change s.getMem ((offsetE l).eval s+BitVec.ofNat 64 (HEAPW+off))=_
  rw[eval_offset s h24 hsel l hl,ofNat_add_ofNat]
  congr 2
  ring

theorem levels_bound (c : Nat) : levels c≤7 := by unfold levels;split <;> omega

theorem step_path {im : Image} {c l sel : Nat} (hlook:LookOK im (look c)) (hc:c<9)
    (hl:l<levels c) (hsel:sel<128) (s : MachineState)
    (hpc:s.pc=pcOf (entry c l)) (h24:s.getReg .x24=BitVec.ofNat 64 (128+sel)) :
    ∃t,Steps im s 12 12 t ∧ t.pc=pcOf (entry c (l+1)) ∧
      t.getMem (BitVec.ofNat 64 (target c l))=s.getMem (BitVec.ofNat 64 (HEAPW+16*(2^(7-l)+(sel/2^l ^^^1)))) ∧
      t.getMem (BitVec.ofNat 64 (target c l+8))=s.getMem (BitVec.ofNat 64 (HEAPW+16*(2^(7-l)+(sel/2^l ^^^1))+8)) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun A=>A=target c l+8∨A=target c l) := by
  have hl7:l<7:=lt_of_lt_of_le hl (levels_bound c)
  have hb:=eval_offset s h24 hsel l hl7
  have hlt:=pathHeap_lt sel l hsel hl7
  obtain ⟨hs,_⟩:=runA_pres hlook (path_run hc hl) s hpc (by
    intro o ho
    simp only[List.mem_cons,List.not_mem_nil,or_false]at ho
    rcases ho with rfl|rfl
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)
    · exact valid_ofNat hb (by ao) (by unfold MEMORY_BYTES;ao)) (no_br s)
  have tb:target c l+8<2^64:=by unfold target slotV;ao
  refine ⟨_,hs,rfl,?_,?_,pres_regsExcept _ _ _ _ _ _ _ s,?_⟩
  · rw[pres_getMem,memEval_mwc_ne _ _ _ (by omega) (by omega) (by omega),memEval_mwc_self _ _ _ _ (by omega),eval_word s h24 hsel hl7,Nat.add_zero]
  · rw[pres_getMem,memEval_mwc_self _ _ _ _ (by omega),eval_word s h24 hsel hl7]
  · refine frame_of_memEval (fun _=>rfl) _ (fun p hp=>?_)
    simp only[expected,pres,List.mem_cons,List.not_mem_nil,or_false]at hp
    rcases hp with rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by omega)] <;> simp
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem end_run {c : Nat} (hc:c<9) : runEnd c=some (expected c) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact end_run_0
  |1,_=>exact end_run_1
  |2,_=>exact end_run_2
  |3,_=>exact end_run_3
  |4,_=>exact end_run_4
  |5,_=>exact end_run_5
  |6,_=>exact end_run_6
  |7,_=>exact end_run_7
  |8,_=>exact end_run_8

theorem step_end {im : Image} {c : Nat} (hlook:LookOK im (look c)) (hc:c<9)
    (s : MachineState) (hpc:s.pc=pcOf (entry c)) :
    ∃t k,Steps im s k k t ∧ k≤5 ∧ t.pc=pcOf (nextPc c) ∧
      (first c=true → DigAt t (target c) 0) ∧ RegsExcept s t [.x29] ∧
      Frame s t (fun A=>first c=true ∧ (A=target c+8 ∨ A=target c)) := by
  obtain ⟨hs,_⟩:=run_pres hlook (end_run hc) s hpc (no_obl s) (no_br s)
  refine ⟨_,_,hs,?_,rfl,?_,?_,?_⟩
  · split <;> omega
  · intro hf
    change DigAt ((expected c).toState s) (target c) 0
    simp only[expected,if_pos hf]
    refine ⟨?_,?_⟩
    · rw[pres_getMem,memEval_mwc_ne _ _ _ (by unfold target slotP;ao) (by unfold target slotP;ao) (by omega),memEval_mwc_self _ _ _ _ (by unfold target slotP;ao)]
      rfl
    · rw[pres_getMem,memEval_mwc_self _ _ _ _ (by unfold target slotP;ao)]
      rfl
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by split <;> simp)
  · refine frame_of_memEval (fun _=>rfl) _ (fun p hp=>?_)
    change p∈(if first c then [mwc (target c+8) (cE 0),mwc (target c) (cE 0)] else []) at hp
    split_ifs at hp with hf
    · simp only[List.mem_cons,List.not_mem_nil,or_false]at hp
      rcases hp with rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by unfold target slotP;ao)] <;> simp[hf]
    · simp at hp
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem lwu_inside (c : Nat) (hc:c < 9) : cbase c < lwuI c ∧ lwuI c < lI c := by
  have h:∀c,c < 9 → cbase c < lwuI c ∧ lwuI c < lI c:=by decide +kernel
  exact h c hc
theorem step_lwu {im : Image} (hcode : Fetch im) {c : Nat} (hc : c < 9) (s : MachineState)
    (hpc : s.pc = pcOf (lwuI c)) {f : Nat} (hf : f < 16384) (h28 : s.getReg .x28 = BitVec.ofNat 64 (TBL + 4 * f))
    (ht : TableAt s) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (lwuI c + 1) ∧ t.getReg .x25 = BitVec.ofNat 64 (pkAt f) ∧
      RegsExcept s t [.x25] ∧ Frame s t (fun _ => False) := by
  have hl := coordLook_ok hcode hc
  have hlw := lwuI_lt c hc
  have hpc' : (s.pc.toNat < 0x1000 || s.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : coordLook c ((s.pc.toNat - 0x1000) / 4) = some 0x000e6c83 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * lwuI c - 0x1000) / 4 = lwuI c by omega]
    rw [coordLook, if_pos (lwu_inside c hc)]
    exact lwu_word c hc
  have hf' : fetch im s = some (.base (.LWU .x25 .x28 0)) :=
    (fetch_of_look hl hpc' hw s rfl).trans decode_lwu
  have hcl : classify (.base (.LWU .x25 .x28 0)) = some (.load .wu .x25 .x28 (signExtend12 0)) := rfl
  have hacc : accessValid (s.getReg .x28 + signExtend12 0) LoadKind.wu.width = true := by
    have e : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (TBL + 4 * f) := by
      rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show TBL + 4 * f < 2 ^ 64 by unfold TBL; omega), MEMORY_BYTES]
    unfold TBL; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
    have e : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (TBL + 4 * f) := by
      rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
    simp only [LoadKind.read, e, table_word ht hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := pkAt_lt f
    omega
  · intro r hr
    have hne : Reg.x25 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp

#print axioms step_lwu
end ClaudeWCT.W9.Machine.Sign.SharedReuse

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem field_run {c : Nat} (hc:c < 9) : runField c=some (expected c) := by
  apply optBeq_eq
  match c,hc with
  |0,_=>exact field_run_0
  |1,_=>exact field_run_1
  |2,_=>exact field_run_2
  |3,_=>exact field_run_3
  |4,_=>exact field_run_4
  |5,_=>exact field_run_5
  |6,_=>exact field_run_6
  |7,_=>exact field_run_7
  |8,_=>exact field_run_8

theorem fields_bounded (c : Nat) (hc:c < 9) :
    rawBit c < 256 ∧ rankBit c < 256 ∧ rawBit c%64+7 ≤ 64 ∧ rankBit c%64+10 ≤ 64 ∧ (words c).length+1 ≤ 18 := by
  have h:∀c,c < 9 → rawBit c < 256 ∧ rankBit c < 256 ∧ rawBit c%64+7 ≤ 64 ∧ rankBit c%64+10 ≤ 64 ∧ (words c).length+1 ≤ 18:=by decide +kernel
  exact h c hc

theorem field_eval (s : MachineState) (a : BitVec 256) (ha:OutAt s NBUF a) {bit width : Nat}
    (hb:bit < 256) (hw:width ≤ 64) (hfit:bit%64+width ≤ 64) :
    (fieldE bit width).eval s=BitVec.ofNat 64 (a.toNat/2^bit%2^width) := by
  have hm:=ha (bit/64) (by omega)
  simp only[fieldE,ldc,E.eval,cE,hm]
  rw[SearchM.srl_eval _ _ (by omega),SearchM.and_eval,SearchM.ofNat_and_mask _ width hw]
  congr 1
  rw[BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    SearchM.mod64_div_mod _ _ _ hfit,Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 3
  omega

theorem step_field {im : Image} {c : Nat} (hl:LookOK im (look c)) (hc:c < 9)
    (s : MachineState) (hpc:s.pc=pcOf (cbase c)) {a : BitVec 256} (ha:OutAt s NBUF a) :
    ∃t n,Steps im s n n t ∧ n ≤ 18 ∧ t.pc=pcOf (lwuI c) ∧
      t.getReg .x24=BitVec.ofNat 64 (a.toNat/2^(rawBit c)%128) ∧
      t.getReg .x28=BitVec.ofNat 64 (TBL+4*(a.toNat/2^(rankBit c)%1024)) ∧
      RegsExcept s t [.x6,.x24,.x25,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨st,_⟩:=run_pres hl (field_run hc) s hpc (no_obl s) (no_br s)
  obtain ⟨hr,ht,hfr,hft,hn⟩:=fields_bounded c hc
  refine ⟨_,_,st,hn,rfl,?_,?_,?_,fun A _ _=>rfl⟩
  · rw[pres_getReg];exact field_eval s a ha hr (by decide) hfr
  · rw[pres_getReg]
    change BinOp.eval .add (BinOp.eval .sll ((fieldE (rankBit c) 10).eval s) (BitVec.ofNat 64 2)) (BitVec.ofNat 64 TBL)=_
    rw[field_eval s a ha ht (by decide) hft,binop_sll _ _ (by decide),ofNat_shl]
    simp only[BinOp.eval,ofNat_add_ofNat]
    congr 1
    ring
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp)
#print axioms step_field
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedBoundary
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
def forLook (n : Nat) : Option (BitVec 32) :=
  if 20715≤n ∧ n<20743 then tailCode[n-20715]? else trampLook n
def runFor : Option PRes := run forLook [370] 20715 []
theorem runFor_eq : runFor=some expFor := optBeq_eq (show optBeq runFor expFor=true by decide +kernel)
variable {im : Image}
theorem step_SK (hcode : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11175) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf (cbase 0) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 8 * k))) ∧
      (∀ k < 2, t.getMem (BitVec.ofNat 64 (PRIVW + 32 + 8 * k)) = s.getMem (BitVec.ofNat 64 (SK + 16 + 8 * k))) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = PRIVW + 40 ∨ A = PRIVW + 32 ∨ A = PRIVW + 8 ∨ A = PRIVW) := by
  obtain ⟨hst, -⟩ := run_pres hcode runSK_eq s hpc (no_obl s) (no_br s)
  have hm : ∀ a, ((expSK).toState s).getMem a = memEval s expSK.st.mem a := fun a => rfl
  refine ⟨_, hst, rfl, fun k hk => ?_, fun k hk => ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · interval_cases k <;> simp [expSK, pres, memEval_mwc, mwc, memEval_nil', ldc, cE] <;> rfl
  · refine frame_of_memEval hm _ (fun p hp => ?_)
    simp only [expSK, pres, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [mwc, PRIVW, BitVec.toNat_ofNat] <;> decide
theorem step_For (hcode : LookOK im forLook) (s : MachineState) (hpc : s.pc = pcOf 20715) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 370 ∧
      t.getMem (BitVec.ofNat 64 FOUT) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8)) ∧
      t.getMem (BitVec.ofNat 64 (FOUT + 8)) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 8)) ∧
      t.getMem (BitVec.ofNat 64 0x20290) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 16)) ∧
      t.getMem (BitVec.ofNat 64 (0x20290 + 8)) = s.getMem (BitVec.ofNat 64 (FORW + forOff 8 + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = 0x20290 + 8 ∨ A = 0x20290 ∨ A = FOUT + 8 ∨ A = FOUT) := by
  obtain ⟨hst', -⟩ := run_pres hcode runFor_eq s hpc (no_obl s) (no_br s)
  refine ⟨_, hst', rfl, ?_, ?_, ?_, ?_, pres_regsExcept _ _ _ _ _ _ _ s, ?_⟩
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),
      memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao), memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · rw [pres_getMem, memEval_mwc_self _ _ _ _ (by ao)]; rfl
  · refine frame_of_memEval (fun a => rfl) _ (fun q hq => ?_)
    simp only [expFor, pres, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> rw [off_mwc _ _ (by ao)] <;> ao

#print axioms step_SK
#print axioms step_For
end ClaudeWCT.W9.Machine.Sign.SharedBoundary


namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
theorem global_checked (m : Bool) : globalCheck m=true := by cases m;exact global_sign;exact global_expand
theorem field_checked (m : Bool) (k : Nat) (hk:k < 9) : fieldCheck m k=true := by
  have h:(List.range 9).all (fieldCheck m)=true:=by cases m;exact fields_sign;exact fields_expand
  exact List.all_eq_true.mp h k (List.mem_range.mpr hk)
theorem head_run (m d : Bool) : run (look m) [trial m+3,fail m] (trial m) [.br d]=some (expectedHead m d) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  cases d <;> apply optBeq_eq <;> tauto
theorem trial_run (m : Bool) : run (look m) [] (trial m+3) []=some (expectedTrial m) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem gate_run (m d : Bool) : run (look m) [next m,base m+21] (base m+15) [.br d]=some (expectedGate m d) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  cases d <;> apply optBeq_eq <;> tauto
theorem init_run (m : Bool) : run (look m) [firstField m] (base m+21) []=some (expectedInit m) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem cap_run (m d : Bool) : run (look m) [next m,accepted m] (cap m) [.br d]=some (expectedCap m d) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  cases d <;> apply optBeq_eq <;> tauto
theorem next_run (m : Bool) : run (look m) [trial m] (next m) []=some (expectedNext m) := by
  have h:=global_checked m
  simp only[globalCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem rank_run (m : Bool) (k : Nat) (hk:k < 9) (d : Bool) :
    run (look m) [next m,field m k+5] (field m k) [.br d]=some (expectedRank m k d) := by
  have h:=field_checked m k hk
  simp only[fieldCheck,Bool.and_eq_true] at h
  cases d <;> apply optBeq_eq <;> tauto
theorem rankAddr_run (m : Bool) (k : Nat) (hk:k < 9) :
    run (look m) [rankLoad m k] (field m k+5) []=some (expectedRankAddr m k) := by
  have h:=field_checked m k hk
  simp only[fieldCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem corrPrep_run (m : Bool) (k : Nat) (hk:k < 9) :
    run (look m) [corrLoad m k] (rankLoad m k+1) []=some (expectedCorrPrep m k) := by
  have h:=field_checked m k hk
  simp only[fieldCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
theorem sum_run (m : Bool) (k : Nat) (hk:k < 9) :
    run (look m) [field m (k+1)] (corrLoad m k+1) []=some (expectedSum m k) := by
  have h:=field_checked m k hk
  simp only[fieldCheck,Bool.and_eq_true] at h
  apply optBeq_eq;tauto
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

theorem field_eval (s : MachineState) (a : BitVec 256) (ha:OutAt s NBUF a)
    (h17:s.getReg .x17=BitVec.ofNat 64 NBUF) {bit width : Nat}
    (hb:bit < 256) (hw:width ≤ 64) (hfit:bit%64+width ≤ 64) :
    (fieldE bit width).eval s=BitVec.ofNat 64 (a.toNat/2^bit%2^width) := by
  have hm:=ha (bit/64) (by omega)
  simp only[fieldE,E.eval,Addr.toE_eval,fieldAddr,Addr.eval,h17,ofNat_add_ofNat,hm,cE]
  rw[SearchM.srl_eval _ _ (by omega),SearchM.and_eval,SearchM.ofNat_and_mask _ width hw]
  congr 1
  rw[BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
    SearchM.mod64_div_mod _ _ _ hfit,Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 3
  omega

theorem head_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (trial m))
    (i : Nat) (hi:i ≤ 2^21) (h19:s.getReg .x19=BitVec.ofNat 64 i) :
    ∃ t,Steps im s 3 3 t ∧ t.pc=(if i < 2^21 then pcOf (trial m+3) else pcOf (fail m)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hbr : ∀b∈(expectedHead m (decide (2^21 ≤ i))).brs,b.holds s := by
    intro b hb
    simp only[expectedHead,pres,pres2,List.mem_singleton] at hb
    subst hb
    simp only [Br.holds,CmpOp.eval,E.eval,cE,h19,BitVec.ult,toNat_ofNat_lt (by omega : i < 2^64),
      toNat_ofNat_lt (by decide : 2^21 < 2^64)]
    change (!decide (i < 2097152))=decide (2097152 ≤ i)
    by_cases h:i < 2097152
    · have h2:¬2097152 ≤ i:=by omega
      simp [h,h2]
    · have h2:2097152 ≤ i:=by omega
      simp [h,h2]
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (head_run m _) s hpc rfl hbr rfl
  refine ⟨_,hs,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · rw[hp];simp only[expectedHead,pres,pres2]
    simp only [decide_eq_true_eq]
    split_ifs <;> first | rfl | omega
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp)

theorem trial_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (trial m+3))
    (i : Nat) (h19:s.getReg .x19=BitVec.ofNat 64 i) :
    ∃t,Steps im s 9 9 t ∧ fetch im t=some (.base .ECALL) ∧ t.pc=pcOf (base m+14) ∧
      t.getReg .x10=BitVec.ofNat 64 DIG ∧ t.getReg .x11=BitVec.ofNat 64 64 ∧
      t.getReg .x12=BitVec.ofNat 64 NBUF ∧
      t.getMem (BitVec.ofNat 64 (DIG+16))=0 ∧ t.getMem (BitVec.ofNat 64 (DIG+24))=BitVec.ofNat 64 i ∧
      RegsExcept s t [.x10,.x11,.x12,.x28] ∧ Frame s t (fun A=>A=DIG+24 ∨ A=DIG+16) := by
  obtain ⟨hs,hp,he,hr,hm⟩:=SearchM.piece hl (trial_run m) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,he rfl,hp,by rw[hr];rfl,by rw[hr];rfl,by rw[hr];rfl,?_,?_,?_,?_⟩
  · rw[hm]
    change memEval s [mwc (DIG+24) (.reg .x19),mwc (DIG+16) (cE 0)] _=0
    rw[memEval_mwc_ne _ _ _ (by ao) (by ao) (by ao),memEval_mwc_self _ _ _ _ (by ao)]
    rfl
  · rw[hm]
    change memEval s [mwc (DIG+24) (.reg .x19),mwc (DIG+16) (cE 0)] _=BitVec.ofNat 64 i
    rw[memEval_mwc_self _ _ _ _ (by ao)]
    exact h19
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp)
  · refine frame_of_memEval (fun a=>rfl) _ (fun q hq=>?_)
    simp only[expectedTrial,pres,pres2,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> refine ⟨rfl,?_⟩ <;> rw[off_mwc _ _ (by ao)] <;> ao

theorem next_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (next m))
    (i : Nat) (h19:s.getReg .x19=BitVec.ofNat 64 i) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf (trial m) ∧ t.getReg .x19=BitVec.ofNat 64 (i+1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (next_run m) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,hp,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · rw[hr]
    change s.getReg .x19+BitVec.ofNat 64 1=_
    rw[h19,ofNat_add_ofNat]
  · exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp)

#print axioms trial_spec
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {im : Image}

theorem lbu_spec (s : MachineState) (r : Reg) (off : BitVec 12) (A value : Nat)
    (hf:fetch im s=some (.base (.LBU .x6 r off)))
    (hA:s.getReg r+signExtend12 off=BitVec.ofNat 64 A) (hbound:A < MEMORY_BYTES)
    (hbyte:s.getByte (BitVec.ofNat 64 A)=BitVec.ofNat 8 value) (hv:value < 256) :
    ∃t,Steps im s 1 1 t ∧ t.pc=s.pc+4 ∧ t.getReg .x6=BitVec.ofNat 64 value ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hclass:classify (.base (.LBU .x6 r off))=some (.load .bu .x6 r (signExtend12 off)):=rfl
  have hacc:accessValid (s.getReg r+signExtend12 off) LoadKind.bu.width=true := by
    rw[hA]
    simp only[accessValid,rangeValid,LoadKind.width,Bool.and_eq_true,decide_eq_true_eq,
      toNat_ofNat_lt (by unfold MEMORY_BYTES at hbound;omega : A < 2^64),MEMORY_BYTES]
    unfold MEMORY_BYTES at hbound
    omega
  refine ⟨_,Steps.step hf (by rw[classify_sound hclass];simp only[Micro.exec,hacc,if_true];rfl) (Steps.refl _),rfl,?_,?_,?_⟩
  · rw[MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide)]
    simp only[LoadKind.read,hA,hbyte]
    apply BitVec.eq_of_toNat_eq
    simp only[BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro reg hr
    have hn:Reg.x6 ≠ reg:=fun h=>hr (by simp[h])
    rw[MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ hn]
  · intro A _ _;simp

theorem rank_lbu (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (rankLoad m k)) :
    fetch im s=some (.base (.LBU .x6 (addrReg m) 0)) := by
  have hb:rankLoad m k < 50000:=by cases m <;> simp [rankLoad,field,firstField] <;> omega
  have hlook:look m (rankLoad m k)=some (rankLbuWord m) := by
    have h:=field_checked m k hk
    simp only[fieldCheck,Bool.and_eq_true]at h
    have he:(look m (rankLoad m k)==some (rankLbuWord m))=true:=by tauto
    exact eq_of_beq he
  have hpc':(s.pc.toNat < 0x1000 || s.pc.toNat%4 != 0)=false:=by
    rw[hpc,pcOf,toNat_ofNat_lt (by omega)];simp
  have hw:look m ((s.pc.toNat-0x1000)/4)=some (rankLbuWord m):=by
    rw[hpc,pcOf,toNat_ofNat_lt (by omega),show (0x1000+4*rankLoad m k-0x1000)/4=rankLoad m k by omega]
    exact hlook
  apply (fetch_of_look hl hpc' hw s rfl).trans
  cases m <;> rfl

theorem corr_lbu (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (corrLoad m k)) :
    fetch im s=some (.base (.LBU .x6 (addrReg m)
      (BitVec.ofNat 12 (if m then 0 else correctionOffset m k)))) := by
  have hb:corrLoad m k < 50000:=by cases m <;> simp [corrLoad,field,firstField] <;> omega
  have hlook:look m (corrLoad m k)=some (corrLbuWord m k) := by
    have h:=field_checked m k hk
    simp only[fieldCheck,Bool.and_eq_true]at h
    have he:(look m (corrLoad m k)==some (corrLbuWord m k))=true:=by tauto
    exact eq_of_beq he
  have hpc':(s.pc.toNat < 0x1000 || s.pc.toNat%4 != 0)=false:=by
    rw[hpc,pcOf,toNat_ofNat_lt (by omega)];simp
  have hw:look m ((s.pc.toNat-0x1000)/4)=some (corrLbuWord m k):=by
    rw[hpc,pcOf,toNat_ofNat_lt (by omega),show (0x1000+4*corrLoad m k-0x1000)/4=corrLoad m k by omega]
    exact hlook
  apply (fetch_of_look hl hpc' hw s rfl).trans
  cases m <;> simp only[corrLbuWord,correctionOffset,addrReg,Bool.false_eq_true,if_false,if_true]
  · split <;> rfl
  · rfl

#print axioms lbu_spec
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

def gateN (a : BitVec 256) : Nat := a.toNat/2^242%16384
def rankN (a : BitVec 256) (k : Nat) : Nat := a.toNat/2^(SharedField.rankBit k)%1024
def costN (a : BitVec 256) (k : Nat) : Nat := a.toNat/2^(costBit k)%32

theorem geu_holds (s : MachineState) (e : E) (v bound : Nat) (hv:v < 2^64) (hb:bound < 2^64)
    (he:e.eval s=BitVec.ofNat 64 v) : (Br.mk .geu e (cE bound) (decide (¬v < bound))).holds s := by
  simp only[Br.holds,CmpOp.eval,E.eval,cE,he,BitVec.ult,toNat_ofNat_lt hv,toNat_ofNat_lt hb]
  by_cases h:v < bound <;> simp only[h,not_true_eq_false,not_false_eq_true,decide_true,decide_false,
    Bool.not_true,Bool.not_false]

theorem gate_eval (s : MachineState) (a : BitVec 256) (ha:OutAt s NBUF a) :
    gateE.eval s=BitVec.ofNat 64 (gateN a) := by
  have h3:s.getMem (BitVec.ofNat 64 (NBUF+24))=a.extractLsb' 192 64:=ha 3 (by decide)
  simp only[gateE,ldc,cE,E.eval,h3]
  rw[SearchM.srl_eval _ 50 (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw[SigGolfCandidate.Research.V7Composed198Gate.gate_shift50_toNat,toNat_ofNat_lt (by unfold gateN;omega)]
  rfl

theorem gate_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (base m+15))
    (a : BitVec 256) (ha:OutAt s NBUF a) :
    ∃t,Steps im s 6 6 t ∧ t.pc=(if gateN a < 734 then pcOf (base m+21) else pcOf (next m)) ∧
      (m=true → t.getReg .x17=BitVec.ofNat 64 NBUF) ∧
      RegsExcept s t [.x6,.x7,.x17,.x28] ∧ Frame s t (fun _=>False) := by
  have hbr:∀b∈(expectedGate m (decide (¬gateN a < 734))).brs,b.holds s:=by
    intro b hb
    simp only[expectedGate,pres,pres2,List.mem_singleton]at hb
    subst hb
    exact geu_holds s gateE (gateN a) 734 (by unfold gateN;omega) (by decide) (gate_eval s a ha)
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (gate_run m _) s hpc rfl hbr rfl
  refine ⟨_,hs,?_,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · rw[hp];simp only[expectedGate,pres,pres2,decide_eq_true_eq]
    split_ifs <;> first | rfl | contradiction
  · intro hm;subst m;rw[hr];rfl
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem init_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (base m+21))
    (h17:m=true → s.getReg .x17=BitVec.ofNat 64 NBUF) :
    ∃t,Steps im s (if m then 3 else 5) (if m then 3 else 5) t ∧ t.pc=pcOf (firstField m) ∧
      t.getReg (sumReg m)=0 ∧ t.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m) ∧
      t.getReg .x17=BitVec.ofNat 64 NBUF ∧ RegsExcept s t [.x17,.x20,.x21] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (init_run m) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,hp,?_,?_,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · cases m <;> rw[hr] <;> rfl
  · cases m <;> rw[hr] <;> rfl
  · cases m
    · rw[hr];rfl
    · rw[hr];exact h17 rfl
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem fields_bounded (k : Nat) (hk:k < 9) :
    SharedField.rankBit k < 256 ∧ SharedField.rankBit k%64+10 ≤ 64 ∧ costBit k < 256 ∧ costBit k%64+5 ≤ 64 := by
  have h:∀k,k < 9 → SharedField.rankBit k < 256 ∧ SharedField.rankBit k%64+10 ≤ 64 ∧ costBit k < 256 ∧ costBit k%64+5 ≤ 64:=by decide +kernel
  exact h k hk

theorem field_valid (s : MachineState) (h17:s.getReg .x17=BitVec.ofNat 64 NBUF)
    (bit : Nat) (hb:bit < 256) : (Oblig.valid (fieldAddr bit) 8).holds s := by
  exact valid_ofNat h17 (by unfold NBUF;omega) (by unfold NBUF MEMORY_BYTES;omega)

theorem rank_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (field m k)) (a : BitVec 256) (ha:OutAt s NBUF a)
    (h17:s.getReg .x17=BitVec.ofNat 64 NBUF) :
    ∃t,Steps im s 5 5 t ∧ t.pc=(if rankN a k < 563 then pcOf (field m k+5) else pcOf (next m)) ∧
      t.getReg (rankReg m)=BitVec.ofNat 64 (rankN a k) ∧ RegsExcept s t [.x6,.x24,.x25] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hb,hfit,-,-⟩:=fields_bounded k hk
  have he:(rankE k).eval s=BitVec.ofNat 64 (rankN a k):=field_eval s a ha h17 hb (by decide) hfit
  have hbr:∀b∈(expectedRank m k (decide (¬rankN a k < 563))).brs,b.holds s:=by
    intro b hb
    simp only[expectedRank,pres,pres2,List.mem_singleton]at hb
    subst hb
    exact geu_holds s (rankE k) (rankN a k) 563 (by unfold rankN;omega) (by decide) he
  obtain ⟨hst,-⟩:=run_pres hl (rank_run m k hk _) s hpc (by
    intro ob ho
    simp only[expectedRank,pres,pres2,List.mem_singleton]at ho
    subst ho
    exact field_valid s h17 _ hb) hbr
  refine ⟨_,hst,?_,?_,?_,fun A _ _=>rfl⟩
  · change pcOf (if decide (¬rankN a k < 563) then next m else field m k+5)=_
    simp only[decide_eq_true_eq]
    split_ifs <;> first | rfl | contradiction
  · cases m <;> rw[pres_getReg] <;> exact he
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem cap_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState) (hpc:s.pc=pcOf (cap m))
    (total : Nat) (ht:total < 2^64) (hs:s.getReg (sumReg m)=BitVec.ofNat 64 total) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if total ≤ 778 then pcOf (accepted m) else pcOf (next m)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hbr:∀b∈(expectedCap m (decide (¬total < 779))).brs,b.holds s:=by
    intro b hb
    simp only[expectedCap,pres,pres2,List.mem_singleton]at hb
    subst hb
    exact geu_holds s (.reg (sumReg m)) total 779 ht (by decide) hs
  obtain ⟨st,hp,-,hr,hm⟩:=SearchM.piece hl (cap_run m _) s hpc rfl hbr rfl
  refine ⟨_,st,?_,(pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg]),fun A _ _=>by rw[hm];rfl⟩
  rw[hp];simp only[expectedCap,pres,pres2,decide_eq_true_eq]
  split_ifs <;> first | rfl | omega

#print axioms rank_spec
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
/-- C1 (stage 1): `2 - skips′` per class `p mod 32`, the same table for A and for B/C. -/
def correctionA : List Nat := [2, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 2]
def correctionB : List Nat := [2, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 2]
def rankByte (f : Nat) : Nat := WCT9.routineCosts.getD f 0
 def correctionByte (k j : Nat) : Nat := (if SharedLeaf.first k then correctionA else correctionB).getD j 0
 structure TablesAt (m : Bool) (s : MachineState) : Prop where
   ranks : ∀f,f < 563 → s.getByte (BitVec.ofNat 64 (tableBase m+f))=BitVec.ofNat 8 (rankByte f)
   corrections : ∀k,k < 9 → ∀j,j < 32 →
     s.getByte (BitVec.ofNat 64 (tableBase m+correctionOffset m k+j))=BitVec.ofNat 8 (correctionByte k j)
 theorem rankByte_lt (f : Nat) (hf:f < 563) : rankByte f < 256 := by
   unfold rankByte
   have hfl:f < WCT9.routineCosts.length:=by rw[WCT9.routineCosts_length];exact hf
   rw[List.getD_eq_getElem _ _ hfl]
   have h:=(WCT9.routineCosts_bounds _ (List.getElem_mem hfl)).2
   omega
 theorem correctionByte_lt (k j : Nat) (hk:k < 9) (hj:j < 32) : correctionByte k j < 256 := by
   have h:∀k,k < 9 → ∀j,j < 32 → correctionByte k j < 256:=by decide +kernel
   exact h k hk j hj
 def writes (A : Nat) : Prop := A=DIG+16 ∨ A=DIG+24 ∨ (NBUF ≤ A ∧ A < NBUF+32)
 def regs : List Reg := [.x6,.x7,.x10,.x11,.x12,.x17,.x19,.x20,.x21,.x24,.x25,.x28]
 theorem TablesAt.frame {m : Bool} {s t : MachineState} (hs:TablesAt m s) (hf:Frame s t writes) : TablesAt m t := by
   constructor
   · intro f hff
     rw[hf.getByte (by cases m <;> unfold tableBase <;> simp <;> omega) (by cases m <;> simp[tableBase,writes,DIG,NBUF] <;> omega)]
     exact hs.ranks f hff
   · intro k hk j hj
     have ho:correctionOffset m k ≤ 1568:=by unfold correctionOffset;split <;> split <;> omega
     rw[hf.getByte (by cases m <;> unfold tableBase <;> simp <;> omega) (by cases m <;> simp only[tableBase,writes,DIG,NBUF,Bool.false_eq_true,if_false,if_true] <;> omega)]
     exact hs.corrections k hk j hj
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

theorem rankAddr_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (field m k+5)) (r : Nat)
    (ht:s.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m)) (hr:s.getReg (rankReg m)=BitVec.ofNat 64 r) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf (rankLoad m k) ∧
      t.getReg (addrReg m)=BitVec.ofNat 64 (tableBase m+r) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,hp,-,hreg,hm⟩:=SearchM.piece hl (rankAddr_run m k hk) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,hp,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · cases m <;> rw[hreg] <;> change s.getReg _+s.getReg _=_ <;> rw[ht,hr,ofNat_add_ofNat]
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem corrPrep_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (rankLoad m k+1)) (a : BitVec 256) (ha:OutAt s NBUF a)
    (h17:s.getReg .x17=BitVec.ofNat 64 NBUF) (ht:s.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m))
    (sum value : Nat) (hsum:s.getReg (sumReg m)=BitVec.ofNat 64 sum) (h6:s.getReg .x6=BitVec.ofNat 64 value) :
    ∃t,Steps im s (if m then 7 else 5) (if m then 7 else 5) t ∧ t.pc=pcOf (corrLoad m k) ∧
      t.getReg (sumReg m)=BitVec.ofNat 64 (sum+value) ∧
      t.getReg (addrReg m)=BitVec.ofNat 64 (tableBase m+costN a k+(if m then correctionOffset m k else 0)) ∧
      RegsExcept s t [sumReg m,.x6,.x24,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨-, -, hb,hfit⟩:=fields_bounded k hk
  have he:(costE k).eval s=BitVec.ofNat 64 (costN a k):=field_eval s a ha h17 hb (by decide) hfit
  obtain ⟨st,-⟩:=run_pres hl (corrPrep_run m k hk) s hpc (by
    intro ob ho
    simp only[expectedCorrPrep,pres,pres2,List.mem_singleton]at ho
    subst ho
    exact field_valid s h17 _ hb) (no_br s)
  refine ⟨_,st,rfl,?_,?_,?_,fun A _ _=>rfl⟩
  · cases m <;> rw[pres_getReg] <;> change s.getReg _+s.getReg .x6=_ <;> rw[hsum,h6,ofNat_add_ofNat]
  · cases m
    · rw[pres_getReg]
      change s.getReg (tableReg false)+(costE k).eval s=_
      rw[ht,he,ofNat_add_ofNat]
      rfl
    · rw[pres_getReg]
      change (costE k).eval s+BitVec.ofNat 64 (tableBase true+correctionOffset true k)=_
      rw[he,ofNat_add_ofNat]
      congr 1
      simp only[if_true]
      omega
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

theorem sum_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (corrLoad m k+1)) (total value : Nat)
    (hs:s.getReg (sumReg m)=BitVec.ofNat 64 total) (hv:s.getReg .x6=BitVec.ofNat 64 value) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf (field m (k+1)) ∧ t.getReg (sumReg m)=BitVec.ofNat 64 (total+value) ∧
      RegsExcept s t [sumReg m] ∧ Frame s t (fun _=>False) := by
  obtain ⟨st,hp,-,hr,hm⟩:=SearchM.piece hl (sum_run m k hk) s hpc rfl (no_br s) rfl
  refine ⟨_,st,hp,?_,?_,fun A _ _=>by rw[hm];rfl⟩
  · cases m <;> rw[hr] <;> change s.getReg _+s.getReg .x6=_ <;> rw[hs,hv,ofNat_add_ofNat]
  · cases m <;> exact (pres_regsExcept _ _ _ _ _ _ _ s).mono (by simp [rankReg,addrReg,sumReg])

#print axioms corrPrep_spec
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}

theorem out_frame {s t : MachineState} {a : BitVec 256} (h:OutAt s NBUF a) (hf:Frame s t (fun _=>False)) :
    OutAt t NBUF a := fun j hj=>by rw[hf.get (by unfold NBUF;omega) (fun h=>h)];exact h j hj
theorem TablesAt.frameEmpty {m : Bool} {s t : MachineState} (h:TablesAt m s) (hf:Frame s t (fun _=>False)) :
    TablesAt m t := h.frame (hf.mono (fun _ _ h=>h.elim))

theorem cost_spec (m : Bool) (k : Nat) (hk:k < 9) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (field m k+5)) (a : BitVec 256) (ha:OutAt s NBUF a) (hc:TablesAt m s)
    (h17:s.getReg .x17=BitVec.ofNat 64 NBUF) (ht:s.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m))
    (hr:s.getReg (rankReg m)=BitVec.ofNat 64 (rankN a k)) (hf:rankN a k < 563)
    (total : Nat) (hs:s.getReg (sumReg m)=BitVec.ofNat 64 total) :
    ∃t n,Steps im s n n t ∧ n ≤ 11 ∧ t.pc=pcOf (field m (k+1)) ∧
      t.getReg (sumReg m)=BitVec.ofNat 64 (total+rankByte (rankN a k)+correctionByte k (costN a k)) ∧
      RegsExcept s t [sumReg m,.x6,.x24,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t1,st1,p1,addr1,r1,f1⟩:=rankAddr_spec m k hk hl s hpc _ ht hr
  have c1:=hc.frameEmpty f1
  obtain ⟨t2,st2,p2,v2,r2,f2⟩:=lbu_spec t1 (addrReg m) 0 (tableBase m+rankN a k) (rankByte (rankN a k))
    (rank_lbu m k hk hl t1 p1) (by rw[addr1];simp [signExtend12])
    (by cases m <;> simp [tableBase,MEMORY_BYTES] <;> omega) (c1.ranks _ hf) (rankByte_lt _ hf)
  have p2':t2.pc=pcOf (rankLoad m k+1):=by rw[p2,p1];exact pcOf_add4 _
  have c2:=c1.frameEmpty f2
  have r12:=r1.trans r2
  obtain ⟨t3,st3,p3,sum3,addr3,r3,f3⟩:=corrPrep_spec m k hk hl t2 p2' a (out_frame (out_frame ha f1) f2)
    (by rw[r12.get (by simp)];exact h17)
    (by rw[r12.get (by cases m <;> simp [tableReg])];exact ht)
    total (rankByte (rankN a k)) (by rw[r12.get (by cases m <;> simp [sumReg])];exact hs) v2
  have c3:=c2.frameEmpty f3
  have hlo:costN a k < 32:=Nat.mod_lt _ (by decide)
  have hoff:signExtend12 (BitVec.ofNat 12 (if m then 0 else correctionOffset m k))=
      BitVec.ofNat 64 (if m then 0 else correctionOffset m k) := by
    cases m <;> simp only[correctionOffset,Bool.false_eq_true,if_false,if_true]
    · split <;> decide +kernel
    · decide +kernel
  have ho:correctionOffset m k ≤ 1568:=by unfold correctionOffset;split <;> split <;> omega
  obtain ⟨t4,st4,p4,v4,r4,f4⟩:=lbu_spec t3 (addrReg m)
    (BitVec.ofNat 12 (if m then 0 else correctionOffset m k))
    (tableBase m+correctionOffset m k+costN a k) (correctionByte k (costN a k))
    (corr_lbu m k hk hl t3 p3) (by rw[addr3,hoff,ofNat_add_ofNat];congr 1;cases m <;> simp <;> omega)
    (by cases m <;> simp [tableBase,MEMORY_BYTES] <;> omega)
    (c3.corrections k hk _ hlo) (correctionByte_lt k _ hk hlo)
  have p4':t4.pc=pcOf (corrLoad m k+1):=by rw[p4,p3];exact pcOf_add4 _
  obtain ⟨t5,st5,p5,sum5,r5,f5⟩:=sum_spec m k hk hl t4 p4' (total+rankByte (rankN a k)) _
    (by rw[r4.get (by cases m <;> simp[sumReg])];exact sum3) v4
  refine ⟨t5,1+1+(if m then 7 else 5)+1+1,(((st1.trans st2).trans st3).trans st4).trans st5,?_,p5,sum5,?_,?_⟩
  · cases m <;> decide
  · exact ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by simp)
  · exact ((((f1.trans f2).trans f3).trans f4).trans f5).mono (fun A _ h=>by simpa using h)

#print axioms cost_spec
end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
variable {im : Image}
attribute [local instance] Classical.propDecidable

def psum (a : BitVec 256) (n : Nat) : Nat :=
  ((List.range n).map (fun k=>rankByte (rankN a k)+correctionByte k (costN a k))).sum
theorem psum_succ (a : BitVec 256) (k : Nat) :
    psum a (k+1)=psum a k+rankByte (rankN a k)+correctionByte k (costN a k) := by
  simp [psum,List.range_succ,List.map_append,List.sum_append,Nat.add_assoc]
theorem rankByte_lt_all (f : Nat) : rankByte f < 256 := by
  by_cases hf:f < 563
  · exact rankByte_lt f hf
  · unfold rankByte
    rw[List.getD_eq_default _ _ (by rw[WCT9.routineCosts_length];omega)]
    decide
theorem psum_le (a : BitVec 256) (n : Nat) (hn:n ≤ 9) : psum a n ≤ 512*n := by
  induction n with
  | zero=>simp [psum]
  | succ n ih=>
    rw[psum_succ]
    have h1:=rankByte_lt_all (rankN a n)
    have h2:=correctionByte_lt n (costN a n) (by omega) (Nat.mod_lt _ (by decide))
    have h3:=ih (by omega)
    omega

theorem fields_from (m : Bool) (hl:LookOK im (look m)) (a : BitVec 256) :
    ∀ n k,k+n=9 → ∀s : MachineState,s.pc=pcOf (field m k) → OutAt s NBUF a → TablesAt m s →
      s.getReg .x17=BitVec.ofNat 64 NBUF → s.getReg (tableReg m)=BitVec.ofNat 64 (tableBase m) →
      s.getReg (sumReg m)=BitVec.ofNat 64 (psum a k) →
      ∃t c,Steps im s c c t ∧ c ≤ 16*n ∧ RegsExcept s t [sumReg m,.x6,.x24,.x25,.x28] ∧
        Frame s t (fun _=>False) ∧
        (if ∀k',k' < 9 → k ≤ k' → rankN a k' < 563 then
          t.pc=pcOf (cap m) ∧ t.getReg (sumReg m)=BitVec.ofNat 64 (psum a 9) else t.pc=pcOf (next m)) := by
  intro n
  induction n with
  | zero=>
    intro k hk s hpc _ _ _ _ hs
    have h:k=9:=by omega
    subst k
    refine ⟨s,0,Steps.refl _,by omega,RegsExcept.refl _ _,Frame.refl _ _,?_⟩
    rw[if_pos (by intro k' hk' hle;omega)]
    exact ⟨hpc,hs⟩
  | succ n ih=>
    intro k hk s hpc ha hc h17 ht hs
    have hk9:k < 9:=by omega
    obtain ⟨t1,s1,p1,v1,r1,f1⟩:=rank_spec m k hk9 hl s hpc a ha h17
    by_cases hrank:rankN a k < 563
    · rw[if_pos hrank]at p1
      obtain ⟨t2,c2,s2,hc2,p2,v2,r2,f2⟩:=cost_spec m k hk9 hl t1 p1 a (out_frame ha f1)
        (hc.frameEmpty f1) (by rw[r1.get (by simp)];exact h17)
        (by rw[r1.get (by cases m <;> simp[tableReg])];exact ht) v1 hrank (psum a k)
        (by rw[r1.get (by cases m <;> simp[sumReg])];exact hs)
      have r12:=r1.trans r2
      obtain ⟨t3,c3,s3,hc3,r3,f3,p3⟩:=ih (k+1) (by omega) t2 p2 (out_frame (out_frame ha f1) f2)
        ((hc.frameEmpty f1).frameEmpty f2) (by rw[r12.get (by cases m <;> simp[sumReg])];exact h17)
        (by rw[r12.get (by cases m <;> simp[tableReg,sumReg])];exact ht) (by rw[v2,psum_succ])
      refine ⟨t3,5+c2+c3,(s1.trans s2).trans s3,by omega,(r12.trans r3).mono (by simp),
        ((f1.trans f2).trans f3).mono (fun A _ h=>by simpa using h),?_⟩
      have hiff:(∀j,j < 9 → k ≤ j → rankN a j < 563) ↔ (∀j,j < 9 → k+1 ≤ j → rankN a j < 563) := by
        constructor
        · intro h j hj hle;exact h j hj (by omega)
        · intro h j hj hle
          by_cases he:j=k
          · subst j;exact hrank
          · exact h j hj (by omega)
      by_cases hall:∀j,j < 9 → k+1 ≤ j → rankN a j < 563
      · rw[if_pos hall]at p3
        rw[if_pos (hiff.mpr hall)]
        exact p3
      · rw[if_neg hall]at p3
        rw[if_neg (fun h=>hall (hiff.mp h))]
        exact p3
    · rw[if_neg hrank]at p1
      refine ⟨t1,5,s1,by omega,r1.mono (by simp),f1,?_⟩
      rw[if_neg (fun h=>hrank (h k hk9 le_rfl))]
      exact p1

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
variable {im : Image}

def acceptedTest (a : BitVec 256) : Bool := decide (gateN a < 734) &&
  (List.range 9).all (fun k=>decide (rankN a k < 563)) && decide (psum a 9 ≤ 778)
theorem acceptedTest_iff (a : BitVec 256) : acceptedTest a=true ↔
    gateN a < 734 ∧ (∀k,k < 9 → rankN a k < 563) ∧ psum a 9 ≤ 778 := by
  simp only[acceptedTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,and_assoc]

theorem checks_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (base m+15)) (a : BitVec 256) (ha:OutAt s NBUF a) (hc:TablesAt m s) :
    ∃t c,Steps im s c c t ∧ c ≤ 157 ∧ RegsExcept s t [.x6,.x7,.x17,.x20,.x21,.x24,.x25,.x28] ∧
      Frame s t (fun _=>False) ∧ t.pc=(if acceptedTest a then pcOf (accepted m) else pcOf (next m)) ∧
      (acceptedTest a=true → t.getReg .x17=BitVec.ofNat 64 NBUF) := by
  obtain ⟨t1,s1,p1,r17,r1,f1⟩:=gate_spec m hl s hpc a ha
  by_cases hg:gateN a < 734
  · rw[if_pos hg]at p1
    obtain ⟨t2,s2,p2,sm2,tb2,r172,r2,f2⟩:=init_spec m hl t1 p1 r17
    obtain ⟨t3,c3,s3,b3,r3,f3,p3⟩:=fields_from m hl a 9 0 rfl t2 p2
      (out_frame (out_frame ha f1) f2) ((hc.frameEmpty f1).frameEmpty f2) r172 tb2 sm2
    have hall:(∀k,k < 9 → 0 ≤ k → rankN a k < 563) ↔ (∀k,k < 9 → rankN a k < 563) := by simp
    by_cases hf:∀k,k < 9 → rankN a k < 563
    · rw[if_pos (hall.mpr hf)]at p3
      obtain ⟨t4,s4,p4,r4,f4⟩:=cap_spec m hl t3 p3.1 (psum a 9) (by have:=psum_le a 9 (by omega);omega) p3.2
      refine ⟨t4,6+(if m then 3 else 5)+c3+2,((s1.trans s2).trans s3).trans s4,?_,?_,?_,?_,?_⟩
      · cases m <;> simp at * <;> omega
      · exact (((r1.trans r2).trans r3).trans r4).mono (by cases m <;> simp [sumReg])
      · exact (((f1.trans f2).trans f3).trans f4).mono (fun A _ h=>by simpa using h)
      · rw[p4]
        have he:(acceptedTest a=true) ↔ psum a 9 ≤ 778:=by
          constructor
          · intro h;exact ((acceptedTest_iff a).mp h).2.2
          · intro h;exact (acceptedTest_iff a).mpr ⟨hg,hf,h⟩
        simp only[he]
      · intro _
        rw [r4.get (by cases m <;> simp [sumReg]),r3.get (by cases m <;> simp [sumReg])]
        exact r172
    · rw[if_neg (fun h=>hf (hall.mp h))]at p3
      refine ⟨t3,6+(if m then 3 else 5)+c3,(s1.trans s2).trans s3,?_,?_,?_,?_,?_⟩
      · cases m <;> simp at * <;> omega
      · exact ((r1.trans r2).trans r3).mono (by cases m <;> simp [sumReg])
      · exact ((f1.trans f2).trans f3).mono (fun A _ h=>by simpa using h)
      · rw[if_neg (fun h=>hf ((acceptedTest_iff a).mp h).2.1)]
        exact p3
      · intro ha
        exact False.elim (hf ((acceptedTest_iff a).mp ha).2.1)
  · rw[if_neg hg]at p1
    refine ⟨t1,6,s1,by omega,r1.mono (by simp),f1,?_,?_⟩
    · rw[if_neg (fun h=>hg ((acceptedTest_iff a).mp h).1)]
      exact p1
    · intro ha
      exact False.elim (hg ((acceptedTest_iff a).mp ha).1)

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem correctionByte_canonical (k : Fin 9) (j : Fin 32) :
    correctionByte k.val j.val=(if SharedForest.firstCoord k.val then SharedForest.aCorrection j.val
      else SharedForest.bCorrection j.val) := by
  have h:∀k : Fin 9,∀j : Fin 32,correctionByte k.val j.val=(if SharedForest.firstCoord k.val then
    SharedForest.aCorrection j.val else SharedForest.bCorrection j.val):=by decide +kernel
  exact h k j
theorem correctionByte_field (a : BitVec 256) (k : Fin 9) :
    correctionByte k.val (costN a k.val)=SharedForest.accountingCorrection k.val (SharedForest.rawChildFromOutput a k) := by
  rw[SharedForest.accountingCorrection_field]
  exact correctionByte_canonical k (SharedForest.costField a k)
theorem rankByte_source (a : BitVec 256) (k : Fin 9) (hk:rankN a k.val < 563) :
    rankByte (rankN a k.val)=WCT9.routineCost (SharedForest.forestRank a k.val) := by
  have hr:(SharedForest.forestRank a k.val).val=rankN a k.val := by
    change rankN a k.val % 563=rankN a k.val
    exact Nat.mod_eq_of_lt hk
  unfold rankByte WCT9.routineCost
  simp only [hr]
  rw[List.getD_eq_getElem _ _ (by rw[WCT9.routineCosts_length];exact hk)]

theorem psum_source (a : BitVec 256) (h:∀k,k < 9 → rankN a k < 563) :
    psum a 9=SharedForest.jointAccountingCost a := by
  unfold psum SharedForest.jointAccountingCost SharedForest.coordinateAccountingCost
  have hr:List.range 9=(List.finRange 9).map Fin.val:=by decide
  rw[hr,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  simp only[Function.comp_def,rankByte_source a k (h k.val k.isLt),correctionByte_field]

theorem acceptedTest_source (a : BitVec 256) : acceptedTest a=SharedForest.digestAccepted a := by
  apply Bool.eq_iff_iff.mpr
  rw[acceptedTest_iff]
  have hr:SharedForest.ranksAccepted a=true ↔ (∀k,k < 9 → rankN a k < 563) := by
    simp only[SharedForest.ranksAccepted,List.all_eq_true,decide_eq_true_eq,List.mem_finRange,forall_const]
    constructor
    · intro h k hk;exact h ⟨k,hk⟩
    · intro h k;exact h k.val k.isLt
  simp only[SharedForest.digestAccepted,Bool.and_eq_true,decide_eq_true_eq,hr,and_assoc]
  constructor
  · rintro ⟨hg,hf,hc⟩
    exact ⟨hg,hf,by rwa[←psum_source a hf]⟩
  · rintro ⟨hg,hf,hc⟩
    exact ⟨hg,hf,by rwa[psum_source a hf]⟩

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
structure Pre (m : Bool) (rho : BitVec 128) (msg : SigGolfCandidate.T3.Message) (s : MachineState) : Prop where
  x5 : s.getReg .x5=0
  rho : DigAt s DIG rho
  msg : ∀k,k < 4 → s.getMem (BitVec.ofNat 64 (DIG+32+8*k))=msg.extractLsb' (64*k) 64
  tables : TablesAt m s
structure LoopInv (m : Bool) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (trial m)
  hi : i ≤ 2^21
  x19 : t.getReg .x19=BitVec.ofNat 64 i
  regs : RegsExcept s0 t regs
  frame : Frame s0 t writes
structure Post (m : Bool) (s0 : MachineState) (r : Option (BitVec 32 × BitVec 256)) (t : MachineState) : Prop where
  x5 : t.getReg .x5=0
  regs : RegsExcept s0 t regs
  frame : Frame s0 t writes
  result : match r with
    | none => t.pc=pcOf (fail m) ∧ t.getReg .x19=BitVec.ofNat 64 (2^21)
    | some (c,a) => t.pc=pcOf (accepted m) ∧ t.getReg .x19=BitVec.ofNat 64 c.toNat ∧
      c.toNat < 2^21 ∧ SharedForest.digestAccepted a=true ∧ OutAt t NBUF a

  resultR17 : match r with
    | none => True
    | some _ => t.getReg .x17=BitVec.ofNat 64 NBUF

variable {im : Image} {sk : BitVec 256}
theorem loop (m : Bool) (hl : LookOK im (look m)) {s0 : MachineState} {rho : BitVec 128} {msg : SigGolfCandidate.T3.Message}
    (hpre : Pre m rho msg s0) :
    ∀F i t,i+F=2^21 → LoopInv m s0 i t →
      TBSim im sk t (F*200+10) (SharedForest.sharedDigestSearch rho msg i F) (Post m s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1,s1,p1,r1,f1⟩:=head_spec m hl t hI.pc i hI.hi hI.x19
    rw[if_neg (by omega)] at p1
    have rr : RegsExcept s0 t1 regs := (hI.regs.trans r1).mono (by simp[regs])
    have ff : Frame s0 t1 writes := (hI.frame.trans f1).mono (fun A _ hh=>hh.elim id False.elim)
    have hp : Post m s0 none t1 := ⟨by rw[rr.get (by decide),hpre.x5],rr,ff,⟨p1,by
      have hiEq:i=2^21:=by omega
      rw[r1.get (by decide),hI.x19,hiEq]⟩,trivial⟩
    exact (TBSim.pure_steps' (sk:=sk) s1 hp).mono (by omega) (fun _ _ hh=>hh)
  | succ F ih =>
    intro i t h hI
    have hi:i < 2^21:=by omega
    have hc:(BitVec.ofNat 32 i).toNat=i:=by rw[BitVec.toNat_ofNat];omega
    obtain ⟨t1,s1,p1,r1,f1⟩:=head_spec m hl t hI.pc i hI.hi hI.x19
    rw[if_pos hi]at p1
    obtain ⟨u,s2,hfu,p2,h10,h11,h12,h16,h24,r2,f2⟩:=trial_spec m hl t1 p1 i
      (by rw[r1.get (by decide),hI.x19])
    have ru : RegsExcept s0 u regs := ((hI.regs.trans r1).trans r2).mono (by decide)
    have fu : Frame s0 u writes := ((hI.frame.trans f1).trans f2).mono (fun A _ hA=>by
      rcases hA with (hA|hA)|hA
      · exact hA
      · exact hA.elim
      · unfold writes;rcases hA with hA|hA <;> simp[hA])
    have mem : ∀A,A < 2^64 → ¬writes A → u.getMem (BitVec.ofNat 64 A)=s0.getMem (BitVec.ofNat 64 A):=
      fun A hA hn=>fu.get hA hn
    have nw:∀A,A=DIG ∨ A=DIG+8 ∨ A=DIG+32 ∨ A=DIG+40 ∨ A=DIG+48 ∨ A=DIG+56 → ¬writes A:=by
      intro A hA;simp only[writes,DIG,NBUF]at hA ⊢;omega
    have hm0:s0.getMem (BitVec.ofNat 64 (DIG+32))=msg.extractLsb' 0 64:=hpre.msg 0 (by decide)
    have hm1:s0.getMem (BitVec.ofNat 64 (DIG+40))=msg.extractLsb' 64 64:=hpre.msg 1 (by decide)
    have hm2:s0.getMem (BitVec.ofNat 64 (DIG+48))=msg.extractLsb' 128 64:=hpre.msg 2 (by decide)
    have hm3:s0.getMem (BitVec.ofNat 64 (DIG+56))=msg.extractLsb' 192 64:=hpre.msg 3 (by decide)
    have hq:hashInput u=toQ (SigGolfCandidate.T3.pad64
        (SigGolfCandidate.T3.digestInput rho msg (BitVec.ofNat 32 i))):=by
      refine hashInput_toQ u _ 0 DIG (by rw[SearchM.pad64_digestInput',SearchM.digestInput_length']) h10
        (by decide) (by decide) h11 (by decide) ?_
      rw[readWords_eight,SearchM.wordsOf_digestInput',hc,h16,h24,
        mem DIG (by decide) (nw _ (by omega)),mem (DIG+8) (by decide) (nw _ (by omega)),
        mem (DIG+32) (by decide) (nw _ (by omega)),mem (DIG+40) (by decide) (nw _ (by omega)),
        mem (DIG+48) (by decide) (nw _ (by omega)),mem (DIG+56) (by decide) (nw _ (by omega)),
        hpre.rho.1,hpre.rho.2,hm0,hm1,hm2,hm3]
      rfl
    have hv:hashArgumentsValid u=true:=hashArgs_const u DIG 64 NBUF h10 h11 h12
      (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5:u.getReg .x5=0:=by rw[ru.get (by decide),hpre.x5]
    have prog:SharedForest.sharedDigestSearch rho msg i (F+1)=
        (SigGolfCandidate.T3.publicHash (SigGolfCandidate.T3.digestInput rho msg (BitVec.ofNat 32 i)) >>= fun output=>
          if SharedForest.digestAccepted output=true then pure (some (BitVec.ofNat 32 i,output))
          else SharedForest.sharedDigestSearch rho msg (i+1) F):=rfl
    rw[prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind' hfu h5 hv hq
      (W:=159+(F*200+10)) (fun a=>?_))).mono ?_ (fun _ _ hh=>hh)
    swap
    · rw[SearchM.blocks_digestInput'];omega
    have pw:(writeHash u a).pc=pcOf (base m+15):=by rw[pc_writeHash,p2,pcOf_add4]
    have hN:OutAt (writeHash u a) NBUF a:=SearchM.outAt_writeHash u a h12
    have fw:=Frame.writeHash u a NBUF h12 (by decide)
    have fuw:Frame s0 (writeHash u a) writes:=(fu.trans fw).mono (fun A _ hA=>by
      rcases hA with hA|hA
      · exact hA
      · exact Or.inr (Or.inr hA))
    obtain ⟨v,c,sv,hcv,rv,fv,pv,vr17⟩:=checks_spec m hl (writeHash u a) pw a hN (hpre.tables.frame fuw)
    rw[acceptedTest_source]at pv vr17
    have rv':RegsExcept s0 v regs:=
      ((ru.trans (fun r _=>getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans rv).mono (by decide)
    have fv':Frame s0 v writes:=(fuw.trans fv).mono (fun A _ hA=>hA.elim id False.elim)
    have hNv:OutAt v NBUF a:=out_frame hN fv
    have x19v:v.getReg .x19=BitVec.ofNat 64 i:=by
      rw[rv.get (by decide),getReg_writeHash,r2.get (by decide),r1.get (by decide),hI.x19]
    by_cases hadm:SharedForest.digestAccepted a=true
    · rw[if_pos hadm]at pv
      simp only[hadm,↓reduceIte]
      have hp:Post m s0 (some (BitVec.ofNat 32 i,a)) v:=⟨by rw[rv'.get (by decide),hpre.x5],rv',fv',
        ⟨pv,by rw[hc];exact x19v,by rw[hc];exact hi,hadm,hNv⟩,vr17 hadm⟩
      exact (TBSim.pure_steps' sv hp).mono (by omega) (fun _ _ hh=>hh)
    · rw[if_neg hadm]at pv
      simp only[hadm,↓reduceIte]
      obtain ⟨w,sw,pw',x19w,rw',fw'⟩:=next_spec m hl v pv i x19v
      have hI':LoopInv m s0 (i+1) w:=⟨pw',by omega,x19w,(rv'.trans rw').mono (by decide),
        (fv'.trans fw').mono (fun A _ hA=>hA.elim id False.elim)⟩
      exact (TBSim.steps (sv.trans sw) (ih (i+1) w (by omega) hI')).mono (by omega) (fun _ _ hh=>hh)

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {im : Image} {sk : BitVec 256}
def expectedEntry (m : Bool) : PRes := pres [(.x5,cE 0),(.x19,cE 0)] [] [] (trial m) false 2 []
theorem entry_run (m : Bool) : run (look m) [trial m] (base m) []=some (expectedEntry m) := by
  cases m <;> apply optBeq_eq <;> decide +kernel

theorem entry_spec (m : Bool) (hl:LookOK im (look m)) (s : MachineState)
    (hpc:s.pc=pcOf (base m)) (h5:s.getReg .x5=0) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf (trial m) ∧ t.getReg .x19=0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _=>False) := by
  obtain ⟨hs,hp,-,hr,hm⟩:=SearchM.piece hl (entry_run m) s hpc rfl (no_br s) rfl
  refine ⟨_,hs,hp,by rw[hr];rfl,?_,fun A _ _=>by rw[hm];rfl⟩
  intro r hx
  have rr:=pres_regsExcept [(.x5,cE 0),(.x19,cE 0)] [] [] (trial m) false 2 [] s
  by_cases h:r=.x5
  · subst r
    rw[hr,h5]
    rfl
  · exact rr r (by simpa[h]using hx)

theorem search_good (m : Bool) (hl:LookOK im (look m)) {s0 : MachineState}
    {rho : BitVec 128} {msg : SigGolfCandidate.T3.Message} (hpre:Pre m rho msg s0)
    (hpc:s0.pc=pcOf (base m)) :
    TBSim im sk s0 (2^21*200+12) (SharedForest.sharedDigestSearch rho msg 0 (2^21)) (Post m s0) := by
  obtain ⟨t,ss,hp,h19,rr,ff⟩:=entry_spec m hl s0 hpc hpre.x5
  have hi:LoopInv m s0 0 t:=⟨hp,by decide,h19,rr.mono (by simp[regs]),ff.mono (fun _ _ h=>h.elim)⟩
  exact (TBSim.steps ss (loop m hl hpre (2^21) 0 t (by omega) hi)).mono (by omega) (fun _ _ h=>h)

end ClaudeWCT.W9.Machine.Sign.SharedDigest

namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def signCode : List (BitVec 32) := [0x20e37,0x160e0e13,0xe3b03,0x21b5b13,0x20e37,0x550e0e13,0x16e3023,0xaf9f406f]
sym_block signRun := symRun {noAlias:=true} signCode (pcOf 22754) 30
def expandCode : List (BitVec 32) := [0x180006f]
def failureCode : List (BitVec 32) := [0x100293,0x100513]
sym_block failRun := symRun {noAlias:=true} failureCode (pcOf 543) 10
sym_block failExpandRun := symRun {noAlias:=true} failureCode (pcOf 45229) 10
def failPC (m : Bool) : Word := pcOf (if m then 45229 else 543)
def failResult (m : Bool) : Result := if m then failExpandRun.res else failRun.res
theorem failure_run (m : Bool) : symRun {noAlias:=true} failureCode (failPC m) 10=some (failResult m) := by
  cases m
  · exact failRun
  · exact failExpandRun

theorem sign_steps {im : Image} (hc : CodeAt im (pcOf 22754) signCode)
    (s : MachineState) (hp : s.pc=pcOf 22754) (h17 : s.getReg .x17=0x20160) :
    ∃t,Steps im s 8 8 t ∧ t.pc=pcOf 11175 ∧
      t.getReg .x22=s.getMem 0x20160 >>> 33 ∧
      t.getMem 0x20550=s.getMem 0x20160 >>> 33 ∧
      RegsExcept s t [.x22,.x28] ∧ Frame s t (fun A=>A=0x20550) := by
  refine ⟨_,symRun_sound signRun hc s hp ?_,?_,?_,?_,?_,?_⟩
  · simp [signRun.res,rv_simp,h17,accessValid_iff,MEMORY_BYTES]
  · rfl
  · simp [signRun.res,rv_simp,h17]
  · simp [signRun.res,rv_simp,h17]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,signRun.res]
    t3n [h17]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA),if_neg hn]


theorem failure_steps {im : Image} (m : Bool) (hc : CodeAt im (failPC m) failureCode)
    (s : MachineState) (hp : s.pc=failPC m) :
    ∃t,Steps im s 2 2 t ∧ t.pc=failPC m+8 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧
      RegsExcept s t [.x5,.x10] ∧ Frame s t (fun _=>False) := by
  cases m <;>
    refine ⟨_,symRun_sound (failure_run _) hc s hp ?_,?_,rfl,rfl,?_,?_⟩
  all_goals first
    | solve | simp [failResult,failRun.res,failExpandRun.res,failPC,rv_simp]
    | rfl
    | (intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl)
    | (intro A hA hn;rfl)
#print axioms sign_steps
#print axioms failure_steps
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem correction_cost (k j : Nat) (hk:k<9) (hj:j<32) :
    SearchM.costByte (correctionOffset false k+j)=correctionByte k j := by
  have h:∀k,k<9 → ∀j,j<32 → SearchM.costByte (correctionOffset false k+j)=correctionByte k j := by decide +kernel
  exact h k hk j hj

theorem tables_of_costAt {s : MachineState} (hc : CostAt s) : TablesAt false s := by
  constructor
  · intro f hf
    rw [show tableBase false=COST by rfl,SearchM.cost_byte hc (by omega)]
    simp only [SearchM.costByte,if_pos hf,rankByte]
  · intro k hk j hj
    have ho:correctionOffset false k≤1056:=by simp only [correctionOffset,Bool.false_eq_true,if_false];split <;> omega
    rw [show tableBase false=COST by rfl,Nat.add_assoc,SearchM.cost_byte hc (by omega),correction_cost k j hk hj]
#print axioms tables_of_costAt
end ClaudeWCT.W9.Machine.Sign.SharedDigest
