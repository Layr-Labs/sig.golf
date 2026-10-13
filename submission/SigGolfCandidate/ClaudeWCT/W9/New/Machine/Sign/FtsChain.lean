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
/-- The FTS output half offset of heap `h`: 16 (the HIGH half) when `WCT9.ftsHighHeap h` (nested FTS r1-1: heaps 2 and
3; C1: even heaps `>= 16`, including the leaves of even children), else 0. -/
def hiOff (h : Nat) : Nat := if WCT9.ftsHighHeap h then 16 else 0
theorem hiOff_leaf (j : Nat) : hiOff (128 + j) = if j % 2 = 0 then 16 else 0 := by
  unfold hiOff
  by_cases hj : j % 2 = 0
  · rw [if_pos (WCT9.ftsHighHeap_even (by omega) (by omega)), if_pos hj]
  · rw [if_neg (by rw [WCT9.ftsHighHeap_odd (by omega) (by omega)]; simp), if_neg hj]
theorem DigAt.writeHash_half (t : MachineState) (a : BitVec 256) (h B : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) :
    DigAt (writeHash t a) (B + hiOff h) (WCT9.ftsHalf h a) := by
  unfold hiOff WCT9.ftsHalf
  by_cases hh : WCT9.ftsHighHeap h = true
  · rw [if_pos hh, if_pos hh]; exact DigAt.writeHash_hi t a B h12 hB
  · rw [if_neg hh, if_neg hh, Nat.add_zero]; exact DigAt.writeHash_lo t a B h12 hB
/-- C1: the leaf tail. An even leaf copies the high half (`slot + 16`) onto its slot, then `x18 += 1` and the loop
test (back to the next leaf, or on to the tree after leaf 127). -/
theorem step_T (hcode : NewCodeAt im) {c j : Nat} (hc : c < 9) (hj : j < 128) (s : MachineState)
    (hpc : s.pc = pcOf (tI c)) (h18 : s.getReg .x18 = BitVec.ofNat 64 j)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 (HEAPW + 16 * (128 + j))) :
    ∃ t k, Steps im s k k t ∧ k ≤ 12 ∧ (j + 1 < 128 → t.pc = pcOf (leafI c) ∧ t.getReg .x18 = BitVec.ofNat 64 (j + 1)) ∧
      (j + 1 = 128 → t.pc = pcOf (nodeI c) ∧ t.getReg .x18 = BitVec.ofNat 64 127) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * (128 + j))) =
        s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (128 + j) + hiOff (128 + j))) ∧
      t.getMem (BitVec.ofNat 64 (HEAPW + 16 * (128 + j) + 8)) =
        s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (128 + j) + hiOff (128 + j) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x18] ∧
      Frame s t (fun A => A = HEAPW + 16 * (128 + j) ∨ A = HEAPW + 16 * (128 + j) + 8) := by
  have hl := coordLook_ok hcode hc
  have hodd : ∀ d, Br.holds s ⟨.ne, .bin .and (.reg .x18) (cE 1), cE 0, d⟩ ↔ (decide (j % 2 ≠ 0) = d) := fun d => by
    rw [br_ne_holds]
    show ((s.getReg .x18 &&& BitVec.ofNat 64 1) != BitVec.ofNat 64 0) = d ↔ _
    rw [h18, ofNat_and_one j (by omega), ofNat_bne (by omega) (by norm_num)]
  have hlt : ∀ d, Br.holds s ⟨.ltu, x18p1, cE 128, d⟩ ↔ (decide (j + 1 < 128) = d) := fun d => by
    rw [br_ltu_holds, eval_x18p1 s h18, eval_cE, ofNat_ult (by omega) (by omega)]
  have hld : ∀ off, (E.ld (a2E off)).eval s = s.getMem (BitVec.ofNat 64 (HEAPW + 16 * (128 + j) + off)) := by
    intro off
    show s.getMem (s.getReg .x12 + BitVec.ofNat 64 off) = _
    rw [h12, ofNat_add_ofNat]
  have hea : ∀ off, Addr.eval s (a2A off) = BitVec.ofNat 64 (HEAPW + 16 * (128 + j) + off) := by
    intro off
    show s.getReg .x12 + BitVec.ofNat 64 off = _
    rw [h12, ofNat_add_ofNat]
  have hrg : ∀ (l : List (Reg × E)), (l.map Prod.fst = [.x6, .x18] ∨ l.map Prod.fst = [.x6, .x7, .x18]) →
      ∀ r ∈ l.map Prod.fst, r ∈ [.x6, .x7, .x18] := by
    intro l hl r hr
    rcases hl with hl | hl <;> rw [hl] at hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;> tauto
  by_cases hj2 : j % 2 = 0
  · -- even leaf: the copy runs, and `j + 1 < 128` since 127 is odd
    have hb : j + 1 < 128 := by omega
    have ho : hiOff (128 + j) = 16 := by rw [hiOff_leaf, if_pos hj2]
    obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc false true (Or.inr rfl)) s hpc (by
      intro o ho'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho'
      rcases ho' with rfl | rfl | rfl | rfl <;>
        exact valid_ofNat (show (E.reg .x12).eval s = _ from h12) (by ao) (by unfold MEMORY_BYTES; ao)) (by
      intro b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      rcases hb' with rfl | rfl
      · rw [hlt]; simp [hb]
      · rw [hodd]; simp [hj2])
    refine ⟨_, 11, hst', by norm_num, fun _ => ⟨rfl, by rw [pres_getReg]; exact eval_x18p1 s h18⟩,
      fun h => absurd h (by omega), ?_, ?_,
      (pres_regsExcept _ _ _ _ _ _ _ s).mono (hrg _ (Or.inr rfl)), ?_⟩
    · rw [pres_getMem, memEval_cons, memEval_cons, hea, hea, if_neg (by
        intro he; have := (ofNat_inj (by ao) (by ao)).mp he; omega), if_pos (by rw [Nat.add_zero]), hld, ho]
    · rw [pres_getMem, memEval_cons, hea, if_pos rfl, hld, ho]
    · intro A hA hn
      simp only [not_or] at hn
      rw [pres_getMem, memEval_cons, memEval_cons, hea, hea,
        if_neg (fun he => hn.2 ((ofNat_inj hA (by ao)).mp he)),
        if_neg (fun he => hn.1 (by rw [(ofNat_inj hA (by ao)).mp he, Nat.add_zero]))]
      rfl
  · have ho : hiOff (128 + j) = 0 := by rw [hiOff_leaf, if_neg hj2]
    have hbo : ∀ b ∈ [(⟨.ne, .bin .and (.reg .x18) (cE 1), cE 0, true⟩ : Br)], b.holds s := by
      intro b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      subst hb'; rw [hodd]; simp [hj2]
    by_cases hb : j + 1 < 128
    · obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc true true (Or.inl rfl)) s hpc (no_obl s) (by
        intro b hb'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
        rcases hb' with rfl | rfl
        · rw [hlt]; simp [hb]
        · exact hbo _ (List.mem_singleton_self _))
      exact ⟨_, 7, hst', by norm_num, fun _ => ⟨rfl, by rw [pres_getReg]; exact eval_x18p1 s h18⟩,
        fun h => absurd h (by omega), by rw [ho, Nat.add_zero]; rfl, by rw [ho, Nat.add_zero]; rfl,
        (pres_regsExcept _ _ _ _ _ _ _ s).mono (hrg _ (Or.inl rfl)), fun A _ _ => rfl⟩
    · obtain ⟨hst', -⟩ := run_pres hl (runT_eq hc true false (Or.inl rfl)) s hpc (no_obl s) (by
        intro b hb'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
        rcases hb' with rfl | rfl
        · rw [hlt]; simp [hb]
        · exact hbo _ (List.mem_singleton_self _))
      exact ⟨_, 8, hst', by norm_num, fun h => absurd h hb, fun _ => ⟨rfl, rfl⟩,
        by rw [ho, Nat.add_zero]; rfl, by rw [ho, Nat.add_zero]; rfl,
        (pres_regsExcept _ _ _ _ _ _ _ s).mono (hrg _ (Or.inl rfl)), fun A _ _ => rfl⟩
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
/-- Cycles of the fold post-hash block (nested FTS r1-1; C1: +7 for the half selector `Q_c`). -/
def ntC (c h : Nat) : Nat := if c = 0 then 25 else if h = 4 ∨ h = 2 then 32 else 29
/-- The fold pad word `NODEW + 32 + off` after the post-hash block of heap `h` (nested FTS r1-1): `R_{c-1}` after
heap 4, zero after heap 2 (coordinates `c >= 1`), unchanged otherwise. -/
def ntPad (c h off : Nat) (s : MachineState) : Word :=
  if 1 ≤ c ∧ h = 4 then s.getMem (BitVec.ofNat 64 (FORW + forOff (c - 1) + 16 + off))
  else if 1 ≤ c ∧ h = 2 then 0 else s.getMem (BitVec.ofNat 64 (NODEW + 32 + off))
set_option maxRecDepth 100000 in
theorem hiSel_table : ∀ h, h < 128 →
    BinOp.eval .sll (BinOp.eval .or (BinOp.eval .sltu (BitVec.ofNat 64 h) (BitVec.ofNat 64 4))
      (BinOp.eval .xor (BinOp.eval .or (BinOp.eval .and (BitVec.ofNat 64 h) (BitVec.ofNat 64 1))
        (BinOp.eval .sltu (BitVec.ofNat 64 h) (BitVec.ofNat 64 16))) (BitVec.ofNat 64 1))) (BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (hiOff h) := by
  decide +kernel
theorem eval_hiSelE (s : MachineState) {h : Nat} (h18 : s.getReg .x18 = BitVec.ofNat 64 h) (hh : h < 128) :
    hiSelE.eval s = BitVec.ofNat 64 (hiOff h) := by
  show BinOp.eval .sll (BinOp.eval .or (BinOp.eval .sltu (s.getReg .x18) (BitVec.ofNat 64 4))
    (BinOp.eval .xor (BinOp.eval .or (BinOp.eval .and (s.getReg .x18) (BitVec.ofNat 64 1))
      (BinOp.eval .sltu (s.getReg .x18) (BitVec.ofNat 64 16))) (BitVec.ofNat 64 1))) (BitVec.ofNat 64 4) = _
  rw [h18]
  exact hiSel_table h hh
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
      ∃ t, Steps im s (if c = 0 then 25 else if kd = 0 then 29 else 32)
          (if c = 0 then 25 else if kd = 0 then 29 else 32) t ∧ t.pc = pcOf (if b then nodeI c else rI c) ∧
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
      (if c = 0 then 25 else if kd = 0 then 29 else 32) = ntC c h := by
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
    WCT9.leafHashP index c j pad ends = WCT9.ftsHash (128 + j) (leafIn index c j pad ends) := rfl
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
    WCT9.wctNodeHash c index h L R = WCT9.ftsHash h (nodeIn c index h 0 L R) := by
  unfold nodeIn; rw [WCT9.bytesLE_zero16]; rfl
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
