import SigGolfCandidate.Legacy
import Mathlib.Tactic
import SigGolfCandidate.Rv.Sound

namespace SigGolfCandidate.T3M.Nonbinary.TailDispatch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
-- Boolean result checker copied with attribution from T3M.Verify.ChainRuns.
-- It is kept local to avoid importing the selected giant image into this packet.
def lstBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && lstBeq f as bs
  | _, _ => false
theorem lstBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, lstBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [lstBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [lstBeq] at h
    | cons b bs =>
      simp only [lstBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]
def rfBeq (a b : RegFile) : Bool := lstBeq E.beq a.fields b.fields
theorem rfBeq_eq {a b : RegFile} (h : rfBeq a b = true) : a = b := by
  have := lstBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl
def wBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2
theorem wBeq_eq {a b : Addr × E} (h : wBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [wBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]
def stBeq (a b : SymState) : Bool :=
  rfBeq a.regs b.regs && lstBeq wBeq a.mem b.mem && lstBeq Oblig.beq a.obl b.obl
theorem stBeq_eq {a b : SymState} (h : stBeq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [stBeq, Bool.and_eq_true] at h
  rw [rfBeq_eq h.1.1, lstBeq_eq (fun _ _ => wBeq_eq) h.1.2, lstBeq_eq (fun _ _ => Oblig.beq_eq) h.2]
def resBeq (a b : Result) : Bool :=
  stBeq a.st b.st && E.beq a.pc b.pc && decide (a.stop = b.stop) && a.steps == b.steps &&
    a.cycles == b.cycles
theorem resBeq_eq {a b : Result} (h : resBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a; obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [resBeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [stBeq_eq h1, E.beq_eq h2, h3, h4, h5]
def rOK (o : Option Result) (r : Result) : Bool :=
  match o with
  | some r' => resBeq r' r
  | none => false
theorem rOK_eq {o : Option Result} {r : Result} (h : rOK o r = true) : o = some r := by
  cases o with
  | none => simp [rOK] at h
  | some r' => simp only [rOK] at h; rw [resBeq_eq h]

def dispatchWords : List (BitVec 32) := [11441939,16189235,3389456487]
def armPC (rank : Nat) : Nat := 176936 + 256 * rank
def dispatchR : Result :=
  let ptr := .bin .add (.bin .sll (.reg .x29) (.c 10)) (.reg .x15)
  ⟨⟨RegFile.init.set .x14 ptr, [], []⟩,
    .bin .and (.bin .add ptr (.c 18446744073709550752)) (.c (~~~1#64)), .jump, 3, 3⟩

theorem dispatch_run (pc : Word) : symRun {} dispatchWords pc 3 = some dispatchR := by
  rfl

def pcOf (p : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * p)
theorem dispatch_target (k : Nat) (hk : k < 64) :
    ((((BitVec.ofNat 64 k <<< 10) + 712704#64) + 18446744073709550752#64) &&& ~~~1#64) =
      pcOf (armPC k) := by
  interval_cases k <;> decide +kernel

theorem dispatch_steps {image : Image} (pc : Word) (hc : CodeAt image pc dispatchWords)
    (s : MachineState) (hp : s.pc = pc) (k : Nat) (hk : k < 64)
    (hr : s.getReg .x29 = BitVec.ofNat 64 k) (hb : s.getReg .x15 = 712704#64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (armPC k) ∧
      (∀ r, r ≠ .x14 → t.getReg r = s.getReg r) ∧
      (∀ a, t.getMem a = s.getMem a) ∧ t.getReg .x15 = 712704#64 := by
  let t := dispatchR.toState s
  have st : Steps image s 3 3 t := symRun_sound (dispatch_run pc) hc s hp (by simp [dispatchR, Result.obligs, Oblig.all])
  refine ⟨t, st, ?_, ?_, ?_, ?_⟩
  · change (((s.getReg .x29 <<< 10) + s.getReg .x15 + 18446744073709550752#64) &&& ~~~1#64) = _
    rw [hr, hb]
    exact dispatch_target k hk
  · intro r hn
    rw [Result.toState_getReg]
    change (RegFile.get (RegFile.set RegFile.init .x14 _) r).eval s = _
    rw [RegFile.get_set_ne _ _ hn, RegFile.init_get_eval]
  · intro a
    simp [t, dispatchR, Result.toState_getMem, memEval]
  · rw [Result.toState_getReg]
    change (RegFile.get (RegFile.set RegFile.init .x14 _) .x15).eval s = _
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.init_get_eval, hb]
end SigGolfCandidate.T3M.Nonbinary.TailDispatch
