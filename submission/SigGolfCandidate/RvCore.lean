import Mathlib.Analysis.Complex.ExponentialBounds
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.EvalDist.Bool
import Mathlib.Data.BitVec
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import SigGolfCandidate.Merge001
import SigGolfCandidate.Merge007
import SigGolfCandidate.Merge009
import SigGolfCandidate.Merge015
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge027
set_option debug.skipKernelTC true
set_option linter.all false

-- ==== merged from Rv_Steps ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
inductive Steps (image : Image) : MachineState → Nat → Nat → MachineState → Prop where
  | refl (s : MachineState) : Steps image s 0 0 s
  | step {s t u : MachineState} {i : Instruction} {k c : Nat}
      (hf : fetch image s = some i) (hs : ordinaryStep s i = some t)
      (tail : Steps image t k c u) :
      Steps image s (k + 1) (instructionCycles i + c) u
theorem Steps.of_eq {image : Image} {s t : MachineState} {k c k' c' : Nat}
    (h : Steps image s k c t) (hk : k = k') (hc : c = c') : Steps image s k' c' t := by
  subst hk hc; exact h
theorem Steps.trans {image : Image} {s t u : MachineState} {k₁ c₁ k₂ c₂ : Nat}
    (h₁ : Steps image s k₁ c₁ t) (h₂ : Steps image t k₂ c₂ u) :
    Steps image s (k₁ + k₂) (c₁ + c₂) u := by
  induction h₁ with
  | refl => simpa using h₂
  | @step s t u i k c hf hs _ ih =>
    have := Steps.step hf hs (ih h₂)
    exact Steps.of_eq this (by omega) (by omega)
@[simp] theorem Execution.charge_zero (e : Execution) : e.charge 0 0 0 = e := by
  cases e; simp [Execution.charge]
@[simp] theorem Execution.charge_charge (e : Execution) (a b c a' b' c' : Nat) :
    (e.charge a b c).charge a' b' c' = e.charge (a' + a) (b' + b) (c' + c) := by
  cases e; simp [Execution.charge, Nat.add_assoc]
@[simp] theorem Execution.charge_exit (e : Execution) (a b c : Nat) : (e.charge a b c).exit = e.exit := rfl
@[simp] theorem Execution.charge_state (e : Execution) (a b c : Nat) : (e.charge a b c).state = e.state := rfl
@[simp] theorem Execution.charge_cycles (e : Execution) (a b c : Nat) :
    (e.charge a b c).cycles = a + e.cycles := rfl
@[simp] theorem Execution.charge_hashCalls (e : Execution) (a b c : Nat) :
    (e.charge a b c).hashCalls = b + e.hashCalls := rfl
@[simp] theorem Execution.charge_hashCompressions (e : Execution) (a b c : Nat) :
    (e.charge a b c).hashCompressions = c + e.hashCompressions := rfl
theorem ordinaryStep_ne_ecall {s t : MachineState} {i : Instruction}
    (h : ordinaryStep s i = some t) : i ≠ .base .ECALL := by
  rintro rfl; simp [ordinaryStep] at h
theorem execute_ordinary {image : Image} {s t : MachineState} {i : Instruction} (fuel : Nat)
    (hf : fetch image s = some i) (hs : ordinaryStep s i = some t) :
    execute (fuel + 1) image s =
      (fun r => r.charge (instructionCycles i) 0 0) <$> execute fuel image t := by
  cases i with
  | base j =>
    have hne := ordinaryStep_ne_ecall hs
    cases j <;> first | exact absurd rfl hne | simp_all [execute]
  | word op rd rs1 rs2 => simp [execute, hf, hs]
  | sraiw rd rs sh => simp [execute, hf, hs]
theorem Steps.execute {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) (fuel : Nat) :
    Riscv.execute (fuel + k) image s = (fun r => r.charge c 0 0) <$> Riscv.execute fuel image t := by
  induction h with
  | refl => simp
  | @step s t u i k c hf hs _ ih =>
    rw [← Nat.add_assoc, execute_ordinary _ hf hs, ih, Functor.map_map]
    simp [Nat.add_comm]
theorem Steps.execute_le {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) {fuel : Nat} (hle : k ≤ fuel) :
    Riscv.execute fuel image s =
      (fun r => r.charge c 0 0) <$> Riscv.execute (fuel - k) image t := by
  have := h.execute (fuel - k)
  rwa [Nat.sub_add_cancel hle] at this
theorem execute_hash {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) :
    Riscv.execute (fuel + 1) image s = (do
      let a ← HashSpec.query (hashInput s)
      (fun r => r.charge (8 * (hashInput s).blocks) 1 (hashInput s).blocks) <$>
        Riscv.execute fuel image (writeHash s a)) := by
  simp [Riscv.execute, hf, ht0, hv, map_eq_bind_pure_comp]
theorem execute_halt {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 1) :
    Riscv.execute (fuel + 1) image s =
      pure ⟨if s.getReg .x10 = 0 then .success else .failure, s, 1, 0, 0⟩ := by
  simp [Riscv.execute, hf, ht0]
theorem execute_ecall_fail {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL))
    (hbad : ¬ (s.getReg .x5 = 0 ∧ hashArgumentsValid s = true)) (ht0 : s.getReg .x5 ≠ 1) :
    Riscv.execute (fuel + 1) image s = pure ⟨.failure, s, 1, 0, 0⟩ := by
  have hbad' : ¬ (s.getReg .x5 = 0#64 ∧ hashArgumentsValid s = true) := hbad
  have ht0' : ¬ s.getReg .x5 = 1#64 := ht0
  simp [Riscv.execute, hf]
  rw [if_neg hbad', if_neg ht0']
theorem execute_fetch_none {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = none) :
    Riscv.execute (fuel + 1) image s = pure ⟨.failure, s, 0, 0, 0⟩ := by
  simp [Riscv.execute, hf]
theorem Steps.evalWith {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) (hash : Hash) (fuel : Nat) :
    evalWithAnswerFn hash (Riscv.execute (fuel + k) image s) =
      (evalWithAnswerFn hash (Riscv.execute fuel image t)).charge c 0 0 := by
  rw [h.execute, evalWithAnswerFn_map]
theorem evalWith_hash {image : Image} {s : MachineState} (hash : Hash) (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) :
    evalWithAnswerFn hash (Riscv.execute (fuel + 1) image s) =
      (evalWithAnswerFn hash (Riscv.execute fuel image (writeHash s (hash (hashInput s))))).charge
        (8 * (hashInput s).blocks) 1 (hashInput s).blocks := by
  rw [execute_hash fuel hf ht0 hv, evalWithAnswerFn_bind, evalWithAnswerFn_map]
  have : evalWithAnswerFn hash (HashSpec.query (hashInput s) : OracleComp HashSpec _) =
      hash (hashInput s) := evalWithAnswerFn_query hash _
  rw [this]
theorem evalWith_halt {image : Image} {s : MachineState} (hash : Hash) (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 1) :
    evalWithAnswerFn hash (Riscv.execute (fuel + 1) image s) =
      ⟨if s.getReg .x10 = 0 then .success else .failure, s, 1, 0, 0⟩ := by
  rw [execute_halt fuel hf ht0]; rfl
def toRunResult (submission : Submission) (phase : Phase) (e : Execution) :
    RunResult (Output submission.sizes phase) :=
  ⟨if e.exit = .success then
      some (readOutput submission.sizes submission.layout phase e.state) else none,
    e.exit != .unfinished, e.cycles, e.hashCalls, e.hashCompressions⟩
theorem run_eq (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    (s : MachineState) (hinit : initialState submission phase input = some s) :
    submission.run phase input =
      toRunResult submission phase <$> Riscv.execute CYCLE_LIMIT (submission.image phase) s := by
  simp only [Submission.run, hinit, map_eq_bind_pure_comp]
  rfl
theorem runWith_eq (submission : Submission) (hash : Hash) (phase : Phase)
    (input : Input submission.sizes phase)
    (s : MachineState) (hinit : initialState submission phase input = some s) :
    submission.runWith hash phase input =
      toRunResult submission phase
        (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT (submission.image phase) s)) := by
  rw [Submission.runWith, run_eq submission phase input s hinit, evalWithAnswerFn_map]
theorem initialState_pc (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase) (s : MachineState)
    (hinit : initialState submission phase input = some s) : s.pc = 0x1000 := by
  unfold initialState at hinit
  dsimp only at hinit
  split at hinit
  · cases hinit
    simp only [MachineState.pc_setReg]
    generalize (inputBuffers submission.sizes submission.layout phase input) = bufs
    suffices ∀ (st : MachineState), st.pc = 0x1000 → (bufs.foldl (fun state buffer =>
        state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) st).pc = 0x1000 from
      this _ (by simp)
    induction bufs with
    | nil => intro st h; exact h
    | cons b bs ih => intro st h; exact ih _ (by simp [h])
  · cases hinit
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Expr ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
deriving instance Lean.ToExpr for Reg
deriving instance Lean.ToExpr for WordOp
inductive LoadKind where
  | d | w | wu | h | hu | b | bu
  deriving DecidableEq, Repr, Lean.ToExpr
inductive StoreKind where
  | d | w | h | b
  deriving DecidableEq, Repr, Lean.ToExpr
def LoadKind.width : LoadKind → Nat
  | .d => 8 | .w => 4 | .wu => 4 | .h => 2 | .hu => 2 | .b => 1 | .bu => 1
def StoreKind.width : StoreKind → Nat
  | .d => 8 | .w => 4 | .h => 2 | .b => 1
def LoadKind.fromWord : LoadKind → Word → Nat → Word
  | .d, x, _ => x
  | .w, x, bo => (extractWord32 x (bo / 4)).signExtend 64
  | .wu, x, bo => (extractWord32 x (bo / 4)).zeroExtend 64
  | .h, x, bo => (extractHalfword x (bo / 2)).signExtend 64
  | .hu, x, bo => (extractHalfword x (bo / 2)).zeroExtend 64
  | .b, x, bo => (extractByte x bo).signExtend 64
  | .bu, x, bo => (extractByte x bo).zeroExtend 64
def StoreKind.merge : StoreKind → Word → Nat → Word → Word
  | .d, _, _, v => v
  | .w, old, bo, v => replaceWord32 old (bo / 4) (v.truncate 32)
  | .h, old, bo, v => replaceHalfword old (bo / 2) (v.truncate 16)
  | .b, old, bo, v => replaceByte old bo (v.truncate 8)
inductive BinOp where
  | add | sub | and | or | xor | sll | srl | sra | slt | sltu
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  | w (op : WordOp)
  | st (k : StoreKind) (bo : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr
inductive UnOp where
  | ld (k : LoadKind) (bo : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr
inductive CmpOp where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr, Lean.ToExpr
def BinOp.eval : BinOp → Word → Word → Word
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .sll, x, y => x <<< (y.toNat % 64)
  | .srl, x, y => x >>> (y.toNat % 64)
  | .sra, x, y => BitVec.sshiftRight x (y.toNat % 64)
  | .slt, x, y => if BitVec.slt x y then 1 else 0
  | .sltu, x, y => if BitVec.ult x y then 1 else 0
  | .mul, x, y => x * y
  | .mulh, x, y => rv64_mulh x y
  | .mulhsu, x, y => rv64_mulhsu x y
  | .mulhu, x, y => rv64_mulhu x y
  | .div, x, y => rv64_div x y
  | .divu, x, y => rv64_divu x y
  | .rem, x, y => rv64_rem x y
  | .remu, x, y => rv64_remu x y
  | .w op, x, y => (wordResult op (x.truncate 32) (y.truncate 32)).signExtend 64
  | .st k bo, x, y => k.merge x bo y
def UnOp.eval : UnOp → Word → Word
  | .ld k bo, x => k.fromWord x bo
def CmpOp.eval : CmpOp → Word → Word → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lt, x, y => BitVec.slt x y
  | .ge, x, y => !BitVec.slt x y
  | .ltu, x, y => BitVec.ult x y
  | .geu, x, y => !BitVec.ult x y
inductive E where
  | c (v : Word)
  | reg (r : Reg)
  | ld (a : E)
  | un (op : UnOp) (a : E)
  | bin (op : BinOp) (a b : E)
  | ite (op : CmpOp) (x y a b : E)
  deriving Repr, Lean.ToExpr
def E.eval (s : MachineState) : E → Word
  | .c v => v
  | .reg r => s.getReg r
  | .ld a => s.getMem (a.eval s)
  | .un op a => op.eval (a.eval s)
  | .bin op a b => op.eval (a.eval s) (b.eval s)
  | .ite op x y a b => if op.eval (x.eval s) (y.eval s) then a.eval s else b.eval s
def Reg.beqN (a b : Reg) : Bool := a.toNat == b.toNat
theorem Reg.toNat_inj {a b : Reg} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Reg.toNat] at h)
theorem Reg.beqN_eq {a b : Reg} (h : Reg.beqN a b = true) : a = b :=
  Reg.toNat_inj (by simpa [Reg.beqN] using h)
def E.beq : E → E → Bool
  | .c x, .c y => x.toNat == y.toNat
  | .reg a, .reg b => Reg.beqN a b
  | .ld a, .ld b => E.beq a b
  | .un o a, .un o' b => decide (o = o') && E.beq a b
  | .bin o a b, .bin o' a' b' => decide (o = o') && E.beq a a' && E.beq b b'
  | .ite o x y a b, .ite o' x' y' a' b' =>
      decide (o = o') && E.beq x x' && E.beq y y' && E.beq a a' && E.beq b b'
  | _, _ => false
theorem E.beq_eq : ∀ {a b : E}, E.beq a b = true → a = b := by
  intro a
  induction a with
  | c x => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (BitVec.eq_of_toNat_eq h)
  | reg r => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (Reg.beqN_eq h)
  | ld a ih => intro b h; cases b <;> simp [E.beq] at h; exact congrArg _ (ih h)
  | un o a ih =>
    intro b h; cases b <;> simp [E.beq] at h
    obtain ⟨h1, h2⟩ := h; subst h1; rw [ih h2]
  | bin o a b iha ihb =>
    intro b' h; cases b' <;> simp [E.beq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h; subst h1; rw [iha h2, ihb h3]
  | ite o x y a b ihx ihy iha ihb =>
    intro b' h; cases b' <;> simp [E.beq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h; subst h1; rw [ihx h2, ihy h3, iha h4, ihb h5]
def addC (a : E) (k : Word) : E :=
  match a with
  | .c x => .c (x + k)
  | .bin .add a' (.c x) => if (x + k).toNat == 0 then a' else .bin .add a' (.c (x + k))
  | a => if k.toNat == 0 then a else .bin .add a (.c k)
def mkAdd (a b : E) : E :=
  match b with
  | .c k => addC a k
  | b =>
    match a with
    | .c k => addC b k
    | a =>
      match b with
      | .bin .add b' (.c k) => addC (.bin .add a b') k
      | b => .bin .add a b
def mkBin (op : BinOp) (a b : E) : E :=
  match op with
  | .add => mkAdd a b
  | .sub =>
    match a, b with
    | .c x, .c y => .c (x - y)
    | a, .c y => addC a (-y)
    | a, b => .bin .sub a b
  | op =>
    match a, b with
    | .c x, .c y => .c (op.eval x y)
    | a, b => .bin op a b
def mkUn (op : UnOp) (a : E) : E :=
  match a with
  | .c x => .c (op.eval x)
  | a => .un op a
def mkIte (op : CmpOp) (x y a b : E) : E :=
  match x, y with
  | .c u, .c v => if op.eval u v then a else b
  | x, y => .ite op x y a b
theorem addC_eval (s : MachineState) (a : E) (k : Word) :
    (addC a k).eval s = a.eval s + k := by
  unfold addC
  split
  · rfl
  · rename_i a' x
    split
    · rename_i h
      have h0 : x + k = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
      simp [E.eval, BinOp.eval, BitVec.add_assoc, h0]
    · simp [E.eval, BinOp.eval, BitVec.add_assoc]
  · split
    · rename_i h
      have h0 : k = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
      simp [h0]
    · rfl
theorem mkAdd_eval (s : MachineState) (a b : E) :
    (mkAdd a b).eval s = a.eval s + b.eval s := by
  unfold mkAdd
  split
  · rw [addC_eval]; rfl
  · split
    · rw [addC_eval, BitVec.add_comm]; rfl
    · split
      · rw [addC_eval]; simp [E.eval, BinOp.eval, BitVec.add_assoc]
      · rfl
theorem mkBin_eval (s : MachineState) (op : BinOp) (a b : E) :
    (mkBin op a b).eval s = op.eval (a.eval s) (b.eval s) := by
  unfold mkBin
  split
  · exact mkAdd_eval s a b
  · split
    · rfl
    · rw [addC_eval]; simp [E.eval, BinOp.eval, BitVec.sub_eq_add_neg]
    · rfl
  · split
    · rfl
    · rfl
theorem mkUn_eval (s : MachineState) (op : UnOp) (a : E) :
    (mkUn op a).eval s = op.eval (a.eval s) := by
  unfold mkUn; split <;> rfl
theorem mkIte_eval (s : MachineState) (op : CmpOp) (x y a b : E) :
    (mkIte op x y a b).eval s =
      if op.eval (x.eval s) (y.eval s) then a.eval s else b.eval s := by
  unfold mkIte
  split
  · split <;> simp_all [E.eval]
  · rfl
structure Addr where
  base : Option E
  off : Word
  deriving Repr, Lean.ToExpr
def Addr.eval (s : MachineState) (a : Addr) : Word :=
  match a.base with
  | none => a.off
  | some b => b.eval s + a.off
def Addr.toE (a : Addr) : E :=
  match a.base with
  | none => .c a.off
  | some b => addC b a.off
theorem Addr.toE_eval (s : MachineState) (a : Addr) : a.toE.eval s = a.eval s := by
  rcases a with ⟨_ | b, off⟩
  · rfl
  · simp [Addr.toE, Addr.eval, addC_eval]
def norm : E → Addr
  | .c k => ⟨none, k⟩
  | .bin .add a (.c k) => ⟨some a, k⟩
  | e => ⟨some e, 0⟩
theorem norm_eval (s : MachineState) (e : E) : (norm e).eval s = e.eval s := by
  unfold norm
  split
  · rfl
  · rfl
  · simp [Addr.eval]
def Addr.beq (a b : Addr) : Bool :=
  (match a.base, b.base with
   | none, none => true
   | some x, some y => E.beq x y
   | _, _ => false) && a.off.toNat == b.off.toNat
theorem Addr.beq_eq {a b : Addr} (h : Addr.beq a b = true) : a = b := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;> simp [Addr.beq] at h
  · rw [BitVec.eq_of_toNat_eq h]
  · rw [E.beq_eq h.1, BitVec.eq_of_toNat_eq h.2]
inductive Alias where
  | same | diff | unknown
  deriving DecidableEq, Repr
def Addr.alias (a b : Addr) : Alias :=
  match a.base, b.base with
  | none, none => if a.off.toNat == b.off.toNat then .same else .diff
  | some x, some y =>
    if E.beq x y then (if a.off.toNat == b.off.toNat then .same else .diff) else .unknown
  | _, _ => .unknown
theorem Addr.alias_same {a b : Addr} (h : a.alias b = .same) (s : MachineState) :
    a.eval s = b.eval s := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;>
    simp only [Addr.alias, Addr.eval] at h ⊢
  · split at h
    · rename_i h'; exact BitVec.eq_of_toNat_eq (by simpa using h')
    · cases h
  · cases h
  · cases h
  · split at h
    · rename_i hb; split at h
      · rename_i h'
        have h1 := E.beq_eq hb
        have h2 : o = o' := BitVec.eq_of_toNat_eq (by simpa using h')
        rw [h1, h2]
      · cases h
    · cases h
theorem Addr.alias_diff {a b : Addr} (h : a.alias b = .diff) (s : MachineState) :
    a.eval s ≠ b.eval s := by
  rcases a with ⟨_ | x, o⟩ <;> rcases b with ⟨_ | y, o'⟩ <;>
    simp only [Addr.alias, Addr.eval] at h ⊢
  · split at h
    · cases h
    · rename_i h'; intro heq; apply h'; simp [heq]
  · cases h
  · cases h
  · split at h
    · rename_i hb; split at h
      · cases h
      · rename_i h'; rw [E.beq_eq hb]; intro heq; apply h'
        have := (BitVec.add_right_inj _).mp heq
        simp [this]
    · cases h
inductive Oblig where
  | valid (a : Addr) (w : Nat)
  | align8 (b : E)
  | ne (a b : Addr)
  deriving Repr, Lean.ToExpr
def Oblig.holds (s : MachineState) : Oblig → Prop
  | .valid a w => accessValid (a.eval s) w = true
  | .align8 b => (b.eval s).toNat % 8 = 0
  | .ne a b => a.eval s ≠ b.eval s
def Oblig.beq : Oblig → Oblig → Bool
  | .valid a w, .valid b w' => Addr.beq a b && w == w'
  | .align8 a, .align8 b => E.beq a b
  | .ne a b, .ne a' b' => Addr.beq a a' && Addr.beq b b'
  | _, _ => false
theorem Oblig.beq_eq {a b : Oblig} (h : Oblig.beq a b = true) : a = b := by
  cases a <;> cases b <;> simp [Oblig.beq] at h
  · rw [Addr.beq_eq h.1, h.2]
  · rw [E.beq_eq h]
  · rw [Addr.beq_eq h.1, Addr.beq_eq h.2]
def Oblig.all (s : MachineState) : List Oblig → Prop
  | [] => True
  | [o] => o.holds s
  | o :: os => o.holds s ∧ Oblig.all s os
theorem Oblig.all_iff (s : MachineState) (os : List Oblig) :
    Oblig.all s os ↔ ∀ o ∈ os, o.holds s := by
  induction os with
  | nil => simp [Oblig.all]
  | cons o os ih =>
    cases os with
    | nil => simp [Oblig.all]
    | cons o' os' => simp only [Oblig.all] at ih ⊢; simp [ih]
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Micro ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
inductive Src where
  | reg (r : Reg)
  | imm (v : Word)
  | pc
  deriving Repr
def Src.eval (s : MachineState) : Src → Word
  | .reg r => s.getReg r
  | .imm v => v
  | .pc => s.pc
inductive Micro where
  | alu (rd : Reg) (op : BinOp) (a b : Src)
  | load (k : LoadKind) (rd rs : Reg) (off : Word)
  | store (k : StoreKind) (rs1 rs2 : Reg) (off : Word)
  | branch (op : CmpOp) (rs1 rs2 : Reg) (off : Word)
  | jal (rd : Reg) (off : Word)
  | jalr (rd rs : Reg) (off : Word)
  deriving Repr
def LoadKind.read (s : MachineState) (addr : Word) : LoadKind → Word
  | .d => s.getMem addr
  | .w => (s.getWord32 addr).signExtend 64
  | .wu => (s.getWord32 addr).zeroExtend 64
  | .h => (s.getHalfword addr).signExtend 64
  | .hu => (s.getHalfword addr).zeroExtend 64
  | .b => (s.getByte addr).signExtend 64
  | .bu => (s.getByte addr).zeroExtend 64
def StoreKind.write (s : MachineState) (addr v : Word) : StoreKind → MachineState
  | .d => s.setMem addr v
  | .w => s.setWord32 addr (v.truncate 32)
  | .h => s.setHalfword addr (v.truncate 16)
  | .b => s.setByte addr (v.truncate 8)
theorem LoadKind.read_sub (s : MachineState) (addr : Word) (k : LoadKind) (hk : k ≠ .d) :
    k.read s addr = k.fromWord (s.getMem (alignToDword addr)) (byteOffset addr) := by
  cases k <;> first | exact absurd rfl hk | rfl
theorem StoreKind.write_sub (s : MachineState) (addr v : Word) (k : StoreKind) (hk : k ≠ .d) :
    k.write s addr v =
      s.setMem (alignToDword addr) (k.merge (s.getMem (alignToDword addr)) (byteOffset addr) v) := by
  cases k <;> first | exact absurd rfl hk | rfl
def Micro.exec (s : MachineState) : Micro → Option MachineState
  | .alu rd op a b => some ((s.setReg rd (op.eval (a.eval s) (b.eval s))).setPC (s.pc + 4))
  | .load k rd rs off =>
    if accessValid (s.getReg rs + off) k.width then
      some ((s.setReg rd (k.read s (s.getReg rs + off))).setPC (s.pc + 4))
    else none
  | .store k rs1 rs2 off =>
    if accessValid (s.getReg rs1 + off) k.width then
      some ((k.write s (s.getReg rs1 + off) (s.getReg rs2)).setPC (s.pc + 4))
    else none
  | .branch op rs1 rs2 off =>
    some (s.setPC (if op.eval (s.getReg rs1) (s.getReg rs2) then s.pc + off else s.pc + 4))
  | .jal rd off => some ((s.setReg rd (s.pc + 4)).setPC (s.pc + off))
  | .jalr rd rs off => some ((s.setReg rd (s.pc + 4)).setPC ((s.getReg rs + off) &&& ~~~1#64))
def luiVal (imm : BitVec 20) : Word := ((imm.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64
def classify : Instruction → Option Micro
  | .base i =>
    match i with
    | .ADD rd a b => some (.alu rd .add (.reg a) (.reg b))
    | .SUB rd a b => some (.alu rd .sub (.reg a) (.reg b))
    | .SLL rd a b => some (.alu rd .sll (.reg a) (.reg b))
    | .SRL rd a b => some (.alu rd .srl (.reg a) (.reg b))
    | .SRA rd a b => some (.alu rd .sra (.reg a) (.reg b))
    | .AND rd a b => some (.alu rd .and (.reg a) (.reg b))
    | .OR rd a b => some (.alu rd .or (.reg a) (.reg b))
    | .XOR rd a b => some (.alu rd .xor (.reg a) (.reg b))
    | .SLT rd a b => some (.alu rd .slt (.reg a) (.reg b))
    | .SLTU rd a b => some (.alu rd .sltu (.reg a) (.reg b))
    | .ADDI rd a imm => some (.alu rd .add (.reg a) (.imm (signExtend12 imm)))
    | .ANDI rd a imm => some (.alu rd .and (.reg a) (.imm (signExtend12 imm)))
    | .ORI rd a imm => some (.alu rd .or (.reg a) (.imm (signExtend12 imm)))
    | .XORI rd a imm => some (.alu rd .xor (.reg a) (.imm (signExtend12 imm)))
    | .SLTI rd a imm => some (.alu rd .slt (.reg a) (.imm (signExtend12 imm)))
    | .SLTIU rd a imm => some (.alu rd .sltu (.reg a) (.imm (signExtend12 imm)))
    | .SLLI rd a sh => some (.alu rd .sll (.reg a) (.imm (sh.zeroExtend 64)))
    | .SRLI rd a sh => some (.alu rd .srl (.reg a) (.imm (sh.zeroExtend 64)))
    | .SRAI rd a sh => some (.alu rd .sra (.reg a) (.imm (sh.zeroExtend 64)))
    | .LUI rd imm => some (.alu rd .add (.imm (luiVal imm)) (.imm 0))
    | .AUIPC rd imm => some (.alu rd .add .pc (.imm (luiVal imm)))
    | .LD rd a off => some (.load .d rd a (signExtend12 off))
    | .LW rd a off => some (.load .w rd a (signExtend12 off))
    | .LWU rd a off => some (.load .wu rd a (signExtend12 off))
    | .LH rd a off => some (.load .h rd a (signExtend12 off))
    | .LHU rd a off => some (.load .hu rd a (signExtend12 off))
    | .LB rd a off => some (.load .b rd a (signExtend12 off))
    | .LBU rd a off => some (.load .bu rd a (signExtend12 off))
    | .SD a b off => some (.store .d a b (signExtend12 off))
    | .SW a b off => some (.store .w a b (signExtend12 off))
    | .SH a b off => some (.store .h a b (signExtend12 off))
    | .SB a b off => some (.store .b a b (signExtend12 off))
    | .BEQ a b off => some (.branch .eq a b (signExtend13 off))
    | .BNE a b off => some (.branch .ne a b (signExtend13 off))
    | .BLT a b off => some (.branch .lt a b (signExtend13 off))
    | .BGE a b off => some (.branch .ge a b (signExtend13 off))
    | .BLTU a b off => some (.branch .ltu a b (signExtend13 off))
    | .BGEU a b off => some (.branch .geu a b (signExtend13 off))
    | .JAL rd off => some (.jal rd (signExtend21 off))
    | .JALR rd a off => some (.jalr rd a (signExtend12 off))
    | .ADDIW rd a imm => some (.alu rd (.w .add) (.reg a) (.imm (signExtend12 imm)))
    | .SUBW rd a b => some (.alu rd (.w .sub) (.reg a) (.reg b))
    | .SRLW rd a b => some (.alu rd (.w .srl) (.reg a) (.reg b))
    | .SLLIW rd a sh => some (.alu rd (.w .sll) (.reg a) (.imm (sh.zeroExtend 64)))
    | .SRLIW rd a sh => some (.alu rd (.w .srl) (.reg a) (.imm (sh.zeroExtend 64)))
    | .MUL rd a b => some (.alu rd .mul (.reg a) (.reg b))
    | .MULH rd a b => some (.alu rd .mulh (.reg a) (.reg b))
    | .MULHSU rd a b => some (.alu rd .mulhsu (.reg a) (.reg b))
    | .MULHU rd a b => some (.alu rd .mulhu (.reg a) (.reg b))
    | .DIV rd a b => some (.alu rd .div (.reg a) (.reg b))
    | .DIVU rd a b => some (.alu rd .divu (.reg a) (.reg b))
    | .REM rd a b => some (.alu rd .rem (.reg a) (.reg b))
    | .REMU rd a b => some (.alu rd .remu (.reg a) (.reg b))
    | .FENCE => some (.alu .x0 .add (.imm 0) (.imm 0))
    | _ => none
  | .word op rd a b => some (.alu rd (.w op) (.reg a) (.reg b))
  | .sraiw rd a sh => some (.alu rd (.w .sra) (.reg a) (.imm (sh.zeroExtend 64)))
private theorem toNat_zext6 (sh : BitVec 6) : (sh.zeroExtend 64).toNat % 64 = sh.toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := sh.isLt
  omega
private theorem toNat_trunc_zext5 (sh : BitVec 5) :
    ((sh.zeroExtend 64).truncate 32).toNat % 32 = sh.toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := sh.isLt
  omega
private theorem toNat_trunc32 (x : Word) : (x.truncate 32).toNat % 32 = x.toNat % 32 := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  omega
private theorem toNat_mod32 (sh : BitVec 5) : sh.toNat % 32 = sh.toNat := by
  have := sh.isLt; omega
private theorem setPC_ite (s : MachineState) (c : Prop) [Decidable c] (a b : Word) :
    (if c then s.setPC a else s.setPC b) = s.setPC (if c then a else b) := by
  split <;> rfl
set_option maxHeartbeats 1000000 in
theorem classify_sound {i : Instruction} {m : Micro} (h : classify i = some m) (s : MachineState) :
    ordinaryStep s i = m.exec s := by
  cases i with
  | base i =>
    cases i <;> simp only [classify, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first
        | rfl
        | (refine (show some (execInstrBr s _) = _ from ?_)
           simp only [execInstrBr, Micro.exec, Src.eval, BinOp.eval, CmpOp.eval, toNat_zext6,
             toNat_trunc32, wordResult, luiVal, setPC_ite]
           try simp only [toNat_mod32]
           try simp
           try congr
           all_goals exact (toNat_mod32 _).symm)
  | word op rd a b =>
    simp only [classify, Option.some.injEq] at h; subst h; rfl
  | sraiw rd a sh =>
    simp only [classify, Option.some.injEq] at h; subst h
    simp only [ordinaryStep, Micro.exec, Src.eval, BinOp.eval, wordResult, toNat_trunc_zext5]
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Exec ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
structure RegFile where
  r1 : E
  r2 : E
  r3 : E
  r4 : E
  r5 : E
  r6 : E
  r7 : E
  r8 : E
  r9 : E
  r10 : E
  r11 : E
  r12 : E
  r13 : E
  r14 : E
  r15 : E
  r16 : E
  r17 : E
  r18 : E
  r19 : E
  r20 : E
  r21 : E
  r22 : E
  r23 : E
  r24 : E
  r25 : E
  r26 : E
  r27 : E
  r28 : E
  r29 : E
  r30 : E
  r31 : E
  deriving Repr, Lean.ToExpr
def RegFile.fields (rf : RegFile) : List E := [rf.r1, rf.r2, rf.r3, rf.r4, rf.r5, rf.r6, rf.r7, rf.r8, rf.r9, rf.r10, rf.r11, rf.r12, rf.r13, rf.r14, rf.r15, rf.r16, rf.r17, rf.r18, rf.r19, rf.r20, rf.r21, rf.r22, rf.r23, rf.r24, rf.r25, rf.r26, rf.r27, rf.r28, rf.r29, rf.r30, rf.r31]
def RegFile.init : RegFile := ⟨.reg .x1, .reg .x2, .reg .x3, .reg .x4, .reg .x5, .reg .x6, .reg .x7, .reg .x8, .reg .x9, .reg .x10, .reg .x11, .reg .x12, .reg .x13, .reg .x14, .reg .x15, .reg .x16, .reg .x17, .reg .x18, .reg .x19, .reg .x20, .reg .x21, .reg .x22, .reg .x23, .reg .x24, .reg .x25, .reg .x26, .reg .x27, .reg .x28, .reg .x29, .reg .x30, .reg .x31⟩
def RegFile.get (rf : RegFile) : Reg → E
  | .x0 => .c 0
  | .x1 => rf.r1
  | .x2 => rf.r2
  | .x3 => rf.r3
  | .x4 => rf.r4
  | .x5 => rf.r5
  | .x6 => rf.r6
  | .x7 => rf.r7
  | .x8 => rf.r8
  | .x9 => rf.r9
  | .x10 => rf.r10
  | .x11 => rf.r11
  | .x12 => rf.r12
  | .x13 => rf.r13
  | .x14 => rf.r14
  | .x15 => rf.r15
  | .x16 => rf.r16
  | .x17 => rf.r17
  | .x18 => rf.r18
  | .x19 => rf.r19
  | .x20 => rf.r20
  | .x21 => rf.r21
  | .x22 => rf.r22
  | .x23 => rf.r23
  | .x24 => rf.r24
  | .x25 => rf.r25
  | .x26 => rf.r26
  | .x27 => rf.r27
  | .x28 => rf.r28
  | .x29 => rf.r29
  | .x30 => rf.r30
  | .x31 => rf.r31
def RegFile.set (rf : RegFile) (r : Reg) (e : E) : RegFile :=
  match r with
  | .x0 => rf
  | .x1 => { rf with r1 := e }
  | .x2 => { rf with r2 := e }
  | .x3 => { rf with r3 := e }
  | .x4 => { rf with r4 := e }
  | .x5 => { rf with r5 := e }
  | .x6 => { rf with r6 := e }
  | .x7 => { rf with r7 := e }
  | .x8 => { rf with r8 := e }
  | .x9 => { rf with r9 := e }
  | .x10 => { rf with r10 := e }
  | .x11 => { rf with r11 := e }
  | .x12 => { rf with r12 := e }
  | .x13 => { rf with r13 := e }
  | .x14 => { rf with r14 := e }
  | .x15 => { rf with r15 := e }
  | .x16 => { rf with r16 := e }
  | .x17 => { rf with r17 := e }
  | .x18 => { rf with r18 := e }
  | .x19 => { rf with r19 := e }
  | .x20 => { rf with r20 := e }
  | .x21 => { rf with r21 := e }
  | .x22 => { rf with r22 := e }
  | .x23 => { rf with r23 := e }
  | .x24 => { rf with r24 := e }
  | .x25 => { rf with r25 := e }
  | .x26 => { rf with r26 := e }
  | .x27 => { rf with r27 := e }
  | .x28 => { rf with r28 := e }
  | .x29 => { rf with r29 := e }
  | .x30 => { rf with r30 := e }
  | .x31 => { rf with r31 := e }
abbrev SymMem := List (Addr × E)
def memEval (s : MachineState) : SymMem → Word → Word
  | [], a => s.getMem a
  | (k, v) :: ws, a => if a = k.eval s then v.eval s else memEval s ws a
structure Config where
  noAlias : Bool := false
  deriving Repr
def readMem (cfg : Config) (k : Addr) : SymMem → Option (E × List Oblig)
  | [] => some (.ld k.toE, [])
  | (k', v) :: ws =>
    match k.alias k' with
    | .same => some (v, [])
    | .diff => readMem cfg k ws
    | .unknown =>
      if cfg.noAlias then
        match readMem cfg k ws with
        | none => none
        | some (e, os) => some (e, .ne k k' :: os)
      else none
def isSame (k k' : Addr) : Bool :=
  match k.alias k' with
  | .same => true
  | _ => false
def writeMem (k : Addr) (v : E) (ws : SymMem) : SymMem :=
  (k, v) :: ws.filter (fun p => !isSame k p.1)
structure SymState where
  regs : RegFile
  mem : SymMem
  obl : List Oblig
  deriving Repr, Lean.ToExpr
def SymState.init : SymState := ⟨RegFile.init, [], []⟩
def Oblig.dedupable : Oblig → Bool
  | .ne .. => false
  | _ => true
def SymState.addObl (σ : SymState) (o : Oblig) : SymState :=
  if o.dedupable && σ.obl.any (Oblig.beq o) then σ else { σ with obl := o :: σ.obl }
def SymState.addObls (σ : SymState) (os : List Oblig) : SymState :=
  os.foldl SymState.addObl σ
def Src.sym (rf : RegFile) (pc : Word) : Src → E
  | .reg r => rf.get r
  | .imm v => .c v
  | .pc => .c pc
def checkValid (σ : SymState) (a : Addr) (w : Nat) : Option SymState :=
  match a.base with
  | none => if accessValid a.off w then some σ else none
  | some _ => some (σ.addObl (.valid a w))
def subKey (σ : SymState) (a : Addr) : SymState × Addr × Nat :=
  match a.base with
  | none => (σ, ⟨none, alignToDword a.off⟩, byteOffset a.off)
  | some b => (σ.addObl (.align8 b), ⟨some b, alignToDword a.off⟩, byteOffset a.off)
def LoadKind.isD : LoadKind → Bool
  | .d => true
  | _ => false
def StoreKind.isD : StoreKind → Bool
  | .d => true
  | _ => false
def symMicro (cfg : Config) (pc : Word) (σ : SymState) : Micro → Option (SymState × Option E)
  | .alu rd op a b =>
    some ({ σ with regs := σ.regs.set rd (mkBin op (a.sym σ.regs pc) (b.sym σ.regs pc)) }, none)
  | .load k rd rs off =>
    let a := norm (mkAdd (σ.regs.get rs) (.c off))
    match checkValid σ a k.width with
    | none => none
    | some σ₁ =>
      if k.isD then
        match readMem cfg a σ₁.mem with
        | none => none
        | some (v, os) =>
          let σ₂ := σ₁.addObls os
          some ({ σ₂ with regs := σ₂.regs.set rd v }, none)
      else
        match subKey σ₁ a with
        | (σ₂, key, bo) =>
          match readMem cfg key σ₂.mem with
          | none => none
          | some (w, os) =>
            let σ₃ := σ₂.addObls os
            some ({ σ₃ with regs := σ₃.regs.set rd (mkUn (.ld k bo) w) }, none)
  | .store k rs1 rs2 off =>
    let a := norm (mkAdd (σ.regs.get rs1) (.c off))
    let v := σ.regs.get rs2
    match checkValid σ a k.width with
    | none => none
    | some σ₁ =>
      if k.isD then
        some ({ σ₁ with mem := writeMem a v σ₁.mem }, none)
      else
        match subKey σ₁ a with
        | (σ₂, key, bo) =>
          match readMem cfg key σ₂.mem with
          | none => none
          | some (old, os) =>
            let σ₃ := σ₂.addObls os
            some ({ σ₃ with mem := writeMem key (mkBin (.st k bo) old v) σ₃.mem }, none)
  | .branch op r1 r2 off =>
    some (σ, some (mkIte op (σ.regs.get r1) (σ.regs.get r2) (.c (pc + off)) (.c (pc + 4))))
  | .jal rd off =>
    some ({ σ with regs := σ.regs.set rd (.c (pc + 4)) }, some (.c (pc + off)))
  | .jalr rd rs off =>
    some ({ σ with regs := σ.regs.set rd (.c (pc + 4)) },
      some (mkBin .and (mkAdd (σ.regs.get rs) (.c off)) (.c (~~~1#64))))
inductive Stop where
  | fuel | endOfCode | branch | jump | ecall
  deriving DecidableEq, Repr, Lean.ToExpr
structure Result where
  st : SymState
  pc : E
  stop : Stop
  steps : Nat
  cycles : Nat
  deriving Repr, Lean.ToExpr
def Micro.stopKind : Micro → Stop
  | .branch .. => .branch
  | _ => .jump
def isEcall : Instruction → Bool
  | .base .ECALL => true
  | _ => false
def symRunAux (cfg : Config) : List (BitVec 32) → Word → Nat → SymState → Option Result
  | _, pc, 0, σ => some ⟨σ, .c pc, .fuel, 0, 0⟩
  | [], pc, _ + 1, σ => some ⟨σ, .c pc, .endOfCode, 0, 0⟩
  | w :: ws, pc, f + 1, σ =>
    match decodeInstruction w with
    | none => none
    | some i =>
      if isEcall i then some ⟨σ, .c pc, .ecall, 0, 0⟩ else
      match classify i with
      | none => none
      | some m =>
        match symMicro cfg pc σ m with
        | none => none
        | some (σ', none) =>
          match symRunAux cfg ws (pc + 4) f σ' with
          | none => none
          | some r => some { r with steps := r.steps + 1, cycles := instructionCycles i + r.cycles }
        | some (σ', some t) => some ⟨σ', t, m.stopKind, 1, instructionCycles i⟩
def symRun (cfg : Config) (code : List (BitVec 32)) (pc : Word) (fuel : Nat) : Option Result :=
  symRunAux cfg code pc fuel SymState.init
def SymState.toState (σ : SymState) (s : MachineState) (pc : Word) : MachineState :=
  { s with
    regs := fun r => if r = .x0 then s.regs .x0 else (σ.regs.get r).eval s
    mem := memEval s σ.mem
    pc := pc }
def Result.toState (r : Result) (s : MachineState) : MachineState :=
  r.st.toState s (r.pc.eval s)
def Result.obligs (r : Result) (s : MachineState) : Prop := Oblig.all s r.st.obl
def CodeAt (image : Image) (pc : Word) (code : List (BitVec 32)) : Prop :=
  0x1000 ≤ pc.toNat ∧ pc.toNat % 4 = 0 ∧ pc.toNat + 4 * code.length < 2 ^ 64 ∧
    code <+: image.code.drop ((pc.toNat - 0x1000) / 4)
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Sound ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
@[simp] theorem RegFile.get_x0 (rf : RegFile) : rf.get .x0 = .c 0 := rfl
@[simp] theorem RegFile.set_x0 (rf : RegFile) (e : E) : rf.set .x0 e = rf := rfl
theorem RegFile.get_set_self (rf : RegFile) {r : Reg} (e : E) (h : r ≠ .x0) :
    (rf.set r e).get r = e := by
  cases r <;> first | exact absurd rfl h | rfl
set_option maxHeartbeats 4000000 in
theorem RegFile.get_set_ne (rf : RegFile) {r r' : Reg} (e : E) (h : r' ≠ r) :
    (rf.set r e).get r' = rf.get r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl
theorem RegFile.init_get_eval (s : MachineState) (r : Reg) :
    (RegFile.init.get r).eval s = s.getReg r := by
  cases r <;> rfl
theorem MachineState.ext' {a b : MachineState} (hr : a.regs = b.regs) (hm : a.mem = b.mem)
    (hc : a.code = b.code) (hp : a.pc = b.pc) (h1 : a.committed = b.committed)
    (h2 : a.publicValues = b.publicValues) (h3 : a.privateInput = b.privateInput)
    (h4 : a.inputBufBase = b.inputBufBase) : a = b := by
  cases a; cases b; simp_all
@[simp] theorem SymState.toState_getReg (σ : SymState) (s : MachineState) (pc : Word) (r : Reg) :
    (σ.toState s pc).getReg r = (σ.regs.get r).eval s := by
  cases r <;> rfl
@[simp] theorem SymState.toState_getMem (σ : SymState) (s : MachineState) (pc a : Word) :
    (σ.toState s pc).getMem a = memEval s σ.mem a := rfl
@[simp] theorem SymState.toState_pc (σ : SymState) (s : MachineState) (pc : Word) :
    (σ.toState s pc).pc = pc := rfl
@[simp] theorem SymState.toState_code (σ : SymState) (s : MachineState) (pc : Word) :
    (σ.toState s pc).code = s.code := rfl
theorem SymState.toState_setPC (σ : SymState) (s : MachineState) (pc pc' : Word) :
    (σ.toState s pc).setPC pc' = σ.toState s pc' := rfl
theorem SymState.toState_congr {σ σ' : SymState} {s : MachineState} (hr : σ.regs = σ'.regs)
    (hm : memEval s σ.mem = memEval s σ'.mem) (pc : Word) : σ.toState s pc = σ'.toState s pc := by
  unfold SymState.toState; rw [hr, hm]
theorem SymState.init_toState (s : MachineState) : SymState.init.toState s s.pc = s := by
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> rfl
theorem setReg_of_ne (t : MachineState) {r : Reg} (v : Word) (h : r ≠ .x0) :
    t.setReg r v = { t with regs := fun r' => if r' = r then v else t.regs r' } := by
  cases r <;> first | exact absurd rfl h | (simp only [MachineState.setReg, beq_iff_eq])
theorem SymState.toState_setReg (σ : SymState) (s : MachineState) (pc : Word) (rd : Reg) (e : E) :
    (σ.toState s pc).setReg rd (e.eval s) = ({ σ with regs := σ.regs.set rd e }).toState s pc := by
  by_cases hrd : rd = .x0
  · subst hrd; rfl
  · rw [setReg_of_ne _ _ hrd]
    apply MachineState.ext' <;> try rfl
    funext r'
    simp only [SymState.toState]
    by_cases h : r' = rd
    · subst h; simp [hrd, RegFile.get_set_self _ _ hrd]
    · simp [h, RegFile.get_set_ne _ _ h]
theorem SymState.toState_setMem (σ : SymState) (s : MachineState) (pc : Word) (k : Addr) (e : E) :
    (σ.toState s pc).setMem (k.eval s) (e.eval s) =
      ({ σ with mem := (k, e) :: σ.mem }).toState s pc := by
  apply MachineState.ext' <;> try rfl
  funext a
  simp [MachineState.setMem, SymState.toState, memEval]
theorem memEval_nil (s : MachineState) (a : Word) : memEval s [] a = s.getMem a := rfl
theorem memEval_cons (s : MachineState) (k : Addr) (v : E) (ws : SymMem) (a : Word) :
    memEval s ((k, v) :: ws) a = if a = k.eval s then v.eval s else memEval s ws a := rfl
theorem memEval_frame (s : MachineState) (ws : SymMem) (a : Word)
    (h : ∀ p ∈ ws, a ≠ p.1.eval s) : memEval s ws a = s.getMem a := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨k, v⟩ := p
    rw [memEval_cons, if_neg (h _ (List.mem_cons_self ..))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
theorem isSame_eval {k k' : Addr} (h : isSame k k' = true) (s : MachineState) :
    k.eval s = k'.eval s := by
  unfold isSame at h
  split at h
  · rename_i hs; exact Addr.alias_same hs s
  · cases h
theorem memEval_writeMem (s : MachineState) (k : Addr) (v : E) (ws : SymMem) :
    memEval s (writeMem k v ws) = memEval s ((k, v) :: ws) := by
  funext a
  simp only [writeMem, memEval_cons]
  split
  · rfl
  · rename_i hne
    induction ws with
    | nil => rfl
    | cons p ws ih =>
      obtain ⟨k', v'⟩ := p
      simp only [List.filter_cons]
      split
      · rw [memEval_cons, memEval_cons, ih]
      · rename_i hs
        have hs' : isSame k k' = true := by simpa using hs
        rw [memEval_cons, if_neg, ih]
        rw [← isSame_eval hs' s]; exact hne
theorem readMem_sound {cfg : Config} {k : Addr} {ws : SymMem} {e : E} {os : List Oblig}
    (h : readMem cfg k ws = some (e, os)) (s : MachineState) (hos : ∀ o ∈ os, o.holds s) :
    memEval s ws (k.eval s) = e.eval s := by
  induction ws generalizing e os with
  | nil =>
    simp only [readMem, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [memEval_nil, E.eval, Addr.toE_eval]
  | cons p ws ih =>
    obtain ⟨k', v⟩ := p
    simp only [readMem] at h
    rw [memEval_cons]
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_pos (Addr.alias_same hs s)]
    · rename_i hd
      rw [if_neg (Addr.alias_diff hd s)]
      exact ih h hos
    · split at h
      · split at h
        · cases h
        · rename_i e' os' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hne := hos _ (List.mem_cons_self ..)
          simp only [Oblig.holds] at hne
          rw [if_neg hne]
          exact ih hr (fun o ho => hos o (List.mem_cons_of_mem _ ho))
      · cases h
theorem SymState.addObl_regs (σ : SymState) (o : Oblig) : (σ.addObl o).regs = σ.regs := by
  unfold SymState.addObl; split <;> rfl
theorem SymState.addObl_mem (σ : SymState) (o : Oblig) : (σ.addObl o).mem = σ.mem := by
  unfold SymState.addObl; split <;> rfl
theorem SymState.addObl_sub (σ : SymState) (o : Oblig) : σ.obl ⊆ (σ.addObl o).obl := by
  unfold SymState.addObl; split
  · exact List.Subset.refl _
  · exact List.subset_cons_self _ _
theorem SymState.addObl_mem_obl (σ : SymState) (o : Oblig) : o ∈ (σ.addObl o).obl := by
  unfold SymState.addObl; split
  · rename_i h
    obtain ⟨o', ho', hb⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp h).2
    rw [Oblig.beq_eq hb]; exact ho'
  · exact List.mem_cons_self ..
theorem SymState.addObls_regs (σ : SymState) (os : List Oblig) : (σ.addObls os).regs = σ.regs := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih => simp only [SymState.addObls, List.foldl_cons] at ih ⊢; rw [ih, addObl_regs]
theorem SymState.addObls_mem (σ : SymState) (os : List Oblig) : (σ.addObls os).mem = σ.mem := by
  induction os generalizing σ with
  | nil => rfl
  | cons o os ih => simp only [SymState.addObls, List.foldl_cons] at ih ⊢; rw [ih, addObl_mem]
theorem SymState.addObls_sub (σ : SymState) (os : List Oblig) : σ.obl ⊆ (σ.addObls os).obl := by
  induction os generalizing σ with
  | nil => exact List.Subset.refl _
  | cons o os ih =>
    simp only [SymState.addObls, List.foldl_cons] at ih ⊢
    exact List.Subset.trans (addObl_sub σ o) (ih _)
theorem SymState.addObls_mem_obl (σ : SymState) (os : List Oblig) :
    ∀ o ∈ os, o ∈ (σ.addObls os).obl := by
  induction os generalizing σ with
  | nil => intro o h; cases h
  | cons o os ih =>
    intro o' h
    simp only [SymState.addObls, List.foldl_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact addObls_sub _ os (addObl_mem_obl σ o')
    · exact ih _ o' h
theorem byteOffset_eq (x : Word) : byteOffset x = x.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and, show (7#64).toNat = 7 from rfl]
  simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 3
theorem alignToDword_toNat (x : Word) : (alignToDword x).toNat = x.toNat - x.toNat % 8 := by
  unfold alignToDword
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 7 from rfl]
  have hhi_mod : (x.toNat &&& (2 ^ 64 - 1 - 7)) % 8 = 0 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_mod_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) % 2 ^ 3 = 0 from by decide]
    simp
  have hhi_div : (x.toNat &&& (2 ^ 64 - 1 - 7)) / 8 = x.toNat / 8 := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, Nat.and_div_two_pow,
      show (2 ^ 64 - 1 - 7 : Nat) / 2 ^ 3 = 2 ^ 61 - 1 from by decide]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by have := x.isLt; omega)
  have heucl := Nat.div_add_mod (x.toNat &&& (2 ^ 64 - 1 - 7)) 8
  have heucl2 := Nat.div_add_mod x.toNat 8
  omega
theorem aligned_add (b k : Word) (hb : b.toNat % 8 = 0) :
    alignToDword (b + k) = b + alignToDword k ∧ byteOffset (b + k) = byteOffset k := by
  have hbl := b.isLt
  have hkl := k.isLt
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, BitVec.toNat_add, BitVec.toNat_add, alignToDword_toNat]
    omega
  · rw [byteOffset_eq, byteOffset_eq, BitVec.toNat_add]
    omega
theorem checkValid_sound {σ σ₁ : SymState} {a : Addr} {w : Nat} (h : checkValid σ a w = some σ₁)
    (s : MachineState) (hobl : ∀ o ∈ σ₁.obl, o.holds s) :
    accessValid (a.eval s) w = true ∧ σ₁.regs = σ.regs ∧ σ₁.mem = σ.mem ∧ σ.obl ⊆ σ₁.obl := by
  unfold checkValid at h
  split at h
  · rename_i hb
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h; subst h
      refine ⟨?_, rfl, rfl, List.Subset.refl _⟩
      simp only [Addr.eval, hb]; exact hv
    · cases h
  · rename_i b hb
    simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, SymState.addObl_regs _ _, SymState.addObl_mem _ _, SymState.addObl_sub _ _⟩
    exact hobl _ (SymState.addObl_mem_obl _ _)
theorem subKey_sound {σ σ₂ : SymState} {a key : Addr} {bo : Nat} (h : subKey σ a = (σ₂, key, bo))
    (s : MachineState) (hobl : ∀ o ∈ σ₂.obl, o.holds s) :
    key.eval s = alignToDword (a.eval s) ∧ bo = byteOffset (a.eval s) ∧
      σ₂.regs = σ.regs ∧ σ₂.mem = σ.mem ∧ σ.obl ⊆ σ₂.obl := by
  unfold subKey at h
  split at h
  · rename_i hb
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Addr.eval, hb]
  · rename_i b hb
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hal : (b.eval s).toNat % 8 = 0 := hobl _ (SymState.addObl_mem_obl _ _)
    have := aligned_add (b.eval s) a.off hal
    refine ⟨?_, ?_, SymState.addObl_regs _ _, SymState.addObl_mem _ _, SymState.addObl_sub _ _⟩
    · simp [Addr.eval, hb, this.1]
    · simp [Addr.eval, hb, this.2]
theorem Src.sym_eval (σ : SymState) (s : MachineState) (pc : Word) (a : Src) :
    (a.sym σ.regs pc).eval s = a.eval (σ.toState s pc) := by
  cases a <;> simp [Src.sym, Src.eval, E.eval]
theorem LoadKind.isD_iff (k : LoadKind) : k.isD = true ↔ k = .d := by cases k <;> simp [LoadKind.isD]
theorem StoreKind.isD_iff (k : StoreKind) : k.isD = true ↔ k = .d := by
  cases k <;> simp [StoreKind.isD]
def nextPc (s : MachineState) (pc : Word) : Option E → Word
  | none => pc + 4
  | some t => t.eval s
set_option maxHeartbeats 1000000 in
theorem symMicro_sound {cfg : Config} {pc : Word} {σ σ' : SymState} {m : Micro} {ctl : Option E}
    (h : symMicro cfg pc σ m = some (σ', ctl)) (s : MachineState)
    (hobl : ∀ o ∈ σ'.obl, o.holds s) :
    σ.obl ⊆ σ'.obl ∧ m.exec (σ.toState s pc) = some (σ'.toState s (nextPc s pc ctl)) := by
  cases m with
  | alu rd op a b =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, SymState.toState_pc, ← Src.sym_eval, ← mkBin_eval,
      SymState.toState_setReg, SymState.toState_setPC, nextPc]
  | load k rd rs off =>
    simp only [symMicro] at h
    split at h
    · cases h
    · rename_i σ₁ hcv
      have haddr : (norm (mkAdd (σ.regs.get rs) (.c off))).eval s =
          (σ.toState s pc).getReg rs + off := by
        rw [norm_eval, mkAdd_eval]; simp [E.eval]
      split at h
      ·
        rename_i hk
        have hk' : k = .d := (LoadKind.isD_iff k).mp hk
        subst hk'
        split at h
        · cases h
        · rename_i v os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub2 := SymState.addObls_sub σ₁ os
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl o (hsub2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₁ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 hsub2, ?_⟩
          rw [haddr, hm1] at hread
          rw [haddr] at hv
          simp only [Micro.exec, hv, if_true, LoadKind.read, SymState.toState_getMem,
            SymState.toState_pc]
          rw [hread, SymState.toState_setReg, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1]
          · simp [SymState.addObls_mem, hm1]
      ·
        rename_i hk
        have hk' : k ≠ .d := fun h' => hk ((LoadKind.isD_iff k).mpr h')
        generalize hsk : subKey σ₁ (norm (mkAdd (σ.regs.get rs) (E.c off))) = p at h
        obtain ⟨σ₂, key, bo⟩ := p
        simp only at h
        split at h
        · cases h
        · rename_i w os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub3 := SymState.addObls_sub σ₂ os
          have hobl2 : ∀ o ∈ σ₂.obl, o.holds s := fun o ho => hobl o (hsub3 ho)
          obtain ⟨hkey, hbo, hr2, hm2, hs2⟩ := subKey_sound hsk s hobl2
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl2 o (hs2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₂ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 (List.Subset.trans hs2 hsub3), ?_⟩
          rw [haddr] at hv hkey hbo
          rw [hkey, hm2, hm1] at hread
          simp only [Micro.exec, hv, if_true, SymState.toState_pc]
          rw [LoadKind.read_sub _ _ _ hk', SymState.toState_getMem, hread, ← hbo,
            show k.fromWord (w.eval s) bo = (mkUn (.ld k bo) w).eval s by rw [mkUn_eval]; rfl,
            SymState.toState_setReg, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1, hr2]
          · simp [SymState.addObls_mem, hm1, hm2]
  | store k rs1 rs2 off =>
    simp only [symMicro] at h
    split at h
    · cases h
    · rename_i σ₁ hcv
      have haddr : (norm (mkAdd (σ.regs.get rs1) (.c off))).eval s =
          (σ.toState s pc).getReg rs1 + off := by
        rw [norm_eval, mkAdd_eval]; simp [E.eval]
      split at h
      · rename_i hk
        have hk' : k = .d := (StoreKind.isD_iff k).mp hk
        subst hk'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl
        refine ⟨hs1, ?_⟩
        rw [haddr] at hv
        simp only [Micro.exec, hv, if_true, StoreKind.write, SymState.toState_pc]
        rw [← haddr, show (σ.toState s pc).getReg rs2 = (σ.regs.get rs2).eval s by simp,
          SymState.toState_setMem, SymState.toState_setPC]
        congr 1
        apply SymState.toState_congr
        · simp [hr1]
        · simp [memEval_writeMem, hm1]
      · rename_i hk
        have hk' : k ≠ .d := fun h' => hk ((StoreKind.isD_iff k).mpr h')
        generalize hsk : subKey σ₁ (norm (mkAdd (σ.regs.get rs1) (E.c off))) = p at h
        obtain ⟨σ₂, key, bo⟩ := p
        simp only at h
        split at h
        · cases h
        · rename_i old os hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hsub3 := SymState.addObls_sub σ₂ os
          have hobl2 : ∀ o ∈ σ₂.obl, o.holds s := fun o ho => hobl o (hsub3 ho)
          obtain ⟨hkey, hbo, hr2, hm2, hs2⟩ := subKey_sound hsk s hobl2
          have hobl1 : ∀ o ∈ σ₁.obl, o.holds s := fun o ho => hobl2 o (hs2 ho)
          obtain ⟨hv, hr1, hm1, hs1⟩ := checkValid_sound hcv s hobl1
          have hos : ∀ o ∈ os, o.holds s := fun o ho =>
            hobl o (SymState.addObls_mem_obl σ₂ os o ho)
          have hread := readMem_sound hr s hos
          refine ⟨List.Subset.trans hs1 (List.Subset.trans hs2 hsub3), ?_⟩
          rw [haddr] at hv hkey hbo
          rw [hkey, hm2, hm1] at hread
          simp only [Micro.exec, hv, if_true, SymState.toState_pc]
          rw [StoreKind.write_sub _ _ _ _ hk', SymState.toState_getMem, hread, ← hbo, ← hkey,
            show k.merge (old.eval s) bo ((σ.toState s pc).getReg rs2) =
              (mkBin (.st k bo) old (σ.regs.get rs2)).eval s by rw [mkBin_eval]; simp; rfl,
            SymState.toState_setMem, SymState.toState_setPC]
          congr 1
          apply SymState.toState_congr
          · simp [SymState.addObls_regs, hr1, hr2]
          · simp [memEval_writeMem, SymState.addObls_mem, hm1, hm2]
  | branch op r1 r2 off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, mkIte_eval, SymState.toState_getReg, SymState.toState_pc,
      SymState.toState_setPC, E.eval]
  | jal rd off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, SymState.toState_pc, E.eval]
    rw [show pc + 4 = (E.c (pc + 4)).eval s from rfl, SymState.toState_setReg,
      SymState.toState_setPC]
    rfl
  | jalr rd rs off =>
    simp only [symMicro, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.Subset.refl _, ?_⟩
    simp only [Micro.exec, nextPc, SymState.toState_pc, mkBin_eval, mkAdd_eval, E.eval,
      SymState.toState_getReg, BinOp.eval]
    rw [show pc + 4 = (E.c (pc + 4)).eval s from rfl, SymState.toState_setReg,
      SymState.toState_setPC]
    rfl
theorem getElem?_of_prefix_drop {l : List (BitVec 32)} {i : Nat} {w : BitVec 32}
    {ws : List (BitVec 32)} (h4 : w :: ws <+: List.drop i l) : l[i]? = some w := by
  obtain ⟨t, ht⟩ := h4
  have := congrArg (·[0]?) ht
  simp only [List.getElem?_drop, List.cons_append, List.getElem?_cons_zero, Nat.add_zero] at this
  exact this.symm
theorem CodeAt.fetch {image : Image} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    (h : CodeAt image pc (w :: ws)) (t : MachineState) (ht : t.pc = pc) :
    fetch image t = decodeInstruction w := by
  obtain ⟨h1, h2, _, h4⟩ := h
  have hget : image.code[(pc.toNat - 0x1000) / 4]? = some w := getElem?_of_prefix_drop h4
  unfold Riscv.fetch
  rw [ht]
  have hc : (decide (pc.toNat < 0x1000) || pc.toNat % 4 != 0) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, bne_eq_false_iff_eq]
    exact ⟨by omega, h2⟩
  simp only [hc, Bool.false_eq_true, if_false, hget]
  rfl
theorem CodeAt.tail {image : Image} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    (h : CodeAt image pc (w :: ws)) : CodeAt image (pc + 4) ws := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.length_cons] at h3
  have hpc : (pc + 4).toNat = pc.toNat + 4 := by
    rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (pc.toNat + 4 - 0x1000) / 4 = (pc.toNat - 0x1000) / 4 + 1 by omega,
    ← List.drop_drop]
  obtain ⟨t, ht⟩ := h4
  rw [← ht]
  exact ⟨t, by simp⟩
theorem CodeAt.of_append {image : Image} {pre code post : List (BitVec 32)}
    (h : image.code = pre ++ code ++ post) (pc : Word)
    (hpc : pc.toNat = 0x1000 + 4 * pre.length)
    (hrange : 0x1000 + 4 * (pre.length + code.length) < 2 ^ 64) : CodeAt image pc code := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * pre.length - 0x1000) / 4 = pre.length by omega, h,
    List.append_assoc, List.drop_left]
  exact List.prefix_append _ _
theorem isEcall_eq {i : Instruction} (h : isEcall i = true) : i = .base .ECALL := by
  unfold isEcall at h; split at h <;> first | rfl | cases h
theorem symRunAux_sound (cfg : Config) (image : Image) (s : MachineState) :
    ∀ (code : List (BitVec 32)) (pc : Word) (fuel : Nat) (σ : SymState) (r : Result),
      symRunAux cfg code pc fuel σ = some r → CodeAt image pc code →
      (∀ o ∈ r.st.obl, o.holds s) →
      Steps image (σ.toState s pc) r.steps r.cycles (r.toState s) ∧ σ.obl ⊆ r.st.obl ∧
        (r.stop = .ecall → fetch image (r.toState s) = some (.base .ECALL)) := by
  intro code
  induction code with
  | nil =>
    intro pc fuel σ r h _ _
    cases fuel <;> simp only [symRunAux, Option.some.injEq] at h <;> subst h <;>
      exact ⟨Steps.refl _, List.Subset.refl _, by simp⟩
  | cons w ws ih =>
    intro pc fuel σ r h hcode hobl
    cases fuel with
    | zero =>
      simp only [symRunAux, Option.some.injEq] at h; subst h
      exact ⟨Steps.refl _, List.Subset.refl _, by simp⟩
    | succ f =>
      simp only [symRunAux] at h
      split at h
      · cases h
      · rename_i i hdec
        split at h
        · rename_i he
          simp only [Option.some.injEq] at h; subst h
          refine ⟨Steps.refl _, List.Subset.refl _, fun _ => ?_⟩
          rw [hcode.fetch _ rfl, hdec, isEcall_eq he]
        · split at h
          · cases h
          · rename_i m hcl
            split at h
            · cases h
            · rename_i σ' hm
              split at h
              · cases h
              · rename_i r' hr'
                simp only [Option.some.injEq] at h; subst h
                obtain ⟨hsteps, hsub, hec⟩ := ih (pc + 4) f σ' r' hr' hcode.tail hobl
                obtain ⟨hsub', hexec⟩ := symMicro_sound hm s (fun o ho => hobl o (hsub ho))
                refine ⟨?_, List.Subset.trans hsub' hsub, hec⟩
                refine Steps.step ((hcode.fetch (σ.toState s pc) rfl).trans hdec) ?_ hsteps
                rw [classify_sound hcl, hexec]; rfl
            · rename_i σ' t hm
              simp only [Option.some.injEq] at h; subst h
              obtain ⟨hsub', hexec⟩ := symMicro_sound hm s hobl
              refine ⟨?_, hsub', ?_⟩
              · refine Steps.step (i := i) ((hcode.fetch (σ.toState s pc) rfl).trans hdec) ?_ (Steps.refl _)
                rw [classify_sound hcl, hexec]; rfl
              · intro hst; cases m <;> cases hst
theorem symRun_sound {cfg : Config} {image : Image} {code : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg code pc fuel = some r)
    (hcode : CodeAt image pc code) (s : MachineState) (hpc : s.pc = pc) (hobl : r.obligs s) :
    Steps image s r.steps r.cycles (r.toState s) := by
  have := (symRunAux_sound cfg image s code pc fuel _ r hrun hcode
    ((Oblig.all_iff s _).mp hobl)).1
  rwa [← hpc, SymState.init_toState] at this
theorem symRun_ecall {cfg : Config} {image : Image} {code : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg code pc fuel = some r)
    (hcode : CodeAt image pc code) (s : MachineState) (hobl : r.obligs s)
    (hstop : r.stop = .ecall) : fetch image (r.toState s) = some (.base .ECALL) :=
  (symRunAux_sound cfg image s code pc fuel _ r hrun hcode ((Oblig.all_iff s _).mp hobl)).2.2 hstop
@[simp] theorem Result.toState_getReg (r : Result) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := by
  simp [Result.toState]
@[simp] theorem Result.toState_getMem (r : Result) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl
@[simp] theorem Result.toState_pc (r : Result) (s : MachineState) :
    (r.toState s).pc = r.pc.eval s := rfl
@[simp] theorem Result.toState_code (r : Result) (s : MachineState) :
    (r.toState s).code = s.code := rfl
theorem Result.toState_getMem_of_read (r : Result) (s : MachineState) {cfg : Config} {k : Addr}
    {e : E} {os : List Oblig} (h : readMem cfg k r.st.mem = some (e, os))
    (hos : Oblig.all s os) : (r.toState s).getMem (k.eval s) = e.eval s :=
  readMem_sound h s ((Oblig.all_iff s _).mp hos)
theorem Result.toState_getMem_frame (r : Result) (s : MachineState) (a : Word)
    (h : ∀ p ∈ r.st.mem, a ≠ p.1.eval s) : (r.toState s).getMem a = s.getMem a :=
  memEval_frame s _ a h
end SigGolfCandidate.Rv
end
-- ==== merged from Rv_Hash ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
def wordsToNat : List Word → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * wordsToNat ws
def queryOfWords (n : Nat) (ws : List Word) : Query := ⟨n, BitVec.ofNat _ (wordsToNat ws)⟩
theorem wordsToNat_append_single (l : List Word) (w : Word) :
    wordsToNat (l ++ [w]) = wordsToNat l + 2 ^ (64 * l.length) * w.toNat := by
  induction l with
  | nil => simp [wordsToNat]
  | cons x xs ih =>
    simp only [List.cons_append, wordsToNat, ih, List.length_cons]
    rw [show 64 * (xs.length + 1) = 64 + 64 * xs.length by ring, Nat.pow_add]
    ring
theorem readWords_succ_last (t : MachineState) (base : Word) (m : Nat) :
    t.readWords base (m + 1) = t.readWords base m ++ [t.getMem (base + BitVec.ofNat 64 (8 * m))] := by
  induction m generalizing base with
  | zero => simp
  | succ m ih =>
    rw [MachineState.readWords_succ, ih (base + 8), MachineState.readWords_succ]
    simp only [List.cons_append, List.cons.injEq, List.append_cancel_left_eq, List.cons.injEq,
      and_true, true_and]
    congr 1
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
    omega
theorem readWords_length (t : MachineState) (base : Word) (m : Nat) :
    (t.readWords base m).length = m := by
  induction m generalizing base with
  | zero => rfl
  | succ m ih => simp [ih]
private theorem foldl_range_succ (g : Nat → Nat) (N : Nat) :
    (List.range (N + 1)).foldl (fun acc i => acc + g i) 0 =
      (List.range N).foldl (fun acc i => acc + g i) 0 + g N := by
  rw [List.range_succ, List.foldl_append]; rfl
private theorem extractByte_toNat (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
private theorem word_bytes (x : Nat) (hx : x < 2 ^ 64) :
    x / 2 ^ (8 * 0) % 256 * 2 ^ (8 * 0) + x / 2 ^ (8 * 1) % 256 * 2 ^ (8 * 1) +
      x / 2 ^ (8 * 2) % 256 * 2 ^ (8 * 2) + x / 2 ^ (8 * 3) % 256 * 2 ^ (8 * 3) +
      x / 2 ^ (8 * 4) % 256 * 2 ^ (8 * 4) + x / 2 ^ (8 * 5) % 256 * 2 ^ (8 * 5) +
      x / 2 ^ (8 * 6) % 256 * 2 ^ (8 * 6) + x / 2 ^ (8 * 7) % 256 * 2 ^ (8 * 7) = x := by
  simp only [Nat.reducePow, Nat.reduceMul]
  omega
private theorem getByte_aligned (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b : Nat) (hb : b < 8) (hi : 8 * m + b < 2 ^ 64) :
    t.getByte (src + BitVec.ofNat 64 (8 * m + b)) =
      extractByte (t.getMem (src + BitVec.ofNat 64 (8 * m))) b := by
  unfold MachineState.getByte
  obtain ⟨h1, h2⟩ := aligned_add src (BitVec.ofNat 64 (8 * m + b)) hal
  rw [h1, h2, byteOffset_eq]
  have hlt : (BitVec.ofNat 64 (8 * m + b)).toNat = 8 * m + b := by
    simp only [BitVec.toNat_ofNat]; omega
  congr 2
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, hlt]
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [hlt]; omega
private theorem byte_term (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b i : Nat) (hb : b < 8) (hi : i = 8 * m + b) (hlt : i < 2 ^ 64) :
    (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i) =
      2 ^ (64 * m) * ((t.getMem (src + BitVec.ofNat 64 (8 * m))).toNat / 2 ^ (8 * b) % 256 *
        2 ^ (8 * b)) := by
  subst hi
  rw [getByte_aligned t src hal m b hb hlt, extractByte_toNat,
    show 8 * (8 * m + b) = 64 * m + 8 * b by ring, Nat.pow_add]
  ring
theorem hashInput_eq_words (t : MachineState) (n : Nat)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1))) (hn : 64 * (n + 1) < 2 ^ 64)
    (h10 : (t.getReg .x10).toNat % 8 = 0) :
    hashInput t = queryOfWords n (t.readWords (t.getReg .x10) (8 * (n + 1))) := by
  have hN : (t.getReg .x11).toNat / 64 - 1 = n := by
    rw [h11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
  generalize hsrc : t.getReg .x10 = src at h10
  have key : ∀ m, 8 * m ≤ 64 * (n + 1) →
      (List.range (8 * m)).foldl (fun acc i =>
        acc + (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0 =
        wordsToNat (t.readWords src m) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [show 8 * (m + 1) = 8 * m + 7 + 1 by omega]
      simp only [foldl_range_succ]
      rw [ih (by omega), readWords_succ_last, wordsToNat_append_single, readWords_length,
        byte_term t src h10 m 0 (8 * m) (by omega) (by omega) (by omega),
        byte_term t src h10 m 1 (8 * m + 1) (by omega) (by omega) (by omega),
        byte_term t src h10 m 2 (8 * m + 2) (by omega) (by omega) (by omega),
        byte_term t src h10 m 3 (8 * m + 3) (by omega) (by omega) (by omega),
        byte_term t src h10 m 4 (8 * m + 4) (by omega) (by omega) (by omega),
        byte_term t src h10 m 5 (8 * m + 5) (by omega) (by omega) (by omega),
        byte_term t src h10 m 6 (8 * m + 6) (by omega) (by omega) (by omega),
        byte_term t src h10 m 7 (8 * m + 6 + 1) (by omega) (by omega) (by omega)]
      generalize (t.getMem (src + BitVec.ofNat 64 (8 * m))) = w
      conv_rhs => rw [← word_bytes w.toNat w.isLt]
      ring
  have k := key (8 * (n + 1)) (by omega)
  rw [show 8 * (8 * (n + 1)) = 64 * (n + 1) by ring] at k
  unfold hashInput queryOfWords
  rw [hsrc]
  generalize (t.getReg .x11).toNat / 64 - 1 = N at hN ⊢
  subst hN
  simp only []
  rw [k]
end SigGolfCandidate.Rv
end
namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
theorem readLE_cons (b : UInt8) (L : List UInt8) : readLE (b :: L) = b.toNat + 256 * readLE L := rfl
theorem readLE_append (A B : List UInt8) : readLE (A ++ B) = readLE A + 256 ^ A.length * readLE B := by
  induction A with
  | nil => simp [readLE]
  | cons a A ih => rw [List.cons_append, readLE_cons, readLE_cons, ih, List.length_cons, pow_succ]; ring
theorem readLE_lt (L : List UInt8) : readLE L < 256 ^ L.length := by
  induction L with
  | nil => simp [readLE]
  | cons a L ih =>
      rw [readLE_cons, List.length_cons, pow_succ]
      have := a.toNat_lt
      omega
end SigGolfCandidate.T3M

-- ==== merged from T3M_Bytes ====
section

set_option maxRecDepth 20000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (readLE pad64 zero16 header privateInput Cache cacheBytes Region)
open SphincsSecurity (bytesLE bytesLE_length)
@[simp] theorem readLE_nil : readLE [] = 0 := rfl
theorem readLE_inj : ∀ {l₁ l₂ : List UInt8}, l₁.length = l₂.length → readLE l₁ = readLE l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hl, h => by
    simp only [readLE_cons, List.length_cons, Nat.add_right_cancel_iff] at hl h
    have h1 : b₁.toNat < 256 := b₁.toNat_lt
    have h2 : b₂.toNat < 256 := b₂.toNat_lt
    have hb : b₁.toNat = b₂.toNat := by omega
    have hr : readLE l₁ = readLE l₂ := by omega
    rw [UInt8.toNat_inj.mp hb, readLE_inj hl hr]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
@[simp] theorem readLE_replicate_zero (n : Nat) : readLE (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, readLE_cons, ih]; rfl
theorem readLE_ofFn_digits : ∀ (n N : Nat),
    readLE (List.ofFn fun i : Fin n => UInt8.ofNat (N / 256 ^ i.val % 256)) = N % 256 ^ n
  | 0, N => by simp [Nat.mod_one]
  | n + 1, N => by
    rw [List.ofFn_succ, readLE_cons]
    have e : (fun i : Fin n => UInt8.ofNat (N / 256 ^ (i.succ : Fin (n + 1)).val % 256)) =
        fun i : Fin n => UInt8.ofNat (N / 256 / 256 ^ i.val % 256) := by
      funext i
      rw [Fin.val_succ, pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    rw [e, readLE_ofFn_digits n (N / 256), pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    simp
theorem readLE_bytesLE (n : Nat) (x : BitVec (8 * n)) : readLE (bytesLE n x) = x.toNat := by
  have e : bytesLE n x = List.ofFn fun i : Fin n => UInt8.ofNat (x.toNat / 256 ^ i.val % 256) := by
    unfold bytesLE
    congr 1; funext i
    apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, UInt8.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [show 256 ^ i.val = 2 ^ (8 * i.val) by rw [Nat.pow_mul]]
    omega
  rw [e, readLE_ofFn_digits, Nat.mod_eq_of_lt]
  have := x.isLt
  rwa [Nat.pow_mul] at this
theorem readLE_div_mod (l : List UInt8) (i : Nat) : readLE l / 256 ^ i % 256 = (l.getD i 0).toNat := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rcases i with _ | i
    · have := b.toNat_lt
      simp only [readLE_cons, pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    · rw [readLE_cons, pow_succ, Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul,
        show (b.toNat + 256 * readLE l) / 256 = readLE l by have := b.toNat_lt; omega, ih]
      simp
def toQ (l : List UInt8) : Query := ⟨l.length / 64 - 1, BitVec.ofNat _ (readLE l)⟩
def Aligned (l : List UInt8) : Prop := 0 < l.length ∧ l.length % 64 = 0
def ofQ (q : Query) : List UInt8 := bytesLE (64 * (q.1 + 1)) q.2
theorem aligned_len {l : List UInt8} (h : Aligned l) : 64 * (l.length / 64 - 1 + 1) = l.length := by
  obtain ⟨h0, h64⟩ := h
  have : 1 ≤ l.length / 64 := by omega
  rw [Nat.sub_add_cancel this]
  omega
theorem toQ_injOn : Set.InjOn toQ {l | Aligned l} := by
  intro l₁ h₁ l₂ h₂ h
  have hn : l₁.length / 64 - 1 = l₂.length / 64 - 1 := congrArg (fun q : Query => q.1) h
  have ht : (toQ l₁).2.toNat = (toQ l₂).2.toNat := congrArg (fun q : Query => q.2.toNat) h
  have e₁ := aligned_len h₁
  have e₂ := aligned_len h₂
  have hlen : l₁.length = l₂.length := by omega
  simp only [toQ, BitVec.toNat_ofNat] at ht
  rw [e₁, e₂] at ht
  have hp : ∀ l : List UInt8, (2 : Nat) ^ (8 * l.length) = 256 ^ l.length := fun l => by
    rw [pow_mul]; norm_num
  rw [hp, hp, Nat.mod_eq_of_lt (readLE_lt l₁), Nat.mod_eq_of_lt (readLE_lt l₂)] at ht
  exact readLE_inj hlen ht
theorem blocks_toQ {l : List UInt8} (h : Aligned l) : (toQ l).blocks = l.length / 64 := by
  have := aligned_len h
  unfold toQ Query.blocks
  dsimp only
  omega
theorem ofQ_length (q : Query) : (ofQ q).length = 64 * (q.1 + 1) := bytesLE_length _ _
theorem toQ_eq (l : List UInt8) (n : Nat) (hl : l.length = 64 * (n + 1)) :
    toQ l = ⟨n, BitVec.ofNat _ (readLE l)⟩ := by
  have hn : l.length / 64 - 1 = n := by rw [hl]; omega
  unfold toQ
  rw [hn]
theorem toQ_ofQ (q : Query) : toQ (ofQ q) = q := by
  obtain ⟨n, v⟩ := q
  rw [toQ_eq _ n (ofQ_length _), ofQ, readLE_bytesLE]
  simp
theorem ofQ_toQ {l : List UInt8} (h : Aligned l) : ofQ (toQ l) = l := by
  have e := aligned_len h
  apply readLE_inj
  · rw [ofQ_length]; exact e
  · unfold ofQ toQ
    rw [readLE_bytesLE]
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hl := readLE_lt l
    rw [show (2 : Nat) ^ (8 * (64 * (l.length / 64 - 1 + 1))) = 256 ^ l.length by
      rw [e, pow_mul]; norm_num]
    exact hl
def wordsOf : List UInt8 → List Word
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      BitVec.ofNat 64 (readLE [b0, b1, b2, b3, b4, b5, b6, b7]) :: wordsOf rest
  | _ => []
@[simp] theorem wordsOf_nil : wordsOf [] = [] := rfl
theorem wordsOf_append8 (l rest : List UInt8) (hl : l.length = 8) :
    wordsOf (l ++ rest) = BitVec.ofNat 64 (readLE l) :: wordsOf rest := by
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl
theorem wordsOf_append (l₁ l₂ : List UInt8) (h : l₁.length % 8 = 0) :
    wordsOf (l₁ ++ l₂) = wordsOf l₁ ++ wordsOf l₂ := by
  obtain ⟨n, hn⟩ : ∃ n, l₁.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing l₁ with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0
      rw [List.length_eq_zero_iff] at hn
      subst hn; rfl
    · have ht : (l₁.take 8).length = 8 := by simp; omega
      rw [← List.take_append_drop 8 l₁, List.append_assoc,
        wordsOf_append8 (l₁.take 8) (l₁.drop 8 ++ l₂) ht, wordsOf_append8 (l₁.take 8) (l₁.drop 8) ht,
        ih (n - 8) (by omega) (l₁.drop 8) (by simp; omega) (by simp; omega)]
      rfl
theorem wordsOf_eq_range : ∀ (m : Nat) (l : List UInt8), l.length = 8 * m →
    wordsOf l = (List.range m).map fun j => BitVec.ofNat 64 (readLE l / 2 ^ (64 * j))
  | 0, l, h => by
    rw [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | m + 1, l, h => by
    have hl : l = l.take 8 ++ l.drop 8 := (List.take_append_drop 8 l).symm
    have ht : (l.take 8).length = 8 := by simp; omega
    have hd : (l.drop 8).length = 8 * m := by simp; omega
    have hr : readLE l = readLE (l.take 8) + 2 ^ 64 * readLE (l.drop 8) := by
      conv_lhs => rw [hl]
      rw [readLE_append, ht]; norm_num
    have hlt : readLE (l.take 8) < 2 ^ 64 := by
      have := readLE_lt (l.take 8); rw [ht] at this; norm_num at this ⊢; exact this
    rw [hl, wordsOf_append8 _ _ ht, ← hl, wordsOf_eq_range m _ hd, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.mul_zero, pow_zero, Nat.div_one, hr]
      omega
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp, hr]
      congr 1
      rw [show 64 * (j + 1) = 64 + 64 * j by ring, pow_add, ← Nat.div_div_eq_div_mul]
      congr 1
      omega
theorem length_wordsOf (m : Nat) (l : List UInt8) (h : l.length = 8 * m) : (wordsOf l).length = m := by
  rw [wordsOf_eq_range m l h]; simp
theorem wordsToNat_wordsOf : ∀ (m : Nat) (l : List UInt8), l.length = 8 * m →
    wordsToNat (wordsOf l) = readLE l
  | 0, l, h => by
    rw [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | m + 1, l, h => by
    have hl : l = l.take 8 ++ l.drop 8 := (List.take_append_drop 8 l).symm
    have ht : (l.take 8).length = 8 := by simp; omega
    have hd : (l.drop 8).length = 8 * m := by simp; omega
    have hlt : readLE (l.take 8) < 2 ^ 64 := by
      have := readLE_lt (l.take 8); rw [ht] at this; norm_num at this ⊢; exact this
    rw [hl, wordsOf_append8 _ _ ht, wordsToNat, wordsToNat_wordsOf m _ hd, readLE_append, ht,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    norm_num
theorem wordsOf_bytesLE (m : Nat) (x : BitVec (8 * (8 * m))) :
    wordsOf (bytesLE (8 * m) x) = (List.range m).map fun j => x.extractLsb' (64 * j) 64 := by
  rw [wordsOf_eq_range m _ (bytesLE_length _ _), readLE_bytesLE]
  apply List.map_congr_left
  intro j _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem wordsOf_bytesLE16 (x : BitVec 128) :
    wordsOf (bytesLE 16 x) = [x.extractLsb' 0 64, x.extractLsb' 64 64] :=
  wordsOf_bytesLE 2 x
theorem wordsOf_bytesLE32 (x : BitVec 256) :
    wordsOf (bytesLE 32 x) =
      [x.extractLsb' 0 64, x.extractLsb' 64 64, x.extractLsb' 128 64, x.extractLsb' 192 64] :=
  wordsOf_bytesLE 4 x
@[simp] theorem wordsOf_zero16 : wordsOf zero16 = [0, 0] := rfl
theorem wordsOf_replicate_zero (m : Nat) : wordsOf (List.replicate (8 * m) 0) = List.replicate m 0 := by
  rw [wordsOf_eq_range m _ (by simp), readLE_replicate_zero]
  apply List.ext_getElem (by simp)
  intro i _ _
  simp
theorem wordsOf_flatMap16 (ds : List (BitVec 128)) :
    wordsOf (ds.flatMap (bytesLE 16)) = ds.flatMap fun d => [d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by rw [bytesLE_length]),
      wordsOf_bytesLE16, ih]
def hdr0 (tag lay tree position : Nat) : Nat :=
  1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + tree / 2 ^ 32 % 256 * 2 ^ 24 + position % 2 ^ 32 * 2 ^ 32
def hdr1 (tree index : Nat) : Nat := tree % 2 ^ 32 + index % 2 ^ 32 * 2 ^ 32
theorem hdr0_lt (tag lay tree position : Nat) : hdr0 tag lay tree position < 2 ^ 64 := by
  unfold hdr0
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  have := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  omega
theorem hdr1_lt (tree index : Nat) : hdr1 tree index < 2 ^ 64 := by
  unfold hdr1
  have := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  omega
theorem nodeWord_3 (position index : Nat) : T3.nodeWord 3 position index = hdr1 index position := by
  simp [T3.nodeWord, T3.revNodeTag, hdr1]
theorem nodeWord_10 (position index : Nat) :
    T3.nodeWord 10 position index = T3.Rev.revBits 64 (hdr1 index position) := by
  simp [T3.nodeWord, T3.revNodeTag, hdr1]
theorem nodeWord_9 (position index : Nat) :
    T3.nodeWord 9 position index = T3.Rev.revBits 64 (hdr1 (index % 2 ^ 32 ^^^ 2048) position) := by
  have hx : index % 2 ^ 32 ^^^ 2048 < 2 ^ 32 := Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (by decide)
  simp only [T3.nodeWord, T3.revNodeTag, hdr1, Nat.mod_eq_of_lt hx]
  norm_num
theorem header_toNat (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat =
      if T3.packedNodeTag tag then hdr0 tag lay tree tree + 2 ^ 64 * T3.nodeWord tag position index
      else hdr0 tag lay tree position + 2 ^ 64 * hdr1 tree index := by
  unfold header hdr0 hdr1
  rw [BitVec.toNat_ofNat]
  have ht := Nat.mod_lt tag (by decide : 0 < 256)
  have hl := Nat.mod_lt lay (by decide : 0 < 256)
  have hth := Nat.mod_lt (tree / 2 ^ 32) (by decide : 0 < 256)
  have hp := Nat.mod_lt position (by decide : 0 < 2 ^ 32)
  have htl := Nat.mod_lt tree (by decide : 0 < 2 ^ 32)
  have hi := Nat.mod_lt index (by decide : 0 < 2 ^ 32)
  have hw := T3.nodeWord_lt tag position index
  split_ifs <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega
theorem header_lo (tag lay tree position index : Nat) :
    (header tag lay tree position index).extractLsb' 0 64 =
      BitVec.ofNat 64 (if T3.packedNodeTag tag then hdr0 tag lay tree tree else hdr0 tag lay tree position) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := hdr0_lt tag lay tree position
  have hp := hdr0_lt tag lay tree tree
  have h1 := hdr1_lt tree index
  have hq := T3.nodeWord_lt tag position index
  rw [BitVec.extractLsb'_toNat, header_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  split_ifs <;> omega
theorem header_hi (tag lay tree position index : Nat) :
    (header tag lay tree position index).extractLsb' 64 64 =
      BitVec.ofNat 64 (if T3.packedNodeTag tag then T3.nodeWord tag position index else hdr1 tree index) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := hdr0_lt tag lay tree position
  have hp := hdr0_lt tag lay tree tree
  have h1 := hdr1_lt tree index
  have hq := T3.nodeWord_lt tag position index
  rw [BitVec.extractLsb'_toNat, header_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split_ifs <;> omega
theorem wordsOf_header (tag lay tree position index : Nat) :
    wordsOf (bytesLE 16 (header tag lay tree position index)) =
      [BitVec.ofNat 64 (if T3.packedNodeTag tag then hdr0 tag lay tree tree else hdr0 tag lay tree position),
       BitVec.ofNat 64 (if T3.packedNodeTag tag then T3.nodeWord tag position index else hdr1 tree index)] := by
  rw [wordsOf_bytesLE16, header_lo, header_hi]
theorem header_packed_lo (tag lay tree position index : Nat)
    (hn : T3.packedNodeTag tag := by decide) :
    (header tag lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 tag lay tree tree) := by
  rw [header_lo, if_pos hn]
theorem header_packed_hi (tag lay tree position index : Nat)
    (hn : T3.packedNodeTag tag := by decide) :
    (header tag lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (T3.nodeWord tag position index) := by
  rw [header_hi, if_pos hn]
theorem header_packed_lo_3 (lay tree position index : Nat) :
    (header 3 lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 3 lay tree tree) :=
  header_packed_lo 3 lay tree position index (by decide)
theorem header_packed_hi_3 (lay tree position index : Nat) :
    (header 3 lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (hdr1 index position) := by
  rw [header_packed_hi 3 lay tree position index (by decide), nodeWord_3]
theorem header_packed_lo_9 (lay tree position index : Nat) :
    (header 9 lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 9 lay tree tree) :=
  header_packed_lo 9 lay tree position index (by decide)
theorem header_packed_hi_9 (lay tree position index : Nat) :
    (header 9 lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (T3.nodeWord 9 position index) :=
  header_packed_hi 9 lay tree position index (by decide)
theorem header_packed_lo_10 (lay tree position index : Nat) :
    (header 10 lay tree position index).extractLsb' 0 64 = BitVec.ofNat 64 (hdr0 10 lay tree tree) :=
  header_packed_lo 10 lay tree position index (by decide)
theorem header_packed_hi_10 (lay tree position index : Nat) :
    (header 10 lay tree position index).extractLsb' 64 64 = BitVec.ofNat 64 (T3.nodeWord 10 position index) :=
  header_packed_hi 10 lay tree position index (by decide)
theorem wordsOf_packed_header (tag lay tree position index : Nat)
    (hn : T3.packedNodeTag tag := by decide) :
    wordsOf (bytesLE 16 (header tag lay tree position index)) =
      [BitVec.ofNat 64 (hdr0 tag lay tree tree), BitVec.ofNat 64 (T3.nodeWord tag position index)] := by
  rw [wordsOf_bytesLE16, header_packed_lo _ _ _ _ _ hn, header_packed_hi _ _ _ _ _ hn]
theorem wordsOf_packed_header_3 (lay tree position index : Nat) :
    wordsOf (bytesLE 16 (header 3 lay tree position index)) =
      [BitVec.ofNat 64 (hdr0 3 lay tree tree), BitVec.ofNat 64 (hdr1 index position)] := by
  rw [wordsOf_packed_header 3 lay tree position index (by decide), nodeWord_3]
theorem hdr0_eq (tag lay tree position : Nat) (ht : tag < 256) (hl : lay < 256) (htr : tree < 2 ^ 32)
    (hp : position < 2 ^ 32) :
    hdr0 tag lay tree position = 1 + 256 * tag + 65536 * lay + 2 ^ 32 * position := by
  unfold hdr0
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hp, Nat.div_eq_of_lt htr]
  omega
theorem hdr1_eq (tree index : Nat) (htr : tree < 2 ^ 32) (hi : index < 2 ^ 32) :
    hdr1 tree index = tree + 2 ^ 32 * index := by
  unfold hdr1
  rw [Nat.mod_eq_of_lt htr, Nat.mod_eq_of_lt hi]
  omega
theorem pad64_of_aligned (l : List UInt8) (h : l.length % 64 = 0) : pad64 l = l := by
  unfold pad64; rw [h]; simp
theorem pad64_length (l : List UInt8) : (pad64 l).length = l.length + (64 - l.length % 64) % 64 := by
  simp [pad64]
theorem pad64_aligned (l : List UInt8) (h : 0 < l.length) : Aligned (pad64 l) := by
  rw [Aligned, pad64_length]; omega
theorem sk_words (sk : BitVec 256) :
    (sk.extractLsb' 0 128).extractLsb' 0 64 = sk.extractLsb' 0 64 ∧
    (sk.extractLsb' 0 128).extractLsb' 64 64 = sk.extractLsb' 64 64 ∧
    (sk.extractLsb' 128 128).extractLsb' 0 64 = sk.extractLsb' 128 64 ∧
    (sk.extractLsb' 128 128).extractLsb' 64 64 = sk.extractLsb' 192 64 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] <;>
    norm_num <;> omega
theorem privateInput_tweak (sk : BitVec 256) (tw : BitVec 128) :
    privateInput sk (.inl tw) = bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 tw ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 := by
  show pad64 (bytesLE 16 (sk.extractLsb' 0 128) ++ bytesLE 16 tw ++
      bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++ []) = _
  rw [List.append_nil, pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length]; rfl)]
theorem wordsOf_privateInput_tweak (sk : BitVec 256) (tw : BitVec 128) :
    wordsOf (privateInput sk (.inl tw)) =
      [sk.extractLsb' 0 64, sk.extractLsb' 64 64, tw.extractLsb' 0 64, tw.extractLsb' 64 64,
        sk.extractLsb' 128 64, sk.extractLsb' 192 64, 0, 0] := by
  obtain ⟨h1, h2, h3, h4⟩ := sk_words sk
  rw [privateInput_tweak, wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16, h1, h2, h3, h4]
  rfl
theorem privateInput_tweak_length (sk : BitVec 256) (tw : BitVec 128) :
    (privateInput sk (.inl tw)).length = 64 := by
  rw [privateInput_tweak]; simp [bytesLE_length, zero16]
theorem privateInput_mac_eq (sk : BitVec 256) (region : Region) :
    privateInput sk (.inr (.inr region)) = bytesLE 16 (sk.extractLsb' 0 128) ++
      bytesLE 16 (header 14 0 0 0 0) ++ bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++
      List.ofFn region ++ List.replicate 32 0 := by
  simp only [privateInput, pad64, List.length_append, bytesLE_length, zero16, List.length_replicate,
    List.length_ofFn]
theorem privateInput_mac_length (sk : BitVec 256) (region : Region) :
    (privateInput sk (.inr (.inr region))).length = 131136 := by
  rw [privateInput_mac_eq]
  simp only [List.length_append, bytesLE_length, List.length_ofFn, List.length_replicate, zero16]
theorem privateInput_nonce_eq (sk : BitVec 256) (m : T3.Message) :
    privateInput sk (.inr (.inl m)) = bytesLE 16 (sk.extractLsb' 0 128) ++
      bytesLE 16 (header 7 0 0 0 0) ++ bytesLE 16 (sk.extractLsb' 128 128) ++ zero16 ++
      bytesLE 32 m ++ List.replicate 32 0 := by
  simp only [privateInput, pad64, List.length_append, bytesLE_length, zero16, List.length_replicate]
theorem privateInput_aligned (sk : BitVec 256) (c : T3.Coordinate) : Aligned (privateInput sk c) := by
  rcases c with tw | m | region
  · rw [Aligned, privateInput_tweak_length]; omega
  · rw [Aligned, privateInput_nonce_eq]
    simp only [List.length_append, bytesLE_length, List.length_replicate, zero16]; decide
  · rw [Aligned, privateInput_mac_length]; omega
theorem hashInput_toQ (t : MachineState) (l : List UInt8) (n A : Nat)
    (hl : l.length = 64 * (n + 1)) (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A < 2 ^ 64) (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1)))
    (hn : 64 * (n + 1) < 2 ^ 64)
    (hw : t.readWords (BitVec.ofNat 64 A) (8 * (n + 1)) = wordsOf l) : hashInput t = toQ l := by
  rw [hashInput_eq_words t n h11 hn (by rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA']; exact hA),
    h10, hw, queryOfWords, wordsToNat_wordsOf (8 * (n + 1)) l (by rw [hl]; ring)]
  have hn' : l.length / 64 - 1 = n := by rw [hl]; omega
  unfold toQ
  rw [hn']
theorem readWords_add (t : MachineState) (A m₁ m₂ : Nat) :
    t.readWords (BitVec.ofNat 64 A) (m₁ + m₂) =
      t.readWords (BitVec.ofNat 64 A) m₁ ++ t.readWords (BitVec.ofNat 64 (A + 8 * m₁)) m₂ := by
  induction m₁ generalizing A with
  | zero => simp
  | succ m ih =>
    have e : BitVec.ofNat 64 A + 8 = BitVec.ofNat 64 (A + 8) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [show m + 1 + m₂ = (m + m₂) + 1 by omega, MachineState.readWords_succ,
      MachineState.readWords_succ, e, ih]
    simp only [List.cons_append]
    rw [show A + 8 + 8 * m = A + 8 * (m + 1) by ring]
theorem readWords_one (t : MachineState) (A : Nat) :
    t.readWords (BitVec.ofNat 64 A) 1 = [t.getMem (BitVec.ofNat 64 A)] := rfl
theorem readWords_two (t : MachineState) (A : Nat) :
    t.readWords (BitVec.ofNat 64 A) 2 =
      [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8))] := by
  have := readWords_add t A 1 1
  rw [readWords_one, readWords_one] at this
  simpa using this
private theorem foldl_range_succ (g : Nat → Nat) (N : Nat) :
    (List.range (N + 1)).foldl (fun acc i => acc + g i) 0 =
      (List.range N).foldl (fun acc i => acc + g i) 0 + g N := by
  rw [List.range_succ, List.foldl_append]; rfl
private theorem extractByte_toNat (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
private theorem word_bytes (x : Nat) (hx : x < 2 ^ 64) :
    x / 2 ^ (8 * 0) % 256 * 2 ^ (8 * 0) + x / 2 ^ (8 * 1) % 256 * 2 ^ (8 * 1) +
      x / 2 ^ (8 * 2) % 256 * 2 ^ (8 * 2) + x / 2 ^ (8 * 3) % 256 * 2 ^ (8 * 3) +
      x / 2 ^ (8 * 4) % 256 * 2 ^ (8 * 4) + x / 2 ^ (8 * 5) % 256 * 2 ^ (8 * 5) +
      x / 2 ^ (8 * 6) % 256 * 2 ^ (8 * 6) + x / 2 ^ (8 * 7) % 256 * 2 ^ (8 * 7) = x := by
  simp only [Nat.reducePow, Nat.reduceMul]
  omega
private theorem getByte_aligned (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b : Nat) (hb : b < 8) (hi : 8 * m + b < 2 ^ 64) :
    t.getByte (src + BitVec.ofNat 64 (8 * m + b)) =
      extractByte (t.getMem (src + BitVec.ofNat 64 (8 * m))) b := by
  unfold MachineState.getByte
  obtain ⟨h1, h2⟩ := aligned_add src (BitVec.ofNat 64 (8 * m + b)) hal
  rw [h1, h2, byteOffset_eq]
  have hlt : (BitVec.ofNat 64 (8 * m + b)).toNat = 8 * m + b := by
    simp only [BitVec.toNat_ofNat]; omega
  congr 2
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, hlt]
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [hlt]; omega
private theorem byte_term (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b i : Nat) (hb : b < 8) (hi : i = 8 * m + b) (hlt : i < 2 ^ 64) :
    (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i) =
      2 ^ (64 * m) * ((t.getMem (src + BitVec.ofNat 64 (8 * m))).toNat / 2 ^ (8 * b) % 256 *
        2 ^ (8 * b)) := by
  subst hi
  rw [getByte_aligned t src hal m b hb hlt, extractByte_toNat,
    show 8 * (8 * m + b) = 64 * m + 8 * b by ring, Nat.pow_add]
  ring
theorem foldl_bytes_eq_words (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0) :
    ∀ m, 8 * m < 2 ^ 64 →
      (List.range (8 * m)).foldl (fun acc i =>
        acc + (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0 =
        wordsToNat (t.readWords src m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [show 8 * (m + 1) = 8 * m + 7 + 1 by omega]
    simp only [foldl_range_succ]
    rw [ih (by omega), readWords_succ_last, wordsToNat_append_single, readWords_length,
      byte_term t src hal m 0 (8 * m) (by omega) (by omega) (by omega),
      byte_term t src hal m 1 (8 * m + 1) (by omega) (by omega) (by omega),
      byte_term t src hal m 2 (8 * m + 2) (by omega) (by omega) (by omega),
      byte_term t src hal m 3 (8 * m + 3) (by omega) (by omega) (by omega),
      byte_term t src hal m 4 (8 * m + 4) (by omega) (by omega) (by omega),
      byte_term t src hal m 5 (8 * m + 5) (by omega) (by omega) (by omega),
      byte_term t src hal m 6 (8 * m + 6) (by omega) (by omega) (by omega),
      byte_term t src hal m 7 (8 * m + 6 + 1) (by omega) (by omega) (by omega)]
    generalize (t.getMem (src + BitVec.ofNat 64 (8 * m))) = w
    conv_rhs => rw [← word_bytes w.toNat w.isLt]
    ring
theorem readBuffer_of_words (t : MachineState) (A m : Nat) (l : List UInt8) (hA : A % 8 = 0)
    (hA' : A + 8 * m < 2 ^ 64) (hl : l.length = 8 * m)
    (hw : t.readWords (BitVec.ofNat 64 A) m = wordsOf l) :
    readBuffer t A (8 * m) = BitVec.ofNat _ (readLE l) := by
  unfold readBuffer
  have e : ∀ i, BitVec.ofNat 64 (A + i) = BitVec.ofNat 64 A + BitVec.ofNat 64 i := fun i => by
    apply BitVec.eq_of_toNat_eq; simp
  simp only [e]
  rw [foldl_bytes_eq_words t _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show A < 2 ^ 64 by omega)]; exact hA) m
    (by omega), hw, wordsToNat_wordsOf m l hl]
def cacheB (c : SigGolfCandidate.T3.Cache) : Bytes 131072 := BitVec.ofNat _ (readLE (cacheBytes c))
def cacheDec (b : Bytes 131072) : SigGolfCandidate.T3.Cache :=
  ⟨b.extractLsb' 0 256, fun i => UInt8.ofNat (b.toNat / 256 ^ (32 + i.val) % 256)⟩
theorem cacheBytes_length (c : SigGolfCandidate.T3.Cache) : (cacheBytes c).length = 131072 := by
  simp only [cacheBytes, List.length_append, bytesLE_length, List.length_ofFn]
theorem two_pow_eight_mul (n : Nat) : (2 : Nat) ^ (8 * n) = 256 ^ n := by
  rw [pow_mul]; norm_num
theorem readLE_cacheBytes_lt (c : SigGolfCandidate.T3.Cache) : readLE (cacheBytes c) < 2 ^ (8 * 131072) := by
  have := readLE_lt (cacheBytes c)
  rwa [cacheBytes_length, ← two_pow_eight_mul] at this
theorem cacheDec_cacheB (c : SigGolfCandidate.T3.Cache) : cacheDec (cacheB c) = c := by
  obtain ⟨tag, region⟩ := c
  have hlt := readLE_cacheBytes_lt ⟨tag, region⟩
  have hr : readLE (cacheBytes ⟨tag, region⟩) = tag.toNat + 256 ^ 32 * readLE (List.ofFn region) := by
    rw [cacheBytes, readLE_append, readLE_bytesLE, bytesLE_length]
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by norm_num
  have htag : tag.toNat < 256 ^ 32 := by have := tag.isLt; rwa [h256] at this
  unfold cacheDec cacheB
  refine congrArg₂ SigGolfCandidate.T3.Cache.mk ?_ ?_
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.shiftRight_zero, hr,
      h256, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htag]
  · funext i
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, pow_add, ← Nat.div_div_eq_div_mul,
      hr, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt htag, Nat.zero_add, readLE_div_mod]
    have hi := (region i).toNat_lt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
    simp
theorem cacheB_cacheDec (b : Bytes 131072) : cacheB (cacheDec b) = b := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have e2 : (256 : Nat) ^ 131072 = 256 ^ 131040 * 256 ^ 32 := (pow_add 256 131040 32 : _)
  have hb' : b.toNat < 256 ^ 131040 * 256 ^ 32 := by
    have h := hb
    rw [two_pow_eight_mul, e2] at h; exact h
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by norm_num
  have h3 : b.toNat / 256 ^ 32 < 256 ^ 131040 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr hb'
  unfold cacheB cacheDec cacheBytes
  rw [BitVec.toNat_ofNat, readLE_append, readLE_bytesLE, bytesLE_length]
  have e : List.ofFn (fun i : Fin 131040 => UInt8.ofNat (b.toNat / 256 ^ (32 + i.val) % 256)) =
      List.ofFn fun i : Fin 131040 => UInt8.ofNat (b.toNat / 256 ^ 32 / 256 ^ i.val % 256) := by
    exact congrArg List.ofFn (funext fun i => by rw [pow_add, Nat.div_div_eq_div_mul])
  rw [e, readLE_ofFn_digits, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, h256, Nat.mod_eq_of_lt h3,
    Nat.mod_add_div]
  exact Nat.mod_eq_of_lt hb
end SigGolfCandidate.T3M
end

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 OracleComp
abbrev Layout := List (Nat × List (BitVec 32))
def layoutOk : Nat → Layout → Bool
  | _, [] => true
  | n, (o, seg) :: rest => (o == n) && layoutOk (n + seg.length) rest
def layoutCode (L : Layout) : List (BitVec 32) := (L.map Prod.snd).flatten
theorem layout_split : ∀ (L : Layout) (n i o : Nat) (seg : List (BitVec 32)),
    layoutOk n L = true → L[i]? = some (o, seg) →
    ∃ pre post, layoutCode L = pre ++ seg ++ post ∧ n + pre.length = o := by
  intro L
  induction L with
  | nil => intro n i o seg _ h; simp at h
  | cons p L ih =>
    intro n i o seg hok hi
    obtain ⟨o', seg'⟩ := p
    simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hok
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact ⟨[], layoutCode L, by simp [layoutCode], by simp [hok.1]⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨pre, post, h1, h2⟩ := ih _ i o seg hok.2 hi
      refine ⟨seg' ++ pre, post, ?_, ?_⟩
      · simp only [layoutCode, List.map_cons, List.flatten_cons] at h1 ⊢
        rw [h1]; simp
      · simp only [List.length_append]; omega
theorem codeAt_layout {image : Image} {L : Layout} (himage : image.code = layoutCode L)
    (hok : layoutOk 0 L = true) {i o : Nat} {seg : List (BitVec 32)}
    (hi : L[i]? = some (o, seg)) (hrange : 0x1000 + 4 * (o + seg.length) < 2 ^ 64) :
    CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * o)) seg := by
  obtain ⟨pre, post, h1, h2⟩ := layout_split L 0 i o seg hok hi
  refine CodeAt.of_append (himage.trans h1) _ ?_ (by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega
end SigGolfCandidate.Rv

-- ==== merged from Rv_Tactic ====
section

namespace SigGolfCandidate.Rv
open Lean Meta Elab Tactic Command
unsafe def evalOptResultUnsafe (e : Expr) : MetaM (Option Result) :=
  evalExpr (Option Result) (mkApp (mkConst ``Option [0]) (mkConst ``Result)) e
@[implemented_by evalOptResultUnsafe]
opaque evalOptResult (e : Expr) : MetaM (Option Result)
unsafe def evalExprExprUnsafe (e : Expr) : MetaM Expr := evalExpr Expr (mkConst ``Expr) e
@[implemented_by evalExprExprUnsafe]
opaque evalExprExpr (e : Expr) : MetaM Expr
def evalToLiteral (lhs : Expr) : MetaM Expr := do
  let lhs ← instantiateMVars lhs
  if lhs.hasFVar || lhs.hasMVar then
    throwError "sym_eval: the left-hand side must be a closed term, got{indentExpr lhs}"
  let α ← inferType lhs
  let u ← getLevel α
  let some u' := u.dec | throwError "sym_eval: type must live in `Type u`"
  let inst ← synthInstance (mkApp (mkConst ``Lean.ToExpr [u']) α)
  evalExprExpr (mkApp3 (mkConst ``Lean.toExpr [u']) α inst lhs)
def kernelEq (lhs lit : Expr) : MetaM Expr := do
  let ty ← mkEq lhs lit
  let pf ← mkEqRefl lit
  let name ← mkAuxLemma [] ty pf
  return mkConst name
elab "sym_eval" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "sym_eval: goal is not an equation"
  let lit ← evalToLiteral lhs
  unless ← isDefEq rhs lit do
    throwError "sym_eval: result mismatch; the computation returned{indentExpr lit}"
  goal.assign (← kernelEq lhs lit)
  replaceMainGoal []
section Shared
open Std
abbrev ShareM := StateM (HashMap USize Expr)
unsafe def eToExprShared (e : E) : ShareM Expr := do
  let key := ptrAddrUnsafe e
  if let some x := (← get).get? key then return x
  let x ← match e with
    | .c _ | .reg _ => pure (toExpr e)
    | .ld a => do pure (mkApp (mkConst ``E.ld) (← eToExprShared a))
    | .un op a => do pure (mkApp2 (mkConst ``E.un) (toExpr op) (← eToExprShared a))
    | .bin op a b => do
      pure (mkApp3 (mkConst ``E.bin) (toExpr op) (← eToExprShared a) (← eToExprShared b))
    | .ite op x y a b => do
      pure (mkApp5 (mkConst ``E.ite) (toExpr op) (← eToExprShared x) (← eToExprShared y)
        (← eToExprShared a) (← eToExprShared b))
  modify (·.insert key x)
  return x
unsafe def addrToExprShared (a : Addr) : ShareM Expr := do
  let b ← match a.base with
    | none => pure (mkApp (mkConst ``Option.none [0]) (mkConst ``E))
    | some b => do
      let x ← eToExprShared b
      pure (mkApp2 (mkConst ``Option.some [0]) (mkConst ``E) x)
  return mkApp2 (mkConst ``Addr.mk) b (toExpr a.off)
unsafe def obligToExprShared : Oblig → ShareM Expr
  | .valid a w => return mkApp2 (mkConst ``Oblig.valid) (← addrToExprShared a) (toExpr w)
  | .align8 b => return mkApp (mkConst ``Oblig.align8) (← eToExprShared b)
  | .ne a b => return mkApp2 (mkConst ``Oblig.ne) (← addrToExprShared a) (← addrToExprShared b)
def listLit (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)
unsafe def resultToExprSharedM (r : Result) : ShareM Expr := do
  let regs ← r.st.regs.fields.mapM eToExprShared
  let regsE := mkAppN (mkConst ``RegFile.mk) regs.toArray
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Addr) (mkConst ``E)
  let mem ← r.st.mem.mapM fun (k, v) => do
    return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Addr) (mkConst ``E)
      (← addrToExprShared k) (← eToExprShared v)
  let obl ← r.st.obl.mapM obligToExprShared
  let st := mkApp3 (mkConst ``SymState.mk) regsE (listLit pairTy mem)
    (listLit (mkConst ``Oblig) obl)
  return mkApp5 (mkConst ``Result.mk) st (← eToExprShared r.pc) (toExpr r.stop)
    (toExpr r.steps) (toExpr r.cycles)
unsafe def resultToExprSharedUnsafe (r : Result) : Expr :=
  (resultToExprSharedM r).run' {}
@[implemented_by resultToExprSharedUnsafe]
opaque resultToExprShared (r : Result) : Expr
end Shared
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := t.eq? | throwError "kernel_rfl: goal is not an equation"
  if t.hasFVar || t.hasMVar then throwError "kernel_rfl: goal must be closed"
  let pf ← mkEqRefl lhs
  let name ← mkAuxLemma [] t (← mkExpectedTypeHint pf t)
  let _ := rhs
  goal.assign (mkConst name)
  replaceMainGoal []
elab "sym_block " id:ident " := " t:term : command => do
  liftTermElabM do
    let e ← Term.elabTermEnsuringType t (mkApp (mkConst ``Option [0]) (mkConst ``Result))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasFVar || e.hasMVar then
      throwError "sym_block: the executor call must be a closed term"
    let v ← evalOptResult e
    let some r := v | throwError "sym_block: symbolic execution returned `none`{indentExpr e}"
    let base := (← getCurrNamespace) ++ id.getId
    let resName := base ++ `res
    addDecl <| Declaration.defnDecl {
      name := resName, levelParams := [], type := mkConst ``Result, value := resultToExprShared r,
      hints := .abbrev, safety := .safe }
    enableRealizationsForConst resName
    compileDecls #[resName]
    let lit := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Result) (mkConst resName)
    let ty ← mkEq e lit
    let pf ← mkEqRefl lit
    addDecl <| Declaration.thmDecl { name := base, levelParams := [], type := ty, value := pf }
    enableRealizationsForConst base
end SigGolfCandidate.Rv
end
