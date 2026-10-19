import SigGolfCandidate.T3M_Sim

/-!
# Bounded-cycle refinement helpers (top-bytes layer, keygen)

The top-bytes keygen grinds a nonce per top-tree node, so its cycle, call and compression counts are data dependent.
These are the `TBSim` (= `Sim` on `mrealize`) combinators the keygen proof needs besides those in `T3M/Sim.lean`:
program rewriting, `map`, the public-hash query, a `mapM` over `List.range` with a constant per-element bound and a
`foldlM` over `List.range'` with a per-iteration bound.
-/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.Rv
open SigGolfCandidate.T3 (M publicHash HashOutput)

section sim
variable {α β : Type} {image : Image}

theorem Sim.mapM_range' {δ : Type} (f : Nat → OracleComp HashSpec δ) (W : Nat)
    (Inv : List δ → MachineState → Prop) :
    ∀ (n a : Nat) (pre : List δ) {s : MachineState}, pre.length = a →
    (∀ (pre' : List δ) t, a ≤ pre'.length → pre'.length < a + n → Inv pre' t →
      Sim image t W (f pre'.length) (fun d u => Inv (pre' ++ [d]) u)) →
    Inv pre s →
    Sim image s (n * W) ((List.range' a n).mapM f) (fun ds u => ds.length = n ∧ Inv (pre ++ ds) u)
  | 0, a, pre, s, _, _, h0 => by
    simpa using Sim.pure (image := image) (Q := fun ds u => ds.length = 0 ∧ Inv (pre ++ ds) u)
      (a := []) (by simpa using h0)
  | n + 1, a, pre, s, hlen, hb, h0 => by
    rw [List.range'_succ, List.mapM_cons]
    have h1 := hb pre s (by omega) (by omega) h0
    rw [hlen] at h1
    have key : ∀ d t, Inv (pre ++ [d]) t → Sim image t (n * W)
        (do let ds ← (List.range' (a + 1) n).mapM f; Pure.pure (d :: ds))
        (fun ds u => ds.length = n + 1 ∧ Inv (pre ++ ds) u) := by
      intro d t ht
      have h2 := Sim.mapM_range' f W Inv n (a + 1) (pre ++ [d]) (by simp [hlen])
        (fun pre' t' h1' h2' => hb pre' t' (by omega) (by omega)) ht
      have := Sim.bind (W₂ := 0) h2 (f := fun ds => Pure.pure (d :: ds))
        (fun ds u hu => Sim.pure (image := image) (Q := fun ds u => ds.length = n + 1 ∧ Inv (pre ++ ds) u)
          ⟨by simp [hu.1], by simpa using hu.2⟩)
      simpa using this
    have := Sim.bind h1 key
    refine this.mono (by rw [Nat.succ_mul]; omega) (fun _ _ h => h)

theorem Sim.foldlM_range'_var {γ : Type} (a n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → Sim image t (W j) (f acc (a + j)) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    Sim image s (sumTo W n) ((List.range' a n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa [sumTo] using Sim.pure (image := image) h0
  | succ n ih =>
    rw [List.range'_concat, Nat.one_mul, List.foldlM_append]
    have := Sim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [a + n].foldlM f acc)
      (W₂ := W n) (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    simpa [sumTo] using this
end sim

section tbsim
variable {α β : Type} {image : Image} {sk : BitVec 256}

theorem TBSim.of_eq {s : MachineState} {W : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (he : p = q) : TBSim image sk s W q Q := he ▸ h

theorem TBSim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ

theorem TBSim.map {s : MachineState} {W : Nat} {p : M α} (f : α → β)
    {Q : β → MachineState → Prop} (h : TBSim image sk s W p (fun a t => Q (f a) t)) :
    TBSim image sk s W (f <$> p) Q := by
  rw [map_eq_bind_pure_comp]
  have := TBSim.bind (W₂ := 0) h (f := Pure.pure ∘ f) (Q₂ := Q) (fun a t ht => TBSim.pure ht)
  simpa using this

theorem TBSim.publicHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h

theorem TBSim.mapM_range {δ : Type} (n : Nat) (f : Nat → M δ) (W : Nat)
    (Inv : List δ → MachineState → Prop) {s : MachineState}
    (hbody : ∀ (pre : List δ) t, pre.length < n → Inv pre t →
      TBSim image sk t W (f pre.length) (fun d u => Inv (pre ++ [d]) u))
    (h0 : Inv [] s) :
    TBSim image sk s (n * W) ((List.range n).mapM f) (fun ds u => ds.length = n ∧ Inv ds u) := by
  unfold TBSim; rw [mrealize_mapM, List.range_eq_range']
  have := Sim.mapM_range' (image := image) (fun x => mrealize sk (f x)) W Inv n 0 [] rfl
    (fun pre' t _ h2 h3 => hbody pre' t (by omega) h3) h0
  simpa using this

theorem TBSim.foldlM_range'_var {γ : Type} (a n : Nat) (f : γ → Nat → M γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → TBSim image sk t (W j) (f acc (a + j)) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TBSim image sk s (sumTo W n) ((List.range' a n).foldlM f init) (Inv n) := by
  unfold TBSim; rw [mrealize_foldlM]
  exact Sim.foldlM_range'_var a n (fun acc x => mrealize sk (f acc x)) init Inv W hbody h0
end tbsim

section run
variable {α : Type}
/-- A bounded-cycle refinement determines the whole `runWith` result: the value, termination within `W + 1` cycles,
and the hash call / compression counts of `countBoth oa` evaluated at `hash`. -/
theorem Sim.runWith_eval (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W + 1 < CYCLE_LIMIT)
    (F : α → Output submission.sizes phase)
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
      t.getReg .x10 = 0 ∧ readOutput submission.sizes submission.layout phase t = F a)
    (hash : Hash) :
    (submission.runWith hash phase input).value = some (F (evalWithAnswerFn hash oa)) ∧
    (submission.runWith hash phase input).finished = true ∧
    (submission.runWith hash phase input).cycles ≤ W + 1 ∧
    (submission.runWith hash phase input).hashCalls = (evalWithAnswerFn hash (countBoth oa)).2.1 ∧
    (submission.runWith hash phase input).hashCompressions = (evalWithAnswerFn hash (countBoth oa)).2.2 := by
  obtain ⟨oc, hp, hf⟩ := hsim
  have hc : evalWithAnswerFn hash (countBoth oa) =
      ((evalWithAnswerFn hash oc).1.val, (evalWithAnswerFn hash oc).1.calls, (evalWithAnswerFn hash oc).1.blocks) := by
    rw [← hp, evalWithAnswerFn_map]
  have hv : evalWithAnswerFn hash oa = (evalWithAnswerFn hash oc).1.val := by
    rw [← fst_countBoth oa, evalWithAnswerFn_map, hc]
  rw [hc, hv, runWith_eq submission hash phase input s hinit, hf CYCLE_LIMIT (by omega),
    evalWithAnswerFn_bind, evalWithAnswerFn_map]
  generalize evalWithAnswerFn hash oc = o
  obtain ⟨h1, h2, h3, h4⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := by have := o.2.1; have := o.2.2.1; omega
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', evalWith_halt hash f h1 h2]
  have := o.2.2.1
  simp only [toRunResult, Execution.charge, h3, if_true, h4]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega
end run
end SigGolfCandidate.T3M
