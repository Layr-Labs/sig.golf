import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge046

-- ==== merged from Rv_Api ====
section

namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 OracleComp
def BlockSpec (image : Image) (entry : Word) (k c : Nat) (P : MachineState → Prop)
    (Q : MachineState → MachineState → Prop) : Prop :=
  ∀ s, s.pc = entry → P s → ∃ t, Steps image s k c t ∧ Q s t
theorem BlockSpec.of_symRun {cfg : Config} {image : Image} {code : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg code pc fuel = some r)
    (hcode : CodeAt image pc code) {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop}
    (hobl : ∀ s, P s → r.obligs s) (hQ : ∀ s, P s → Q s (r.toState s)) :
    BlockSpec image pc r.steps r.cycles P Q :=
  fun s hpc hP => ⟨_, symRun_sound hrun hcode s hpc (hobl s hP), hQ s hP⟩
theorem BlockSpec.execute {image : Image} {entry : Word} {k c : Nat} {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop} (h : BlockSpec image entry k c P Q)
    (s : MachineState) (hpc : s.pc = entry) (hP : P s) (fuel : Nat) :
    ∃ t, Q s t ∧ Riscv.execute (fuel + k) image s =
      (fun e => e.charge c 0 0) <$> Riscv.execute fuel image t := by
  obtain ⟨t, hst, hQ⟩ := h s hpc hP
  exact ⟨t, hQ, hst.execute fuel⟩
theorem BlockSpec.evalWith {image : Image} {entry : Word} {k c : Nat} {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop} (h : BlockSpec image entry k c P Q) (hash : Hash)
    (s : MachineState) (hpc : s.pc = entry) (hP : P s) (fuel : Nat) :
    ∃ t, Q s t ∧ evalWithAnswerFn hash (Riscv.execute (fuel + k) image s) =
      (evalWithAnswerFn hash (Riscv.execute fuel image t)).charge c 0 0 := by
  obtain ⟨t, hst, hQ⟩ := h s hpc hP
  exact ⟨t, hQ, hst.evalWith hash fuel⟩
theorem BlockSpec.mono {image : Image} {entry : Word} {k c : Nat} {P P' : MachineState → Prop}
    {Q Q' : MachineState → MachineState → Prop} (h : BlockSpec image entry k c P Q)
    (hP : ∀ s, P' s → P s) (hQ : ∀ s t, P' s → Q s t → Q' s t) :
    BlockSpec image entry k c P' Q' := by
  intro s hpc hs
  obtain ⟨t, h1, h2⟩ := h s hpc (hP s hs)
  exact ⟨t, h1, hQ s t hs h2⟩
theorem Steps.iterate {image : Image} {k c : Nat} (Inv : Nat → MachineState → Prop)
    (body : ∀ i s, Inv (i + 1) s → ∃ t, Steps image s k c t ∧ Inv i t) :
    ∀ n s, Inv n s → ∃ t, Steps image s (n * k) (n * c) t ∧ Inv 0 t := by
  intro n
  induction n with
  | zero => intro s h; exact ⟨s, by simpa using Steps.refl s, h⟩
  | succ n ih =>
    intro s h
    obtain ⟨t, h1, h2⟩ := body n s h
    obtain ⟨u, h3, h4⟩ := ih t h2
    exact ⟨u, Steps.of_eq (h1.trans h3) (by rw [Nat.succ_mul, Nat.add_comm])
      (by rw [Nat.succ_mul, Nat.add_comm]), h4⟩
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
def readWordsSym (cfg : Config) (mem : SymMem) (k : Addr) : Nat → Option (List E × List Oblig)
  | 0 => some ([], [])
  | n + 1 =>
    match readMem cfg k mem, readWordsSym cfg mem ⟨k.base, k.off + 8⟩ n with
    | some (e, os), some (es, os') => some (e :: es, os ++ os')
    | _, _ => none
theorem Addr.eval_add8 (s : MachineState) (k : Addr) :
    (⟨k.base, k.off + 8⟩ : Addr).eval s = k.eval s + 8 := by
  rcases k with ⟨_ | b, off⟩
  · rfl
  · simp [Addr.eval, BitVec.add_assoc]
theorem readWordsSym_sound {cfg : Config} {mem : SymMem} (s : MachineState) (t : MachineState)
    (ht : ∀ a, t.getMem a = memEval s mem a) :
    ∀ (n : Nat) (k : Addr) (es : List E) (os : List Oblig),
      readWordsSym cfg mem k n = some (es, os) → (∀ o ∈ os, o.holds s) →
      t.readWords (k.eval s) n = es.map (E.eval s) := by
  intro n
  induction n with
  | zero => intro k es os h _; simp [readWordsSym] at h; rw [h.1]; rfl
  | succ n ih =>
    intro k es os h hos
    simp only [readWordsSym] at h
    split at h
    · rename_i e os1 es' os2 h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [MachineState.readWords_succ, ht, readMem_sound h1 s (fun o ho => hos o
        (List.mem_append_left _ ho)), ← Addr.eval_add8,
        ih _ es' os2 h2 (fun o ho => hos o (List.mem_append_right _ ho))]
      rfl
    · cases h
theorem Result.readWords_toState (r : Result) (s : MachineState) {cfg : Config} {k : Addr}
    {n : Nat} {es : List E} {os : List Oblig} (h : readWordsSym cfg r.st.mem k n = some (es, os))
    (hos : Oblig.all s os) :
    (r.toState s).readWords (k.eval s) n = es.map (E.eval s) :=
  readWordsSym_sound s (r.toState s) (fun _ => rfl) n k es os h ((Oblig.all_iff s _).mp hos)
theorem Result.hashInput_toState (r : Result) (s : MachineState) {cfg : Config} {k : Addr}
    {n : Nat} {es : List E} {os : List Oblig}
    (h10 : (r.st.regs.get .x10).eval s = k.eval s)
    (h11 : (r.st.regs.get .x11).eval s = BitVec.ofNat 64 (64 * (n + 1)))
    (hn : 64 * (n + 1) < 2 ^ 64) (hal : (k.eval s).toNat % 8 = 0)
    (h : readWordsSym cfg r.st.mem k (8 * (n + 1)) = some (es, os)) (hos : Oblig.all s os) :
    hashInput (r.toState s) = queryOfWords n (es.map (E.eval s)) := by
  rw [hashInput_eq_words (r.toState s) n (by simpa using h11) hn
    (by simpa [h10] using hal)]
  rw [Result.toState_getReg, h10, r.readWords_toState s h hos]
def Oblig.dedup : List Oblig → List Oblig
  | [] => []
  | o :: os => if os.any (Oblig.beq o) then Oblig.dedup os else o :: Oblig.dedup os
theorem Oblig.mem_dedup : ∀ {l : List Oblig} {o : Oblig}, o ∈ l → o ∈ Oblig.dedup l := by
  intro l
  induction l with
  | nil => intro o h; cases h
  | cons x xs ih =>
    intro o h
    simp only [Oblig.dedup]
    split
    · rename_i hany
      rcases List.mem_cons.mp h with rfl | h
      · obtain ⟨y, hy, hb⟩ := List.any_eq_true.mp hany
        rw [Oblig.beq_eq hb]; exact ih hy
      · exact ih h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)
theorem Result.obligs_of_dedup (r : Result) (s : MachineState) {l : List Oblig}
    (hl : Oblig.dedup r.st.obl = l) (h : Oblig.all s l) : r.obligs s := by
  subst hl
  rw [Result.obligs, Oblig.all_iff]
  intro o ho
  exact (Oblig.all_iff s _).mp h o (Oblig.mem_dedup ho)
theorem add_ofNat_big (x : Word) (n : Nat) (h1 : 2 ^ 63 ≤ n) (h2 : n < 2 ^ 64) :
    x + BitVec.ofNat 64 n = x - BitVec.ofNat 64 (2 ^ 64 - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - n < 2 ^ 64)]
  omega
attribute [rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.toState_getMem Result.pc Result.st Result.steps Result.cycles Result.stop
  SymState.regs SymState.mem SymState.obl BitVec.ofNat_eq_ofNat
open Lean Meta Simp in
simproc [rv_simp] addNegLit ((_ : BitVec 64) + BitVec.ofNat 64 _) := fun e => do
  let_expr HAdd.hAdd _ _ _ _ x c := e | return .continue
  let_expr BitVec.ofNat w n := c | return .continue
  let some wv := (← instantiateMVars w).nat? | return .continue
  unless wv == 64 do return .continue
  let some nv := (← instantiateMVars n).nat? | return .continue
  unless 2 ^ 63 ≤ nv ∧ nv < 2 ^ 64 do return .continue
  let m := 2 ^ 64 - nv
  let rhs ← mkAppM ``HSub.hSub #[x, mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit m)]
  let h1 ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit (2 ^ 63), n])
  let h2 ← mkDecideProof (← mkAppM ``LT.lt #[n, mkNatLit (2 ^ 64)])
  let pf := mkApp4 (mkConst ``add_ofNat_big) x n h1 h2
  let pf ← mkExpectedTypeHint pf (← mkEq e rhs)
  return .done { expr := rhs, proof? := some pf }
theorem accessValid_iff (a : Word) (w : Nat) :
    accessValid a w = true ↔ a.toNat + w ≤ MEMORY_BYTES ∧ a.toNat % w = 0 := by
  simp [accessValid, rangeValid]
macro "rv_obligs" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| (simp only [rv_simp, accessValid_iff, MEMORY_BYTES, ne_eq, BitVec.toNat_eq,
      BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, $ts',*] <;>
    (try and_intros) <;> omega))
end SigGolfCandidate.Rv
end
-- ==== merged from Rv ====
section

end
-- ==== merged from T3M_Verify_Exec ====
section

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
structure Br where
  op : CmpOp
  x : E
  y : E
  d : Bool
  deriving Repr
def Br.holds (s : MachineState) (b : Br) : Prop := b.op.eval (b.x.eval s) (b.y.eval s) = b.d
structure PRes where
  st : SymState
  pc : Word
  ecall : Bool
  steps : Nat
  cycles : Nat
  brs : List Br
  spc : Option E := none
  deriving Repr
def PRes.finalPc (r : PRes) (s : MachineState) : Word :=
  match r.spc with
  | some e => e.eval s
  | none => r.pc
def PRes.toState (r : PRes) (s : MachineState) : MachineState := r.st.toState s (r.finalPc s)
inductive Dir where
  | br (d : Bool)
  | jmp
  deriving Repr
def nextSym (pc : Word) (ctl : Option E) (dirs : List Dir) :
    Option ((Word × List Dir × List Br) ⊕ E) :=
  match ctl with
  | none => some (.inl (pc + 4, dirs, []))
  | some (.c t) => some (.inl (t, dirs, []))
  | some (.ite op x y (.c a) (.c b)) =>
    match dirs with
    | .br d :: ds => some (.inl (if d then a else b, ds, [⟨op, x, y, d⟩]))
    | _ => none
  | some e =>
    match dirs with
    | .jmp :: _ => some (.inr e)
    | _ => none
def pathAux (cfg : Config) (look : Nat → Option (BitVec 32)) (stops : List Word) :
    Nat → Word → List Dir → SymState → List Br → Option PRes
  | 0, _, _, _, _ => none
  | f + 1, pc, dirs, σ, brs =>
    if pc.toNat < 0x1000 || pc.toNat % 4 != 0 then none else
    match look ((pc.toNat - 0x1000) / 4) with
    | none => none
    | some w =>
      match decodeInstruction w with
      | none => none
      | some i =>
        if isEcall i then some ⟨σ, pc, true, 0, 0, brs, none⟩ else
        match classify i with
        | none => none
        | some m =>
          match symMicro cfg pc σ m with
          | none => none
          | some (σ', ctl) =>
            match nextSym pc ctl dirs with
            | none => none
            | some (.inr e) => some ⟨σ', 0, false, 1, instructionCycles i, brs, some e⟩
            | some (.inl (pc', dirs', nb)) =>
              if stops.contains pc' then some ⟨σ', pc', false, 1, instructionCycles i, nb ++ brs, none⟩
              else
                match pathAux cfg look stops f pc' dirs' σ' (nb ++ brs) with
                | none => none
                | some r => some { r with steps := r.steps + 1, cycles := instructionCycles i + r.cycles }
def LookOK (image : Image) (look : Nat → Option (BitVec 32)) : Prop :=
  ∀ n w, look n = some w → image.code[n]? = some w
theorem nextSym_sound {pc pc' : Word} {ctl : Option E} {dirs ds : List Dir} {nb : List Br}
    (h : nextSym pc ctl dirs = some (.inl (pc', ds, nb))) (s : MachineState) (hb : ∀ b ∈ nb, b.holds s) :
    nextPc s pc ctl = pc' := by
  unfold nextSym at h
  split at h
  · simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl
  · simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl
  · rename_i op x y a b
    split at h
    · rename_i d ds'
      simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      have := hb _ (List.mem_singleton_self _)
      simp only [Br.holds] at this
      simp only [nextPc, E.eval, this]
    · cases h
  · split at h
    · cases h
    · cases h
theorem nextSym_sound_jmp {pc : Word} {ctl : Option E} {dirs : List Dir} {e : E}
    (h : nextSym pc ctl dirs = some (.inr e)) (s : MachineState) :
    nextPc s pc ctl = e.eval s := by
  unfold nextSym at h
  split at h
  · cases h
  · cases h
  · split at h <;> cases h
  · split at h
    · rename_i e' _ _ _ _ _
      simp only [Option.some.injEq, Sum.inr.injEq] at h
      subst h; rfl
    · cases h
theorem fetch_of_look {image : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK image look)
    {pc : Word} {w : BitVec 32} (hpc : (pc.toNat < 0x1000 || pc.toNat % 4 != 0) = false)
    (hw : look ((pc.toNat - 0x1000) / 4) = some w) (t : MachineState) (ht : t.pc = pc) :
    fetch image t = decodeInstruction w := by
  unfold Riscv.fetch
  rw [ht, hpc]
  simp only [Bool.false_eq_true, if_false, hl _ _ hw]
  rfl
theorem pathAux_sound (cfg : Config) (image : Image) (look : Nat → Option (BitVec 32))
    (stops : List Word) (hl : LookOK image look) (s : MachineState) :
    ∀ (fuel : Nat) (pc : Word) (dirs : List Dir) (σ : SymState) (brs : List Br) (r : PRes),
      pathAux cfg look stops fuel pc dirs σ brs = some r →
      (∀ o ∈ r.st.obl, o.holds s) → (∀ b ∈ r.brs, b.holds s) →
      Steps image (σ.toState s pc) r.steps r.cycles (r.toState s) ∧ σ.obl ⊆ r.st.obl ∧
        brs ⊆ r.brs ∧ (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) := by
  intro fuel
  induction fuel with
  | zero => intro pc dirs σ brs r h; simp [pathAux] at h
  | succ f ih =>
    intro pc dirs σ brs r h hobl hbr
    simp only [pathAux] at h
    split at h
    · cases h
    · rename_i hpc
      have hpc' : (pc.toNat < 0x1000 || pc.toNat % 4 != 0) = false := by simpa using hpc
      split at h
      · cases h
      · rename_i w hw
        split at h
        · cases h
        · rename_i i hdec
          have hfetch : ∀ t : MachineState, t.pc = pc → fetch image t = some i := fun t ht =>
            (fetch_of_look hl hpc' hw t ht).trans hdec
          split at h
          · rename_i he
            simp only [Option.some.injEq] at h; subst h
            refine ⟨Steps.refl _, List.Subset.refl _, List.Subset.refl _, fun _ => ?_⟩
            rw [hfetch _ rfl, isEcall_eq he]
          · split at h
            · cases h
            · rename_i m hcl
              split at h
              · cases h
              · rename_i σ' ctl hm
                split at h
                · cases h
                · rename_i e hns
                  simp only [Option.some.injEq] at h; subst h
                  obtain ⟨hsub', hexec⟩ := symMicro_sound hm s hobl
                  refine ⟨?_, hsub', List.Subset.refl _, fun h => by cases h⟩
                  refine Steps.step (i := i) (hfetch _ rfl) ?_ (Steps.refl _)
                  rw [classify_sound hcl, hexec, nextSym_sound_jmp hns s]; rfl
                · rename_i pc' dirs' nb hns
                  split at h
                  · simp only [Option.some.injEq] at h; subst h
                    have hnb : ∀ b ∈ nb, b.holds s := fun b hb => hbr b (List.mem_append_left _ hb)
                    obtain ⟨hsub', hexec⟩ := symMicro_sound hm s hobl
                    refine ⟨?_, hsub', List.subset_append_right _ _, fun h => by cases h⟩
                    refine Steps.step (i := i) (hfetch _ rfl) ?_ (Steps.refl _)
                    rw [classify_sound hcl, hexec, nextSym_sound hns s hnb]; try rfl
                  · split at h
                    · cases h
                    · rename_i r' hr'
                      simp only [Option.some.injEq] at h; subst h
                      obtain ⟨hsteps, hsub, hbsub, hec⟩ := ih pc' dirs' σ' (nb ++ brs) r' hr' hobl hbr
                      have hnb : ∀ b ∈ nb, b.holds s := fun b hb =>
                        hbr b (hbsub (List.mem_append_left _ hb))
                      obtain ⟨hsub', hexec⟩ := symMicro_sound hm s (fun o ho => hobl o (hsub ho))
                      refine ⟨?_, List.Subset.trans hsub' hsub,
                        List.Subset.trans (List.subset_append_right _ _) hbsub, hec⟩
                      refine Steps.step (hfetch _ rfl) ?_ hsteps
                      rw [classify_sound hcl, hexec, nextSym_sound hns s hnb]; try rfl
def RegFile.withKnown (known : List (Reg × Word)) : RegFile :=
  known.foldl (fun rf p => rf.set p.1 (.c p.2)) RegFile.init
def σK (known : List (Reg × Word)) : SymState := ⟨RegFile.withKnown known, [], []⟩
theorem RegFile.withKnown_eval (s : MachineState) (known : List (Reg × Word))
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) (r : Reg) :
    ((RegFile.withKnown known).get r).eval s = s.getReg r := by
  unfold RegFile.withKnown
  suffices ∀ (l : List (Reg × Word)) (rf : RegFile), (∀ p ∈ l, s.getReg p.1 = p.2) →
      (∀ r, (rf.get r).eval s = s.getReg r) →
      ∀ r, ((l.foldl (fun rf p => rf.set p.1 (.c p.2)) rf).get r).eval s = s.getReg r from
    this known _ hk (RegFile.init_get_eval s) r
  intro l
  induction l with
  | nil => intro rf _ h; exact h
  | cons p l ih =>
    intro rf hl hrf
    obtain ⟨q, v⟩ := p
    simp only [List.foldl_cons]
    apply ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    intro r
    by_cases hr : r = q
    · subst hr
      by_cases h0 : r = .x0
      · subst h0; rfl
      · rw [RegFile.get_set_self _ _ h0]; simp only [E.eval]
        exact (hl (r, v) (List.mem_cons_self ..)).symm
    · rw [RegFile.get_set_ne _ _ hr]; exact hrf r
theorem σK_toState (s : MachineState) (known : List (Reg × Word))
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) : (σK known).toState s s.pc = s := by
  apply MachineState.ext' <;> try rfl
  funext r
  simp only [SymState.toState, σK]
  split
  · rename_i h; subst h; rfl
  · rename_i h
    rw [RegFile.withKnown_eval s known hk r]
    cases r <;> first | exact absurd rfl h | rfl
theorem pathRun_sound {cfg : Config} {image : Image} {look : Nat → Option (BitVec 32)}
    {stops : List Word} {fuel : Nat} {pc : Word} {dirs : List Dir} {known : List (Reg × Word)}
    {r : PRes} (h : pathAux cfg look stops fuel pc dirs (σK known) [] = some r)
    (hl : LookOK image look) (s : MachineState) (hpc : s.pc = pc)
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) (hobl : ∀ o ∈ r.st.obl, o.holds s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) := by
  obtain ⟨h1, -, -, h4⟩ := pathAux_sound cfg image look stops hl s fuel pc dirs _ [] r h hobl hbr
  rw [← hpc, σK_toState s known hk] at h1
  exact ⟨h1, h4⟩
def listBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listBeq f as bs
  | _, _ => false
theorem listBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, listBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [listBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [listBeq] at h
    | cons b bs =>
      simp only [listBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]
def RegFile.beq (a b : RegFile) : Bool := listBeq E.beq a.fields b.fields
theorem RegFile.beq_eq {a b : RegFile} (h : RegFile.beq a b = true) : a = b := by
  have := listBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl
def pairBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2
theorem pairBeq_eq {a b : Addr × E} (h : pairBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [pairBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]
def SymState.beq (a b : SymState) : Bool :=
  RegFile.beq a.regs b.regs && listBeq pairBeq a.mem b.mem && listBeq Oblig.beq a.obl b.obl
theorem SymState.beq_eq {a b : SymState} (h : SymState.beq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [SymState.beq, Bool.and_eq_true] at h
  rw [RegFile.beq_eq h.1.1, listBeq_eq (fun _ _ => pairBeq_eq) h.1.2,
    listBeq_eq (fun _ _ => Oblig.beq_eq) h.2]
def Br.beq (a b : Br) : Bool :=
  decide (a.op = b.op) && E.beq a.x b.x && E.beq a.y b.y && a.d == b.d
theorem Br.beq_eq {a b : Br} (h : Br.beq a b = true) : a = b := by
  obtain ⟨o, x, y, d⟩ := a; obtain ⟨o', x', y', d'⟩ := b
  simp only [Br.beq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [h1, E.beq_eq h2, E.beq_eq h3, h4]
def optEBeq : Option E → Option E → Bool
  | none, none => true
  | some a, some b => E.beq a b
  | _, _ => false
theorem optEBeq_eq {a b : Option E} (h : optEBeq a b = true) : a = b := by
  cases a <;> cases b <;> simp [optEBeq] at h ⊢
  exact E.beq_eq h
def PRes.beq (a b : PRes) : Bool :=
  SymState.beq a.st b.st && a.pc.toNat == b.pc.toNat && a.ecall == b.ecall &&
    a.steps == b.steps && a.cycles == b.cycles && listBeq Br.beq a.brs b.brs && optEBeq a.spc b.spc
theorem PRes.beq_eq {a b : PRes} (h : PRes.beq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := a; obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp only [PRes.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  rw [SymState.beq_eq h1, BitVec.eq_of_toNat_eq h2, h3, h4, h5, listBeq_eq (fun _ _ => Br.beq_eq) h6,
    optEBeq_eq h7]
def optBeq (o : Option PRes) (r : PRes) : Bool :=
  match o with
  | some r' => PRes.beq r' r
  | none => false
theorem optBeq_eq {o : Option PRes} {r : PRes} (h : optBeq o r = true) : o = some r := by
  cases o with
  | none => simp [optBeq] at h
  | some r' => simp only [optBeq] at h; rw [PRes.beq_eq h]
end SigGolfCandidate.T3M.Verify
end
