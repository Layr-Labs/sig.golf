import SigGolfCandidate.SimCore
import SigGolfCandidate.Merge048
import SigGolfCandidate.FtsCode
set_option debug.skipKernelTC true
set_option linter.all false

/-! # FTS carrier grind: the expand witness post-pass (`POST`, 61050..61088)

Entered from the final HALT word (a `jal zero, POST`). For `k = 0..8` it reads the record of the coordinate with
frame base `sB k = 9768 - 848 k` (`slotA (sB k)`: witness pad address, nonce) and stores the nonce at the address,
then halts with the `ecall` at `POST + 38`. -/

namespace SigGolfCandidate.FtsGrind
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M

/-- Frame base of coordinate `k` in the expand FTS pass. -/
def sB (k : Nat) : Nat := 9768 - 848 * k
def cfgP : Config := { noAlias := true }
def postBody : List (BitVec 32) := postWords.take 38

sym_block ePost := symRun cfgP postWords (pcOf POST) 40

/-- `t3n` without the (not yet imported) `rv_simp` set: the Merge047 `rv_simp` lemmas listed explicitly. -/
macro "pn" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [Result.toState_getReg, Result.toState_getMem, Result.toState_pc, Result.toState_code,
      SymState.toState_getReg, SymState.toState_getMem, SymState.toState_pc, RegFile.get, E.eval, BinOp.eval,
      UnOp.eval, CmpOp.eval, LoadKind.fromWord, StoreKind.merge, Addr.eval, memEval_cons, memEval_nil,
      BitVec.add_zero, Oblig.all, Oblig.holds, Result.obligs, Result.pc, Result.st, Result.steps, Result.cycles,
      Result.stop, SymState.regs, SymState.mem, SymState.obl, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat,
      ofNat_eq_iff, BitVec.toNat_ofNat, memAccessValid_iff, MEMORY_BYTES, ne_eq, bne_iff_ne,
      decide_eq_true_eq, ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, $ts',*])

/-- One dword store. -/
def upd (M : Word → Word) (a : Word) (v : Word) : Word → Word := fun A => if A = a then v else M A
/-- Memory after the post-pass: the nine recorded nonces stored at the recorded addresses, `k = 0` first. -/
def postMem (M : Word → Word) : Word → Word :=
  (List.range 9).foldl (fun N k => upd N (M (BitVec.ofNat 64 (slotA (sB k))))
    (M (BitVec.ofNat 64 (slotA (sB k) + 8)))) M

/-- The recorded pad addresses: 8-aligned and below the record area. -/
def AddrsOK (M : Word → Word) : Prop :=
  ∀ k < 9, (M (BitVec.ofNat 64 (slotA (sB k)))).toNat % 8 = 0 ∧
    (M (BitVec.ofNat 64 (slotA (sB k)))).toNat + 8 ≤ SCR

theorem postBody_code {im : Image} (h : CodeAt im (pcOf POST) postWords) : CodeAt im (pcOf POST) postBody := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · have : postBody.length ≤ postWords.length := by decide
    omega
  · exact (List.take_prefix _ _).trans h4

/-- The post-pass: 38 steps to the halting `ecall` at `POST + 38`; memory is `postMem`. -/
theorem post_run {im : Image} (hc : CodeAt im (pcOf POST) postWords) (s : MachineState)
    (hpc : s.pc = pcOf POST) (addr : Nat → Nat)
    (hm : ∀ k < 9, s.getMem (BitVec.ofNat 64 (slotA (sB k))) = BitVec.ofNat 64 (addr k))
    (hb : ∀ k < 9, addr k % 8 = 0 ∧ addr k + 8 ≤ SCR) :
    ∃ t, Steps im s 38 38 t ∧ t.pc = pcOf (POST + 38) ∧ fetch im t = some (.base .ECALL) ∧
      RegsExcept s t [.x29, .x30, .x31] ∧ (∀ A, t.getMem A = postMem s.getMem A) := by
  have hc' := hc
  have h0 := hm 0 (by decide); have h1 := hm 1 (by decide); have h2 := hm 2 (by decide)
  have h3 := hm 3 (by decide); have h4 := hm 4 (by decide); have h5 := hm 5 (by decide)
  have h6 := hm 6 (by decide); have h7 := hm 7 (by decide); have h8 := hm 8 (by decide)
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide); have b4 := hb 4 (by decide); have b5 := hb 5 (by decide)
  have b6 := hb 6 (by decide); have b7 := hb 7 (by decide); have b8 := hb 8 (by decide)
  simp only [sB, slotA, SCR, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 h8 b0 b1 b2 b3 b4 b5 b6 b7 b8
  have hob : ePost.res.obligs s := by
    simp only [ePost.res]
    pn [h0, h1, h2, h3, h4, h5, h6, h7, h8]
    omega
  refine ⟨_, symRun_sound ePost hc' s hpc hob, ?_, symRun_ecall ePost hc' s hob rfl, ?_, ?_⟩
  · simp [ePost.res, Result.toState_pc, E.eval, POST]
  · intro r hr; simp at hr; cases r <;> simp_all [ePost.res] <;> pn [] <;> rfl
  · intro A
    simp only [Result.toState_getMem, ePost.res, postMem, upd, List.range, List.range.loop, List.foldl,
      sB, slotA, SCR]
    pn [h0, h1, h2, h3, h4, h5, h6, h7, h8]

end SigGolfCandidate.FtsGrind

