import SigGolfCandidate.Rv.Sound

set_option autoImplicit false
namespace W9Drv.ChildRouteStore
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv

def baseAddr (off : Nat) : Addr := ⟨some (.reg .x8), BitVec.ofNat 64 off⟩
def baseExpr (off : Nat) : E := addC (.reg .x8) (BitVec.ofNat 64 off)
def result (pc : Word) : Result :=
  ⟨⟨RegFile.init,
    [(baseAddr 904, .bin (.st .w 4) (.ld (baseExpr 904)) (.reg .x22))],
    [.align8 (.reg .x8), .valid (baseAddr 908) 4]⟩,
    .c (pc + 4), .fuel, 1, 1⟩
theorem run (pc : Word) : symRun {} [0x39642623] pc 1 = some (result pc) := by rfl

theorem addr_eval {s : MachineState} {B : Nat}
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (baseAddr off).eval s = BitVec.ofNat 64 (B + off) := by
  simp only [baseAddr, Addr.eval, E.eval, hB, BitVec.ofNat_add_ofNat]
theorem expr_eval {s : MachineState} {B : Nat}
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (baseExpr off).eval s = BitVec.ofNat 64 (B + off) := by
  rw [baseExpr, addC_eval]
  simp only [E.eval, hB, BitVec.ofNat_add_ofNat]

theorem execute {im : Image} (pc : Word) (hc : CodeAt im pc [0x39642623])
    (B : Nat) (s : MachineState) (hp : s.pc = pc)
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (h8 : B % 8 = 0)
    (hhi : B + 912 ≤ MEMORY_BYTES) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pc + 4 ∧
      (∀ r, t.getReg r = s.getReg r) ∧
      (∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
        if A = B + 904 then StoreKind.merge .w (s.getMem (BitVec.ofNat 64 (B + 904))) 4 (s.getReg .x22)
        else s.getMem (BitVec.ofNat 64 A)) := by
  have hB64 : B + 912 < 2 ^ 64 := by unfold MEMORY_BYTES at hhi; omega
  have hob : (result pc).obligs s := by
    apply (Oblig.all_iff s _).mpr
    intro o ho
    simp only [result, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, E.eval, hB, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : B < 2 ^ 64)]
      exact h8
    · simp only [Oblig.holds, addr_eval hB, accessValid, rangeValid,
        Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : B + 908 < 2 ^ 64)]
      exact ⟨hhi, by omega⟩
  let t := (result pc).toState s
  refine ⟨t, symRun_sound (run pc) hc s hp hob, rfl, ?_, ?_⟩
  · intro r
    exact (Result.toState_getReg _ _ _).trans (RegFile.init_get_eval _ _)
  · intro A hA
    change memEval s [(baseAddr 904, .bin (.st .w 4) (.ld (baseExpr 904)) (.reg .x22))] _ = _
    rw [memEval_cons, memEval_nil, addr_eval hB]
    have he : BitVec.ofNat 64 A = BitVec.ofNat 64 (B + 904) ↔ A = B + 904 := by
      constructor
      · intro h; have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA,
          Nat.mod_eq_of_lt (by omega : B + 904 < 2 ^ 64)] at this
        exact this
      · intro h; rw [h]
    simp only [he, E.eval, BinOp.eval, expr_eval hB]

theorem replace_hi_toNat (w : BitVec 64) (p : Nat) (hp : p < 2 ^ 32) :
    (replaceWord32 w 1 ((BitVec.ofNat 64 p).truncate 32)).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * p := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (1 * 32)) : BitVec 64) = BitVec.ofNat 64 (2 ^ 32 - 1) := by decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have e1 : (2 ^ 32 - 1) % 2 ^ 64 = 2 ^ 32 - 1 := by norm_num
  have e2 : p % 2 ^ 64 % 2 ^ 32 = p := by omega
  have e3 : p % 2 ^ 64 * 2 ^ (1 * 32) % 2 ^ 64 = 2 ^ 32 * p := by
    rw [Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]
    rw [Nat.mod_eq_of_lt (by norm_num; omega)]; ring
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, e3]
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

theorem merge_index_child (index child : Nat) (hi : index < 2 ^ 31) (hj : child < 128) :
    StoreKind.merge .w (BitVec.ofNat 64 index) 4 (BitVec.ofNat 64 child) =
      BitVec.ofNat 64 (index + 2 ^ 32 * child) := by
  apply BitVec.eq_of_toNat_eq
  change (replaceWord32 _ 1 _).toNat = _
  rw [replace_hi_toNat _ _ (by omega)]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : index < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : index < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : index + 2 ^ 32 * child < 2 ^ 64)]

theorem execute_header {im : Image} (pc : Word) (hc : CodeAt im pc [0x39642623])
    (B index child : Nat) (s : MachineState) (hp : s.pc = pc)
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (h8 : B % 8 = 0)
    (hhi : B + 912 ≤ MEMORY_BYTES) (hi : index < 2 ^ 31) (hj : child < 128)
    (hold : s.getMem (BitVec.ofNat 64 (B + 904)) = BitVec.ofNat 64 index)
    (hchild : s.getReg .x22 = BitVec.ofNat 64 child) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pc + 4 ∧
      (∀ r, t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 (B + 904)) = BitVec.ofNat 64 (index + 2 ^ 32 * child) ∧
      (∀ A, A < 2 ^ 64 → A ≠ B + 904 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) := by
  obtain ⟨t, hs, hpc, hr, hm⟩ := execute pc hc B s hp hB h8 hhi
  refine ⟨t, hs, hpc, hr, ?_, ?_⟩
  · rw [hm _ (by unfold MEMORY_BYTES at hhi; omega), if_pos rfl, hold, hchild,
      merge_index_child index child hi hj]
  · intro A hA hn; rw [hm A hA, if_neg hn]
end W9Drv.ChildRouteStore
