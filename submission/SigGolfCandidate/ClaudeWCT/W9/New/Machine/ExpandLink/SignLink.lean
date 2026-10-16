import SigGolfCandidate.T3M.Sign.BoundaryInvariant
import SigGolfCandidate.T3M.Sign.InitState
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.Main

namespace ClaudeWCT.W9.Machine.SignLink
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.Boundary
open ClaudeWCT.W9.Machine.Sign (TableAt CostAt TBL COST tblBytes costBytes HookPre)
set_option maxRecDepth 100000
theorem signPrefixData_split : Images.signPrefixData = costBytes ++ tblBytes := by
  unfold Images.signPrefixData ClaudeWCT.W9.Machine.Sign.costBytes ClaudeWCT.W9.Machine.Sign.tblBytes
  rw [← List.flatten_append]
  rfl
theorem signData_split : Images.signData = costBytes ++ (tblBytes ++ Images.signLegacyData) := by
  rw [Images.signData, signPrefixData_split, List.append_assoc]
theorem slice_mid {α : Type} (l1 l2 l3 : List α) (n : Nat) (h : n + 8 ≤ l2.length) :
    ((l1 ++ (l2 ++ l3)).drop (l1.length + n)).take 8 = (l2.drop n).take 8 := by
  rw [List.drop_append, List.drop_eq_nil_of_le (show l1.length ≤ l1.length + n by omega), List.nil_append,
    Nat.add_sub_cancel_left, List.drop_append_of_le_length (show n ≤ l2.length by omega),
    List.take_append_of_le_length (show 8 ≤ (l2.drop n).length by rw [List.length_drop]; omega)]
theorem slice_head {α : Type} (l1 l2 : List α) (n : Nat) (h : n + 8 ≤ l1.length) :
    ((l1 ++ l2).drop n).take 8 = (l1.drop n).take 8 := by
  rw [List.drop_append_of_le_length (show n ≤ l1.length by omega),
    List.take_append_of_le_length (show 8 ≤ (l1.drop n).length by rw [List.length_drop]; omega)]
theorem sinit_wct_cost (sk : SecretKey) (cache : Bytes 131072) (m : Message) : CostAt (sinit sk cache m) := by
  intro k hk
  have hc := ClaudeWCT.W9.Machine.Sign.SearchM.costBytes_length
  rw [sinit_getMem _ _ _ _ (by unfold COST; omega), if_neg (by unfold COST; omega), if_neg (by unfold COST; omega),
    if_neg (by unfold COST; omega), sdata_getMem _ (by unfold COST; omega),
    if_pos (by unfold COST SIGN_DATA; omega), show COST + 8 * k - SIGN_DATA = 8 * k by unfold COST SIGN_DATA; omega,
    signData_split, slice_head _ _ _ (by omega)]
theorem sinit_wct_table (sk : SecretKey) (cache : Bytes 131072) (m : Message) : TableAt (sinit sk cache m) := by
  intro k hk
  have hc := ClaudeWCT.W9.Machine.Sign.SearchM.costBytes_length
  have ht := ClaudeWCT.W9.Machine.Sign.tblBytes_length
  rw [sinit_getMem _ _ _ _ (by unfold TBL; omega), if_neg (by unfold TBL; omega), if_neg (by unfold TBL; omega),
    if_neg (by unfold TBL; omega), sdata_getMem _ (by unfold TBL; omega),
    if_pos (by unfold TBL SIGN_DATA; omega), show TBL + 8 * k - SIGN_DATA = costBytes.length + 8 * k by
      rw [hc]; unfold TBL SIGN_DATA; omega,
    signData_split, slice_mid _ _ _ _ (by omega)]
theorem hook_v7 {sk : SecretKey} {cache : Bytes 131072} {m : Message} {rho : SigGolfCandidate.T3.Digest}
    {t : MachineState} (h : NoncePost sk cache m rho t) : HookPre sk m rho t := by
  refine ⟨⟨h.search.pc, h.search.x5, h.search.x19, h.search.rho, h.search.msg, ?_⟩, h.rho, ?_, ?_, ?_⟩
  · intro k hk
    rw [h.frame.get (by unfold COST; omega) (by unfold FrontW COST; sg_omega)]
    exact sinit_wct_cost sk cache m k hk
  · intro k hk
    change t.getMem (BitVec.ofNat 64 (0x80 + 8 * k)) = _
    rw [h.frame.get (by omega) (by unfold FrontW; sg_omega)]
    exact sinit_sk sk cache m k hk
  · intro A hA
    simp only [ClaudeWCT.W9.Machine.Sign.ScrZero, ClaudeWCT.W9.Machine.Sign.PRIVW, ClaudeWCT.W9.Machine.Sign.CHAINW,
      ClaudeWCT.W9.Machine.Sign.NODEW] at hA
    rw [h.frame.get (by omega) (by unfold FrontW; sg_omega)]
    exact sinit_zero sk cache m A (by unfold SIGN_DATA; omega) (by sg_omega)
  · intro k hk
    rw [h.frame.get (by unfold TBL; omega) (by unfold FrontW TBL; sg_omega)]
    exact sinit_wct_table sk cache m k hk
end ClaudeWCT.W9.Machine.SignLink

namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))
def preTailLook (n : Nat) := if n<20743 then tailLook n else none
def preHookLook (n : Nat) := if n=540 then hookLook n else none
def preCLook (n : Nat) := if n<20743 ∨ 20813≤n ∧ n<20832 then cLook n else none
def cHook : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 20730, false, 1, 1, [], none⟩
def cLoopRegs : RegFile :=
  (((RegFile.init.set .x6 (.ld (.reg .x28))).set .x7 (.ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8))))).set .x28
    (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16)))).set .x29 (.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16)))
def cLoopMem : SymMem :=
  [(⟨some (.reg .x29), BitVec.ofNat 64 8⟩, .ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8)))), (⟨some (.reg .x29), BitVec.ofNat 64 0⟩, .ld (.reg .x28))]
def cLoopObl : List Oblig :=
  [.valid ⟨some (.reg .x29), BitVec.ofNat 64 8⟩ 8, .valid ⟨some (.reg .x29), BitVec.ofNat 64 0⟩ 8, .valid ⟨some (.reg .x28), BitVec.ofNat 64 8⟩ 8,
    .valid ⟨some (.reg .x28), BitVec.ofNat 64 0⟩ 8]
def cBr (d : Bool) : Br := ⟨.ltu, .bin .add (.reg .x28) (.c (BitVec.ofNat 64 16)), .reg .x30, d⟩
def cBack : PRes := ⟨⟨cLoopRegs, cLoopMem, cLoopObl⟩, pcOf 20736, false, 7, 7, [cBr true], none⟩
def cExit : PRes :=
  ⟨⟨cLoopRegs, cLoopMem, cLoopObl⟩, pcOf 20743, false, 7, 7, [cBr false], none⟩
theorem run_cHook : run preHookLook [20730] 540 [] = some cHook := optBeq_eq (by decide +kernel)
theorem run_cBack : run preTailLook [20736] 20736 [.br true] = some cBack := optBeq_eq (by decide +kernel)
theorem run_cExit : run preTailLook [20736,20743] 20736 [.br false] = some cExit := optBeq_eq (by decide +kernel)
theorem cLoopMem_get (s : MachineState) (S D A : Nat) (hD : D + 16 < 2 ^ 64)
    (hA : A < 2 ^ 64) (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    memEval s cLoopMem (BitVec.ofNat 64 A) =
      if A = D + 8 then s.getMem (BitVec.ofNat 64 (S + 8)) else if A = D then s.getMem (BitVec.ofNat 64 S)
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold cLoopMem
  rw [memEval_cons, memEval_cons, memEval_nil]
  have e1 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 8⟩ = BitVec.ofNat 64 (D + 8) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 8
  have e0 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 0⟩ = BitVec.ofNat 64 D := by
    simp only [Addr.eval, E.eval, h29, ofNat_add_ofNat, Nat.add_zero]
  have v1 : (E.ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8)))).eval s = s.getMem (BitVec.ofNat 64 (S + 8)) := by
    simp only [E.eval, BinOp.eval, h28]; rw [ofNat_add_ofNat S 8]
  have v0 : (E.ld (.reg .x28)).eval s = s.getMem (BitVec.ofNat 64 S) := by
    simp only [E.eval, h28]
  rw [e1, e0, v1, v0]
  simp only [ofNat_inj hA (show D + 8 < 2 ^ 64 by so), ofNat_inj hA (show D < 2 ^ 64 by so)]
theorem cLoopObl_holds (s : MachineState) (S D : Nat) (hS : S + 16 ≤ MEMORY_BYTES) (hD : D + 16 ≤ MEMORY_BYTES)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    ∀ o ∈ cLoopObl, o.holds s := by
  unfold MEMORY_BYTES at hS hD
  intro o ho
  simp only [cLoopObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;>
    simp only [Oblig.holds, Addr.eval, E.eval, h28, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
theorem cBr_holds (s : MachineState) (S : Nat) (d : Bool) (hS : S + 16 < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h30 : s.getReg .x30 = BitVec.ofNat 64 (SIG + 5616))
    (hd : (decide (S + 16 < SIG + 5616)) = d) : (cBr d).holds s := by
  simp only [Br.holds, cBr, CmpOp.eval, E.eval, BinOp.eval, h28, h30]
  rw [ofNat_add_ofNat]
  rw [← hd]
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS, Nat.mod_eq_of_lt (show SIG + 5616 < 2 ^ 64 by
    decide)]
structure CInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 20736
  x28 : t.getReg .x28 = BitVec.ofNat 64 (SIG + 2192 + 16 * k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (SIG + 1888 + 16 * k)
  x30 : t.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)
  done : ∀ j < 2 * k, t.getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * j)) = s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 8 * j))
  frame : Frame s0 t (fun A => SIG + 1888 ≤ A ∧ A < SIG + 1888 + 16 * k)
theorem cIter_mem {s0 t : MachineState} {k : Nat} (hk : k < 214) (h : CInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (A : Nat) (hA : A < 2 ^ 64) :
    (r.toState t).getMem (BitVec.ofNat 64 A) =
      if A = SIG + 1888 + 16 * k + 8 then s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * k + 8))
      else if A = SIG + 1888 + 16 * k then s0.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * k))
      else t.getMem (BitVec.ofNat 64 A) := by
  rw [PRes.toState_getMem', hmem, cLoopMem_get t _ _ A (by so) hA h.x28 h.x29]
  rw [h.frame.get (by so) (by so), h.frame.get (by so) (by so)]
theorem cIter_inv {s0 t : MachineState} {k : Nat} (hk : k < 214) (h : CInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (u : MachineState) (hu : u = r.toState t)
    (hpc : u.pc = pcOf 20736) (h28 : u.getReg .x28 = BitVec.ofNat 64 (SIG + 2192 + 16 * (k + 1)))
    (h29 : u.getReg .x29 = BitVec.ofNat 64 (SIG + 1888 + 16 * (k + 1)))
    (h30 : u.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)) : CInv s0 (k + 1) u := by
  subst hu
  refine ⟨hpc, h28, h29, h30, fun j hj => ?_, fun A hA hn => ?_⟩
  · rw [cIter_mem hk h r hmem _ (by so)]
    by_cases hj2 : j < 2 * k
    · rw [if_neg (by so), if_neg (by so)]; exact h.done j hj2
    · by_cases hje : j = 2 * k
      · subst hje; rw [if_neg (by so), if_pos (by so)]; congr 2; omega
      · have : j = 2 * k + 1 := by so
        subst this; rw [if_pos (by so)]; congr 2; omega
  · rw [cIter_mem hk h r hmem A hA, if_neg (by so), if_neg (by so)]
    exact h.frame.get hA (by so)
theorem cLoop {im : Image} (hl : LookOK im preTailLook) {s0 u : MachineState} (h0 : CInv s0 0 u) :
    ∀ k, k ≤ 213 → ∃ t, Steps im u (7 * k) (7 * k) t ∧ CInv s0 k t := by
  intro k
  induction k with
  | zero => intro _; exact ⟨u, Steps.refl u, h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨t, st, ht⟩ := ih (by so)
    obtain ⟨st1, -⟩ := run_sound hl run_cBack t ht.pc
      (cLoopObl_holds t _ _ (by so) (by so) (by so)
        (by so) ht.x28 ht.x29)
      (by
        intro b hb
        simp only [cBack, List.mem_singleton] at hb
        subst hb
        exact cBr_holds t _ true (by so) ht.x28 ht.x30 (by simp; omega))
    refine ⟨_, (st.trans st1).of_eq (by simp [cBack]; ring) (by simp [cBack]; ring),
      cIter_inv (by so) ht cBack rfl _ rfl (PRes.toState_pc' _ _ rfl) ?_ ?_ ?_⟩
    · rw [PRes.toState_getReg']
      show (E.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16))).eval t = _
      simp only [E.eval, BinOp.eval, ht.x28]; rw [ofNat_add_ofNat]; congr 1
    · rw [PRes.toState_getReg']
      show (E.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16))).eval t = _
      simp only [E.eval, BinOp.eval, ht.x29]; rw [ofNat_add_ofNat]; congr 1
    · rw [PRes.toState_getReg']; exact ht.x30
/-- [h2 lane] the sign prepass (words 20813..20831, entered from the copy hook at 20730). -/
def pSetupRegs : RegFile :=
  ((((RegFile.init.set .x14 (.ld (.c (BitVec.ofNat 64 0x7ca0)))).set .x15 (.ld (.c (BitVec.ofNat 64 0x7ca8)))).set .x28
    (.c (BitVec.ofNat 64 0x7cb0))).set .x29 (.c (BitVec.ofNat 64 0x7ca0))).set .x30 (.c (BitVec.ofNat 64 0x85f0))
def pSetup : PRes := ⟨⟨pSetupRegs, [], []⟩, pcOf 20821, false, 9, 9, [], none⟩
def pBack : PRes := ⟨⟨cLoopRegs, cLoopMem, cLoopObl⟩, pcOf 20821, false, 7, 7, [cBr true], none⟩
def pExitRegs : RegFile :=
  ((cLoopRegs.set .x28 (.c (BitVec.ofNat 64 0x7890))).set .x29 (.c (BitVec.ofNat 64 0x7760))).set .x30
    (.c (BitVec.ofNat 64 0x85f0))
def pExitMem : SymMem :=
  (⟨some (.reg .x29), BitVec.ofNat 64 24⟩, .reg .x15) :: (⟨some (.reg .x29), BitVec.ofNat 64 16⟩, .reg .x14) :: cLoopMem
def pExitObl : List Oblig :=
  .valid ⟨some (.reg .x29), BitVec.ofNat 64 24⟩ 8 :: .valid ⟨some (.reg .x29), BitVec.ofNat 64 16⟩ 8 :: cLoopObl
def pExit : PRes := ⟨⟨pExitRegs, pExitMem, pExitObl⟩, pcOf 20736, false, 16, 16, [cBr false], none⟩
theorem run_pSetup : run preCLook [20821] 20730 [] = some pSetup := optBeq_eq (by decide +kernel)
theorem run_pBack : run preCLook [20821] 20821 [.br true] = some pBack := optBeq_eq (by decide +kernel)
theorem run_pExit : run preCLook [20736] 20821 [.br false] = some pExit := optBeq_eq (by decide +kernel)
theorem pExitMem_get (s : MachineState) (S D A : Nat) (hD : D + 32 < 2 ^ 64) (hA : A < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    memEval s pExitMem (BitVec.ofNat 64 A) =
      if A = D + 24 then s.getReg .x15 else if A = D + 16 then s.getReg .x14 else
      if A = D + 8 then s.getMem (BitVec.ofNat 64 (S + 8)) else if A = D then s.getMem (BitVec.ofNat 64 S)
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold pExitMem
  rw [memEval_cons, memEval_cons]
  have e24 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 24⟩ = BitVec.ofNat 64 (D + 24) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 24
  have e16 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 16⟩ = BitVec.ofNat 64 (D + 16) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 16
  have v15 : (E.reg .x15).eval s = s.getReg .x15 := rfl
  have v14 : (E.reg .x14).eval s = s.getReg .x14 := rfl
  rw [e24, e16, v15, v14, cLoopMem_get s S D A (by so) hA h28 h29]
  simp only [ofNat_inj hA (show D + 24 < 2 ^ 64 by so), ofNat_inj hA (show D + 16 < 2 ^ 64 by so)]
theorem pExitObl_holds (s : MachineState) (S D : Nat) (hS : S + 16 ≤ MEMORY_BYTES) (hD : D + 32 ≤ MEMORY_BYTES)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    ∀ o ∈ pExitObl, o.holds s := by
  intro o ho
  simp only [pExitObl, List.mem_cons] at ho
  rcases ho with rfl | rfl | ho
  · unfold MEMORY_BYTES at hD
    simp only [Oblig.holds, Addr.eval, E.eval, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
  · unfold MEMORY_BYTES at hD
    simp only [Oblig.holds, Addr.eval, E.eval, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so
  · exact cLoopObl_holds s S D hS (by so) hS8 hD8 h28 h29 o ho
structure PInv (s0 : MachineState) (k : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 20821
  x28 : t.getReg .x28 = BitVec.ofNat 64 (SIG + 3248 + 16 * k)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (SIG + 3232 + 16 * k)
  x30 : t.getReg .x30 = BitVec.ofNat 64 (SIG + 5616)
  x14 : t.getReg .x14 = s0.getMem (BitVec.ofNat 64 (SIG + 3232))
  x15 : t.getReg .x15 = s0.getMem (BitVec.ofNat 64 (SIG + 3240))
  done : ∀ j < 2 * k, t.getMem (BitVec.ofNat 64 (SIG + 3232 + 8 * j)) = s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 8 * j))
  frame : Frame s0 t (fun A => SIG + 3232 ≤ A ∧ A < SIG + 3232 + 16 * k)
theorem pIter_mem {s0 t : MachineState} {k : Nat} (hk : k < 148) (h : PInv s0 k t) (r : PRes)
    (hmem : r.st.mem = cLoopMem) (A : Nat) (hA : A < 2 ^ 64) :
    (r.toState t).getMem (BitVec.ofNat 64 A) =
      if A = SIG + 3232 + 16 * k + 8 then s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 16 * k + 8))
      else if A = SIG + 3232 + 16 * k then s0.getMem (BitVec.ofNat 64 (SIG + 3248 + 16 * k))
      else t.getMem (BitVec.ofNat 64 A) := by
  rw [PRes.toState_getMem', hmem, cLoopMem_get t _ _ A (by so) hA h.x28 h.x29]
  rw [h.frame.get (by so) (by so), h.frame.get (by so) (by so)]
theorem pIter_inv {s0 t : MachineState} {k : Nat} (hk : k < 148) (h : PInv s0 k t) (u : MachineState)
    (hu : u = pBack.toState t) : PInv s0 (k + 1) u := by
  subst hu
  refine ⟨PRes.toState_pc' _ _ rfl, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun A hA hn => ?_⟩
  · rw [PRes.toState_getReg']
    show (E.bin .add (.reg .x28) (.c (BitVec.ofNat 64 16))).eval t = _
    simp only [E.eval, BinOp.eval, h.x28]; rw [ofNat_add_ofNat]; congr 1
  · rw [PRes.toState_getReg']
    show (E.bin .add (.reg .x29) (.c (BitVec.ofNat 64 16))).eval t = _
    simp only [E.eval, BinOp.eval, h.x29]; rw [ofNat_add_ofNat]; congr 1
  · rw [PRes.toState_getReg']; exact h.x30
  · rw [PRes.toState_getReg']; exact h.x14
  · rw [PRes.toState_getReg']; exact h.x15
  · rw [pIter_mem hk h pBack rfl _ (by so)]
    by_cases hj2 : j < 2 * k
    · rw [if_neg (by so), if_neg (by so)]; exact h.done j hj2
    · by_cases hje : j = 2 * k
      · subst hje; rw [if_neg (by so), if_pos (by so)]; congr 2; omega
      · have : j = 2 * k + 1 := by so
        subst this; rw [if_pos (by so)]; congr 2; omega
  · rw [pIter_mem hk h pBack rfl A hA, if_neg (by so), if_neg (by so)]
    exact h.frame.get hA (by so)
theorem pLoop {im : Image} (hl : LookOK im preCLook) {s0 u : MachineState} (h0 : PInv s0 0 u) :
    ∀ k, k ≤ 147 → ∃ t, Steps im u (7 * k) (7 * k) t ∧ PInv s0 k t := by
  intro k
  induction k with
  | zero => intro _; exact ⟨u, Steps.refl u, h0⟩
  | succ k ih =>
    intro hk
    obtain ⟨t, st, ht⟩ := ih (by so)
    obtain ⟨st1, -⟩ := run_sound hl run_pBack t ht.pc
      (cLoopObl_holds t _ _ (by so) (by so) (by so) (by so) ht.x28 ht.x29)
      (by
        intro b hb
        simp only [pBack, List.mem_singleton] at hb
        subst hb
        exact cBr_holds t _ true (by so) ht.x28 ht.x30 (by simp; omega))
    exact ⟨_, (st.trans st1).of_eq (by simp [pBack]; ring) (by simp [pBack]; ring),
      pIter_inv (by so) ht _ rfl⟩
def preCost : Nat := 1 + 9 + 148 * 7 + 4 + 5 + 214 * 7

def PrePost (s t : MachineState) : Prop :=
  t.pc=pcOf 20743 ∧
  (∀ k < 428, t.getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * k)) =
    s.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * cpIdx (k / 2) + 8 * (k % 2)))) ∧
  Frame s t (fun A => SIG + 1888 ≤ A ∧ A < SIG + 5616)

theorem pre_good {im : Image} (hlt : LookOK im preTailLook) (hlh : LookOK im preHookLook)
    (hlc : LookOK im preCLook) (s : MachineState) (hpc : s.pc=pcOf 540) :
    ∃t, Steps im s preCost preCost t ∧ PrePost s t := by
  obtain ⟨s1, -⟩ := run_sound hlh run_cHook s hpc (by intro o ho; cases ho) (by intro b hb; cases hb)
  set u1 := cHook.toState s with hu1
  have u1pc : u1.pc = pcOf 20730 := PRes.toState_pc' _ _ rfl
  obtain ⟨s2, -⟩ := run_sound hlc run_pSetup u1 u1pc (by intro o ho; cases ho) (by intro b hb; cases hb)
  set u2 := pSetup.toState u1 with hu2
  have h0 : PInv s 0 u2 := by
    refine ⟨PRes.toState_pc' _ _ rfl, ?_, ?_, ?_, ?_, ?_, fun j hj => by so, fun A _ _ => rfl⟩
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
    · rw [PRes.toState_getReg']; rfl
  obtain ⟨t, st, ht⟩ := pLoop hlc h0 147 le_rfl
  obtain ⟨s3, -⟩ := run_sound hlc run_pExit t ht.pc
    (pExitObl_holds t _ _ (by so) (by so) (by so) (by so) ht.x28 ht.x29)
    (by
      intro b hb
      simp only [pExit, List.mem_singleton] at hb
      subst hb
      exact cBr_holds t _ false (by so) ht.x28 ht.x30 (by simp))
  set u3 := pExit.toState t with hu3
  have u3pc : u3.pc = pcOf 20736 := PRes.toState_pc' _ _ rfl
  have u3get : ∀ A, A < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 A) =
      if A = SIG + 5608 then s.getMem (BitVec.ofNat 64 (SIG + 3240))
      else if A = SIG + 5600 then s.getMem (BitVec.ofNat 64 (SIG + 3232))
      else if A = SIG + 5592 then s.getMem (BitVec.ofNat 64 (SIG + 5608))
      else if A = SIG + 5584 then s.getMem (BitVec.ofNat 64 (SIG + 5600))
      else t.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hu3, PRes.toState_getMem']
    show memEval t pExitMem (BitVec.ofNat 64 A) = _
    rw [pExitMem_get t (SIG + 3248 + 16 * 147) (SIG + 3232 + 16 * 147) A (by so) hA ht.x28 ht.x29, ht.x15, ht.x14,
      ht.frame.get (A := SIG + 3248 + 16 * 147 + 8) (by so) (by so),
      ht.frame.get (A := SIG + 3248 + 16 * 147) (by so) (by so)]
    try rfl
  have u3frame : Frame s u3 (fun A => SIG + 3232 ≤ A ∧ A < SIG + 5616) := fun A hA hn => by
    rw [u3get A hA, if_neg (by so), if_neg (by so), if_neg (by so), if_neg (by so)]
    exact ht.frame.get hA (by so)
  have u3mem : ∀ k < 428, u3.getMem (BitVec.ofNat 64 (SIG + 2192 + 8 * k)) =
      s.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * cpIdx (k / 2) + 8 * (k % 2))) := by
    intro k hk
    rw [u3get _ (by so)]
    unfold cpIdx
    by_cases k1 : k = 427
    · subst k1; rw [if_pos (by so)]; rfl
    by_cases k2 : k = 426
    · subst k2; rw [if_neg (by so), if_pos (by so)]; rfl
    by_cases k3 : k = 425
    · subst k3; rw [if_neg (by so), if_neg (by so), if_pos (by so)]; rfl
    by_cases k4 : k = 424
    · subst k4; rw [if_neg (by so), if_neg (by so), if_neg (by so), if_pos (by so)]; rfl
    rw [if_neg (by so), if_neg (by so), if_neg (by so), if_neg (by so)]
    by_cases hlo : k < 130
    · rw [ht.frame.get (by so) (by so), if_pos (show k / 2 < 65 by omega)]
      congr 2; omega
    · have hd := ht.done (k - 130) (by omega)
      rw [show SIG + 3232 + 8 * (k - 130) = SIG + 2192 + 8 * k by so] at hd
      rw [hd, if_neg (show ¬ k / 2 < 65 by omega), if_pos (show k / 2 < 213 by omega)]
      rw [show SIG + 3248 + 8 * (k - 130) = SIG + 2192 + 16 * (k / 2 + 1) + 8 * (k % 2) by so]
  have h0' : CInv u3 0 u3 := by
    refine ⟨u3pc, ?_, ?_, ?_, fun j hj => by so, Frame.refl _ _⟩
    · rw [hu3, PRes.toState_getReg']; rfl
    · rw [hu3, PRes.toState_getReg']; rfl
    · rw [hu3, PRes.toState_getReg']; rfl
  obtain ⟨t', st', ht'⟩ := cLoop hlt h0' 213 le_rfl
  obtain ⟨s4, -⟩ := run_sound hlt run_cExit t' ht'.pc
    (cLoopObl_holds t' _ _ (by so) (by so) (by so)
      (by so) ht'.x28 ht'.x29)
    (by
      intro b hb
      simp only [cExit, List.mem_singleton] at hb
      subst hb
      exact cBr_holds t' _ false (by so) ht'.x28 ht'.x30 (by simp))
  have hfin : ∀ k < 428, (cExit.toState t').getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * k)) =
      u3.getMem (BitVec.ofNat 64 (SIG + 2192 + 8 * k)) := by
    intro k hk
    rw [cIter_mem (by so) ht' cExit rfl _ (by so)]
    by_cases hk2 : k < 2 * 213
    · rw [if_neg (by so), if_neg (by so)]; exact ht'.done k hk2
    · by_cases hke : k = 2 * 213
      · subst hke; rw [if_neg (by so), if_pos (by so)]
      · have : k = 2 * 213 + 1 := by so
        subst this; rw [if_pos (by so)]
  refine ⟨cExit.toState t', ((s1.trans s2).trans ((st.trans s3).trans (st'.trans s4))).of_eq
    (by simp [cHook, pSetup, pExit, cExit, preCost]) (by simp [cHook, pSetup, pExit, cExit, preCost]),
    PRes.toState_pc' _ _ rfl, fun k hk => (hfin k hk).trans (u3mem k hk), fun A hA hn => ?_⟩
  rw [cIter_mem (by so) ht' cExit rfl A hA, if_neg (by so), if_neg (by so),
      ht'.frame.get hA (by so), u3frame.get hA (by so)]

#print axioms pre_good
end ClaudeWCT.W9.Machine.Sign.SharedSerializer

namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def tailWords : List (BitVec 32) := bv_list% 32 [0xd00313,0x2690863,0x2700313,0x2690463,0x4100313,0x2690063,0x5b00313,0x690c63,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x10e8e93,0x10e0e13,0x190913,0x14b00313,0xfc6960e3]
def tailLook (n : Nat) : Option (BitVec 32) := if 22509≤n then tailWords[n-22509]? else none

def iterDirs (kind : Fin 5) (back : Bool) : List Dir :=
  List.replicate kind.val (.br false) ++ (if kind.val<4 then [.br true] else []) ++ [.br back]
def iterRegs (kind : Fin 5) : RegFile :=
  regsOf ([ (.x6,cE 331), (.x18,x18p1), (.x28,.bin .add (.reg .x28) (cE 16)) ] ++
    if kind.val=4 then [(.x7,.ld (.bin .add (.reg .x28) (cE 8))),(.x29,.bin .add (.reg .x29) (cE 16))] else [])
def iterMem : SymMem :=
  [(⟨some (.reg .x29),BitVec.ofNat 64 8⟩,.ld (.bin .add (.reg .x28) (cE 8))),
   (⟨some (.reg .x29),BitVec.ofNat 64 0⟩,.ld (.reg .x28))]
def iterObl : List Oblig :=
  [.valid ⟨some (.reg .x29),BitVec.ofNat 64 8⟩ 8,.valid ⟨some (.reg .x29),BitVec.ofNat 64 0⟩ 8,
   .valid ⟨some (.reg .x28),BitVec.ofNat 64 8⟩ 8,.valid ⟨some (.reg .x28),BitVec.ofNat 64 0⟩ 8]
def iterBranches (kind : Fin 5) (back : Bool) : List Br :=
  ⟨.ltu,x18p1,cE 331,back⟩ ::
  ((List.range (if kind.val<4 then kind.val+1 else 4)).map fun k=>
    (⟨.eq,.reg .x18,cE (13+26*k),decide (k=kind.val)⟩ : Br)).reverse

def iterCost (kind : Fin 5) : Nat := if kind.val=4 then 17 else 6+2*kind.val

def iterResult (kind : Fin 5) (back : Bool) : PRes :=
  ⟨⟨iterRegs kind,if kind.val=4 then iterMem else [],if kind.val=4 then iterObl else []⟩,
    pcOf (if back then 22509 else 22526),false,iterCost kind,iterCost kind,iterBranches kind back,none⟩

theorem run_iter (kind : Fin 5) (back : Bool) :
    run tailLook [22509,22526] 22509 (iterDirs kind back)=some (iterResult kind back) := by
  fin_cases kind <;> cases back <;> exact optBeq_eq (by decide +kernel)

#print axioms run_iter
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))
theorem iterMem_get (s : MachineState) (S D A : Nat) (hD : D + 16 < 2 ^ 64)
    (hA : A < 2 ^ 64) (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    memEval s iterMem (BitVec.ofNat 64 A) =
      if A = D + 8 then s.getMem (BitVec.ofNat 64 (S + 8)) else if A = D then s.getMem (BitVec.ofNat 64 S)
      else s.getMem (BitVec.ofNat 64 A) := by
  unfold iterMem cE
  rw [memEval_cons, memEval_cons, memEval_nil]
  have e1 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 8⟩ = BitVec.ofNat 64 (D + 8) := by
    simp only [Addr.eval, E.eval, h29]; exact ofNat_add_ofNat D 8
  have e0 : Addr.eval s ⟨some (.reg .x29), BitVec.ofNat 64 0⟩ = BitVec.ofNat 64 D := by
    simp only [Addr.eval, E.eval, h29, ofNat_add_ofNat, Nat.add_zero]
  have v1 : (E.ld (.bin .add (.reg .x28) (.c (BitVec.ofNat 64 8)))).eval s = s.getMem (BitVec.ofNat 64 (S + 8)) := by
    simp only [E.eval, BinOp.eval, h28]; rw [ofNat_add_ofNat S 8]
  have v0 : (E.ld (.reg .x28)).eval s = s.getMem (BitVec.ofNat 64 S) := by
    simp only [E.eval, h28]
  rw [e1, e0, v1, v0]
  simp only [ofNat_inj hA (show D + 8 < 2 ^ 64 by so), ofNat_inj hA (show D < 2 ^ 64 by so)]
theorem iterObl_holds (s : MachineState) (S D : Nat) (hS : S + 16 ≤ MEMORY_BYTES) (hD : D + 16 ≤ MEMORY_BYTES)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D) :
    ∀ o ∈ iterObl, o.holds s := by
  unfold MEMORY_BYTES at hS hD
  intro o ho
  simp only [iterObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;>
    simp only [Oblig.holds, Addr.eval, E.eval, h28, h29, accessValid_iff, MEMORY_BYTES, BitVec.toNat_add,
      BitVec.toNat_ofNat] <;> so

def validKind (kind : Fin 5) (j : Nat) : Prop :=
  if kind.val=4 then ∀k,k<4 → j≠13+26*k else j=13+26*kind.val

theorem iterBranches_holds (kind : Fin 5) (j : Nat) (hj : j<331) (hk : validKind kind j)
    (s : MachineState) (h18 : s.getReg .x18=BitVec.ofNat 64 j) (back : Bool)
    (hb : decide (j+1<331)=back) :
    ∀b∈iterBranches kind back,b.holds s := by
  have hj64 : j<2^64 := by omega
  have hj164 : j+1<2^64 := by omega
  intro b hmem
  simp only [iterBranches,List.mem_cons,List.mem_reverse,List.mem_map,List.mem_range] at hmem
  rcases hmem with rfl | ⟨k,hkb,rfl⟩
  · simpa [Br.holds,CmpOp.eval,E.eval,BinOp.eval,cE,x18p1,h18,ofNat_add_ofNat,
      BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show j+1<18446744073709551616 by omega)] using hb
  · have hk4 : k<4 := by split_ifs at hkb <;> omega
    have he : (j=13+26*k) ↔ k=kind.val := by
      unfold validKind at hk
      by_cases hc : kind.val=4
      · have hn := (show ∀k,k<4 → j≠13+26*k by simpa [hc] using hk) k hk4
        omega
      · have hjk : j=13+26*kind.val := by simpa [hc] using hk
        omega
    simp only [Br.holds,CmpOp.eval,E.eval,cE,h18]
    change (BitVec.ofNat 64 j == BitVec.ofNat 64 (13+26*k))=decide (k=kind.val)
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq,decide_eq_true_eq,ofNat_inj hj64 (show 13+26*k<2^64 by omega)] using he

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem iter_steps {im : Image} (hc : LookOK im tailLook)
    (kind : Fin 5) (j d : Nat) (hj : j<331) (hd : d≤j) (hk : validKind kind j)
    (s : MachineState) (hp : s.pc=pcOf 22509)
    (h18 : s.getReg .x18=BitVec.ofNat 64 j)
    (h28 : s.getReg .x28=BitVec.ofNat 64 (SIG+16*j))
    (h29 : s.getReg .x29=BitVec.ofNat 64 (SIG+16*d)) :
    ∃t, Steps im s (iterCost kind) (iterCost kind) t ∧
      t.pc=pcOf (if j+1<331 then 22509 else 22526) ∧
      t.getReg .x18=BitVec.ofNat 64 (j+1) ∧
      t.getReg .x28=BitVec.ofNat 64 (SIG+16*(j+1)) ∧
      t.getReg .x29=BitVec.ofNat 64 (SIG+16*(d+if kind.val=4 then 1 else 0)) ∧
      (∀A,A<2^64 → t.getMem (BitVec.ofNat 64 A)=
        if kind.val=4 then
          if A=SIG+16*d+8 then s.getMem (BitVec.ofNat 64 (SIG+16*j+8))
          else if A=SIG+16*d then s.getMem (BitVec.ofNat 64 (SIG+16*j))
          else s.getMem (BitVec.ofNat 64 A)
        else s.getMem (BitVec.ofNat 64 A)) ∧
      RegsExcept s t [.x6,.x7,.x18,.x28,.x29] := by
  have ho : ∀o∈(iterResult kind (decide (j+1<331))).st.obl,o.holds s := by
    change ∀o∈(if kind.val=4 then iterObl else []),o.holds s
    split_ifs
    · exact iterObl_holds s (SIG+16*j) (SIG+16*d) (by simp [SIG,MEMORY_BYTES];omega)
        (by simp [SIG,MEMORY_BYTES];omega) (by simp [SIG];omega) (by simp [SIG];omega) h28 h29
    · simp
  have hs := (run_sound hc (run_iter kind (decide (j+1<331))) s hp ho
    (iterBranches_holds kind j hj hk s h18 _ rfl)).1
  refine ⟨_,hs,?_,?_,?_,?_,?_,?_⟩
  · simp [PRes.toState_pc',iterResult]
  · rw [PRes.toState_getReg']
    fin_cases kind <;> simp [iterResult,iterRegs,regsOf,RegFile.set,RegFile.init,rv_simp,cE,x18p1,h18,ofNat_add_ofNat]
  · rw [PRes.toState_getReg']
    fin_cases kind <;> simp [iterResult,iterRegs,regsOf,RegFile.set,RegFile.init,rv_simp,cE,h28,ofNat_add_ofNat] <;>
      congr 1 <;> omega
  · rw [PRes.toState_getReg']
    fin_cases kind <;> simp [iterResult,iterRegs,regsOf,RegFile.set,RegFile.init,rv_simp,cE,h29,ofNat_add_ofNat] <;>
      congr 1 <;> omega
  · intro A hA
    rw [PRes.toState_getMem']
    change memEval s (if kind.val=4 then iterMem else []) _ = _
    by_cases hk : kind.val=4
    · rw [if_pos hk,if_pos hk]
      exact iterMem_get s (SIG+16*j) (SIG+16*d) A (by simp [SIG];omega) hA h28 h29
    · rw [if_neg hk,if_neg hk]; rfl
  · intro r hr
    rw [PRes.toState_getReg']
    fin_cases kind <;> cases r <;> simp_all [iterResult,iterRegs,regsOf,RegFile.set,RegFile.init,rv_simp,cE] <;> rfl

end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))

def kept (n : Nat) : Nat :=
  if n≤13 then n else if n≤39 then n-1 else if n≤65 then n-2 else if n≤91 then n-3 else n-4
def sourceIndex (n : Nat) : Nat :=
  if n<13 then n else if n<38 then n+1 else if n<63 then n+2 else if n<88 then n+3 else n+4

def kind (n : Nat) : Fin 5 :=
  if n=13 then 0 else if n=39 then 1 else if n=65 then 2 else if n=91 then 3 else 4

theorem kind_valid (n : Nat) : validKind (kind n) n := by
  unfold kind validKind
  split_ifs <;> simp_all
  intro k hk
  omega

theorem kept_le (n : Nat) : kept n≤n := by unfold kept;split_ifs <;> omega

theorem kept_succ (k : Fin 5) (n : Nat) (h : validKind k n) :
    kept (n+1)=kept n+(if k.val=4 then 1 else 0) := by
  unfold validKind at h
  by_cases hk : k.val=4
  · rw [if_pos hk] at h ⊢
    have h0:=h 0 (by decide);have h1:=h 1 (by decide)
    have h2:=h 2 (by decide);have h3:=h 3 (by decide)
    unfold kept
    split_ifs <;> omega
  · rw [if_neg hk] at h ⊢
    have := k.isLt
    unfold kept
    split_ifs <;> omega

theorem source_kept (n : Nat) (h : validKind 4 n) : sourceIndex (kept n)=n := by
  simp only [validKind,Fin.reduceFinMk,ite_true] at h
  have h0:=h 0 (by decide);have h1:=h 1 (by decide)
  have h2:=h 2 (by decide);have h3:=h 3 (by decide)
  unfold sourceIndex kept
  split_ifs <;> omega

structure TailInv (s : MachineState) (j : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (if j<331 then 22509 else 22526)
  x18 : t.getReg .x18=BitVec.ofNat 64 j
  x28 : t.getReg .x28=BitVec.ofNat 64 (SIG+16*j)
  x29 : t.getReg .x29=BitVec.ofNat 64 (SIG+16*kept j)
  done : ∀k,k<2*kept j → t.getMem (BitVec.ofNat 64 (SIG+8*k))=
    s.getMem (BitVec.ofNat 64 (SIG+16*sourceIndex (k/2)+8*(k%2)))
  frame : Frame s t (fun A=>SIG≤A ∧ A<SIG+16*kept j)

theorem tail_iter {im : Image} (hc : LookOK im tailLook) {s t : MachineState} {j : Nat}
    (hj : j<331) (h : TailInv s j t) :
    ∃u, Steps im t (iterCost (kind j)) (iterCost (kind j)) u ∧ TailInv s (j+1) u := by
  have hk := kind_valid j
  have hd := kept_le j
  obtain ⟨u,st,pc,x18,x28,x29,mem,regs⟩:=iter_steps hc (kind j) j (kept j) hj hd hk t
    (by simpa [hj] using h.pc) h.x18 h.x28 h.x29
  have ksucc := kept_succ (kind j) j hk
  have mm (A : Nat) (hA : A<2^64) : u.getMem (BitVec.ofNat 64 A)=
      if (kind j).val=4 then
        if A=SIG+16*kept j+8 then s.getMem (BitVec.ofNat 64 (SIG+16*j+8))
        else if A=SIG+16*kept j then s.getMem (BitVec.ofNat 64 (SIG+16*j))
        else t.getMem (BitVec.ofNat 64 A)
      else t.getMem (BitVec.ofNat 64 A) := by
    rw [mem A hA,h.frame.get (by so) (by so),h.frame.get (by so) (by so)]
  refine ⟨u,st,pc,x18,x28,?_,?_,?_⟩
  · simpa only [ksucc] using x29
  · intro k hkbound
    rw [mm _ (by have:=kept_le (j+1);so)]
    by_cases hc : (kind j).val=4
    · rw [if_pos hc]
      have hkg : kind j=4 := Fin.ext hc
      have hsource := source_kept j (hkg ▸ hk)
      rw [hc,if_pos rfl] at ksucc
      by_cases hprior : k<2*kept j
      · rw [if_neg (by so),if_neg (by so)]
        exact h.done k hprior
      · have he : k=2*kept j ∨ k=2*kept j+1 := by omega
        rcases he with rfl | rfl
        · rw [if_neg (by so),if_pos (by so)]
          simp only [Nat.mul_div_cancel_left _ (by decide : 0<2),Nat.mul_mod_right,Nat.mul_zero,Nat.add_zero,hsource]
        · rw [if_pos (by so)]
          have hdv : (2*kept j+1)/2=kept j := by omega
          have hmd : (2*kept j+1)%2=1 := by omega
          rw [hdv,hmd,hsource]
    · rw [if_neg hc]
      exact h.done k (by rw [ksucc,if_neg hc] at hkbound;omega)
  · intro A hA hn
    rw [mm A hA]
    by_cases hc : (kind j).val=4
    · rw [if_pos hc,if_neg (by rw [ksucc,if_pos hc] at hn;so),
        if_neg (by rw [ksucc,if_pos hc] at hn;so)]
      exact h.frame.get hA (by rw [ksucc,if_pos hc] at hn;so)
    · rw [if_neg hc]
      exact h.frame.get hA (by rw [ksucc,if_neg hc] at hn;simpa using hn)

theorem tail_loop {im : Image} (hc : LookOK im tailLook) {s u : MachineState}
    (h0 : TailInv s 0 u) : ∀j,j≤331 → ∃n≤17*j,∃t,Steps im u n n t ∧ TailInv s j t := by
  intro j
  induction j with
  | zero => intro _;exact ⟨0,by omega,u,Steps.refl u,h0⟩
  | succ j ih =>
    intro hj
    obtain ⟨n,hn,t,st,ht⟩:=ih (by omega)
    obtain ⟨v,sv,hv⟩:=tail_iter hc (by omega) ht
    refine ⟨n+iterCost (kind j),?_,v,st.trans sv,hv⟩
    have := (kind j).isLt
    unfold iterCost
    split_ifs <;> omega

#print axioms tail_loop
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def setupWords : List (BitVec 32) := bv_list% 32 [0x7e37,0xe0e13,0x7eb7,0xe8e93,0x913]
def finishWords : List (BitVec 32) := bv_list% 32 [0xe3303,0x8e3383,0x1039393,0x103d393,0x66f37,0xf0f13,0xf3f03,0x30f1f13,0x1e3e3b3,0x6eb023,0x7eb423,0x100293,0xbf8fe06f]

sym_block setupRun := symRun {noAlias:=true} setupWords (pcOf 22504) 20
sym_block finishRun := symRun {noAlias:=true} finishWords (pcOf 22526) 20

theorem setup_steps {im : Image} (hc : CodeAt im (pcOf 22504) setupWords)
    (s : MachineState) (hp : s.pc=pcOf 22504) :
    ∃t, Steps im s 5 5 t ∧ TailInv s 0 t := by
  refine ⟨_,symRun_sound setupRun hc s hp ?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setupRun.res,rv_simp]
  · rfl
  · simp [setupRun.res,rv_simp]
  · simp [setupRun.res,rv_simp,SIG]
  · simp [setupRun.res,rv_simp,SIG,kept]
  · simp [kept]
  · intro A hA hn;rfl

theorem finish_steps {im : Image} (hc : CodeAt im (pcOf 22526) finishWords)
    (s : MachineState) (hp : s.pc=pcOf 22526)
    (h28 : s.getReg .x28=BitVec.ofNat 64 (SIG+16*331))
    (h29 : s.getReg .x29=BitVec.ofNat 64 (SIG+16*327)) :
    ∃t, Steps im s 13 13 t ∧ t.pc=pcOf 20744 ∧ t.getReg .x5=1 ∧
      t.getMem (BitVec.ofNat 64 (SIG+16*327))=s.getMem (BitVec.ofNat 64 (SIG+16*331)) ∧
      t.getMem (BitVec.ofNat 64 (SIG+16*327+8))=
        ((s.getMem (BitVec.ofNat 64 (SIG+16*331+8))<<<16)>>>16) ||| (s.getMem 0x66000<<<48) ∧
      Frame s t (fun A=>A=SIG+16*327 ∨ A=SIG+16*327+8) := by
  refine ⟨_,symRun_sound finishRun hc s hp ?_,?_,?_,?_,?_,?_⟩
  · simp [finishRun.res,rv_simp,h28,h29,SIG,accessValid_iff,MEMORY_BYTES]
  · rfl
  · simp [finishRun.res,rv_simp]
  · simp [finishRun.res,rv_simp,h28,h29,SIG]
  · simp [finishRun.res,rv_simp,h28,h29,SIG]
  · intro A hA hn
    have h0 : A≠SIG+16*327 := by tauto
    have h8 : A≠SIG+16*327+8 := by tauto
    simp [finishRun.res,rv_simp,h28,h29,SIG,ofNat_inj hA (by decide : 33904<2^64),
      ofNat_inj hA (by decide : 33912<2^64)]
    simp_all [SIG]

#print axioms finish_steps
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))

def packedWord (read : Nat→Word) (hints : Word) (k : Nat) : Word :=
  if k<654 then read (2*sourceIndex (k/2)+k%2)
  else if k=654 then read 662
  else ((read 663<<<16)>>>16) ||| (hints<<<48)

theorem tail_readout {im : Image} (hs : CodeAt im (pcOf 22504) setupWords)
    (hl : LookOK im tailLook) (hf : CodeAt im (pcOf 22526) finishWords)
    (s : MachineState) (hp : s.pc=pcOf 22504) :
    ∃n≤5645,∃t,Steps im s n n t ∧ t.pc=pcOf 20744 ∧ t.getReg .x5=1 ∧
      (∀k,k<656 → t.getMem (BitVec.ofNat 64 (SIG+8*k))=
        packedWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j))) (s.getMem 0x66000) k) ∧
      Frame s t (fun A=>SIG≤A ∧ A<SIG+5248) := by
  obtain ⟨u,su,hu⟩:=setup_steps hs s hp
  obtain ⟨n,hn,v,sv,hv⟩:=tail_loop hl hu 331 (by omega)
  obtain ⟨t,st,pc,x5,lo,hi,frame⟩:=finish_steps hf v
    (by simpa using hv.pc) hv.x28 (by simpa [kept] using hv.x29)
  have hframe : Frame s v (fun A=>SIG≤A ∧ A<SIG+5232) := by simpa [kept] using hv.frame
  have low : t.getMem (BitVec.ofNat 64 (SIG+8*654))=s.getMem (BitVec.ofNat 64 (SIG+8*662)) :=
    lo.trans (hframe.get (by decide) (by simp [SIG] <;> omega))
  have high : t.getMem (BitVec.ofNat 64 (SIG+8*655))=
      ((s.getMem (BitVec.ofNat 64 (SIG+8*663))<<<16)>>>16) ||| (s.getMem 0x66000<<<48) := by
    rw [hi,hframe.get (by decide) (by simp [SIG] <;> omega)]
    have hh : v.getMem (0x66000 : Word)=s.getMem (0x66000 : Word) :=
      hframe.get (A:=0x66000) (by decide) (by simp [SIG])
    rw [hh]
  refine ⟨5+n+13,by omega,t,(su.trans sv).trans st,pc,x5,?_,?_⟩
  · intro k hk
    unfold packedWord
    by_cases hk654 : k<654
    · rw [if_pos hk654,frame.get (by so) (by so)]
      have hdone:=hv.done k (by simpa [kept] using hk654)
      rw [hdone]
      congr 2
      omega
    · rw [if_neg hk654]
      by_cases he : k=654
      · subst k;rw [if_pos rfl];exact low
      · have he' : k=655 := by omega
        subst k;rw [if_neg (by omega)];exact high
  · exact (hframe.trans frame).mono (fun A _ h=>by
      rcases h with h|h
      · omega
      · rcases h with h|h <;> so)

#print axioms tail_readout
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem codeAt_get_word {im : Image} {b : Nat} {code : List (BitVec 32)}
    (hb : b<2^30) (hc : CodeAt im (pcOf b) code) {i : Nat} {w : BitVec 32}
    (hi : code[i]?=some w) : im.code[b+i]?=some w := by
  have hpc : (pcOf b).toNat=4096+4*b := by
    simp only [pcOf,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨rest,hrest⟩ := hc.2.2.2
  rw [hpc,show (4096+4*b-4096)/4=b by omega] at hrest
  have hlen:= (List.getElem?_eq_some_iff.mp hi).1
  have hh : (code++rest)[i]?=some w := by rwa [List.getElem?_append_left hlen]
  rw [hrest,List.getElem?_drop] at hh
  simpa [Nat.add_comm] using hh

structure Code (im : Image) : Prop where
  preHook : CodeAt im (pcOf 540) [hook540]
  preTail : CodeAt im (pcOf 20715) (tailCode.take 28)
  preH2 : CodeAt im (pcOf 20813) h2SignTail
  jump : CodeAt im (pcOf 20743) [0x3850106f]
  setup : CodeAt im (pcOf 22504) setupWords
  loop : CodeAt im (pcOf 22509) tailWords
  finish : CodeAt im (pcOf 22526) finishWords
  halt : CodeAt im (pcOf 20744) [0x513,0x73]

theorem Code.pre_tail_look {im : Image} (h : Code im) : LookOK im preTailLook := by
  intro n w hw
  unfold preTailLook at hw
  split at hw
  · rename_i hn
    unfold Sign.tailLook at hw
    split at hw
    · rename_i hlo
      have he : (tailCode.take 28)[n-20715]?=some w := by
        rw [List.getElem?_take,if_pos (by omega)];exact hw
      have hh:=codeAt_get_word (by decide : 20715<2^30) h.preTail he
      simpa only [Nat.add_sub_cancel' hlo] using hh
    · cases hw
  · cases hw

theorem Code.pre_hook_look {im : Image} (h : Code im) : LookOK im preHookLook := by
  intro n w hw
  unfold preHookLook at hw
  split at hw
  · rename_i hn
    subst n
    have he : w=hook540 := by simpa [hookLook] using hw.symm
    subst w
    simpa using codeAt_get_word (by decide : 540<2^30) h.preHook (i:=0) (by rfl)
  · cases hw

theorem Code.pre_c_look {im : Image} (h : Code im) : LookOK im preCLook := by
  intro n w hw
  unfold preCLook at hw
  split at hw
  · rename_i hn
    unfold cLook at hw
    split at hw
    · rename_i w' hh
      cases hw
      have hb : n<20743 := by
        unfold Sign.tailLook at hh
        split at hh
        · have hlen := (List.getElem?_eq_some_iff.mp hh).1
          rw [tailCode_length] at hlen
          omega
        · cases hh
      exact h.pre_tail_look n _ (by simpa [preTailLook,hb] using hh)
    · unfold h2Look at hw
      split at hw
      · rename_i hlo
        have hh:=codeAt_get_word (by decide : 20813<2^30) h.preH2 hw
        simpa only [Nat.add_sub_cancel' hlo] using hh
      · cases hw
  · cases hw

theorem Code.tail_look {im : Image} (h : Code im) : LookOK im tailLook := by
  intro n w hw
  unfold tailLook at hw
  split at hw
  · rename_i hn
    have hh:=codeAt_get_word (by decide : 22509<2^30) h.loop hw
    simpa only [Nat.add_sub_cancel' hn] using hh
  · cases hw

theorem installed_code : Code Images.signImage := by
  constructor <;> apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;> decide +kernel

#print axioms installed_code
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
local macro "so" : tactic => `(tactic| ((try simp only [SIG, MEMORY_BYTES] at *) <;> omega))

def preWord (read : Nat→Word) (k : Nat) : Word :=
  if k<236 then read k else read (274+2*cpIdx ((k-236)/2)+(k-236)%2)

theorem PrePost.read {s t : MachineState} (h : PrePost s t) (k : Nat) (hk : k<664) :
    t.getMem (BitVec.ofNat 64 (SIG+8*k))=preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j))) k := by
  unfold preWord
  split
  · exact h.2.2.get (by so) (by so)
  · rename_i he
    have hm:=h.2.1 (k-236) (by omega)
    rw [show SIG+1888+8*(k-236)=SIG+8*k by omega,
      show SIG+2192+16*cpIdx ((k-236)/2)+8*((k-236)%2)=SIG+8*(274+2*cpIdx ((k-236)/2)+(k-236)%2) by omega] at hm
    exact hm

sym_block jumpRun := symRun { noAlias := true } (bv_list% 32 [0x3850106f]) (pcOf 20743) 100
sym_block haltRun := symRun { noAlias := true } (bv_list% 32 [0x513]) (pcOf 20744) 100

theorem full_readout {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 540) :
    ∃n≤8200,∃t,Steps im s n n t ∧ t.pc=pcOf 20745 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      (∀k,k<656 → t.getMem (BitVec.ofNat 64 (SIG+8*k))=
        packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j)))) (s.getMem 0x66000) k) := by
  obtain ⟨a,sa,ha⟩:=pre_good hc.pre_tail_look hc.pre_hook_look hc.pre_c_look s hp
  let b:=jumpRun.res.toState a
  have ab : Steps im a 1 1 b := symRun_sound jumpRun hc.jump a ha.1 (by simp [jumpRun.res,rv_simp])
  have bp : b.pc=pcOf 22504 := by simp [b,jumpRun.res,rv_simp]
  have bm (A : Word) : b.getMem A=a.getMem A := rfl
  obtain ⟨n,hn,u,bu,up,ux5,uw,uf⟩:=tail_readout hc.setup hc.tail_look hc.finish b bp
  have hc1 : CodeAt im (pcOf 20744) [0x513] := by
    rcases hc.halt with ⟨h1,h2,h3,rest,hrest⟩
    refine ⟨h1,h2,by simp_all,0x73::rest,?_⟩
    exact hrest
  let t:=haltRun.res.toState u
  have ut : Steps im u 1 1 t := symRun_sound haltRun hc1 u up (by simp [haltRun.res,rv_simp])
  refine ⟨preCost+1+n+1,by unfold preCost;omega,t,((sa.trans ab).trans bu).trans ut,?_,?_,?_,?_⟩
  · simp [t,haltRun.res,rv_simp]
  · simpa [t,haltRun.res,rv_simp] using ux5
  · simp [t,haltRun.res,rv_simp]
  · intro k hk
    change u.getMem _=_
    rw [uw k hk]
    have hh : b.getMem (0x66000 : Word)=s.getMem (0x66000 : Word) :=
      (bm _).trans (ha.2.2.get (A:=0x66000) (by decide) (by simp [SIG]))
    rw [hh]
    unfold packedWord
    split
    · rename_i hk654
      have hb : 2*sourceIndex (k/2)+k%2<664 := by unfold sourceIndex;split_ifs <;>omega
      exact (bm _).trans (ha.read _ hb)
    · split
      · exact (bm _).trans (ha.read _ (by omega))
      · dsimp only
        rw [bm,ha.read 663 (by omega)]

#print axioms full_readout
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def rawIndex (k : Nat) : Nat :=
  if k<13 then k else if k<38 then k+1 else if k<63 then k+2 else if k<88 then k+3
  else if k<114 then k+4 else k+23

def fullIndex (k : Nat) : Nat := if k<179 then k else k+1

def wordIndex (k : Nat) : Nat :=
  if k<236 then k else 274+2*cpIdx ((k-236)/2)+(k-236)%2

theorem preWord_eq (read : Nat→Word) (k : Nat) : preWord read k=read (wordIndex k) := by
  unfold preWord wordIndex
  split <;>rfl

theorem indices (k i : Nat) (hk : k<327) (hi : i<2) :
    wordIndex (2*sourceIndex k+i)=2*rawIndex (fullIndex k)+i := by
  unfold wordIndex sourceIndex rawIndex fullIndex cpIdx
  split_ifs <;>omega

def RawAt (s : MachineState) (sig : SharedSignature) : Prop :=
  ∀k,k<328 → DigAt s (SIG+16*rawIndex k) ((sigDigests sig).getD k 0)

theorem RawAt.word {s : MachineState} {sig : SharedSignature} (h : RawAt s sig)
    (k i : Nat) (hk : k<328) (hi : i<2) :
    s.getMem (BitVec.ofNat 64 (SIG+8*(2*rawIndex k+i)))=
      ((sigDigests sig).getD k 0).extractLsb' (64*i) 64 := by
  have hd:=h k hk
  have he : i=0 ∨ i=1 := by omega
  rcases he with rfl|rfl
  · simpa [←Nat.mul_assoc] using hd.1
  · simpa [Nat.mul_add,Nat.add_assoc,←Nat.mul_assoc] using hd.2

def sigWord (sig : SharedSignature) (k : Nat) : Word :=
  if k<654 then ((sigDigests sig).getD (fullIndex (k/2)) 0).extractLsb' (64*(k%2)) 64
  else if k=654 then ((sigDigests sig).getD 179 0).extractLsb' 0 64
  else ((((sigDigests sig).getD 179 0).extractLsb' 64 64<<<16)>>>16) ||| (sig.policyHints.setWidth 64<<<48)

theorem packedWord_raw {s : MachineState} {sig : SharedSignature} (h : RawAt s sig)
    (hh : s.getMem 0x66000<<<48=sig.policyHints.setWidth 64<<<48) (k : Nat) (hk : k<656) :
    packedWord (preWord (fun j=>s.getMem (BitVec.ofNat 64 (SIG+8*j)))) (s.getMem 0x66000) k=sigWord sig k := by
  unfold packedWord sigWord
  split
  · rename_i hk654
    rw [preWord_eq,indices _ _ (by omega) (by omega)]
    exact h.word _ _ (by unfold fullIndex;split_ifs <;>omega) (by omega)
  · split
    · rw [preWord_eq]
      exact h.word 179 0 (by omega) (by omega)
    · rw [preWord_eq,hh]
      have hm:=h.word 179 1 (by omega) (by omega)
      change s.getMem (BitVec.ofNat 64 (SIG+8*405))=_ at hm
      rw [show wordIndex 663=405 by decide,hm]

 theorem sigBC_word (sig : SharedSignature) (k : Nat) (hk : k<654) :
    (sigBC sig).extractLsb' (64*k) 64=sigWord sig k := by
  unfold sigWord
  rw [if_pos hk]
  have h:=congrArg (fun d : Digest=>d.extractLsb' (64*(k%2)) 64) (cDig_sigBC sig (k/2) (by omega))
  rw [cDig,extract_digest_word _ _ _ (by omega),ClaudeWCT.W9.T3M.getD_eraseIdx] at h
  rw [show 128*(k/2)+64*(k%2)=64*k by omega] at h
  by_cases hq : k/2<179 <;>simpa [fullIndex,hq] using h

#print axioms packedWord_raw
#print axioms sigBC_word
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 50000

theorem setTop_zero (d : Digest) : ClaudeWCT.WCT9.setTop d 0=(d.extractLsb' 0 112).setWidth 128 := by
  apply BitVec.eq_of_toNat_eq
  simp [ClaudeWCT.WCT9.setTop,BitVec.toNat_setWidth,BitVec.extractLsb'_toNat]

theorem setTop_low (d : Digest) : (ClaudeWCT.WCT9.setTop d 0).extractLsb' 0 64=d.extractLsb' 0 64 := by
  rw [setTop_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hj,show j<128 by omega,show j<112 by omega]

theorem setTop_high (d : Digest) : (ClaudeWCT.WCT9.setTop d 0).extractLsb' 64 64=(d.extractLsb' 64 64<<<16)>>>16 := by
  rw [setTop_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft]
  by_cases h48 : j<48
  · simp [hj,show 64+j<128 by omega,show 64+j<112 by omega,show 16+j<64 by omega,show ¬16+j<16 by omega]
  · simp [hj,show 64+j<128 by omega,show ¬64+j<112 by omega,show ¬16+j<64 by omega]

theorem high_word_hints (b : CBytes) : b.extractLsb' (64*655) 64=
    ((b.extractLsb' (64*655) 64<<<16)>>>16) ||| ((b.extractLsb' (8*5246) 16).setWidth 64<<<48) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_or]
  by_cases h48 : j<48
  · simp [hj,h48,show 16+j<64 by omega,show ¬16+j<16 by omega]
  · simp [hj,h48,show ¬16+j<64 by omega,show j-48<16 by omega,show j-48<64 by omega]
    congr 1
    omega

theorem sigBC_tail_words (sig : SharedSignature) :
    (sigBC sig).extractLsb' (64*654) 64=sigWord sig 654 ∧
    (sigBC sig).extractLsb' (64*655) 64=sigWord sig 655 := by
  have ht:=digC_sigBC sig 179 (by omega)
  change ((sigBC sig).extractLsb' (128*327) 112).setWidth 128=ClaudeWCT.WCT9.setTop ((sigDigests sig).getD 179 0) 0 at ht
  have h0:=congrArg (fun d : Digest=>d.extractLsb' 0 64) ht
  have h1:=congrArg (fun d : Digest=>d.extractLsb' 64 64) ht
  rw [tail_low_word,setTop_low] at h0
  rw [tail_high_word,setTop_high] at h1
  refine ⟨h0,?_⟩
  rw [high_word_hints,h1]
  have hh:=policyHints_sigDecC_sigBC sig
  change (sigBC sig).extractLsb' (8*5246) 16=sig.policyHints at hh
  rw [hh]
  rfl

#print axioms sigBC_tail_words
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem hint_shift (w : Word) : w<<<48=(w.setWidth 16).setWidth 64<<<48 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth]
  by_cases hj48 : j<48
  · simp [hj,hj48]
  · simp [hj,hj48,show j-48<64 by omega,show j-48<16 by omega]

theorem sigBC_all_words (sig : SharedSignature) (k : Nat) (hk : k<656) :
    (sigBC sig).extractLsb' (64*k) 64=sigWord sig k := by
  by_cases h : k<654
  · exact sigBC_word sig k h
  · have h' : k=654 ∨ k=655 := by omega
    rcases h' with rfl|rfl
    · exact (sigBC_tail_words sig).1
    · exact (sigBC_tail_words sig).2

theorem words_map (t : MachineState) (A : Nat) : ∀n,
    t.readWords (BitVec.ofNat 64 A) n=(List.range n).map (fun j=>t.getMem (BitVec.ofNat 64 (A+8*j)))
  | 0 => rfl
  | n+1 => by
    rw [readWords_add,words_map t A n,readWords_one,List.range_succ,List.map_append]
    rfl

theorem readBuffer_encoded (t : MachineState) (sig : SharedSignature)
    (hw : ∀k,k<656 → t.getMem (BitVec.ofNat 64 (SIG+8*k))=sigWord sig k) :
    readBuffer t SIG 5248=sigBC sig := by
  have hw' : t.readWords (BitVec.ofNat 64 SIG) 656=wordsOf (SphincsSecurity.bytesLE 5248 (sigBC sig)) := by
    rw [words_map,wordsOf_bytesLE 656]
    apply List.map_congr_left
    intro k hk
    have hk' : k<656 := List.mem_range.mp hk
    exact (hw k hk').trans (sigBC_all_words sig k hk').symm
  have h:=readBuffer_of_words t SIG 656 (SphincsSecurity.bytesLE 5248 (sigBC sig))
    (by decide) (by decide) (by rw [SphincsSecurity.bytesLE_length]) hw'
  rw [readLE_bytesLE] at h
  change readBuffer t SIG 5248=BitVec.ofNat (8*5248) (sigBC sig).toNat at h
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using h

theorem serialize_good {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 540)
    (sig : SharedSignature) (hraw : RawAt s sig)
    (hh : (s.getMem 0x66000).setWidth 16=sig.policyHints) :
    ∃n≤8200,∃t,Steps im s n n t ∧ t.pc=pcOf 20745 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t SIG 5248=sigBC sig := by
  obtain ⟨n,hn,t,st,tp,t5,t10,tw⟩:=full_readout hc s hp
  refine ⟨n,hn,t,st,tp,t5,t10,readBuffer_encoded t sig ?_⟩
  intro k hk
  rw [tw k hk]
  exact packedWord_raw hraw (by rw [hint_shift,hh]) k hk

#print axioms serialize_good
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem pair_rawIndex (p : Fin 4) (j : Nat) (hj : j<25) :
    rawIndex (1+25*p.val+j)=1+26*p.val+j+(if j<12 then 0 else 1) := by
  fin_cases p <;>simp only [Fin.reduceFinMk] <;>unfold rawIndex <;>split_ifs <;>omega

theorem rawAt_of_layout (s : MachineState) (sig : SharedSignature)
    (hrho : DigAt s SIG sig.rho)
    (hpairs : ∀p : Fin 4,∀j,j<25 →
      DigAt s (SIG+16*(1+26*p.val+j+(if j<12 then 0 else 1))) ((pairList (sig.forest.pairs p)).getD j 0))
    (hsingle : ∀j,j<13 → DigAt s (SIG+16*(105+j)) ((singletonList sig.forest.singleton).getD j 0))
    (hlayers : ∀lay : Layer,∀j,j<chainCount lay+height lay →
      DigAt s (SIG+16*(ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+23+j)) ((layerList sig lay).getD j 0)) : RawAt s sig := by
  intro k hk
  by_cases h0 : k=0
  · subst k
    rw [ClaudeWCT.W9.T3M.SharedCodec.sigDigests_rho]
    simpa [rawIndex] using hrho
  by_cases hp : k<101
  · let p : Fin 4 := ⟨(k-1)/25,by omega⟩
    let j:= (k-1)%25
    have hj : j<25 := Nat.mod_lt _ (by omega)
    have he : k=1+25*p.val+j := by dsimp [p,j];omega
    rw [he,pair_rawIndex p j hj,sigDigests_pair sig p j hj]
    exact hpairs p j hj
  by_cases hs : k<114
  · have he : rawIndex k=k+4 := by unfold rawIndex;split_ifs <;>omega
    rw [he,show k=101+(k-101) by omega,sigDigests_singleton sig _ (by omega)]
    convert hsingle (k-101) (by omega) using 1 <;>congr 1 <;>omega
  · have he : rawIndex k=k+23 := by unfold rawIndex;split_ifs <;>omega
    rw [he]
    have key (lay : Layer) (j : Nat) (hj : j<chainCount lay+height lay) (heq : k=ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+j) :
        DigAt s (SIG+16*(k+23)) ((sigDigests sig).getD k 0) := by
      rw [heq,sigDigests_layer sig lay j hj,show ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+j+23=ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+23+j by omega]
      exact hlayers lay j hj
    by_cases h1 : k<180
    · exact key 0 (k-114) (by change k-114<54+12;omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
    by_cases h2 : k<230
    · exact key 1 (k-180) (by change k-180<43+7;omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
    by_cases h3 : k<279
    · exact key 2 (k-230) (by change k-230<43+6;omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)
    · exact key 3 (k-279) (by change k-279<43+6;omega) (by simp [ClaudeWCT.W9.T3M.SharedCodec.layIdx];omega)

#print axioms rawAt_of_layout
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem pair_layout (s : MachineState) (p : Fin 4) (op : PairOpening)
    (hfv : ∀i : Fin 6,DigAt s (SIG+16*(1+26*p.val+i.val)) (op.firstValues i))
    (hfp : ∀i : Fin 6,DigAt s (SIG+16*(7+26*p.val+i.val)) (op.firstPath i))
    (hsv : ∀i : Fin 6,DigAt s (SIG+16*(14+26*p.val+i.val)) (op.secondValues i))
    (hsp : ∀i : Fin 7,DigAt s (SIG+16*(20+26*p.val+i.val)) (op.secondPath i))
    (j : Nat) (hj : j<25) :
    DigAt s (SIG+16*(1+26*p.val+j+(if j<12 then 0 else 1))) ((pairList op).getD j 0) := by
  by_cases h6 : j<6
  · rw [if_pos (by omega)]
    rw [show (pairList op).getD j 0=op.firstValues ⟨j,h6⟩ from pairList_firstValue op ⟨j,h6⟩]
    simpa using hfv ⟨j,h6⟩
  by_cases h12 : j<12
  · rw [if_pos h12]
    have he : j=6+(j-6) := by omega
    rw [he,pairList_firstPath op ⟨j-6,by omega⟩]
    convert hfp ⟨j-6,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega
  by_cases h18 : j<18
  · rw [if_neg h12]
    have he : j=12+(j-12) := by omega
    rw [he,pairList_secondValue op ⟨j-12,by omega⟩]
    convert hsv ⟨j-12,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega
  · rw [if_neg h12]
    have he : j=18+(j-18) := by omega
    rw [he,pairList_secondPath op ⟨j-18,by omega⟩]
    convert hsp ⟨j-18,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega

theorem singleton_layout (s : MachineState) (op : SingletonOpening)
    (hv : ∀i : Fin 6,DigAt s (SIG+16*(105+i.val)) (op.values i))
    (hp : ∀i : Fin 7,DigAt s (SIG+16*(111+i.val)) (op.path i))
    (j : Nat) (hj : j<13) : DigAt s (SIG+16*(105+j)) ((singletonList op).getD j 0) := by
  unfold singletonList
  by_cases h6 : j<6
  · rw [getD_append_left' (by simp;omega),getD_ofFn' _ j h6]
    exact hv ⟨j,h6⟩
  · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (j-6) (by omega)]
    convert hp ⟨j-6,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega

theorem layer_layout (s : MachineState) (sig : SharedSignature) (lay : Layer)
    (hv : ∀i : Fin (chainCount lay),DigAt s (SIG+16*(ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+23+i.val)) ((sig.layers lay).values i))
    (hp : ∀i : Fin (height lay),DigAt s (SIG+16*(ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+23+chainCount lay+i.val)) ((sig.layers lay).path i))
    (j : Nat) (hj : j<chainCount lay+height lay) :
    DigAt s (SIG+16*(ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+23+j)) ((ClaudeWCT.W9.T3M.SharedCodec.layerList sig lay).getD j 0) := by
  unfold ClaudeWCT.W9.T3M.SharedCodec.layerList
  by_cases hc : j<chainCount lay
  · rw [getD_append_left' (by simp;omega),getD_ofFn' _ j hc]
    exact hv ⟨j,hc⟩
  · rw [getD_append_right' (by simp;omega),List.length_ofFn,getD_ofFn' _ (j-chainCount lay) (by omega)]
    convert hp ⟨j-chainCount lay,by omega⟩ using 1 <;>dsimp only <;>congr 1 <;>omega

#print axioms pair_layout
#print axioms singleton_layout
#print axioms layer_layout
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem forest_pair_layout (s : MachineState) (forest : ForestOpening)
    (hv : ∀c : Fin 9,∀i : Fin 6,DigAt s (slotV c.val i.val) (SharedCoordinate.openingValues forest c i))
    (hp : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt s (SharedPath.target c.val l) (SharedCoordinate.openingPath forest c l))
    (p : Fin 4) (j : Nat) (hj : j<25) :
    DigAt s (SIG+16*(1+26*p.val+j+(if j<12 then 0 else 1))) ((pairList (forest.pairs p)).getD j 0) := by
  apply pair_layout s p (forest.pairs p) _ _ _ _ j hj
  · intro i
    have h:=hv ⟨2*p.val,by omega⟩ i
    fin_cases p <;>simpa [SharedCoordinate.openingValues,slotV,Nat.mul_add,Nat.add_assoc] using h
  · intro i
    have h:=hp ⟨2*p.val,by omega⟩ i.val (by fin_cases p <;>simpa [SharedPath.levels] using i.isLt)
    fin_cases p <;>simpa [SharedCoordinate.openingPath,SharedPath.target,slotV,Nat.mul_add,Nat.add_assoc,Nat.mod_eq_of_lt i.isLt] using h
  · intro i
    have h:=hv ⟨2*p.val+1,by omega⟩ i
    fin_cases p <;>simpa [SharedCoordinate.openingValues,slotV,Nat.mul_add,Nat.add_assoc] using h
  · intro i
    have h:=hp ⟨2*p.val+1,by omega⟩ i.val (by fin_cases p <;>simpa [SharedPath.levels] using i.isLt)
    fin_cases p <;>simpa [SharedCoordinate.openingPath,SharedPath.target,slotV,Nat.mul_add,Nat.add_assoc,Nat.mod_eq_of_lt i.isLt] using h

theorem forest_singleton_layout (s : MachineState) (forest : ForestOpening)
    (hv : ∀c : Fin 9,∀i : Fin 6,DigAt s (slotV c.val i.val) (SharedCoordinate.openingValues forest c i))
    (hp : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt s (SharedPath.target c.val l) (SharedCoordinate.openingPath forest c l))
    (j : Nat) (hj : j<13) : DigAt s (SIG+16*(105+j)) ((singletonList forest.singleton).getD j 0) := by
  apply singleton_layout s forest.singleton _ _ j hj
  · intro i
    simpa [SharedCoordinate.openingValues,slotV,Nat.mul_add,Nat.add_assoc] using hv 8 i
  · intro i
    have h:=hp 8 i.val (by simpa [SharedPath.levels] using i.isLt)
    simpa [SharedCoordinate.openingPath,SharedPath.target,slotV,Nat.mul_add,Nat.add_assoc,Nat.mod_eq_of_lt i.isLt] using h

#print axioms forest_pair_layout
#print axioms forest_singleton_layout
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedRootBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

abbrev enc : Nat := 0x20260

def words : List (BitVec 32) := bv_list% 32 [0x20eb7,0x3a0e8e93,0x20f37,0x260f0f13,0xeb303,0x8eb383,0x6f3023,0x7f3423,0x36d1706f]
sym_block block := symRun {noAlias:=true} words (pcOf 370) 100

theorem steps {im : Image} (hc : CodeAt im (pcOf 370) words) (s : MachineState) (hp : s.pc=pcOf 370) :
    ∃t,Steps im s 9 9 t ∧ t.pc=pcOf 24661 ∧
      t.getMem (BitVec.ofNat 64 enc)=s.getMem (BitVec.ofNat 64 FOUT) ∧
      t.getMem (BitVec.ofNat 64 (enc+8))=s.getMem (BitVec.ofNat 64 (FOUT+8)) ∧
      RegsExcept s t [.x6,.x7,.x29,.x30] ∧ Frame s t (fun A=>A=enc ∨ A=enc+8) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [block.res,rv_simp]
  · simp [block.res,rv_simp,enc,FOUT]
  · simp [block.res,rv_simp,enc,FOUT]
  · intro r hr;cases r <;>simp at hr <;>rfl
  · intro A hA hn
    simp only [Result.toState_getMem,block.res]
    t3n [enc,FOUT]
    repeat rw [if_neg (by unfold enc at hn;omega)]

theorem installed_code : CodeAt Images.signImage (pcOf 370) words := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;>decide +kernel

#print axioms steps
#print axioms installed_code
end ClaudeWCT.W9.Machine.Sign.SharedRootBridge
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def LayerFields (s : MachineState) (pieces : List SigGolfCandidate.T3.Pieces) : Prop :=
  ∀lay : Layer,
    (∀i,i<chainCount lay → DigAt s (SIG+16*(SigGolfCandidate.T3M.layIdx lay+i)) ((pieces.getD lay.val ([],[])).1.getD i 0)) ∧
    (∀j,j<height lay → DigAt s (SIG+16*(SigGolfCandidate.T3M.layIdx lay+chainCount lay+j)) ((pieces.getD lay.val ([],[])).2.getD j 0))

theorem stored_layer_fields {s : MachineState} {lay : Layer} {pieces : SigGolfCandidate.T3.Pieces}
    (hl : lay≠0) (hn : pieces.1.length=43) (hh : pieces.2.length=height lay)
    (h : PiecesStored lay pieces s) :
    (∀i,i<chainCount lay → DigAt s (SIG+16*(SigGolfCandidate.T3M.layIdx lay+i)) (pieces.1.getD i 0)) ∧
    (∀j,j<height lay → DigAt s (SIG+16*(SigGolfCandidate.T3M.layIdx lay+chainCount lay+j)) (pieces.2.getD j 0)) := by
  constructor
  · intro i hi
    have hi' : i<43 := by fin_cases lay <;>simp_all [chainCount]
    have h':=h.1 i (by omega)
    fin_cases lay <;>simp_all [SharedRootControl.sigBase,SigGolfCandidate.T3M.layIdx,SIG,Nat.mul_add,←Nat.add_assoc]
  · intro j hj
    have h':=h.2 j (by omega)
    fin_cases lay <;>simp_all [SharedRootControl.sigBase,SigGolfCandidate.T3M.layIdx,SIG,chainCount,Nat.mul_add,←Nat.add_assoc]

theorem completed_layer_fields {index : Nat} {p : PreparedRoots} {a : Choices} {top : SigGolfCandidate.T3.Pieces}
    {s : MachineState} (h : Completed index p a top s) : LayerFields s (layersValue index p a top).pieces := by
  intro lay
  fin_cases lay
  · constructor
    · intro i hi
      simpa [layersValue,SigGolfCandidate.T3M.layIdx,Nat.mul_add,←Nat.add_assoc] using h.topValues i hi
    · intro j hj
      simpa [layersValue,SigGolfCandidate.T3M.layIdx,chainCount,Nat.mul_add,←Nat.add_assoc] using h.topPath j hj
  · exact stored_layer_fields (by decide) (prepared_length 1 (by decide) _ _ _).1
      (prepared_length 1 (by decide) _ _ _).2 h.one
  · exact stored_layer_fields (by decide) (prepared_length 2 (by decide) _ _ _).1
      (prepared_length 2 (by decide) _ _ _).2 h.two
  · exact stored_layer_fields (by decide) (prepared_length 3 (by decide) _ _ _).1
      (prepared_length 3 (by decide) _ _ _).2 h.three

#print axioms completed_layer_fields
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem shared_layIdx_eq (lay : Layer) :
    SigGolfCandidate.T3M.layIdx lay=ClaudeWCT.W9.T3M.SharedCodec.layIdx lay+23 := by
  fin_cases lay <;>rfl

theorem assembled_raw (s : MachineState) (rho : Digest) (hints : BitVec 16)
    (forest : ForestOpening) (pieces : List SigGolfCandidate.T3.Pieces)
    (hrho : DigAt s SIG rho)
    (hv : ∀c : Fin 9,∀i : Fin 6,DigAt s (slotV c.val i.val) (SharedCoordinate.openingValues forest c i))
    (hp : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt s (SharedPath.target c.val l) (SharedCoordinate.openingPath forest c l))
    (hl : LayerFields s pieces) :
    RawAt s ⟨rho,hints,forest,fun lay=>piecesSignature lay (pieces.getD lay.val ([],[]))⟩ := by
  apply rawAt_of_layout s _ hrho
  · exact forest_pair_layout s forest hv hp
  · exact forest_singleton_layout s forest hv hp
  · intro lay j hj
    apply layer_layout s _ lay _ _ j hj
    · intro i
      rw [←shared_layIdx_eq]
      exact (hl lay).1 i.val i.isLt
    · intro i
      rw [←shared_layIdx_eq]
      exact (hl lay).2 i.val i.isLt

#print axioms assembled_raw
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedCoordinate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def WriteArea (A : Nat) : Prop := (SIG+16≤A ∧ A<SIG+1888) ∨ (0x50000≤A ∧ A<0x68000)

theorem coordinate_write_area {c A : Nat} (hc : c<9) (h : coordinateW c A) : WriteArea A := by
  have hn : SharedFinish.nwords c≤8 := by unfold SharedFinish.nwords;split_ifs <;>omega
  have hlevels : SharedPath.levels c≤7 := SharedPath.levels_bound c
  have htarget : 0x50000≤SharedFinish.target c ∧ SharedFinish.target c+64<0x68000 := by
    unfold SharedFinish.target
    split_ifs <;> (try simp only [FORW]) <;> omega
  unfold coordinateW allWrites writes FinalWrites at h
  rcases h with h|((h|h)|(h|h|h))
  · unfold SharedReuse.coefW WriteArea at *
    simp only [PRIVW,COEF,SIG] at *
    omega
  · unfold loopW bodyW WriteArea at *
    simp only [PRIVW,PAIRW,CHAINW,LEAFW,HEAPW,SCREND,slotV,SIG] at *
    omega
  · unfold treeW WriteArea at *
    simp only [NODEW,NOUTW,HEAPW,SIG] at *
    omega
  · rcases h with ⟨k,hk,rfl⟩
    right
    omega
  · left
    simp only [SharedPath.target,slotV] at h
    omega
  · left
    simp only [SharedEnd.target,slotP] at h
    omega

theorem ClosedPost.write_frame {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : ClosedPost sk a s rv t) : Frame s t (fun A=>WriteArea A ∨ FinalW A) := by
  apply h.frame.mono
  intro A hA hw
  rcases hw with hw|hw|hw|hw|⟨c,hc,hw⟩|hw
  · left;right;subst A;decide
  · left;right;subst A;decide
  · left;right;subst A;decide
  · left;right;subst A;decide
  · exact Or.inl (coordinate_write_area hc hw)
  · exact Or.inr hw

#print axioms ClosedPost.write_frame
end ClaudeWCT.W9.Machine.Sign.SharedCoordinate
namespace ClaudeWCT.W9.Machine.Sign.SharedNonceJump
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def words : List (BitVec 32) := [0x6bd1506f]
sym_block block := symRun {noAlias:=true} words (pcOf 153) 10

theorem steps {im : Image} (hc : CodeAt im (pcOf 153) words) (s : MachineState) (hp : s.pc=pcOf 153) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 22600 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr;cases r <;>rfl
  · intro A hA hn;rfl

theorem installed_code : CodeAt Images.signImage (pcOf 153) words := by
  apply SigGolfCandidate.T3M.codeAt_sign_current_slice <;>decide +kernel
#print axioms steps
#print axioms installed_code
end ClaudeWCT.W9.Machine.Sign.SharedNonceJump
namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem sign_steps_free {im : Image} (hc : CodeAt im (pcOf 22754) signCode)
    (s : MachineState) (hp : s.pc=pcOf 22754) :
    ∃t,Steps im s 8 8 t ∧ t.pc=pcOf 11175 ∧
      t.getReg .x22=s.getMem 0x20160 >>> 33 ∧
      t.getMem 0x20550=s.getMem 0x20160 >>> 33 ∧
      RegsExcept s t [.x22,.x28] ∧ Frame s t (fun A=>A=0x20550) := by
  refine ⟨_,symRun_sound signRun hc s hp ?_,?_,?_,?_,?_,?_⟩
  · simp [signRun.res,rv_simp,accessValid_iff,MEMORY_BYTES]
  · rfl
  · simp [signRun.res,rv_simp]
  · simp [signRun.res,rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,signRun.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA),if_neg hn]

sym_block failJump := symRun {noAlias:=true} [0xcccea06f] (pcOf 22764) 2

theorem sign_failure_steps {im : Image}
    (hc : CodeAt im (pcOf 22764) [0xcccea06f])
    (hf : CodeAt im (pcOf 543) failureCode) (s : MachineState) (hp : s.pc=pcOf 22764) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 545 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧
      Frame s t (fun _=>False) := by
  have hs : Steps im s 1 1 (failJump.res.toState s) :=
    symRun_sound failJump hc s hp (by simp [failJump.res,rv_simp])
  obtain ⟨t,st,pt,h5,h10,rt,ft⟩:=failure_steps false hf (failJump.res.toState s) rfl
  refine ⟨t,hs.trans st,pt,h5,h10,?_⟩
  have ff : Frame s (failJump.res.toState s) (fun _=>False) :=fun A _ _=>rfl
  exact (ff.trans ft).mono (fun _ _ h=>h.elim id id)
#print axioms sign_steps_free
#print axioms sign_failure_steps
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
namespace SigGolfCandidate.T3M.Sign.SharedFlagInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen SigGolfCandidate.T3M.Search
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem frame_result (s : MachineState) : Frame s (block.res.toState s) (fun A=>A=TOP_DATA+624) := by
  intro A hA hn
  simp only [Result.toState_getMem,block.res];t3n []
  rw [if_neg (by unfold TOP_DATA at hn;omega)]

theorem base_result {sk : SecretKey} {cache : Bytes 131072} {cfFlag : Nat} {s : MachineState}
    (hb : Base (cfFlag:=cfFlag) sk cache s) : Base (cfFlag:=0) sk cache (block.res.toState s) := by
  have ff:=frame_result s
  have ht:=tables_result s cfFlag hb.table hb.cf hb.reward
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,ht.1,ht.2.1,ht.2.2⟩
  · exact hb.x5
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p0
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p8
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p32
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p40
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p48
  · rw [ff.get (by unfold PRIV;decide) (by unfold PRIV TOP_DATA;decide)];exact hb.p56
  · intro k hk
    rw [ff.get (by unfold REGION;omega) (by unfold REGION TOP_DATA;omega)]
    exact hb.region k hk
  · intro A hA hn
    rw [ff.get hA (by unfold NeverW at hn;unfold TOP_DATA;sg_omega)]
    exact hb.zero A hA hn

theorem steps_base {im : Image} (hc : CodeAt im (pcOf 24661) code)
    {sk : SecretKey} {cache : Bytes 131072} {cfFlag : Nat}
    (s : MachineState) (hp : s.pc=pcOf 24661) (hb : Base (cfFlag:=cfFlag) sk cache s) :
    ∃t,Steps im s 4 4 t ∧ t.pc=pcOf 22100 ∧ Base (cfFlag:=0) sk cache t ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>A=TOP_DATA+624) := by
  refine ⟨_,symRun_sound block hc s hp (by simp [block.res,rv_simp]),?_,base_result hb,?_,frame_result s⟩
  · simp [block.res,rv_simp]
  · intro r hr;cases r <;>first | exact (hr (by decide)).elim | rfl
#print axioms base_result
#print axioms steps_base
end SigGolfCandidate.T3M.Sign.SharedFlagInit
namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def JoinedPost (im : Image) (s : MachineState) : Option (BitVec 32×BitVec 256)→MachineState→Prop
  | none,t => t.pc=pcOf 545 ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch im t=some (.base .ECALL)
  | some (c,a),t => c.toNat<2^21 ∧ SharedForest.digestAccepted a=true ∧
      t.pc=pcOf 11175 ∧ t.getReg .x5=0 ∧
      t.getReg .x22=BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      t.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a) ∧ OutAt t NBUF a ∧
      Frame s t (fun A=>SharedDigest.writes A ∨ A=0x20550)

theorem search_to_forest {im : Image} {sk : BitVec 256}
    (hl : LookOK im (SharedDigest.look false))
    (hs : CodeAt im (pcOf 22754) signCode)
    (hj : CodeAt im (pcOf 22764) [0xcccea06f])
    (hf : CodeAt im (pcOf 543) failureCode)
    (he : CodeAt im (pcOf 545) [0x73])
    {s : MachineState} {rho : BitVec 128} {msg : SigGolfCandidate.T3.Message}
    (hp : SharedDigest.Pre false rho msg s) (hpc : s.pc=pcOf 22600) :
    TBSim im sk s (2^21*200+20) (SharedForest.sharedDigestSearch rho msg 0 (2^21)) (JoinedPost im s) := by
  rw [←bind_pure (SharedForest.sharedDigestSearch rho msg 0 (2^21))]
  refine (TBSim.bind (SharedDigest.search_good false hl hp hpc) (W₂:=8) ?_).mono (by omega) (fun _ _ h=>h)
  intro r u hu
  cases r with
  | none =>
    obtain ⟨t,st,pt,h5,h10,ft⟩:=sign_failure_steps hj hf u hu.result.1
    have hp' : JoinedPost im s none t:=⟨pt,h5,h10,(he.fetch t pt).trans rfl⟩
    exact (TBSim.pure_steps' st hp').mono (by omega) (fun _ _ h=>h)
  | some r =>
    rcases r with ⟨c,a⟩
    obtain ⟨pcu,h19,hc,ha,hN⟩:=hu.result
    obtain ⟨t,st,pt,h22,hidx,rt,ft⟩:=sign_steps_free hs u pcu
    have hword : u.getMem 0x20160 >>> 33=BitVec.ofNat 64 (WCT9.digestIndex a) := by
      have h0:=hN 0 (by decide)
      change u.getMem 0x20160=a.extractLsb' 0 64 at h0
      rw [h0]
      simpa only [BitVec.shiftLeft_zero] using SearchM.shl0_shr33 a
    have hNt : OutAt t NBUF a := by
      intro j hj
      rw [ft.get (by unfold NBUF;omega) (by unfold NBUF;omega)]
      exact hN j hj
    have ht : JoinedPost im s (some (c,a)) t :=
      ⟨hc,ha,pt,(rt.get (by decide)).trans hu.x5,h22.trans hword,hidx.trans hword,hNt,hu.frame.trans ft⟩
    exact TBSim.pure_steps' st ht
#print axioms search_to_forest
end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
namespace ClaudeWCT.W9.Machine.Sign.SharedState
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem base_frame_mem {sk : SecretKey} {cache : Bytes 131072} {cfFlag : Nat}
    {s t : MachineState} {W : Nat→Prop} (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hf : Frame s t W) (h5 : t.getReg .x5=0)
    (hn : ∀ A,A<2^64 → BaseA A → ¬W A) : Base (cfFlag:=cfFlag) sk cache t := by
  apply hb.frame hf (l:=[.x0,.x1,.x2,.x3,.x4,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]) ?_ (by decide) hn
  intro r hr
  cases r <;>simp only [List.mem_cons,List.mem_singleton,not_or] at hr <;>
    first | contradiction | exact h5.trans hb.x5.symm

theorem forest_base {sk a : BitVec 256} {cache : Bytes 131072} {cfFlag : Nat}
    {s t : MachineState} {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (hb : Base (cfFlag:=cfFlag) sk cache s) (h : SharedCoordinate.ClosedPost sk a s rv t) :
    Base (cfFlag:=cfFlag) sk cache t := by
  apply base_frame_mem hb h.write_frame h.x5
  intro A hA hb hw
  unfold BaseA NeverW at hb
  unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW at hw
  simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,SigGolfCandidate.T3M.Sign.NBUF,Search.TOP_DATA,SIG,FOUT] at hb hw
  omega

theorem forest_rho {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : SharedCoordinate.ClosedPost sk a s rv t) {rho : BitVec 128} (hr : DigAt s SIG rho) : DigAt t SIG rho := by
  exact hr.frame h.write_frame (by unfold SIG;decide)
    (by unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW SIG FOUT;decide)
    (by unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW SIG FOUT;decide)

theorem forest_counter {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : SharedCoordinate.ClosedPost sk a s rv t) :
    t.getMem (BitVec.ofNat 64 (ENC+32))=s.getMem (BitVec.ofNat 64 (ENC+32)) :=
  h.write_frame.get (by unfold ENC;decide)
    (by unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW SIG FOUT ENC;decide)

theorem forest_index {sk a : BitVec 256} {s t : MachineState}
    {rv : SigGolfCandidate.Research.SharedForest.ForestOpening×SigGolfCandidate.Research.SharedForest.PairRoot}
    (h : SharedCoordinate.ClosedPost sk a s rv t) : t.getMem 0x20550=s.getMem 0x20550 :=
  h.write_frame.get (A:=0x20550) (by decide)
    (by unfold SharedCoordinate.WriteArea SharedCoordinate.FinalW SIG FOUT;decide)
#print axioms forest_base
#print axioms forest_rho
end ClaudeWCT.W9.Machine.Sign.SharedState
namespace ClaudeWCT.W9.Machine.Sign.SharedRootBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

structure Ready (sk : SecretKey) (cache : Bytes 131072) (index : Nat)
    (forest : BitVec 128×BitVec 128) (s : MachineState) : Prop where
  pc : s.pc=pcOf 22100
  base : Base (cfFlag:=0) sk cache s
  indexMem : s.getMem 0x20550=BitVec.ofNat 64 index
  counter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c
  rootLeft : DigAt s ENC forest.1
  rootRight : DigAt s (ENC+48) forest.2

theorem bridge_steps {im : Image}
    (hc : CodeAt im (pcOf 370) words) (hf : CodeAt im (pcOf 24661) SharedFlagInit.code)
    {sk : SecretKey} {cache : Bytes 131072} {cfFlag index : Nat} (forest : BitVec 128×BitVec 128)
    (s : MachineState) (hp : s.pc=pcOf 370) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hcounter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hl : DigAt s FOUT forest.1) (hr : DigAt s (ENC+48) forest.2) :
    ∃t,Steps im s 13 13 t ∧ Ready sk cache index forest t ∧
      Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)) := by
  obtain ⟨u,su,pu,l0,l8,ru,fu⟩:=steps hc s hp
  have bu : Base (cfFlag:=cfFlag) sk cache u := hb.frame fu ru (by decide) (by
    intro A hA ha hw
    unfold BaseA NeverW at ha
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,SigGolfCandidate.T3M.Sign.NBUF,Search.TOP_DATA] at ha
    unfold enc at hw
    omega)
  obtain ⟨t,st,pt,bt,rt,ft⟩:=SharedFlagInit.steps_base hf u pu bu
  have mem : ∀A,A<2^64 → A≠enc → A≠enc+8 → A≠Search.TOP_DATA+624 →
      t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h0 h8 ht
    rw [ft.get hA ht,fu.get hA (by simp [h0,h8])]
  refine ⟨t,su.trans st,⟨pt,bt,?_,?_,?_,?_⟩,?_⟩
  · exact (mem 0x20550 (by decide) (by unfold enc;decide) (by unfold enc;decide) (by unfold Search.TOP_DATA;decide)).trans hi
  · obtain ⟨c,hc,hcv⟩:=hcounter
    exact ⟨c,hc,(mem (ENC+32) (by unfold ENC;decide) (by unfold ENC enc;decide)
      (by unfold ENC enc;decide) (by unfold ENC Search.TOP_DATA;decide)).trans hcv⟩
  · constructor
    · rw [ft.get (by unfold ENC;decide) (by unfold ENC Search.TOP_DATA;decide)]
      exact l0.trans hl.1
    · rw [ft.get (by unfold ENC;decide) (by unfold ENC Search.TOP_DATA;decide)]
      exact l8.trans hl.2
  · exact hr.frame (fu.trans ft) (by unfold ENC;decide)
      (by unfold ENC enc Search.TOP_DATA;decide) (by unfold ENC enc Search.TOP_DATA;decide)
  · apply (fu.trans ft).mono
    intro A hA hw hlo
    simp only [enc,SIG,Search.TOP_DATA] at hw hlo
    omega
#print axioms bridge_steps
end ClaudeWCT.W9.Machine.Sign.SharedRootBridge
namespace ClaudeWCT.W9.Machine.Sign.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Research
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.Boundary
open SharedDigestBoundary
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem joined_prepend {im : Image} {s u t : MachineState} {r : Option (BitVec 32×BitVec 256)}
    (hf : Frame s u (fun _=>False)) (h : JoinedPost im u r t) : JoinedPost im s r t := by
  cases r with
  | none => exact h
  | some r =>
    rcases h with ⟨hc,ha,hp,h5,h22,hi,hN,ff⟩
    refine ⟨hc,ha,hp,h5,h22,hi,hN,(hf.trans ff).mono ?_⟩
    intro A hA hw
    exact hw.elim False.elim id

theorem nonce_search {sk : SecretKey} {cache : Bytes 131072} {msg : SigGolfCandidate.T3.Message}
    {α : Type} {W : Nat} {Q : Option α→MachineState→Prop}
    (hlook : LookOK Images.signImage (SharedDigest.look false))
    (hs : CodeAt Images.signImage (pcOf 22754) signCode)
    (hj : CodeAt Images.signImage (pcOf 22764) [0xcccea06f])
    (hf : CodeAt Images.signImage (pcOf 543) failureCode)
    (he : CodeAt Images.signImage (pcOf 545) [0x73])
    (htables : ∀rho t,NoncePost sk cache msg rho t → SharedDigest.TablesAt false t)
    (K : BitVec 128→BitVec 32→BitVec 256→SigGolfCandidate.T3.M (Option α))
    (hfail : ∀t,JoinedPost Images.signImage t none t → Q none t)
    (hrest : ∀rho s,NoncePost sk cache msg rho s → ∀c a t,
      JoinedPost Images.signImage s (some (c,a)) t → TBSim Images.signImage sk t W (K rho c a) Q) :
    TBSim Images.signImage sk (sinit sk cache msg) (frontC+(1+(2^21*200+20+W))) (do
      let tag ← SigGolfCandidate.T3.privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else do
        let rho ← SigGolfCandidate.T3.privateNonce msg
        let r ← SharedForest.sharedDigestSearch rho msg 0 (2^21)
        match r with
        | none => pure none
        | some (c,a) => K rho c a) Q := by
  apply Generic.sign_nonce_front
  · intro t ht
    exact hfail t ⟨ht.pc,ht.x5,ht.x10,(he.fetch t ht.pc).trans rfl⟩
  · intro rho s hn
    obtain ⟨u,su,pu,ru,fu⟩:=SharedNonceJump.steps SharedNonceJump.installed_code s hn.search.pc
    have hp : SharedDigest.Pre false rho msg u := by
      refine ⟨(ru.get (by simp)).trans hn.search.x5,?_,?_,?_⟩
      · exact hn.search.rho.frame fu (by unfold SigGolfCandidate.T3M.Sign.DIG;decide) (by tauto) (by tauto)
      · intro k hk
        rw [fu.get (by unfold DIG;omega) (by tauto)]
        exact hn.search.msg k hk
      · exact (htables rho s hn).frame (fu.mono (fun _ _ h=>h.elim))
    apply TBSim.steps su
    refine TBSim.bind (search_to_forest hlook hs hj hf he hp pu) (W₂:=W) ?_
    intro r t ht
    cases r with
    | none => exact (TBSim.pure (hfail t ht)).mono (by omega) (fun _ _ h=>h)
    | some r => exact hrest rho s hn r.1 r.2 t (joined_prepend fu ht)
#print axioms nonce_search
end ClaudeWCT.W9.Machine.Sign.SharedFront
namespace ClaudeWCT.W9.Machine.Sign.SharedState
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Keygen
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem digest_state {im : Image} {sk : SecretKey} {cache : Bytes 131072} {cfFlag : Nat}
    {rho : BitVec 128} {msg : SigGolfCandidate.T3.Message} {s t : MachineState} {c : BitVec 32} {a : BitVec 256}
    (hp : HookPre sk msg rho s) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hz : s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (hj : SharedDigestBoundary.JoinedPost im s (some (c,a)) t) :
    SharedCoordinate.Entry sk a t ∧ Base (cfFlag:=cfFlag) sk cache t ∧ DigAt t SIG rho ∧
      t.getMem (BitVec.ofNat 64 (ENC+32))=0 ∧
      t.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      (∀k,k<9 → SharedCoordinate.rank k a<563) := by
  rcases hj with ⟨hc,ha,hpc,h5,h22,hidx,hN,hf⟩
  have gm : ∀A,A<2^64 → ¬(SharedDigest.writes A ∨ A=0x20550) →
      t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) :=fun A hA hn=>hf.get hA hn
  refine ⟨⟨hpc,h5,h22,hN,?_,?_,?_⟩,?_,?_,?_,hidx,?_⟩
  · intro k hk
    rw [gm _ (by unfold TBL;omega) (by unfold SharedDigest.writes DIG NBUF TBL;omega)]
    exact hp.table k hk
  · intro k hk
    rw [gm _ (by unfold SK;omega) (by unfold SharedDigest.writes DIG NBUF SK;omega)]
    exact hp.sk k hk
  · intro A hA
    have hzero:=hA.1
    rw [gm _ (by unfold ScrZero PRIVW CHAINW NODEW at hzero;omega)
      (by unfold SharedDigest.writes DIG NBUF;unfold ScrZero PRIVW CHAINW NODEW at hzero;omega)]
    exact hp.zero A hzero
  · apply base_frame_mem hb hf h5
    intro A hA hbase hw
    unfold BaseA NeverW at hbase
    unfold SharedDigest.writes at hw
    simp only [PRIV,REGION,FLEAF,NODE,CHAIN,ZDIG,ENC,SigGolfCandidate.T3M.Sign.NBUF,Search.TOP_DATA,DIG,NBUF] at hbase hw
    omega
  · exact hp.sigRho.frame hf (by unfold SIG;decide)
      (by unfold SharedDigest.writes DIG NBUF SIG;decide)
      (by unfold SharedDigest.writes DIG NBUF SIG;decide)
  · rw [gm _ (by unfold ENC;decide) (by unfold SharedDigest.writes DIG NBUF ENC;decide)]
    exact hz
  · exact ((SharedDigest.acceptedTest_iff a).mp (by rw [SharedDigest.acceptedTest_source];exact ha)).2.1
#print axioms digest_state
end ClaudeWCT.W9.Machine.Sign.SharedState
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

structure ForestFields (rho : Digest) (forest : ForestOpening) (s : MachineState) : Prop where
  rho : DigAt s SIG rho
  values : ∀c : Fin 9,∀i : Fin 6,DigAt s (slotV c.val i.val) (SharedCoordinate.openingValues forest c i)
  paths : ∀c : Fin 9,∀l,l<SharedPath.levels c.val → DigAt s (SharedPath.target c.val l) (SharedCoordinate.openingPath forest c l)

theorem ForestFields.frame {rho : Digest} {forest : ForestOpening} {s t : MachineState}
    (h : ForestFields rho forest s) (hf : Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192))) : ForestFields rho forest t := by
  refine ⟨h.rho.frame hf (by unfold SIG;decide) (by unfold SIG;decide) (by unfold SIG;decide),?_,?_⟩
  · intro c i
    exact (h.values c i).frame hf (by unfold slotV SIG;omega)
      (by unfold slotV SIG;omega) (by unfold slotV SIG;omega)
  · intro c l hl
    have hh : SharedPath.levels c.val≤7 := by unfold SharedPath.levels;split_ifs <;>omega
    exact (h.paths c l hl).frame hf (by unfold SharedPath.target slotV SIG;omega)
      (by unfold SharedPath.target slotV SIG;omega) (by unfold SharedPath.target slotV SIG;omega)

def FinalPost (im : Image) : Option SharedSignature→MachineState→Prop
  | none,t => SearchError im t
  | some sig,t => t.pc=pcOf 20745 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t SIG 5248=sigBC sig ∧ fetch im t=some (.base .ECALL)

def assemble (rho : Digest) (forest : ForestOpening) (layers : CanonicalLayers) : SharedSignature :=
  ⟨rho,layers.policyHints,forest,fun lay=>piecesSignature lay (layers.pieces.getD lay.val ([],[]))⟩

theorem completed_serialize {im : Image} {sk : SecretKey} (hc : Code im)
    {rho : Digest} {forest : ForestOpening} {index : Nat} {p : PreparedRoots}
    {a : Choices} {top : SigGolfCandidate.T3.Pieces} {s : MachineState}
    (hs : Completed index p a top s) (hforest : ForestFields rho forest s) :
    TBSim im sk s 8200 (pure (some (assemble rho forest (layersValue index p a top)))) (FinalPost im) := by
  have hr := assembled_raw s rho (layersValue index p a top).policyHints forest _
    hforest.rho hforest.values hforest.paths (completed_layer_fields hs)
  have hh : (s.getMem 0x66000).setWidth 16=(layersValue index p a top).policyHints := by
    rw [show (0x66000 : Word)=(0x66000#64) by decide,hs.hints]
    apply BitVec.eq_of_toNat_eq
    simp [layersValue,BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_mod_of_dvd _ (show 2^16 ∣ 2^64 by norm_num)]
  obtain ⟨n,hn,t,st,pt,h5,h10,hbytes⟩:=serialize_good hc s hs.pc _ hr hh
  have hpost : FinalPost im (some (assemble rho forest (layersValue index p a top))) t :=
    ⟨pt,h5,h10,hbytes,(hc.halt.tail.fetch t pt).trans rfl⟩
  exact (TBSim.pure_steps' st hpost).mono hn (fun _ _ h=>h)
#print axioms completed_serialize
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem search_serialize {im : Image} {sk : SecretKey} {cache : Bytes 131072} {W : Nat}
    (hc : Code im) {rho : Digest} {forest : ForestOpening} {pair : Digest×Digest}
    {index : Nat} {p : PreparedRoots} {s : MachineState}
    (hsearch : TBSim im sk s W (searchPreparedLayers (cacheDec cache) index p pair) (FramedLayersPost im index p s))
    (hfields : ForestFields rho forest s) :
    TBSim im sk s (W+8200) (do
      let layers ← searchPreparedLayers (cacheDec cache) index p pair
      pure (layers.map (assemble rho forest))) (FinalPost im) := by
  refine TBSim.bind hsearch (W₂:=8200) ?_
  intro layers t ht
  cases layers with
  | none => exact (TBSim.pure (a:=none) (s:=t) (Q:=FinalPost im) ht).mono (by omega) (fun _ _ h=>h)
  | some layers =>
    rcases ht with ⟨⟨a,top,rfl,ha⟩,hf⟩
    exact completed_serialize hc ha (hfields.frame (layers_lowFrame hf))
#print axioms search_serialize
end ClaudeWCT.W9.Machine.Sign.SharedSerializer
namespace ClaudeWCT.W9.Machine.Sign.SharedSerializer
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem prepared_serialize {im : Image} {sk : SecretKey} {cache : Bytes 131072} {Wr Ws : Nat}
    (hc : Code im) {rho : Digest} {forest : ForestOpening} {pair : Digest×Digest}
    {index : Nat} {s : MachineState} {P : PreparedRoots→MachineState→Prop}
    (hroot : TBSim im sk s Wr (prepareRoots index) P)
    (hsearch : ∀p t,P p t → TBSim im sk t Ws (searchPreparedLayers (cacheDec cache) index p pair)
      (FramedLayersPost im index p t))
    (hframe : ∀p t,P p t → Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)))
    (hfields : ForestFields rho forest s) :
    TBSim im sk s (Wr+(Ws+8200)) (do
      let prepared ← prepareRoots index
      let layers ← searchPreparedLayers (cacheDec cache) index prepared pair
      pure (layers.map (assemble rho forest))) (FinalPost im) := by
  refine TBSim.bind hroot (W₂:=Ws+8200) ?_
  intro p t hp
  exact search_serialize hc (hsearch p t hp) (hfields.frame (hframe p t hp))
#print axioms prepared_serialize
end ClaudeWCT.W9.Machine.Sign.SharedSerializer

namespace ClaudeWCT.W9.Machine.Sign.SharedRootBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.Sign
open SigGolfCandidate.T3M.Keygen SigGolfCandidate.Research.SharedForest

theorem roots_good {sk : SecretKey} {cache : Bytes 131072} {index : Nat}
    (hi : index<2^31) {forest : BitVec 128×BitVec 128} {s : MachineState}
    (h : Ready sk cache index forest s) :
    TBSim Images.signImage sk s (28+3*(Packed.btCost+47)) (prepareRoots index)
      (fun p t => SharedRootControl.BuiltPost (cfFlag:=0) sk cache index forest s p t ∧
        SharedRootControl.LowFrame s t) :=
  SharedRootControl.entry_roots_framed SharedRootControl.installed_code
    SharedRootControl.installed_extraCode SharedLowCode.installed_code
    SharedTreeCode.installed_code SharedLeafCode.installed_code SharedLeaf.installed_copy
    SharedChain.installed_code SharedChain.installed_prefix_code
    SharedSeed.installed_code SharedSeed.installed_seed_hook
    hi forest s h.pc h.indexMem h.base h.rootLeft h.rootRight
#print axioms roots_good
end ClaudeWCT.W9.Machine.Sign.SharedRootBridge

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def layersProgram (cache : Bytes 131072) (rho : Digest) (index : Nat)
    (forest : ForestOpening×(Digest×Digest)) : SigGolfCandidate.T3.M (Option SharedSignature) := do
  let prepared ← prepareRoots index
  let layers ← searchPreparedLayers (cacheDec cache) index prepared forest.2
  pure (layers.map (assemble rho forest.1))

theorem after_forest_with {im : Image} {sk : SecretKey} {cache : Bytes 131072} {cfFlag index Wr Ws : Nat}
    (hbridge : CodeAt im (pcOf 370) SharedRootBridge.words)
    (hflag : CodeAt im (pcOf 24661) SharedFlagInit.code) (hcodec : SharedSerializer.Code im)
    {rho : Digest} {forest : ForestOpening×(Digest×Digest)}
    {P : MachineState→PreparedRoots→MachineState→Prop}
    (hroot : ∀s,SharedRootBridge.Ready sk cache index forest.2 s → TBSim im sk s Wr (prepareRoots index) (P s))
    (hsearch : ∀s,SharedRootBridge.Ready sk cache index forest.2 s → ∀p t,P s p t →
      TBSim im sk t Ws (searchPreparedLayers (cacheDec cache) index p forest.2) (FramedLayersPost im index p t))
    (hframe : ∀s p t,P s p t → Frame s t (fun A=>¬(SIG≤A ∧ A<SIG+2192)))
    (s : MachineState) (hp : s.pc=pcOf 370) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hcounter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hl : DigAt s FOUT forest.2.1) (hr : DigAt s (ENC+48) forest.2.2)
    (hfields : ForestFields rho forest.1 s) :
    TBSim im sk s (13+(Wr+(Ws+8200))) (layersProgram cache rho index forest) (FinalPost im) := by
  obtain ⟨t,st,ht,ff⟩:=SharedRootBridge.bridge_steps hbridge hflag forest.2 s hp hb hi hcounter hl hr
  exact TBSim.steps st (prepared_serialize hcodec (hroot t ht) (hsearch t ht)
    (hframe t) (hfields.frame ff))
#print axioms after_forest_with
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def outputProgram (cache : Bytes 131072) (rho : Digest) (a : BitVec 256) :
    SigGolfCandidate.T3.M (Option SharedSignature) := do
  let forest ← buildForest (WCT9.digestIndex a) (forestSelectionFromOutput a) (forestWordsFromOutput a)
  layersProgram cache rho (WCT9.digestIndex a) forest

theorem forest_tbsim_with {im : Image} {sk a : BitVec 256} {cache : Bytes 131072}
    {cfFlag W : Nat} {rho : Digest}
    (hf : SharedReuse.Fetch im) (hc : ∀c,c<9 → SharedCoordinate.Code im c)
    (hl : LookOK im SharedBoundary.forLook)
    (hrest : ∀(forest : ForestOpening×PairRoot) (s : MachineState),s.pc=pcOf 370 →
      Base (cfFlag:=cfFlag) sk cache s → s.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a) →
      (∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c) →
      DigAt s FOUT forest.2.1 → DigAt s (ENC+48) forest.2.2 → ForestFields rho forest.1 s →
      TBSim im sk s W (layersProgram cache rho (WCT9.digestIndex a) forest) (FinalPost im))
    (s : MachineState) (hp : SharedCoordinate.Entry sk a s) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hrho : DigAt s SIG rho) (hz : s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a))
    (hranks : ∀c,c<9 → SharedCoordinate.rank c a<563) :
    TBSim im sk s ((9*SharedCoordinate.forestStepBound+23)+W) (outputProgram cache rho a) (FinalPost im) := by
  refine TBSim.bind (SharedCoordinate.forest_boundary_good hf hc hl hranks s hp) (W₂:=W) ?_
  intro forest t ht
  exact hrest forest t ht.pc (SharedState.forest_base hb ht)
    ((SharedState.forest_index ht).trans hi)
    ⟨0,by decide,by simpa using (SharedState.forest_counter ht).trans hz⟩
    ht.rootLeft ht.rootRight ⟨SharedState.forest_rho ht hrho,ht.values,ht.paths⟩

theorem outputProgram_source (cache : Bytes 131072) (rho : Digest) (c : BitVec 32) (a : BitVec 256) :
    (do let w ← signFromOutput (cacheDec cache) rho c a
        pure (w.map Witness.signature))=outputProgram cache rho a := by
  simp only [signFromOutput,outputProgram,layersProgram,bind_assoc]
  congr 1
  funext forest
  congr 1
  funext prepared
  congr 1
  funext layers
  cases layers <;> simp [assemble]
#print axioms forest_tbsim_with
#print axioms outputProgram_source
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

/-- The paired submission's sizes and layout (stage 2: W 24828, message at 26144 = 0x6620). -/
def runtimeSub (imgs : Phase→Image) : Submission :=
  ⟨⟨5248,24828,131072⟩,⟨0x6620,0x80,0xa0,0x80000,0x7000,0x520⟩,imgs⟩

theorem initialState_of_wsub (imgs : Phase→Image)
    (hv : (imgs .sign).Valid (runtimeSub imgs).sizes (runtimeSub imgs).layout)
    (ho : (imgs .sign).Valid (wsub imgs).sizes (wsub imgs).layout)
    (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) {s : MachineState}
    (h : initialState (wsub imgs) .sign (sk,cache,msg)=some s) :
    initialState (runtimeSub imgs) .sign (sk,cache,msg)=some s := by
  dsimp only [runtimeSub,wsub] at hv ho h ⊢
  simp only [initialState,hv,ho,↓reduceIte] at h ⊢
  exact h

theorem finalPost_halt {im : Image} {o : Option SharedSignature} {t : MachineState}
    (h : FinalPost im o t) : fetch im t=some (.base .ECALL) ∧ t.getReg .x5=1 := by
  cases o with
  | none => exact ⟨h.2.2.2,h.2.1⟩
  | some sig => exact ⟨h.2.2.2.2,h.2.1⟩

theorem finalPost_readout {imgs : Phase→Image} {o : Option SharedSignature} {t : MachineState}
    (h : FinalPost (imgs .sign) o t) :
    o.map sigBC=if t.getReg .x10=0 then some (readOutput (runtimeSub imgs).sizes
      (runtimeSub imgs).layout .sign t) else none := by
  cases o with
  | none => rw [if_neg (by rw [h.2.2.1];decide)];rfl
  | some sig =>
    rw [if_pos h.2.2.1]
    exact congrArg some h.2.2.2.1.symm

theorem runtime_refines {imgs : Phase→Image} {W : Nat}
    (hW : W<CYCLE_LIMIT) (program : SigGolfCandidate.T3.M (Option SharedSignature)) (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message)
    {s : MachineState} (hinit : initialState (runtimeSub imgs) .sign (sk,cache,msg)=some s)
    (hsim : TBSim (imgs .sign) sk s W program
      (FinalPost (imgs .sign))) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> (runtimeSub imgs).run .sign (sk,cache,msg)=
      (fun p=>(p.1.map sigBC,p.2.1,p.2.2)) <$>
        countBoth (mrealize sk program) := by
  apply Sim.run_eq (runtimeSub imgs) .sign (sk,cache,msg) hinit hsim hW (fun o=>o.map sigBC)
  intro o t ht
  exact ⟨(finalPost_halt ht).1,(finalPost_halt ht).2,finalPost_readout ht⟩

theorem runtime_terminates {imgs : Phase→Image} {W : Nat}
    (hW : W+1<CYCLE_LIMIT) (program : SigGolfCandidate.T3.M (Option SharedSignature)) (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message)
    {s : MachineState} (hinit : initialState (runtimeSub imgs) .sign (sk,cache,msg)=some s)
    (hsim : TBSim (imgs .sign) sk s W program
      (FinalPost (imgs .sign))) :
    ((runtimeSub imgs).runWith hash .sign (sk,cache,msg)).finished=true ∧
      ((runtimeSub imgs).runWith hash .sign (sk,cache,msg)).cycles<CYCLE_LIMIT := by
  obtain ⟨hf,hc⟩:=Sim.runWith (runtimeSub imgs) .sign (sk,cache,msg) hinit hsim hW
    (fun _ _ h=>finalPost_halt h) hash
  exact ⟨hf,lt_of_le_of_lt hc hW⟩
#print axioms runtime_refines
#print axioms runtime_terminates
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer

def tailCost : Nat := 13+((28+3*(Packed.btCost+47))+((prefixCost+290006)+8200))

theorem after_forest {sk : SecretKey} {cache : Bytes 131072} {cfFlag index : Nat}
    (hib : index<2^31) {rho : Digest} {forest : ForestOpening×(Digest×Digest)}
    (s : MachineState) (hp : s.pc=pcOf 370) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hcounter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 c)
    (hl : DigAt s FOUT forest.2.1) (hr : DigAt s (ENC+48) forest.2.2)
    (hfields : ForestFields rho forest.1 s) :
    TBSim Images.signImage sk s tailCost (layersProgram cache rho index forest) (FinalPost Images.signImage) := by
  exact after_forest_with SharedRootBridge.installed_code SharedFlagInit.installed_code
    SharedSerializer.installed_code
    (fun _ h=>SharedRootBridge.roots_good hib h)
    (fun _ h _ _ hp=>SharedSearches.from_built_framed hib hp.1 h.counter)
    (fun _ _ _ hp=>hp.2) s hp hb hi hcounter hl hr hfields
#print axioms after_forest
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem option_bind_map {α β : Type} (program : SigGolfCandidate.T3.M (Option α)) (f : α→β) :
    (do let some a ← program | pure none
        pure (some (f a)))=(do let a ← program;pure (a.map f)) := by
  apply congrArg (fun k=>program >>= k)
  funext a
  cases a <;>rfl

theorem sign_program (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    SigGolfCandidate.Research.SharedForest.sign (cacheDec cache) msg=(do
      let tag ← SigGolfCandidate.T3.privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else do
        let rho ← SigGolfCandidate.T3.privateNonce msg
        let r ← sharedDigestSearch rho msg 0 (2^21)
        match r with
        | none => pure none
        | some (_,a) => outputProgram cache rho a) := by
  simp only [SigGolfCandidate.Research.SharedForest.sign,SigGolfCandidate.Research.SharedForest.signPayload,ClaudeWCT.WCT9.digestAttemptLimit]
  congr 1
  funext tag
  split <;>rename_i ht
  · rfl
  · congr 1
    funext rho
    congr 1
    funext r
    cases r with
    | none => rfl
    | some r =>
      rcases r with ⟨c,a⟩
      dsimp only
      refine Eq.trans ?_ (outputProgram_source cache rho c a)
      congr 1
      funext w
      cases w <;>rfl

#print axioms sign_program
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

theorem sign_tbsim_with {W : Nat}
    (hlook : LookOK Images.signImage (SharedDigest.look false))
    (hs : CodeAt Images.signImage (pcOf 22754) SharedDigestBoundary.signCode)
    (hj : CodeAt Images.signImage (pcOf 22764) [0xcccea06f])
    (hf : CodeAt Images.signImage (pcOf 543) SharedDigestBoundary.failureCode)
    (he : CodeAt Images.signImage (pcOf 545) [0x73])
    (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message)
    (htables : ∀rho s,NoncePost sk cache msg rho s → SharedDigest.TablesAt false s)
    (hfront : ∀rho s,NoncePost sk cache msg rho s → HookPre sk msg rho s ∧
      Base sk cache s ∧ s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (houtput : ∀rho a t,SharedCoordinate.Entry sk a t → Base sk cache t → DigAt t SIG rho →
      t.getMem (BitVec.ofNat 64 (ENC+32))=0 →
      t.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a) →
      (∀k,k<9 → SharedCoordinate.rank k a<563) →
      TBSim Images.signImage sk t W (outputProgram cache rho a) (FinalPost Images.signImage)) :
    TBSim Images.signImage sk (sinit sk cache msg) (frontC+(1+(2^21*200+20+W)))
      (SigGolfCandidate.Research.SharedForest.sign (cacheDec cache) msg) (FinalPost Images.signImage) := by
  rw [sign_program]
  refine SharedFront.nonce_search hlook hs hj hf he htables (fun rho _ a=>outputProgram cache rho a)
    (fun _ h=>h) ?_
  intro rho s hn c a t hj
  obtain ⟨hp,hb,hz⟩:=hfront rho s hn
  obtain ⟨he,hb,hr,hz,hi,hranks⟩:=SharedState.digest_state hp hb hz hj
  exact houtput rho a t he hb hr hz hi hranks
#print axioms sign_tbsim_with
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def restCost : Nat := (9*SharedCoordinate.forestStepBound+23)+tailCost
def signCost : Nat := frontC+(1+(2^21*200+20+restCost))

theorem forest_tbsim {sk a : BitVec 256} {cache : Bytes 131072} {rho : Digest}
    (s : MachineState) (hp : SharedCoordinate.Entry sk a s) (hb : Base sk cache s)
    (hrho : DigAt s SIG rho) (hz : s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 (WCT9.digestIndex a))
    (hranks : ∀c,c<9 → SharedCoordinate.rank c a<563) :
    TBSim Images.signImage sk s restCost (outputProgram cache rho a) (FinalPost Images.signImage) := by
  exact forest_tbsim_with SharedReuse.installed_fetch SharedCoordinate.installed_Code
    SharedBoundary.installed_forLook
    (fun _ t=>after_forest (WCT9.digestIndex_lt a) t) s hp hb hrho hz hi hranks

theorem sign_tbsim (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    TBSim Images.signImage sk (sinit sk cache msg) signCost
      (SigGolfCandidate.Research.SharedForest.sign (cacheDec cache) msg) (FinalPost Images.signImage) := by
  exact sign_tbsim_with SharedDigest.installed_sign_look SharedDigestBoundary.installed_sign_success
    SharedDigestBoundary.installed_sign_failure_jump SharedDigestBoundary.installed_sign_failure
    SharedDigestBoundary.installed_sign_failure_ecall sk cache msg
    (fun _ _ hn=>SharedDigest.tables_of_costAt (SignLink.hook_v7 hn).search.cost)
    (fun _ _ hn=>⟨SignLink.hook_v7 hn,hn.inv⟩)
    (fun _ _ t=>forest_tbsim t)

#print axioms forest_tbsim
#print axioms sign_tbsim
end ClaudeWCT.W9.Machine.Sign.SharedController

namespace ClaudeWCT.W9.Machine.Sign.SharedController
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.Research.SharedForest
open ClaudeWCT.W9.T3M.SharedCodec SharedSerializer
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

/-- C1 (stage 1): the leaf stub adds at most 9 steps per leaf and the fold stub at most 6 per node
(`SharedLeaves.cost` 6·stepC+65, node bound 68); still far below `CYCLE_LIMIT`. -/
theorem signCost_lt : signCost+1<CYCLE_LIMIT := by decide +kernel

theorem initialState_paired (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    initialState Paired.submission .sign (sk,cache,msg)=some (sinit sk cache msg) := by
  exact initialState_of_wsub submission.image Paired.submission_sign_valid submission_sign_valid
    sk cache msg (initialState_sign sk cache msg)

theorem sign_refines (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> Paired.submission.run .sign (sk,cache,msg)=
      (fun p=>(p.1.map sigBC,p.2.1,p.2.2)) <$>
        countBoth (mrealize sk (SigGolfCandidate.Research.SharedForest.sign (cacheDec cache) msg)) := by
  exact runtime_refines (imgs:=submission.image) (Nat.lt_of_succ_lt signCost_lt) _ sk cache msg
    (initialState_paired sk cache msg) (sign_tbsim sk cache msg)

theorem sign_terminates (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    (Paired.submission.runWith hash .sign (sk,cache,msg)).finished=true ∧
      (Paired.submission.runWith hash .sign (sk,cache,msg)).cycles<CYCLE_LIMIT := by
  exact runtime_terminates (imgs:=submission.image) signCost_lt _ hash sk cache msg
    (initialState_paired sk cache msg) (sign_tbsim sk cache msg)
#print axioms initialState_paired
#print axioms sign_refines
#print axioms sign_terminates
end ClaudeWCT.W9.Machine.Sign.SharedController
