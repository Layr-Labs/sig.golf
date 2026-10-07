import SigGolfCandidate.W9Drv.FtsJumpTable

section







section
set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def coordDispatch (p ld cpos fsh coord : Nat) (advance : Bool) : Result :=
  let dig : E := if coord ≥ 7 then .reg .x17 else if ld ≠ 0 then .ld (.c (BitVec.ofNat 64 ld)) else .reg .x16
  let child : E := if cpos = 0 then mkBin .and dig (.c 127)
    else if cpos = 57 then mkBin .srl dig (.c (BitVec.ofNat 64 57))
    else mkBin .and (mkBin .srl dig (.c (BitVec.ofNat 64 cpos))) (.c 127)
  let pre := if advance then mkAdd (.reg .x15) (.reg .x6) else .reg .x15
  let packed := mkBin .or (mkBin .sll child (.c 20)) pre
  let childPc := mkAdd (mkBin .sll child (.c 8)) (.reg .x29)
  let hb := if advance then mkAdd (.reg .x28) (.reg .x6) else .c (BitVec.ofNat 64 1537)
  let field := mkAdd (mkBin .and
    (mkBin .srl dig (.c (BitVec.ofNat 64 fsh))) (if advance then .reg .x2 else addC (.reg .x6) (BitVec.ofNat 64 (2^64-4)))) (.reg .x24)
  let n := (if ld ≠ 0 then 1 else 0) + (if cpos = 0 ∨ cpos = 57 then 1 else 2) + (if advance then 13 else 11)
  let regs := if ld ≠ 0 then RegFile.init.set .x16 dig else RegFile.init
  let regs := if advance then regs else regs.set .x2 (addC (.reg .x6) (BitVec.ofNat 64 (2^64-4)))
  let regs := regs.set .x4 child
  let regs := if advance then regs.set .x15 pre else regs
  let regs := (regs.set .x31 packed).set .x23 childPc
  let regs := if advance then (regs.set .x8 (addC (.reg .x8) 896)).set .x28 hb else regs.set .x28 hb
  let node := if advance then mkAdd (.reg .x27) (.reg .x6) else mkBin .or (.reg .x27) (.reg .x28)
  let regs := (((regs.set .x27 node).set
    .x14 field).set .x9 (if advance then addC (.reg .x9) 32 else .reg .x9)).set
    .x1 (.c (pcOf (p + n)))
  ⟨⟨regs, [], []⟩, mkBin .and field (.c (~~~1#64)), .jump, n, n⟩
end W9Machine
end
section
namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWordsN (k : Nat) : List (BitVec 32) :=[[4290969875,133722643,21110675,16773043,8526739,31165363,30272947,1611664915,5789459,2586419,25626419,458983],[8402947,133722643,6784947,21110675,16773043,8526739,31165363,939787283,7212595,7179699,5789459,2586419,25626419,33850515,458983],[22565395,133329427,6784947,21110675,16773043,8526739,31165363,939787283,7212595,7179699,27809555,2586419,25626419,33850515,458983],[60314131,6784947,21110675,16773043,8526739,31165363,939787283,7212595,7179699,43538195,2586419,25626419,33850515,458983],[16791555,133722643,6784947,21110675,16773043,8526739,31165363,939787283,7212595,7179699,5789459,2586419,25626419,33850515,458983],[22565395,133329427,6784947,21110675,16773043,8526739,31165363,939787283,7212595,7179699,27809555,2586419,25626419,33850515,458983],[60314131,6784947,21110675,16773043,8526739,31165363,939787283,7212595,7179699,43538195,2586419,25626419,33850515,458983],[133755411,6784947,21110675,16773043,8526739,31165363,939787283,7212595,7179699,5822227,2586419,25626419,33850515,458983],[22598163,133329427,6784947,21110675,16773043,8526739,31165363,939787283,7212595,7179699,27842323,2586419,25626419,33850515,458983]].getD k []
def digWord (k : Nat) : Nat := [0,1,1,1,2,2,2,3,3].getD k 0
def ldOf (k : Nat) : Nat := [0,8,0,0,16,0,0,0,0].getD k 0
def cposOf (k : Nat) : Nat := [0,0,21,57,0,21,57,0,21].getD k 0
def fshOf (k : Nat) : Nat := [5,5,26,41,5,26,41,5,26].getD k 0
def dispatchLenN (k : Nat) : Nat := [12,15,15,14,15,15,14,14,15].getD k 0
def dispatchResultN (k : Nat) : Result :=
  coordDispatch (dispatchPc k) (ldOf k) (cposOf k) (fshOf k) k (decide (k ≠ 0))
theorem dispatch_all_checked : (List.range 9).all (fun k =>
    rOK (symRun {} (dispatchWordsN k) (pcOf (dispatchPc k)) (dispatchLenN k)) (dispatchResultN k)) = true := by
  decide +kernel
theorem dispatch_all_linked : (List.range 9).all (fun k => sliceChecked (dispatchPc k) (dispatchWordsN k)) = true := by
  decide +kernel
end W9Drv
end
section
namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchCode (k : Fin 9) : List (BitVec 32) := dispatchWordsN k.val
def dispatchLen (k : Fin 9) : Nat := dispatchLenN k.val
def dispatchResult (k : Fin 9) : Result := dispatchResultN k.val
theorem dispatch_checked (k : Fin 9) :
    rOK (symRun {} (dispatchCode k) (pcOf (dispatchPc k.val)) (dispatchLen k))
      (dispatchResult k) = true :=
  List.all_eq_true.mp dispatch_all_checked k.val (List.mem_range.mpr k.isLt)
theorem dispatch_linked (k : Fin 9) :
    sliceChecked (dispatchPc k.val) (dispatchCode k) = true :=
  List.all_eq_true.mp dispatch_all_linked k.val (List.mem_range.mpr k.isLt)
theorem dispatch_mem (k : Fin 9) (u : MachineState) (A : Word) :
    ((dispatchResult k).toState u).getMem A = u.getMem A := by
  fin_cases k <;> rfl
theorem dispatch_steps (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    Steps Frozen.image u (dispatchLen k) (dispatchLen k) ((dispatchResult k).toState u) := by
  have hs := symRun_sound (rOK_eq (dispatch_checked k))
    (slice_at _ _ (dispatch_linked k)) u hu.pc
  have hcost : (dispatchResult k).steps = dispatchLen k ∧
      (dispatchResult k).cycles = dispatchLen k := by
    fin_cases k <;> exact ⟨rfl, rfl⟩
  rw [hcost.1, hcost.2] at hs
  apply hs
  change Oblig.all u (dispatchResult k).st.obl
  rw [Oblig.all_iff]
  intro o ho
  have hobl : (dispatchResult k).st.obl = [] := by
    fin_cases k <;> rfl
  rw [hobl] at ho
  simp at ho
end W9Drv
end
section
set_option maxRecDepth 10000
namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def chainEntryState (a : HashOutput) (k : Fin 9) (u : MachineState) : MachineState :=
  { (dispatchResult k).toState u with
    pc := pcOf (Frozen.layout.chainWord (N600.embed (ClaudeWCT.WCT9.rank a k))) }
theorem nat_and127 (n : Nat) : n &&& 127 = n % 128 := by
  have h := Nat.and_two_pow_sub_one_eq_mod n 7
  simpa using h
def childOfWord (k : Fin 9) (x : Word) : Word :=
  if cposOf k.val = 0 then x &&& 127#64 else if cposOf k.val = 57 then x >>> 57
  else (x >>> cposOf k.val) &&& 127#64
theorem dispatch_child (a : HashOutput) (k : Fin 9) :
    childOfWord k (a.extractLsb' (64 * digWord k.val) 64) =
      BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  apply BitVec.eq_of_toNat_eq
  fin_cases k <;> simp [childOfWord, cposOf, digWord, ClaudeWCT.WCT9.child, ClaudeWCT.WCT9.childBase,
    BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    nat_and127, BitVec.toNat_ofNat] <;> omega
def dispatchDig (k : Fin 9) : E :=
  if k.val ≥ 7 then .reg .x17 else
  if ldOf k.val ≠ 0 then .ld (.c (BitVec.ofNat 64 (ldOf k.val))) else .reg .x16
theorem dispatchDig_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    (dispatchDig k).eval u = a.extractLsb' (64 * digWord k.val) 64 := by
  have hd := hu.digest (digWord k.val) (by fin_cases k <;> decide)
  fin_cases k <;> first | exact hd | exact hu.cached | exact hu.cached3
def dispatchChild (k : Fin 9) : E :=
  if cposOf k.val = 0 then mkBin .and (dispatchDig k) (.c 127)
  else if cposOf k.val = 57 then mkBin .srl (dispatchDig k) (.c (BitVec.ofNat 64 57))
  else mkBin .and (mkBin .srl (dispatchDig k) (.c (BitVec.ofNat 64 (cposOf k.val)))) (.c 127)
theorem dispatchChild_eval (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    (dispatchChild k).eval u = BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  have hd := dispatchDig_eval pk w a k pairs u hu
  rw [← dispatch_child a k, ← hd]
  fin_cases k <;> rfl
theorem dispatch_keep (k : Fin 9) (u : MachineState) (r : Reg)
    (hr : r ∉ [.x1,.x2,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
    ((dispatchResult k).toState u).getReg r = u.getReg r := by
  rw [Result.toState_getReg]
  fin_cases k <;> cases r <;> first | exact False.elim (hr (by decide)) | rfl
theorem dispatch_childReg (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x4 = (dispatchChild k).eval u := by
  fin_cases k <;> rfl
theorem dispatch_childPC (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x23 =
      ((dispatchChild k).eval u <<< 8) + u.getReg .x29 := by
  fin_cases k <;> rfl
theorem dispatch_prefix (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x31 =
      ((dispatchChild k).eval u <<< 20) |||
        (if k.val = 0 then u.getReg .x15 else u.getReg .x15 + u.getReg .x6) := by
  fin_cases k <;> rfl
theorem packedPrefix_eval (i k j : Nat) (hk : k < 9) :
    (BitVec.ofNat 64 j <<< 20) ||| BitVec.ofNat 64 (i*2^27 + 65536*k) =
      BitVec.ofNat 64 (V3.chainPrefix i k j) := by
  have hc : 65536*k < 2^27 := by omega
  have hp : i*2^27 + 65536*k = (i <<< 27) ||| (k <<< 16) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa [Nat.shiftLeft_eq, Nat.mul_comm] using hc)]
    simp [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [hp, BitVec.ofNat_or]
  have hs (x n : Nat) : BitVec.ofNat 64 x <<< n = BitVec.ofNat 64 (x <<< n) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]
  rw [hs, ← BitVec.ofNat_or, ← BitVec.ofNat_or]
  unfold V3.chainPrefix
  rw [Nat.or_comm]
theorem nodeLow_step (k : Nat) (hk : k < 8) (index : Nat) :
    BitVec.ofNat 64 (V3.nodeLow k index) + 65536 = BitVec.ofNat 64 (V3.nodeLow (k + 1) index) := by
  have h1 := nodeLow_add ⟨k, by omega⟩ index
  have h2 := nodeLow_add ⟨k + 1, by omega⟩ index
  simp only [Fin.val_mk] at h1 h2
  rw [h1, h2, show (65536 : BitVec 64) = BitVec.ofNat 64 65536 from rfl, ← BitVec.ofNat_add]
  congr 1
  omega
theorem dispatch_x28 (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    ((dispatchResult k).toState u).getReg .x28 = BitVec.ofNat 64 (1537 + 65536 * k.val) := by
  by_cases hk0 : k.val = 0
  · have hkz : k = 0 := Fin.ext hk0
    subst hkz
    rfl
  · have he : ((dispatchResult k).toState u).getReg .x28 = u.getReg .x28 + u.getReg .x6 := by
      fin_cases k <;> first | exact absurd rfl hk0 | rfl
    rw [he, hu.headerReg hk0, hu.coordStep, show (65536 : BitVec 64) = BitVec.ofNat 64 65536 from rfl,
      ← BitVec.ofNat_add]
    congr 1
    omega
theorem dispatch_chain_pre (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    N600.Pre Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k) (ClaudeWCT.WCT9.rank a k)
      (chainEntryState a k u) := by
  have hm (A : Word) : (chainEntryState a k u).getMem A = u.getMem A := rfl
  have hr (r : Reg) (h : r ∉ [.x1,.x2,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hc := dispatchChild_eval pk w a k pairs u hu
  have hi : idxOf a < 2^31 := Nat.mod_lt _ (by decide)
  have hj := (ClaudeWCT.WCT9.child a k).isLt
  refine {
    indexBound := hi
    pc := rfl
    baseReg := ?_
    headerReg := ?_
    prefixReg := ?_
    childReg := ?_
    hashMode := (hr .x5 (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
    stepOne := (hr .x7 (by decide)).trans hu.stepOne
    stepTwo := (hr .x13 (by decide)).trans hu.stepTwo
    hashLen := (hr .x11 (by decide)).trans hu.hashLen
    childPC := ?_
    returnPC := ?_
    indexReg := (hr .x22 (by decide)).trans hu.index
    nodeHeader := ?_
    forestPointer := ?_
    heaps := ?_
    witness := by
      intro off ho h8
      have hw := hu.coords k (Nat.le_refl _) off ho h8
      rw [hm]
      simpa only [W9Machine.OrigW, Chain.base, coordinateBase, V3.regionOffset,
        show 2112 + 896*k.val + off - 2048 = 64 + 896*k.val + off by omega] using hw }
  · change ((dispatchResult k).toState u).getReg .x8 = _
    fin_cases k <;> simp [dispatchResult, dispatchResultN, coordDispatch, ldOf, cposOf, fshOf, dispatchPc,
      Result.toState_getReg, RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, hu.baseReg, Chain.base,
      coordinateBase]
  · change ((dispatchResult k).toState u).getReg .x28 = _
    rw [dispatch_x28 pk w a k pairs u hu, header_lo, if_neg (by decide)]
    rw [hdr0_eq 6 k.val (idxOf a) 0 (by decide) (by have := k.isLt; omega)
      (by omega) (by decide)]
    congr 1 <;> omega
  · change ((dispatchResult k).toState u).getReg .x31 = _
    rw [dispatch_prefix, hc, hu.prefixReg, hu.coordStep]
    have he : (if k.val = 0 then BitVec.ofNat 64 (idxOf a*2^27+65536*(k.val-1))
        else BitVec.ofNat 64 (idxOf a*2^27+65536*(k.val-1)) + 65536) =
        BitVec.ofNat 64 (idxOf a*2^27+65536*k.val) := by
      fin_cases k <;> simp [← BitVec.ofNat_add, Nat.add_assoc]
    rw [he]
    exact packedPrefix_eval _ _ _ k.isLt
  · change ((dispatchResult k).toState u).getReg .x4 = _
    rw [dispatch_childReg, hc]
  · change ((dispatchResult k).toState u).getReg .x23 = _
    rw [dispatch_childPC, hc, hu.childBlock]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Frozen.layout, pcOf]
    omega
  · change ((dispatchResult k).toState u).getReg .x1 = _
    fin_cases k <;> rfl
  · change ((dispatchResult k).toState u).getReg .x27 = _
    by_cases hk0 : k.val = 0
    · have hkz : k = 0 := Fin.ext hk0
      subst hkz
      have he : ((dispatchResult 0).toState u).getReg .x27 =
          BitVec.ofNat 64 (1+3*256+(4+(0 : Fin 9).val)*65536) ||| BitVec.ofNat 64 (idxOf a*2^32) := by
        have h27 : ((dispatchResult 0).toState u).getReg .x27 = u.getReg .x27 ||| u.getReg .x28 := rfl
        rw [h27, hu.nodeZero rfl, hu.headerZero rfl]
        all_goals rfl
      rw [he, nodeLow_add]
      rw [BitVec.or_comm, ofNat_or_disjoint _ _ 32 (by simp) (by simp)]
      rw [Nat.add_comm]
    · have he : ((dispatchResult k).toState u).getReg .x27 = u.getReg .x27 + u.getReg .x6 := by
        fin_cases k <;> first | exact absurd rfl hk0 | rfl
      rw [he, hu.nodeReg hk0, hu.coordStep]
      have hs := nodeLow_step (k.val - 1) (by have := k.isLt; omega) (idxOf a)
      rwa [show k.val - 1 + 1 = k.val by omega] at hs
  · change ((dispatchResult k).toState u).getReg .x9 = _
    fin_cases k <;> simp [dispatchResult, dispatchResultN, coordDispatch, ldOf, cposOf, fshOf, dispatchPc,
      Result.toState_getReg, RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval,
      hu.forestPointer, pairAddress, forestInputAddress, ← BitVec.ofNat_add]
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hu.heaps h h2 h7)
end W9Drv
end
section
namespace W9Drv
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
theorem aligned_clear_low (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0
    simp
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]
    simp [h]
  · simp [h0, hj]
theorem field_mask (x : BitVec 64) :
    x &&& 65532#64 = ((x >>> 2) &&& 16383#64) <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp
theorem dispatch_field (a : HashOutput) (k : Fin 9) :
    (a.extractLsb' (64 * digWord k.val) 64 >>> fshOf k.val) &&&
      65532#64 = BitVec.ofNat 64 (4 * ClaudeWCT.WCT9.field a k) := by
  rw [field_mask]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (_ &&& (2 ^ 14 - 1)) * 4 % 2 ^ 64 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  fin_cases k <;> simp [digWord, fshOf, ClaudeWCT.WCT9.field, ClaudeWCT.WCT9.fieldBase,
    BitVec.toNat_ofNat] <;> omega
theorem dispatch_mask (k : Fin 9) (u : MachineState)
    (hmask : u.getReg .x2 = BitVec.ofNat 64 (if k.val = 0 then 0xffbde0 else 0xfffc))
    (h6 : u.getReg .x6 = 65536) :
    ((dispatchResult k).toState u).getReg .x2 = 0xfffc := by
  fin_cases k
  · change u.getReg .x6 + BitVec.ofNat 64 (2^64-4) = _
    rw [h6]
    rfl
  all_goals exact hmask
theorem dispatch_pc (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    ((dispatchResult k).toState u).pc = pcOf (jtStart + ClaudeWCT.WCT9.field a k) := by
  have he : ((dispatchResult k).toState u).pc =
      (mkBin .and (mkAdd (mkBin .and
    (mkBin .srl (dispatchDig k)
      (.c (BitVec.ofNat 64 (fshOf k.val)))) (if k.val = 0 then addC (.reg .x6) (BitVec.ofNat 64 (2^64-4)) else .reg .x2)) (.reg .x24))
      (.c (~~~1#64))).eval u := by
    fin_cases k <;> rfl
  rw [he]
  have hmask : (if k.val = 0 then addC (.reg .x6) (BitVec.ofNat 64 (2^64-4)) else .reg .x2).eval u = 65532 := by
    by_cases hk0 : k.val = 0
    · simp [hk0, addC_eval, E.eval, hu.coordStep]
    · simp [hk0, E.eval, hu.mask]
  simp only [mkBin_eval, mkAdd_eval, E.eval, BinOp.eval, hu.jt]
  rw [hmask, dispatchDig_eval pk w a k roots u hu]
  have hshift : (BitVec.ofNat 64 (fshOf k.val)).toNat % 64 = fshOf k.val := by fin_cases k <;> decide
  rw [hshift]
  change (((a.extractLsb' (64 * digWord k.val) 64 >>> fshOf k.val) &&& 65532#64) + 878592#64) &&& ~~~1#64 = _
  rw [dispatch_field a k]
  rw [ofNat_add_ofNat, aligned_clear_low _ (by omega)]
  congr 1
  unfold jtStart
  omega
theorem codeAt_single (pc : Nat) (words : List (BitVec 32))
    (hb : pc + words.length < 242393)
    (hc : CodeAt Frozen.image (pcOf pc) words) (i : Nat) (hi : i < words.length) :
    CodeAt Frozen.image (pcOf (pc + i)) [words[i]] := by
  have hp : (pcOf pc).toNat = 4096 + 4 * pc := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  have hpi : (pcOf (pc + i)).toNat = 4096 + 4 * (pc + i) := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  refine ⟨by rw [hpi]; omega, by rw [hpi]; omega, by rw [hpi]; simp; omega, ?_⟩
  have hpre := hc.2.2.2.drop i
  have hs : [words[i]] <+: words.drop i := by
    rw [List.singleton_prefix_iff_head?_eq_some]
    simp [List.head?_drop, hi]
  have ht := hs.trans hpre
  simpa [hp, hpi, List.drop_drop, Nat.add_comm] using ht
theorem jt_steps (field : Fin 16384) (u : MachineState)
    (hu : u.pc = pcOf (jtStart + field.val)) :
    Steps Frozen.image u 1 1 {u with pc := pcOf (jtTarget field.val)} := by
  let c : Fin 64 := ⟨field.val / 256, by omega⟩
  let i : Nat := field.val % 256
  have hi : i < (jtChunk c).length := by rw [jtChunk_length]; exact Nat.mod_lt _ (by decide)
  have he : 256 * c.val + i = field.val := by dsimp [c, i]; omega
  have hcode := codeAt_single (jtStart + 256 * c.val) (jtChunk c)
    (by rw [jtChunk_length]; have := c.isLt; unfold jtStart; omega)
    (jtChunk_linked c) i hi
  have hcheck := jtChunk_checked c
  unfold jtCheck at hcheck
  have hmem : ((jtChunk c)[i], i) ∈ (jtChunk c).zipIdx := by
    have hx := List.getElem_mem (l := (jtChunk c).zipIdx) (n := i) (by simpa using hi)
    simpa using hx
  have hrun := List.all_eq_true.mp hcheck _ hmem
  simp only at hrun
  rw [Nat.add_assoc, he] at hrun
  rw [Nat.add_assoc, he] at hcode
  have hs := symRun_sound (rOK_eq hrun) hcode u hu (by trivial)
  convert hs using 1
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> rfl
end W9Drv
end
section
set_option maxHeartbeats 400000
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open W9Machine
theorem coord_core_good (chains : N600.AllGood Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good Frozen.layout ⟨43, 100, 100 - ClaudeWCT.WCT9.childSave j.val⟩ j)
    (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 600)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : (Digest × Digest) → OracleComp HashSpec Obs)
    (hu : N600.Pre Frozen.layout w index k j rank u)
    (hnext : ∀ ends entry, Chain.Post Frozen.layout w index k j u ends entry →
      ∀ pair t, Child.Post Frozen.layout k entry pair t →
        GoodQFor Frozen.image t N C Q A (K (pair.left, pair.right))) :
    GoodQFor Frozen.image u (N + 132) (C + 189) Q (A + (N600.rankCost rank + (100 - ClaudeWCT.WCT9.childSave j.val)))
      (ccM (ClaudeWCT.W9.T3M.wctCoordP w index k j rank) K) := by
  rw [wctCoordP_split w index k j rank hu.indexBound, ccM_bind]
  have hcont (ends : List Digest) (entry : MachineState)
      (hp : Chain.Post Frozen.layout w index k j u ends entry) :
      GoodQFor Frozen.layout.image entry (N+43) (C+100) Q (A+(100 - ClaudeWCT.WCT9.childSave j.val))
        (ccM (coordTail w index k j ends) K) := by
    have hg := childs j w index k ends entry N C A Q
      (fun pair => K (pair.left, pair.right)) hp.child (hnext ends entry hp)
    rw [← childProgram_canonical w index k j ends hp.length hu.indexBound]
    simp only [ccM_bind, ccM_pure]
    exact hg
  have hc := chains rank w index k j u (N+43) (C+100) (A+(100 - ClaudeWCT.WCT9.childSave j.val)) Q
    (fun ends => ccM (coordTail w index k j ends) K) hu hcont
  convert hc using 1 <;> first | rfl | omega
end W9Drv
end
section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
theorem coord_frame (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9) (u entry t : MachineState)
    (ends : List Digest) (pair : V3.RootPair)
    (hp : Chain.Post Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : Child.Post Frozen.layout k entry pair t) :
    Frame u t (fun A => (coordinateBase k ≤ A ∧ A < coordinateBase k + 896) ∨
      (pairAddress k ≤ A ∧ A < pairAddress k + 48)) := by
  intro A hA hn
  rw [ht.frame A hA (by unfold Child.writes; dsimp at hn; omega)]
  exact hp.frame A hA (by unfold Chain.writes Chain.base; dsimp at hn; omega)
theorem coord_next (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u entry t : MachineState) (ends : List Digest)
    (pair : V3.RootPair) (hu : CoordPre pk w a k.val pairs u)
    (hp : Chain.Post Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : Child.Post Frozen.layout k entry pair t) :
    CoordPre pk w a (k.val+1) (pairs ++ [(pair.left,pair.right)]) t := by
  have hk := k.isLt
  have hc := dispatch_chain_pre pk w a k pairs u hu
  have hf := coord_frame w a k u entry t ends pair hp ht
  have hm (A : Nat) (hA : A < 2^64)
      (hs : A < 1056 ∨ (1360 ≤ A ∧ A < 2112) ∨
      (10176 ≤ A ∧ A < 0xffbe10) ∨ 0xffbf40 ≤ A) :
      t.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    apply hf A hA
    unfold coordinateBase pairAddress forestInputAddress
    omega
  have hr (r : Reg) (h : r ∉ [.x3,.x10,.x11,.x12,.x14,.x25]) :
      t.getReg r = (chainEntryState a k u).getReg r := by
    rw [ht.keep r (by
      simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false] at *
      tauto)]
    exact hp.keep r h
  have hd (r : Reg) (h : r ∉ [.x1,.x2,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hg : Glob baseK w pk t := by
    obtain ⟨hreg, hh, hpk, hz, hhalf, hdata⟩ := hu.glob
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact (hr .x5 (by decide)).trans ((hd .x5 (by decide)).trans (hreg (.x5, 0) (by simp [baseK])))
      · exact (hr .x18 (by decide)).trans ((hd .x18 (by decide)).trans (hreg (.x18, 4095) (by simp [baseK])))
    · intro j hj
      rw [hm _ (by simp only [WIT, WX] at *; omega) (by simp only [WIT, WX] at *; omega)]
      exact hh j hj
    · exact ⟨(hm 160 (by decide) (by omega)).trans hpk.1,
        (hm 168 (by decide) (by omega)).trans hpk.2⟩
    · intro A hA
      have hb : A < 1056 := by simp [pSlots] at hA; omega
      exact (hm A (by omega) (Or.inl hb)).trans (hz A hA)
    · change (t.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hm CTRW (by decide) (Or.inl (by decide))]
      exact hhalf
    · refine ⟨?_, ?_⟩
      · exact (hm _ (by unfold TOPBASE; omega) (by unfold TOPBASE; omega)).trans hdata.mask
      · intro lay hl
        exact (hm _ (by unfold HDATA; omega) (by unfold HDATA; omega)).trans (hdata.header lay hl)
  refine {
    le := by omega
    length := by simp [hu.length]
    pc := ?_
    glob := hg
    digest := fun i hi => (hm _ (by omega) (Or.inl (by omega))).trans (hu.digest i hi)
    bank := ?_
    index := (hr .x22 (by decide)).trans hc.indexReg
    heaps := ?_
    stepOne := (hr .x7 (by decide)).trans hc.stepOne
    stepTwo := (hr .x13 (by decide)).trans hc.stepTwo
    hashLen := ht.hashLen
    coordStep := (hr .x6 (by decide)).trans ((hd .x6 (by decide)).trans hu.coordStep)
    prefixReg := ?_
    cached3 := (hr .x17 (by decide)).trans ((hd .x17 (by decide)).trans hu.cached3)
    cached := ?_
    nodeReg := fun _ => by
      rw [show k.val + 1 - 1 = k.val by omega]
      exact (hr .x27 (by decide)).trans hc.nodeHeader
    nodeZero := fun h => absurd h (by omega)
    headerZero := fun h => absurd h (by omega)
    zero := ⟨(hm 1024 (by decide) (Or.inl (by omega))).trans hu.zero.1,
      (hm 1032 (by decide) (Or.inl (by omega))).trans hu.zero.2⟩
    mask := by
      simpa using (hr .x2 (by decide)).trans (dispatch_mask k u hu.mask hu.coordStep)
    forestPointer := (hr .x9 (by decide)).trans hc.forestPointer
    jt := (hr .x24 (by decide)).trans ((hd .x24 (by decide)).trans hu.jt)
    childBlock := (hr .x29 (by decide)).trans ((hd .x29 (by decide)).trans hu.childBlock)
    baseReg := by simpa [Chain.base, coordinateBase] using (hr .x8 (by decide)).trans hc.baseReg
    headerReg := fun _ => by
      rw [hr .x28 (by decide), show k.val + 1 - 1 = k.val by omega]
      exact dispatch_x28 pk w a k pairs u hu
    pairs := ?_
    coords := ?_
    layer := ?_ }
  · rw [ht.pc]
    fin_cases k <;> rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hm _ (by omega) (by omega)).trans hu.bank.node
    · intro i hi
      exact (hm _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)).trans
        (hu.bank.top i hi)
    · exact (hm _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)).trans hu.bank.top8
    · intro j hj
      exact (hm _ (by omega) (by omega)).trans (hu.bank.forest j hj)
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hc.heaps h h2 h7)
  · rw [hr .x15 (by decide)]
    change ((dispatchResult k).toState u).getReg .x15 = _
    fin_cases k <;> simp [dispatchResult, dispatchResultN, coordDispatch, ldOf, cposOf, fshOf, dispatchPc,
      Result.toState_getReg, RegFile.get, RegFile.set, RegFile.init, mkAdd_eval, E.eval, hu.prefixReg, hu.coordStep,
      ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hr .x16 (by decide)]
    have hd1 := hu.digest 1 (by decide)
    have hd2 := hu.digest 2 (by decide)
    have hcache := hu.cached
    fin_cases k <;> first | exact hcache | exact hd1 | exact hd2
  · intro i hi
    by_cases he : i = k.val
    · subst i
      rw [List.getD_append_right _ _ _ _ (by rw [hu.length]), hu.length, Nat.sub_self]
      exact ⟨ht.left, ht.right⟩
    · rw [List.getD_append _ _ _ _ (by rw [hu.length]; omega)]
      have old := hu.pairs i (by omega)
      refine ⟨digAt_of_eq old.1 ?_ ?_, digAt_of_eq old.2 ?_ ?_⟩
      all_goals apply hf _ (by omega); unfold coordinateBase pairAddress forestInputAddress; omega
  · intro l hl off hoff halign
    unfold W9Machine.OrigW
    rw [hf _ (by have := l.isLt; unfold coordinateBase; omega) (by
      have := l.isLt
      unfold coordinateBase pairAddress forestInputAddress
      omega)]
    exact hu.coords l (by omega) off hoff halign
  · exact hu.layer.frame (fun j hj h => hm _ (by simp only [WIT, WX] at *; omega)
      (by simp only [WIT, WX] at *; omega))
theorem coord_good (chains : N600.AllGood Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good Frozen.layout ⟨43, 100, 100 - ClaudeWCT.WCT9.childSave j.val⟩ j) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (k : Fin 9) (roots : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Option (List (Digest × Digest)) → OracleComp HashSpec Obs)
    (hu : CoordPre pk w a k.val roots u) (hnone : K none = pure (false, 0))
    (hnext : ∀ root t, CoordPre pk w a (k.val + 1) (roots ++ [root]) t →
      GoodQFor Frozen.image t N C Q A (K (some (roots ++ [root])))) :
    GoodQFor Frozen.image u (N + (dispatchLen k + 190))
      (C + (dispatchLen k + 190)) Q (A + ((dispatchLen k + 98) + (N600.rankCost (ClaudeWCT.WCT9.rank a k) +
        ClaudeWCT.WCT9.childExtra (ClaudeWCT.WCT9.child a k))))
      (ccM (ClaudeWCT.W9.T3M.wctStep w a (some roots) k) K) := by
  have ds := dispatch_steps pk w a k roots u hu
  let f : Fin 16384 := ⟨ClaudeWCT.WCT9.field a k, Nat.mod_lt _ (by decide)⟩
  have js := jt_steps f ((dispatchResult k).toState u) (dispatch_pc pk w a k roots u hu)
  by_cases hok : ClaudeWCT.W9.T3M.fieldOk a k = true
  · have hfield : ClaudeWCT.WCT9.field a k < 16200 := by
      exact of_decide_eq_true hok
    have he : jtTarget f.val = Frozen.layout.chainWord (N600.embed (ClaudeWCT.WCT9.rank a k)) := by
      simp only [jtTarget, f, if_pos hfield, ClaudeWCT.WCT9.rank]
    rw [he] at js
    change Steps Frozen.image ((dispatchResult k).toState u) 1 1 (chainEntryState a k u) at js
    have core := coord_core_good chains childs w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (ClaudeWCT.WCT9.rank a k) (chainEntryState a k u) N C A Q
      (fun root => K (some (roots ++ [root]))) (dispatch_chain_pre pk w a k roots u hu)
      (fun ends entry hp pair t ht => hnext _ _ (coord_next pk w a k roots u entry t ends pair hu hp ht))
    have full := (core.steps js).steps ds
    have hce := ClaudeWCT.WCT9.childExtra_add (ClaudeWCT.WCT9.child a k)
    have hmx : ClaudeWCT.WCT9.maxChildSave = 3 := rfl
    simp only [ClaudeWCT.W9.T3M.wctStep, hok, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, ccM_bind, ccM_pure]
    exact full.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
  · have hfield : ¬ ClaudeWCT.WCT9.field a k < 16200 := by
      intro hh
      exact hok (show decide (ClaudeWCT.WCT9.field a k < 16200) = true from decide_eq_true hh)
    have he : jtTarget f.val = 32792 := by simp only [jtTarget, f, if_neg hfield, jtReject]
    rw [he] at js
    let s : MachineState := { (dispatchResult k).toState u with pc := pcOf 32792 }
    have rs := block_steps gReject_checked gReject_linked rfl s (by rfl)
    have rf := block_ecall gReject_checked gReject_linked rfl s rfl
    have rr : GoodQFor Frozen.image (gReject.toState s) 1 1 Q 0 (pure (false, 0)) :=
      GoodQFor.reject rf rfl rfl
    have full := ((rr.steps rs).steps js).steps ds
    dsimp only [gReject] at full
    have hfalse : ClaudeWCT.W9.T3M.fieldOk a k = false := Bool.eq_false_iff.mpr hok
    simp only [ClaudeWCT.W9.T3M.wctStep, hfalse, Bool.not_false, ↓reduceIte, ccM_pure, hnone]
    exact full.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
end W9Drv
end
end

section





section
namespace W9Drv
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64 W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def fPrepWords : List (BitVec 32) := [16761015,3781211171,3741353235,335545747,268437011,115]
def fTailWords : List (BitVec 32) := []
def gpE : E := .bin .add (.reg .x18) (.c (BitVec.ofNat 64 (2 ^ 64 - 254)))
def fPrep : Result :=
  ⟨⟨(((RegFile.init.set .x1 (.c (BitVec.ofNat 64 0xffc000))).set .x10 (.c 0xffbdf0)).set
      .x11 (.c 320)).set .x12 (.c 256),
    [(⟨none, 0xffbe08⟩, .reg .x22)], []⟩, .c (pcOf 32970), .ecall, 5, 5⟩
def fTail : Result := ⟨SymState.init, .c (pcOf 32971), .fuel, 0, 0⟩
theorem fPrep_checked : rOK (symRun {} fPrepWords (pcOf 32965) 6) fPrep = true := by decide +kernel
theorem fPrep_linked : sliceChecked 32965 fPrepWords = true := by decide +kernel
theorem fTail_checked : rOK (symRun {} fTailWords (pcOf 32971) 0) fTail = true := by decide +kernel
theorem fTail_linked : sliceChecked 32971 fTailWords = true := by decide +kernel
end W9Drv
end
section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M HashInput pad64 shortHash)
open SphincsSecurity (bytesLE bytesLE_length)
open W9Machine
abbrev forestIn := ClaudeWCT.WCT9.forestInput
theorem forestIn_length (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (forestIn index pairs).length = 320 := by
  simp only [forestIn, ClaudeWCT.WCT9.forestInput, List.length_append, bytesLE_length,
    SigGolfCandidate.T3.zero16, List.length_replicate, List.length_flatMap]
  simp [h]
theorem wordsOf_forestIn (index : Nat) (pairs : List (Digest × Digest)) :
    wordsOf (forestIn index pairs) =
      [0, 0, BitVec.ofNat 64 (hdr0 15 0 index 0), BitVec.ofNat 64 (hdr1 index 0)] ++
        pairs.flatMap (fun p => [dlo p.1, dhi p.1, dlo p.2, dhi p.2]) := by
  unfold forestIn ClaudeWCT.WCT9.forestInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3.zero16]), wordsOf_append _ _ (by simp [SigGolfCandidate.T3.zero16]), wordsOf_header]
  have hp : ∀ ps : List (Digest × Digest),
      wordsOf (ps.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)) =
        ps.flatMap (fun p => [dlo p.1, dhi p.1, dlo p.2, dhi p.2]) := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.flatMap_cons]
      rw [wordsOf_append _ _ (by simp [bytesLE_length]),
        wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, ih]
      rfl
  rw [hp]
  rfl
theorem pad64_forestIn (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    pad64 (forestIn index pairs) = forestIn index pairs := by
  simp [pad64, forestIn_length index pairs h]
theorem blocks_forestIn (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (toQ (pad64 (forestIn index pairs))).blocks = 5 := by
  rw [pad64_forestIn index pairs h,
    blocks_toQ (by rw [Aligned, forestIn_length index pairs h]; omega), forestIn_length index pairs h]
theorem hdr0_forest15 (idx : Nat) (hi : idx < 2^32) : hdr0 15 0 idx 0 = 3841 := by
  rw [hdr0_eq 15 0 idx 0 (by decide) (by decide) hi (by decide)]; norm_num
theorem hdr1_forest15 (idx : Nat) (hi : idx < 2^32) : hdr1 idx 0 = idx := by
  unfold hdr1; rw [Nat.mod_eq_of_lt hi]; simp
theorem fPrep_mem (u : MachineState) (B : Nat) (hB : B < 2^64) :
    (fPrep.toState u).getMem (BitVec.ofNat 64 B) =
      if B = 0xffbe08 then u.getReg .x22 else u.getMem (BitVec.ofNat 64 B) := by
  rw [Result.toState_getMem]
  change memEval u [(⟨none, BitVec.ofNat 64 0xffbe08⟩, .reg .x22)] (BitVec.ofNat 64 B) = _
  rw [memEval_cons_ofNat _ _ _ _ _ hB (by norm_num), memEval_nil]
  rfl
theorem fPrep_frame (u : MachineState) (B : Nat) (hB : B < 2^64)
    (h : B ≠ 0xffbe08) :
    (fPrep.toState u).getMem (BitVec.ofNat 64 B) = u.getMem (BitVec.ofNat 64 B) := by
  rw [fPrep_mem u B hB, if_neg h]
theorem forest_words (u : MachineState) (idx : Nat) (pairs : List (Digest × Digest))
    (hlen : pairs.length = 9) (hi : idx < 2^31)
    (h22 : u.getReg .x22 = BitVec.ofNat 64 idx) (h18 : u.getReg .x18 = 0xFFF)
    (hz : u.getMem (BitVec.ofNat 64 0xffbdf0) = 0 ∧ u.getMem (BitVec.ofNat 64 0xffbdf8) = 0)
    (hheader : u.getMem (BitVec.ofNat 64 0xffbe00) = 3841)
    (hr : ∀ i, i < 9 → DigAt u (0xffbe10+32*i) (pairs.getD i (0,0)).1 ∧
      DigAt u (0xffbe10+32*i+16) (pairs.getD i (0,0)).2) :
    (fPrep.toState u).readWords (BitVec.ofNat 64 0xffbdf0) 40 =
      wordsOf (pad64 (forestIn idx pairs)) := by
  have hp : ∀ i, i < 9 → DigAt (fPrep.toState u) (0xffbe10+32*i) (pairs.getD i (0,0)).1 ∧
      DigAt (fPrep.toState u) (0xffbe10+32*i+16) (pairs.getD i (0,0)).2 := by
    intro i hi9
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).1.1
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).1.2
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).2.1
    · exact (fPrep_frame u _ (by omega) (by omega)).trans (hr i hi9).2.2
  rw [readWords_ofNat _ 0xffbdf0 40 (by norm_num), pad64_forestIn idx pairs hlen,
    wordsOf_forestIn, show List.range 40 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39] from rfl]
  match pairs, hlen, hp with
  | [p0,p1,p2,p3,p4,p5,p6,p7,p8], _, hp =>
    have d0 := hp 0 (by decide)
    have d1 := hp 1 (by decide)
    have d2 := hp 2 (by decide)
    have d3 := hp 3 (by decide)
    have d4 := hp 4 (by decide)
    have d5 := hp 5 (by decide)
    have d6 := hp 6 (by decide)
    have d7 := hp 7 (by decide)
    have d8 := hp 8 (by decide)
    norm_num [List.getD_cons_zero, List.getD_cons_succ] at d0 d1 d2 d3 d4 d5 d6 d7 d8
    have h16 : (fPrep.toState u).getMem (BitVec.ofNat 64 0xffbe00) =
        BitVec.ofNat 64 (hdr0 15 0 idx 0) := by
      rw [fPrep_frame u _ (by norm_num) (by norm_num), hdr0_forest15 idx (by omega)]
      exact hheader
    have h24 : (fPrep.toState u).getMem (BitVec.ofNat 64 0xffbe08) =
        BitVec.ofNat 64 (hdr1 idx 0) := by
      rw [fPrep_mem u _ (by norm_num), hdr1_forest15 idx (by omega)]; exact h22
    have z0 : (fPrep.toState u).getMem (BitVec.ofNat 64 0xffbdf0) = 0 :=
      (fPrep_frame u _ (by norm_num) (by omega)).trans hz.1
    have z1 : (fPrep.toState u).getMem (BitVec.ofNat 64 0xffbdf8) = 0 :=
      (fPrep_frame u _ (by norm_num) (by omega)).trans hz.2
    simp only [List.map_cons, List.map_nil, Nat.reduceMul, Nat.reduceAdd, d0.1.1, d0.1.2, d0.2.1, d0.2.2, d1.1.1, d1.1.2, d1.2.1, d1.2.2, d2.1.1, d2.1.2, d2.2.1, d2.2.2, d3.1.1, d3.1.2, d3.2.1, d3.2.2, d4.1.1, d4.1.2, d4.2.1, d4.2.2, d5.1.1, d5.1.2, d5.2.1, d5.2.2, d6.1.1, d6.1.2, d6.2.1, d6.2.2, d7.1.1, d7.1.2, d7.2.1, d7.2.2, d8.1.1, d8.1.2, d8.2.1, d8.2.2,
      h16, h24, z0, z1, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil]
theorem forest_good (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (roots : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs)
    (hu : CoordPre pk w a 9 roots u)
    (hnext : ∀ root t, FtsOut ⟨pk, w, a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K root)) :
    GoodQFor Frozen.image u (N + 6) (C + 45) Q (A + 45)
      (ccM (ClaudeWCT.WCT9.forestPk (idxOf a) roots) K) := by
  have hi : idxOf a < 2 ^ 31 := ClaudeWCT.WCT9.digestIndex_lt a
  have st1 := block_steps fPrep_checked fPrep_linked rfl u hu.pc
  have st1' : Steps Frozen.image u 5 5 (fPrep.toState u) := st1
  set s1 := fPrep.toState u with hs1
  have hf := block_ecall fPrep_checked fPrep_linked rfl u rfl
  have r1 : ∀ x, x ≠ .x3 → x ≠ .x10 → x ≠ .x11 → x ≠ .x12 → x ≠ .x1 → s1.getReg x = u.getReg x := by
    intro x h3 h10 h11 h12 h1
    rw [hs1, Result.toState_getReg]
    cases x <;> first | exact absurd rfl ‹_› | rfl
  have h5 : s1.getReg .x5 = 0 :=
    (r1 .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
  have h10 : s1.getReg .x10 = BitVec.ofNat 64 0xffbdf0 := by rw [hs1, Result.toState_getReg]; rfl
  have h11 : s1.getReg .x11 = BitVec.ofNat 64 (64 * (4 + 1)) := by rw [hs1, Result.toState_getReg]; rfl
  have h12 : s1.getReg .x12 = BitVec.ofNat 64 0x100 := by rw [hs1, Result.toState_getReg]; rfl
  have h22 : s1.getReg .x22 = BitVec.ofNat 64 (idxOf a) :=
    (r1 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu.index
  have hv : hashArgumentsValid s1 = true :=
    hashArgs_of s1 0xffbdf0 320 0x100 h10 h11 h12 (by decide) (by decide) (by norm_num) (by decide)
      (by norm_num)
  have hin : hashInput s1 = toQ (pad64 (forestIn (idxOf a) roots)) :=
    hashInput_toQ s1 _ 4 0xffbdf0 (by rw [pad64_forestIn _ _ hu.length, forestIn_length _ _ hu.length]) h10 (by decide) (by norm_num)
      h11 (by norm_num) (forest_words u (idxOf a) roots hu.length hi hu.index
        (hu.glob.1 (.x18, 0xFFF) (by simp [baseK]))
        ⟨by simpa using hu.bank.forest 0 (by decide), by simpa using hu.bank.forest 1 (by decide)⟩
        (by simpa using hu.bank.forest 2 (by decide)) hu.pairs)
  have g1 : Glob [] w pk s1 := by
    obtain ⟨-, hh, hpk, hz, hhalf, hdata⟩ := hu.glob
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      exact (fPrep_frame u _ (by simp only [WIT, WX] at *; omega) (by simp only [WIT, WX] at *; omega)).trans (hh j hj)
    · exact ⟨(fPrep_frame u _ (by norm_num) (by norm_num)).trans hpk.1,
        (fPrep_frame u _ (by norm_num) (by norm_num)).trans hpk.2⟩
    · intro A hA
      exact (fPrep_frame u _ (by simp [pSlots] at hA; omega)
        (by simp [pSlots] at hA; omega)).trans (hz A hA)
    · change ((fPrep.toState u).getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [fPrep_frame u CTRW (by unfold CTRW; omega) (by unfold CTRW; omega)]
      exact hhalf
    · refine ⟨?_, ?_⟩
      · exact (fPrep_frame u _ (by unfold TOPBASE; omega) (by unfold TOPBASE; omega)).trans hdata.mask
      · intro lay hl
        exact (fPrep_frame u _ (by unfold HDATA; omega) (by unfold HDATA; omega)).trans (hdata.header lay hl)
  have o1 : Orig w (fun o => o < 64 ∨ 8136 ≤ o) s1 :=
    hu.layer.frame (fun j hj _ => fPrep_frame u _ (by simp only [WIT, WX] at *; omega)
      (by simp only [WIT, WX] at *; omega))
  have hpost : ∀ ans : BitVec 256, GoodQFor Frozen.image (writeHash s1 ans) (N + 0) (C + 0) Q (A + 0)
      (ccM (pure (ans.extractLsb' 0 128) : M Digest) K) := by
    intro ans
    rw [ccM_pure]
    have hpc : (writeHash s1 ans).pc = pcOf 32971 := by
      rw [writeHash_pc]
      show pcOf 32970 + 4 = pcOf 32971
      exact SigGolfCandidate.T3M.pcOf_add4 32970
    have st2 := block_steps fTail_checked fTail_linked rfl (writeHash s1 ans) hpc
    have st2' : Steps Frozen.image (writeHash s1 ans) 0 0 (fTail.toState (writeHash s1 ans)) := st2
    set t := fTail.toState (writeHash s1 ans) with ht
    have mt : t.mem = (writeHash s1 ans).mem := toState_mem_nil _ _ rfl
    have et : ∀ A, t.getMem A = (writeHash s1 ans).getMem A := fun A => congrFun mt A
    have hout : FtsOut ⟨pk, w, a⟩ (ans.extractLsb' 0 128) t := by
      refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have gg := Glob_writeHash g1 ans 0x100 h12 (by decide)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · change (writeHash s1 ans).getReg .x5 = 0
            rw [writeHash_getReg]; exact h5
          · change (writeHash s1 ans).getReg .x18 = 4095
            rw [writeHash_getReg, r1 .x18 (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hu.glob.1 (.x18,4095) (by simp [baseK])
        · exact fun j hj => (et _).trans (gg.2.1 j hj)
        · exact ⟨(et _).trans gg.2.2.1.1, (et _).trans gg.2.2.1.2⟩
        · exact fun A hA => (et _).trans (gg.2.2.2.1 A hA)
        · change (t.getMem _).toNat / 2^32 = 0
          rw [et]; exact gg.2.2.2.2.1
        · exact gg.2.2.2.2.2.congr (fun A _ _ => et _)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x22 = _
        rw [writeHash_getReg]; exact h22
      · obtain ⟨e0, e1⟩ := writeHash_lo s1 ans 0x100 h12 (by norm_num)
        exact ⟨(et _).trans e0, (et _).trans e1⟩
      · have o2 := Orig_writeHash o1 ans 0x100 h12 (by norm_num)
        have o3 : Orig w (fun o => o < 64 ∨ 8136 ≤ o) (writeHash s1 ans) :=
          o2.mono (fun o ho => ⟨ho, Or.inr (by simp only [WIT, WX] at *; omega)⟩)
        exact o3.frame (fun j _ _ => et _)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x12 = _
        rw [writeHash_getReg]
        exact h12
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x26 = _
        rw [writeHash_getReg, r1 .x26 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 6 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x7 = _
        rw [writeHash_getReg, r1 .x7 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.stepOne
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x13 = _
        rw [writeHash_getReg, r1 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.stepTwo
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x30 = _
        rw [writeHash_getReg, r1 .x30 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 7 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x19 = _
        rw [writeHash_getReg, r1 .x19 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 3 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x20 = _
        rw [writeHash_getReg, r1 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 4 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x21 = _
        rw [writeHash_getReg, r1 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.heaps 5 (by decide) (by decide)
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x6 = _
        rw [writeHash_getReg, r1 .x6 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hu.coordStep
      · rw [ht, Result.toState_getReg]
        show (writeHash s1 ans).getReg .x1 = _
        rw [writeHash_getReg, hs1, Result.toState_getReg]
        rfl
      · intro k hk
        rw [et, writeHash_frame s1 ans 0x100 (TOPLOAD + 8 * k) h12
          (by unfold TOPLOAD; omega) (by norm_num) (Or.inr (by unfold TOPLOAD; omega))]
        exact (fPrep_frame u _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)).trans
          (hu.bank.top k hk)
      · rw [et, writeHash_frame s1 ans 0x100 (TOPLOAD - 8) h12
          (by unfold TOPLOAD; omega) (by norm_num) (Or.inr (by unfold TOPLOAD; omega))]
        exact (fPrep_frame u _ (by unfold TOPLOAD; omega) (by unfold TOPLOAD; omega)).trans
          hu.bank.top8
    exact (hnext _ t hout).steps st2'
  have hq := GoodQFor.shortHash_bind (f := fun d : Digest => (pure d : M Digest)) (K := K)
    hf h5 hv hin hpost
  rw [blocks_forestIn _ _ hu.length, bind_pure] at hq
  have := hq.steps st1'
  change GoodQFor Frozen.image u (N+6) (C+45) Q (A+45) (ccM (shortHash (forestIn (idxOf a) roots)) K)
  exact this.mono (by omega) (by omega) (fun hq => ⟨hq, by omega⟩)
end W9Drv
end
end

section




namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def FtsGoodByCost (acceptCost : HashOutput → Nat) : Prop :=
  ∀ (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs),
    GatePre pk w a u → K none = pure (false, 0) →
    (∀ root t, FtsOut ⟨pk,w,a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K (some root))) →
    GoodQFor Frozen.image u (N+2023) (C+2023) Q (A+acceptCost a)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a else pure none) K)
def ftsAcceptCost (a : HashOutput) : Nat := 1075 + ClaudeWCT.WCT9.jointCost a
end W9Drv
end

section



section
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open W9Machine
def finishFts (a : HashOutput) (state : Option (List (Digest × Digest))) : M (Option Digest) :=
  match state with
  | none => pure none
  | some roots => some <$> ClaudeWCT.WCT9.forestPk (idxOf a) roots
def coordsCost (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => dispatchLen k + 190)).sum
def coordsAccept (a : HashOutput) (ks : List (Fin 9)) : Nat :=
  (ks.map (fun k => (dispatchLen k + 98) + (N600.rankCost (ClaudeWCT.WCT9.rank a k) +
    ClaudeWCT.WCT9.childExtra (ClaudeWCT.WCT9.child a k)))).sum
theorem fold_none (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput) (ks : List (Fin 9)) :
    ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) none = pure none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [List.foldlM_cons, ClaudeWCT.W9.T3M.wctStep, pure_bind] using ih
theorem coordinates_good (chains : N600.AllGood Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good Frozen.layout ⟨43, 100, 100 - ClaudeWCT.WCT9.childSave j.val⟩ j) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (a : HashOutput)
    (ks : List (Fin 9)) (n : Nat) (roots : List (Digest × Digest)) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs)
    (horder : ks.map Fin.val = List.range' n ks.length) (hend : n + ks.length = 9)
    (hu : CoordPre pk w a n roots u) (hnone : K none = pure (false, 0))
    (hnext : ∀ root t, FtsOut ⟨pk,w,a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K (some root))) :
    GoodQFor Frozen.image u (N + (coordsCost ks + 45)) (C + (coordsCost ks + 45)) Q
      (A + (coordsAccept a ks + 45))
      (ccM (ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) (some roots) >>= finishFts a) K) := by
  induction ks generalizing n roots u with
  | nil =>
    have hn : n = 9 := by simpa using hend
    subst n
    simp only [List.foldlM_nil, pure_bind, finishFts]
    have hf := forest_good pk w a roots u N C A Q (fun root => K (some root)) hu hnext
    rw [map_eq_bind_pure_comp, ccM_bind]
    simp only [Function.comp_apply, ccM_pure]
    exact hf.mono (by change N + 6 ≤ N + 45; omega) (by rfl) (fun hq => ⟨hq, by rfl⟩)
  | cons k ks ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at horder
    obtain ⟨hn, ht⟩ := horder
    subst n
    let K' : Option (List (Digest × Digest)) → OracleComp HashSpec Obs := fun state =>
      ccM (ks.foldlM (ClaudeWCT.W9.T3M.wctStep w a) state >>= finishFts a) K
    have hkNone : K' none = pure (false, 0) := by
      simp only [K', fold_none, pure_bind, finishFts, ccM_pure, hnone]
    have hstep := coord_good chains childs pk w a k roots u (N + (coordsCost ks + 45))
      (C + (coordsCost ks + 45)) (A + (coordsAccept a ks + 45)) Q K' hu hkNone
      (fun root t hh => ih (k.val + 1) (roots ++ [root]) t ht (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hend) hh)
    simp only [List.foldlM_cons, bind_assoc, ccM_bind]
    convert hstep using 1 <;> simp [coordsCost, coordsAccept, Nat.add_left_comm, Nat.add_comm,
      K', ccM_bind] <;> omega
theorem coordsAccept_all (a : HashOutput) :
    coordsAccept a (List.finRange 9) = 1011 + ClaudeWCT.WCT9.jointCost a := by
  unfold coordsAccept
  rw [List.sum_map_add]
  have hfixed : ((List.finRange 9).map (fun k => dispatchLen k + 98)).sum = 1011 := by decide
  rw [hfixed]
  congr 1
  simp only [ClaudeWCT.WCT9.jointCost, ClaudeWCT.WCT9.coordCost,
    (show N600.rankCost = ClaudeWCT.WCT9.routineCost from N600.rankCost_eq_c1)]
theorem fts_good_of (chains : N600.AllGood Frozen.layout)
    (childs : ∀ j : Fin 128, Child.Good Frozen.layout ⟨43, 100, 100 - ClaudeWCT.WCT9.childSave j.val⟩ j) : FtsGoodByCost ftsAcceptCost := by
  intro pk w a u N C A Q K hu hnone hnext
  let KG : Bool → OracleComp HashSpec Obs := fun b =>
    if b then ccM (ClaudeWCT.W9.T3M.wctP w a) K else K none
  have hg := gate_good pk w a u (N + 1884) (C + 1884) (A + (1056 + ClaudeWCT.WCT9.jointCost a)) Q KG hu
    (by simpa only [KG, Bool.false_eq_true, ↓reduceIte] using hnone)
    (fun t ht => by
      have hc := coordinates_good chains childs pk w a (List.finRange 9) 0 [] t N C A Q K
        (by decide)
        (by simp) ht hnone hnext
      rw [show coordsCost (List.finRange 9) + 45 = 1884 by decide,
        show coordsAccept a (List.finRange 9) + 45 = 1056 + ClaudeWCT.WCT9.jointCost a by
          rw [coordsAccept_all]; omega] at hc
      apply hc.congr
      change ccM (_ >>= finishFts a) K = ccM (ClaudeWCT.W9.T3M.wctP w a) K
      apply congrArg (fun p : M (Option Digest) => ccM p K)
      unfold ClaudeWCT.W9.T3M.wctP
      apply congrArg (fun f : Option (List (Digest × Digest)) → M (Option Digest) =>
        (List.finRange 9).foldlM (ClaudeWCT.W9.T3M.wctStep w a) (some []) >>= f)
      funext state
      cases state <;> rfl)
  change GoodQFor Frozen.image u (N + 1903) (C + 1903) Q (A + (1056 + ClaudeWCT.WCT9.jointCost a) + 19)
    (KG (ClaudeWCT.W9.T3M.gateOk a)) at hg
  apply (hg.mono (by omega) (by omega) (fun hq => ⟨hq, by simp only [ftsAcceptCost]; omega⟩)).congr
  cases ClaudeWCT.W9.T3M.gateOk a <;> simp [KG, ccM_pure]
end W9Drv
end
end
