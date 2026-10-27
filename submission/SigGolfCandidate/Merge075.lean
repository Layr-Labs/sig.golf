import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge047
import SigGolfCandidate.Merge049
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge074

-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_Search ====
section

section
namespace ClaudeWCT.W9.Machine.Sign.SearchM
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
def cst (n : Nat) : E := .c (BitVec.ofNat 64 n)
def rfs (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def mw (a : Nat) (e : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, e)
def fsi (k : Nat) : Nat := sfIdx.getD k 0
def sci (k : Nat) : Nat := scIdx.getD k 0
def dw (k : Nat) : Nat := WCT9.childBase k / 64
def sh (k : Nat) : Nat := [0,0,21,36,0,21,36,0,21].getD k 0
def hasSh (k : Nat) : Bool := k % 3 != 1
def CBASE : Nat := 0xfef000
def resH153 : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 11003, false, 1, 1, [], none⟩
def resHead (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, cst (2 ^ 21)), (.x7, cst CBASE)], [], []⟩, if d then pcOf 11007 else pcOf 11172, false,
    if d then 3 else 4, if d then 3 else 4, [⟨.ltu, .reg .x19, cst (2 ^ 21), d⟩], none⟩
def ctrE : E := .bin .sll (.reg .x19) (cst 0)
def resTrial : PRes :=
  ⟨⟨rfs [(.x6, ctrE), (.x10, cst DIG), (.x11, cst 64), (.x12, cst NBUF), (.x28, cst DIG)],
    [mw (DIG + 24) ctrE, mw (DIG + 16) (cst 0)], []⟩, pcOf 11019, true, 12, 12, [], none⟩
def gateE : E := .bin .sltu (.bin .srl (.ld (cst (NBUF + 24))) (cst 50)) (cst 1353)
def resGate (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, gateE), (.x22, .ld (cst NBUF)), (.x28, cst NBUF)], [], []⟩,
    if d then pcOf 11170 else pcOf 11027, false, 7, 7, [⟨.eq, gateE, .c 0, d⟩], none⟩
def resCost0 : PRes := ⟨⟨rfs [(.x20, cst 0), (.x21, cst COST)], [], []⟩, pcOf (fsi 0), false, 3, 3, [], none⟩
def grpE (k : Nat) : E :=
  if hasSh k then .bin .srl (.ld (cst (NBUF + 8 * dw k))) (cst (sh k)) else .ld (cst (NBUF + 8 * dw k))
def childE (k : Nat) : E := if k = 3 ∨ k = 6 then .bin .srl (grpE k) (cst 21) else .bin .and (grpE k) (cst 127)
def fieldE (k : Nat) : E := .bin .srl (.bin .sll (grpE k) (cst 47)) (cst 54)
def fieldLen (k : Nat) : Nat := if hasSh k then 9 else 8
def resField (k : Nat) (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, cst 563), (.x24, childE k), (.x25, fieldE k), (.x28, cst 131072)], [], []⟩,
    if d then pcOf 11170 else pcOf (sci k), false, fieldLen k, fieldLen k,
    [⟨.geu, fieldE k, cst 563, d⟩], none⟩
def resSc1 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x6, .bin .add (.reg .x21) (.reg .x25))], [], []⟩, pcOf (sci k + 1), false, 1, 1, [], none⟩
def resSc3 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x20, .bin .add (.reg .x20) (.reg .x6))], [], []⟩, pcOf (sci k + 3), false, 1, 1, [], none⟩
def resCc1 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x6, .bin .add (.reg .x7) (.reg .x24))], [], []⟩, pcOf (sci k + 4), false, 1, 1, [], none⟩
def resCc3 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x20, .bin .add (.reg .x20) (.reg .x6))], [], []⟩, pcOf (fsi (k + 1)), false, 1, 1, [], none⟩
def capE : E := .bin .sltu (.reg .x20) (cst 790)
def resCap (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, capE)], [], []⟩, if d then pcOf 11170 else pcOf 11164, false, 2, 2, [⟨.eq, capE, .c 0, d⟩], none⟩
def idxE : E := .bin .srl (.bin .sll (.reg .x22) (cst 0)) (cst 33)
def resFinal : PRes :=
  ⟨⟨rfs [(.x22, idxE), (.x28, cst IDXV)], [mw IDXV idxE], []⟩, pcOf 11175, false, 6, 6, [], none⟩
def resNext : PRes :=
  ⟨⟨rfs [(.x19, .bin .add (.reg .x19) (cst 1))], [], []⟩, pcOf 11003, false, 2, 2, [], none⟩
def resFail : PRes :=
  ⟨⟨rfs [(.x5, cst 1), (.x10, cst 1)], [], []⟩, pcOf 11174, true, 2, 2, [], none⟩
theorem chk_h153 : optBeq (run hookLook [11003] 153 []) resH153 = true := by decide +kernel
theorem chk_head : (optBeq (run headLook [11007, 11172] 11003 [.br true]) (resHead true) &&
    optBeq (run headLook [11007, 11172] 11003 [.br false]) (resHead false)) = true := by decide +kernel
theorem chk_trial : optBeq (run headLook [] 11007 []) resTrial = true := by decide +kernel
theorem chk_gate : (optBeq (run headLook [11170, 11027] 11020 [.br true]) (resGate true) &&
    optBeq (run headLook [11170, 11027] 11020 [.br false]) (resGate false)) = true := by decide +kernel
theorem chk_cost0 : optBeq (run headLook [fsi 0] 11027 []) resCost0 = true := by decide +kernel
theorem chk_fields : (List.range 9).all (fun k =>
    optBeq (run headLook [11170, sci k] (fsi k) [.br true]) (resField k true) &&
    optBeq (run headLook [11170, sci k] (fsi k) [.br false]) (resField k false) &&
    optBeq (run headLook [sci k + 1] (sci k) []) (resSc1 k) &&
    optBeq (run headLook [sci k + 3] (sci k + 2) []) (resSc3 k) &&
    headLook (sci k + 1) == some 0x00034303) = true := by
  decide +kernel
theorem chk_childs : (List.range 9).all (fun k =>
    optBeq (run headLook [sci k + 4] (sci k + 3) []) (resCc1 k) &&
    optBeq (run headLook [fsi (k + 1)] (sci k + 5) []) (resCc3 k) &&
    headLook (sci k + 4) == some 0xf8034303) = true := by
  decide +kernel
theorem chk_cap : (optBeq (run headLook [11170, 11164] 11162 [.br true]) (resCap true) &&
    optBeq (run headLook [11170, 11164] 11162 [.br false]) (resCap false)) = true := by decide +kernel
theorem chk_final : optBeq (run headLook [11175] 11164 []) resFinal = true := by decide +kernel
theorem chk_next : optBeq (run headLook [11003] 11170 []) resNext = true := by decide +kernel
theorem chk_fail : optBeq (run headLook [] 11172 []) resFail = true := by decide +kernel
theorem fsi_nine : fsi 9 = 11162 := by decide +kernel
theorem sci_lt : ∀ k, k < 9 → sci k + 6 = fsi (k + 1) ∧ fsi k < sci k ∧ sci k + 5 < 11162 := by decide +kernel
theorem run_h153 : run hookLook [11003] 153 [] = some resH153 := optBeq_eq chk_h153
theorem run_head (d : Bool) : run headLook [11007, 11172] 11003 [.br d] = some (resHead d) := by
  have h := chk_head
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_trial : run headLook [] 11007 [] = some resTrial := optBeq_eq chk_trial
theorem run_gate (d : Bool) : run headLook [11170, 11027] 11020 [.br d] = some (resGate d) := by
  have h := chk_gate
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_cost0 : run headLook [fsi 0] 11027 [] = some resCost0 := optBeq_eq chk_cost0
theorem chk_fields_k {k : Nat} (hk : k < 9) :
    (optBeq (run headLook [11170, sci k] (fsi k) [.br true]) (resField k true) &&
    optBeq (run headLook [11170, sci k] (fsi k) [.br false]) (resField k false) &&
    optBeq (run headLook [sci k + 1] (sci k) []) (resSc1 k) &&
    optBeq (run headLook [sci k + 3] (sci k + 2) []) (resSc3 k) &&
    headLook (sci k + 1) == some 0x00034303) = true :=
  List.all_eq_true.mp chk_fields k (List.mem_range.mpr hk)
theorem chk_childs_k {k : Nat} (hk : k < 9) :
    (optBeq (run headLook [sci k + 4] (sci k + 3) []) (resCc1 k) &&
    optBeq (run headLook [fsi (k + 1)] (sci k + 5) []) (resCc3 k) &&
    headLook (sci k + 4) == some 0xf8034303) = true :=
  List.all_eq_true.mp chk_childs k (List.mem_range.mpr hk)
theorem run_cc1 (k : Nat) (hk : k < 9) : run headLook [sci k + 4] (sci k + 3) [] = some (resCc1 k) := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.1
theorem run_cc3 (k : Nat) (hk : k < 9) : run headLook [fsi (k + 1)] (sci k + 5) [] = some (resCc3 k) := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.2
theorem look_lbu2 (k : Nat) (hk : k < 9) : headLook (sci k + 4) = some 0xf8034303 := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2
theorem run_field (k : Nat) (hk : k < 9) (d : Bool) :
    run headLook [11170, sci k] (fsi k) [.br d] = some (resField k d) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.1.1.1.2
  · exact optBeq_eq h.1.1.1.1
theorem run_sc1 (k : Nat) (hk : k < 9) : run headLook [sci k + 1] (sci k) [] = some (resSc1 k) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.1.2
theorem run_sc3 (k : Nat) (hk : k < 9) : run headLook [sci k + 3] (sci k + 2) [] = some (resSc3 k) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.2
theorem look_lbu (k : Nat) (hk : k < 9) : headLook (sci k + 1) = some 0x00034303 := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2
theorem run_cap (d : Bool) : run headLook [11170, 11164] 11162 [.br d] = some (resCap d) := by
  have h := chk_cap
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_final : run headLook [11175] 11164 [] = some resFinal := optBeq_eq chk_final
theorem run_next : run headLook [11003] 11170 [] = some resNext := optBeq_eq chk_next
theorem run_fail : run headLook [] 11172 [] = some resFail := optBeq_eq chk_fail
end ClaudeWCT.W9.Machine.Sign.SearchM
end
section
namespace ClaudeWCT.W9.Machine.Sign.SearchM
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.T3 (Digest HashOutput)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
def costByte (f : Nat) : Nat :=
  if f < 563 then WCT9.routineCosts.getD f 0
  else if 16256 ≤ f then WCT9.maxChildSave - WCT9.childSave (f - 16256)
  else if 1024 ≤ f ∧ f < 1280 then
    (SigGolfCandidate.T3M.Images.signPrefix_4.getD (f - 1024) 0).toNat else 255
def costChk : Nat → List (BitVec 8) → Bool
  | _, [] => true
  | f, b :: bs => (b.toNat == costByte f) && costChk (f + 1) bs
set_option maxRecDepth 100000 in
theorem costBytes_chk : costChk 0 costBytes = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem costBytes_length : costBytes.length = 16384 := by decide +kernel
theorem costChk_getD : ∀ (l : List (BitVec 8)) (f : Nat), costChk f l = true →
    ∀ i, i < l.length → (l.getD i 0).toNat = costByte (f + i)
  | [], _, _, i, hi => absurd hi (by simp)
  | b :: bs, f, h, i, hi => by
    simp only [costChk, Bool.and_eq_true, beq_iff_eq] at h
    rcases i with _ | i
    · simpa using h.1
    · have := costChk_getD bs (f + 1) h.2 i (by simpa using hi)
      simpa [show f + 1 + i = f + (i + 1) by omega] using this
theorem costBytes_getD (f : Nat) (hf : f < 16384) : (costBytes.getD f 0).toNat = costByte f := by
  have := costChk_getD costBytes 0 costBytes_chk f (by rw [costBytes_length]; exact hf)
  rwa [Nat.zero_add] at this
theorem costByte_lt (f : Nat) : costByte f < 256 := by
  unfold costByte
  split_ifs with h h2 h3
  · have hm : f < WCT9.routineCosts.length := by rw [WCT9.routineCosts_length]; exact h
    rw [List.getD_eq_getElem _ _ hm]
    have := (WCT9.routineCosts_bounds _ (List.getElem_mem hm)).2
    omega
  · unfold WCT9.maxChildSave; omega
  · exact BitVec.isLt _
  · decide
def childN (a : BitVec 256) (c : Nat) : Nat := a.toNat / 2 ^ WCT9.childBase c % 128
theorem childN_lt (a : BitVec 256) (c : Nat) : childN a c < 128 := Nat.mod_lt _ (by decide +kernel)
theorem costByte_child (c : Nat) (hc : c < 128) :
    costByte (16256 + c) = WCT9.maxChildSave - WCT9.childSave c := by
  unfold costByte
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
theorem costByte_childN (a : HashOutput) (k : WCT9.Coord) :
    costByte (16256 + childN a k.val) = WCT9.childExtra (WCT9.child a k) := by
  rw [costByte_child _ (childN_lt a k.val)]; rfl
theorem costByte_rank (a : HashOutput) (c : WCT9.Coord) (h : WCT9.field a c < 563) :
    costByte (WCT9.field a c) = WCT9.routineCost (WCT9.rank a c) := by
  unfold costByte WCT9.routineCost WCT9.rank
  rw [if_pos h, List.getD_eq_getElem _ _ (by rw [WCT9.routineCosts_length]; exact h)]
  simp only [Nat.mod_eq_of_lt h]
theorem cost_byte {s : MachineState} (hc : CostAt s) {f : Nat} (hf : f < 16384) :
    s.getByte (BitVec.ofNat 64 (COST + f)) = BitVec.ofNat 8 (costByte f) := by
  rw [getByte_eq_word s _ (by unfold COST; omega)]
  rw [show (COST + f) / 8 * 8 = COST + 8 * (f / 8) by unfold COST; omega,
    show (COST + f) % 8 = f % 8 by unfold COST; omega, hc (f / 8) (by omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide +kernel))]
  apply BitVec.eq_of_toNat_eq
  rw [← costBytes_getD f hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos (Nat.mod_lt _ (by decide +kernel)), show 8 * (f / 8) + f % 8 = f by omega]
theorem rfs_get_other (l : List (Reg × E)) (x : Reg) (h : ∀ p ∈ l, p.1 ≠ x) :
    (rfs l).get x = RegFile.init.get x := by
  unfold rfs
  suffices ∀ rf : RegFile, (l.foldl (fun rf p => rf.set p.1 p.2) rf).get x = rf.get x from this _
  induction l with
  | nil => intro rf; rfl
  | cons p l ih =>
    intro rf
    simp only [List.foldl_cons]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq)), RegFile.get_set_ne _ _ (Ne.symm (h p (by simp)))]
theorem piece {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat} {n : Nat}
    {dirs : List Dir} {r : PRes} (h : run look stops n dirs = some r) (s : MachineState) (hpc : s.pc = pcOf n)
    (hobl : r.st.obl = []) (hbr : ∀ b ∈ r.brs, b.holds s) (hspc : r.spc = none) :
    Steps im s r.steps r.cycles (r.toState s) ∧ (r.toState s).pc = r.pc ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) ∧
      (∀ x, (r.toState s).getReg x = (r.st.regs.get x).eval s) ∧
      (∀ a, (r.toState s).getMem a = memEval s r.st.mem a) := by
  obtain ⟨h1, h2⟩ := run_sound hl h s hpc (by rw [hobl]; intro o ho; cases ho) hbr
  exact ⟨h1, PRes.toState_pc' r s hspc, h2, fun x => PRes.toState_getReg' r s x,
    fun a => PRes.toState_getMem' r s a⟩
theorem regs_rfs {t s : MachineState} {l : List (Reg × E)} (h : ∀ x, t.getReg x = ((rfs l).get x).eval s) :
    RegsExcept s t (l.map Prod.fst) := by
  intro x hx
  rw [h x, rfs_get_other l x (fun p hp he => hx (List.mem_map.mpr ⟨p, hp, he⟩)), RegFile.init_get_eval]
theorem mod64_div_mod (x p q : Nat) (h : p + q ≤ 64) : x % 2 ^ 64 / 2 ^ p % 2 ^ q = x / 2 ^ p % 2 ^ q := by
  have e : (2 : Nat) ^ 64 = 2 ^ p * 2 ^ (64 - p) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
theorem ofNat_and_mask (x : Word) (q : Nat) (hq : q ≤ 64) :
    x &&& BitVec.ofNat 64 (2 ^ q - 1) = BitVec.ofNat 64 (x.toNat % 2 ^ q) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (2 : Nat) ^ q - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide +kernel) hq; omega
  have h2 : x.toNat % 2 ^ q < 2 ^ 64 := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide +kernel) hq)
  rw [BitVec.toNat_and, toNat_ofNat_lt h1, Nat.and_two_pow_sub_one_eq_mod, toNat_ofNat_lt h2]
theorem and_eval (x y : Word) : BinOp.eval .and x y = x &&& y := rfl
theorem srl_eval (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .srl x (BitVec.ofNat 64 k) = x >>> k := by
  simp only [BinOp.eval, toNat_ofNat_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]
theorem shl0_shr33 (a : BitVec 256) : ((a.extractLsb' 0 64) <<< 0) >>> 33 = BitVec.ofNat 64 (WCT9.digestIndex a) := by
  apply BitVec.eq_of_toNat_eq
  rw [WCT9.digestIndex_val]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.extractLsb'_toNat, pow_zero, Nat.mul_one, Nat.shiftRight_zero]
  omega
theorem sh_bound (k : Nat) (hk : k < 9) : sh k + 21 ≤ 64 ∧ 64 * dw k + sh k + 7 = WCT9.fieldBase k ∧ dw k < 4 := by
  interval_cases k <;> decide +kernel
theorem sll_eval (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .sll x (BitVec.ofNat 64 k) = x <<< k := by
  simp only [BinOp.eval, toNat_ofNat_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]
theorem gateE_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) :
    gateE.eval s = BitVec.ofNat 64 (if a.toNat / 2 ^ 242 % 2 ^ 14 < 1353 then 1 else 0) := by
  have h3 : s.getMem (BitVec.ofNat 64 (NBUF + 24)) = a.extractLsb' 192 64 := ha 3 (by decide +kernel)
  simp only [gateE, cst, E.eval, h3]
  rw [srl_eval _ 50 (by decide +kernel)]
  change (if BitVec.ult (a.extractLsb' 192 64 >>> 50) 1353#64 then (1 : BitVec 64) else 0) = _
  rw [show BitVec.ult (a.extractLsb' 192 64 >>> 50) 1353#64 = decide (a.toNat / 2 ^ 242 % 2 ^ 14 < 1353) by
    simp only [BitVec.ult, SigGolfCandidate.Research.V7Composed198Gate.gate_shift50_toNat,
      show (1353#64 : BitVec 64).toNat = 1353 from rfl]]
  by_cases h : a.toNat / 2 ^ 242 % 2 ^ 14 < 1353
  · simp only [h, decide_true, if_true]; rfl
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; rfl

theorem grpE_toNat (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    ((grpE k).eval s).toNat = a.toNat / 2 ^ (64 * dw k) % 2 ^ 64 / 2 ^ sh k := by
  obtain ⟨h21, -, hd⟩ := sh_bound k hk
  have hm := ha (dw k) hd
  unfold grpE
  split_ifs with h0
  · simp only [cst, E.eval, hm]
    rw [srl_eval _ _ (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
  · have hs0 : sh k = 0 := by interval_cases k <;> simp_all [hasSh, sh]
    simp only [cst, E.eval, hm, hs0, pow_zero, Nat.div_one, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem sll47_srl54 (g : Word) : ((g <<< 47) >>> 54).toNat = g.toNat / 2 ^ 7 % 2 ^ 10 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 64 = 2 ^ 17 * 2 ^ 47 by norm_num, Nat.mul_mod_mul_right,
    show (2 : Nat) ^ 54 = 2 ^ 47 * 2 ^ 7 by norm_num, ← Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel _ (by positivity), show (2 : Nat) ^ 17 = 2 ^ 7 * 2 ^ 10 by norm_num,
    Nat.mod_mul_right_div_self]
theorem sll47_srl54' (g : Word) : (g <<< 47) >>> 54 = BitVec.ofNat 64 (g.toNat / 2 ^ 7 % 2 ^ 10) := by
  apply BitVec.eq_of_toNat_eq
  rw [sll47_srl54, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel))]
theorem fieldE_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    (fieldE k).eval s = BitVec.ofNat 64 (a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 10) := by
  obtain ⟨h21, hcb, -⟩ := sh_bound k hk
  have hg := grpE_toNat s a ha k hk
  simp only [fieldE, cst, E.eval]
  rw [sll_eval _ 47 (by decide +kernel), srl_eval _ 54 (by decide +kernel), sll47_srl54']
  congr 1
  rw [hg, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    mod64_div_mod _ (sh k + 7) 10 (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  all_goals omega
def fieldEOld (k : Nat) : E := .bin .and (.bin .srl (grpE k) (cst 7)) (cst 1023)
theorem fieldEOld_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    (fieldEOld k).eval s = BitVec.ofNat 64 (a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 10) := by
  obtain ⟨h21, hcb, -⟩ := sh_bound k hk
  have hg := grpE_toNat s a ha k hk
  simp only [fieldEOld, cst, E.eval]
  rw [srl_eval _ 7 (by decide +kernel), and_eval, show (1023 : Nat) = 2 ^ 10 - 1 from rfl, ofNat_and_mask _ 10 (by decide +kernel)]
  congr 1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hg, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    mod64_div_mod _ (sh k + 7) 10 (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  all_goals omega
theorem childE_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    (childE k).eval s = BitVec.ofNat 64 (a.toNat / 2 ^ WCT9.childBase k % 128) := by
  obtain ⟨h21, -, -⟩ := sh_bound k hk
  have hg := grpE_toNat s a ha k hk
  have hcb : 64 * dw k + sh k + (if k = 3 ∨ k = 6 then 21 else 0) = WCT9.childBase k := by
    interval_cases k <;> decide +kernel
  unfold childE
  split_ifs with h36
  · simp only [cst, E.eval]
    rw [srl_eval _ 21 (by decide +kernel)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hg, BitVec.toNat_ofNat]
    have hs : sh k = 36 := by rcases h36 with rfl | rfl <;> rfl
    rw [if_pos h36, hs, show 64 * dw k + 36 + 21 = 64 * dw k + (36 + 21) by omega] at hcb
    have hlt : a.toNat / 2 ^ WCT9.childBase k % 128 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
    rw [Nat.mod_eq_of_lt hlt, hs, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← hcb]
    conv_lhs => rw [show (2 : Nat) ^ 64 = 2 ^ (36 + 21) * 2 ^ 7 by norm_num, Nat.mod_mul_right_div_self]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    rfl
  · simp only [cst, E.eval]
    rw [and_eval, show (127 : Nat) = 2 ^ 7 - 1 from rfl, ofNat_and_mask _ 7 (by decide +kernel)]
    congr 1
    rw [if_neg h36, Nat.add_zero] at hcb
    rw [hg, mod64_div_mod _ (sh k) 7 (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add, hcb]
    rfl
section pieces
variable {im : Image}
theorem h153_spec (hl : LookOK im hookLook) (s : MachineState) (hpc : s.pc = pcOf 153) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 11003 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_h153 s hpc rfl (by intro b hb; cases hb) rfl
  refine ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x, fun A _ _ => by rw [hm]; rfl⟩
theorem head_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11003) (i : Nat)
    (hi : i ≤ 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t k, Steps im s k k t ∧ k ≤ 4 ∧ t.pc = (if i < 2 ^ 21 then pcOf 11007 else pcOf 11172) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) ∧ t.getReg .x7 = BitVec.ofNat 64 CBASE := by
  have hbr : ∀ b ∈ (resHead (decide (i < 2 ^ 21))).brs, b.holds s := by
    intro b hb
    simp only [resHead, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, h19, BitVec.ult, toNat_ofNat_lt (by omega : i < 2 ^ 64),
      toNat_ofNat_lt (by decide +kernel : 2 ^ 21 < 2 ^ 64)]
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_head _) s hpc rfl hbr rfl
  refine ⟨_, _, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl, by rw [hr]; rfl⟩
  · simp only [resHead]; split <;> decide +kernel
  · rw [hp]; simp only [resHead]; by_cases h : i < 2 ^ 21 <;> simp [h]
theorem trial_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11007) (i : Nat)
    (_hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 12 12 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf 11019 ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 i ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 24 ∨ A = DIG + 16) := by
  obtain ⟨hs, hp, he, hr, hm⟩ := piece hl run_trial s hpc rfl (by intro b hb; cases hb) rfl
  have hctr : ctrE.eval s = BitVec.ofNat 64 i := by
    simp only [ctrE, cst, E.eval, BinOp.eval, h19, toNat_ofNat_lt (by decide +kernel : (0 : Nat) < 2 ^ 64)]
    rw [ofNat_shl i 0, pow_zero, Nat.mul_one]
  refine ⟨_, hs, he rfl, hp, by rw [hr]; rfl, by rw [hr]; rfl, by rw [hr]; rfl, ?_, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide +kernel) (by decide +kernel), if_neg (by decide +kernel),
      memEval_cons_ofNat _ _ _ _ _ (by decide +kernel) (by decide +kernel), if_pos rfl]; rfl
  · rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide +kernel) (by decide +kernel), if_pos rfl, hctr]
  · intro A hA hn
    simp only [not_or] at hn
    rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide +kernel), if_neg hn.1, memEval_cons_ofNat _ _ _ _ _ hA (by decide +kernel),
      if_neg hn.2]; rfl
theorem gate_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11020) (a : BitVec 256)
    (ha : OutAt s NBUF a) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = (if a.toNat / 2 ^ 242 % 2 ^ 14 < 1353 then pcOf 11027 else pcOf 11170) ∧
      t.getReg .x22 = a.extractLsb' 0 64 ∧ RegsExcept s t [.x6, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  have hg := gateE_eval s a ha
  have hbr : ∀ b ∈ (resGate (decide ¬ (a.toNat / 2 ^ 242 % 2 ^ 14 < 1353))).brs, b.holds s := by
    intro b hb
    simp only [resGate, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hg]
    by_cases h0 : a.toNat / 2 ^ 242 % 2 ^ 14 < 1353
    · simp only [h0, if_true, not_true_eq_false, decide_false]; decide +kernel
    · simp only [h0, if_false, not_false_eq_true, decide_true]; decide +kernel
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_gate _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · rw [hp]; simp only [resGate]
    by_cases h0 : a.toNat / 2 ^ 242 % 2 ^ 14 < 1353
    · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
    · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
  · rw [hr]
    have h0 := ha 0 (by decide +kernel)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    show s.getMem (BitVec.ofNat 64 NBUF) = _
    exact h0
theorem cost0_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11027) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (fsi 0) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x21 = BitVec.ofNat 64 COST ∧ RegsExcept s t [.x20, .x21] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_cost0 s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, hp, by rw [hr]; rfl, by rw [hr]; rfl, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
theorem field_spec (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (s : MachineState)
    (hpc : s.pc = pcOf (fsi k)) (a : BitVec 256) (ha : OutAt s NBUF a) :
    ∃ t c, Steps im s c c t ∧ c ≤ 9 ∧
      t.pc = (if WCT9.field a ⟨k, hk⟩ < 563 then pcOf (sci k) else pcOf 11170) ∧
      t.getReg .x25 = BitVec.ofNat 64 (WCT9.field a ⟨k, hk⟩) ∧
      t.getReg .x24 = BitVec.ofNat 64 (childN a k) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  have hf := fieldE_eval s a ha k hk
  have hfd : WCT9.field a ⟨k, hk⟩ = a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 10 := rfl
  have hlt : a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 10 < 2 ^ 64 :=
    lt_trans (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel)
  have hbr : ∀ b ∈ (resField k (decide ¬ (WCT9.field a ⟨k, hk⟩ < 563))).brs, b.holds s := by
    intro b hb
    simp only [resField, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, hf, BitVec.ult, toNat_ofNat_lt hlt,
      toNat_ofNat_lt (by decide +kernel : 563 < 2 ^ 64), hfd]
    rw [decide_not]
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_field k hk _) s hpc rfl hbr rfl
  refine ⟨_, _, hs, ?_, ?_, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · simp only [resField, fieldLen]; split <;> omega
  · rw [hp]; simp only [resField]
    by_cases h : WCT9.field a ⟨k, hk⟩ < 563 <;> simp [h]
  · rw [hr]; exact hf
  · rw [hr]; exact childE_eval s a ha k hk
theorem decode_lbu : decodeInstruction 0x00034303 = some (.base (.LBU .x6 .x6 0)) := by rfl
theorem lbu_step (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (u : MachineState)
    (hpc : u.pc = pcOf (sci k + 1)) (f : Nat) (hf : f < 16384) (h6 : u.getReg .x6 = BitVec.ofNat 64 (COST + f))
    (hc : CostAt u) :
    ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf (sci k + 2) ∧ v.getReg .x6 = BitVec.ofNat 64 (costByte f) ∧
      RegsExcept u v [.x6] ∧ Frame u v (fun _ => False) := by
  have hb := (sci_lt k hk).2.2
  have hpc' : (u.pc.toNat < 0x1000 || u.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : headLook ((u.pc.toNat - 0x1000) / 4) = some 0x00034303 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * (sci k + 1) - 0x1000) / 4 = sci k + 1 by omega]
    exact look_lbu k hk
  have hf' : fetch im u = some (.base (.LBU .x6 .x6 0)) := (fetch_of_look hl hpc' hw u rfl).trans decode_lbu
  have hcl : classify (.base (.LBU .x6 .x6 0)) = some (.load .bu .x6 .x6 (signExtend12 0)) := rfl
  have e : u.getReg .x6 + signExtend12 0 = BitVec.ofNat 64 (COST + f) := by
    rw [h6]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have hacc : accessValid (u.getReg .x6 + signExtend12 0) LoadKind.bu.width = true := by
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show COST + f < 2 ^ 64 by unfold COST; omega), MEMORY_BYTES]
    unfold COST; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact SigGolfCandidate.T3M.pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide +kernel)]
    simp only [LoadKind.read, e, cost_byte hc hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := costByte_lt f
    omega
  · intro r hr
    have hne : Reg.x6 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp
theorem sc_spec (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (sci k))
    (f S : Nat) (hf : f < 16384) (hS : S + 256 < 2 ^ 64) (h21 : s.getReg .x21 = BitVec.ofNat 64 COST)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 f) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) (hc : CostAt s) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (sci k + 3) ∧ t.getReg .x20 = BitVec.ofNat 64 (S + costByte f) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs1, hp1, -, hr1, hm1⟩ := piece hl (run_sc1 k hk) s hpc rfl (by intro b hb; cases hb) rfl
  set u := (resSc1 k).toState s with hu
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (COST + f) := by
    rw [hr1]; show s.getReg .x21 + s.getReg .x25 = _; rw [h21, h25, ofNat_add_ofNat]
  have hcu : CostAt u := fun j hj => by rw [hm1]; exact hc j hj
  obtain ⟨v, hs2, hp2, v6, hr2, hf2⟩ := lbu_step hl k hk u hp1 f hf u6 hcu
  obtain ⟨hs3, hp3, -, hr3, hm3⟩ := piece hl (run_sc3 k hk) v hp2 rfl (by intro b hb; cases hb) rfl
  refine ⟨_, (hs1.trans (hs2.trans hs3)).of_eq rfl rfl, hp3, ?_, ?_, ?_⟩
  · rw [hr3]; show v.getReg .x20 + v.getReg .x6 = _
    rw [hr2.get (by decide +kernel), hr1, v6]
    show s.getReg .x20 + _ = _
    rw [h20, ofNat_add_ofNat]
  · exact ((regs_rfs hr1).trans (hr2.trans (regs_rfs hr3))).mono (by decide +kernel)
  · intro A hA hn
    rw [hm3]
    show v.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
    rw [hf2.get hA hn, hm1]; rfl
theorem decode_lbu2 : decodeInstruction 0xf8034303 = some (.base (.LBU .x6 .x6 3968)) := by rfl
theorem lbu_step2 (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (u : MachineState)
    (hpc : u.pc = pcOf (sci k + 4)) (c : Nat) (hc' : c < 128) (h6 : u.getReg .x6 = BitVec.ofNat 64 (CBASE + c))
    (hc : CostAt u) :
    ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf (sci k + 5) ∧ v.getReg .x6 = BitVec.ofNat 64 (costByte (16256 + c)) ∧
      RegsExcept u v [.x6] ∧ Frame u v (fun _ => False) := by
  have hb := (sci_lt k hk).2.2
  have hpc' : (u.pc.toNat < 0x1000 || u.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : headLook ((u.pc.toNat - 0x1000) / 4) = some 0xf8034303 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * (sci k + 4) - 0x1000) / 4 = sci k + 4 by omega]
    exact look_lbu2 k hk
  have hf' : fetch im u = some (.base (.LBU .x6 .x6 3968)) := (fetch_of_look hl hpc' hw u rfl).trans decode_lbu2
  have hcl : classify (.base (.LBU .x6 .x6 3968)) = some (.load .bu .x6 .x6 (signExtend12 3968)) := rfl
  have hse : signExtend12 3968 = BitVec.ofNat 64 (2 ^ 64 - 128) := by decide +kernel
  have hf : 16256 + c < 16384 := by omega
  have e : u.getReg .x6 + signExtend12 3968 = BitVec.ofNat 64 (COST + (16256 + c)) := by
    rw [h6, hse, ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    unfold CBASE COST; omega
  have hacc : accessValid (u.getReg .x6 + signExtend12 3968) LoadKind.bu.width = true := by
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show COST + (16256 + c) < 2 ^ 64 by unfold COST; omega), MEMORY_BYTES]
    unfold COST; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact SigGolfCandidate.T3M.pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide +kernel)]
    simp only [LoadKind.read, e, cost_byte hc hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := costByte_lt (16256 + c)
    omega
  · intro r hr
    have hne : Reg.x6 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp
theorem cc_spec (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (sci k + 3))
    (c S : Nat) (hc' : c < 128) (hS : S + 256 < 2 ^ 64) (h7 : s.getReg .x7 = BitVec.ofNat 64 CBASE)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 c) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) (hc : CostAt s) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (fsi (k + 1)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (S + costByte (16256 + c)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs1, hp1, -, hr1, hm1⟩ := piece hl (run_cc1 k hk) s hpc rfl (by intro b hb; cases hb) rfl
  set u := (resCc1 k).toState s with hu
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (CBASE + c) := by
    rw [hr1]; show s.getReg .x7 + s.getReg .x24 = _; rw [h7, h24, ofNat_add_ofNat]
  have hcu : CostAt u := fun j hj => by rw [hm1]; exact hc j hj
  obtain ⟨v, hs2, hp2, v6, hr2, hf2⟩ := lbu_step2 hl k hk u hp1 c hc' u6 hcu
  obtain ⟨hs3, hp3, -, hr3, hm3⟩ := piece hl (run_cc3 k hk) v hp2 rfl (by intro b hb; cases hb) rfl
  refine ⟨_, (hs1.trans (hs2.trans hs3)).of_eq rfl rfl, hp3, ?_, ?_, ?_⟩
  · rw [hr3]; show v.getReg .x20 + v.getReg .x6 = _
    rw [hr2.get (by decide +kernel), hr1, v6]
    show s.getReg .x20 + _ = _
    rw [h20, ofNat_add_ofNat]
  · exact ((regs_rfs hr1).trans (hr2.trans (regs_rfs hr3))).mono (by decide +kernel)
  · intro A hA hn
    rw [hm3]
    show v.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
    rw [hf2.get hA hn, hm1]; rfl
def fieldN (a : BitVec 256) (c : Nat) : Nat := a.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10
def psum (a : BitVec 256) (k : Nat) : Nat :=
  ((List.range k).map fun c => costByte (fieldN a c) + costByte (16256 + childN a c)).sum
theorem psum_succ (a : BitVec 256) (k : Nat) :
    psum a (k + 1) = psum a k + costByte (fieldN a k) + costByte (16256 + childN a k) := by
  simp [psum, List.range_succ, List.sum_append, Nat.add_assoc]
theorem psum_le (a : BitVec 256) (k : Nat) : psum a k ≤ 512 * k := by
  induction k with
  | zero => simp [psum]
  | succ k ih =>
    rw [psum_succ]; have := costByte_lt (fieldN a k); have := costByte_lt (16256 + childN a k); omega
theorem fieldN_lt (a : BitVec 256) (c : Nat) : fieldN a c < 16384 :=
  lt_of_lt_of_le (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel)
theorem fields_from (hl : LookOK im headLook) (a : BitVec 256) :
    ∀ n k, k + n = 9 → ∀ v : MachineState, v.pc = pcOf (fsi k) → OutAt v NBUF a → CostAt v →
      v.getReg .x21 = BitVec.ofNat 64 COST → v.getReg .x7 = BitVec.ofNat 64 CBASE →
      v.getReg .x20 = BitVec.ofNat 64 (psum a k) →
      ∃ t c, Steps im v c c t ∧ c ≤ 15 * n ∧ RegsExcept v t [.x6, .x20, .x24, .x25, .x28] ∧
        Frame v t (fun _ => False) ∧
        (if ∀ k' (hk' : k' < 9), k ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563
          then t.pc = pcOf 11162 ∧ t.getReg .x20 = BitVec.ofNat 64 (psum a 9) else t.pc = pcOf 11170) := by
  intro n
  induction n with
  | zero =>
    intro k hk v hv _ _ _ _ h20
    have hk9 : k = 9 := by omega
    subst hk9
    refine ⟨v, 0, Steps.refl v, le_refl _, RegsExcept.refl _ _, Frame.refl _ _, ?_⟩
    rw [if_pos (fun k' hk' hle => by omega)]
    exact ⟨by rw [hv, fsi_nine], h20⟩
  | succ n ih =>
    intro k hk v hv ha hc h21 h7 h20
    have hk9 : k < 9 := by omega
    obtain ⟨t1, c1, s1, hc1, p1, x25, x24, r1, f1⟩ := field_spec hl k hk9 v hv a ha
    by_cases hf : WCT9.field a ⟨k, hk9⟩ < 563
    · rw [if_pos hf] at p1
      have hc1' : CostAt t1 := fun j hj => by rw [f1.get (by unfold COST; omega) (fun h => h)]; exact hc j hj
      obtain ⟨t2, s2, p2, x20', r2, f2⟩ := sc_spec hl k hk9 t1 p1 (WCT9.field a ⟨k, hk9⟩) (psum a k)
        (fieldN_lt a k) (by have := psum_le a k; omega) (by rw [r1.get (by decide +kernel)]; exact h21) x25
        (by rw [r1.get (by decide +kernel)]; exact h20) hc1'
      have hc2' : CostAt t2 := fun j hj => by rw [f2.get (by unfold COST; omega) (fun h => h)]; exact hc1' j hj
      obtain ⟨t2b, s2b, p2b, x20b, r2b, f2b⟩ := cc_spec hl k hk9 t2 p2 (childN a k)
        (psum a k + costByte (WCT9.field a ⟨k, hk9⟩)) (childN_lt a k)
        (by have := psum_le a k; have := costByte_lt (WCT9.field a ⟨k, hk9⟩); omega)
        (by rw [r2.get (by decide +kernel), r1.get (by decide +kernel)]; exact h7)
        (by rw [r2.get (by decide +kernel)]; exact x24) x20' hc2'
      have ha2 : OutAt t2b NBUF a := fun j hj => by
        rw [f2b.get (by simp only [NBUF]; omega) (fun h => h), f2.get (by simp only [NBUF]; omega) (fun h => h),
          f1.get (by simp only [NBUF]; omega) (fun h => h)]
        exact ha j hj
      have hc2 : CostAt t2b := fun j hj => by rw [f2b.get (by unfold COST; omega) (fun h => h)]; exact hc2' j hj
      obtain ⟨t, c, s3, hc3, r3, f3, p3⟩ := ih (k + 1) (by omega) t2b p2b ha2 hc2
        (by rw [r2b.get (by decide +kernel), r2.get (by decide +kernel), r1.get (by decide +kernel)]; exact h21)
        (by rw [r2b.get (by decide +kernel), r2.get (by decide +kernel), r1.get (by decide +kernel)]; exact h7)
        (by rw [x20b, psum_succ]; rfl)
      refine ⟨t, c1 + 3 + 3 + c, ((s1.trans s2).trans s2b).trans s3, by omega,
        (((r1.trans r2).trans r2b).trans r3).mono (by decide +kernel),
        (((f1.trans f2).trans f2b).trans f3).mono (fun _ _ h => by simp at h), ?_⟩
      have hiff : (∀ k' (hk' : k' < 9), k ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563) ↔
          (∀ k' (hk' : k' < 9), k + 1 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563) := by
        constructor
        · intro h k' hk' hle; exact h k' hk' (by omega)
        · intro h k' hk' hle
          by_cases he : k' = k
          · subst he; exact hf
          · exact h k' hk' (by omega)
      by_cases hall : ∀ k' (hk' : k' < 9), k + 1 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563
      · rw [if_pos hall] at p3; rw [if_pos (hiff.2 hall)]; exact p3
      · rw [if_neg hall] at p3; rw [if_neg (fun h => hall (hiff.1 h))]; exact p3
    · rw [if_neg hf] at p1
      refine ⟨t1, c1, s1, by omega, r1.mono (by decide +kernel), f1, ?_⟩
      rw [if_neg (fun h => hf (h k hk9 le_rfl))]; exact p1
theorem psum_nine (a : BitVec 256) (h : ∀ c : WCT9.Coord, WCT9.field a c < 563) :
    psum a 9 = WCT9.jointCost a := by
  unfold psum WCT9.jointCost WCT9.coordCost
  rw [show List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl,
    show List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [← costByte_rank a 0 (h 0), ← costByte_rank a 1 (h 1), ← costByte_rank a 2 (h 2), ← costByte_rank a 3 (h 3),
    ← costByte_rank a 4 (h 4), ← costByte_rank a 5 (h 5), ← costByte_rank a 6 (h 6), ← costByte_rank a 7 (h 7),
    ← costByte_rank a 8 (h 8), ← costByte_childN a 0, ← costByte_childN a 1, ← costByte_childN a 2,
    ← costByte_childN a 3, ← costByte_childN a 4, ← costByte_childN a 5, ← costByte_childN a 6,
    ← costByte_childN a 7, ← costByte_childN a 8]
  rfl
theorem cap_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11162) (S : Nat)
    (hS : S < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if S ≤ 789 then pcOf 11164 else pcOf 11170) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hce : capE.eval s = BitVec.ofNat 64 (if S < 790 then 1 else 0) := by
    simp only [capE, cst, E.eval, h20, BinOp.eval, BitVec.ult, toNat_ofNat_lt hS,
      toNat_ofNat_lt (show 790 < 2 ^ 64 by decide +kernel)]
    by_cases h : S < 790 <;> simp [h]
  have hbr : ∀ b ∈ (resCap (decide ¬ (S ≤ 789))).brs, b.holds s := by
    intro b hb
    simp only [resCap, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hce]
    by_cases h0 : S ≤ 789
    · simp only [show S < 790 by omega, if_true, h0, not_true_eq_false, decide_false]; decide +kernel
    · simp only [show ¬ S < 790 by omega, if_false, h0, not_false_eq_true, decide_true]; decide +kernel
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_cap _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hp]; simp only [resCap]
  by_cases h0 : S ≤ 789
  · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
  · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
theorem checks_spec (hl : LookOK im headLook) (u : MachineState) (hpc : u.pc = pcOf 11020) (a : BitVec 256)
    (ha : OutAt u NBUF a) (hc : CostAt u) (h7 : u.getReg .x7 = BitVec.ofNat 64 CBASE) :
    ∃ t c, Steps im u c c t ∧ c ≤ 147 ∧ RegsExcept u t [.x6, .x7, .x20, .x21, .x22, .x24, .x25, .x28] ∧
      Frame u t (fun _ => False) ∧
      (if WCT9.producerAdmissible a = true then t.pc = pcOf 11164 ∧ t.getReg .x22 = a.extractLsb' 0 64
        else t.pc = pcOf 11170) := by
  obtain ⟨t1, s1, p1, x22, r1, f1⟩ := gate_spec hl u hpc a ha
  have hadm := WCT9.admissible_iff a
  have hprod := WCT9.producerAdmissible_iff a
  by_cases hg : a.toNat / 2 ^ 242 % 2 ^ 14 < 1353
  · rw [if_pos hg] at p1
    obtain ⟨t2, s2, p2, x20, x21, r2, f2⟩ := cost0_spec hl t1 p1
    have ha2 : OutAt t2 NBUF a := fun j hj => by
      rw [f2.get (by simp only [NBUF]; omega) (fun h => h), f1.get (by simp only [NBUF]; omega) (fun h => h)]
      exact ha j hj
    have hc2 : CostAt t2 := fun j hj => by
      rw [f2.get (by unfold COST; omega) (fun h => h), f1.get (by unfold COST; omega) (fun h => h)]; exact hc j hj
    obtain ⟨t3, c3, s3, hc3, r3, f3, p3⟩ := fields_from hl a 9 0 rfl t2 p2 ha2 hc2 x21
      (by rw [r2.get (by decide +kernel), r1.get (by decide +kernel)]; exact h7) (by rw [x20]; rfl)
    have h22 : ∀ {t : MachineState}, RegsExcept t2 t [.x6, .x20, .x24, .x25, .x28] →
        t.getReg .x22 = a.extractLsb' 0 64 := fun h => by rw [h.get (by decide +kernel), r2.get (by decide +kernel)]; exact x22
    have hall : (∀ k' (hk' : k' < 9), 0 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563) ↔
        ∀ c : WCT9.Coord, WCT9.field a c < 563 :=
      ⟨fun h c => h c.val c.isLt (Nat.zero_le _), fun h k' hk' _ => h ⟨k', hk'⟩⟩
    by_cases hf : ∀ c : WCT9.Coord, WCT9.field a c < 563
    · rw [if_pos (hall.2 hf)] at p3
      obtain ⟨p3, x20'⟩ := p3
      have hS := psum_le a 9
      obtain ⟨t4, s4, p4, r4, f4⟩ := cap_spec hl t3 p3 (psum a 9) (by omega) x20'
      refine ⟨t4, 7 + 3 + c3 + 2, ((s1.trans s2).trans s3).trans s4, by omega,
        (((r1.trans r2).trans r3).trans r4).mono (by decide +kernel),
        (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by simp at h), ?_⟩
      have hjc : psum a 9 = WCT9.jointCost a := psum_nine a hf
      by_cases hA : WCT9.producerAdmissible a = true
      · rw [if_pos hA]
        have hcap := (hprod.1 hA).2
        rw [if_pos (by rw [hjc]; exact hcap)] at p4
        exact ⟨p4, by rw [r4.get (by decide +kernel)]; exact h22 r3⟩
      · rw [if_neg hA]
        have hcap : ¬ psum a 9 ≤ 789 := fun h => hA (hprod.2 ⟨hadm.2 ⟨hg, hf⟩, by rw [← hjc]; exact h⟩)
        rw [if_neg hcap] at p4; exact p4
    · rw [if_neg (fun h => hf (hall.1 h))] at p3
      refine ⟨t3, 7 + 3 + c3, (s1.trans s2).trans s3, by omega, ((r1.trans r2).trans r3).mono (by decide +kernel),
        ((f1.trans f2).trans f3).mono (fun _ _ h => by simp at h), ?_⟩
      have hA : ¬ WCT9.producerAdmissible a = true := fun h => hf ((hadm.1 (hprod.1 h).1).2)
      rw [if_neg hA]; exact p3
  · rw [if_neg hg] at p1
    refine ⟨t1, 7, s1, by omega, r1.mono (by decide +kernel), f1, ?_⟩
    have hA : ¬ WCT9.producerAdmissible a = true := fun h => hg ((hadm.1 (hprod.1 h).1).1)
    rw [if_neg hA]; exact p1
theorem final_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11164) (a : BitVec 256)
    (h22 : s.getReg .x22 = a.extractLsb' 0 64) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 11175 ∧ t.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      RegsExcept s t [.x22, .x28] ∧ Frame s t (fun A => A = IDXV) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_final s hpc rfl (by intro b hb; cases hb) rfl
  have hidx : idxE.eval s = BitVec.ofNat 64 (WCT9.digestIndex a) := by
    simp only [idxE, cst, E.eval, h22]
    rw [srl_eval _ 33 (by decide +kernel), sll_eval _ 0 (by decide +kernel)]
    exact shl0_shr33 a
  refine ⟨_, hs, hp, by rw [hr]; exact hidx, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resFinal, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide +kernel) (by decide +kernel), if_pos rfl, hidx]
  · intro A hA hn
    rw [hm]; simp only [resFinal, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide +kernel), if_neg hn]; rfl
theorem next_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11170) (i : Nat)
    (_hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 11003 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_next s hpc rfl (by intro b hb; cases hb) rfl
  refine ⟨_, hs, hp, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hr]
  show s.getReg .x19 + BitVec.ofNat 64 1 = _
  rw [h19, ofNat_add_ofNat]
theorem fail_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11172) :
    ∃ t, Steps im s 2 2 t ∧ fetch im t = some (.base .ECALL) ∧ FailedS t := by
  obtain ⟨hs, hp, he, hr, -⟩ := piece hl run_fail s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, he rfl, ⟨hp, by rw [hr]; rfl, by rw [hr]; rfl⟩⟩
end pieces
theorem digestInput_length' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    (SigGolfCandidate.T3.digestInput rho m c).length = 64 := by
  simp only [SigGolfCandidate.T3.digestInput, List.length_append, bytesLE_length]
theorem pad64_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c) = SigGolfCandidate.T3.digestInput rho m c := by
  unfold SigGolfCandidate.T3.pad64
  rw [digestInput_length']
  simp
theorem wordsOf_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    wordsOf (SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c)) =
      [rho.extractLsb' 0 64, rho.extractLsb' 64 64, BitVec.ofNat 64 0,
        BitVec.ofNat 64 c.toNat, m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64] := by
  rw [pad64_digestInput']
  unfold SigGolfCandidate.T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE32]
  have hc := c.isLt
  have h0 : (SigGolfCandidate.T3.digestHeader c).extractLsb' 0 64 = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, SigGolfCandidate.T3.digestHeader_toNat]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have h1 : (SigGolfCandidate.T3.digestHeader c).extractLsb' 64 64 = BitVec.ofNat 64 c.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, SigGolfCandidate.T3.digestHeader_toNat]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  rw [h0, h1]
  rfl
theorem blocks_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    (toQ (SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput', blocks_toQ (by rw [Aligned, digestInput_length']; omega), digestInput_length']
structure LInv (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 11003
  hi : i ≤ 2 ^ 21
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t searchRegs
  frame : Frame s0 t SearchW
theorem outAt_writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    OutAt (writeHash t a) NBUF a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide +kernel) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp
theorem costAt_frame {s t : MachineState} (h : CostAt s) (hf : Frame s t SearchW) : CostAt t := fun j hj => by
  rw [hf.get (by unfold COST; omega) (by unfold SearchW COST DIG NBUF IDXV; omega)]; exact h j hj
section loop
variable {im : Image} {sk : BitVec 256}
theorem loop (hl : LookOK im headLook) {s0 : MachineState} {rho : Digest} {m : Message}
    (hpre : SearchPre rho m s0) :
    ∀ F i t, i + F = 2 ^ 21 → LInv s0 i t →
      TBSim im sk t (F * 200 + 100) (WCT9.digestSearch rho m i F) (SearchPost s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, k1, s1, hk1, p1, -, -, -⟩ := head_spec hl t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨t2, s2, -, hf⟩ := fail_spec hl t1 p1
    exact (TBSim.pure_steps' (sk := sk) (s1.trans s2) (Q := SearchPost s0) (a := none) hf).mono
      (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 21 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, x7h⟩ := head_spec hl t hI.pc i hI.hi hI.x19
    rw [if_pos hi] at p1
    obtain ⟨u, s2, hfu, p2, h10, h11, h12, h16, h24, r2, f2⟩ :=
      trial_spec hl t1 p1 i hi (by rw [r1.get (by decide +kernel), hI.x19])
    have ru : RegsExcept s0 u searchRegs :=
      ((hI.regs.trans r1).trans r2).mono (by decide +kernel)
    have fu : Frame s0 u SearchW := ((hI.frame.trans f1).trans f2).mono (fun A _ hA => by
      simp only [or_false] at hA
      rcases hA with hA | hA
      · exact hA
      · unfold SearchW; rcases hA with hA | hA <;> simp [hA])
    have mem : ∀ A, A < 2 ^ 64 → ¬ SearchW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ SearchW A := by
      intro A hA; simp only [SearchW, DIG, NBUF, IDXV] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide +kernel)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide +kernel)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide +kernel)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide +kernel)
    have hq : hashInput u = toQ (SigGolfCandidate.T3.pad64
        (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i))) := by
      refine hashInput_toQ u _ 0 DIG (by rw [pad64_digestInput', digestInput_length']) h10 (by decide +kernel)
        (by decide +kernel) h11 (by decide +kernel) ?_
      rw [SigGolfCandidate.T3M.readWords_eight, wordsOf_digestInput', hc, h16, h24,
        mem DIG (by decide +kernel) (nw _ (by omega)), mem (DIG + 8) (by decide +kernel) (nw _ (by omega)),
        mem (DIG + 32) (by decide +kernel) (nw _ (by omega)), mem (DIG + 40) (by decide +kernel) (nw _ (by omega)),
        mem (DIG + 48) (by decide +kernel) (nw _ (by omega)), mem (DIG + 56) (by decide +kernel) (nw _ (by omega)),
        hpre.rho.1, hpre.rho.2, hm0, hm1, hm2, hm3]
    have hv : hashArgumentsValid u = true :=
      hashArgs_const u DIG 64 NBUF h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h5 : u.getReg .x5 = 0 := by rw [ru.get (by decide +kernel), hpre.x5]
    have prog : WCT9.digestSearch rho m i (F + 1) =
        (SigGolfCandidate.T3.publicHash (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if WCT9.producerAdmissible output = true then pure (some (BitVec.ofNat 32 i, output))
          else WCT9.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind' hfu h5 hv hq
      (W := 176 + (F * 200 + 100)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput']; ring_nf; omega
    have pw : (writeHash u a).pc = pcOf 11020 := by rw [pc_writeHash, p2, SigGolfCandidate.T3M.pcOf_add4]
    have hN : OutAt (writeHash u a) NBUF a := outAt_writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide +kernel)
    have fuw : Frame s0 (writeHash u a) SearchW := (fu.trans fw).mono (fun A _ hA => by
      rcases hA with hA | hA
      · exact hA
      · unfold SearchW; right; right; left; exact hA)
    obtain ⟨v, c, sv, hcv, rv, fv, pv⟩ := checks_spec hl (writeHash u a) pw a hN (costAt_frame hpre.cost fuw)
      (by rw [getReg_writeHash, r2.get (by decide +kernel)]; exact x7h)
    have rv' : RegsExcept s0 v searchRegs :=
      ((ru.trans (fun r _ => getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans rv).mono
        (by decide +kernel)
    have fv' : Frame s0 v SearchW := (fuw.trans fv).mono (fun A _ hA => by
      simp only [or_false] at hA; exact hA)
    have hNv : OutAt v NBUF a := fun j hj => by
      rw [fv.get (by simp only [NBUF]; omega) (fun h => h)]; exact hN j hj
    have x19v : v.getReg .x19 = BitVec.ofNat 64 i := by
      rw [rv.get (by decide +kernel), getReg_writeHash, r2.get (by decide +kernel), r1.get (by decide +kernel), hI.x19]
    by_cases hadm : WCT9.producerAdmissible a = true
    · rw [if_pos hadm] at pv
      simp only [hadm, ↓reduceIte]
      obtain ⟨w, sw, pw', x22w, idxw, rw', fw'⟩ := final_spec hl v pv.1 a pv.2
      refine (TBSim.pure_steps' (sv.trans sw) ?_).mono (by omega) (fun _ _ h => h)
      refine ⟨pw', by rw [rw'.get (by decide +kernel), rv'.get (by decide +kernel), hpre.x5], hadm, ?_, x22w, idxw,
        by rw [hc]; exact hi, ?_, ?_⟩
      · intro j hj; rw [fw'.get (by simp only [NBUF]; omega) (by simp only [IDXV, NBUF]; omega)]; exact hNv j hj
      · exact (rv'.trans rw').mono (by decide +kernel)
      · exact (fv'.trans fw').mono (fun A _ hA => by
          rcases hA with hA | hA
          · exact hA
          · unfold SearchW; right; right; right; exact hA)
    · rw [if_neg hadm] at pv
      simp only [hadm, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨w, sw, pw', x19w, rw', fw'⟩ := next_spec hl v pv i hi x19v
      have hI' : LInv s0 (i + 1) w :=
        ⟨pw', by omega, x19w, (rv'.trans rw').mono (by decide +kernel),
          (fv'.trans fw').mono (fun A _ hA => by simp only [or_false] at hA; exact hA)⟩
      exact (TBSim.steps (sv.trans sw) (ih (i + 1) w (by omega) hI')).mono (by omega) (fun _ _ h => h)
end loop
end ClaudeWCT.W9.Machine.Sign.SearchM
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign.SearchM
theorem searchGood (im : Image) : SearchGood im := by
  intro hnew hhooks sk rho m s hpre
  obtain ⟨t0, s0, p0, r0, f0⟩ := h153_spec (hookLook_ok hhooks) s hpre.pc
  have hI : LInv s 0 t0 :=
    ⟨p0, by norm_num, by rw [r0.get (by simp), hpre.x19], r0.mono (by intro x hx; simp at hx),
      f0.mono (fun _ _ h => h.elim)⟩
  have := TBSim.steps (sk := sk) s0
    (loop (headLook_ok hnew) hpre (2 ^ 21) 0 t0 (by norm_num) hI)
  refine this.mono ?_ (fun _ _ h => h)
  unfold searchC trialC WCT9.digestAttemptLimit
  omega
end ClaudeWCT.W9.Machine.Sign
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Code ====
section

namespace ClaudeWCT.W9.Machine.Expand
def expChunk_4 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_4
def expChunk_5 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_5
def expChunk_6 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_6
def expChunk_7 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_7
def expChunk_8 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_8
def expChunk_9 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_9
def expChunk_10 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_10
def expChunk_11 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_11
def expChunk_12 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_12
def expChunk_13 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_13
def expChunk_14 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_14
def expChunk_15 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_15
def expChunk_16 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_16
def expChunk_17 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_17
def expChunk_18 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_18
def expChunk_19 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_19
def expChunk_20 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_20
def expChunk_21 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_21
def expChunk_22 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_22
def expChunk_23 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_23
def expChunk_24 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_24
def expChunk_25 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_25
def expChunk_26 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_26
def expChunk_27 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_27
def expChunk_28 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_28
def expChunk_29 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_29
def expChunk_30 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_30
def expChunk_31 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_31
def expChunk_32 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_32
def expChunk_33 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_33
def expChunk_34 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_34
def expChunk_35 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_35
def expChunk_36 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_36
def expChunk_37 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_37
def expChunk_38 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_38
def expChunk_39 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_39
def expChunk_40 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_40
def expChunk_41 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_41
def expChunk_42 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_42
def expChunk_43 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_43
def expChunk_44 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_44
def expChunk_45 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_45
def expChunk_46 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_46
def expChunk_47 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_47
def expChunk_48 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_48
def expChunk_49 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_49
def expChunk_50 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_50
def expChunk_51 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_51
def expChunk_52 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_52
def expChunk_53 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_53
def expChunk_54 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_54
def expChunk_55 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_55
def expChunk_56 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_56
def expChunk_57 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_57
def expChunk_58 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_58
def expChunk_59 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_59
def expChunk_60 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_60
def expChunk_61 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_61
def expChunk_62 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_62
def expChunk_63 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_63
def expChunk_64 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_64
def expChunk_65 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_65
def expChunk_66 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_66
def expChunk_67 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_67
def expChunk_68 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_68
def expChunk_69 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_69
def expChunk_70 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_70
def expChunk_71 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_71
def expChunk_72 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_72
def expChunk_73 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_73
def expChunk_74 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_74
def expChunk_75 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_75
def expChunk_76 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_76
def expChunk_77 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_77
def expChunk_78 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_78
def expChunk_79 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_79
def expChunk_80 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_80
def expChunk_81 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_81
def expChunk_82 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_82
def expChunk_83 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_83
def expChunk_84 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_84
def expChunk_85 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_85
def expChunk_86 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_86
def expChunk_87 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_87
def expChunk_88 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_88
def expChunk_89 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_89
def expChunk_90 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_90
def expChunk_91 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_91
def expChunk_92 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_92
def expChunk_93 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_93
def expChunk_94 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_94
def expChunk_95 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_95
def expChunk_96 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_96
def expChunk_97 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_97
def expChunk_98 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_98
def expChunk_99 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_99
def expChunk_100 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_100
def expChunk_101 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_101
def expChunk_102 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_102
def expChunk_103 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_103
def expChunk_104 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_104
def expChunk_105 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_105
def expChunk_106 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_106
def expChunk_107 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_107
def expChunk_108 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_108
def expChunk_109 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_109
def expChunk_110 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_110
def expChunk_111 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_111
def expChunk_112 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_112
def expChunk_113 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_113
def expChunk_114 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_114
def expChunk_115 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_115
def expChunk_116 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_116
def expChunk_117 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_117
def expChunk_118 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_118
def expChunk_119 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_119
def expChunk_120 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_120
def expChunk_121 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_121
def expChunk_122 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_122
def expChunk_123 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_123
def expChunk_124 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_124
def expChunk_125 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_125
def expChunk_126 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_126
def expChunk_127 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_127
def expChunk_128 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_128
def expChunk_129 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_129
def expChunk_130 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_130
def expChunk_131 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_131
def expChunk_132 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_132
def expChunk_133 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_133
def expChunk_134 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_134
def expChunk_135 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_135
def expChunk_136 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_136
def expChunk_137 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_137
def expChunk_138 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_138
def expChunk_139 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_139
def expChunk_140 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_140
def expChunk_141 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_141
def expChunk_142 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_142
def expChunk_143 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_143
def expChunk_144 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_144
def expChunk_145 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_145
def expChunk_146 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_146
def expChunk_147 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_147
def expChunk_148 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_148
def expChunk_149 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_149
def expChunk_150 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_150
def expChunk_151 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_151
def expChunk_152 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_152
def expChunk_153 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_153
def expChunk_154 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_154
def expChunk_155 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_155
def expChunk_156 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_156
def expChunk_157 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_157
def expChunk_158 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_158
def expChunk_159 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_159
def expChunk_160 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_160
def expChunk_161 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_161
def expChunk_162 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_162
def expChunk_163 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_163
def expChunk_164 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_164
def expChunk_165 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_165
def expChunk_166 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_166
def expChunk_167 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_167
def expChunk_168 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_168
def expChunk_169 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandCode_169  -- pairing stage 1: installed (constructor/top-path edits)
def expChunk_170 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandCode_170  -- pairing stage 1: installed (chain step block 43764)
def expChunk_171 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_171
def expChunk_172 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_172
def expChunks : List (List (BitVec 32)) := [expChunk_4, expChunk_5, expChunk_6, expChunk_7, expChunk_8, expChunk_9, expChunk_10, expChunk_11, expChunk_12, expChunk_13, expChunk_14, expChunk_15, expChunk_16, expChunk_17, expChunk_18, expChunk_19, expChunk_20, expChunk_21, expChunk_22, expChunk_23, expChunk_24, expChunk_25, expChunk_26, expChunk_27, expChunk_28, expChunk_29, expChunk_30, expChunk_31, expChunk_32, expChunk_33, expChunk_34, expChunk_35, expChunk_36, expChunk_37, expChunk_38, expChunk_39, expChunk_40, expChunk_41, expChunk_42, expChunk_43, expChunk_44, expChunk_45, expChunk_46, expChunk_47, expChunk_48, expChunk_49, expChunk_50, expChunk_51, expChunk_52, expChunk_53, expChunk_54, expChunk_55, expChunk_56, expChunk_57, expChunk_58, expChunk_59, expChunk_60, expChunk_61, expChunk_62, expChunk_63, expChunk_64, expChunk_65, expChunk_66, expChunk_67, expChunk_68, expChunk_69, expChunk_70, expChunk_71, expChunk_72, expChunk_73, expChunk_74, expChunk_75, expChunk_76, expChunk_77, expChunk_78, expChunk_79, expChunk_80, expChunk_81, expChunk_82, expChunk_83, expChunk_84, expChunk_85, expChunk_86, expChunk_87, expChunk_88, expChunk_89, expChunk_90, expChunk_91, expChunk_92, expChunk_93, expChunk_94, expChunk_95, expChunk_96, expChunk_97, expChunk_98, expChunk_99, expChunk_100, expChunk_101, expChunk_102, expChunk_103, expChunk_104, expChunk_105, expChunk_106, expChunk_107, expChunk_108, expChunk_109, expChunk_110, expChunk_111, expChunk_112, expChunk_113, expChunk_114, expChunk_115, expChunk_116, expChunk_117, expChunk_118, expChunk_119, expChunk_120, expChunk_121, expChunk_122, expChunk_123, expChunk_124, expChunk_125, expChunk_126, expChunk_127, expChunk_128, expChunk_129, expChunk_130, expChunk_131, expChunk_132, expChunk_133, expChunk_134, expChunk_135, expChunk_136, expChunk_137, expChunk_138, expChunk_139, expChunk_140, expChunk_141, expChunk_142, expChunk_143, expChunk_144, expChunk_145, expChunk_146, expChunk_147, expChunk_148, expChunk_149, expChunk_150, expChunk_151, expChunk_152, expChunk_153, expChunk_154, expChunk_155, expChunk_156, expChunk_157, expChunk_158, expChunk_159, expChunk_160, expChunk_161, expChunk_162, expChunk_163, expChunk_164, expChunk_165, expChunk_166, expChunk_167, expChunk_168, expChunk_169, expChunk_170, expChunk_171, expChunk_172]
def lplanBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.expandPrefix_0, SigGolfCandidate.T3M.Images.expandPrefix_1, SigGolfCandidate.T3M.Images.expandPrefix_2, SigGolfCandidate.T3M.Images.expandPrefix_3, SigGolfCandidate.T3M.Images.expandPrefix_4, SigGolfCandidate.T3M.Images.expandPrefix_5].flatten
def planBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.expandPrefix_6, SigGolfCandidate.T3M.Images.expandPrefix_7, SigGolfCandidate.T3M.Images.expandPrefix_8, SigGolfCandidate.T3M.Images.expandPrefix_9].flatten
def expCostBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.expandPrefix_10, SigGolfCandidate.T3M.Images.expandPrefix_11, SigGolfCandidate.T3M.Images.expandPrefix_12, SigGolfCandidate.T3M.Images.expandPrefix_13, SigGolfCandidate.T3M.Images.expandPrefix_14, SigGolfCandidate.T3M.Images.expandPrefix_15, SigGolfCandidate.T3M.Images.expandPrefix_16, SigGolfCandidate.T3M.Images.expandPrefix_17, SigGolfCandidate.T3M.Images.expandPrefix_18, SigGolfCandidate.T3M.Images.expandPrefix_19, SigGolfCandidate.T3M.Images.expandPrefix_20, SigGolfCandidate.T3M.Images.expandPrefix_21, SigGolfCandidate.T3M.Images.expandPrefix_22, SigGolfCandidate.T3M.Images.expandPrefix_23, SigGolfCandidate.T3M.Images.expandPrefix_24, SigGolfCandidate.T3M.Images.expandPrefix_25, SigGolfCandidate.T3M.Images.expandPrefix_26, SigGolfCandidate.T3M.Images.expandPrefix_27, SigGolfCandidate.T3M.Images.expandPrefix_28, SigGolfCandidate.T3M.Images.expandPrefix_29, SigGolfCandidate.T3M.Images.expandPrefix_30, SigGolfCandidate.T3M.Images.expandPrefix_31, SigGolfCandidate.T3M.Images.expandPrefix_32, SigGolfCandidate.T3M.Images.expandPrefix_33, SigGolfCandidate.T3M.Images.expandPrefix_34, SigGolfCandidate.T3M.Images.expandPrefix_35, SigGolfCandidate.T3M.Images.expandPrefix_36, SigGolfCandidate.T3M.Images.expandPrefix_37, SigGolfCandidate.T3M.Images.expandPrefix_38, SigGolfCandidate.T3M.Images.expandPrefix_39, SigGolfCandidate.T3M.Images.expandPrefix_40, SigGolfCandidate.T3M.Images.expandPrefix_41, SigGolfCandidate.T3M.Images.expandPrefix_42, SigGolfCandidate.T3M.Images.expandPrefix_43, SigGolfCandidate.T3M.Images.expandPrefix_44, SigGolfCandidate.T3M.Images.expandPrefix_45, SigGolfCandidate.T3M.Images.expandPrefix_46, SigGolfCandidate.T3M.Images.expandPrefix_47, SigGolfCandidate.T3M.Images.expandPrefix_48, SigGolfCandidate.T3M.Images.expandPrefix_49, SigGolfCandidate.T3M.Images.expandPrefix_50, SigGolfCandidate.T3M.Images.expandPrefix_51, SigGolfCandidate.T3M.Images.expandPrefix_52, SigGolfCandidate.T3M.Images.expandPrefix_53, SigGolfCandidate.T3M.Images.expandPrefix_54, SigGolfCandidate.T3M.Images.expandPrefix_55, SigGolfCandidate.T3M.Images.expandPrefix_56, SigGolfCandidate.T3M.Images.expandPrefix_57, SigGolfCandidate.T3M.Images.expandPrefix_58, SigGolfCandidate.T3M.Images.expandPrefix_59, SigGolfCandidate.T3M.Images.expandPrefix_60, SigGolfCandidate.T3M.Images.expandPrefix_61, SigGolfCandidate.T3M.Images.expandPrefix_62, SigGolfCandidate.T3M.Images.expandPrefix_63, SigGolfCandidate.T3M.Images.expandPrefix_64, SigGolfCandidate.T3M.Images.expandPrefix_65, SigGolfCandidate.T3M.Images.expandPrefix_66, SigGolfCandidate.T3M.Images.expandPrefix_67, SigGolfCandidate.T3M.Images.expandPrefix_68, SigGolfCandidate.T3M.Images.expandPrefix_69, SigGolfCandidate.T3M.Images.expandPrefix_70, SigGolfCandidate.T3M.Images.expandPrefix_71, SigGolfCandidate.T3M.Images.expandPrefix_72, SigGolfCandidate.T3M.Images.expandPrefix_73].flatten
def hdrBankBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.expandPrefix_74, SigGolfCandidate.T3M.Images.expandPrefix_75, SigGolfCandidate.T3M.Images.expandPrefix_76, SigGolfCandidate.T3M.Images.expandPrefix_77, SigGolfCandidate.T3M.Images.expandPrefix_78, SigGolfCandidate.T3M.Images.expandPrefix_79, SigGolfCandidate.T3M.Images.expandPrefix_80, SigGolfCandidate.T3M.Images.expandPrefix_81, SigGolfCandidate.T3M.Images.expandPrefix_82, SigGolfCandidate.T3M.Images.expandPrefix_83, SigGolfCandidate.T3M.Images.expandPrefix_84, SigGolfCandidate.T3M.Images.expandPrefix_85, SigGolfCandidate.T3M.Images.expandPrefix_86, SigGolfCandidate.T3M.Images.expandPrefix_87, SigGolfCandidate.T3M.Images.expandPrefix_88, SigGolfCandidate.T3M.Images.expandPrefix_89, SigGolfCandidate.T3M.Images.expandPrefix_90, SigGolfCandidate.T3M.Images.expandPrefix_91].flatten
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_VLib ====
section

namespace ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (header pad64 zero16 Digest HashOutput HashInput)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
def cfg0 : Config := {}
def keepB (rs : List Reg) (r : PRes) : Bool := rs.all fun x => E.beq (r.st.regs.get x) (.reg x)
theorem PRes.toState_getReg (r : PRes) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := SymState.toState_getReg _ _ _ _
theorem PRes.toState_getMem (r : PRes) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl
theorem PRes.toState_pc (r : PRes) (s : MachineState) (h : r.spc = none := by rfl) :
    (r.toState s).pc = r.pc := by
  simp [PRes.toState, PRes.finalPc, h]
theorem keepB_ok {rs : List Reg} {r : PRes} (h : keepB rs r = true) (s : MachineState) :
    ∀ x ∈ rs, (r.toState s).getReg x = s.getReg x := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  rw [PRes.toState_getReg, E.beq_eq this]; rfl
theorem br_ne_zero (x : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.ne, x, .c 0, d⟩ ↔ (decide (x.eval s ≠ 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp [bne_iff_ne]
def hashArgsB (a n d : Nat) : Bool :=
  decide (a % 8 = 0) && decide (0 < n ∧ n % 64 = 0) && decide (a + n ≤ MEMORY_BYTES) &&
    decide (d + 8 ≤ MEMORY_BYTES ∧ d % 8 = 0) && decide (d + 32 ≤ MEMORY_BYTES)
theorem hashArgs_ofNat (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) (h : hashArgsB a n d = true) :
    hashArgumentsValid t = true := by
  simp only [hashArgsB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Bool.and_eq_true,
    decide_eq_true_eq]
  omega
theorem hashArgs_of (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha8 : a % 8 = 0) (hn : 0 < n ∧ n % 64 = 0) (han : a + n ≤ 2 ^ 24) (hd8 : d % 8 = 0)
    (hd : d + 32 ≤ 2 ^ 24) : hashArgumentsValid t = true :=
  hashArgs_ofNat t a n d h10 h11 h12 (by omega) (by omega) (by omega) (by
    unfold hashArgsB
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨decide_eq_true ha8, decide_eq_true hn⟩, decide_eq_true ?_⟩, decide_eq_true ⟨?_, hd8⟩⟩,
      decide_eq_true ?_⟩ <;> unfold MEMORY_BYTES <;> omega)
theorem ofNat_eq_iff' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]
theorem ofNat_ne' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun h' => h ((ofNat_eq_iff' ha hb).mp h')
theorem memEval_cons_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  have e : Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ = BitVec.ofNat 64 k := rfl
  by_cases h : A = k
  · subst h; rw [if_pos e.symm, if_pos rfl]
  · have hne : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ := by
      rw [e]; exact ofNat_ne' hA hk h
    rw [if_neg hne, if_neg h]
abbrev dlo (d : BitVec 128) : Word := d.extractLsb' 0 64
abbrev dhi (d : BitVec 128) : Word := d.extractLsb' 64 64
def blk4 (a b c d : BitVec 128) : List UInt8 := bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c ++ bytesLE 16 d
theorem blk4_length (a b c d : BitVec 128) : (blk4 a b c d).length = 64 := by
  simp only [blk4, List.length_append, bytesLE_length]
theorem pad64_blk4 (a b c d : BitVec 128) : pad64 (blk4 a b c d) = blk4 a b c d :=
  pad64_of_aligned _ (by rw [blk4_length])
theorem wordsOf_blk4 (a b c d : BitVec 128) :
    wordsOf (blk4 a b c d) = [dlo a, dhi a, dlo b, dhi b, dlo c, dhi c, dlo d, dhi d] := by
  unfold blk4
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  rfl
theorem aligned_blk4 (a b c d : BitVec 128) : Aligned (blk4 a b c d) := by
  rw [Aligned, blk4_length]; omega
theorem blocks_blk4 (a b c d : BitVec 128) : (toQ (pad64 (blk4 a b c d))).blocks = 1 := by
  rw [pad64_blk4, blocks_toQ (aligned_blk4 a b c d), blk4_length]
theorem bytesLE16_zero : bytesLE 16 (0 : BitVec 128) = zero16 := by decide
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)
theorem sum_map_16 : ∀ l : List Digest, (l.map fun _ => (16 : Nat)).sum = 16 * l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_map_16 l, List.length_cons]; ring
theorem forestInput_length (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    (forestInput index roots).length = 128 := by
  unfold forestInput
  simp only [List.length_append, bytesLE_length, List.length_flatMap]
  rw [sum_map_16, List.length_drop, h]
theorem readWords_ofNat (t : MachineState) (a : Nat) : ∀ m, a + 8 * m < 2 ^ 64 →
    t.readWords (BitVec.ofNat 64 a) m =
      (List.range m).map fun j => t.getMem (BitVec.ofNat 64 (a + 8 * j)) := by
  intro m
  induction m generalizing a with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [MachineState.readWords_succ, ofNat_add8, ih (a + 8) (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    congr 2; omega
theorem readWords_eight' (t : MachineState) (A : Nat) (hA : A + 64 < 2 ^ 64) :
    t.readWords (BitVec.ofNat 64 A) 8 =
      [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] := by
  rw [readWords_ofNat t A 8 (by omega)]
  rfl
theorem hashInput_words8 (t : MachineState) (l : List UInt8) (A : Nat) (hl : l.length = 64)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hw : [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] = wordsOf l) :
    hashInput t = toQ l :=
  hashInput_toQ t l 0 A hl h10 hA (by omega) h11 (by norm_num) (by rw [readWords_eight' t A hA']; exact hw)
theorem writeHash_getReg (s : MachineState) (ans : BitVec 256) (r : Reg) :
    (writeHash s ans).getReg r = s.getReg r := getReg_writeHash s ans r
theorem writeHash_pc (s : MachineState) (ans : BitVec 256) :
    (writeHash s ans).pc = s.pc + 4 := pc_writeHash s ans
theorem writeHash_lo (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = dlo (ans.extractLsb' 0 128) ∧
      (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = dhi (ans.extractLsb' 0 128) :=
  DigAt.writeHash_lo t ans d hd hd'
theorem replaceByte_toNat (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
theorem foldl_append_flatten : ∀ (l : List (List (BitVec 32))) (a : List (BitVec 32)),
    l.foldl (· ++ ·) a = a ++ l.flatten
  | [], a => by simp
  | c :: l, a => by simp [foldl_append_flatten l (a ++ c)]
theorem drop_chunks {α : Type} (B : Nat) : ∀ (cs : List (List α)) (k : Nat),
    (cs.dropLast.all fun c => c.length == B) = true → k < cs.length →
    cs.flatten.drop (B * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = B := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == B) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show B * (k + 1) = c.length + B * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this
end ClaudeWCT.W9.Machine.VLib
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Fetch ====
section

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
def NewCodeAt (im : Image) : Prop :=
  ∀ c, c < 169 → CodeAt im (pcOf (256 * (c + 4))) (expChunks.getD c [])
def expLook (n : Nat) : Option (BitVec 32) :=
  if 1024 ≤ n then (expChunks.getD (n / 256 - 4) [])[n % 256]? else none
set_option maxRecDepth 100000 in
theorem expChunks_length : expChunks.length = 169 := by decide +kernel
set_option maxRecDepth 100000 in
theorem expChunks_len_le : ∀ c, c < 169 → (expChunks.getD c []).length ≤ 256 := by decide +kernel
theorem expLook_ok {im : Image} (h : NewCodeAt im) : LookOK im expLook := by
  intro n w hw
  unfold expLook at hw
  split at hw
  · rename_i hn
    have hc : n / 256 - 4 < 169 := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by rw [expChunks_length]; omega)] at hw
      simp at hw
    obtain ⟨h1, h2, h3, h4⟩ := h (n / 256 - 4) hc
    have hpc : (pcOf (256 * (n / 256 - 4 + 4))).toNat = 0x1000 + 4 * (256 * (n / 256)) := by
      rw [show n / 256 - 4 + 4 = n / 256 by omega, pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have : expLook n = some w := by unfold expLook; rw [if_pos hn]; exact hw
      have hl := List.getElem?_eq_some_iff.mp hw
      have hlen : (expChunks.getD (n / 256 - 4) []).length ≤ 256 := by
        exact expChunks_len_le _ hc
      omega
    rw [hpc] at h4 h3
    obtain ⟨t, ht⟩ := h4
    have := congrArg (·[n % 256]?) ht
    simp only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hw).1, hw,
      List.getElem?_drop] at this
    rw [show 0x1000 + 4 * (256 * (n / 256)) - 0x1000 = 4 * (256 * (n / 256)) by omega,
      show 4 * (256 * (n / 256)) / 4 + n % 256 = n by omega] at this
    exact this.symm
  · cases hw
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_WitV5 ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.T3 (HashOutput Layer height chainCount)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap_const window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3 (LayerSignature route)
open SigGolfCandidate.T3M (layerBytes)
open ClaudeWCT.W9.T3M (headerBytes chainBytes leafBytes regionBytes)
def bcTopBlockV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  if leaf / 2 ^ (height lay - 1) % 2 = 1 then
    bytesLE 16 (ls.path (WCT9.topLevel lay)) ++ zeros 16 ++ bytesLE 4 ctr ++ zeros 28
  else zeros 32 ++ bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path (WCT9.topLevel lay))
def layerBytesBCV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  bcTopBlockV6 lay leaf ls ctr ++ (layerBytes lay leaf ls).drop 64
/-- T51: chain blocks of a staging region. The top keeps #938's 54 blocks (chain `i` at block `53 - i` below the
path blocks; the blocks of chains 51..53 are never written and stay zero). -/
def chainSlotsV6 (lay : Layer) : Nat := if lay.val = 0 then 54 else chainCount lay
theorem chainSlotsV6_lower (lay : Layer) (hl : lay.val ≠ 0) : chainSlotsV6 lay = chainCount lay := by
  simp [chainSlotsV6, hl]
theorem chainSlotsV6_ge (lay : Layer) : chainCount lay ≤ chainSlotsV6 lay := by
  fin_cases lay <;> decide
/-- T51: a staging region without its counter block. The top inserts the 3 zero blocks of #938's chains 51..53
between its 12 path blocks and its 51 chain blocks. -/
def layerBytesV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  if lay.val = 0 then (layerBytes lay leaf ls).take 768 ++ zeros 192 ++ (layerBytes lay leaf ls).drop 768
  else layerBytes lay leaf ls
def layerRegionV6 (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then layerBytesV6 lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
  else layerBytesBCV6 lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
    (w.counters (Fin.ofNat 4 (lay.val - 1)))
/-- Staging region of the compaction pass (896 bytes). r3w (witness stack): the FTS content of the staging is dead
(the finish pass zeroes `[1152, 11000)` and rebuilds the FTS block from the signature), so only its length matters. -/
def regionBytesV6 (_child : Nat) (_op : WCT9.Opening) : List UInt8 := zeros 896
/-- Header of the first-pass scratch layout at 0x800 (the frontier's 64-byte header: rho, digest counter, L3
counter). Machine internal; the final witness uses `ClaudeWCT.W9.T3M.headerBytes`. -/
def headerBytesV5 (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3) ++ zeros 28
theorem headerBytesV5_length (w : WCT9.Witness) : (headerBytesV5 w).length = 64 := by
  simp [headerBytesV5, zeros, bytesLE_length]
def wctBytesV6 (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytesV6 (WCT9.child N k).val (sig.openings k)
def witListV6 (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytesV5 w ++ wctBytesV6 N w.signature ++ zeros 8 ++ (List.finRange 4).flatMap (layerRegionV6 N w)
def merkleBytesV5 (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 7).reverse.flatMap fun l =>
    if child / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48 else zeros 48 ++ bytesLE 16 (op.path l)
/-- Expand scratch region (1024 bytes). r3w: dead FTS content (see `regionBytesV6`); only the length matters. -/
def regionBytesV5 (_child : Nat) (_op : WCT9.Opening) : List UInt8 := zeros 1024
def wctBytesV5 (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytesV5 (WCT9.child N k).val (sig.openings k)
def witListV5 (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytesV5 w ++ wctBytesV5 N w.signature ++ zeros 8 ++ (List.finRange 4).flatMap (layerRegionV6 N w)
theorem leafBytesZ_length (op : WCT9.Opening) : (ClaudeWCT.W9.T3M.leafBytes op (zeros 16)).length = 128 :=
  ClaudeWCT.W9.T3M.leafBytes_length _ _ (by simp [zeros])
theorem leafBytesZ_length' (op : WCT9.Opening) :
    (ClaudeWCT.W9.T3M.leafBytes op (List.replicate 16 0)).length = 128 :=
  ClaudeWCT.W9.T3M.leafBytes_length _ _ (by simp)
theorem merkleBytesV5_length (c : Nat) (op : WCT9.Opening) : (merkleBytesV5 c op).length = 448 := by
  unfold merkleBytesV5
  rw [List.length_flatMap]
  have : ∀ l : Fin 7, (if c / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (op.path l)).length = 64 := fun l => by
    split <;> simp [zeros, bytesLE_length]
  simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem regionBytesV5_length (c : Nat) (op : WCT9.Opening) : (regionBytesV5 c op).length = 1024 := by
  simp only [regionBytesV5, zeros, List.length_replicate]
theorem wctBytesV5_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytesV5 N sig).length = 9216 := by
  unfold wctBytesV5
  rw [List.length_flatMap]
  simp only [regionBytesV5_length, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem bcTopBlockV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (bcTopBlockV6 lay leaf ls ctr).length = 64 := by
  unfold bcTopBlockV6; split <;> simp [zeros, bytesLE_length]
theorem height_pos (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem layerBytesBCV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (layerBytesBCV6 lay leaf ls ctr).length = 64 * (height lay + chainCount lay) := by
  unfold layerBytesBCV6
  rw [List.length_append, bcTopBlockV6_length, List.length_drop, SigGolfCandidate.T3M.layerBytes_length]
  have := height_pos lay
  have : 64 ≤ 64 * (height lay + chainCount lay) := by nlinarith
  omega
theorem layerBytesV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerBytesV6 lay leaf ls).length = 64 * (height lay + chainSlotsV6 lay) := by
  unfold layerBytesV6 chainSlotsV6
  split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    have e1 : (zeros 192 : List UInt8).length = 192 := List.length_replicate ..
    have h1 : height (0 : Layer) = 12 := rfl
    have h2 : chainCount (0 : Layer) = 51 := rfl
    rw [List.length_append, List.length_append, List.length_take, List.length_drop,
      SigGolfCandidate.T3M.layerBytes_length, e1, h1, h2]
    simp
  · rw [SigGolfCandidate.T3M.layerBytes_length]
theorem layerRegionV6_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegionV6 N w lay).length = 64 * (height lay + chainSlotsV6 lay) := by
  unfold layerRegionV6; split
  · exact layerBytesV6_length _ _ _
  · rename_i h
    rw [layerBytesBCV6_length]
    simp [chainSlotsV6, h]
theorem layersV6_length (N : HashOutput) (w : WCT9.Witness) :
    ((List.finRange 4).flatMap (layerRegionV6 N w)).length = 13696 := by
  simp only [List.length_flatMap, layerRegionV6_length]
  decide

theorem witListV5_length (N : HashOutput) (w : WCT9.Witness) : (witListV5 N w).length = 22984 := by
  unfold witListV5
  simp only [List.length_append, headerBytesV5_length, wctBytesV5_length, zeros,
    List.length_replicate, layersV6_length]
theorem regionBytesV6_length (c : Nat) (op : WCT9.Opening) : (regionBytesV6 c op).length = 896 := by
  simp only [regionBytesV6, zeros, List.length_replicate]
theorem wctBytesV6_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytesV6 N sig).length = 8064 := by
  unfold wctBytesV6
  rw [List.length_flatMap]
  simp only [regionBytesV6_length, List.map_const', List.length_finRange, List.sum_replicate,
    smul_eq_mul]
theorem witListV6_length (N : HashOutput) (w : WCT9.Witness) : (witListV6 N w).length = 21832 := by
  unfold witListV6
  simp only [List.length_append, headerBytesV5_length, wctBytesV6_length, zeros,
    List.length_replicate, layersV6_length]
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from T3M_Sign_Basic ====
section


section
namespace SigGolfCandidate.T3M
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def signCurrentCodeChunks : List (List (BitVec 32)) := [Images.signCode_0, Images.signCode_1, Images.signCode_2, Images.signCode_3, Images.signCode_4, Images.signCode_5, Images.signCode_6, Images.signCode_7, Images.signCode_8, Images.signCode_9, Images.signCode_10, Images.signCode_11, Images.signCode_12, Images.signCode_13, Images.signCode_14, Images.signCode_15, Images.signCode_16, Images.signCode_17, Images.signCode_18, Images.signCode_19, Images.signCode_20, Images.signCode_21, Images.signCode_22, Images.signCode_23, Images.signCode_24, Images.signCode_25, Images.signCode_26, Images.signCode_27, Images.signCode_28, Images.signCode_29, Images.signCode_30, Images.signCode_31, Images.signCode_32, Images.signCode_33, Images.signCode_34, Images.signCode_35, Images.signCode_36, Images.signCode_37, Images.signCode_38, Images.signCode_39, Images.signCode_40, Images.signCode_41, Images.signCode_42, Images.signCode_43, Images.signCode_44, Images.signCode_45, Images.signCode_46, Images.signCode_47, Images.signCode_48, Images.signCode_49, Images.signCode_50, Images.signCode_51, Images.signCode_52, Images.signCode_53, Images.signCode_54, Images.signCode_55, Images.signCode_56, Images.signCode_57, Images.signCode_58, Images.signCode_59, Images.signCode_60, Images.signCode_61, Images.signCode_62, Images.signCode_63, Images.signCode_64, Images.signCode_65, Images.signCode_66, Images.signCode_67, Images.signCode_68, Images.signCode_69, Images.signCode_70, Images.signCode_71, Images.signCode_72, Images.signCode_73, Images.signCode_74, Images.signCode_75, Images.signCode_76, Images.signCode_77, Images.signCode_78, Images.signCode_79, Images.signCode_80, Images.signCode_81, Images.signCode_82, Images.signCode_83, Images.signCode_84, Images.signCode_85]
private theorem foldl_chunks (cs : List (List (BitVec 32))) (acc : List (BitVec 32)) :
    cs.foldl (· ++ ·) acc = acc ++ cs.flatten := by
  induction cs generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
  | cons c cs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]
theorem signCurrentCode_flatten : Images.signCode = signCurrentCodeChunks.flatten := by
  change signCurrentCodeChunks.foldl (· ++ ·) [] = signCurrentCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_sign_current_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (signCurrentCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.signImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.signCode.drop b).take code.length = code
  rw [signCurrentCode_flatten]
  exact h
/-- The final chunk carries the appended roots-first producer without changing old addresses. -/
private theorem signCurrentCodeChunks_prefix_length :
    (signCurrentCodeChunks.take 85).flatten.length = 21760 := by
  set_option maxRecDepth 100000 in decide +kernel

theorem signCodeTailLast_eq (b : Nat) (hlo : 21760 ≤ b) :
    Images.signCode_85.drop (b - 21760) = signCurrentCodeChunks.flatten.drop b := by
  have hs : signCurrentCodeChunks = signCurrentCodeChunks.take 85 ++ [Images.signCode_85] := by rfl
  have he : signCurrentCodeChunks.flatten.drop 21760 = Images.signCode_85 := by
    conv_lhs => rw [hs]
    rw [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← signCurrentCodeChunks_prefix_length, List.drop_left]
  rw [show b = 21760 + (b - 21760) by omega, ← List.drop_drop, he]
  simp only [Nat.add_sub_cancel_left]

theorem codeAt_sign_last {b : Nat} {code : List (BitVec 32)}
    (hlo : 21760 ≤ b) (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (hc : (Images.signCode_85.drop (b - 21760)).take code.length = code) :
    CodeAt Images.signImage (pcOf b) code := by
  apply codeAt_sign_current_slice hb
  rw [← signCodeTailLast_eq b hlo]
  exact hc

theorem codeAt_sign_shared_prefix :
    CodeAt Images.signImage (pcOf 22016) Images.signSharedPrefix := by
  apply codeAt_sign_last <;> decide +kernel

theorem codeAt_sign_shared_main :
    CodeAt Images.signImage (pcOf 22100) Images.signSharedMain := by
  apply codeAt_sign_last <;> decide +kernel

theorem codeAt_sign_shared_fts :
    CodeAt Images.signImage (pcOf 22600) Images.signSharedFts := by
  apply codeAt_sign_last <;> decide +kernel

def signCodeChunks : List (List (BitVec 32)) := [Images.signReferenceCode_0, Images.signReferenceCode_1, Images.signReferenceCode_2, Images.signReferenceCode_3, Images.signReferenceCode_4, Images.signReferenceCode_5, Images.signReferenceCode_6, Images.signReferenceCode_7, Images.signReferenceCode_8, Images.signReferenceCode_9, Images.signReferenceCode_10, Images.signReferenceCode_11, Images.signReferenceCode_12, Images.signReferenceCode_13, Images.signReferenceCode_14, Images.signReferenceCode_15, Images.signReferenceCode_16, Images.signReferenceCode_17, Images.signReferenceCode_18, Images.signReferenceCode_19, Images.signReferenceCode_20, Images.signReferenceCode_21, Images.signReferenceCode_22, Images.signReferenceCode_23, Images.signReferenceCode_24, Images.signReferenceCode_25, Images.signReferenceCode_26, Images.signReferenceCode_27, Images.signReferenceCode_28, Images.signReferenceCode_29, Images.signReferenceCode_30, Images.signReferenceCode_31, Images.signReferenceCode_32, Images.signReferenceCode_33, Images.signReferenceCode_34, Images.signReferenceCode_35, Images.signReferenceCode_36, Images.signReferenceCode_37, Images.signReferenceCode_38, Images.signReferenceCode_39, Images.signReferenceCode_40, Images.signReferenceCode_41, Images.signReferenceCode_42, Images.signReferenceCode_43, Images.signReferenceCode_44, Images.signReferenceCode_45, Images.signReferenceCode_46, Images.signReferenceCode_47, Images.signReferenceCode_48, Images.signReferenceCode_49, Images.signReferenceCode_50, Images.signReferenceCode_51, Images.signReferenceCode_52, Images.signReferenceCode_53, Images.signReferenceCode_54, Images.signReferenceCode_55, Images.signReferenceCode_56, Images.signReferenceCode_57, Images.signReferenceCode_58, Images.signReferenceCode_59, Images.signReferenceCode_60, Images.signReferenceCode_61, Images.signReferenceCode_62, Images.signReferenceCode_63, Images.signReferenceCode_64, Images.signReferenceCode_65, Images.signReferenceCode_66, Images.signReferenceCode_67, Images.signReferenceCode_68, Images.signReferenceCode_69, Images.signReferenceCode_70, Images.signReferenceCode_71, Images.signReferenceCode_72, Images.signReferenceCode_73, Images.signReferenceCode_74, Images.signReferenceCode_75, Images.signReferenceCode_76, Images.signReferenceCode_77, Images.signReferenceCode_78, Images.signReferenceCode_79, Images.signReferenceCode_80, Images.signReferenceCode_81, Images.signReferenceCode_82, Images.signReferenceCode_83, Images.signReferenceCode_84, Images.signReferenceCode_85]
theorem signCode_flatten : Images.signReferenceCode = signCodeChunks.flatten := by
  change signCodeChunks.foldl (· ++ ·) [] = signCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_sign_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (signCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.signReferenceImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.signReferenceCode.drop b).take code.length = code
  rw [signCode_flatten]
  exact h
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def seg_0 : List (BitVec 32) := [659,528055,134967,1074728723,963331,9352067,7286819,8336419,528055,17731219,134967,1091505939,963331,9352067,7286819,8336419,784339055]
def seg_46 : List (BitVec 32) := [115]
def seg_47 : List (BitVec 32) := [134711,1041108499,134839,1074695827,930563,963459,2054362211]
def seg_54 : List (BitVec 32) := [9319171,9352067,2020810339]
def seg_57 : List (BitVec 32) := [17707779,17740675,2020808803]
def seg_60 : List (BitVec 32) := [26096387,26129283,2020807267]
def seg_63 : List (BitVec 32) := [134221459,134967,963331,9352067,7286819,8336419,150998675,134967,34541331,963331,9352067,7286819,8336419,134967,34551843,34552867,134221459,134967,135204627,963331,9352067,7286819,8336419,150998675,134967,168759059,963331,9352067,7286819,8336419,134967,135204627,34551843,34552867,1880097555,915,134711,135138835,7223331,8272931,28343,134967,202313491,1645130499,1653519235,7286819,8336419,28343,134967,219090707,1661907715,1670296451,7286819,8336419,132407,134546707,134219155,132663,268830227]
def seg_122 : List (BitVec 32) := [115]
def seg_123 : List (BitVec 32) := [134839,269389459,32567,963331,9352067,7286819,8336419,134839,269389459,134967,302976787,963331,9352067,7286819,8336419,28343,134967,336531219,1645130499,1653519235,7286819,8336419,28343,134967,353308435,1661907715,1670296451,7286819,8336419,2451]
def seg_153 : List (BitVec 32) := [412131439,1617529443]
def seg_155 : List (BitVec 32) := [4919,787,627603,134711,302910995,7223331,8272931,132407,302318867,67110291,132663,369493523]
def seg_167 : List (BitVec 32) := [115]
def seg_168 : List (BitVec 32) := [121639151]
def seg_169 : List (BitVec 32) := [431715]
def seg_170 : List (BitVec 32) := [1673619,4221562991]
def seg_172 : List (BitVec 32) := [134711,370019859,930947,34903187,34919571,134711,1426984467,10367011,196919,30775,369625107,32055,17632531,1043]
def seg_186 : List (BitVec 32) := [7340819,711218275]
def seg_188 : List (BitVec 32) := [2323]
def seg_189 : List (BitVec 32) := [4919,2147681043,241784419]
def seg_192 : List (BitVec 32) := [1667859,67310691]
def seg_194 : List (BitVec 32) := [1662483,4919,2148729619,17047315,31679283,295827,34479891,31712179,134711,7223331,8272931,4791827,263735,29754931,132407,67110291]
def seg_210 : List (BitVec 32) := [115]
def seg_211 : List (BitVec 32) := [4791827,265911,31329843,134967,772738835,930563,9319299,7286819,8336419,4919,2417165075,17047315,31679283,1196429423]
def seg_225 : List (BitVec 32) := [33857299,31679283,134711,739118611,7223331,8272931,132407,738526483,67110291,132663,805701139]
def seg_236 : List (BitVec 32) := [115]
def seg_237 : List (BitVec 32) := [7735,2148404755,19795507,5119507,3018291,134839,806260371,963331,9352067,7221283,8270883,1640723,4045402223]
def seg_250 : List (BitVec 32) := [11536275,6839,2686093971,17047315,32172723,1506803951]
def seg_256 : List (BitVec 32) := [4461331,3412883,7537459,134327,1242336403,7113907,2451]
def seg_263 : List (BitVec 32) := [3146515,40492131]
def seg_265 : List (BitVec 32) := [3773203,26411827,209667,4395795,263095,7540275,930563,9319299,7155747,8205347,17632531,1673619,4238340207]
def seg_278 : List (BitVec 32) := [7342995,2451]
def seg_280 : List (BitVec 32) := [3146515,208262243]
def seg_282 : List (BitVec 32) := [3773203,26411827,211459,5047,2147713939,7998003,2707,2098067,7965283]
def seg_291 : List (BitVec 32) := [8600195,5047,2147713939,8030899]
def seg_295 : List (BitVec 32) := [756499]
def seg_296 : List (BitVec 32) := [34278499]
def seg_297 : List (BitVec 32) := [4294642451,23745331,1274771,4261644515]
def seg_301 : List (BitVec 32) := [1262355,4398611,3018291,930563,9319299,6828067,7877667,17303571,4242534511]
def seg_310 : List (BitVec 32) := [2835]
def seg_311 : List (BitVec 32) := [7340819,74141795]
def seg_313 : List (BitVec 32) := [23745331,1274771,33789539]
def seg_316 : List (BitVec 32) := [1262355,23778227,40076387]
def seg_319 : List (BitVec 32) := [4398611,3018291,930563,9319299,6828067,7877667,17303571]
def seg_326 : List (BitVec 32) := [1772307,4229951599]
def seg_328 : List (BitVec 32) := [723859,1673619,4087345263]
def seg_331 : List (BitVec 32) := [7342867]
def seg_332 : List (BitVec 32) := [11535123,40589411]
def seg_334 : List (BitVec 32) := [23745331,1262355,4398611,3018291,930563,9319299,6828067,7877667,17303571,1772307,4246728815]
def seg_345 : List (BitVec 32) := [4464147,263267]
def seg_347 : List (BitVec 32) := [17698323]
def seg_348 : List (BitVec 32) := [134839,839814803,31329843,16855811,25244547,7221283,8270883,1311763,3584028783]
def seg_357 : List (BitVec 32) := [4919,2954035987,295827,134711,839781907,7223331,8272931,132407,839189779,134219155,132663,973473299]
def seg_369 : List (BitVec 32) := [115]
def seg_370 : List (BitVec 32) := [134839,974032531,134967,638521107,963331,9352067,7286819,8336419,135479,3987,45092115,3475,3146771,6293395,34871,772278291,211814547,134711,1426984467,930563,218003,66063891,29620531,591635,6509715,1052770543]
def seg_396 : List (BitVec 32) := [1112539375]
def seg_397 : List (BitVec 32) := [2098195,6293395,34871,4245162003,211814547,134711,1426984467,930563,6509459,66063891,29620531,591635,12801171,989855983]
def seg_411 : List (BitVec 32) := [1049624815]
def seg_412 : List (BitVec 32) := [1049619,7341971,34871,3406301203,210765971,134711,1426984467,930563,12800915,133172755,29620531,591635,20141203,926941423]
def seg_426 : List (BitVec 32) := [986710255]
def seg_427 : List (BitVec 32) := [1043,1171,56626451,53480851,152045715,134711,1426984467,930563,20140947,7735,4294839827,29620531,591635,864026863]
def seg_441 : List (BitVec 32) := [1052563,133943,1108019987,35767,2299235219,344981743]
def seg_447 : List (BitVec 32) := [1989148783]
def seg_456 : List (BitVec 32) := [1530131,1657107,1644819,138167,2685111187,134327,537693331,273678575]
def seg_464 : List (BitVec 32) := [1640723,138167,2685111187,134327,588024979,248512751]
def seg_470 : List (BitVec 32) := [1662483,5047,2147713939,8261171,806355731,918419,134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
def seg_485 : List (BitVec 32) := [115]
def seg_486 : List (BitVec 32) := [134839,604933779,36663,3289321235,963331,9352067,7286819,8336419,2099987,35895,3305901075,1073744403]
def seg_498 : List (BitVec 32) := [12583699,174805603]
def seg_500 : List (BitVec 32) := [23551539,1986067,4919,3490906899,34283283,31679283,34476947,134711,7223331,8272931,132407,67110291,132663,101058067]
def seg_514 : List (BitVec 32) := [115]
def seg_515 : List (BitVec 32) := [23548723,1262355,5047,2147713939,7537459,1711635,1103299379,4395795,37815,33784723,7537459,209795,8601091,134839,101617299,963331,9354883,6538163,31346227,8138787,30159907,17566739,1726995,1772307,4125093999]
def seg_540 : List (BitVec 32) := [932261999,1299]
def seg_542 : List (BitVec 32) := [115]
def seg_1173 : List (BitVec 32) := [33299,1683]
def seg_1175 : List (BitVec 32) := [1049363,15930163,73846883]
def seg_1178 : List (BitVec 32) := [428307,133943,1175128851,138167,2685111187,15112291]
def seg_1184 : List (BitVec 32) := [133943,1108019987,527251]
def seg_1187 : List (BitVec 32) := [13829043,4428691,2329779,3667914991]
def seg_1191 : List (BitVec 32) := [1476243,4225757295]
def seg_1193 : List (BitVec 32) := [1463812207,19,4007653615]
def seg_1196 : List (BitVec 32) := [1683,1049363,15930163,14879155,5051283,7867443]
def seg_1202 : List (BitVec 32) := [49731683]
def seg_1203 : List (BitVec 32) := [14278195,1986067,5119507,3018291,930563,9319299,7090211,8139811,17566739,1476243,4250923119]
def seg_1214 : List (BitVec 32) := [134967,638521107,210800751,25244547,7286819,8336419,131175]
def seg_543 : List (BitVec 32) := [1049235,1049875]
def seg_545 : List (BitVec 32) := [115]
def ker_546 : List (BitVec 32) := [22022803,2579,134327,0x4a0c8c93,7340819,376066659,5903123,3806099,0x40730333,21168947,32703251,6509459,3380115,134711,370019859,29590451,245251,8633987,66286355,7233075,2006675,66061203,0x406383b3,8298163,31354419,33555383,0xfff38393,8289843,0xfe7313,7541523,5135123,0x7fb7b13,0xbe5b93,0x7fbfb93,19815443,0x7fc7c13,23844963,721811,756499,232339,24926307,754579,789395,232467,23844963,721811,756499,232339,0xd7b0463,0xd8b8263,24855475,8392211,2342547,0x41de0e33,4439699,0x41de0e33,8634003,0x41de0e33,17022611,0x41de0e33,33799827,0x41de0e33,67354259,0x41de0e33,0x803be93,0x41de0e33,30050995,25936819,8392211,2342547,0x41de0e33,4439699,0x41de0e33,8634003,0x41de0e33,17022611,0x41de0e33,33799827,0x41de0e33,67354259,0x41de0e33,0x803be93,0x41de0e33,30050995,4885139,23266227,8171555,24314803,8172579,25363379,8173603,25988243,1706515,0xe9dff06f,0x7400313,7001699,1050259,32871,1683,32871,0x5790006f,0x6911306f,19,19,19,19,19,19,19,2451,617689199,0x4c698c63,134711,638455315,54403107,132407,637863187,67110291,132663,705037843,115,134711,705564179,930563,9319299,3219,0x540406e3,0x4851306f,0x540e5263,7568915,30182579,3366419,8289811,30182579,6512147,8289811,30182579,9657875,8289811,30182579,0xc35e13,8289811,30182579,0xf35e13,8289811,30182579,19095059,8289811,30182579,22240787,8289811,30182579,25386515,8289811,30182579,28532243,8289811,30182579,31677971,8289811,30182579,34823699,8289811,30182579,37969427,8289811,30182579,41115155,8289811,30182579,44260883,8289811,30182579,47406611,8289811,30182579,50552339,8289811,30182579,53698067,8289811,30182579,56843795,8289811,30182579,59989523,8289811,30182579,63135251,8289811,30182579,7601683,30182579,3399187,8289811,30182579,6544915,8289811,30182579,9690643,8289811,30182579,0xc3de13,8289811,30182579,0xf3de13,8289811,30182579,19127827,8289811,30182579,22273555,8289811,30182579,25419283,8289811,30182579,28565011,8289811,30182579,31710739,8289811,30182579,34856467,8289811,30182579,38002195,8289811,30182579,41147923,8289811,30182579,44293651,8289811,30182579,47439379,8289811,30182579,50585107,8289811,30182579,53730835,8289811,30182579,56876563,8289811,30182579,60022291,8289811,30182579,63168019,8289811,30182579,0x41988e33,8392339,903771235,0x10d1306f,19,19,19,0x13,0x13,0xffff37,200211,0x7fe7e93,32411315,969859,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,1285779,30338611,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7e7e93,31231155,0x3e5e93,0x7efe93,31231155,0x3d3de93,31231155,0x411c8eb3,0xbe0e9ee3,0x7591306f,133815,0x420a8a93,0x80f0f13,0x7f37e13,3022355,32378419,945795,31096867,9363091,31096995,9363091,31097123,7557907,60005907,29582131,7590803,3836563,1706515,18497043,0xfc0e10e3,0x737e13,0x1ca8123,0x335313,0x737e13,0x1ca8023,0x335313,0x737e13,0x1ca80a3,0x8067,197907,230803,1555,17828371,0x7f57e13,3022355,32378419,0x83e4e03,29754931,7689491,60136979,29713715,7722387,0xfffa0a13,0xfc0a1ce3,0x757e13,0xffae0e13,1981971,29754931,0x355513,0x757e13,0xffae0e13,1981971,29754931,0x355513,0xffa50e13,1981971,29754931,9846291,0xa0e1e63,2579,0xf11ff06f,0x960410e3,0xffff37,662654467,0x940e0ae3,663696131,672084867,0x8100c93,2579,0xeedff06f,1281555,66985491,29573939,1282963,2347923,854675,263267,0xfffd0a93,2579,89806435,7343635,3149459,28989027,3149331,2100883,29589299,134711,0x420e0e13,21892659,32374819,30626611,67112467,0x41de0e33,29597235,29582131,30659507,1706515,0xfb9ff06f,265315,0x41988e33,134839,0x420e8e93,22974131,30310435,0x8067,1673619,0x4bc1306f]
def seg_1221 : List (BitVec 32) := [131895,394474243,14897939,7566099,3993179747,3591368815]
def seg_17 : List (BitVec 32) := [40759,4262399763,963331,9352067,7286819,8336419,150998675,40759,963331,9352067,7286819,8336419,40759,4262399763,34551843,34552867,4919,3759342355,915,40503,4262333971,7223331,8272931,38199,4261741843,34231,67470739,132663,1040582163]
def seg_448 : List (BitVec 32) := [133943,1175128851,138167,2685111187,36023,3272379539,1526035,307233007]
def seg_1227 : List (BitVec 32) := [134711,921107,3767,135171731,963331,7221283,9351939,7222307,17740547,40775715,26129155,40776739,34486307,34487331,4919,3759342355,7223331,932899,132407,328979,67110291,460343,394771,115,1049363,33755923,7224355,460343,33949203,115,4293921043,3758355,657847,625043,461623,723731,134327,1041009811,736131,19659699,9124867,526007,33982099,1811,452483,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,4181106403,64444307,19363635,16189235,19351475,1554323,4294412179,16217907,25626419,15511587,17500947,736131,19659699,9124867,526007,33982099,1811,452483,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,4181106403,64444307,19363635,16189235,19351475,1554323,4294412179,16217907,25626419,15512611,17500947,736131,19659699,9124867,526007,33982099,1811,452483,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,4181106403,64444307,19363635,16189235,19351475,1554323,4294412179,16217907,25626419,15513635,17500947,736131,19659699,9124867,526007,33982099,1811,452483,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,4181106403,64444307,19363635,16189235,19351475,1554323,4294412179,16217907,25626419,15514659]
def seg_1432 : List (BitVec 32) := [2782912623]
def seg_1433 : List (BitVec 32) := [2835,35895,3205237779,6711,657939]
def seg_1438 : List (BitVec 32) := [23551539,1986067,920467,4919,3490906899,34280339,7562035,1823635,33788819,134711,921107,7223331,8272931,132407,328979,67110291,132663,101058067]
def seg_1456 : List (BitVec 32) := [115]
def seg_1457 : List (BitVec 32) := [11831,921107,1711763,1105071667,25038387,5119507,528055,34508435,31329843,1834643,5152403,13536947,930563,963459,7553843,7090211,9319171,9352067,7553843,7091235,17566739,1726995,1772307,12583699,4100680419]
def seg_1482 : List (BitVec 32) := [2492461167]
def kerCode : List (BitVec 32) := seg_543 ++ seg_545 ++ ker_546
/-- Campaign T8D (NF17): the sign's max-digit selector at 2013 (`li s5,7; bge s3,s11; li s5,4; j`): top chains
`< 51` have maximum digit 4, chains 51..53 (radix 8) maximum digit 7. The keygen keeps its own `Keygen.maxLow`. -/
def maxLowS : List (BitVec 32) := [0x700a93,0x99b9d663]
def maxLayoutS : Rv.Layout := [(0, maxLowS), (2, Keygen.maxHigh)]
def maxDigitCodeS : List (BitVec 32) := layoutCode maxLayoutS
theorem maxLayoutS_ok : layoutOk 0 maxLayoutS = true := by decide +kernel
def seg_2045 : List (BitVec 32) := [1074332563,1073972115,267648787,9379603,8639379,31712179,7735,4043181587,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,1432227347,29622067,2039571,1299347,29619123,31712179,50566035,2987384943]
def seg_1483 : List (BitVec 32) := Keygen.packedHelper ++ List.drop 25 [0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013]
def signL : Rv.Layout := [(0, seg_0), (17, seg_17), (46, seg_46), (47, seg_47), (54, seg_54), (57, seg_57), (60, seg_60), (63, seg_63), (122, seg_122), (123, seg_123), (153, seg_153), (155, seg_155), (167, seg_167), (168, seg_168), (169, seg_169), (170, seg_170), (172, seg_172), (186, seg_186), (188, seg_188), (189, seg_189), (192, seg_192), (194, seg_194), (210, seg_210), (211, seg_211), (225, seg_225), (236, seg_236), (237, seg_237), (250, seg_250), (256, seg_256), (263, seg_263), (265, seg_265), (278, seg_278), (280, seg_280), (282, seg_282), (291, seg_291), (295, seg_295), (296, seg_296), (297, seg_297), (301, seg_301), (310, seg_310), (311, seg_311), (313, seg_313), (316, seg_316), (319, seg_319), (326, seg_326), (328, seg_328), (331, seg_331), (332, seg_332), (334, seg_334), (345, seg_345), (347, seg_347), (348, seg_348), (357, seg_357), (369, seg_369), (370, seg_370), (396, seg_396), (397, seg_397), (411, seg_411), (412, seg_412), (426, seg_426), (427, seg_427), (441, seg_441), (447, seg_447), (448, seg_448), (456, seg_456), (464, seg_464), (470, seg_470), (485, seg_485), (486, seg_486), (498, seg_498), (500, seg_500), (514, seg_514), (515, seg_515), (540, seg_540), (542, seg_542), (543, seg_543), (545, seg_545), (546, ker_546), (1013, Keygen.subCode), (1173, seg_1173), (1175, seg_1175), (1178, seg_1178), (1184, seg_1184), (1187, seg_1187), (1191, seg_1191), (1193, seg_1193), (1196, seg_1196), (1202, seg_1202), (1203, seg_1203), (1214, seg_1214), (1221, seg_1221), (1227, seg_1227), (1432, seg_1432), (1433, seg_1433), (1438, seg_1438), (1456, seg_1456), (1457, seg_1457), (1482, seg_1482), (1483, seg_1483), (2013, maxDigitCodeS), (2017, Keygen.revCode), (2045, seg_2045)]
theorem signL_ok : layoutOk 0 signL = true := by decide +kernel
abbrev image : Image := Images.signReferenceImage
theorem codeAt_0 : CodeAt image (pcOf 0) seg_0 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_46 : CodeAt image (pcOf 46) seg_46 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_47 : CodeAt image (pcOf 47) seg_47 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_54 : CodeAt image (pcOf 54) seg_54 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_57 : CodeAt image (pcOf 57) seg_57 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_60 : CodeAt image (pcOf 60) seg_60 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_63 : CodeAt image (pcOf 63) seg_63 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_122 : CodeAt image (pcOf 122) seg_122 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_123 : CodeAt image (pcOf 123) seg_123 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_155 : CodeAt image (pcOf 155) seg_155 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_167 : CodeAt image (pcOf 167) seg_167 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_168 : CodeAt image (pcOf 168) seg_168 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_169 : CodeAt image (pcOf 169) seg_169 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_170 : CodeAt image (pcOf 170) seg_170 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_172 : CodeAt image (pcOf 172) seg_172 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_186 : CodeAt image (pcOf 186) seg_186 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_188 : CodeAt image (pcOf 188) seg_188 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_189 : CodeAt image (pcOf 189) seg_189 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_192 : CodeAt image (pcOf 192) seg_192 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_194 : CodeAt image (pcOf 194) seg_194 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_210 : CodeAt image (pcOf 210) seg_210 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_211 : CodeAt image (pcOf 211) seg_211 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_236 : CodeAt image (pcOf 236) seg_236 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_237 : CodeAt image (pcOf 237) seg_237 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_250 : CodeAt image (pcOf 250) seg_250 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_256 : CodeAt image (pcOf 256) seg_256 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_263 : CodeAt image (pcOf 263) seg_263 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_265 : CodeAt image (pcOf 265) seg_265 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_278 : CodeAt image (pcOf 278) seg_278 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_280 : CodeAt image (pcOf 280) seg_280 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_282 : CodeAt image (pcOf 282) seg_282 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_291 : CodeAt image (pcOf 291) seg_291 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_295 : CodeAt image (pcOf 295) seg_295 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_296 : CodeAt image (pcOf 296) seg_296 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_297 : CodeAt image (pcOf 297) seg_297 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_301 : CodeAt image (pcOf 301) seg_301 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_310 : CodeAt image (pcOf 310) seg_310 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_311 : CodeAt image (pcOf 311) seg_311 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_313 : CodeAt image (pcOf 313) seg_313 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_316 : CodeAt image (pcOf 316) seg_316 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_319 : CodeAt image (pcOf 319) seg_319 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_326 : CodeAt image (pcOf 326) seg_326 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_328 : CodeAt image (pcOf 328) seg_328 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_331 : CodeAt image (pcOf 331) seg_331 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_332 : CodeAt image (pcOf 332) seg_332 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_334 : CodeAt image (pcOf 334) seg_334 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_345 : CodeAt image (pcOf 345) seg_345 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_347 : CodeAt image (pcOf 347) seg_347 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_348 : CodeAt image (pcOf 348) seg_348 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_357 : CodeAt image (pcOf 357) seg_357 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_369 : CodeAt image (pcOf 369) seg_369 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_370 : CodeAt image (pcOf 370) seg_370 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_396 : CodeAt image (pcOf 396) seg_396 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_397 : CodeAt image (pcOf 397) seg_397 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_411 : CodeAt image (pcOf 411) seg_411 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_412 : CodeAt image (pcOf 412) seg_412 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_426 : CodeAt image (pcOf 426) seg_426 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_427 : CodeAt image (pcOf 427) seg_427 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_441 : CodeAt image (pcOf 441) seg_441 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_447 : CodeAt image (pcOf 447) seg_447 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_456 : CodeAt image (pcOf 456) seg_456 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_464 : CodeAt image (pcOf 464) seg_464 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_470 : CodeAt image (pcOf 470) seg_470 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_485 : CodeAt image (pcOf 485) seg_485 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_486 : CodeAt image (pcOf 486) seg_486 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_498 : CodeAt image (pcOf 498) seg_498 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_500 : CodeAt image (pcOf 500) seg_500 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_514 : CodeAt image (pcOf 514) seg_514 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_515 : CodeAt image (pcOf 515) seg_515 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_542 : CodeAt image (pcOf 542) seg_542 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_543 : CodeAt image (pcOf 543) seg_543 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_545 : CodeAt image (pcOf 545) seg_545 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1173 : CodeAt image (pcOf 1173) seg_1173 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1175 : CodeAt image (pcOf 1175) seg_1175 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1178 : CodeAt image (pcOf 1178) seg_1178 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1184 : CodeAt image (pcOf 1184) seg_1184 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1187 : CodeAt image (pcOf 1187) seg_1187 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1191 : CodeAt image (pcOf 1191) seg_1191 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1193 : CodeAt image (pcOf 1193) seg_1193 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1196 : CodeAt image (pcOf 1196) seg_1196 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1202 : CodeAt image (pcOf 1202) seg_1202 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1203 : CodeAt image (pcOf 1203) seg_1203 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_17 : CodeAt image (pcOf 17) seg_17 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_448 : CodeAt image (pcOf 448) seg_448 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1227 : CodeAt image (pcOf 1227) seg_1227 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1432 : CodeAt image (pcOf 1432) seg_1432 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1433 : CodeAt image (pcOf 1433) seg_1433 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1438 : CodeAt image (pcOf 1438) seg_1438 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1456 : CodeAt image (pcOf 1456) seg_1456 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1457 : CodeAt image (pcOf 1457) seg_1457 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1482 : CodeAt image (pcOf 1482) seg_1482 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_maxDigit : CodeAt image (pcOf 2013) maxDigitCodeS :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_2017 : CodeAt image (pcOf 2017) Keygen.revCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_225 : CodeAt image (pcOf 225) seg_225 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_2045 : CodeAt image (pcOf 2045) seg_2045 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
def signK : Rv.Layout := [(0, seg_0), (17, seg_17), (46, seg_46), (47, seg_47), (54, seg_54), (57, seg_57), (60, seg_60), (63, seg_63), (122, seg_122), (123, seg_123), (153, seg_153), (155, seg_155), (167, seg_167), (168, seg_168), (169, seg_169), (170, seg_170), (172, seg_172), (186, seg_186), (188, seg_188), (189, seg_189), (192, seg_192), (194, seg_194), (210, seg_210), (211, seg_211), (225, seg_225), (236, seg_236), (237, seg_237), (250, seg_250), (256, seg_256), (263, seg_263), (265, seg_265), (278, seg_278), (280, seg_280), (282, seg_282), (291, seg_291), (295, seg_295), (296, seg_296), (297, seg_297), (301, seg_301), (310, seg_310), (311, seg_311), (313, seg_313), (316, seg_316), (319, seg_319), (326, seg_326), (328, seg_328), (331, seg_331), (332, seg_332), (334, seg_334), (345, seg_345), (347, seg_347), (348, seg_348), (357, seg_357), (369, seg_369), (370, seg_370), (396, seg_396), (397, seg_397), (411, seg_411), (412, seg_412), (426, seg_426), (427, seg_427), (441, seg_441), (447, seg_447), (448, seg_448), (456, seg_456), (464, seg_464), (470, seg_470), (485, seg_485), (486, seg_486), (498, seg_498), (500, seg_500), (514, seg_514), (515, seg_515), (540, seg_540), (542, seg_542), (543, kerCode), (1013, Keygen.subCode), (1173, seg_1173), (1175, seg_1175), (1178, seg_1178), (1184, seg_1184), (1187, seg_1187), (1191, seg_1191), (1193, seg_1193), (1196, seg_1196), (1202, seg_1202), (1203, seg_1203), (1214, seg_1214), (1221, seg_1221), (1227, seg_1227), (1432, seg_1432), (1433, seg_1433), (1438, seg_1438), (1456, seg_1456), (1457, seg_1457), (1482, seg_1482), (1483, seg_1483), (2013, maxDigitCodeS), (2017, Keygen.revCode), (2045, seg_2045)]
theorem signK_ok : layoutOk 0 signK = true := by decide +kernel
sym_block blk_0 := symRun { noAlias := true } seg_0 (pcOf 0) 100
sym_block blk_47 := symRun { noAlias := true } seg_47 (pcOf 47) 100
sym_block blk_54 := symRun { noAlias := true } seg_54 (pcOf 54) 100
sym_block blk_57 := symRun { noAlias := true } seg_57 (pcOf 57) 100
sym_block blk_60 := symRun { noAlias := true } seg_60 (pcOf 60) 100
sym_block blk_63 := symRun { noAlias := true } seg_63 (pcOf 63) 100
sym_block blk_123 := symRun { noAlias := true } seg_123 (pcOf 123) 100
sym_block blk_153 := symRun { noAlias := true } seg_153 (pcOf 153) 100
sym_block blk_155 := symRun { noAlias := true } seg_155 (pcOf 155) 100
sym_block blk_168 := symRun { noAlias := true } seg_168 (pcOf 168) 100
sym_block blk_169 := symRun { noAlias := true } seg_169 (pcOf 169) 100
sym_block blk_170 := symRun { noAlias := true } seg_170 (pcOf 170) 100
sym_block blk_172 := symRun { noAlias := true } seg_172 (pcOf 172) 100
sym_block blk_186 := symRun { noAlias := true } seg_186 (pcOf 186) 100
sym_block blk_188 := symRun { noAlias := true } seg_188 (pcOf 188) 100
sym_block blk_189 := symRun { noAlias := true } seg_189 (pcOf 189) 100
sym_block blk_192 := symRun { noAlias := true } seg_192 (pcOf 192) 100
sym_block blk_194 := symRun { noAlias := true } seg_194 (pcOf 194) 100
sym_block blk_211 := symRun { noAlias := true } seg_211 (pcOf 211) 100
sym_block blk_225 := symRun { noAlias := true } seg_225 (pcOf 225) 100
sym_block blk_2045 := symRun { noAlias := true } seg_2045 (pcOf 2045) 100
sym_block blk_237 := symRun { noAlias := true } seg_237 (pcOf 237) 100
sym_block blk_250 := symRun { noAlias := true } seg_250 (pcOf 250) 100
sym_block blk_256 := symRun { noAlias := true } seg_256 (pcOf 256) 100
sym_block blk_263 := symRun { noAlias := true } seg_263 (pcOf 263) 100
sym_block blk_265 := symRun { noAlias := true } seg_265 (pcOf 265) 100
sym_block blk_278 := symRun { noAlias := true } seg_278 (pcOf 278) 100
sym_block blk_280 := symRun { noAlias := true } seg_280 (pcOf 280) 100
sym_block blk_282 := symRun { noAlias := true } seg_282 (pcOf 282) 100
sym_block blk_291 := symRun { noAlias := true } seg_291 (pcOf 291) 100
sym_block blk_295 := symRun { noAlias := true } seg_295 (pcOf 295) 100
sym_block blk_296 := symRun { noAlias := true } seg_296 (pcOf 296) 100
sym_block blk_297 := symRun { noAlias := true } seg_297 (pcOf 297) 100
sym_block blk_301 := symRun { noAlias := true } seg_301 (pcOf 301) 100
sym_block blk_310 := symRun { noAlias := true } seg_310 (pcOf 310) 100
sym_block blk_311 := symRun { noAlias := true } seg_311 (pcOf 311) 100
sym_block blk_313 := symRun { noAlias := true } seg_313 (pcOf 313) 100
sym_block blk_316 := symRun { noAlias := true } seg_316 (pcOf 316) 100
sym_block blk_319 := symRun { noAlias := true } seg_319 (pcOf 319) 100
sym_block blk_326 := symRun { noAlias := true } seg_326 (pcOf 326) 100
sym_block blk_328 := symRun { noAlias := true } seg_328 (pcOf 328) 100
sym_block blk_331 := symRun { noAlias := true } seg_331 (pcOf 331) 100
sym_block blk_332 := symRun { noAlias := true } seg_332 (pcOf 332) 100
sym_block blk_334 := symRun { noAlias := true } seg_334 (pcOf 334) 100
sym_block blk_345 := symRun { noAlias := true } seg_345 (pcOf 345) 100
sym_block blk_347 := symRun { noAlias := true } seg_347 (pcOf 347) 100
sym_block blk_348 := symRun { noAlias := true } seg_348 (pcOf 348) 100
sym_block blk_357 := symRun { noAlias := true } seg_357 (pcOf 357) 100
sym_block blk_370 := symRun { noAlias := true } seg_370 (pcOf 370) 100
sym_block blk_396 := symRun { noAlias := true } seg_396 (pcOf 396) 100
sym_block blk_397 := symRun { noAlias := true } seg_397 (pcOf 397) 100
sym_block blk_411 := symRun { noAlias := true } seg_411 (pcOf 411) 100
sym_block blk_412 := symRun { noAlias := true } seg_412 (pcOf 412) 100
sym_block blk_426 := symRun { noAlias := true } seg_426 (pcOf 426) 100
sym_block blk_427 := symRun { noAlias := true } seg_427 (pcOf 427) 100
sym_block blk_441 := symRun { noAlias := true } seg_441 (pcOf 441) 100
sym_block blk_447 := symRun { noAlias := true } seg_447 (pcOf 447) 100
sym_block blk_456 := symRun { noAlias := true } seg_456 (pcOf 456) 100
sym_block blk_464 := symRun { noAlias := true } seg_464 (pcOf 464) 100
sym_block blk_470 := symRun { noAlias := true } seg_470 (pcOf 470) 100
sym_block blk_486 := symRun { noAlias := true } seg_486 (pcOf 486) 100
sym_block blk_498 := symRun { noAlias := true } seg_498 (pcOf 498) 100
sym_block blk_500 := symRun { noAlias := true } seg_500 (pcOf 500) 100
sym_block blk_515 := symRun { noAlias := true } seg_515 (pcOf 515) 100
sym_block blk_540 := symRun { noAlias := true } seg_540 (pcOf 540) 100
sym_block blk_1173 := symRun { noAlias := true } seg_1173 (pcOf 1173) 100
sym_block blk_1175 := symRun { noAlias := true } seg_1175 (pcOf 1175) 100
sym_block blk_1178 := symRun { noAlias := true } seg_1178 (pcOf 1178) 100
sym_block blk_1184 := symRun { noAlias := true } seg_1184 (pcOf 1184) 100
sym_block blk_1187 := symRun { noAlias := true } seg_1187 (pcOf 1187) 100
sym_block blk_1191 := symRun { noAlias := true } seg_1191 (pcOf 1191) 100
sym_block blk_1193 := symRun { noAlias := true } seg_1193 (pcOf 1193) 100
sym_block blk_1196 := symRun { noAlias := true } seg_1196 (pcOf 1196) 100
sym_block blk_1202 := symRun { noAlias := true } seg_1202 (pcOf 1202) 100
sym_block blk_1203 := symRun { noAlias := true } seg_1203 (pcOf 1203) 100
sym_block blk_1214 := symRun { noAlias := true } seg_1214 (pcOf 1214) 100
sym_block blk_543 := symRun { noAlias := true } seg_543 (pcOf 543) 100
sym_block blk_1432 := symRun { noAlias := true } seg_1432 (pcOf 1432) 100
sym_block blk_1433 := symRun { noAlias := true } seg_1433 (pcOf 1433) 100
sym_block blk_1438 := symRun { noAlias := true } seg_1438 (pcOf 1438) 100
sym_block blk_1457 := symRun { noAlias := true } seg_1457 (pcOf 1457) 100
sym_block blk_1482 := symRun { noAlias := true } seg_1482 (pcOf 1482) 100
end SigGolfCandidate.T3M.Sign
end
section
abbrev SigGolfCandidate.T3M.Keygen.MACBLK : Nat := 0x8FE0
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Spec publicHash shortHash privateHash privatePair privateMac privateNonce mask
  privateInput header pad64 Coordinate HashOutput Digest Region)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
abbrev MSG : Nat := 0x6620
abbrev SK : Nat := 0x80
abbrev SIG : Nat := 0x7000
abbrev CACHE : Nat := 0x80000
abbrev NONCE : Nat := 0x20080
abbrev RHOOUT : Nat := 0x20100
abbrev DIG : Nat := 0x20120
abbrev NBUF : Nat := 0x20160
abbrev ENC : Nat := 0x20260
abbrev EOUT : Nat := 0x202A0
abbrev FLEAF : Nat := 0x202C0
abbrev LFOUT : Nat := 0x20300
abbrev FOREST : Nat := 0x20320
abbrev FOUT : Nat := 0x203A0
abbrev MACOUT : Nat := 0x203E0
abbrev TAG : Nat := 0x20400
abbrev DIGITS : Nat := 0x20420
abbrev SEL : Nat := 0x204A0
abbrev IDXV : Nat := 0x20550
abbrev LOW : Nat := 0x21000
abbrev FTS : Nat := 0x30000
abbrev SEC : Nat := 0x40000
macro "sg_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC] at *); omega))
section tb
variable {α β : Type} {image : Image} {sk : BitVec 256}
theorem TBSim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
theorem TBSim.of_eq {s : MachineState} {W W' : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (he : p = q) (hW : W = W') : TBSim image sk s W' q Q := by
  subst he hW; exact h
theorem TBSim.post_steps {s : MachineState} {W k c : Nat} {p : M α} {Q Q' : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (hs : ∀ a t, Q a t → ∃ u, Steps image t k c u ∧ Q' a u) :
    TBSim image sk s (W + c) p Q' :=
  TBSim.of_eq (TBSim.bind (f := fun a => (Pure.pure a : M α)) h
    (fun a t ht => by obtain ⟨u, hu, hq⟩ := hs a t ht; exact TBSim.pure_steps hu hq)) (bind_pure p) rfl
theorem TBSim.publicHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.shortHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (pad64 input)).blocks + W) (shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem TBSim.privateHash_bind {s : MachineState} {co : Coordinate} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk co))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (privateInput sk co)).blocks + W) (privateHash co >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_privateHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.privateNonce_bind {s : MachineState} {m : T3.Message} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk (.inr (.inl m))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * 2 + W) (privateNonce m >>= f) Q := by
  have hb : (toQ (privateInput sk (.inr (.inl m)))).blocks = 2 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_nonce_eq]
    simp [bytesLE_length, SigGolfCandidate.T3.zero16]
  have : privateNonce m >>= f = privateHash (.inr (.inl m)) >>= fun a => f (a.extractLsb' 0 128) := by
    unfold privateNonce; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])
theorem TBSim.privatePair_bind {s : MachineState} {tag lay tree position index : Nat} {W : Nat}
    {f : Digest × Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header tag lay tree position index))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W
      (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TBSim image sk s (8 + W) (privatePair tag lay tree position index >>= f) Q := by
  have hb : (toQ (privateInput sk (.inl (header tag lay tree position index)))).blocks = 1 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_tweak_length]
  have : privatePair tag lay tree position index >>= f =
      privateHash (.inl (header tag lay tree position index)) >>= fun a =>
        f (a.extractLsb' 0 128, a.extractLsb' 128 128) := by
    unfold privatePair; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])
theorem TBSim.mask_bind {s : MachineState} {level index : Nat} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header 13 0 0 level (index/2)))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W
      (f (if index % 2 = 0 then a.extractLsb' 0 128 else a.extractLsb' 128 128)) Q) :
    TBSim image sk s (8 + W) (mask level index >>= f) Q := by
  have : mask level index >>= f = privatePair 13 0 0 level (index/2) >>=
      fun x => f (if index % 2 = 0 then x.1 else x.2) := by
    unfold mask T3.pairedMask; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.privatePair_bind hf ht0 hv hq h
end tb
structure Failed (t : MachineState) : Prop where
  pc : t.pc = pcOf 545
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
theorem fetch_545 (s : MachineState) (hpc : s.pc = pcOf 545) : fetch image s = some (.base .ECALL) :=
  (codeAt_545.fetch s hpc).trans rfl
theorem fail_spec (s : MachineState) (hpc : s.pc = pcOf 543) :
    ∃ t, Steps image s 2 2 t ∧ Failed t ∧ RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_543 codeAt_543 s hpc (by simp [blk_543.res, rv_simp]), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [blk_543.res, E.eval]
  · simp [blk_543.res, rv_simp]
  · simp [blk_543.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_543.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_543.res, rv_simp]
theorem bv256_eq_iff (x y : BitVec 256) :
    x = y ↔ (x.extractLsb' 0 64 = y.extractLsb' 0 64 ∧ x.extractLsb' 64 64 = y.extractLsb' 64 64 ∧
      x.extractLsb' 128 64 = y.extractLsb' 128 64 ∧ x.extractLsb' 192 64 = y.extractLsb' 192 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    apply BitVec.eq_of_toNat_eq
    have e0 := congrArg BitVec.toNat h0; have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2; have e3 := congrArg BitVec.toNat h3
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at e0 e1 e2 e3
    have hx := x.isLt; have hy := y.isLt
    simp only [Nat.reducePow] at e0 e1 e2 e3 hx hy
    omega
theorem bytesToWordLE_bytes {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply Keygen.word_ext_bytes
  intro i hi
  rw [Keygen.extractByte_bytesToWordLE _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [Keygen.extractByte_toNat']
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < n by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * j) = y
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
end SigGolfCandidate.T3M.Sign
end
end
-- ==== merged from T3M_Expand_PackedHeader ====
section

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Keygen.PackedBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen.PackedBlocks
class Code (im : Image) : Prop where
  entry : CodeAt im (pcOf 1032) expand_entry
  layer0 : CodeAt im (pcOf 1247) expand_layer0
  layer1 : CodeAt im (pcOf 1249) expand_layer1
  layer23 : CodeAt im (pcOf 1251) expand_layer23
  inc : CodeAt im (pcOf 1252) expand_inc
  body : CodeAt im (pcOf 1253) expand_body
  store : CodeAt im (pcOf 1038) expand_store
variable {im : Image} [Code im]
theorem steps_expand_entry (s : MachineState) (hpc : s.pc = pcOf 1032) :
    Steps im s 1 1 (run_expand_entry.res.toState s) := by
  exact symRun_sound run_expand_entry (Code.entry (im := im)) s hpc (by simp [run_expand_entry.res, rv_simp])

theorem steps_expand_layer0 (s : MachineState) (hpc : s.pc = pcOf 1247) :
    Steps im s 2 2 (run_expand_layer0.res.toState s) := by
  exact symRun_sound run_expand_layer0 (Code.layer0 (im := im)) s hpc (by simp [run_expand_layer0.res, rv_simp])

theorem steps_expand_layer1 (s : MachineState) (hpc : s.pc = pcOf 1249) :
    Steps im s 2 2 (run_expand_layer1.res.toState s) := by
  exact symRun_sound run_expand_layer1 (Code.layer1 (im := im)) s hpc (by simp [run_expand_layer1.res, rv_simp])

theorem steps_expand_layer23 (s : MachineState) (hpc : s.pc = pcOf 1251) :
    Steps im s 2 2 (run_expand_layer23.res.toState s) := by
  exact symRun_sound run_expand_layer23 (Code.layer23 (im := im)) s hpc (by simp [run_expand_layer23.res, rv_simp])

theorem steps_expand_inc (s : MachineState) (hpc : s.pc = pcOf 1252) :
    Steps im s 1 1 (run_expand_inc.res.toState s) := by
  exact symRun_sound run_expand_inc (Code.inc (im := im)) s hpc (by simp [run_expand_inc.res, rv_simp])

theorem steps_expand_body (s : MachineState) (hpc : s.pc = pcOf 1253) :
    Steps im s 19 19 (run_expand_body.res.toState s) := by
  exact symRun_sound run_expand_body (Code.body (im := im)) s hpc (by simp [run_expand_body.res, rv_simp])

theorem steps_expand_store (s : MachineState) (hpc : s.pc = pcOf 1038) :
    Steps im s 3 3 (run_expand_store.res.toState s) := by
  exact symRun_sound run_expand_store (Code.store (im := im)) s hpc (by simp [run_expand_store.res, rv_simp])
end SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
open SigGolfCandidate.T3M.Keygen.PackedBlocks
variable {im : SigGolfCandidate.Legacy.Riscv.Image} [Code im]
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
/-- Pairing stage 1: expand's chain header store ends at 1040 (1041 is `jal 43764`, the G/F step block); `t3`
holds `CHAIN`. -/
structure ExpHeaderPost (s t : MachineState) (height : Nat) : Prop where
  low : t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = packedAt s height
  high : t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = routedAt s height >>> 32
  x28 : t.getReg .x28 = BitVec.ofNat 64 0x201A0
  regs : RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30]
  frame : Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24)
theorem expand_header_0 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps im s 25 25 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 12 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_body.res.toState s1
  have h2 := steps_expand_body (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_store.res.toState s2
  have h3 := steps_expand_store (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s3, (((h0.trans h1).trans h2).trans h3), ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_1 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps im s 28 28 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 7 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_inc.res.toState s2
  have h3 := steps_expand_inc (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_2 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 6 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_layer23.res.toState s2
  have h3 := steps_expand_layer23 (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_3 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 6 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_layer23.res.toState s2
  have h3 := steps_expand_layer23 (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
end
-- ==== merged from T3M_Keygen_Tree ====
section

section



namespace SigGolfCandidate.T3M.RevNet
open SigGolfCandidate.Rv SigGolfCandidate.T3.Rev
theorem tabRev_eq : ∀ n v, Images.tabRev n v = revBits n v
  | 0, _ => rfl
  | n + 1, v => by simp only [Images.tabRev, revBits, tabRev_eq n (v / 2)]
theorem verifyTabWord_eq (j : Nat) : Images.verifyTabWord j = revBits 64 (2048 + j) := tabRev_eq 64 _
def bvA (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .or (BinOp.eval .srl x 8#64) (BinOp.eval .sll (BinOp.eval .and x 255#64) 8#64)
def bvS (k M x : BitVec 64) : BitVec 64 :=
  BinOp.eval .or (BinOp.eval .and (BinOp.eval .srl x k) M) (BinOp.eval .sll (BinOp.eval .and x M) k)
def revNetBV (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .sll (bvS 1#64 21845#64 (bvS 2#64 13107#64 (bvS 4#64 3855#64 (bvA x)))) 48#64
@[irreducible] def ok1 (v : Nat) : Bool := revNetBV (BitVec.ofNat 64 v) == BitVec.ofNat 64 (revBits 64 v)
def chk (b : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => ok1 (b + n) && chk b n
theorem ok1_sound {v : Nat} (h : ok1 v = true) : revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v) := by
  unfold ok1 at h; exact beq_iff_eq.mp h
theorem chk_succ (b n : Nat) : chk b (n + 1) = (ok1 (b + n) && chk b n) := by rw [chk]
theorem chk_sound (b : Nat) : ∀ n, chk b n = true → ∀ v, b ≤ v → v < b + n →
    revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v)
  | 0, _, v, _, h2 => absurd h2 (by omega)
  | n + 1, h, v, h1, h2 => by
    rw [chk_succ, Bool.and_eq_true] at h
    by_cases hv : v = b + n
    · subst hv; exact ok1_sound h.1
    · exact chk_sound b n h.2 v h1 (by omega)
theorem chk0 : chk 0 1024 = true := by decide +kernel
theorem chk1 : chk 1024 1024 = true := by decide +kernel
theorem chk2 : chk 2048 1024 = true := by decide +kernel
theorem chk3 : chk 3072 1024 = true := by decide +kernel
theorem revNetBV_eq (v : Nat) (hv : v < 2 ^ 12) :
    revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v) := by
  rcases (show v < 1024 ∨ (1024 ≤ v ∧ v < 2048) ∨ (2048 ≤ v ∧ v < 3072) ∨ (3072 ≤ v ∧ v < 4096) by omega) with
    h | h | h | h
  · exact chk_sound 0 1024 chk0 v (by omega) (by omega)
  · exact chk_sound 1024 1024 chk1 v h.1 (by omega)
  · exact chk_sound 2048 1024 chk2 v h.1 (by omega)
  · exact chk_sound 3072 1024 chk3 v h.1 (by omega)
end SigGolfCandidate.T3M.RevNet
end

section



section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem sub116_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 116)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lo = 0 then pcOf (b + 159) else pcOf (b + 117)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_116 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_116 h) s hpc (by simp [st_116, blk117_116.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_116, rebase, blk117_116.res, E.eval, CmpOp.eval, h20]
    by_cases h0 : lo = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 lo ≠ 0#64 := fun he => h0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h0, this]
  · intro r hr; cases r <;> simp_all [st_116, blk117_116.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_116, blk117_116.res, rv_simp]
theorem sub117_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 117)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = s.getReg .x20 ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  have hrun := run_117 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_117 h) s hpc (by simp [st_117, blk117_117.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_117, Result.toState_pc, E.eval]
  · simp [st_117, blk117_117.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_117, blk117_117.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_117, blk117_117.res, rv_simp]
theorem sub118_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 118)) (lo k : Nat) (hlo : lo < 2 ^ 40) (hk : k < 2 ^ 40)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if k < 2 * lo then pcOf (b + 120) else pcOf (b + 157)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_118 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_118 h) s hpc (by simp [st_118, blk117_118.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_118, rebase, blk117_118.res, rv_simp, h20, h24]
    rw [ofNat_shl, show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_slt k (lo * 2 ^ 1) (by omega) (by omega)]
    by_cases hkl : k < 2 * lo
    · simp [hkl, show k < lo * 2 by omega]
    · simp [hkl, show ¬ k < lo * 2 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_118, blk117_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_118, blk117_118.res, rv_simp]
theorem slt_shl52n (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< 52) 0#64 = decide (2048 ≤ h0 % 4096) := by
  have e : BitVec.ofNat 64 h0 <<< 52 = BitVec.ofNat 64 (h0 % 4096 * 2 ^ 52) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    norm_num
    omega
  rw [e, BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have hr := Nat.mod_lt h0 (show 0 < 4096 by norm_num)
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show h0 % 4096 * 2 ^ 52 < 2 ^ 64 by omega)]
  by_cases hc : 2048 ≤ h0 % 4096
  · simp only [hc, decide_true]
    rw [if_neg (by omega)]
    simp <;> omega
  · simp only [hc, decide_false]
    rw [if_pos (by omega)]
    simp <;> omega
theorem slt_shl52n' (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< 52) (0 : Word) = decide (2048 ≤ h0 % 4096) := slt_shl52n h0
theorem slt_shl52 (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< ((52#64 : Word).toNat % 64)) (0 : Word) = decide (2048 ≤ h0 % 4096) :=
  slt_shl52n h0
theorem slt_shl52' (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< ((52#64 : Word).toNat % 64)) 0#64 = decide (2048 ≤ h0 % 4096) :=
  slt_shl52n h0
/-- Node window (C4, b3cc11b's keygen words): left/right children copied to `NODE`/`NODE + 48`, one-word label
`(x21 ||| tree << 32) + k` at `NODE + 16`, zero high word, `x29 = k % 2` (the half selector). -/
theorem sub120_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat) (ha8 : arena % 8 = 0)
    (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 20 20 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x29 = BitVec.ofNat 64 (k % 2) ∧ t.getReg .x30 = BitVec.ofNat 64 (NODE + 48) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32)) + BitVec.ofNat 64 k ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  have hc := codeAt_sub120K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  have hobl : Oblig.all s st_120K.obl := by
    simp only [st_120K, kblk_120.res]
    t3n [h2, h24]
    simp only [NODE] at hdis
    omega
  refine ⟨_, symRun_sound run_120K hc s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_120K, kblk_120.res, rv_simp, h24]
    exact ofNat_and1 k
  · simp [st_120K, kblk_120.res, rv_simp]
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h9, h24]
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n []
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_120K, kblk_120.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, st_120K, kblk_120.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
theorem sub214_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1004)) (k : Nat) (hk : k < 2 ^ 12) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 28 28 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x7 = BitVec.ofNat 64 (T3.Rev.revBits 64 k) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_rev h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_rev h) s hpc (by simp [st_rev, blk117_rev.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_rev, Result.toState_pc, E.eval]
  · rw [Result.toState_getReg, ← RevNet.revNetBV_eq k hk, ← h24]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_rev, blk117_rev.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_rev, blk117_rev.res, rv_simp]
theorem valid8_ofNat (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
theorem node48_m24 : BitVec.ofNat 64 (NODE + 48) + BitVec.ofNat 64 18446744073709551592 = BitVec.ofNat 64 (NODE + 24) := by
  rw [ofNat_add_ofNat]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, NODE]
theorem sub140_obl (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    Oblig.all s st_140.obl := by
  simp only [st_140, blk117_140.res, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
    BitVec.ofNat_eq_ofNat]
  rw [h30, node48_m24]
  exact valid8_ofNat _ (by simp only [NODE]) (by simp only [NODE]; omega)
theorem sub140_m24 (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    memEval s st_140.mem (BitVec.ofNat 64 (NODE + 24)) = s.getReg .x7 := by
  simp only [st_140, blk117_140.res]
  t3n [h30, NODE]
theorem sub140_frame (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) (X : Nat)
    (hX : X < 2 ^ 64) (hn : X ≠ 131608) :
    memEval s st_140.mem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) := by
  simp only [st_140, blk117_140.res]
  t3n [h30, NODE]
  rw [if_neg (by omega)]
/-- C4 (b3cc11b's keygen word): the hash call setup also scales the half selector, `x29 = 16 p`. -/
theorem sub140_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 140)) (p : Nat) (h29 : s.getReg .x29 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧ t.getReg .x29 = BitVec.ofNat 64 (p * 2 ^ 4) ∧
      RegsExcept s t [.x10, .x11, .x12, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := codeAt_sub140K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  refine ⟨_, symRun_sound run_140K hc s hpc (by simp [st_140K, kblk_140.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp only [Result.toState_getReg, st_140K, kblk_140.res, rv_simp, h29]
    rw [ofNat_shl]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_140K, kblk_140.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_140K, kblk_140.res, rv_simp]
def revX (tag : Nat) : Nat := if tag = 10 then 28 else 0
/-- Base of the node label word in the `s5` register: the C4 top label is the heap itself (base 0; it was 64); the
lower trees (the sign's) keep `hyperWord (lay - 1) tree`. -/
def nodeLo (lay tree : Nat) : Nat := if lay = 0 then 0 else (T3.hyperWord (lay - 1) tree).toNat
theorem nodeLo_mod (lay tree : Nat) : nodeLo lay tree % 4096 < 2048 := by
  unfold nodeLo; split
  · decide
  · rw [T3.hyperWord_toNat]; simp only [Nat.reducePow]; omega
/-- C4: the top node tweak is the one-word label `0#64 ++ heap` (`nodeLo 0 tree = 0`). -/
theorem nodeTweak_3_top (tree heap : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) :
    T3.nodeTweak 3 0 tree heap = 0#64 ++ BitVec.ofNat 64 (nodeLo 0 tree + heap) := by
  rw [T3.nodeTweak_top, T3.topNodeWord_eq h1 h2]
  simp [nodeLo]
/-- The tree node block from `b + 120` to the hash call (C4: no reversed labels, one-word label). -/
theorem sub120_full {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat)
    (ha8 : arena % 8 = 0) (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧ t.getReg .x29 = BitVec.ofNat 64 (k % 2 * 2 ^ 4) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32)) + BitVec.ofNat 64 k ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  obtain ⟨t1, st1, t1pc, t1x29, t1x30, m0, m8, m16, m24, m48, m56, t1r, t1f⟩ :=
    sub120_spec h s hpc arena k tree h0 ha8 hk htree hdis h2 h24 h9 h21
  obtain ⟨t, stt, tpc, tx10, tx11, tx12, tx29, tr, tf⟩ := sub140_spec h t1 t1pc (k % 2) t1x29
  have g : ∀ X, X < 2 ^ 64 → t.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => tf.get hX (fun h => h)
  refine ⟨t, (st1.trans stt).of_eq (by omega) (by omega), tpc, tx10, tx11, tx12, tx29, ?_, ?_, ?_, ?_, ?_, ?_,
    t1r.trans tr, (t1f.trans tf).mono (fun X _ hX => by rcases hX with hX | hX; exact hX; exact hX.elim)⟩
  · rw [g NODE (by decide), m0]
  · rw [g (NODE + 8) (by decide), m8]
  · rw [g (NODE + 16) (by decide), m16]
  · rw [g (NODE + 24) (by decide), m24]
  · rw [g (NODE + 48) (by decide), m48]
  · rw [g (NODE + 56) (by decide), m56]
theorem fetch_sub146 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 146)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_146 h).fetch s hpc).trans rfl
theorem sub159_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 159)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_159 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_159 h) s hpc (by simp [st_159, blk117_159.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_159, blk117_159.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_159, blk117_159.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_159, blk117_159.res, rv_simp]
end SigGolfCandidate.T3M.Keygen
end
section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest buildLevels buildLevel nodeHash shortHash header pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
structure LevArgs where
  tag : Nat
  lay : Nat
  tree : Nat
  h : Nat
  arena : Nat
  ret : Nat
namespace LevArgs
variable (B : LevArgs)
def levK : Nat := 3 + sumTo (fun j => 6 + (39 + revX B.tag) * 2 ^ (B.h - 1 - j)) B.h + 2
def levC : Nat := 3 + sumTo (fun j => 6 + (46 + revX B.tag) * 2 ^ (B.h - 1 - j)) B.h + 2
def levN : Nat := sumTo (fun j => 2 ^ (B.h - 1 - j)) B.h
end LevArgs
def LevW (B : LevArgs) (X : Nat) : Prop :=
  X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨ X = NODE + 56 ∨
    (NOUT ≤ X ∧ X < NOUT + 32) ∨ (B.arena + 16 ≤ X ∧ X < B.arena + 16 * 2 ^ B.h)
def levRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x24, .x28, .x29, .x30]
structure LevPre (s : MachineState) (B : LevArgs) (leaves : List Digest) : Prop where
  x1 : s.getReg .x1 = pcOf B.ret
  x2 : s.getReg .x2 = BitVec.ofNat 64 B.arena
  x5 : s.getReg .x5 = 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 B.tree
  x15 : s.getReg .x15 = BitVec.ofNat 64 B.h
  x21 : s.getReg .x21 = BitVec.ofNat 64 (nodeLo B.lay B.tree)
  tag3 : B.tag = 3
  hlay : B.lay < 4
  htree : B.tree < 2 ^ 32
  hh1 : 1 ≤ B.h
  hh : B.h ≤ 12
  ha8 : B.arena % 8 = 0
  ha : B.arena + 16 * 2 ^ (B.h + 1) ≤ 2 ^ 24
  has : NOUT + 32 ≤ B.arena ∨ B.arena + 16 * 2 ^ (B.h + 1) ≤ NODE
  z32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  z40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  hlen : leaves.length = 2 ^ B.h
  hleaves : DigsAt s (B.arena + 16 * 2 ^ B.h) leaves
def HeapAt (t : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest)) : Prop :=
  levels.length = ℓ + 1 ∧ ∀ l ≤ ℓ, (levels.getD l []).length = 2 ^ (B.h - l) ∧
    DigsAt t (B.arena + 16 * 2 ^ (B.h - l)) (levels.getD l [])
structure LevInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (t : MachineState) : Prop where
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ B.h / 2 ^ (ℓ + 1))
  regs : RegsExcept s0 t levRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
structure NodeInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (pre : List Digest) (t : MachineState) : Prop where
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1) + pre.length)
  regs : RegsExcept s0 t levRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
  cur : DigsAt t (B.arena + 16 * 2 ^ (B.h - ℓ - 1)) pre
theorem nodeInput_length (tag lay tree heap : Nat) (l r : Digest) :
    (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem wordsOf_nodeInput (tag lay tree heap : Nat) (l r : Digest)
    (hn : T3.packedNodeTag tag := by decide) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 tag lay tree tree),
        BitVec.ofNat 64 (T3.nodeWord tag 0 heap), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_packed_header _ _ _ _ _ hn, wordsOf_zero16,
    wordsOf_bytesLE16]
  rfl
theorem wordsOf_nodeInput_3 (lay tree heap : Nat) (l r : Digest) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header 3 lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 3 lay tree tree),
        BitVec.ofNat 64 (hdr1 heap 0), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_nodeInput 3 lay tree heap l r (by decide), nodeWord_3]
/-- C4: the words of a top node input (label `nodeLo 0 tree + heap`, zero high word, zero pad). -/
theorem wordsOf_nodeInputT (tree heap : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (l r : Digest) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (T3.nodeTweak 3 0 tree heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (nodeLo 0 tree + heap),
        0, 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
    wordsOf_bytesLE16, nodeTweak_3_top tree heap h1 h2, T3.append64_low]
  have hhi : (0#64 ++ BitVec.ofNat 64 (nodeLo 0 tree + heap)).extractLsb' 64 64 = 0#64 :=
    BitVec.extractLsb'_append_eq_left
  rw [hhi]; rfl
theorem nodeInputT_length (tag lay tree heap : Nat) (l r : Digest) :
    (bytesLE 16 l ++ bytesLE 16 (T3.nodeTweak tag lay tree heap) ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem two_pow_split {h l : Nat} (hl : l < h) : 2 ^ (h - l) = 2 * 2 ^ (h - l - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega
/-! The keygen top-tree level routine (top-bytes layer: node nonces) is proved in `TopTree.lean`
(`sub113`/`sub147`/`sub157` now hook into KINIT/KCHK/KNEXT). -/
end SigGolfCandidate.T3M.Keygen
end
end
end
