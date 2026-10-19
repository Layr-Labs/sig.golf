import SigGolfCandidate.T3M_Search_RewardBlocks
set_option Elab.async false

/-!
# Top zero-digit cap `zc` (top-bytes layer; img-v6 sign 21667..21784, expand 43077..43194)

After the top floor test passes, the canonical top trial counts the zero digits of the 54 top digits with a
128-byte table `Zt` (prepended to the data segment; `Zt[r]` = number of zero base-5 digits of the rank `r < 125`)
for the 17 rank groups, plus the three raw radix-8 digits at bits 119..127, and rejects the half (jump to the
`choice_r` entry) when the count is at least 10 (`canonicalZeroBound 0`: at most 9 zero digits).
Registers: `x6`/`x7` = the two words of the (unflipped) top value `v`, `x29` = running count; clobbers
`x10`, `x28`, `x29`.
-/

namespace SigGolfCandidate.T3M.Search.ZeroCap
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

/-- First word of the routine. -/
def zcBase (b : Nat) : Nat := if b = 354 then 43077 else 21667
/-- `lui t3` value (the table base plus 128). -/
def ZTB (b : Nat) : Nat := if b = 354 then 0xFF9000 else 0xFEB000
/-- Table address (`= dataBase` of the image). -/
def ZT (b : Nat) : Nat := if b = 354 then 0xFF8B10 else 0xFEAF80
/-- Signed offset of the table load (`ZT = ZTB + off`, off as a 64-bit two's complement). -/
def zoff (b : Nat) : Nat := if b = 354 then 2 ^ 64 - 1264 else 2 ^ 64 - 128
/-- Pass / fail targets. -/
def zcPass (b : Nat) : Nat := if b = 354 then 46924 else 22499
def zcFail (b : Nat) : Nat := if b = 354 then 43043 else 21035

def win (q : Nat) : List (BitVec 32) :=
  if q = 0 then [0x7f37513]
  else if q < 9 then [BitVec.ofNat 32 (0x35513 + 7 * q * 2 ^ 20), 0x7f57513]
  else if q = 9 then [0x3f35513, 0x139e13, 0x1c56533, 0x7f57513]
  else [BitVec.ofNat 32 (0x3d513 + (7 * q - 64) * 2 ^ 20), 0x7f57513]
def luiW (b : Nat) : BitVec 32 := if b = 354 then 0xff9e37 else 0xfebe37
def lbuW (b : Nat) : BitVec 32 := if b = 354 then 0xb1054503 else 0xf8054503
def pre (b q : Nat) : List (BitVec 32) := win q ++ [luiW b, 0x1c50533]
def group (b q : Nat) : List (BitVec 32) := pre b q ++ [lbuW b, 0xae8eb3]
def tailW (b : Nat) : List (BitVec 32) :=
  [0x373d513, 0x757e13, 0x1e3e13, 0x1ce8eb3, 0x355e13, 0x7e7e13, 0x1e3e13, 0x1ce8eb3, 0x655e13, 0x1e3e13,
    0x1ce8eb3, 0xa00e13, if b = 354 then 0xdbcef4e3 else 0xc5cef863]
def jalW (b : Nat) : BitVec 32 := if b = 354 then 0x2490306f else 0x32d0006f
def code (b : Nat) : List (BitVec 32) :=
  [0xe93] ++ (List.range 17).flatMap (group b) ++ tailW b ++ [jalW b]
def gstart (q : Nat) : Nat := if q = 0 then 1 else 6 * q + (if 10 ≤ q then 2 else 0)
def wlen (q : Nat) : Nat := if q = 0 then 1 else if q = 9 then 4 else 2

theorem code_length (b : Nat) : (code b).length = 118 := by
  unfold code; by_cases h : b = 354 <;> simp [h, group, pre, win, tailW] <;> decide

/-! ### Table and count -/
/-- Number of zero base-5 digits of a rank `r < 125` (0 for `r ≥ 125`). -/
def ztNat (r : Nat) : Nat :=
  if r < 125 then (if r % 5 = 0 then 1 else 0) + (if r / 5 % 5 = 0 then 1 else 0) + (if r / 25 % 5 = 0 then 1 else 0)
  else 0
def ztByte (r : Nat) : BitVec 8 := BitVec.ofNat 8 (ztNat r)
def ZtOK (b : Nat) (s : MachineState) : Prop :=
  ∀ r, r < 128 → s.getByte (BitVec.ofNat 64 (ZT b + r)) = ztByte r
theorem ZtOK.frame {b : Nat} {s t : MachineState} {W : Nat → Prop} (h : ZtOK b s) (hf : Frame s t W)
    (hd : ∀ r, r < 128 → ¬ W ((ZT b + r) / 8 * 8)) : ZtOK b t := by
  intro r hr
  exact (hf.getByte (by unfold ZT; split_ifs <;> omega) (hd r hr)).trans (h r hr)
/-- The raw tail field (bits 119..127). -/
def tailField (v : Digest) : Nat := v.toNat / 2 ^ 119 % 512
def tailZeros (r : Nat) : Nat :=
  (if r % 8 = 0 then 1 else 0) + (if r / 8 % 8 = 0 then 1 else 0) + (if r / 64 = 0 then 1 else 0)
def runningZ (v : Digest) (n : Nat) : Nat := ((List.range n).map (fun q => ztNat (topRank v q))).sum
/-- Zero-digit count computed by the routine. -/
def zcount (v : Digest) : Nat := runningZ v 17 + tailZeros (tailField v)

theorem runningZ_succ (v : Digest) (n : Nat) : runningZ v (n + 1) = runningZ v n + ztNat (topRank v n) := by
  simp [runningZ, List.range_succ]
theorem ztNat_le (r : Nat) : ztNat r ≤ 3 := by unfold ztNat; split_ifs <;> omega
theorem runningZ_le (v : Digest) (n : Nat) : runningZ v n ≤ 3 * n := by
  induction n with
  | zero => simp [runningZ]
  | succ n ih => rw [runningZ_succ]; have := ztNat_le (topRank v n); omega

theorem filter_zero_length (l : List Nat) :
    (l.filter (· = 0)).length = (l.map (fun d => if d = 0 then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : a = 0 <;> simp [List.filter_cons, h, ih] <;> omega

theorem digit_group (v : Digest) (q j : Nat) (hq : q < 17) (hj : j < 3) :
    T3.coreDigit 0 (T3.topFlip v) (3 * q + j) = topRank v q / 5 ^ j % 5 := by
  unfold T3.coreDigit
  rw [if_pos rfl, if_pos (by omega), T3.topCode_topFlip, show (3 * q + j) / 3 = q by omega,
    show (3 * q + j) % 3 = j by omega]
  rfl
theorem digit_tail (v : Digest) :
    T3.coreDigit 0 (T3.topFlip v) 51 = tailField v / 8 % 8 ∧
    T3.coreDigit 0 (T3.topFlip v) 52 = tailField v / 64 ∧
    T3.coreDigit 0 (T3.topFlip v) 53 = tailField v % 8 := by
  unfold T3.coreDigit T3.topRawShift tailField
  simp only [if_pos rfl, show ¬ (51 < 51) by omega, show ¬ (52 < 51) by omega, show ¬ (53 < 51) by omega,
    if_false, T3.topCode_topFlip, show ¬ ((51:Nat) = 53) by omega, show ¬ ((52:Nat) = 53) by omega, if_true]
  have h := v.isLt
  refine ⟨?_, ?_, ?_⟩ <;> norm_num <;> omega
theorem group_zeros (v : Digest) (q : Nat) (hq : q < 17) (hr : topRank v q < 125) :
    ([3*q, 3*q+1, 3*q+2].map (fun i => if T3.coreDigit 0 (T3.topFlip v) i = 0 then 1 else 0)).sum =
      ztNat (topRank v q) := by
  have h0 := digit_group v q 0 hq (by omega)
  have h1 := digit_group v q 1 hq (by omega)
  have h2 := digit_group v q 2 hq (by omega)
  simp only [Nat.add_zero] at h0
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2, ztNat, if_pos hr]
  simp only [pow_zero, pow_one, Nat.div_one, Nat.add_zero, Nat.add_assoc, show (5:Nat) ^ 2 = 25 by norm_num]
theorem zcount_eq (v : Digest) (hv : T3.topRanksValid (T3.topFlip v) = true) :
    zcount v = ((topDigits (T3.topFlip v)).filter (· = 0)).length := by
  have hg : ∀ q, q < 17 → topRank v q < 125 := fun q hq =>
    (topRanksValid_iff v).mp hv _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
  rw [filter_zero_length]
  have hi : List.range 54 =
      (List.ofFn fun q : Fin 17 => [3*q.val,3*q.val+1,3*q.val+2]).flatten ++ [51,52,53] := by decide +kernel
  unfold topDigits
  rw [List.map_map, hi, List.map_append, List.sum_append, List.map_flatten, List.sum_flatten, List.map_ofFn,
    List.map_ofFn, List.sum_ofFn]
  unfold zcount runningZ
  rw [show List.range 17 = List.ofFn (fun q : Fin 17 => q.val) from rfl, List.map_ofFn, List.sum_ofFn]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply Finset.sum_congr rfl
    intro q _
    have h := group_zeros v q.val q.isLt (hg q.val q.isLt)
    simp only [Function.comp_def, List.map_map] at h ⊢
    exact h.symm
  · obtain ⟨d51, d52, d53⟩ := digit_tail v
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_apply, d51, d52, d53,
      tailZeros]
    omega
/-! ### Machine blocks -/
section blocks
variable {image : Image}

def windowZ (q : Nat) : E := if q = 0 then .reg .x6 else Reward.PackedTop.windowE q
def indexZ (q : Nat) : E := mkBin .and (windowZ q) (.c 127)
def preState (b q : Nat) : SymState :=
  ⟨{RegFile.init with r10 := mkBin .add (indexZ q) (.c (BitVec.ofNat 64 (ZTB b))), r28 := .c (BitVec.ofNat 64 (ZTB b))}, [], []⟩
def preResult (b q : Nat) : Result :=
  ⟨preState b q, .c (pcOf (zcBase b + gstart q + wlen q + 2)), .endOfCode, wlen q + 2, wlen q + 2⟩
theorem pre_run (b q : Nat) (hb : b = 354 ∨ b = 543) (hq : q < 17) :
    symRun {noAlias := true} (pre b q) (pcOf (zcBase b + gstart q)) 10 = some (preResult b q) := by
  rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl

theorem indexZ_eval (s : MachineState) (v : Digest) (q : Nat) (hq : q < 17)
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    (indexZ q).eval s = BitVec.ofNat 64 (topRank v q) := by
  by_cases h0 : q = 0
  · subst q
    simp only [indexZ, windowZ, if_true, mkBin_eval, E.eval, BinOp.eval, h6]
    simpa [topRank] using ext_shr_mask v 0 0 7 (by decide)
  · have he := Reward.PackedTop.index_eval s v q (by omega) h6 h7
    simp only [Reward.PackedTop.indexE, Reward.PackedTop.index, show q < 17 from hq, if_true] at he
    simpa [indexZ, windowZ, h0] using he

theorem codeAt_slice_of {b : Nat} (hc : CodeAt image (pcOf (zcBase b)) (code b)) (k n : Nat)
    (hk : k ≤ 118) : CodeAt image (pcOf (zcBase b + k)) (((code b).drop k).take n) := by
  have he : code b = (code b).take k ++ ((code b).drop k).take n ++ ((code b).drop k).drop n := by
    simp only [List.append_assoc, List.take_append_drop]
  rw [he] at hc
  have hx := CodeAt.drop_prefix hc
  convert hx using 1
  simp only [List.length_take, code_length, Nat.min_eq_left hk, pcOf, ofNat_add_ofNat]
  congr 1; omega

theorem code_pre {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (q : Nat) (hq : q < 17) : CodeAt image (pcOf (zcBase b + gstart q)) (pre b q) := by
  have h := codeAt_slice_of hc (gstart q) (wlen q + 2) (by unfold gstart; split_ifs <;> omega)
  convert h using 1
  rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl

theorem pre_spec {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (s : MachineState) (v : Digest) (q : Nat) (hq : q < 17) (hpc : s.pc = pcOf (zcBase b + gstart q))
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s (wlen q + 2) (wlen q + 2) t ∧ t.pc = pcOf (zcBase b + gstart q + wlen q + 2) ∧
      t.getReg .x10 = BitVec.ofNat 64 (ZTB b + topRank v q) ∧
      RegsExcept s t [.x10, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (pre_run b q hb hq) (code_pre hb hc q hq) s hpc
    (by simp [preResult, preState, rv_simp]), rfl, ?_, ?_, ?_⟩
  · change (mkBin .add (indexZ q) (.c (BitVec.ofNat 64 (ZTB b)))).eval s = _
    rw [mkBin_eval, E.eval, indexZ_eval s v q hq h6 h7]
    simp only [BinOp.eval, ofNat_add_ofNat, Nat.add_comm]
  · intro r hr; cases r <;> simp_all [preResult, preState, RegFile.init, rv_simp] <;> rfl
  · intro A _ _; rfl

theorem lbu_decode (b : Nat) (hb : b = 354 ∨ b = 543) :
    decodeInstruction (lbuW b) = some (.base (.LBU .x10 .x10 (BitVec.ofNat 12 (zoff b % 4096)))) := by
  rcases hb with rfl | rfl <;> kernel_rfl

theorem code_load {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (q : Nat) (hq : q < 17) : CodeAt image (pcOf (zcBase b + gstart q + wlen q + 2)) [lbuW b] := by
  have h := codeAt_slice_of hc (gstart q + wlen q + 2) 1 (by unfold gstart wlen; split_ifs <;> omega)
  simp only [Nat.add_assoc] at h ⊢
  convert h using 1
  rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl

theorem ztNat_lt (r : Nat) : ztNat r < 256 := by have := ztNat_le r; omega

theorem load_spec {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (s : MachineState) (v : Digest) (q : Nat) (hq : q < 17) (ht : ZtOK b s)
    (hpc : s.pc = pcOf (zcBase b + gstart q + wlen q + 2))
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (ZTB b + topRank v q)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (zcBase b + gstart q + wlen q + 3) ∧
      t.getReg .x10 = BitVec.ofNat 64 (ztNat (topRank v q)) ∧ RegsExcept s t [.x10] ∧
      Frame s t (fun _ => False) := by
  have hr := topRank_lt v q
  have hoff : signExtend12 (BitVec.ofNat 12 (zoff b % 4096)) = BitVec.ofNat 64 (zoff b) := by
    rcases hb with rfl | rfl <;> decide +kernel
  have ha : s.getReg .x10 + signExtend12 (BitVec.ofNat 12 (zoff b % 4096)) =
      BitVec.ofNat 64 (ZT b + topRank v q) := by
    rw [h10, hoff, ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rcases hb with rfl | rfl <;> simp [ZTB, ZT, zoff] <;> omega
  have hv : accessValid (s.getReg .x10 + signExtend12 (BitVec.ofNat 12 (zoff b % 4096))) 1 = true := by
    rw [ha, accessValid_iff]
    have hbnd : ZT b + topRank v q < 2 ^ 64 := by unfold ZT; split_ifs <;> omega
    rw [toNat_ofNat_lt hbnd]
    simp only [MEMORY_BYTES, Nat.mod_one, and_true, true_and]
    unfold ZT; split_ifs <;> omega
  have hs := steps_lbu (code_load hb hc q hq) hpc (lbu_decode b hb) hv
  rw [ha, ht _ hr] at hs
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · change s.pc + 4 = _
    rw [hpc, pcOf_add4]
  · change (s.setReg .x10 ((ztByte (topRank v q)).zeroExtend 64)).getReg .x10 = _
    rw [MachineState.getReg_setReg_eq (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [ztByte, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := ztNat_lt (topRank v q)
    omega
  · intro r hr; simp only [List.mem_singleton] at hr
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)
  · intro A _ _; rfl

def addCode : List (BitVec 32) := [0xae8eb3]
sym_block addBase := symRun {noAlias := true} addCode 0#64 2
theorem add_run (pc : Word) : symRun {noAlias := true} addCode pc 2 =
    some ⟨addBase.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by rfl
theorem code_add {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (q : Nat) (hq : q < 17) : CodeAt image (pcOf (zcBase b + gstart q + wlen q + 3)) addCode := by
  have h := codeAt_slice_of hc (gstart q + wlen q + 3) 1 (by unfold gstart wlen; split_ifs <;> omega)
  simp only [Nat.add_assoc] at h ⊢
  convert h using 1
  rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl
theorem add_spec {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (s : MachineState) (q : Nat) (hq : q < 17) (a z : Word)
    (hpc : s.pc = pcOf (zcBase b + gstart q + wlen q + 3)) (h29 : s.getReg .x29 = a) (h10 : s.getReg .x10 = z) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (zcBase b + gstart q + wlen q + 4) ∧
      t.getReg .x29 = a + z ∧ RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (add_run _) (code_add hb hc q hq) s hpc (by simp [addBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval, pcOf_add4, Nat.add_assoc, Nat.reduceAdd]
  · simpa [addBase.res, rv_simp] using congrArg₂ (fun x y : Word => x + y) h29 h10
  · intro r hr; cases r <;> simp_all [addBase.res, rv_simp] <;> rfl
  · intro A _ _; rfl

theorem gstart_succ (q : Nat) (hq : q < 17) : gstart (q + 1) = gstart q + wlen q + 4 := by
  interval_cases q <;> rfl

theorem group_spec {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (s : MachineState) (v : Digest) (q : Nat) (hq : q < 17) (acc : Nat) (ht : ZtOK b s)
    (hpc : s.pc = pcOf (zcBase b + gstart q))
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 acc) :
    ∃ t, Steps image s (wlen q + 4) (wlen q + 4) t ∧ t.pc = pcOf (zcBase b + gstart (q + 1)) ∧
      t.getReg .x29 = BitVec.ofNat 64 (acc + ztNat (topRank v q)) ∧
      RegsExcept s t [.x10, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, g1, r1, f1⟩ := pre_spec hb hc s v q hq hpc h6 h7
  obtain ⟨t2, s2, p2, g2, r2, f2⟩ := load_spec hb hc t1 v q hq (ht.frame f1 (by simp)) p1 g1
  obtain ⟨t3, s3, p3, g3, r3, f3⟩ := add_spec hb hc t2 q hq _ _ p2
    (by rw [r2.get (by decide), r1.get (by decide), h29]) g2
  refine ⟨t3, by simpa only [Nat.add_assoc] using (s1.trans s2).trans s3, ?_, ?_,
    ((r1.trans r2).trans r3).mono (by decide), ((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [gstart_succ q hq]; simpa only [Nat.add_assoc] using p3
  · simpa only [ofNat_add_ofNat] using g3

theorem iter {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (s : MachineState) (v : Digest) (n : Nat) (hn : n ≤ 17) (ht : ZtOK b s)
    (hpc : s.pc = pcOf (zcBase b + 1))
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 0) :
    ∃ t, Steps image s (gstart n - 1) (gstart n - 1) t ∧ t.pc = pcOf (zcBase b + gstart n) ∧
      t.getReg .x29 = BitVec.ofNat 64 (runningZ v n) ∧
      RegsExcept s t [.x10, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  induction n with
  | zero => exact ⟨s, Steps.refl _, by simpa [gstart] using hpc, by simpa [runningZ] using h29,
      RegsExcept.refl _ _, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨t1, s1, p1, g1, r1, f1⟩ := ih (by omega)
    obtain ⟨t2, s2, p2, g2, r2, f2⟩ := group_spec hb hc t1 v n (by omega) (runningZ v n)
      (ht.frame f1 (by simp)) p1 (by rw [r1.get (by decide), h6]) (by rw [r1.get (by decide), h7]) g1
    refine ⟨t2, ?_, p2, ?_, (r1.trans r2).mono (by decide), (f1.trans f2).mono (by simp)⟩
    · have he : gstart n - 1 + (wlen n + 4) = gstart (n + 1) - 1 := by
        rw [gstart_succ n (by omega)]
        have : 1 ≤ gstart n := by unfold gstart; split_ifs <;> omega
        omega
      simpa only [he] using s1.trans s2
    · simpa only [runningZ_succ] using g2

def initCode : List (BitVec 32) := [0xe93]
sym_block initBase := symRun {noAlias := true} initCode 0#64 2
theorem init_run (pc : Word) : symRun {noAlias := true} initCode pc 2 =
    some ⟨initBase.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by rfl
theorem init_spec {b : Nat} (hc : CodeAt image (pcOf (zcBase b)) (code b)) (s : MachineState)
    (hpc : s.pc = pcOf (zcBase b)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (zcBase b + 1) ∧ t.getReg .x29 = 0 ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc0 : CodeAt image (pcOf (zcBase b)) initCode := by
    have h := codeAt_slice_of hc 0 1 (by omega)
    have e : ((code b).drop 0).take 1 = initCode := by unfold code initCode; simp
    rw [e, Nat.add_zero] at h; exact h
  refine ⟨_, symRun_sound (init_run _) hc0 s hpc (by simp [initBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval, pcOf_add4]
  · simp [initBase.res, rv_simp]
  · intro r hr; cases r <;> simp_all [initBase.res, rv_simp] <;> rfl
  · intro A _ _; rfl

def tailCode (b : Nat) : List (BitVec 32) := tailW b
sym_block tailBaseS := symRun {noAlias := true} (tailW 543) (pcOf (21667 + 104)) 20
sym_block tailBaseE := symRun {noAlias := true} (tailW 354) (pcOf (43077 + 104)) 20
def tailResult (b : Nat) : Result :=
  ⟨tailBaseS.res.st, .ite .geu tailBaseS.res.st.regs.r29 (.c 10#64) (.c (pcOf (zcFail b)))
    (.c (pcOf (zcBase b + 117))), .branch, 13, 13⟩
theorem tail_run (b : Nat) (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} (tailW b) (pcOf (zcBase b + 104)) 20 = some (tailResult b) := by
  rcases hb with rfl | rfl
  · exact tailBaseE.trans (congrArg some (by kernel_rfl))
  · exact tailBaseS.trans (congrArg some (by kernel_rfl))

theorem ult_and7 (r : Nat) (hr : r < 512) : (BitVec.ofNat 64 r &&& 7#64).ult 1#64 = decide (r % 8 = 0) := by
  have h : (BitVec.ofNat 64 r &&& 7#64).toNat = r % 8 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (7#64).toNat = 2 ^ 3 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [BitVec.ult, h]; simp
theorem ult_mid (r : Nat) (hr : r < 512) :
    (BitVec.ofNat 64 r >>> 3 &&& 7#64).ult 1#64 = decide (r / 8 % 8 = 0) := by
  have h : (BitVec.ofNat 64 r >>> 3 &&& 7#64).toNat = r / 8 % 8 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      show (7#64).toNat = 2 ^ 3 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    omega
  simp only [BitVec.ult, h]; simp
theorem ult_hi (r : Nat) (hr : r < 512) : (BitVec.ofNat 64 r >>> 6).ult 1#64 = decide (r / 64 = 0) := by
  have h : (BitVec.ofNat 64 r >>> 6).toNat = r / 64 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  simp only [BitVec.ult, h]; simp

theorem tail_eval (s : MachineState) (v : Digest) (acc : Nat) (ha : acc ≤ 51)
    (h7 : s.getReg .x7 = v.extractLsb' 64 64) (h29 : s.getReg .x29 = BitVec.ofNat 64 acc) :
    tailBaseS.res.st.regs.r29.eval s = BitVec.ofNat 64 (acc + tailZeros (tailField v)) := by
  have hf : s.getReg .x7 >>> 55 = BitVec.ofNat 64 (tailField v) := by
    rw [h7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
    have := v.isLt
    unfold tailField
    omega
  have hr : tailField v < 512 := by unfold tailField; omega
  simp only [tailBaseS.res, rv_simp, E.eval, BinOp.eval, h29]
  simp only [show (55#64).toNat % 64 = 55 by rfl, show (3#64).toNat % 64 = 3 by rfl,
    show (6#64).toNat % 64 = 6 by rfl, hf, ult_and7 _ hr, ult_mid _ hr, ult_hi _ hr]
  apply BitVec.eq_of_toNat_eq
  unfold tailZeros
  split_ifs <;> simp_all [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

theorem code_tail {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b)) :
    CodeAt image (pcOf (zcBase b + 104)) (tailW b) := by
  have h := codeAt_slice_of hc 104 13 (by omega)
  convert h using 1
  rcases hb with rfl | rfl <;> kernel_rfl
sym_block jalS := symRun {noAlias := true} [jalW 543] (pcOf (21667 + 117)) 2
sym_block jalE := symRun {noAlias := true} [jalW 354] (pcOf (43077 + 117)) 2
theorem jal_run (b : Nat) (hb : b = 354 ∨ b = 543) :
    symRun {noAlias := true} [jalW b] (pcOf (zcBase b + 117)) 2 =
      some ⟨SymState.init, .c (pcOf (zcPass b)), .jump, 1, 1⟩ := by
  rcases hb with rfl | rfl
  · exact jalE.trans (congrArg some (by kernel_rfl))
  · exact jalS.trans (congrArg some (by kernel_rfl))
theorem code_jal {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b)) :
    CodeAt image (pcOf (zcBase b + 117)) [jalW b] := by
  have h := codeAt_slice_of hc 117 1 (by omega)
  convert h using 1
  rcases hb with rfl | rfl <;> kernel_rfl

theorem jal_regs (t : MachineState) (e : E) :
    RegsExcept t (Result.toState ⟨SymState.init, e, .jump, 1, 1⟩ t) [] := by
  intro r hr; cases r <;> simp [SymState.init, rv_simp] <;> rfl
theorem zcount_le (v : Digest) : runningZ v 17 ≤ 51 := runningZ_le v 17

/-- The whole zero-cap routine: pass (`≤ 9` zero digits) to `zcPass`, fail to `zcFail` (the `choice_r` entry). -/
theorem zc_spec {b : Nat} (hb : b = 354 ∨ b = 543) (hc : CodeAt image (pcOf (zcBase b)) (code b))
    (s : MachineState) (v : Digest) (ht : ZtOK b s) (hpc : s.pc = pcOf (zcBase b))
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ k t, Steps image s k k t ∧ k ≤ 118 ∧
      t.pc = (if zcount v ≤ 9 then pcOf (zcPass b) else pcOf (zcFail b)) ∧
      RegsExcept s t [.x10, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, g0, r0, f0⟩ := init_spec hc s hpc
  obtain ⟨t1, s1, p1, g1, r1, f1⟩ := iter hb hc t0 v 17 (by omega) (ht.frame f0 (by simp)) p0
    (by rw [r0.get (by decide), h6]) (by rw [r0.get (by decide), h7]) g0
  have hacc := zcount_le v
  have p1' : t1.pc = pcOf (zcBase b + 104) := by simpa [gstart] using p1
  have hsr := symRun_sound (tail_run b hb) (code_tail hb hc) t1 p1' (by simp [tailResult, tailBaseS.res, rv_simp])
  set t2 := (tailResult b).toState t1 with ht2
  have g2 : t2.getReg .x29 = BitVec.ofNat 64 (zcount v) := by
    change tailBaseS.res.st.regs.r29.eval t1 = _
    rw [tail_eval t1 v (runningZ v 17) hacc (by rw [r1.get (by decide), r0.get (by decide), h7]) g1]
    rfl
  have r2 : RegsExcept t1 t2 [.x10, .x28, .x29] := by
    intro r hr; cases r <;> simp_all [ht2, tailResult, tailBaseS.res, rv_simp] <;> rfl
  have f2 : Frame t1 t2 (fun _ => False) := by intro A _ _; rfl
  have hz : zcount v < 2 ^ 64 := by unfold zcount tailZeros; split_ifs <;> omega
  have p2 : t2.pc = (if zcount v ≥ 10 then pcOf (zcFail b) else pcOf (zcBase b + 117)) := by
    change (if CmpOp.eval .geu (tailBaseS.res.st.regs.r29.eval t1) 10#64 then _ else _) = _
    rw [show tailBaseS.res.st.regs.r29.eval t1 = BitVec.ofNat 64 (zcount v) from g2]
    by_cases h : zcount v ≥ 10
    · rw [if_pos h]; simp only [CmpOp.eval, E.eval, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hz]
      simp; omega
    · rw [if_neg h]; simp only [CmpOp.eval, E.eval, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hz]
      simp; omega
  by_cases hp : zcount v ≤ 9
  · rw [if_neg (by omega)] at p2
    have hj := symRun_sound (jal_run b hb) (code_jal hb hc) t2 p2 (by simp [SymState.init, rv_simp])
    have rj : RegsExcept t2 (Result.toState ⟨SymState.init, .c (pcOf (zcPass b)), .jump, 1, 1⟩ t2) [] :=
      jal_regs t2 _
    have fj : Frame t2 (Result.toState ⟨SymState.init, .c (pcOf (zcPass b)), .jump, 1, 1⟩ t2) (fun _ => False) :=
      fun _ _ _ => rfl
    refine ⟨_, _, ((s0.trans s1).trans hsr).trans hj, by simp [gstart, tailResult], ?_, ?_, ?_⟩
    · rw [if_pos hp]; rfl
    · exact RegsExcept.mono (l' := [.x10, .x28, .x29])
        (((r0.trans r1).trans r2).trans rj) (by simp)
    · exact (((f0.trans f1).trans f2).trans fj).mono (by simp)
  · rw [if_pos (by omega)] at p2
    refine ⟨_, _, (s0.trans s1).trans hsr, by simp [gstart, tailResult], by rw [if_neg hp]; exact p2, ?_, ?_⟩
    · exact ((r0.trans r1).trans r2).mono (by simp)
    · exact ((f0.trans f1).trans f2).mono (by simp)

end blocks
end SigGolfCandidate.T3M.Search.ZeroCap
