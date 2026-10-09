import SigGolfCandidate.T3M.Verify.BCWords
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP
import SigGolfCandidate.T3M.Verify.ChainGood
import SigGolfCandidate.T3M.Verify.LowerDecode

section
namespace SigGolfCandidate.T3M.Verify
theorem swar7_split (x m : BitVec 64) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x[i] <;> cases m[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]; cases x[i] <;> cases m[i] <;> rfl
theorem swar7_period : ∀ i : Fin 61,
    (0x71c71c71c71c71c7#64).getLsbD i.val = !(0x71c71c71c71c71c7#64).getLsbD (i.val + 3) := by
  decide +kernel
theorem swar7_shift (x : BitVec 64) :
    (x >>> 3) &&& 0x71c71c71c71c71c7#64 = (x &&& ~~~0x71c71c71c71c71c7#64) >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 61
  · have hp := swar7_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 3 + i = i + 3 by omega]
    simp [show i + 3 < 64 by omega]
  · have hx : x.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar7_low (x : BitVec 64) : (x &&& ~~~0x71c71c71c71c71c7#64).toNat % 8 = 0 := by
  have h7 : (x &&& ~~~0x71c71c71c71c71c7#64) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 3
    · have : (0x71c71c71c71c71c7#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +kernel
      simp [this]
    · have : (7#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 7 < 2 ^ 3 := by decide +kernel
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide +kernel) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar7_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 63) :
    ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64)) +
      (((a + b) - ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64))) >>> 3) =
    ((a >>> 3) &&& 0x71c71c71c71c71c7#64) + (a &&& 0x71c71c71c71c71c7#64) +
      ((b >>> 3) &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64) := by
  rw [swar7_shift a, swar7_shift b]
  set M : BitVec 64 := 0x71c71c71c71c71c7#64 with hM
  have la := swar7_low a
  have lb := swar7_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0x8e38e38e38e38e38 := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat ≤ 0x0e38e38e38e38e38 := by
    have hb' : b.toNat % 2 ^ 63 = b.toNat := Nat.mod_eq_of_lt hb
    have he := Nat.and_mod_two_pow (a := b.toNat) (b := (~~~M).toNat) (n := 63)
    rw [hb', Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hb)] at he
    rw [BitVec.toNat_and, he]
    simpa [hM] using (Nat.and_le_right : b.toNat &&& ((~~~M).toNat % 2 ^ 63) ≤ (~~~M).toNat % 2 ^ 63)
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 3 = ((a &&& ~~~M) >>> 3) + ((b &&& ~~~M) >>> 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
theorem swar2_period : ∀ i : Fin 62,
    (0x3333333333333333#64).getLsbD i.val = !(0x3333333333333333#64).getLsbD (i.val + 2) := by
  decide +kernel
theorem swar2_shift (x : BitVec 64) :
    (x >>> 2) &&& 0x3333333333333333#64 = (x &&& ~~~0x3333333333333333#64) >>> 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 62
  · have hp := swar2_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 2 + i = i + 2 by omega]
    simp [show i + 2 < 64 by omega]
  · have hx : x.getLsbD (2 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar2_low (x : BitVec 64) : (x &&& ~~~0x3333333333333333#64).toNat % 4 = 0 := by
  have h7 : (x &&& ~~~0x3333333333333333#64) &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 2
    · have : (0x3333333333333333#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide +kernel
      simp [this]
    · have : (3#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 3 < 2 ^ 2 := by decide +kernel
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide +kernel) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (3#64).toNat = 2 ^ 2 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar2_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 34) :
    ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64)) +
      (((a + b) - ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64))) >>> 2) =
    ((a >>> 2) &&& 0x3333333333333333#64) + (a &&& 0x3333333333333333#64) +
      ((b >>> 2) &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64) := by
  rw [swar2_shift a, swar2_shift b]
  set M : BitVec 64 := 0x3333333333333333#64 with hM
  have la := swar2_low a
  have lb := swar2_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0xcccccccccccccccc := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat < 2 ^ 34 := by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_left hb
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 2 = ((a &&& ~~~M) >>> 2) + ((b &&& ~~~M) >>> 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
end SigGolfCandidate.T3M.Verify
end
section
namespace SigGolfCandidate.T3M.BC
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest Layer route)
open ClaudeWCT.WCT9 (LayerMsg)
def below (lay : Nat) : Nat := [19,12,6,0].getD lay 0
def layerEnd (lay : Nat) : Nat := [11648,14768,17824,20880].getD lay 0
def cpIdx (index lay : Nat) : Nat := if lay = 3 then 0 else index / 2 ^ below (lay + 1) % 2 ^ hL (lay + 1)
def MsgAt (w : ClaudeWCT.W9.T3M.WBytes) (index lay : Nat) (msg : LayerMsg) (s : MachineState) : Prop :=
  match msg with
  | .forest root => lay = 3 ∧ DigAt s WIT root
  | .pair left right => lay < 3 ∧ DigAt s (rowA lay (cpIdx index lay)) left ∧
      DigAt s (rowA lay (cpIdx index lay) + 48) right ∧
      (∀ j, j = 4 ∨ j = 5 →
        s.getMem (BitVec.ofNat 64 (rowA lay (cpIdx index lay) + 8 * j)) =
          wword w ((rowA lay (cpIdx index lay) - WIT) / 8 + j))
structure LayerIn (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index lay : Nat) (msg : LayerMsg)
    (s : MachineState) : Prop where
  lay4 : lay < 4
  idx : index < 2 ^ 31
  copy : s.pc = pcOf (T3M.setupPc lay (trPc lay (cpIdx index lay)))
  glob : Glob (preK lay) w pk s
  route : s.getReg (rReg lay) = BitVec.ofNat 64 (index / 2 ^ below lay)
  word : lay < 3 → s.getReg .x28 = T3.hyperWord lay (index / 2 ^ below lay)
  msg : MsgAt w index lay msg s
  orig : Verify.Orig w (fun o => 7424 ≤ o ∧ o < layerEnd lay) s
  hdr3 : lay = 3 → s.getMem (BitVec.ofNat 64 (TOPLOAD + 32)) = BitVec.ofNat 64 (hyperBase 3) ∧
    s.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21200 ∧
    (∀ k, k < 5 → s.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) = BitVec.ofNat 64 (topWords.getD k 0))
  dst : lay < 3 → ∃ d, s.getReg .x12 = BitVec.ofNat 64 d ∧
    (d = rowA lay (cpIdx index lay) ∨ d = rowA lay (cpIdx index lay) + 48)
structure EncPre (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index lay c : Nat)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (trPc lay c + stepsA lay)
  glob : Glob (bK lay c) w pk t
  word : t.getReg .x28 = T3.hyperWord lay (index / 2 ^ below lay)
  s7 : ∀ L : Layer, L.val = lay → lay < 3 →
    t.getReg .x23 = BitVec.ofNat 64 (dispatchHeap lay (route index L).1)
  t5 : ∀ L : Layer, L.val = lay →
    (lay ≠ 0 → lay < 3 → t.getReg .x31 = BitVec.ofNat 64 (route index L).2) ∧
    (lay = 0 → t.getReg .x31 = BitVec.ofNat 64 (route index L).1)
  orig : Verify.Orig w (fun o => 7424 ≤ o ∧ o < layerEnd lay) t
  hdr3 : lay = 3 → t.getMem (BitVec.ofNat 64 (TOPLOAD + 32)) = BitVec.ofNat 64 (hyperBase 3) ∧
    t.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = BitVec.ofNat 64 21200 ∧
    (∀ k, k < 5 → t.getMem (BitVec.ofNat 64 (TOPLOAD + 8 * k)) = BitVec.ofNat 64 (topWords.getD k 0))
  index3 : lay = 3 → t.getReg .x22 = BitVec.ofNat 64 index
  dst : lay < 3 → ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧ (d = rowA lay c ∨ d = rowA lay c + 48)
def rejectSteps (lay : Nat) : Nat := stepsA lay + if lay = 3 then 21 else 3
def EncodingSetup : Prop :=
  ∀ (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer)
    (msg : LayerMsg) (s : MachineState), LayerIn w pk index lay.val msg s →
  ((ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat ≥ ClaudeWCT.WCT9.verifyWindow →
    ∃ u, Steps image s (rejectSteps lay.val) (rejectSteps lay.val) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
  ((ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < ClaudeWCT.WCT9.verifyWindow →
    ∃ t, Steps image s (stepsA lay.val) (stepsA lay.val) t ∧
      fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = toQ (T3.pad64 (ClaudeWCT.W9.T3M.layerEncodingInputP lay
        (route index lay).2 (route index lay).1 msg
        (ClaudeWCT.W9.T3M.wbcCtr w index lay) (ClaudeWCT.W9.T3M.wbcPad w index lay) (ClaudeWCT.W9.T3M.wbcRight w))) ∧
      EncPre w pk index lay.val (cpIdx index lay.val) t)
def layerLoop (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) : Nat → LayerMsg → T3.M (Option Digest)
  | 0, .forest root => pure (some root)
  | 0, .pair _ _ => pure none
  | n + 1, msg => ClaudeWCT.W9.T3M.layersBC w index (n + 1) msg
end SigGolfCandidate.T3M.BC
end
section
set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64)
def below (lay : Nat) : Nat := [19,12,6,0].getD lay 0
def layerEnd (lay : Nat) : Nat := [11648,14768,17824,20880].getD lay 0
theorem hL_eq (lay : Layer) : hL lay.val = height lay := by fin_cases lay <;> rfl
def slotT (i : Nat) : Nat := 544 + 16 * i
theorem below_eq (lay : Layer) : below lay.val = (![19, 12, 6, 0] : Layer → Nat) lay := by fin_cases lay <;> rfl
theorem tgtL_eq (lay : Layer) : tgtL lay.val = target lay := by fin_cases lay <;> rfl
abbrev LayerIn := BC.LayerIn
theorem route_fst (index : Nat) (lay : Layer) : (route index lay).1 = index / 2 ^ below lay.val % 2 ^ hL lay.val := by
  simp only [route, below_eq, hL_eq]
theorem route_snd (index : Nat) (lay : Layer) : (route index lay).2 = index / 2 ^ (below lay.val + hL lay.val) := by
  simp only [route, below_eq, hL_eq]
theorem leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ hL lay.val := by
  rw [route_fst]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
theorem hL_le (lay : Layer) : 6 ≤ hL lay.val ∧ hL lay.val ≤ 12 := by fin_cases lay <;> decide +kernel
theorem tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  rw [route_snd]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
theorem tree_actual_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 < 2 ^ (31 - height lay) := by
  rw [route_snd]
  fin_cases lay <;> norm_num [below, hL, height] at * <;> omega
theorem routed_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  rw [route_snd, route_fst, ← hL_eq]
  fin_cases lay <;> norm_num [below, hL] at * <;> omega
theorem leaf_lt32 (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h1 := leaf_lt index lay
  have h2 := (hL_le lay).2
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega : hL lay.val ≤ 32))
theorem route_evals (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) (s : MachineState)
    (h : s.getReg (rReg lay.val) = BitVec.ofNat 64 (index / 2 ^ below lay.val)) :
    (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 ∧
      (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 ∧
      (tpE lay.val).eval s = BitVec.ofNat 64 (hdr1 (route index lay).2 (route index lay).1) ∧
      (s7E lay.val).eval s = BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) := by
  have hl := leaf_lt index lay
  have ht := tree_lt index lay hidx
  have hl32 := leaf_lt32 index lay
  have hU : index / 2 ^ below lay.val < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hlE : (leafE lay.val).eval s = BitVec.ofNat 64 (route index lay).1 := by
    rw [route_fst]
    unfold leafE
    split
    · rename_i h0
      have hl0 : lay = 0 := Fin.ext h0
      subst hl0
      simp only [E.eval]
      rw [show rReg (0 : Layer).val = .x31 from rfl] at h
      rw [h]; congr 1
      simp only [show below (0 : Layer).val = 19 from rfl, show hL (0 : Layer).val = 12 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
    · simp only [E.eval, BinOp.eval, h, kw]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hU, Nat.mod_eq_of_lt (show 2 ^ hL lay.val - 1 < 2 ^ 64 by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide +kernel) (hL_le lay).2; omega),
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by have := (hL_le lay).2; omega)))]
  have htE : (treeE lay.val).eval s = BitVec.ofNat 64 (route index lay).2 := by
    rw [route_snd]
    simp only [treeE, E.eval, BinOp.eval, h, kw]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hU,
      Nat.mod_eq_of_lt (show hL lay.val < 2 ^ 64 by have := (hL_le lay).2; omega),
      Nat.mod_eq_of_lt (show hL lay.val < 64 by have := (hL_le lay).2; omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  refine ⟨hlE, htE, ?_, ?_⟩
  · by_cases h0 : lay.val = 0
    ·
      have hz : (route index lay).2 = 0 := by
        have : lay = 0 := Fin.ext h0
        subst this
        rw [route_snd]; exact Nat.div_eq_of_lt (by simpa [below, hL] using hidx)
      simp only [tpE, if_pos h0, E.eval, BinOp.eval, hlE, kw]
      rw [hz, hdr1_eq _ _ (by norm_num) hl32]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
        show 32 % 64 = 32 from rfl, Nat.shiftLeft_eq]
      have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      ring
    simp only [tpE, if_neg h0, E.eval, BinOp.eval, hlE, htE, kw]
    rw [hdr1_eq _ _ ht hl32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (32 : Nat) < 2 ^ 64 by norm_num),
      show 32 % 64 = 32 from rfl, Nat.mod_eq_of_lt (show (route index lay).2 < 2 ^ 64 by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (route index lay).1 * 2 ^ 32 < 2 ^ 64 by
        have : (route index lay).1 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hl32 (by norm_num)
        omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (route index lay).2 + 2 ^ 32 * (route index lay).1 < 2 ^ 64 by omega)]
    rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ht]
    ring
  · by_cases h0 : lay.val = 0
    · have hl0 : (route index lay).1 < 4096 := by simpa [hL, h0] using hl
      simp only [s7E, dispatchHeap, if_pos h0, E.eval, BinOp.eval, hlE, kw]
      rw [h0]
      simp only [s7Bias, hL, List.getD_cons_zero]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show (route index lay).1 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show (4 : Nat) < 2 ^ 64 by decide),
        show 4 % 64 = 4 from rfl, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (show (route index lay).1 * 2 ^ 4 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 16 * 2 ^ 12 < 2 ^ 64 by decide),
        BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 16 * (4096 + (route index lay).1) < 2 ^ 64 by omega)]
      have h16 : (route index lay).1 * 2 ^ 4 < 2 ^ 16 := by omega
      rw [Nat.lor_comm, show (16 * 2 ^ 12 : Nat) = 2 ^ 16 * 1 by decide, ← Nat.two_pow_add_eq_or_of_lt h16]
      omega
    · simp only [s7E, if_neg h0, E.eval, BinOp.eval, hlE, kw, dispatchHeap]
      change BitVec.ofNat 64 (route index lay).1 + BitVec.ofNat 64 (s7Bias lay.val) =
        BitVec.ofNat 64 (s7Bias lay.val + (route index lay).1)
      rw [ofNat_add_ofNat]
      simp [Nat.add_comm]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 lowerSpare lowerWord)
theorem ctrE_eval (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (s : MachineState) (hH : WitHdr w s) :
    (ctrE 3).eval s = BitVec.ofNat 64 (ClaudeWCT.W9.T3M.wbcCtr w index 3).toNat := by
  have hw := hH 4 (by decide +kernel) (by decide +kernel)
  rw [show WIT + 8 * 4 = 0x810 + 8 * ((3 + 1) / 2) by unfold WIT; rfl] at hw
  show LoadKind.wu.fromWord (s.getMem (BitVec.ofNat 64 (0x810 + 8 * ((3 + 1) / 2)))) (4 * ((3 + 1) % 2)) = _
  rw [hw]
  exact BC.counterWord w 4
theorem ctr_lt (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) :
    (ClaudeWCT.W9.T3M.wbcCtr w index lay).toNat < 2 ^ 32 :=
  (ClaudeWCT.W9.T3M.wbcCtr w index lay).isLt
theorem copy_parts (lay c : Nat) (h : BC.copyCheck lay c = true) :
    specB (BC.allowed lay c) [] baseK (runAt (BC.preK lay) [] (T3M.setupPc lay (trPc lay c))
      []) (BC.specA lay c) [] (BC.bK lay c) (BC.keepA lay) = true ∧
    (lay ≠ 0 →
      specB [] [] baseK (runAt (BC.bKB lay c) [] (trPc lay c + stepsA lay + 1)
        [.br (decide (lay = 3)), .br false, .jmp])
        (specBl lay (trPc lay c)) BC.oblB (postBlC lay (trPc lay c)) (keepB lay) = true ∧
      specB [] [] [] (runAt (BC.bKB lay c) [] (trPc lay c + stepsA lay + 1)
        [.br (decide (lay = 3)), .br true]) (rejCk lay)
        BC.oblB [] [] = true ∧
      specB [] [] [] (runAt (BC.bKB lay c) [] (trPc lay c + stepsA lay + 1)
        [.br (decide (lay ≠ 3))]) (rejSpare lay) BC.oblB [] [] = true) := by
  unfold BC.copyCheck BC.setupCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h3⟩ := h
  refine ⟨h1, fun h0 => ?_⟩
  rw [if_neg h0] at h3; simp only [Bool.and_eq_true] at h3; exact ⟨h3.1.1, h3.1.2, h3.2⟩
abbrev EncPre := BC.EncPre
theorem hw4_hdr0 (lay : Layer) (tree : Nat) (ht : tree < 2 ^ 32) : hw 4 lay.val = hdr0 4 lay.val tree 0 := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by have := lay.isLt; omega) ht (by norm_num)]
  unfold hw; ring
theorem toNat_srl (x : Word) (k : Nat) (hk : k < 64) : (x >>> ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]
theorem toNat_sll (x : Word) (k : Nat) (hk : k < 64) :
    (x <<< ((BitVec.ofNat 64 k).toNat % 64)).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.shiftLeft_eq]
theorem toNat_andc (x : Word) (k : Nat) (hk : k < 2 ^ 64) : (x &&& BitVec.ofNat 64 k).toNat = x.toNat &&& k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
theorem toNat_remuc (x : Word) (k : Nat) (hk : 0 < k) (hk' : k < 2 ^ 64) :
    (rv64_remu x (BitVec.ofNat 64 k)).toNat = x.toNat % k := by
  unfold rv64_remu
  have hne : (BitVec.ofNat 64 k == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk'] at this
    simp at this; omega
  rw [hne]
  simp only [Bool.false_eq_true, if_false, BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']
structure AnsAt (u : MachineState) (a : BitVec 256) : Prop where
  lo : a6E.eval u = a.extractLsb' 0 64
  hi : a7E.eval u = a.extractLsb' 64 64
abbrev ansV (a : BitVec 256) : Nat := (a.extractLsb' 0 128).toNat
theorem ansV_split (a : BitVec 256) :
    ansV a = (a.extractLsb' 0 64).toNat + 2 ^ 64 * (a.extractLsb' 64 64).toNat := by
  simp only [ansV, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  generalize a.toNat = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
theorem ansV_lo (a : BitVec 256) : ansV a % 2 ^ 64 = (a.extractLsb' 0 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega
theorem ansV_hi (a : BitVec 256) : ansV a / 2 ^ 64 = (a.extractLsb' 64 64).toNat := by
  rw [ansV_split]; have := (a.extractLsb' 0 64).isLt; omega
theorem a6E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a6E.eval u = a.extractLsb' 0 64 := h.lo
theorem a7E_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) : a7E.eval u = a.extractLsb' 64 64 := h.hi
theorem toNat_clr63 (x : BitVec 64) : (BitVec.ofNat 64 (x.toNat % 2 ^ 63)).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_ofNat]; omega
theorem clr63_M1 (x : BitVec 64) :
    x &&& 0x71c71c71c71c71c7#64 = BitVec.ofNat 64 (x.toNat % 2 ^ 63) &&& 0x71c71c71c71c71c7#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and, toNat_clr63]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_land, Nat.testBit_mod_two_pow]
  by_cases hi : i < 63
  · simp [hi]
  · have : Nat.testBit 8198552921648689607 i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (show 8198552921648689607 < 2 ^ 63 by decide +kernel)
        (Nat.pow_le_pow_right (by decide +kernel) (by omega)))
    simp [this]
theorem add_clr63 (x y : BitVec 64) (hx : 2 ^ 63 ≤ x.toNat) (hy : 2 ^ 63 ≤ y.toNat) :
    x + y = BitVec.ofNat 64 (x.toNat % 2 ^ 63) + BitVec.ofNat 64 (y.toNat % 2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := y.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega
theorem sw1_bv (x y : BitVec 64) :
    (((x >>> 3) &&& 0x71c71c71c71c71c7#64) + (x &&& 0x71c71c71c71c71c7#64) +
      ((y >>> 3) &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64)).toNat = sw1 x.toNat y.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold sw1 mask3
  rfl
theorem swS1 (x y : BitVec 64) (hx : 2 ^ 63 ≤ x.toNat) (hy : 2 ^ 63 ≤ y.toNat) :
    (((x &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64)) +
      (((x + y) - ((x &&& 0x71c71c71c71c71c7#64) + (y &&& 0x71c71c71c71c71c7#64))) >>> 3)).toNat =
    sw1 (x.toNat % 2 ^ 63) (y.toNat % 2 ^ 63) := by
  rw [clr63_M1 x, clr63_M1 y, add_clr63 x y hx hy,
    Verify.swar7_eq _ _ (by rw [toNat_clr63]; omega), sw1_bv, toNat_clr63, toNat_clr63]
abbrev ansD (a : BitVec 256) : Digest := a.extractLsb' 0 128
theorem ansD_lo (a : BitVec 256) : (ansD a).toNat % 2 ^ 64 = (a.extractLsb' 0 64).toNat := ansV_lo a
theorem ansD_hi (a : BitVec 256) : (ansD a).toNat / 2 ^ 64 = (a.extractLsb' 64 64).toNat := ansV_hi a
theorem spare_iff (a : BitVec 256) :
    lowerSpare (ansD a) ↔ 2 ^ 63 ≤ (a.extractLsb' 0 64).toNat ∧ 2 ^ 63 ≤ (a.extractLsb' 64 64).toNat := by
  have hlo := ansD_lo a
  have hhi := ansD_hi a
  have hlt := (ansD a).isLt
  have h0 := (a.extractLsb' 0 64).isLt
  have h1 := (a.extractLsb' 64 64).isLt
  unfold lowerSpare
  constructor
  · rintro ⟨e0, e1⟩; constructor <;> omega
  · rintro ⟨e0, e1⟩; constructor <;> omega
theorem sumE_eval {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hs : lowerSpare (ansD a))
    (lay : Nat) (hm1 : (M1E lay).eval u = BitVec.ofNat 64 M1c)
    (hm2 : (M2E lay).eval u = BitVec.ofNat 64 M2c) :
    ((sumE lay).eval u).toNat = lowSumS1 (ansD a) := by
  obtain ⟨h6, h7⟩ := (spare_iff a).mp hs
  have he : (BitVec.ofNat 64 3).toNat % 64 = 3 := by decide +kernel
  have hs1 : ((sw1E lay).eval u).toNat = sw1 ((a.extractLsb' 0 64).toNat % 2 ^ 63) ((a.extractLsb' 64 64).toNat % 2 ^ 63) := by
    simp only [sw1E, swLowE, E.eval, BinOp.eval, kw, hm1, M1c, he, a6E_eval h, a7E_eval h]
    exact swS1 _ _ h6 h7
  have hlo : (a.extractLsb' 0 64).toNat % 2 ^ 63 = (ansD a).toNat % 2 ^ 63 := by
    rw [← ansD_lo]; omega
  have hhi : (a.extractLsb' 64 64).toNat % 2 ^ 63 = (ansD a).toNat / 2 ^ 64 % 2 ^ 63 := by
    rw [← ansD_hi]
  unfold lowSumS1 lowSwar
  simp only [sumE, E.eval, BinOp.eval, kw, hm2]
  rw [toNat_remuc _ _ (by norm_num) (by norm_num), toNat_andc _ _ (by norm_num [M2c]), BitVec.toNat_add,
    toNat_srl _ 6 (by norm_num), hs1, hlo, hhi]
  rfl
theorem spareBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (lay : Nat) (d : Bool) :
    Br.holds u (spareBr lay d) ↔ d = decide (¬ lowerSpare (ansD a)) := by
  have hb : Br.holds u (spareBr lay d) ↔
      (!((a.extractLsb' 0 64).msb && (a.extractLsb' 64 64).msb)) = d := by
    by_cases h3 : lay = 3
    · simp only [spareBr, if_pos h3, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a6E_eval h, a7E_eval h, kw]
      rw [show (BitVec.ofNat 64 0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_and]
      cases (a.extractLsb' 0 64).msb <;> cases (a.extractLsb' 64 64).msb <;> cases d <;> decide
    · simp only [spareBr, if_neg h3, Br.holds, CmpOp.eval, E.eval, BinOp.eval, a6E_eval h, a7E_eval h, kw]
      rw [show (BitVec.ofNat 64 0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_and]
  have e := spare_iff a
  have hd : decide (¬ lowerSpare (ansD a)) = !((a.extractLsb' 0 64).msb && (a.extractLsb' 64 64).msb) := by
    rw [BitVec.msb_eq_decide, BitVec.msb_eq_decide, decide_not, ← Bool.decide_and, decide_eq_decide.mpr e]
  rw [hb, hd]
  exact eq_comm
def ckOf (lay : Layer) (a : BitVec 256) : Nat := (tgtL lay.val + 2 ^ 64 - lowSumS1 (ansD a)) % 2 ^ 64
theorem ckBr_iff {u : MachineState} {a : BitVec 256} (h : AnsAt u a) (hs : lowerSpare (ansD a)) (lay : Layer)
    (hm1 : (M1E lay.val).eval u = BitVec.ofNat 64 M1c)
    (hm2 : (M2E lay.val).eval u = BitVec.ofNat 64 M2c)
    (d : Bool) :
    Br.holds u (ckBr lay.val d) ↔ d = decide (¬ ckOf lay a < 8) := by
  have hS := lowSumS1_lt (ansD a)
  have hT : tgtL lay.val ≤ 201 := by fin_cases lay <;> decide +kernel
  have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide +kernel
  have ht4 : ((t4E lay.val).eval u).toNat = (lowSumS1 (ansD a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 := by
    simp only [t4E, E.eval, BinOp.eval, kw]
    rw [BitVec.toNat_add, sumE_eval h hs lay.val hm1 hm2, BitVec.toNat_ofNat]
    omega
  have hiff : (lowSumS1 (ansD a) + 2 ^ 64 - (tgtL lay.val - 7)) % 2 ^ 64 < 8 ↔ ckOf lay a < 8 := by
    unfold ckOf; omega
  have key : BitVec.ult (BitVec.ofNat 64 7) ((t4E lay.val).eval u) = decide (¬ ckOf lay a < 8) := by
    simp only [BitVec.ult, ht4, BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 7 by norm_num, decide_eq_decide]
    constructor
    · intro h1 h2
      have := hiff.mpr h2
      omega
    · intro h1
      by_contra h2
      exact h1 (hiff.mp (by omega))
  simp only [ckBr, Br.holds, CmpOp.eval]
  show BitVec.ult ((kw 7).eval u) ((t4E lay.val).eval u) = d ↔ _
  rw [show (kw 7).eval u = BitVec.ofNat 64 7 from rfl, key]; exact eq_comm
def lctxOf (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) : LCtx :=
  ⟨w, lay, 0, 0, (route index lay).2, (route index lay).1, s6v lay.val, a.extractLsb' 0 64, a.extractLsb' 64 64,
    ckOf lay a, ckSlot (ckOf lay a) + partLen (ckOf lay a)⟩
def lfS7 (lay leaf : Nat) : Nat := dispatchHeap lay leaf * 2 ^ s7Sh lay
theorem mod_pow_div_mod (v m k w : Nat) (h : k + w ≤ m) : v % 2 ^ m / 2 ^ k % 2 ^ w = v / 2 ^ k % 2 ^ w := by
  conv_rhs => rw [← Nat.mod_add_div v (2 ^ m)]
  rw [div_mod_add_pow _ _ _ _ _ h]
theorem getD_map_range (f : Nat → Nat) (n i : Nat) (h : i < n) : ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl
theorem lctx_digits (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (hlay : lay ≠ 0)
    (ds : List Nat) (hds : decode lay (ansD a) = some ds) :
    ∀ i < 43, (lctxOf w index lay a).dig i = ds.getD i 0 := by
  rw [decode_lower_v6 lay hlay] at hds
  split at hds
  · split at hds
    · simp only [Option.some.injEq] at hds
      subst hds
      intro i hi
      unfold LCtx.dig lctxOf
      simp only []
      have hlw := lowerWord_eq (ansD a)
      by_cases h21 : i < 21
      · rw [if_pos h21, List.getD_append _ _ _ _ (by simp; omega), getD_map_range _ 42 i (by omega)]
        have e8 : (8 : Nat) ^ i = 2 ^ (3 * i) := by rw [Nat.pow_mul]
        rw [← ansD_lo, e8, hlw]
        have h1 := mod_pow_div_mod (ansD a).toNat 64 (3 * i) 3 (by omega)
        have h2 := mod_pow_div_mod (ansD a).toNat 63 (3 * i) 3 (by omega)
        have h3 := div_mod_add_pow ((ansD a).toNat % 2 ^ 63) ((ansD a).toNat / 2 ^ 64 % 2 ^ 63) (3 * i) 63 3
          (by omega)
        rw [show (2 : Nat) ^ 3 = 8 from rfl] at h1 h2 h3
        rw [h1, h3, h2]
      · by_cases h42 : i < 42
        · rw [if_neg h21, if_pos h42, List.getD_append _ _ _ _ (by simp; omega), getD_map_range _ 42 i (by omega)]
          have e8 : (8 : Nat) ^ (i - 21) = 2 ^ (3 * (i - 21)) := by rw [Nat.pow_mul]
          rw [← ansD_hi, e8, hlw, show 3 * i = 63 + 3 * (i - 21) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
            div_add_pow _ _ _ _ (le_refl _), Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)), Nat.sub_self,
            Nat.pow_zero, Nat.one_mul, Nat.zero_add]
          have h2 := mod_pow_div_mod ((ansD a).toNat / 2 ^ 64) 63 (3 * (i - 21)) 3 (by omega)
          rw [show (2 : Nat) ^ 3 = 8 from rfl] at h2
          exact h2.symm
        · have hi42 : i = 42 := by omega
          subst hi42
          rw [if_neg h21, if_neg h42, List.getD_append_right _ _ _ _ (by simp)]
          rw [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
          show ckOf lay a = _
          unfold ckOf
          rw [tgtL_eq]
    · cases hds
  · cases hds
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Layer route height chainCount counterLimit decode encodingInput target
  dataDigits pad64 lowerSpare lowerWord)
theorem xtrTab_bound : (xtrTab.all fun r => r.all fun x => decide (x < 160000)) = true := by decide +kernel
theorem getD_lt_of_all : ∀ (l : List Nat) (B c : Nat), 0 < B → (l.all fun x => decide (x < B)) = true →
    l.getD c 0 < B
  | [], B, c, hB, _ => by simpa using hB
  | x :: l, B, 0, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | x :: l, B, c + 1, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all l B c hB h.2
theorem getD_getD_lt : ∀ (L : List (List Nat)) (i j B : Nat), 0 < B →
    (L.all fun r => r.all fun x => decide (x < B)) = true → (L.getD i []).getD j 0 < B
  | [], i, j, B, hB, _ => by simpa using hB
  | r :: L, 0, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_lt_of_all r B j hB h.1
  | r :: L, i + 1, j, B, hB, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simpa using getD_getD_lt L i j B hB h.2
theorem trPc_lt (lay c : Nat) : trPc lay c < 160000 :=
  getD_getD_lt xtrTab lay c 160000 (by norm_num) xtrTab_bound
theorem origW_of {w : ClaudeWCT.W9.T3M.WBytes} {s : MachineState} {P : Nat → Prop} (hO : Verify.Orig w P s) (A : Nat)
    (hA : WIT ≤ A) (h8 : (A - WIT) % 8 = 0) (hx : A - WIT < WX) (hP : P (A - WIT)) : OrigW w s A := by
  have := hO.word (A - WIT) h8 hx hP
  rw [show WIT + (A - WIT) = A by omega] at this
  unfold OrigW
  rw [this, wword, show 64 * ((A - WIT) / 8) = 8 * (A - 0x800) by unfold WIT at *; omega]
theorem knownOK_cons (p : Reg × Word) (ps : List (Reg × Word)) (s : MachineState)
    (hp : s.getReg p.1 = p.2) (hps : KnownOK ps s) : KnownOK (p :: ps) s := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact hps q hq
theorem knownOK_at (ps : List (Reg × Word)) (s : MachineState) (i : Nat) (p : Reg × Word)
    (hk : KnownOK ps s) (he : ps[i]? = some p) : s.getReg p.1 = p.2 :=
  hk p (List.mem_of_getElem? he)
theorem ofNat64_add_zero_bridge (v : Word) (n : Nat) (h : v = BitVec.ofNat 64 n) :
    v = BitVec.ofNat 64 (n + 0) := by simpa only [Nat.add_zero] using h
theorem ofNat64_add_zero_bridge385 (v : Word) (n : Nat) (h : v = BitVec.ofNat 64 (n + 385)) :
    v = BitVec.ofNat 64 (n + 0 + 385) := by simpa only [Nat.add_zero] using h
theorem knownOK_fifteen (s : MachineState)
    {p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : Reg × Word}
    (h0 : s.getReg p0.1 = p0.2) (h1 : s.getReg p1.1 = p1.2)
    (h2 : s.getReg p2.1 = p2.2) (h3 : s.getReg p3.1 = p3.2)
    (h4 : s.getReg p4.1 = p4.2) (h5 : s.getReg p5.1 = p5.2)
    (h6 : s.getReg p6.1 = p6.2) (h7 : s.getReg p7.1 = p7.2)
    (h8 : s.getReg p8.1 = p8.2) (h9 : s.getReg p9.1 = p9.2)
    (h10 : s.getReg p10.1 = p10.2) (h11 : s.getReg p11.1 = p11.2)
    (h12 : s.getReg p12.1 = p12.2) (h13 : s.getReg p13.1 = p13.2)
    (h14 : s.getReg p14.1 = p14.2) :
    KnownOK [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] s := by
  iterate 15
    refine knownOK_cons _ _ _ ?_ ?_
    rotate_left
  · intro q hq; cases hq
  all_goals assumption
theorem hyperWord_packed (lay : Layer) (tree leaf : Nat) :
    T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) = BitVec.ofNat 64 (packedPrefix lay tree leaf + 385) := by
  unfold T3.hyperWord packedPrefix packedHi
  have := lay.isLt
  rw [Nat.mod_eq_of_lt (show lay.val < 256 by omega)]
  apply congrArg (BitVec.ofNat 64)
  omega
theorem routed_eq (index : Nat) (lay : Layer) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 = index / 2 ^ below lay.val := by
  rw [route_fst, route_snd, ← hL_eq, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  simpa only [Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div (index / 2 ^ below lay.val) (2 ^ hL lay.val))
theorem hyperWord_route (index : Nat) (lay : Layer) :
    T3.hyperWord lay.val (index / 2 ^ below lay.val) =
      BitVec.ofNat 64 (packedPrefix lay (route index lay).2 (route index lay).1 + 385) := by
  rw [← routed_eq, hyperWord_packed]
theorem hyperWord_x28v (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) :
    T3.hyperWord lay.val (index / 2 ^ below lay.val) = BitVec.ofNat 64 (lctxOf w index lay a).x28v := by
  have e : (lctxOf w index lay a).x28v = packedPrefix lay (route index lay).2 (route index lay).1 + 385 :=
    LCtx.x28v_eq _ rfl
  rw [e]
  exact hyperWord_route index lay
theorem lctxOf_known (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (lay : Layer) (a : BitVec 256) (p : Nat)
    (s : MachineState) (hk : KnownOK (postBl lay.val p) s)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (lctxOf w index lay a).x28v)
    (h16 : s.getReg .x16 = a.extractLsb' 0 64)
    (h17 : s.getReg .x17 = a.extractLsb' 64 64)
    (h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 (ckOf lay a)) :
    KnownOK (lctxOf w index lay a).known s := by
  unfold LCtx.known
  refine knownOK_fifteen s ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact knownOK_at _ s 0 (.x5, 0) hk rfl
  · exact knownOK_at _ s 6 (.x11, 64) hk rfl
  · exact knownOK_at _ s 7 (.x7, 1) hk rfl
  · exact knownOK_at _ s 8 (.x13, 2) hk rfl
  · exact knownOK_at _ s 9 (.x19, 3) hk rfl
  · exact knownOK_at _ s 10 (.x20, 4) hk rfl
  · exact knownOK_at _ s 11 (.x21, 5) hk rfl
  · exact knownOK_at _ s 12 (.x26, 6) hk rfl
  · exact h28
  · exact knownOK_at _ s 3 (.x2, 0x3fe00) hk rfl
  · exact knownOK_at _ s 14 (.x5, 0) hk rfl
  · exact knownOK_at _ s 15 (.x22, BitVec.ofNat 64 (s6v lay.val)) hk rfl
  · exact h16
  · exact h17
  · exact h29
theorem rowA_facts : ∀ lay c, lay < 3 → c < nCopy lay →
    rowA lay c % 16 = 0 ∧ WLO ≤ rowA lay c ∧ rowA lay c + 96 ≤ 2 ^ 23 ∧ WIT + BC.layerEnd lay ≤ rowA lay c := by
  have h : ([0, 1, 2].all fun lay => (List.range (nCopy lay)).all fun c =>
      decide (rowA lay c % 16 = 0 ∧ WLO ≤ rowA lay c ∧ rowA lay c + 96 ≤ 2 ^ 23 ∧
        WIT + BC.layerEnd lay ≤ rowA lay c)) = true := by decide +kernel
  intro lay c hl hc
  have h1 := List.all_eq_true.mp h lay (by simp; omega)
  exact of_decide_eq_true (List.all_eq_true.mp h1 c (List.mem_range.mpr hc))
theorem cpIdx_lt (index : Nat) (lay : Nat) (hl : lay < 4) : BC.cpIdx index lay < nCopy lay := by
  have hn := BC.nCopy_eq
  unfold BC.cpIdx
  interval_cases lay <;> simp only [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2] <;> norm_num [hL] <;> exact Nat.mod_lt _ (by norm_num)
theorem oblB_holds (u : MachineState) (d : Nat) (hd : u.getReg .x12 = BitVec.ofNat 64 d) (h8 : d % 8 = 0)
    (hlt : d + 16 ≤ 2 ^ 23) : ∀ o ∈ BC.oblB, o.holds u := by
  intro o ho
  simp only [BC.oblB, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;>
    simp only [Oblig.holds, Addr.eval, E.eval, hd, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq,
      MEMORY_BYTES, BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl,
      show (0 : Word).toNat = 0 from rfl] <;> omega
theorem encB_step (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index : Nat) (lay : Layer) (hlay : lay ≠ 0) (c : Nat)
    (hc : c < nCopy lay.val) (hidx : index < 2 ^ 31) (t : MachineState) (ht : EncPre w pk index lay.val c t)
    (a : BitVec 256) :
    (decode lay (ansD a) = none → ∃ v k cy, Steps image (writeHash t a) k cy v ∧
        fetch image v = some (.base .ECALL) ∧ v.getReg .x5 = 1 ∧ v.getReg .x10 = 1 ∧ k ≤ 23 ∧ cy ≤ 26) ∧
    (decode lay (ansD a) ≠ none → ∃ s0, Steps image (writeHash t a) (bSt lay.val) (bCy lay.val) s0 ∧
        (lctxOf w index lay a).ok ∧
        (∀ p ∈ (lctxOf w index lay a).known, s0.getReg p.1 = p.2) ∧
        (lctxOf w index lay a).Orig0 s0 ∧
        (lctxOf w index lay a).ChainIn s0 0 [] s0 ∧ Glob (chainK lay.val) w pk s0 ∧
        Verify.Orig w (fun o => 7424 ≤ o ∧ o < layerEnd lay.val) s0 ∧
        s0.getReg .x23 = BitVec.ofNat 64 (lfS7 lay.val (route index lay).1) ∧
        s0.getReg .x31 = BitVec.ofNat 64 (route index lay).2 ∧
        s0.getReg .x9 = BitVec.ofNat 64 TOPB9) := by
  set u := writeHash t a with hu
  have h0 : lay.val ≠ 0 := fun h => hlay (Fin.ext h)
  have hcc := copy_parts lay.val c (BC.copyCheck_at lay.val c lay.isLt hc)
  have hB := hcc.2 h0
  have hkt : KnownOK (BC.bK lay.val c) t := ht.glob.1
  obtain ⟨d, h12, hdc⟩ : ∃ d, t.getReg .x12 = BitVec.ofNat 64 d ∧
      (if lay.val = 3 then d = 2048 else (d = rowA lay.val c ∨ d = rowA lay.val c + 48)) := by
    by_cases h3 : lay.val = 3
    · refine ⟨2048, hkt (.x12, 2048) ?_, by rw [if_pos h3]⟩
      unfold BC.bK; rw [if_pos h3]; simp [bK, h3]
    · obtain ⟨d, hd, hdd⟩ := ht.dst (by have := lay.isLt; omega)
      exact ⟨d, hd, by rw [if_neg h3]; exact hdd⟩
  have hdf : d % 8 = 0 ∧ d + 32 ≤ 2 ^ 23 ∧ safeDest d = true ∧ (lay.val ≠ 3 → WIT + layerEnd lay.val ≤ d) := by
    by_cases h3 : lay.val = 3
    · rw [if_pos h3] at hdc; subst hdc
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun h => absurd h3 h⟩
    · rw [if_neg h3] at hdc
      obtain ⟨r16, rlo, rhi, rend⟩ := rowA_facts lay.val c (by have := lay.isLt; omega) hc
      have hd8 : d % 8 = 0 := by rcases hdc with rfl | rfl <;> omega
      have hd32 : d + 32 ≤ 2 ^ 23 := by rcases hdc with rfl | rfl <;> omega
      have hlo : WLO ≤ d := by rcases hdc with rfl | rfl <;> omega
      refine ⟨hd8, hd32, safeDest_hi d hlo hd8 hd32, fun _ => ?_⟩
      have : layerEnd lay.val = BC.layerEnd lay.val := rfl
      rcases hdc with rfl | rfl <;> omega
  obtain ⟨hd8, hd32, hsafe, hdend⟩ := hdf
  have hku : KnownOK (BC.bK lay.val c) u := fun p hp => by rw [hu, writeHash_getReg]; exact hkt p hp
  have hkuB : KnownOK (BC.bKB lay.val c) u := fun p hp => hku p (List.mem_of_mem_filter hp)
  have hx12u : u.getReg .x12 = BitVec.ofNat 64 d := by rw [hu, writeHash_getReg]; exact h12
  have hobl : ∀ o ∈ BC.oblB, o.holds u := oblB_holds u d hx12u hd8 (by omega)
  have hpcu : u.pc = pcOf (trPc lay.val c + stepsA lay.val + 1) := by
    rw [hu, writeHash_pc, ht.pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat]
    congr 1
  have hans : AnsAt u a := by
    constructor
    · simp only [a6E, E.eval]
      rw [hx12u, hu]
      exact writeHash_at0 t a d h12 (by omega)
    · simp only [a7E, E.eval, BinOp.eval, kw]
      rw [hx12u, hu, ofNat_add_ofNat]
      exact writeHash_at8 t a d h12 (by omega)
  have hm1 : (M1E lay.val).eval u = BitVec.ofNat 64 M1c := by
    by_cases h3 : lay.val = 3
    · simp only [M1E, if_pos h3, E.eval, kw]
      have hd3 : d = 2048 := by rw [if_pos h3] at hdc; exact hdc
      rw [hu, writeHash_frame t a d (TOPLOAD + 8) h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 1 (by decide +kernel)).trans (by decide +kernel)
    · simp only [M1E, if_neg h3, E.eval, kw]
  have hm2 : (M2E lay.val).eval u = BitVec.ofNat 64 M2c := by
    by_cases h3 : lay.val = 3
    · simp only [M2E, if_pos h3, E.eval, kw]
      have hd3 : d = 2048 := by rw [if_pos h3] at hdc; exact hdc
      rw [hu, writeHash_frame t a d TOPLOAD h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 0 (by decide +kernel)).trans (by decide +kernel)
    · simp only [M2E, if_neg h3, E.eval, kw]
  have hmask : (maskE lay.val).eval u = BitVec.ofNat 64 0x3fe00 := by
    by_cases h3 : lay.val = 3
    · simp only [maskE, if_pos h3, E.eval, kw]
      have hd3 : d = 2048 := by rw [if_pos h3] at hdc; exact hdc
      rw [hu, writeHash_frame t a d (TOPLOAD + 24) h12 (by unfold TOPLOAD; omega)
        (by omega) (Or.inr (by unfold TOPLOAD; omega))]
      exact ((ht.hdr3 h3).2.2 3 (by decide +kernel)).trans (by decide +kernel)
    · simp only [maskE, if_neg h3, E.eval, kw]
  have hdec := decode_lower_v6 lay hlay (ansD a)
  have hS := lowSumS1_lt (ansD a)
  constructor
  · intro hnone
    by_cases hs : lowerSpare (ansD a)
    · have hck : ¬ ckOf lay a < 8 := by
        intro hck
        rw [hdec, if_pos hs, if_pos (by rw [← tgtL_eq]; exact hck)] at hnone
        cases hnone
      obtain ⟨v, hv⟩ := spec_run hB.2.1 u hpcu hkuB (by
        intro b hb; simp only [rejCk, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact (ckBr_iff hans hs lay hm1 hm2 true).mpr (by rw [decide_eq_true hck])
        · exact (spareBr_iff hans lay.val false).mpr (by rw [decide_eq_false (not_not_intro hs)])) hobl
      exact ⟨v, if lay.val = 3 then 22 else 20, if lay.val = 3 then 25 else 23, hv.steps, hv.ecall rfl,
        hv.regs (.x5, kw 1) (by simp [rejCk]),
        hv.regs (.x10, kw 1) (by simp [rejCk]), by split_ifs <;> norm_num, by split_ifs <;> norm_num⟩
    · obtain ⟨v, hv⟩ := spec_run hB.2.2 u hpcu hkuB (by
        intro b hb; simp only [rejSpare, List.mem_singleton] at hb; subst hb
        exact (spareBr_iff hans lay.val true).mpr (by rw [decide_eq_true hs])) hobl
      exact ⟨v, 7, 7, hv.steps, hv.ecall rfl, hv.regs (.x5, kw 1) (by simp [rejSpare]),
        hv.regs (.x10, kw 1) (by simp [rejSpare]), by norm_num, by norm_num⟩
  · intro hsome
    have hs : lowerSpare (ansD a) := by
      by_contra hs
      apply hsome; rw [hdec, if_neg hs]
    have hck : ckOf lay a < 8 := by
      by_contra hck
      apply hsome
      rw [hdec, if_pos hs, if_neg (by rw [← tgtL_eq]; exact hck)]
    obtain ⟨h6, h7⟩ := (spare_iff a).mp hs
    obtain ⟨s0, hs0⟩ := spec_run hB.1 u hpcu hkuB (by
      intro b hb; simp only [specBl, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (ckBr_iff hans hs lay hm1 hm2 false).mpr (by rw [decide_eq_false (not_not_intro hck)])
      · exact (spareBr_iff hans lay.val false).mpr (by rw [decide_eq_false (not_not_intro hs)])) hobl
    set L := lctxOf w index lay a with hL
    have hko : KnownOK (postBl lay.val (trPc lay.val c)) s0 := by
      have hk0 := hs0.known
      by_cases h3 : lay.val = 3
      · rw [postBlC, if_pos h3] at hk0
        have e22 : s0.getReg .x22 = BitVec.ofNat 64 (s6v lay.val) := by
          rw [hs0.regs (.x22, .ld (kw (TOPLOAD - 8))) (by simp [specBl, h3]), h3]
          change u.getMem (BitVec.ofNat 64 (TOPLOAD - 8)) = _
          have hd3 : d = 2048 := by rw [if_pos h3] at hdc; exact hdc
          rw [hu, writeHash_frame t a d (TOPLOAD - 8) h12 (by unfold TOPLOAD; omega)
            (by omega) (Or.inr (by unfold TOPLOAD; omega))]
          exact (ht.hdr3 h3).2.1
        have e24 : s0.getReg .x24 = BitVec.ofNat 64 M2c := by
          rw [hs0.regs (.x24, .ld (kw TOPLOAD)) (by simp [specBl, h3])]
          simpa only [M2E, if_pos h3] using hm2
        have e1 : s0.getReg .x1 = BitVec.ofNat 64 M1c := by
          rw [hs0.regs (.x1, .ld (kw (TOPLOAD + 8))) (by simp [specBl, h3])]
          simpa only [M1E, if_pos h3] using hm1
        have e2 : s0.getReg .x2 = BitVec.ofNat 64 0x3fe00 := by
          rw [hs0.regs (.x2, .ld (kw (TOPLOAD + 24))) (by simp [specBl, h3])]
          simpa only [maskE, if_pos h3] using hmask
        intro q hq
        simp only [postBl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with hq | rfl | rfl | rfl
        · by_cases hq24 : q = (.x24, BitVec.ofNat 64 M2c)
          · subst hq24; exact e24
          by_cases hq1 : q = (.x1, BitVec.ofNat 64 M1c)
          · subst hq1; exact e1
          by_cases hq2 : q = (.x2, 0x3fe00)
          · subst hq2; exact e2
          apply hk0 q
          apply List.mem_append_left
          rw [List.mem_filter]
          refine ⟨hq, ?_⟩
          simp only [chainK, baseK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          all_goals first | contradiction | decide
        · exact e22
        · exact hk0 _ (by simp)
        · exact hk0 _ (by simp)
      · rw [postBlC, if_neg h3] at hk0
        exact hk0
    have hkeep := hs0.keep
    have e29 : ((t4E lay.val).eval u) = 7#64 - BitVec.ofNat 64 (ckOf lay a) := by
      have hT : tgtL lay.val ≤ 201 := by fin_cases lay <;> decide +kernel
      have hT7 : 7 ≤ tgtL lay.val := by fin_cases lay <;> decide +kernel
      have hle : lowSumS1 (ansD a) ≤ tgtL lay.val ∧ tgtL lay.val - lowSumS1 (ansD a) < 8 := by
        unfold ckOf at hck; omega
      have hcv : ckOf lay a = tgtL lay.val - lowSumS1 (ansD a) := by unfold ckOf; omega
      rw [hcv]
      apply BitVec.eq_of_toNat_eq
      simp only [t4E, E.eval, BinOp.eval, kw]
      rw [BitVec.toNat_add, sumE_eval hans hs lay.val hm1 hm2, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      omega
    have hLok : L.ok := by
      refine ⟨tree_lt index lay hidx, leaf_lt32 index lay, by simp [hL, lctxOf], ?_, ?_, ?_, ?_, rfl,
        by simp [hL, lctxOf], tree_actual_lt index lay hidx, ?_, ?_, ?_⟩
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; fin_cases lay <;> simp [s6v]
      · simp only [hL, lctxOf]; fin_cases lay <;> decide +kernel
      · simp only [hL, lctxOf]; omega
      · simpa only [hL, lctxOf, hL_eq] using leaf_lt index lay
      · simp only [hL, lctxOf]; exact h6
      · simp only [hL, lctxOf]; exact h7
    have hGu : Glob (BC.bK lay.val c) w pk u := Glob_writeHash ht.glob a d h12 hsafe
    have hGs0 := hs0.glob _ w pk hGu (RelOK.nil u)
    have hOu : Verify.Orig w (fun o => 7424 ≤ o ∧ o < layerEnd lay.val) u := by
      have := Orig_writeHash ht.orig a d h12 (by omega)
      have hL8 : layerEnd lay.val % 8 = 0 := by
        fin_cases lay <;> decide +kernel
      intro j hj hp
      refine this j hj ⟨hp, ?_⟩
      have hp2 := hp.2
      by_cases h3 : lay.val = 3
      · rw [if_pos h3] at hdc
        exact Or.inr (by unfold WIT; omega)
      · have hx := hdend h3
        exact Or.inl (by omega)
    have hOs0 : Verify.Orig w (fun o => 7424 ≤ o ∧ o < layerEnd lay.val) s0 := by
      have := hs0.orig_const hOu
      exact this.mono (fun o ho => ⟨ho, by simp⟩)
    have hpc0 : s0.pc = pcOf (L.startPc 0) := by
      rw [hs0.spc (tgtl lay.val) rfl]
      have hk0 : L.kOf 0 = (a.extractLsb' 0 64).toNat % 512 := by
        rw [L.kOf_eq 0 (by norm_num), if_pos (by norm_num)]
        show (a.extractLsb' 0 64).toNat / 2 ^ (9 * (0 % 7)) % 512 = _
        rw [show 9 * (0 % 7) = 0 from rfl, pow_zero, Nat.div_one]
      have hm : ((a.extractLsb' 0 64) <<< ((BitVec.ofNat 64 9).toNat % 64) &&& BitVec.ofNat 64 0x3fe00) =
          BitVec.ofNat 64 (512 * L.kOf 0) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_andc _ _ (by norm_num), toNat_sll _ 9 (by norm_num), show (0x3fe00 : Nat) = 512 * (2 ^ 9 - 1) by norm_num,
          land_mask _ _ (le_refl _), field_shl _ _ _ (le_refl _) (le_refl _), hk0, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 512 * ((a.extractLsb' 0 64).toNat % 512) < 2 ^ 64 by omega)]
        rw [Nat.sub_self, pow_zero, Nat.div_one]
        rfl
      have hadd : (tgtl lay.val).eval u =
          (BitVec.ofNat 64 (512 * L.kOf 0) + BitVec.ofNat 64 260384) &&& ~~~1#64 := by
        by_cases h3 : lay.val = 3
        · have hm3 : (maskE 3).eval u = BitVec.ofNat 64 0x3fe00 := by rwa [← h3]
          simp only [tgtl, if_pos h3, x14l, E.eval, BinOp.eval, a6E_eval hans, hm3, kw, hm]
          rw [BitVec.add_assoc, show BitVec.ofNat 64 0x3fe00 + BitVec.ofNat 64 (2 ^ 64 - 1248) =
            BitVec.ofNat 64 260384 by decide +kernel]
        · simp only [tgtl, if_neg h3, E.eval, BinOp.eval, a6E_eval hans, kw, hm]
      rw [hadd]
      have e2 : BitVec.ofNat 64 (512 * L.kOf 0) + BitVec.ofNat 64 260384 =
          BitVec.ofNat 64 (0x1000 + 4 * entW 0 (L.kOf 0)) := by
        rw [ofNat_add_ofNat]; congr 1; unfold entW ttabIdx; omega
      rw [e2, even_andNot1' _ (by omega)]
      unfold LCtx.startPc; simp
    have hkL : ∀ q ∈ chainK lay.val, s0.getReg q.1 = q.2 := fun q hq => hko q (by simp [postBl, hq])
    refine ⟨s0, hs0.steps, hLok, ?_, ?_, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl,
      hGs0.2.2.2.2.2, hpc0⟩, ⟨hkL, hGs0.2.1, hGs0.2.2.1, hGs0.2.2.2.1, hGs0.2.2.2.2⟩, hOs0, ?_, ?_, ?_⟩
    · apply lctxOf_known w index lay a (trPc lay.val c) s0 hko
      · rw [hkeep .x28 (by unfold keepB; split_ifs <;> simp), hu, writeHash_getReg, ht.word,
          show BC.below lay.val = below lay.val from rfl, hyperWord_x28v w index lay a]
      · rw [hs0.regs (.x16, a6E) (by simp [specBl]), a6E_eval hans]
      · rw [hs0.regs (.x17, a7E) (by simp [specBl]), a7E_eval hans]
      · rw [hs0.regs (.x29, t4E lay.val) (by simp [specBl]), e29]
    · intro i hi hi' k hk
      have hb := L.blk_props hLok i hi'
      have hS6 : L.S6 = s6v lay.val := rfl
      apply origW_of hOs0 _ (by unfold WIT; omega) (by
          unfold WIT; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v] <;> omega)
        (by unfold WIT WX; simp only [LCtx.blk, hS6]; fin_cases lay <;> simp [s6v] <;> omega)
      simp only [LCtx.blk, hS6]
      unfold WIT
      fin_cases lay <;> simp [s6v, layerEnd] <;> omega
    · rw [hs0.regs (.x23, s23E lay.val) (by simp [specBl])]
      have hs7u : (if lay.val = 3 then (s7E 3).eval u else u.getReg .x23) =
          BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) := by
        by_cases h3 : lay.val = 3
        · obtain rfl : lay = 3 := Fin.ext h3
          rw [if_pos h3]
          have h22u : u.getReg (rReg 3) = BitVec.ofNat 64 (index / 2 ^ below 3) := by
            rw [show rReg 3 = .x22 from rfl, show below 3 = 0 from rfl, pow_zero, Nat.div_one, hu, writeHash_getReg]
            exact ht.index3 rfl
          exact (route_evals index 3 hidx u h22u).2.2.2
        · rw [if_neg h3, hu, writeHash_getReg]
          exact ht.s7 lay rfl (by have := lay.isLt; omega)
      have hs23 : (s23E lay.val).eval u =
          BitVec.ofNat 64 (dispatchHeap lay.val (route index lay).1) <<< ((BitVec.ofNat 64 (s7Sh lay.val)).toNat % 64) := by
        by_cases h3 : lay.val = 3
        · rw [if_pos h3] at hs7u
          rw [s23E, s7Sh, if_pos h3, if_neg (by omega : lay.val ≠ 1)]
          simp only [E.eval, BinOp.eval, hs7u, kw]
        · rw [if_neg h3] at hs7u
          simp only [s23E, if_neg h3, E.eval, BinOp.eval, hs7u, kw]
      rw [hs23]
      have hsh : s7Sh lay.val < 64 := by unfold s7Sh; split_ifs <;> omega
      have hb : s7Bias lay.val ≤ 4096 := by fin_cases lay <;> decide +kernel
      have hl := leaf_lt32 index lay
      have hD : dispatchHeap lay.val (route index lay).1 < 2 ^ 64 := by unfold dispatchHeap; split_ifs <;> omega
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sll _ _ hsh, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD]
      rfl
    · by_cases h3 : lay.val = 3
      · obtain rfl : lay = 3 := Fin.ext h3
        rw [hs0.regs (.x31, treeE 3) (by simp [specBl])]
        have h22u : u.getReg (rReg 3) = BitVec.ofNat 64 (index / 2 ^ below 3) := by
          rw [show rReg 3 = .x22 from rfl, show below 3 = 0 from rfl, pow_zero, Nat.div_one, hu, writeHash_getReg]
          exact ht.index3 rfl
        exact (route_evals index 3 hidx u h22u).2.1
      · rw [hkeep .x31 (by simp [keepB, h3]), hu, writeHash_getReg, (ht.t5 lay rfl).1 h0 (by have := lay.isLt; omega)]
    · exact hko (.x9, BitVec.ofNat 64 TOPB9) (by simp [postBl])
end SigGolfCandidate.T3M
end
