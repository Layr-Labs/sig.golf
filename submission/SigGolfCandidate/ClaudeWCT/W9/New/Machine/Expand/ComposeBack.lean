import SigGolfCandidate.T3M.Search.ProducerData
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ExpSearch
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits
import SigGolfCandidate.Research.V7Composed198Gate
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Region
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Compact2Lv
import SigGolfCandidate.T3M.Expand.Layers

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option autoImplicit false
theorem extractByte_toNat_e (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
theorem word_ext_bytes_e {w₁ w₂ : Word} (h : ∀ j < 8, extractByte w₁ j = extractByte w₂ j) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have e := fun j (hj : j < 8) => congrArg BitVec.toNat (h j hj)
  simp only [extractByte_toNat_e] at e
  have h0 := e 0 (by decide); have h1 := e 1 (by decide); have h2 := e 2 (by decide)
  have h3 := e 3 (by decide); have h4 := e 4 (by decide); have h5 := e 5 (by decide)
  have h6 := e 6 (by decide); have h7 := e 7 (by decide)
  simp only [Nat.reducePow, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  have := w₁.isLt; have := w₂.isLt
  omega
theorem extractByte_or8_e (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)
theorem extractByte_bytesToWordLE_e (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8_e _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl
theorem bytesToWordLE_bytes_e {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply word_ext_bytes_e
  intro i hi
  rw [extractByte_bytesToWordLE_e _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_e]
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < n by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * j) = y
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
theorem bytes_length_e {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV bytesToWordLE_bytes_e bytes_length_e extractByte_bytesToWordLE_e)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests)
set_option linter.unusedSimpArgs false
def w9init (im : Image) (m : Message) (pk : PublicKey) {n : Nat} (σ : Bytes n) : MachineState :=
  (((((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 (dataBase im)) im.data).writeBytesAsWords (BitVec.ofNat 64 0x6620) (bytes m)).writeBytesAsWords
    (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords (BitVec.ofNat 64 0x7000) (bytes σ))).setReg .x2
    (BitVec.ofNat 64 (dataBase im))
set_option maxRecDepth 100000 in
theorem hdrBankBytes_length : hdrBankBytes.length = 4608 := by decide +kernel
set_option maxRecDepth 100000 in
theorem planBytes_length : planBytes.length = 1024 := by decide +kernel
set_option maxRecDepth 100000 in
theorem lplanBytes_length : lplanBytes.length = 1536 := by decide +kernel
theorem data_length {im : Image} (hd : ExpandDataOK im) : im.data.length = 27648 := by
  rw [hd, List.length_append, List.length_append, List.length_append, List.length_append, lplanBytes_length,
    planBytes_length, ESearch.expCostBytes_length, hdrBankBytes_length, Search.expandLegacyData_length]
theorem dataBase_eq {im : Image} (hd : ExpandDataOK im) : dataBase im = Compact2.LPLAN := by
  unfold dataBase
  rw [data_length hd]
  rfl
theorem data_drop_plan {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 1536 = planBytes ++ expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [hd, List.append_assoc, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [lplanBytes_length]),
    List.drop_eq_nil_of_le (by rw [lplanBytes_length]), List.nil_append, List.append_assoc, List.append_assoc]
theorem data_drop_cost {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 2560 = expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 2560 = 1536 + 1024 from rfl, ← List.drop_drop, data_drop_plan hd, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [planBytes_length]),
    List.drop_eq_nil_of_le (by rw [planBytes_length]), List.nil_append, List.append_assoc]
theorem data_drop_bank {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 18944 = hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 18944 = 2560 + 16384 from rfl, ← List.drop_drop, data_drop_cost hd, List.append_assoc,
    List.drop_append_of_le_length (by rw [ESearch.expCostBytes_length]),
    List.drop_eq_nil_of_le (by rw [ESearch.expCostBytes_length]), List.nil_append]
theorem data_drop_legacy {im : Image} (hd : ExpandDataOK im) :
    im.data.drop 23552 = SigGolfCandidate.T3M.Images.expandLegacyData := by
  rw [show 23552 = 18944 + 4608 from rfl, ← List.drop_drop, data_drop_bank hd,
    List.drop_append_of_le_length (by rw [hdrBankBytes_length]),
    List.drop_eq_nil_of_le (by rw [hdrBankBytes_length]), List.nil_append]
section init
variable {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312)
include hd
theorem w9init_getMem (A : Nat) (hA : A < 2 ^ 64) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 5312 ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes σ).drop (A - 0x7000)).take 8)
      else if 0xA0 ≤ A ∧ A < 0xB0 ∧ (A - 0xA0) % 8 = 0 then bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8)
      else if 0x6620 ≤ A ∧ A < 0x6640 ∧ (A - 0x6620) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 0x6620)).take 8)
      else if Compact2.LPLAN ≤ A ∧ A < Compact2.LPLAN + 27648 ∧ (A - Compact2.LPLAN) % 8 = 0 then
        bytesToWordLE ((im.data.drop (A - Compact2.LPLAN)).take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0x6620 A (by rw [bytes_length_e]; decide) hA, dataBase_eq hd,
    getMem_writeBytesAsWords _ _ Compact2.LPLAN A (by rw [data_length hd]; decide) hA, bytes_length_e, bytes_length_e,
    bytes_length_e, data_length hd]
  rfl
theorem w9init_data (A : Nat) (h1 : Compact2.LPLAN ≤ A) (h2 : A < Compact2.LPLAN + 27648)
    (h3 : (A - Compact2.LPLAN) % 8 = 0) :
    (w9init im m pk σ).getMem (BitVec.ofNat 64 A) = bytesToWordLE ((im.data.drop (A - Compact2.LPLAN)).take 8) := by
  unfold Compact2.LPLAN at h1 h2 h3
  rw [w9init_getMem hd _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by unfold Compact2.LPLAN; omega)]
omit hd in
theorem w9init_pc : (w9init im m pk σ).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl
end init
theorem data_plan {im : Image} (hd : ExpandDataOK im) (o : Nat) (ho : o + 8 ≤ 1024) :
    (im.data.drop (1536 + o)).take 8 = (planBytes.drop o).take 8 := by
  rw [← List.drop_drop, data_drop_plan hd, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [planBytes_length]; omega),
    List.take_append_of_le_length (by simp [planBytes_length]; omega)]
theorem data_lplan {im : Image} (hd : ExpandDataOK im) (o : Nat) (ho : o + 8 ≤ 1536) :
    (im.data.drop o).take 8 = (lplanBytes.drop o).take 8 := by
  rw [hd, List.append_assoc, List.append_assoc, List.append_assoc,
    List.drop_append_of_le_length (by rw [lplanBytes_length]; omega),
    List.take_append_of_le_length (by simp [lplanBytes_length]; omega)]
theorem w9init_plan {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    PlanAt (w9init im m pk σ) := by
  intro k hk
  rw [w9init_data hd _ _ _ _ (by unfold PLAN Compact2.LPLAN; omega) (by unfold PLAN Compact2.LPLAN; omega)
      (by unfold PLAN Compact2.LPLAN; omega),
    show PLAN + 8 * k - Compact2.LPLAN = 1536 + 8 * k by unfold PLAN Compact2.LPLAN; omega, data_plan hd _ (by omega)]
theorem w9init_lplan {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    Compact2.LPlanAt (w9init im m pk σ) := by
  intro k hk
  rw [w9init_data hd _ _ _ _ (by unfold Compact2.LPLAN; omega) (by unfold Compact2.LPLAN; omega)
      (by unfold Compact2.LPLAN; omega),
    show Compact2.LPLAN + 8 * k - Compact2.LPLAN = 8 * k by omega, data_lplan hd _ (by omega)]
/-- C4 (adapted from b3cc11b's `w9init_toptab`): the two top-path plan tables of the post-pass (legacy data offsets
2944 / 3456 = data offsets 26496 / 27008). -/
theorem w9init_toptab {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (σ : Bytes 5312) :
    Compact2.TopTabAt (w9init im m pk σ) := by
  have key : ∀ o : Nat, (im.data.drop (23552 + o)).take 8 =
      (SigGolfCandidate.T3M.Images.expandLegacyData.drop o).take 8 := fun o => by
    rw [← List.drop_drop, data_drop_legacy hd]
  have tk : ∀ (L : List (BitVec 8)) (a k : Nat), 8 * k + 8 ≤ 512 →
      (((L.drop a).take 512).drop (8 * k)).take 8 = (L.drop (a + 8 * k)).take 8 := fun L a k hk => by
    rw [List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [w9init_data hd _ _ _ _ (by unfold Compact2.TOPA Compact2.LPLAN; omega)
        (by unfold Compact2.TOPA Compact2.LPLAN; omega) (by unfold Compact2.TOPA Compact2.LPLAN; omega),
      show Compact2.TOPA + 8 * k - Compact2.LPLAN = 23552 + (2944 + 8 * k) by unfold Compact2.TOPA Compact2.LPLAN; omega,
      key]
    unfold Compact2.topABytes
    rw [tk _ _ _ (by omega)]
  · rw [w9init_data hd _ _ _ _ (by unfold Compact2.TOPB Compact2.LPLAN; omega)
        (by unfold Compact2.TOPB Compact2.LPLAN; omega) (by unfold Compact2.TOPB Compact2.LPLAN; omega),
      show Compact2.TOPB + 8 * k - Compact2.LPLAN = 23552 + (3456 + 8 * k) by unfold Compact2.TOPB Compact2.LPLAN; omega,
      key]
    unfold Compact2.topBBytes
    rw [tk _ _ _ (by omega)]
-- [h2 lane] removed front_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
-- [h2 lane] removed front_pre30: a fact about the record's original expand word 0 / 342, which H2 replaces
sym_block zblk := symRun { noAlias := true } zeroBlk (pcOf 42719) 20
theorem zero_spec {im : Image} (hZ : CodeAt im (pcOf 42719) zeroBlk) (s : MachineState) (hpc : s.pc = pcOf 42719) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 30 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      (∀ A, A < 2 ^ 64 → (A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8) → t.getMem (BitVec.ofNat 64 A) = 0) ∧
      RegsExcept s t [.x19, .x29] ∧
      Frame s t (fun A => A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8) := by
  refine ⟨_, symRun_sound zblk hZ s hpc (by simp [zblk.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, zblk.res, E.eval]
  · simp [zblk.res, rv_simp]
  · intro A hA h
    simp only [Result.toState_getMem, zblk.res]
    t3n []
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · ex_regs zblk.res
  · intro A hA hn
    simp only [Result.toState_getMem, zblk.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
-- [h2 lane] removed front_pre30 (record word 0); H2Front.front_pre30' is the H2 version
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput Layer LayerSignature height chainCount)
open SigGolfCandidate.T3M.Expand (lWC lWM RlWit sideOff height_le)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
theorem readWords_blocks (t : MachineState) : ∀ (bs : List (List Word)) (A : Nat),
    (∀ b ∈ bs, b.length = 8) → (∀ k < bs.length, t.readWords (BitVec.ofNat 64 (A + 64 * k)) 8 = bs.getD k []) →
    t.readWords (BitVec.ofNat 64 A) (8 * bs.length) = bs.flatten
  | [], _, _, _ => rfl
  | b :: bs, A, hl, h => by
    rw [List.length_cons, show 8 * (bs.length + 1) = 8 + 8 * bs.length by ring, readWords_add,
      show A + 8 * 8 = A + 64 by ring, List.flatten_cons]
    congr 1
    · simpa using h 0 (by simp)
    · refine readWords_blocks t bs (A + 64) (fun x hx => hl x (by simp [hx])) (fun k hk => ?_)
      have := h (k + 1) (by simp; omega)
      rw [show A + 64 * (k + 1) = A + 64 + 64 * k by ring] at this
      simpa using this
theorem wordsOf_flatMap64 {α : Type} (f : α → List UInt8) (hf : ∀ x, (f x).length = 64) :
    ∀ (xs : List α), wordsOf (xs.flatMap f) = xs.flatMap (fun x => wordsOf (f x))
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by rw [hf]), wordsOf_flatMap64 f hf xs]
theorem wordsOf_dig_zeros48 (d : Digest) :
    wordsOf (bytesLE 16 d ++ SigGolfCandidate.T3M.zeros 48) =
      [d.extractLsb' 0 64, d.extractLsb' 64 64, 0, 0, 0, 0, 0, 0] := by
  rw [wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16,
    show SigGolfCandidate.T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, wordsOf_replicate_zero]
  rfl
theorem wordsOf_zeros48_dig (d : Digest) :
    wordsOf (SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 d) =
      [0, 0, 0, 0, 0, 0, d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by rfl), wordsOf_bytesLE16,
    show SigGolfCandidate.T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, wordsOf_replicate_zero]
  rfl
def lBase (lay : Layer) : Nat := ![0x2c48, 0x3CC8, 0x4948, 0x5588] lay
/-- Campaign R6: the top staging region keeps main's 66 blocks; chain 0's block is the highest
(`lWC = lBase + 64 * (vBlocks - 1)`), and the two blocks above the path (main's chains 52/53) are dead. -/
theorem lBase_eq (lay : Layer) : lWM lay = lBase lay + 64 * (height lay - 1) ∧
    lWC lay = lBase lay + 64 * height lay + 64 * vGap lay + 64 * (chainCount lay - 1) := by
  fin_cases lay <;> decide

def mkWords (leaf j : Nat) (p : Digest) : List Word :=
  if leaf / 2 ^ j % 2 = 1 then [p.extractLsb' 0 64, p.extractLsb' 64 64, 0, 0, 0, 0, 0, 0]
  else [0, 0, 0, 0, 0, 0, p.extractLsb' 0 64, p.extractLsb' 64 64]
def chWords (v : Digest) : List Word := [0, 0, 0, 0, 0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64]
def layBlocks (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List (List Word) :=
  (List.finRange (height lay)).reverse.map (fun j => mkWords leaf j.val (ls.path j)) ++
    (List.finRange (chainCount lay)).reverse.map (fun i => chWords (ls.values i))
theorem length_flatMap_const {α : Type} (f : α → List UInt8) (c : Nat) (hf : ∀ x, (f x).length = c) :
    ∀ (xs : List α), (xs.flatMap f).length = c * xs.length
  | [] => by simp
  | x :: xs => by rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f c hf xs]; simp; ring
theorem flatMap_eq_flatten {α β : Type} (f : α → List β) (g : α → List β) (h : ∀ x, f x = g x) :
    ∀ (xs : List α), xs.flatMap f = (xs.map g).flatten
  | [] => rfl
  | x :: xs => by rw [List.flatMap_cons, List.map_cons, List.flatten_cons, h, flatMap_eq_flatten f g h xs]
theorem layerBytes_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    wordsOf (SigGolfCandidate.T3M.layerBytes lay leaf ls) = (layBlocks lay leaf ls).flatten := by
  unfold SigGolfCandidate.T3M.layerBytes layBlocks
  have hm : ∀ j : Fin (height lay), ((if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++
      SigGolfCandidate.T3M.zeros 48 else SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 (ls.path j))).length = 64 := by
    intro j; split_ifs <;> simp [bytesLE_length, SigGolfCandidate.T3M.zeros]
  have hc : ∀ i : Fin (chainCount lay), (SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 (ls.values i)).length = 64 := by
    intro i; simp [bytesLE_length, SigGolfCandidate.T3M.zeros]
  rw [wordsOf_append _ _ (by rw [length_flatMap_const _ 64 hm]; omega),
    wordsOf_flatMap64 _ hm, wordsOf_flatMap64 _ hc, List.flatten_append]
  rw [flatMap_eq_flatten _ (fun j => mkWords leaf j.val (ls.path j)) (fun j => by
      unfold mkWords
      split_ifs
      · exact wordsOf_dig_zeros48 _
      · exact wordsOf_zeros48_dig _),
    flatMap_eq_flatten _ (fun i => chWords (ls.values i)) (fun i => wordsOf_zeros48_dig _)]
/-- Campaign R6: the staging blocks with the dead (zero) blocks between the path and the chain blocks. -/
def layBlocksV (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List (List Word) :=
  (List.finRange (height lay)).reverse.map (fun j => mkWords leaf j.val (ls.path j)) ++
    List.replicate (vGap lay) (List.replicate 8 0) ++
    (List.finRange (chainCount lay)).reverse.map (fun i => chWords (ls.values i))
theorem flatten_replicate8 : ∀ g : Nat, (List.replicate g (List.replicate 8 (0 : Word))).flatten = List.replicate (8 * g) 0
  | 0 => rfl
  | g + 1 => by
    rw [List.replicate_succ, List.flatten_cons, flatten_replicate8 g,
      show 8 * (g + 1) = 8 + 8 * g by ring, List.replicate_add]
theorem gapBytes_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    wordsOf (gapV6 lay (SigGolfCandidate.T3M.layerBytes lay leaf ls)) = (layBlocksV lay leaf ls).flatten := by
  have hm : ∀ j : Fin (height lay), ((if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++
      SigGolfCandidate.T3M.zeros 48 else SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 (ls.path j))).length = 64 := by
    intro j; split_ifs <;> simp [bytesLE_length, SigGolfCandidate.T3M.zeros]
  have hc : ∀ i : Fin (chainCount lay), (SigGolfCandidate.T3M.zeros 48 ++ bytesLE 16 (ls.values i)).length = 64 := by
    intro i; simp [bytesLE_length, SigGolfCandidate.T3M.zeros]
  have hP := length_flatMap_const _ 64 hm (List.finRange (height lay)).reverse
  simp only [List.length_reverse, List.length_finRange] at hP
  have hZ : (SigGolfCandidate.T3M.zeros (64 * vGap lay)).length = 64 * vGap lay := by
    simp [SigGolfCandidate.T3M.zeros]
  unfold gapV6 SigGolfCandidate.T3M.layerBytes layBlocksV
  rw [List.take_left' hP, List.drop_left' hP,
    wordsOf_append _ _ (by simp only [List.length_append, hP, hZ]; omega),
    wordsOf_append _ _ (by simp only [List.length_append, hP, hZ]; omega),
    wordsOf_flatMap64 _ hm, wordsOf_flatMap64 _ hc,
    show SigGolfCandidate.T3M.zeros (64 * vGap lay) = List.replicate (8 * (8 * vGap lay)) 0 by
      simp [SigGolfCandidate.T3M.zeros]; ring_nf,
    wordsOf_replicate_zero, List.flatten_append, List.flatten_append, flatten_replicate8]
  rw [flatMap_eq_flatten _ (fun j => mkWords leaf j.val (ls.path j)) (fun j => by
      unfold mkWords
      split_ifs
      · exact wordsOf_dig_zeros48 _
      · exact wordsOf_zeros48_dig _),
    flatMap_eq_flatten _ (fun i => chWords (ls.values i)) (fun i => wordsOf_zeros48_dig _)]
theorem mk_block (t : MachineState) (B leaf j : Nat) (p : Digest) (hp : DigAt t (B + sideOff leaf j) p)
    (hz : ∀ r < 8, 8 * r ≠ sideOff leaf j → 8 * r ≠ sideOff leaf j + 8 →
      t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = mkWords leaf j p := by
  rw [readWords_eight]
  unfold mkWords
  unfold sideOff at hp hz
  split_ifs at hp hz ⊢ with hb
  · simp only [Nat.add_zero] at hp
    rw [hp.1, hp.2, show B + 16 = B + 8 * 2 by ring, hz 2 (by omega) (by omega) (by omega),
      show B + 24 = B + 8 * 3 by ring, hz 3 (by omega) (by omega) (by omega),
      show B + 32 = B + 8 * 4 by ring, hz 4 (by omega) (by omega) (by omega),
      show B + 40 = B + 8 * 5 by ring, hz 5 (by omega) (by omega) (by omega),
      show B + 48 = B + 8 * 6 by ring, hz 6 (by omega) (by omega) (by omega),
      show B + 56 = B + 8 * 7 by ring, hz 7 (by omega) (by omega) (by omega)]
  · have h0 := hz 0 (by omega) (by omega) (by omega)
    have h1 := hz 1 (by omega) (by omega) (by omega)
    have h2 := hz 2 (by omega) (by omega) (by omega)
    have h3 := hz 3 (by omega) (by omega) (by omega)
    have h4 := hz 4 (by omega) (by omega) (by omega)
    have h5 := hz 5 (by omega) (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
      show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5, hp.1,
      show B + 56 = B + 48 + 8 by ring, hp.2]
theorem ch_block (t : MachineState) (B : Nat) (v : Digest) (hv : DigAt t (B + 48) v)
    (hz : ∀ r < 6, t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = chWords v := by
  rw [readWords_eight]
  have h0 := hz 0 (by omega); have h1 := hz 1 (by omega); have h2 := hz 2 (by omega)
  have h3 := hz 3 (by omega); have h4 := hz 4 (by omega); have h5 := hz 5 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
    show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5, hv.1,
    show B + 56 = B + 48 + 8 by ring, hv.2]
  rfl
theorem getD_rev_finRange_map {β : Type} (n : Nat) (f : Fin n → β) (d : β) (k : Nat) (hk : k < n) :
    ((List.finRange n).reverse.map f).getD k d = f ⟨n - 1 - k, by omega⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by simp; omega)]
  simp [show n - 1 - k < n by omega]
theorem zero_block (t : MachineState) (B : Nat) (hz : ∀ r < 8, t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = List.replicate 8 0 := by
  rw [readWords_eight]
  have h0 := hz 0 (by omega); have h1 := hz 1 (by omega); have h2 := hz 2 (by omega)
  have h3 := hz 3 (by omega); have h4 := hz 4 (by omega); have h5 := hz 5 (by omega)
  have h6 := hz 6 (by omega); have h7 := hz 7 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
    show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5,
    show B + 48 = B + 8 * 6 by ring, h6, show B + 56 = B + 8 * 7 by ring, h7]
  rfl
theorem vGap_le (lay : Layer) : vGap lay ≤ 2 := by fin_cases lay <;> decide
/-- Campaign R6: the staging region of layer `lay` (`vBlocks lay` blocks, the top with its two dead blocks). -/
theorem layer_words (t : MachineState) (lay : Layer) (leaf : Nat) (ls : LayerSignature lay)
    (hv : ∀ i (h : i < chainCount lay), DigAt t (lWC lay - 64 * i + 48) (ls.values ⟨i, h⟩))
    (hp : ∀ j (h : j < height lay), DigAt t (lWM lay - 64 * j + sideOff leaf j) (ls.path ⟨j, h⟩))
    (hz : ∀ A, lBase lay ≤ A → A < lBase lay + 64 * vBlocks lay →
      ¬ RlWit lay leaf (lWC lay) (lWM lay) A → t.getMem (BitVec.ofNat 64 A) = 0) :
    t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * vBlocks lay) =
      wordsOf (gapV6 lay (SigGolfCandidate.T3M.layerBytes lay leaf ls)) := by
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  have hH := height_le lay
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  have hG := vGap_le lay
  have hVB : vBlocks lay = height lay + vGap lay + chainCount lay := rfl
  have hso : ∀ j, sideOff leaf j = 0 ∨ sideOff leaf j = 48 := fun j => by unfold sideOff; split_ifs <;> simp
  rw [gapBytes_words]
  have hlen : (layBlocksV lay leaf ls).length = vBlocks lay := by
    simp only [layBlocksV, vBlocks, List.length_append, List.length_map, List.length_reverse, List.length_finRange,
      List.length_replicate]
  have hl8 : ∀ b ∈ layBlocksV lay leaf ls, b.length = 8 := by
    intro b hb
    simp only [layBlocksV, List.mem_append, List.mem_map, List.mem_replicate] at hb
    rcases hb with (⟨j, _, rfl⟩ | ⟨_, rfl⟩) | ⟨i, _, rfl⟩
    · unfold mkWords; split_ifs <;> rfl
    · rfl
    · rfl
  have key := readWords_blocks t (layBlocksV lay leaf ls) (lBase lay) hl8 (fun k hk => by
    rw [hlen] at hk
    by_cases hkH : k < height lay
    · rw [layBlocksV, List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
        getD_rev_finRange_map _ _ _ _ hkH]
      obtain ⟨j, hj⟩ : ∃ j, j = height lay - 1 - k := ⟨_, rfl⟩
      have hB : lBase lay + 64 * k = lWM lay - 64 * j := by omega
      have e : (⟨height lay - 1 - k, by omega⟩ : Fin (height lay)) = ⟨j, by omega⟩ := Fin.ext hj.symm
      rw [hB, e]
      refine mk_block t _ leaf j _ (hp j (by omega)) (fun r hr h1 h2 => hz _ (by omega) (by omega) ?_)
      rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
      · omega
      · omega
      · rcases eq_or_ne j' j with rfl | hne
        · omega
        · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases eq_or_ne j' j with rfl | hne
        · omega
        · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
    by_cases hkG : k < height lay + vGap lay
    · rw [layBlocksV, List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_map, List.length_reverse, List.length_finRange]
      have hr : (List.replicate (vGap lay) (List.replicate 8 (0 : Word))).getD (k - height lay) [] =
          List.replicate 8 0 := by
        rw [List.getD_eq_getElem?_getD]; simp [show k - height lay < vGap lay by omega]
      rw [hr]
      refine zero_block t _ (fun r hr => hz _ (by omega) (by omega) ?_)
      rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
      · omega
      · omega
      · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
    · rw [layBlocksV, List.getD_append_right _ _ _ _ (by simp; omega), List.length_append, List.length_map,
        List.length_reverse, List.length_finRange, List.length_replicate,
        getD_rev_finRange_map _ _ _ _ (by omega)]
      obtain ⟨i, hi⟩ : ∃ i, i = chainCount lay - 1 - (k - (height lay + vGap lay)) := ⟨_, rfl⟩
      have hB : lBase lay + 64 * k = lWC lay - 64 * i := by omega
      have e : (⟨chainCount lay - 1 - (k - (height lay + vGap lay)), by omega⟩ : Fin (chainCount lay)) =
          ⟨i, by omega⟩ := Fin.ext hi.symm
      rw [hB, e]
      refine ch_block t _ _ (hv i (by omega)) (fun r hr => hz _ (by omega) (by omega) ?_)
      rintro (⟨i', hi', h | h⟩ | ⟨j', hj', h | h⟩)
      · omega
      · omega
      · rcases hso j' with h4 | h4 <;> omega
      · rcases hso j' with h4 | h4 <;> omega)
  rw [hlen] at key
  exact key
theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
theorem ctr_words (c : BitVec 32) (m : Nat) :
    wordsOf (bytesLE 4 c ++ SigGolfCandidate.T3M.zeros (4 + 8 * m)) = BitVec.ofNat 64 c.toNat :: List.replicate m 0 := by
  have hc : SigGolfCandidate.T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [SigGolfCandidate.T3M.readLE_append, SigGolfCandidate.T3M.readLE_bytesLE,
      SigGolfCandidate.T3M.readLE_replicate_zero]
    simp
  rw [show SigGolfCandidate.T3M.zeros (4 + 8 * m) = List.replicate 4 0 ++ List.replicate (8 * m) 0 by
      simp [SigGolfCandidate.T3M.zeros, List.replicate_add],
    ← List.append_assoc, wordsOf_append8 _ _ (by simp [bytesLE_length]), hc, wordsOf_replicate_zero]
theorem headerW_words (w : WCT9.Witness) :
    wordsOf (headerBytesV5 w) =
      [w.signature.rho.extractLsb' 0 64, w.signature.rho.extractLsb' 64 64, BitVec.ofNat 64 w.digestCounter.toNat,
        0, BitVec.ofNat 64 (w.counters 3).toNat, 0, 0, 0] := by
  unfold headerBytesV5
  simp only [List.append_assoc]
  rw [show SigGolfCandidate.T3M.zeros 12 = SigGolfCandidate.T3M.zeros (4 + 8 * 1) from rfl,
    show SigGolfCandidate.T3M.zeros 28 = SigGolfCandidate.T3M.zeros (4 + 8 * 3) from rfl]
  rw [wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, ← List.append_assoc (bytesLE 4 _),
    wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3M.zeros]), ctr_words, ctr_words]
  rfl
def bcWords (leaf j : Nat) (p : Digest) (c : BitVec 32) : List Word :=
  if leaf / 2 ^ j % 2 = 1 then [p.extractLsb' 0 64, p.extractLsb' 64 64, 0, 0, BitVec.ofNat 64 c.toNat, 0, 0, 0]
  else [0, 0, 0, 0, BitVec.ofNat 64 c.toNat, 0, p.extractLsb' 0 64, p.extractLsb' 64 64]
theorem bcTop_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (c : BitVec 32) :
    wordsOf (bcTopBlockV6 lay leaf ls c) = bcWords leaf (height lay - 1) (ls.path (WCT9.topLevel lay)) c := by
  unfold bcTopBlockV6 bcWords
  split_ifs with hb
  · simp only [List.append_assoc]
    rw [show SigGolfCandidate.T3M.zeros 28 = SigGolfCandidate.T3M.zeros (4 + 8 * 3) from rfl]
    rw [wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16,
      wordsOf_append _ _ (by simp [SigGolfCandidate.T3M.zeros]),
      show SigGolfCandidate.T3M.zeros 16 = List.replicate (8 * 2) 0 from rfl, wordsOf_replicate_zero, ctr_words]
    rfl
  · simp only [List.append_assoc]
    rw [show SigGolfCandidate.T3M.zeros 12 = SigGolfCandidate.T3M.zeros (4 + 8 * 1) from rfl]
    rw [wordsOf_append _ _ (by simp [SigGolfCandidate.T3M.zeros]),
      show SigGolfCandidate.T3M.zeros 32 = List.replicate (8 * 4) 0 from rfl, wordsOf_replicate_zero,
      ← List.append_assoc (bytesLE 4 _), wordsOf_append _ _ (by simp [bytesLE_length, SigGolfCandidate.T3M.zeros]), ctr_words,
      wordsOf_bytesLE16]
    rfl
theorem wordsOf_drop64 (l : List UInt8) (h : 64 ≤ l.length) :
    wordsOf (l.drop 64) = (wordsOf l).drop 8 := by
  conv_rhs => rw [← List.take_append_drop 64 l]
  rw [wordsOf_append _ _ (by simp; omega), List.drop_left' (length_wordsOf 8 _ (by simp; omega))]
theorem layerBytesBC_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (c : BitVec 32) :
    wordsOf (layerBytesBCV6 lay leaf ls c) =
      bcWords leaf (height lay - 1) (ls.path (WCT9.topLevel lay)) c ++ (layBlocks lay leaf ls).flatten.drop 8 := by
  unfold layerBytesBCV6
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  rw [wordsOf_append _ _ (by rw [bcTopBlockV6_length]), bcTop_words,
    wordsOf_drop64 _ (by rw [SigGolfCandidate.T3M.layerBytes_length]; omega), layerBytes_words]
theorem layerBC_words (t : MachineState) (lay : Layer) (h0 : lay.val ≠ 0) (leaf : Nat) (ls : LayerSignature lay)
    (c : BitVec 32) (hv : ∀ i (h : i < chainCount lay), DigAt t (lWC lay - 64 * i + 48) (ls.values ⟨i, h⟩))
    (hp : ∀ j (h : j < height lay), DigAt t (lWM lay - 64 * j + sideOff leaf j) (ls.path ⟨j, h⟩))
    (hc : t.getMem (BitVec.ofNat 64 (lBase lay + 32)) = BitVec.ofNat 64 c.toNat)
    (hz : ∀ A, lBase lay ≤ A → A < lBase lay + 64 * (height lay + chainCount lay) →
      ¬ RlWit lay leaf (lWC lay) (lWM lay) A → A ≠ lBase lay + 32 → t.getMem (BitVec.ofNat 64 A) = 0) :
    t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
      wordsOf (layerBytesBCV6 lay leaf ls c) := by
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  have hg0 := vGap_low lay h0
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  have hlB : lBase lay + 64 * (height lay + chainCount lay) < 2 ^ 64 := by fin_cases lay <;> decide
  have hso : ∀ j, sideOff leaf j = 0 ∨ sideOff leaf j = 48 := fun j => by unfold sideOff; split_ifs <;> simp
  have hRne : ∀ A, RlWit lay leaf (lWC lay) (lWM lay) A → A ≠ lBase lay + 32 := by
    rintro A (⟨i, hi, h | h⟩ | ⟨j, hj, h | h⟩) he
    · omega
    · omega
    · rcases eq_or_ne j (height lay - 1) with rfl | hne
      · rcases hso (height lay - 1) with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases hso j with h4 | h4 <;> rw [h4] at h <;> omega
    · rcases eq_or_ne j (height lay - 1) with rfl | hne
      · rcases hso (height lay - 1) with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases hso j with h4 | h4 <;> rw [h4] at h <;> omega
  set t' := t.setMem (BitVec.ofNat 64 (lBase lay + 32)) 0 with ht'
  have g' : ∀ A, A < 2 ^ 64 → A ≠ lBase lay + 32 → t'.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA hne
    have hne' : BitVec.ofNat 64 A ≠ BitVec.ofNat 64 (lBase lay + 32) := by
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (show lBase lay + 32 < 2 ^ 64 by omega)]
        at this
      exact hne this
    simp only [ht', MachineState.setMem, MachineState.getMem, beq_iff_eq, hne', if_false]
  have g0 : t'.getMem (BitVec.ofNat 64 (lBase lay + 32)) = 0 := by
    simp only [ht', MachineState.setMem, MachineState.getMem, beq_self_eq_true, if_true]
  have dig' : ∀ A d, A + 16 ≤ 2 ^ 64 → A ≠ lBase lay + 32 → A + 8 ≠ lBase lay + 32 → DigAt t A d → DigAt t' A d :=
    fun A d h1 h2 h3 hd => ⟨(g' A (by omega) h2).trans hd.1, (g' (A + 8) (by omega) h3).trans hd.2⟩
  have hW' := layer_words t' lay leaf ls
    (fun i h => dig' _ _ (by omega) (hRne _ (Or.inl ⟨i, h, Or.inl rfl⟩)) (hRne _ (Or.inl ⟨i, h, Or.inr rfl⟩))
      (hv i h))
    (fun j h => dig' _ _ (by rcases hso j with h4 | h4 <;> omega) (hRne _ (Or.inr ⟨j, h, Or.inl rfl⟩))
      (hRne _ (Or.inr ⟨j, h, Or.inr rfl⟩)) (hp j h))
    (fun A h1 h2 hn => by
      rw [vBlocks_low lay h0] at h2
      by_cases he : A = lBase lay + 32
      · rw [he, g0]
      · rw [g' A (by omega) he]; exact hz A h1 h2 hn he)
  rw [vBlocks_low lay h0, gapV6_low lay h0, layerBytes_words] at hW'
  rw [layerBytesBC_words]
  have eM : 8 * (height lay + chainCount lay) = 8 + (8 * (height lay + chainCount lay) - 8) := by omega
  rw [eM, readWords_add] at hW' ⊢
  have hlow : t.readWords (BitVec.ofNat 64 (lBase lay + 8 * 8)) (8 * (height lay + chainCount lay) - 8) =
      t'.readWords (BitVec.ofNat 64 (lBase lay + 8 * 8)) (8 * (height lay + chainCount lay) - 8) := by
    have F : Frame t' t (fun A => A = lBase lay + 32) := fun A hA hn => (g' A hA hn).symm
    exact frame_readWords F _ _ (by omega) (fun i _ h => by omega)
  have hl8 : (t'.readWords (BitVec.ofNat 64 (lBase lay)) 8).length = 8 := SigGolfCandidate.Rv.readWords_length _ _ _
  rw [hlow, ← hW', List.drop_left' hl8]
  congr 1
  have hp1 := hp (height lay - 1) (by omega)
  rw [show lWM lay - 64 * (height lay - 1) = lBase lay by omega] at hp1
  have hzt : ∀ r < 8, 8 * r ≠ sideOff leaf (height lay - 1) → 8 * r ≠ sideOff leaf (height lay - 1) + 8 → r ≠ 4 →
      t.getMem (BitVec.ofNat 64 (lBase lay + 8 * r)) = 0 := by
    intro r hr h1 h2 h4
    refine hz _ (by omega) (by omega) ?_ (by omega)
    rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
    · omega
    · omega
    · rcases eq_or_ne j' (height lay - 1) with rfl | hne
      · omega
      · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
    · rcases eq_or_ne j' (height lay - 1) with rfl | hne
      · omega
      · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
  rw [readWords_eight]
  unfold bcWords
  unfold sideOff at hp1 hzt
  have htl : ls.path (WCT9.topLevel lay) = ls.path ⟨height lay - 1, by omega⟩ := rfl
  rw [htl]
  split_ifs at hp1 hzt ⊢ with hb
  · simp only [Nat.add_zero] at hp1
    rw [hp1.1, hp1.2, show lBase lay + 16 = lBase lay + 8 * 2 by ring, hzt 2 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 24 = lBase lay + 8 * 3 by ring, hzt 3 (by omega) (by omega) (by omega) (by omega), hc,
      show lBase lay + 40 = lBase lay + 8 * 5 by ring, hzt 5 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 48 = lBase lay + 8 * 6 by ring, hzt 6 (by omega) (by omega) (by omega) (by omega),
      show lBase lay + 56 = lBase lay + 8 * 7 by ring, hzt 7 (by omega) (by omega) (by omega) (by omega)]
  · have h0 := hzt 0 (by omega) (by omega) (by omega) (by omega)
    have h1 := hzt 1 (by omega) (by omega) (by omega) (by omega)
    have h2 := hzt 2 (by omega) (by omega) (by omega) (by omega)
    have h3 := hzt 3 (by omega) (by omega) (by omega) (by omega)
    have h5 := hzt 5 (by omega) (by omega) (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    rw [h0, h1, show lBase lay + 16 = lBase lay + 8 * 2 by ring, h2, show lBase lay + 24 = lBase lay + 8 * 3 by ring,
      h3, hc, show lBase lay + 40 = lBase lay + 8 * 5 by ring, h5, hp1.1,
      show lBase lay + 56 = lBase lay + 48 + 8 by ring, hp1.2]
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Layer height chainCount route)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK)
open SigGolfCandidate.T3M.Expand (IDXV)
open SigGolfCandidate.T3M (window window_flatMap_const zeros)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
theorem readWords_ext (t : MachineState) : ∀ (L : List Word) (A : Nat),
    (∀ i, i < L.length → t.getMem (BitVec.ofNat 64 (A + 8 * i)) = L.getD i 0) →
    t.readWords (BitVec.ofNat 64 A) L.length = L
  | [], _, _ => rfl
  | w :: L, A, h => by
    rw [List.length_cons, show L.length + 1 = 1 + L.length by ring, readWords_add, readWords_one]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0, readWords_ext t L (A + 8 * 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show A + 8 * (i + 1) = A + 8 * 1 + 8 * i by ring] at this
      simpa using this)]
    rfl
-- [h2 lane] removed expandN_split: with H2, `expandN` is the searching expander; H2Search.expandN_splitS replaces it
end ClaudeWCT.W9.Machine.Expand
end
