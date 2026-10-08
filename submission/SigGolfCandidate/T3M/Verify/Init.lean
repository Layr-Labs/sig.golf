import SigGolfCandidate.T3M.Verify.Common
import SigGolfCandidate.T3M.Submission

set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
def leNat8 : List (BitVec 8) → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * leNat8 l
theorem shl_or (X y k : Nat) (hX : X < 2 ^ k) : X ||| y * 2 ^ k = X + 2 ^ k * y := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hX]; ring
theorem zext_shl_toNat (b : BitVec 8) (k : Nat) (hk : k ≤ 56) :
    ((b.zeroExtend 64 : Word) <<< (BitVec.ofNat 64 k)).toNat = b.toNat * 2 ^ k := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega)]
  apply Nat.mod_eq_of_lt
  calc b.toNat * 2 ^ k < 2 ^ 8 * 2 ^ k := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
    _ = 2 ^ (8 + k) := by rw [Nat.pow_add]
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide +kernel) (by omega)
theorem leNat8_lt : ∀ l : List (BitVec 8), leNat8 l < 256 ^ l.length
  | [] => by simp [leNat8]
  | b :: l => by
    have := leNat8_lt l
    have hb := b.isLt
    simp only [leNat8, List.length_cons, pow_succ]
    have : b.toNat < 256 := by simpa using hb
    nlinarith
theorem bytesToWordLE8_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]).toNat =
      leNat8 [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [bytesToWordLE, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    BitVec.toNat_or, leNat8]
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, show (16 : Word) = BitVec.ofNat 64 16 from rfl,
    show (24 : Word) = BitVec.ofNat 64 24 from rfl, show (32 : Word) = BitVec.ofNat 64 32 from rfl,
    show (40 : Word) = BitVec.ofNat 64 40 from rfl, show (48 : Word) = BitVec.ofNat 64 48 from rfl,
    show (56 : Word) = BitVec.ofNat 64 56 from rfl]
  rw [zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel),
    zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel), zext_shl_toNat _ _ (by decide +kernel),
    zext_shl_toNat _ _ (by decide +kernel)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := b4.isLt; have := b5.isLt; have := b6.isLt; have := b7.isLt
  generalize b0.toNat = x0 at *; generalize b1.toNat = x1 at *; generalize b2.toNat = x2 at *
  generalize b3.toNat = x3 at *; generalize b4.toNat = x4 at *; generalize b5.toNat = x5 at *
  generalize b6.toNat = x6 at *; generalize b7.toNat = x7 at *
  rw [Nat.mod_eq_of_lt (show x0 < 2 ^ 64 by omega), shl_or x0 x1 8 (by omega),
    shl_or _ x2 16 (by omega), shl_or _ x3 24 (by omega), shl_or _ x4 32 (by omega),
    shl_or _ x5 40 (by omega), shl_or _ x6 48 (by omega), shl_or _ x7 56 (by omega)]
  norm_num
  omega
theorem bytesToWordLE8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7] =
      BitVec.ofNat 64 (leNat8 [b0, b1, b2, b3, b4, b5, b6, b7]) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := leNat8_lt [b0, b1, b2, b3, b4, b5, b6, b7]
  simp only [List.length_cons, List.length_nil] at hlt
  rw [bytesToWordLE8_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num at hlt ⊢; exact hlt)]
theorem bytesToWordLE_len8 (l : List (BitVec 8)) (hl : l.length = 8) :
    bytesToWordLE l = BitVec.ofNat 64 (leNat8 l) := by
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact bytesToWordLE8 b0 b1 b2 b3 b4 b5 b6 b7
theorem length_bytes {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]
theorem leNat8_slice {n : Nat} (x : Bytes n) : ∀ k a, a + k ≤ n →
    leNat8 (((bytes x).drop a).take k) = x.toNat / 2 ^ (8 * a) % 2 ^ (8 * k) := by
  intro k
  induction k with
  | zero => intro a _; simp only [List.take_zero, leNat8, Nat.mul_zero, pow_zero, Nat.mod_one]
  | succ k ih =>
    intro a h
    have ha : a < (bytes x).length := by rw [length_bytes]; omega
    rw [List.drop_eq_getElem_cons ha, List.take_succ_cons, leNat8, ih (a + 1) (by omega)]
    have hb : ((bytes x)[a]'ha).toNat = x.toNat / 2 ^ (8 * a) % 2 ^ 8 := by
      simp only [bytes, List.getElem_map, List.getElem_range, BitVec.extractLsb'_toNat,
        Nat.shiftRight_eq_div_pow]
    rw [hb, show 8 * (a + 1) = 8 * a + 8 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show 8 * (k + 1) = 8 + 8 * k by ring, Nat.pow_add 2 8 (8 * k), Nat.mod_mul]
theorem bytes_word {n : Nat} (x : Bytes n) (j : Nat) (h : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  rw [bytesToWordLE_len8 _ (by simp [length_bytes]; omega), leNat8_slice x 8 (8 * j) h]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * j) = 64 * j by ring, show 8 * 8 = 64 by rfl, Nat.mod_mod]
theorem bytesToWordLE_len4 (l : List (BitVec 8)) (hl : l.length = 4) :
    bytesToWordLE l = BitVec.ofNat 64 (leNat8 l) := by
  match l, hl with
  | [b0, b1, b2, b3], _ =>
    have e : bytesToWordLE [b0, b1, b2, b3] = bytesToWordLE [b0, b1, b2, b3, 0, 0, 0, 0] := rfl
    rw [e, bytesToWordLE8]
    simp [leNat8]
/-- The last, half-filled word of a buffer whose length is 4 mod 8: the loader zero-pads it. -/
theorem bytes_word_tail {n : Nat} (x : Bytes n) (j : Nat) (h : 8 * j + 4 = n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  have hd : ((bytes x).drop (8 * j)).length = 4 := by
    rw [List.length_drop, length_bytes]; omega
  have ht : ((bytes x).drop (8 * j)).take 8 = ((bytes x).drop (8 * j)).take 4 := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  rw [ht, bytesToWordLE_len4 _ (by rw [List.length_take, hd]; rfl), leNat8_slice x 4 (8 * j) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * j) = 64 * j by ring]
  have hx : x.toNat / 2 ^ (64 * j) < 2 ^ (8 * 4) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
    calc x.toNat < 2 ^ (8 * n) := x.isLt
      _ = 2 ^ (8 * 4 + 64 * j) := by congr 1; omega
  rw [Nat.mod_eq_of_lt hx]
theorem bytes_word_lt {n : Nat} (x : Bytes n) (j : Nat) (hn : n % 8 = 4) (h : 8 * j < n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  rcases Nat.lt_or_ge (8 * j + 8) (n + 1) with h1 | h1
  · exact bytes_word x j (by omega)
  · exact bytes_word_tail x j (by omega)
theorem extractByte_or8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)
theorem extractByte_bytesToWordLE (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8 _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0)]
def VERIFY_DATA : Nat := 0xffbde0
def MSGADDR : Nat := 23536
structure InitOK (m : T3.Message) (pk : Digest) (w : ClaudeWCT.W9.T3M.WBytes) (s : MachineState) : Prop where
  known : KnownOK k0 s
  pc : s.pc = pcOf 0
  msg : ∀ k, k < 4 → s.getMem (BitVec.ofNat 64 (MSGADDR + 8 * k)) = m.extractLsb' (64 * k) 64
  pk : PkOK pk s
  wit : WitAll w s
  zero : ∀ A, A < WIT → (A < 0xA0 ∨ 0xB0 ≤ A) → s.getMem (BitVec.ofNat 64 A) = 0
  data : DataOK s
  sp : s.getReg .x2 = BitVec.ofNat 64 VERIFY_DATA
theorem verifyData_length : (submission.image .verify).data.length = 16928 := Images.verifyData_length
theorem dataBase_verify : dataBase (submission.image .verify) = VERIFY_DATA := by
  unfold dataBase; rw [verifyData_length]; decide +kernel
theorem verifyData_mask :
    bytesToWordLE ((((submission.image .verify).data).drop 536).take 8) = 130048#64 := by
  decide +kernel
theorem verifyData_header (lay : Nat) (hl : lay < 4) :
    bytesToWordLE ((((submission.image .verify).data).drop (424 + 8 * ((lay + 1) % 4))).take 8) =
      BitVec.ofNat 64 (hyperBase lay) := by
  interval_cases lay <;> decide +kernel
theorem verifyData_initialMask :
    bytesToWordLE ((((submission.image .verify).data).take 8)) = 0xfff#64 := by
  decide +kernel
set_option maxRecDepth 200000 in
theorem init_ok (m : Legacy.Message) (pk : PublicKey) (w : Bytes 21484) (s : MachineState)
    (h : initialState submission .verify (m, pk, w) = some s) : InitOK m pk w s := by
  unfold initialState at h
  simp only [submission_admissible.2 .verify, if_true, Option.some.injEq] at h
  subst h
  have hl : inputBuffers submission.sizes submission.layout .verify (m, pk, w) =
      [(MSGADDR, bytes m), (0xA0, bytes pk), (0x800, bytes w)] := rfl
  rw [hl]
  simp only [List.foldl_cons, List.foldl_nil]
  have lm : (bytes m).length = 32 := length_bytes m
  have lp : (bytes pk).length = 16 := length_bytes pk
  have lw : (bytes w).length = 21484 := length_bytes w
  have lD := verifyData_length
  have eD := dataBase_verify
  set blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  set s0 := blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase (submission.image .verify)))
    (submission.image .verify).data
  set s1 := s0.writeBytesAsWords (BitVec.ofNat 64 MSGADDR) (bytes m)
  set s2 := s1.writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)
  set s3 := s2.writeBytesAsWords (BitVec.ofNat 64 0x800) (bytes w)
  have gm : ∀ A, (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getMem A =
      s3.getMem A := fun A => by simp [MachineState.setReg, MachineState.getMem]
  have g0 : ∀ A, A < 2 ^ 64 → s0.getMem (BitVec.ofNat 64 A) =
      if VERIFY_DATA ≤ A ∧ A < VERIFY_DATA + 8 * ((16928 + 7) / 8) ∧ (A - VERIFY_DATA) % 8 = 0 then
        bytesToWordLE ((((submission.image .verify).data).drop (A - VERIFY_DATA)).take 8) else 0 := by
    intro A hA
    rw [getMem_writeBytesAsWords (submission.image .verify).data blank (dataBase (submission.image .verify)) A
      (by rw [lD, eD]; unfold VERIFY_DATA; omega) hA, lD, eD]; rfl
  have g0z : ∀ A, A < VERIFY_DATA → s0.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA
    rw [g0 A (by unfold VERIFY_DATA at hA; omega), if_neg (by omega)]
  have g1 : ∀ A, A < 2 ^ 64 → s1.getMem (BitVec.ofNat 64 A) =
      if MSGADDR ≤ A ∧ A < MSGADDR + 8 * ((32 + 7) / 8) ∧ (A - MSGADDR) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - MSGADDR)).take 8) else s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s0 MSGADDR A (by rw [lm]; unfold MSGADDR; omega) hA, lm]
  have g2 : ∀ A, A < 2 ^ 64 → s2.getMem (BitVec.ofNat 64 A) =
      if 0xA0 ≤ A ∧ A < 0xA0 + 8 * ((16 + 7) / 8) ∧ (A - 0xA0) % 8 = 0 then
        bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8) else s1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s1 0xA0 A (by rw [lp]; omega) hA, lp]
  have g3 : ∀ A, A < 2 ^ 64 → s3.getMem (BitVec.ofNat 64 A) =
      if 0x800 ≤ A ∧ A < 0x800 + 8 * ((21484 + 7) / 8) ∧ (A - 0x800) % 8 = 0 then
        bytesToWordLE (((bytes w).drop (A - 0x800)).take 8) else s2.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [getMem_writeBytesAsWords _ s2 0x800 A (by rw [lw]; omega) hA, lw]
  have gb : ∀ A, VERIFY_DATA ≤ A → A < 2 ^ 24 →
      (s3.setReg .x2 (BitVec.ofNat 64 (dataBase (submission.image .verify)))).getByte
        (BitVec.ofNat 64 A) = (submission.image .verify).data.getD (A - VERIFY_DATA) 0 := by
    intro A hA hA'
    rw [T3M.getByte_eq_word _ _ (by omega), gm,
      g3 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g2 _ (by omega), if_neg (by unfold VERIFY_DATA at hA; omega),
      g1 _ (by omega), if_neg (by unfold VERIFY_DATA MSGADDR at *; omega),
      g0 _ (by omega), if_pos (by unfold VERIFY_DATA at *; omega),
      extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide +kernel))]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      if_pos (Nat.mod_lt A (show 0 < 8 by decide +kernel))]
    have hidx : A / 8 * 8 - VERIFY_DATA + A % 8 = A - VERIFY_DATA := by
      unfold VERIFY_DATA at hA ⊢
      omega
    rw [hidx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hr1 : ∀ (st : MachineState) (base : Word) (l : List (BitVec 8)),
        (st.writeBytesAsWords base l).regs = st.regs := by
      intro st base l
      induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length)
        generalizing st base with
      | hwf => exact (measure List.length).wf
      | h l ih =>
        match l with
        | [] => simp
        | b :: bs =>
          unfold MachineState.writeBytesAsWords
          rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
          rfl
    have hr : s3.regs = blank.regs := by simp only [s3, s2, s1, s0, hr1]
    simp only [k0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [MachineState.setReg, MachineState.getReg, hr, blank]
  · have hp1 : ∀ (st : MachineState) (base : Word) (l : List (BitVec 8)),
        (st.writeBytesAsWords base l).pc = st.pc := by
      intro st base l
      induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length)
        generalizing st base with
      | hwf => exact (measure List.length).wf
      | h l ih =>
        match l with
        | [] => simp
        | b :: bs =>
          unfold MachineState.writeBytesAsWords
          rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
          rfl
    simp only [MachineState.pc_setReg, s3, s2, s1, s0, hp1, blank]
    rfl
  · intro k hk
    unfold MSGADDR
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_pos (by unfold MSGADDR; omega), show 23536 + 8 * k - MSGADDR = 8 * k by unfold MSGADDR; omega,
      bytes_word m k (by omega)]
  · refine ⟨?_, ?_⟩
    · show (s3.setReg .x2 _).getMem (BitVec.ofNat 64 0xA0) = _
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_pos (by omega),
        show (0xA0 : Nat) - 0xA0 = 8 * 0 by rfl, bytes_word pk 0 (by omega)]
    · show (s3.setReg .x2 _).getMem (BitVec.ofNat 64 0xA8) = _
      rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_pos (by omega),
        show (0xA8 : Nat) - 0xA0 = 8 * 1 by rfl, bytes_word pk 1 (by omega)]
  · intro j hj
    unfold WX at hj
    rw [gm, g3 _ (by unfold WIT; omega), if_pos (by unfold WIT; omega),
      show WIT + 8 * j - 0x800 = 8 * j by unfold WIT; omega, bytes_word_lt w j (by norm_num) (by omega)]
    rfl
  · intro A hA hz
    unfold WIT at hA
    rw [gm, g3 _ (by omega), if_neg (by omega), g2 _ (by omega), if_neg (by omega), g1 _ (by omega),
      if_neg (by unfold MSGADDR; omega), g0z A (by unfold VERIFY_DATA; omega)]
  · refine ⟨?_, ?_⟩
    · rw [gm, g3 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE; omega),
        g2 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE; omega),
        g1 _ (by unfold TOPBASE; omega), if_neg (by unfold TOPBASE MSGADDR; omega),
        g0 _ (by unfold TOPBASE; omega), if_pos (by unfold TOPBASE VERIFY_DATA; omega),
        show TOPBASE - 8 - VERIFY_DATA = 536 by unfold TOPBASE VERIFY_DATA; omega,
        verifyData_mask]
    · intro lay hl
      have hb := hdrAddr_bounds lay
      unfold TOPBASE at hb
      rw [gm, g3 _ (by omega), if_neg (by omega),
        g2 _ (by omega), if_neg (by omega),
        g1 _ (by omega), if_neg (by unfold MSGADDR; omega),
        g0 _ (by omega), if_pos (by unfold hdrAddr TOPBASE VERIFY_DATA; omega),
        show hdrAddr lay - VERIFY_DATA = 424 + 8 * ((lay + 1) % 4) by unfold hdrAddr TOPBASE VERIFY_DATA; omega,
        verifyData_header lay hl]
  · simp [MachineState.setReg, MachineState.getReg]
    exact congrArg (BitVec.ofNat 64) eD
end SigGolfCandidate.T3M.Verify
