import SigGolfCandidate.T3M.Sign.Basic
import SigGolfCandidate.T3.FullCache.Polynomial

section


namespace SigGolfCandidate.T3M.FullCache.MacPass
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SphincsSecurity
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
def fold61 (x : Nat) : Nat := x / 2 ^ 61 + x % 2 ^ 61
theorem fold61_mod (x : Nat) : fold61 x % macPrime = x % macPrime := by
  unfold fold61 macPrime
  have := Nat.div_add_mod x (2 ^ 61)
  simp only [Nat.reducePow, Nat.reduceSub] at *
  omega
def macStep (acc c k : Nat) : Nat := fold61 (fold61 ((acc + c) * k))
theorem macStep_mod (acc c k : Nat) : macStep acc c k % macPrime = (acc + c) * k % macPrime := by
  unfold macStep; rw [fold61_mod, fold61_mod]
theorem mul_lt_123 (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    (acc + c) * k < 2 ^ 123 :=
  calc (acc + c) * k < 2 ^ 62 * 2 ^ 61 := Nat.mul_lt_mul'' (by omega) hk
    _ = 2 ^ 123 := by norm_num
theorem fold61_lt_64 (m : Nat) (hm : m < 2 ^ 123) : fold61 m < 2 ^ 64 := by
  unfold fold61
  have h1 : m / 2 ^ 61 < 2 ^ 62 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have h2 := Nat.mod_lt m (show 0 < 2 ^ 61 by norm_num)
  omega
theorem fold61_small (s : Nat) (hs : s < 2 ^ 64) : fold61 s < 2 ^ 61 + 7 := by
  unfold fold61
  have h2 := Nat.mod_lt s (show 0 < 2 ^ 61 by norm_num)
  omega
theorem macStep_lt (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    macStep acc c k < 2 ^ 61 + 7 :=
  fold61_small _ (fold61_lt_64 _ (mul_lt_123 acc c k hacc hc hk))
def macStep2 (k acc w : Nat) : Nat := macStep (macStep acc (w % 2 ^ 32) k) (w / 2 ^ 32) k
def passAcc (k : Nat) (ws : List Nat) : Nat := ws.foldl (macStep2 k) 0
def chunksOf (ws : List Nat) : List Nat := ws.flatMap fun w => [w % 2 ^ 32, w / 2 ^ 32]
theorem foldl_macStep2 (k : Nat) (hk : k < 2 ^ 61) (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 64)
    (a b : Nat) (ha : a < 2 ^ 61 + 7) (hab : a % macPrime = b % macPrime) :
    ws.foldl (macStep2 k) a < 2 ^ 61 + 7 ∧
      ws.foldl (macStep2 k) a % macPrime =
        (chunksOf ws).foldl (fun acc c => (acc + c) * k % macPrime) b % macPrime := by
  induction ws generalizing a b with
  | nil => exact ⟨ha, hab⟩
  | cons w ws ih =>
    have hw := hws w (by simp)
    have h1 : w % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
    have h2 : w / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hw (by norm_num)
    have hlt1 := macStep_lt a (w % 2 ^ 32) k ha h1 hk
    have hlt2 := macStep_lt _ (w / 2 ^ 32) k hlt1 h2 hk
    simp only [List.foldl_cons, chunksOf, List.flatMap_cons, List.cons_append, List.nil_append]
    refine ih (fun x hx => hws x (by simp [hx])) _ _ hlt2 ?_
    unfold macStep2
    rw [macStep_mod, Nat.mod_mod]
    refine Nat.ModEq.mul_right k (Nat.ModEq.add_right _ ?_)
    show macStep a (w % 2 ^ 32) k % macPrime = (b + w % 2 ^ 32) * k % macPrime % macPrime
    rw [macStep_mod, Nat.mod_mod]
    exact Nat.ModEq.mul_right k (Nat.ModEq.add_right _ hab)
theorem passAcc_spec (k : Nat) (hk : k < 2 ^ 61) (ws : List Nat) (hws : ∀ w ∈ ws, w < 2 ^ 64) :
    passAcc k ws < 2 ^ 61 + 7 ∧ passAcc k ws % macPrime = polyMac k (chunksOf ws) := by
  obtain ⟨h1, h2⟩ := foldl_macStep2 k hk ws hws 0 0 (by norm_num) rfl
  refine ⟨h1, h2.trans ?_⟩
  unfold polyMac
  generalize chunksOf ws = cs
  rcases List.eq_nil_or_concat cs with rfl | ⟨cs', c, rfl⟩
  · rfl
  · rw [List.concat_eq_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.mod_mod]
theorem canon_eq (acc : Nat) (hacc : acc < 2 ^ 61 + 7) :
    (if fold61 acc = macPrime then 0 else fold61 acc) = acc % macPrime := by
  have hm := fold61_mod acc
  have hlt : fold61 acc ≤ macPrime := by
    unfold fold61 macPrime
    have h2 := Nat.mod_lt acc (show 0 < 2 ^ 61 by norm_num)
    simp only [Nat.reducePow, Nat.reduceSub] at *
    omega
  split_ifs with h
  · rw [← hm, h, Nat.mod_self]
  · rw [← hm, Nat.mod_eq_of_lt (lt_of_le_of_ne hlt h)]
theorem mulhu_toNat (a b : Word) : (rv64_mulhu a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  unfold rv64_mulhu
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show a.toNat * b.toNat < 2 ^ 128 by omega)]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  exact hab
theorem and_p_toNat (x : Word) : (x &&& BitVec.ofNat 64 (2 ^ 61 - 1)).toNat = x.toNat % 2 ^ 61 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), Nat.and_two_pow_sub_one_eq_mod]
def stepW (acc c k p : Word) : Word :=
  let t := c + acc
  let hi := rv64_mulhu t k
  let lo := t * k
  let s := (hi <<< 3) + (lo >>> 61) + (lo &&& p)
  (s >>> 61) + (s &&& p)
theorem stepW_ofNat (acc c k : Nat) (hacc : acc < 2 ^ 61 + 7) (hc : c < 2 ^ 32) (hk : k < 2 ^ 61) :
    stepW (BitVec.ofNat 64 acc) (BitVec.ofNat 64 c) (BitVec.ofNat 64 k) (BitVec.ofNat 64 (2 ^ 61 - 1)) =
      BitVec.ofNat 64 (macStep acc c k) := by
  have hm := mul_lt_123 acc c k hacc hc hk
  have hs := fold61_lt_64 _ hm
  apply BitVec.eq_of_toNat_eq
  unfold stepW macStep
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, and_p_toNat,
    mulhu_toNat, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c + acc < 2 ^ 64 by omega),
    Nat.add_comm c acc]
  generalize (acc + c) * k = m at hm hs ⊢
  have hhi : m / 2 ^ 64 < 2 ^ 59 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have e1 : m / 2 ^ 64 * 2 ^ 3 % 2 ^ 64 = m / 2 ^ 64 * 8 := by
    rw [show (2 : Nat) ^ 3 = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  have e2 : m / 2 ^ 64 * 8 + m % 2 ^ 64 / 2 ^ 61 = m / 2 ^ 61 := by
    have := Nat.div_add_mod m (2 ^ 64)
    omega
  have e3 : m % 2 ^ 64 % 2 ^ 61 = m % 2 ^ 61 := Nat.mod_mod_of_dvd m (by norm_num)
  have h61 : m / 2 ^ 61 < 2 ^ 62 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hm (by norm_num)
  have h61' := Nat.mod_lt m (show 0 < 2 ^ 61 by norm_num)
  rw [e1, e3, Nat.mod_eq_of_lt (show m / 2 ^ 64 * 8 + m % 2 ^ 64 / 2 ^ 61 < 2 ^ 64 by omega), e2,
    Nat.mod_eq_of_lt (show m / 2 ^ 61 + m % 2 ^ 61 < 2 ^ 64 by omega)]
  rfl
def tailW (acc p pad : Word) : Word :=
  let a := (acc &&& p) + (acc >>> 61)
  let b : Word := if BitVec.ult (a ^^^ p) 1 then 1 else 0
  (a &&& (b + 18446744073709551615#64)) + pad
theorem tailW_ofNat (acc : Nat) (hacc : acc < 2 ^ 61 + 7) (pad : Word) :
    tailW (BitVec.ofNat 64 acc) (BitVec.ofNat 64 (2 ^ 61 - 1)) pad =
      BitVec.ofNat 64 (acc % macPrime) + pad := by
  have hc := canon_eq acc hacc
  have ha : (BitVec.ofNat 64 acc &&& BitVec.ofNat 64 (2 ^ 61 - 1)) + (BitVec.ofNat 64 acc >>> 61) =
      BitVec.ofNat 64 (fold61 acc) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, and_p_toNat, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega), BitVec.toNat_ofNat]
    unfold fold61
    rw [Nat.add_comm]
  unfold tailW
  simp only [ha]
  have hf : fold61 acc < 2 ^ 64 := by have := fold61_small acc (by omega); omega
  by_cases h : fold61 acc = macPrime
  · rw [if_pos h] at hc
    rw [← hc, h]
    have : BitVec.ult (BitVec.ofNat 64 macPrime ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = true := by
      show BitVec.ult (BitVec.ofNat 64 (2 ^ 61 - 1) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = true
      rw [BitVec.xor_self]; rfl
    have e : ((1 : Word) + 18446744073709551615#64) = 0 := by decide
    rw [this, if_pos rfl, e]
    simp
  · rw [if_neg h] at hc
    have hx : BitVec.ult (BitVec.ofNat 64 (fold61 acc) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)) 1 = false := by
      rw [Bool.eq_false_iff]
      intro hu
      apply h
      have hu' : (BitVec.ofNat 64 (fold61 acc) ^^^ BitVec.ofNat 64 (2 ^ 61 - 1)).toNat < (1#64).toNat :=
        of_decide_eq_true hu
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf,
        Nat.mod_eq_of_lt (by norm_num)] at hu'
      have h0 := Nat.lt_one_iff.mp hu'
      have hm : macPrime = fold61 acc := by
        calc macPrime = (fold61 acc ^^^ fold61 acc) ^^^ (2 ^ 61 - 1) := by rw [Nat.xor_self, Nat.zero_xor]; rfl
          _ = fold61 acc ^^^ (fold61 acc ^^^ (2 ^ 61 - 1)) := Nat.xor_assoc _ _ _
          _ = fold61 acc := by rw [h0, Nat.xor_zero]
      exact hm.symm
    rw [hx, ← hc]
    have e : ((0 : Word) + 18446744073709551615#64) = BitVec.allOnes 64 := by decide
    simp only [Bool.false_eq_true, if_false]
    rw [e, BitVec.and_allOnes]
theorem ofNat_toNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem byteOffset_ofNat {x : Nat} (hx : x < 2 ^ 64) : byteOffset (BitVec.ofNat 64 x) = x % 8 := by
  rw [byteOffset_eq, ofNat_toNat_lt hx]
theorem alignToDword_ofNat_aligned {x : Nat} (hx : x < 2 ^ 64) (h8 : x % 8 = 0) :
    alignToDword (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [alignToDword_toNat, ofNat_toNat_lt hx]; omega
theorem exec_load {s : MachineState} {k : LoadKind} {rd rs : Reg} {off : Word}
    (h : accessValid (s.getReg rs + off) k.width = true) :
    (Micro.load k rd rs off).exec s = some ((s.setReg rd (k.read s (s.getReg rs + off))).setPC (s.pc + 4)) := by
  simp [Micro.exec, h]
theorem getReg_setReg' (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r' = r ∧ r ≠ .x0 then v else s.getReg r' := by
  cases r <;> cases r' <;> rfl
@[simp] theorem pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl
theorem microN {image : Image} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    {s t u : MachineState} (m : Micro) {k c n : Nat}
    (hc : CodeAt image pc (w :: ws)) (hpc : s.pc = pc)
    (hd : ∃ i, decodeInstruction w = some i ∧ classify i = some m ∧ instructionCycles i = n)
    (hex : m.exec s = some t) (tail : Steps image t k c u) : Steps image s (k + 1) (n + c) u := by
  obtain ⟨i, h1, h2, h3⟩ := hd
  have := Steps.step (hc.fetch s hpc ▸ h1) ((classify_sound h2 s).trans hex) tail
  rwa [h3] at this
theorem codeAt_drop {image : Image} : ∀ (n : Nat) {pc : Word} {code : List (BitVec 32)},
    CodeAt image pc code → n ≤ code.length → CodeAt image (pc + BitVec.ofNat 64 (4 * n)) (code.drop n)
  | 0, pc, code, h, _ => by simpa using h
  | n + 1, pc, [], h, hn => by simp at hn
  | n + 1, pc, w :: ws, h, hn => by
      have h' := codeAt_drop n h.tail (by simpa using hn)
      have e : pc + 4 + BitVec.ofNat 64 (4 * n) = pc + BitVec.ofNat 64 (4 * (n + 1)) := by
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]
        omega
      rw [List.drop_succ_cons, ← e]
      exact h'
def macPassCode : List (BitVec 32) :=
  [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem read_wu0 (s : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24) :
    LoadKind.wu.read s (BitVec.ofNat 64 A + 0) =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 A)).toNat % 2 ^ 32) := by
  have e0 : BitVec.ofNat 64 A + 0 = BitVec.ofNat 64 A := by simp
  rw [e0, LoadKind.read_sub _ _ _ (by decide), byteOffset_ofNat (by omega),
    alignToDword_ofNat_aligned (by omega) hA]
  apply BitVec.eq_of_toNat_eq
  simp [LoadKind.fromWord, extractWord32, hA, Nat.shiftRight_eq_div_pow]
theorem read_wu4 (s : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24) :
    LoadKind.wu.read s (BitVec.ofNat 64 A + 4) =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 A)).toNat / 2 ^ 32) := by
  have e : BitVec.ofNat 64 A + 4 = BitVec.ofNat 64 (A + 4) := by
    apply BitVec.eq_of_toNat_eq; simp
  have ea : alignToDword (BitVec.ofNat 64 (A + 4)) = BitVec.ofNat 64 A := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]; omega
  rw [e, LoadKind.read_sub _ _ _ (by decide), byteOffset_ofNat (by omega), ea]
  apply BitVec.eq_of_toNat_eq
  have hw := (s.getMem (BitVec.ofNat 64 A)).isLt
  simp [LoadKind.fromWord, extractWord32, show (A + 4) % 8 = 4 by omega, Nat.shiftRight_eq_div_pow]
  omega
theorem chunk0_steps {image : Image} {pc : Word} {rest : List (BitVec 32)}
    (hc : CodeAt image pc (0x0006e783 :: 0x00e787b3 :: 0x0377b833 :: 0x037787b3 :: 0x00381813 :: 0x03d7d893 :: 0x01180833 :: 0x0127f7b3 :: 0x00f80833 :: 0x03d85713 :: 0x01287833 :: 0x01070733 :: rest))
    (s : MachineState) (hpc : s.pc = pc)
    (hv : accessValid (s.getReg .x13 + 0) (LoadKind.width .wu) = true) :
    ∃ u, Steps image s 12 18 u ∧ u.pc = pc + 48 ∧
      u.getReg .x14 = stepW (s.getReg .x14) (LoadKind.wu.read s (s.getReg .x13 + 0)) (s.getReg .x23)
        (s.getReg .x18) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  have hc8 := hc7.tail
  have hc9 := hc8.tail
  have hc10 := hc9.tail
  have hc11 := hc10.tail
  refine ⟨_, microN (.load .wu .x15 .x13 0) hc hpc ⟨_, rfl, rfl, rfl⟩ (exec_load hv) <|
    microN (.alu .x15 .add (.reg .x15) (.reg .x14)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .mulhu (.reg .x15) (.reg .x23)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .mul (.reg .x15) (.reg .x23)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .sll (.reg .x16) (.imm 3)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x17 .srl (.reg .x15) (.imm 61)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x17)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .and (.reg .x15) (.reg .x18)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x15)) hc8 ?p8 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .srl (.reg .x16) (.imm 61)) hc9 ?p9 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .and (.reg .x16) (.reg .x18)) hc10 ?p10 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x16)) hc11 ?p11 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, stepW]
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp
theorem chunk4_steps {image : Image} {pc : Word} {rest : List (BitVec 32)}
    (hc : CodeAt image pc (0x0046e783 :: 0x00e787b3 :: 0x0377b833 :: 0x037787b3 :: 0x00381813 :: 0x03d7d893 :: 0x01180833 :: 0x0127f7b3 :: 0x00f80833 :: 0x03d85713 :: 0x01287833 :: 0x01070733 :: rest))
    (s : MachineState) (hpc : s.pc = pc)
    (hv : accessValid (s.getReg .x13 + 4) (LoadKind.width .wu) = true) :
    ∃ u, Steps image s 12 18 u ∧ u.pc = pc + 48 ∧
      u.getReg .x14 = stepW (s.getReg .x14) (LoadKind.wu.read s (s.getReg .x13 + 4)) (s.getReg .x23)
        (s.getReg .x18) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  have hc8 := hc7.tail
  have hc9 := hc8.tail
  have hc10 := hc9.tail
  have hc11 := hc10.tail
  refine ⟨_, microN (.load .wu .x15 .x13 4) hc hpc ⟨_, rfl, rfl, rfl⟩ (exec_load hv) <|
    microN (.alu .x15 .add (.reg .x15) (.reg .x14)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .mulhu (.reg .x15) (.reg .x23)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .mul (.reg .x15) (.reg .x23)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .sll (.reg .x16) (.imm 3)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x17 .srl (.reg .x15) (.imm 61)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x17)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .and (.reg .x15) (.reg .x18)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .add (.reg .x16) (.reg .x15)) hc8 ?p8 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .srl (.reg .x16) (.imm 61)) hc9 ?p9 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x16 .and (.reg .x16) (.reg .x18)) hc10 ?p10 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x16)) hc11 ?p11 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, stepW]
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp
theorem body_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 6))
    (s : MachineState) (hpc : s.pc = pc) (A acc k E : Nat)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 8 ≤ 2 ^ 24)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 acc) (hacc : acc < 2 ^ 61 + 7)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 k) (hk : k < 2 ^ 61)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 E) (hE : E < 2 ^ 64) :
    ∃ u, Steps image s 26 38 u ∧
      u.pc = (if A + 8 = E then pc + 104 else pc) ∧
      u.getReg .x13 = BitVec.ofNat 64 (A + 8) ∧
      u.getReg .x14 = BitVec.ofNat 64 (macStep2 k acc (s.getMem (BitVec.ofNat 64 A)).toNat) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hv : ∀ off : Nat, off = 0 ∨ off = 4 →
      accessValid (BitVec.ofNat 64 A + BitVec.ofNat 64 off) 4 = true := by
    intro off hoff
    rw [accessValid_iff, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show A < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show A + off < 2 ^ 64 by omega)]
    exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩
  have hw := (s.getMem (BitVec.ofNat 64 A)).isLt
  generalize hwdef : (s.getMem (BitVec.ofNat 64 A)).toNat = w at hw
  have hlo : w % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hhi : w / 2 ^ 32 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hw (by norm_num)
  obtain ⟨u0, st0, pc0, a0, r0, m0⟩ := chunk0_steps (rest := macPassCode.drop 18) hc s hpc
    (by rw [h13]; exact hv 0 (Or.inl rfl))
  rw [h13, h14, h23, h18, read_wu0 s A hA hA', hwdef,
    stepW_ofNat acc (w % 2 ^ 32) k hacc hlo hk] at a0
  have hlt1 := macStep_lt acc (w % 2 ^ 32) k hacc hlo hk
  have hc4 : CodeAt image (pc + 48) (macPassCode.drop 18) := codeAt_drop 12 hc (by decide)
  have e13 : u0.getReg .x13 = BitVec.ofNat 64 A := by
    rw [r0 .x13 (by decide) (by decide) (by decide) (by decide), h13]
  have e23 : u0.getReg .x23 = BitVec.ofNat 64 k := by
    rw [r0 .x23 (by decide) (by decide) (by decide) (by decide), h23]
  have e18 : u0.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1) := by
    rw [r0 .x18 (by decide) (by decide) (by decide) (by decide), h18]
  obtain ⟨u1, st1, pc1, a1, r1, m1⟩ := chunk4_steps (rest := macPassCode.drop 30) hc4 u0 pc0
    (by rw [e13]; exact hv 4 (Or.inr rfl))
  rw [e13, a0, e23, e18, read_wu4 u0 A hA hA', m0, hwdef,
    stepW_ofNat _ (w / 2 ^ 32) k hlt1 hhi hk] at a1
  have hc5 : CodeAt image (pc + 48 + 48) (macPassCode.drop 30) := codeAt_drop 12 hc4 (by decide)
  have hc6 := hc5.tail
  have x13 : u1.getReg .x13 = BitVec.ofNat 64 A := by
    rw [r1 .x13 (by decide) (by decide) (by decide) (by decide), e13]
  have x19 : u1.getReg .x19 = BitVec.ofNat 64 E := by
    rw [r1 .x19 (by decide) (by decide) (by decide) (by decide),
      r0 .x19 (by decide) (by decide) (by decide) (by decide), h19]
  have st2 : Steps image u1 2 2 _ :=
    microN (.alu .x13 .add (.reg .x13) (.imm 8)) hc5 pc1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.branch .ne .x13 .x19 0xffffffffffffff9c) hc6 (by simp [pc1]) ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _
  have e8 : BitVec.ofNat 64 A + 8#64 = BitVec.ofNat 64 (A + 8) := by
    apply BitVec.eq_of_toNat_eq; simp
  have hcond : (BitVec.ofNat 64 (A + 8) = BitVec.ofNat 64 E) ↔ A + 8 = E := by
    constructor
    · intro hh
      have := congrArg BitVec.toNat hh
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hE] at this
    · rintro rfl; rfl
  refine ⟨_, (st0.trans (st1.trans st2)).of_eq rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [getReg_setReg', Src.eval, BinOp.eval, CmpOp.eval, x13, x19, pc1]
    simp only [e8, hcond]
    split_ifs
    · bv_omega
    · bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, x13, e8]
  · simp [getReg_setReg', Src.eval, BinOp.eval, a1, macStep2]
  · intro r h1 h2 h3 h4 h5
    simp [getReg_setReg', h1]
    rw [r1 r h2 h3 h4 h5, r0 r h2 h3 h4 h5]
  · intro a
    simp [m1, m0]
theorem loop_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 6))
    (s : MachineState) (hpc : s.pc = pc) (B0 n k : Nat) (ws : List Nat) (hn : 0 < n)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 B0) (hB : B0 % 8 = 0) (hB' : B0 + 8 * n ≤ 2 ^ 24)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 0)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 k) (hk : k < 2 ^ 61)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 (B0 + 8 * n))
    (hlen : ws.length = n)
    (hmem : ∀ i < n, (s.getMem (BitVec.ofNat 64 (B0 + 8 * i))).toNat = ws.getD i 0) :
    ∃ u, Steps image s (n * 26) (n * 38) u ∧ u.pc = pc + 104 ∧
      u.getReg .x14 = BitVec.ofNat 64 (passAcc k ws) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hws : ∀ w ∈ ws, w < 2 ^ 64 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have := hmem i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [← this]; exact BitVec.isLt _
  let Inv : Nat → MachineState → Prop := fun i t =>
    i ≤ n ∧ t.pc = (if i = 0 then pc + 104 else pc) ∧
    t.getReg .x13 = BitVec.ofNat 64 (B0 + 8 * (n - i)) ∧
    t.getReg .x14 = BitVec.ofNat 64 ((ws.take (n - i)).foldl (macStep2 k) 0) ∧
    (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → t.getReg r = s.getReg r) ∧
    ∀ a, t.getMem a = s.getMem a
  have body : ∀ i t, Inv (i + 1) t → ∃ u, Steps image t 26 38 u ∧ Inv i u := by
    intro i t ⟨hi, tpc, t13, t14, treg, tmem⟩
    have hj : n - (i + 1) < n := by omega
    have hacc := (foldl_macStep2 k hk (ws.take (n - (i + 1)))
      (fun w hw => hws w (List.mem_of_mem_take hw)) 0 0 (by norm_num) rfl).1
    obtain ⟨u, st, upc, u13, u14, ureg, umem⟩ := body_steps hc t (by simpa using tpc)
      (B0 + 8 * (n - (i + 1))) _ k (B0 + 8 * n) t13 (by omega) (by omega) t14 hacc
      (by rw [treg .x23 (by decide) (by decide) (by decide) (by decide) (by decide), h23]) hk
      (by rw [treg .x18 (by decide) (by decide) (by decide) (by decide) (by decide), h18])
      (by rw [treg .x19 (by decide) (by decide) (by decide) (by decide) (by decide), h19]) (by omega)
    refine ⟨u, st, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [upc]
      by_cases h0 : i = 0
      · subst h0; rw [if_pos (by omega), if_pos rfl]
      · rw [if_neg (by omega), if_neg h0]
    · rw [u13]; congr 1; omega
    · rw [u14, tmem, hmem _ hj]
      congr 1
      have e : n - i = (n - (i + 1)) + 1 := by omega
      rw [e, List.take_add_one, List.foldl_append, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      simp
    · intro r h1 h2 h3 h4 h5
      rw [ureg r h1 h2 h3 h4 h5, treg r h1 h2 h3 h4 h5]
    · intro a; rw [umem, tmem]
  have hinit : Inv n s := by
    refine ⟨le_refl _, ?_, ?_, ?_, fun _ _ _ _ _ _ => rfl, fun _ => rfl⟩
    · rw [hpc, if_neg (by omega)]
    · simpa using h13
    · simpa using h14
  obtain ⟨u, st, _, upc, _, u14, ureg, umem⟩ := Steps.iterate Inv body n s hinit
  refine ⟨u, st, by simpa using upc, ?_, ureg, umem⟩
  rw [u14, Nat.sub_zero, ← hlen, List.take_length]
  rfl
theorem valid_d (B : Nat) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24) (off : Word) (hoff : off = 0 ∨ off = 8) :
    accessValid (BitVec.ofNat 64 B + off) 8 = true := by
  have z : BitVec.ofNat 64 B + (0 : Word) = BitVec.ofNat 64 B := by simp
  have e0 : (BitVec.ofNat 64 B + (0 : Word)).toNat = B := by
    rw [z, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have e8 : (BitVec.ofNat 64 B + (8 : Word)).toNat = B + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl,
      Nat.mod_eq_of_lt (show B < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [accessValid_iff]
  rcases hoff with rfl | rfl
  · rw [e0]; exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩
  · rw [e8]; exact ⟨by simp [MEMORY_BYTES]; omega, by omega⟩
theorem head_steps {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1)) :
    ∃ u, Steps image s 6 6 u ∧ u.pc = pc + 24 ∧
      u.getReg .x23 = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) ∧
      u.getReg .x24 = s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      u.getReg .x13 = BitVec.ofNat 64 0x80020 ∧ u.getReg .x14 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x23 → r ≠ .x24 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have e8 : BitVec.ofNat 64 B + 8#64 = BitVec.ofNat 64 (B + 8) := by
    apply BitVec.eq_of_toNat_eq; simp
  have k_eq : s.getMem (BitVec.ofNat 64 B) &&& s.getReg .x18 =
      BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) := by
    rw [h18]
    apply BitVec.eq_of_toNat_eq
    rw [and_p_toNat, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt (s.getMem (BitVec.ofNat 64 B)).toNat
      (show 0 < 2 ^ 61 by norm_num)) (show 2 ^ 61 ≤ 2 ^ 64 by norm_num))).symm
  refine ⟨_, microN (.load .d .x23 .x22 0) hc hpc ⟨_, rfl, rfl, rfl⟩
      (exec_load (by rw [h22]; exact valid_d B hB hB' 0 (Or.inl rfl))) <|
    microN (.alu .x23 .and (.reg .x23) (.reg .x18)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.load .d .x24 .x22 8) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩
      (exec_load (by
        simp only [getReg_setReg', MachineState.getReg_setPC]
        simp [h22]
        exact valid_d B hB hB' 8 (Or.inr rfl))) <|
    microN (.alu .x13 .add (.imm 0x80000) (.imm 0)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x13 .add (.reg .x13) (.imm 32)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x0) (.imm 0)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, LoadKind.read, h22, k_eq]
  · simp [getReg_setReg', Src.eval, BinOp.eval, LoadKind.read, h22, e8]
  · simp [getReg_setReg', Src.eval, BinOp.eval]
  · simp [getReg_setReg', Src.eval, BinOp.eval]
    rfl
  · intro r h1 h2 h3 h4
    simp [getReg_setReg', h1, h2, h3, h4]
  · intro a; simp
theorem tail_steps {image : Image} {pc : Word} (hc : CodeAt image pc (macPassCode.drop 32))
    (s : MachineState) (hpc : s.pc = pc) :
    ∃ u, Steps image s 8 8 u ∧ u.pc = pc + 32 ∧
      u.getReg .x14 = tailW (s.getReg .x14) (s.getReg .x18) (s.getReg .x24) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hc1 := hc.tail
  have hc2 := hc1.tail
  have hc3 := hc2.tail
  have hc4 := hc3.tail
  have hc5 := hc4.tail
  have hc6 := hc5.tail
  have hc7 := hc6.tail
  refine ⟨_, microN (.alu .x15 .srl (.reg .x14) (.imm 61)) hc hpc ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .and (.reg .x14) (.reg .x18)) hc1 ?p1 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x15)) hc2 ?p2 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .xor (.reg .x14) (.reg .x18)) hc3 ?p3 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .sltu (.reg .x15) (.imm 1)) hc4 ?p4 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x15 .add (.reg .x15) (.imm 0xffffffffffffffff)) hc5 ?p5 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .and (.reg .x14) (.reg .x15)) hc6 ?p6 ⟨_, rfl, rfl, rfl⟩ rfl <|
    microN (.alu .x14 .add (.reg .x14) (.reg .x24)) hc7 ?p7 ⟨_, rfl, rfl, rfl⟩ rfl <|
    Steps.refl _, ?_⟩
  case p1 | p2 | p3 | p4 | p5 | p6 | p7 => simp [hpc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hpc]; bv_omega
  · simp [getReg_setReg', Src.eval, BinOp.eval, tailW]
  · intro r h1 h2
    simp [getReg_setReg', h1, h2]
  · intro a; simp
theorem mac_pass {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat) (ws : List Nat)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0xA0000)
    (hlen : ws.length = 16380)
    (hmem : ∀ i < 16380, (s.getMem (BitVec.ofNat 64 (0x80020 + 8 * i))).toNat = ws.getD i 0) :
    ∃ u, Steps image s 425894 622454 u ∧ u.pc = pc + 160 ∧
      u.getReg .x14 =
        BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) (chunksOf ws)) +
          s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 →
        u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hk : (s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61 < 2 ^ 61 := Nat.mod_lt _ (by norm_num)
  obtain ⟨u0, st0, pc0, k0, p0, a13, a14, r0, m0⟩ := head_steps hc s hpc B h22 hB hB' h18
  have hcl : CodeAt image (pc + 24) (macPassCode.drop 6) := codeAt_drop 6 hc (by decide)
  have hws : ∀ w ∈ ws, w < 2 ^ 64 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have := hmem i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [← this]; exact BitVec.isLt _
  obtain ⟨u1, st1, pc1, b14, r1, m1⟩ := loop_steps hcl u0 pc0 0x80020 16380 _ ws (by norm_num) a13
    (by norm_num) (by norm_num) a14 k0 hk
    (by rw [r0 .x18 (by decide) (by decide) (by decide) (by decide), h18])
    (by rw [r0 .x19 (by decide) (by decide) (by decide) (by decide), h19]) hlen
    (fun i hi => by rw [m0]; exact hmem i hi)
  have hct : CodeAt image (pc + 24 + 104) (macPassCode.drop 32) := codeAt_drop 26 hcl (by decide)
  obtain ⟨u2, st2, pc2, c14, r2, m2⟩ := tail_steps hct u1 pc1
  obtain ⟨hlt, hmod⟩ := passAcc_spec _ hk ws hws
  refine ⟨u2, (st0.trans (st1.trans st2)).of_eq (by norm_num) (by norm_num), ?_, ?_, ?_, ?_⟩
  · rw [pc2]; bv_omega
  · rw [c14, b14, r1 .x18 (by decide) (by decide) (by decide) (by decide) (by decide),
      r0 .x18 (by decide) (by decide) (by decide) (by decide), h18,
      r1 .x24 (by decide) (by decide) (by decide) (by decide) (by decide), p0,
      tailW_ofNat _ hlt, hmod]
  · intro r h13 h14 h15 h16 h17 h23 h24
    rw [r2 r h14 h15, r1 r h13 h14 h15 h16 h17, r0 r h13 h14 h23 h24]
  · intro a; rw [m2, m1, m0]
end SigGolfCandidate.T3M.FullCache.MacPass
end

section







section
namespace SigGolfCandidate.T3M.FullCache.MacPass
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)
theorem readWords_getD (t : MachineState) : ∀ (n a i : Nat), i < n →
    (t.readWords (BitVec.ofNat 64 a) n).getD i 0 = t.getMem (BitVec.ofNat 64 (a + 8 * i))
  | 0, _, _, h => by omega
  | n + 1, a, i, h => by
      have e : BitVec.ofNat 64 a + 8 = BitVec.ofNat 64 (a + 8) := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [MachineState.readWords_succ, e]
      cases i with
      | zero => simp
      | succ i =>
        rw [List.getD_cons_succ, readWords_getD t n (a + 8) i (by omega)]
        congr 2; omega
theorem chunksOf_of_wordsToNat : ∀ (n : Nat) (R : List Word) (l : List UInt8), R.length = n →
    l.length = 8 * n → wordsToNat R = T3.readLE l → chunksOf (R.map BitVec.toNat) = chunks32 l
  | 0, R, l, hR, hl, _ => by
      rw [List.length_eq_zero_iff.mp hR, List.length_eq_zero_iff.mp (by omega : l.length = 0)]
      rfl
  | n + 1, R, l, hR, hl, h => by
      obtain ⟨w, R', rfl⟩ : ∃ w R', R = w :: R' := by
        cases R with
        | nil => simp at hR
        | cons w R' => exact ⟨w, R', rfl⟩
      obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, l', rfl⟩ :
          ∃ b0 b1 b2 b3 b4 b5 b6 b7 l', l = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l' := by
        match l, hl with
        | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l', _ => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        | [], h => simp at h <;> omega
        | [_], h => simp at h <;> omega
        | [_, _], h => simp at h <;> omega
        | [_, _, _], h => simp at h <;> omega
        | [_, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _, _], h => simp at h <;> omega
        | [_, _, _, _, _, _, _], h => simp at h <;> omega
      simp only [List.length_cons] at hR hl
      have hw := w.isLt
      have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
      have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
      simp only [wordsToNat, T3M.readLE_cons] at h
      have hsplit : w.toNat = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat +
          256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) ∧
          wordsToNat R' = T3.readLE l' := by
        constructor <;> omega
      have ih := chunksOf_of_wordsToNat n R' l' (by omega) (by omega) hsplit.2
      simp only [List.map_cons, chunksOf, List.flatMap_cons, List.cons_append, List.nil_append, chunks32]
      rw [show List.flatMap (fun w => [w % 2 ^ 32, w / 2 ^ 32]) (List.map BitVec.toNat R') =
        chunksOf (R'.map BitVec.toNat) from rfl, ih]
      congr 1
      · rw [hsplit.1]; omega
      · congr 1
        rw [hsplit.1]; omega
theorem mac_pass_region {image : Image} {pc : Word} (hc : CodeAt image pc macPassCode)
    (s : MachineState) (hpc : s.pc = pc) (B : Nat) (region : List UInt8)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B + 16 ≤ 2 ^ 24)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0xA0000)
    (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 0x80020) 16380) = T3.readLE region) :
    ∃ u, Steps image s 425894 622454 u ∧ u.pc = pc + 160 ∧
      u.getReg .x14 =
        BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 B)).toNat % 2 ^ 61) (chunks32 region)) +
          s.getMem (BitVec.ofNat 64 (B + 8)) ∧
      (∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 →
        u.getReg r = s.getReg r) ∧
      ∀ a, u.getMem a = s.getMem a := by
  have hR := readWords_length s (BitVec.ofNat 64 0x80020) 16380
  have hch := chunksOf_of_wordsToNat 16380 _ region hR (by rw [hlen]) hreg
  have := mac_pass hc s hpc B ((s.readWords (BitVec.ofNat 64 0x80020) 16380).map BitVec.toNat) h22 hB hB' h18
    h19 (by rw [List.length_map, hR]) (fun i hi => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, ← readWords_getD s 16380 0x80020 i hi,
        List.getD_eq_getElem?_getD]
      cases h : (s.readWords (BitVec.ofNat 64 0x80020) 16380)[i]? with
      | none =>
        exfalso
        rw [List.getElem?_eq_none_iff, hR] at h
        omega
      | some w => rfl)
  rwa [hch] at this
end SigGolfCandidate.T3M.FullCache.MacPass
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 20000
abbrev PRIV : Nat := 0x20000
abbrev KEYS : Nat := 0x70000
abbrev REGION : Nat := 0x80020
abbrev REGIONEND : Nat := 0xA0000
def macImage (sg : Bool) : Image := if sg then Images.signImage else Images.keygenImage
def macBase (sg : Bool) : Nat := if sg then 1227 else 334
def macOut (sg : Bool) : Nat := if sg then 0x203E0 else 0x80000
def macSeg_0 : List (BitVec 32) := [134711,921107,3767,0x80e8e93,963331,7221283,9351939,7222307,17740547,40775715,26129155,40776739,34486307,34487331,4919,0xe0130313,7223331,932899,132407,328979,67110291,460343,394771]
theorem macAt_0 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 0)) (macSeg_0) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 334)
      (post := Images.keygenCode.drop 357) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1227) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_0 := symRun { noAlias := true } (macSeg_0) (pcOf 334) 100
sym_block macBlkS_0 := symRun { noAlias := true } (macSeg_0) (pcOf 1227) 100
def macSeg_23 : List (BitVec 32) := [115]
theorem macAt_23 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 23)) (macSeg_23) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 357)
      (post := Images.keygenCode.drop 358) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1250) (by decide +kernel) (by decide +kernel)
def macSeg_24 : List (BitVec 32) := [1049363,33755923,7224355,460343,33949203]
theorem macAt_24 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 24)) (macSeg_24) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 358)
      (post := Images.keygenCode.drop 363) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1251) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_24 := symRun { noAlias := true } (macSeg_24) (pcOf 358) 100
sym_block macBlkS_24 := symRun { noAlias := true } (macSeg_24) (pcOf 1251) 100
def macSeg_29 : List (BitVec 32) := [115]
theorem macAt_29 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 29)) (macSeg_29) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 363)
      (post := Images.keygenCode.drop 364) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1256) (by decide +kernel) (by decide +kernel)
def macSeg_30 (sg : Bool) : List (BitVec 32) := if sg then [0xfff00913, 0x00395913, 0x000a09b7, 0x00098993, 0x00070b37, 0x000b0b13, 0x00020cb7, 0x3e0c8c93] else [0xfff00913, 0x00395913, 0x000a09b7, 0x00098993, 0x00070b37, 0x000b0b13, 0x00080cb7, 0x000c8c93]
theorem macAt_30 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 30)) (macSeg_30 sg) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 364)
      (post := Images.keygenCode.drop 372) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1257) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_30 := symRun { noAlias := true } (macSeg_30 false) (pcOf 364) 100
sym_block macBlkS_30 := symRun { noAlias := true } (macSeg_30 true) (pcOf 1257) 100
def macSeg_38 : List (BitVec 32) := [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem macSeg_38_pass : macSeg_38 = MacPass.macPassCode := by decide +kernel
theorem macAt_38 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 38)) (macSeg_38) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 372)
      (post := Images.keygenCode.drop 412) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1265) (by decide +kernel) (by decide +kernel)
def macSeg_78 : List (BitVec 32) := [0xecb023,17500947]
theorem macAt_78 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 78)) (macSeg_78) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 412)
      (post := Images.keygenCode.drop 414) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1305) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_78 := symRun { noAlias := true } (macSeg_78) (pcOf 412) 100
sym_block macBlkS_78 := symRun { noAlias := true } (macSeg_78) (pcOf 1305) 100
def macSeg_80 : List (BitVec 32) := [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem macSeg_80_pass : macSeg_80 = MacPass.macPassCode := by decide +kernel
theorem macAt_80 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 80)) (macSeg_80) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 414)
      (post := Images.keygenCode.drop 454) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1307) (by decide +kernel) (by decide +kernel)
def macSeg_120 : List (BitVec 32) := [0xecb423,17500947]
theorem macAt_120 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 120)) (macSeg_120) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 454)
      (post := Images.keygenCode.drop 456) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1347) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_120 := symRun { noAlias := true } (macSeg_120) (pcOf 454) 100
sym_block macBlkS_120 := symRun { noAlias := true } (macSeg_120) (pcOf 1347) 100
def macSeg_122 : List (BitVec 32) := [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem macSeg_122_pass : macSeg_122 = MacPass.macPassCode := by decide +kernel
theorem macAt_122 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 122)) (macSeg_122) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 456)
      (post := Images.keygenCode.drop 496) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1349) (by decide +kernel) (by decide +kernel)
def macSeg_162 : List (BitVec 32) := [0xecb823,17500947]
theorem macAt_162 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 162)) (macSeg_162) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 496)
      (post := Images.keygenCode.drop 498) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1389) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_162 := symRun { noAlias := true } (macSeg_162) (pcOf 496) 100
sym_block macBlkS_162 := symRun { noAlias := true } (macSeg_162) (pcOf 1389) 100
def macSeg_164 : List (BitVec 32) := [736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419]
theorem macSeg_164_pass : macSeg_164 = MacPass.macPassCode := by decide +kernel
theorem macAt_164 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 164)) (macSeg_164) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 498)
      (post := Images.keygenCode.drop 538) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1391) (by decide +kernel) (by decide +kernel)
def macSeg_204 : List (BitVec 32) := [0xecbc23]
theorem macAt_204 (sg : Bool) : CodeAt (macImage sg) (pcOf (macBase sg + 204)) (macSeg_204) := by
  cases sg
  · exact CodeAt.of_append (pre := Images.keygenCode.take 538)
      (post := Images.keygenCode.drop 539) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact codeAt_sign_slice (b := 1431) (by decide +kernel) (by decide +kernel)
sym_block macBlkK_204 := symRun { noAlias := true } (macSeg_204) (pcOf 538) 100
sym_block macBlkS_204 := symRun { noAlias := true } (macSeg_204) (pcOf 1431) 100
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem mac_init (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg)) :
    ∃ t, Steps (macImage sg) s 23 23 t ∧ t.pc = pcOf (macBase sg + 23) ∧
      t.getReg .x28 = BitVec.ofNat 64 PRIV ∧ t.getReg .x10 = BitVec.ofNat 64 PRIV ∧
      t.getReg .x11 = 64 ∧ t.getReg .x12 = BitVec.ofNat 64 KEYS ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem 0x80 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+8)) = s.getMem 0x88 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = 3585 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+32)) = s.getMem 0x90 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+40)) = s.getMem 0x98 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+48)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+56)) = 0 ∧
      RegsExcept s t [.x6,.x10,.x11,.x12,.x28,.x29] ∧
      Frame s t (fun A => PRIV ≤ A ∧ A < PRIV+64) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_0 (macAt_0 false) s hpc (by simp [macBlkK_0.res, rv_simp]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkK_0.res, macBase, PRIV, KEYS, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_0.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkK_0.res]
      t3n []
      repeat rw [if_neg (by omega)]
  · refine ⟨_, symRun_sound macBlkS_0 (macAt_0 true) s hpc (by simp [macBlkS_0.res, rv_simp]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkS_0.res, macBase, PRIV, KEYS, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_0.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkS_0.res]
      t3n []
      repeat rw [if_neg (by omega)]
theorem mac_next (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg+24))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 PRIV) :
    ∃ t, Steps (macImage sg) s 5 5 t ∧ t.pc = pcOf (macBase sg+29) ∧
      t.getReg .x12 = BitVec.ofNat 64 (KEYS+32) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (2^32) ∧
      RegsExcept s t [.x6,.x12] ∧ Frame s t (fun A => A = PRIV+24) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_24 (macAt_24 false) s hpc
      (by simp only [macBlkK_24.res]; t3n [h28, PRIV]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
    · simp [macBlkK_24.res, macBase, rv_simp]
    · simp [macBlkK_24.res, KEYS, rv_simp]
    · simp only [Result.toState_getMem, macBlkK_24.res]; t3n [h28, PRIV]
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_24.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkK_24.res]
      t3n [h28, PRIV]
      rw [if_neg (by omega)]
  · refine ⟨_, symRun_sound macBlkS_24 (macAt_24 true) s hpc
      (by simp only [macBlkS_24.res]; t3n [h28, PRIV]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
    · simp [macBlkS_24.res, macBase, rv_simp]
    · simp [macBlkS_24.res, KEYS, rv_simp]
    · simp only [Result.toState_getMem, macBlkS_24.res]; t3n [h28, PRIV]
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_24.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkS_24.res]
      t3n [h28, PRIV]
      rw [if_neg (by omega)]
theorem mac_lanes_init (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg+30)) :
    ∃ t, Steps (macImage sg) s 8 8 t ∧ t.pc = pcOf (macBase sg+38) ∧
      t.getReg .x18 = BitVec.ofNat 64 (2^61-1) ∧
      t.getReg .x19 = BitVec.ofNat 64 REGIONEND ∧
      t.getReg .x22 = BitVec.ofNat 64 KEYS ∧ t.getReg .x25 = BitVec.ofNat 64 (macOut sg) ∧
      RegsExcept s t [.x18,.x19,.x22,.x25] ∧ Frame s t (fun _ => False) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_30 (macAt_30 false) s hpc
      (by simp [macBlkK_30.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkK_30.res, macBase, macOut, KEYS, REGIONEND, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_30.res, rv_simp] <;> rfl
    · intro A _ _; simp [macBlkK_30.res, rv_simp]
  · refine ⟨_, symRun_sound macBlkS_30 (macAt_30 true) s hpc
      (by simp [macBlkS_30.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkS_30.res, macBase, macOut, KEYS, REGIONEND, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_30.res, rv_simp] <;> rfl
    · intro A _ _; simp [macBlkS_30.res, rv_simp]
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def laneEnd (j : Fin 4) : Nat := if j.val < 3 then 80+42*j.val else 205
theorem mac_pass_at (sg : Bool) (j : Fin 4) :
    CodeAt (macImage sg) (pcOf (macBase sg+38+42*j.val)) MacPass.macPassCode := by
  fin_cases j
  · have h := macAt_38 sg
    rw [macSeg_38_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_80 sg
    rw [macSeg_80_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_122 sg
    rw [macSeg_122_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_164 sg
    rw [macSeg_164_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
theorem mac_store (sg : Bool) (j : Fin 4) (s : MachineState)
    (hpc : s.pc = pcOf (macBase sg+78+42*j.val))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (macOut sg)) :
    ∃ t, Steps (macImage sg) s (if j.val < 3 then 2 else 1) (if j.val < 3 then 2 else 1) t ∧
      t.pc = pcOf (macBase sg+laneEnd j) ∧
      t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = s.getReg .x14 ∧
      t.getReg .x22 = (if j.val < 3 then s.getReg .x22+16 else s.getReg .x22) ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun A => A = macOut sg+8*j.val) := by
  cases sg
  · fin_cases j
    · refine ⟨_, symRun_sound macBlkK_78 (macAt_78 false) s hpc
        (by simp only [macBlkK_78.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_78.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_78.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_78.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_78.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_78.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_120 (macAt_120 false) s hpc
        (by simp only [macBlkK_120.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_120.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_120.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_120.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_120.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_120.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_162 (macAt_162 false) s hpc
        (by simp only [macBlkK_162.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_162.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_162.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_162.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_162.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_162.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_204 (macAt_204 false) s hpc
        (by simp only [macBlkK_204.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_204.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_204.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_204.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_204.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_204.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
  · fin_cases j
    · refine ⟨_, symRun_sound macBlkS_78 (macAt_78 true) s hpc
        (by simp only [macBlkS_78.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_78.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_78.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_78.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_78.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_78.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_120 (macAt_120 true) s hpc
        (by simp only [macBlkS_120.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_120.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_120.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_120.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_120.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_120.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_162 (macAt_162 true) s hpc
        (by simp only [macBlkS_162.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_162.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_162.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_162.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_162.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_162.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_204 (macAt_204 true) s hpc
        (by simp only [macBlkS_204.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_204.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_204.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_204.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_204.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_204.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
end SigGolfCandidate.T3M.FullCache
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)
set_option maxRecDepth 20000
theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
def laneWord (s : MachineState) (j : Fin 4) (region : List UInt8) : Word :=
  BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 (KEYS+16*j.val))).toNat % 2^61) (chunks32 region)) +
    s.getMem (BitVec.ofNat 64 (KEYS+16*j.val+8))
def laneRegs : List Reg := [.x13,.x14,.x15,.x16,.x17,.x22,.x23,.x24]
theorem one_lane (sg : Bool) (j : Fin 4) (s : MachineState) (region : List UInt8)
    (hpc : s.pc = pcOf (macBase sg+38+42*j.val))
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2^61-1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 REGIONEND)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (KEYS+16*j.val))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (macOut sg))
    (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 REGION) 16380) = T3.readLE region) :
    ∃ t, Steps (macImage sg) s (425894+(if j.val<3 then 2 else 1))
        (622454+(if j.val<3 then 2 else 1)) t ∧
      t.pc = pcOf (macBase sg+laneEnd j) ∧
      t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = laneWord s j region ∧
      t.getReg .x22 = (if j.val<3 then BitVec.ofNat 64 (KEYS+16*(j.val+1)) else s.getReg .x22) ∧
      RegsExcept s t laneRegs ∧ Frame s t (fun A => A = macOut sg+8*j.val) := by
  have hj := j.isLt
  obtain ⟨u,hu,upc,u14,ur,um⟩ := MacPass.mac_pass_region (mac_pass_at sg j) s hpc
    (KEYS+16*j.val) region h22 (by simp [KEYS]; omega) (by simp [KEYS]; omega)
    h18 h19 hlen hreg
  have upc' : u.pc = pcOf (macBase sg+78+42*j.val) := by
    rw [upc]; unfold pcOf
    change BitVec.ofNat 64 (4096+4*(macBase sg+38+42*j.val)) + BitVec.ofNat 64 160 = _
    rw [ofNat_add_ofNat]; exact congrArg (BitVec.ofNat 64) (by omega)
  have ur25 : u.getReg .x25 = BitVec.ofNat 64 (macOut sg) := by
    rw [ur .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h25]
  obtain ⟨t,ht,tpc,tm,t22,tr,tf⟩ := mac_store sg j u upc' ur25
  refine ⟨t,hu.trans ht,tpc,?_,?_,?_,?_⟩
  · rw [tm,u14]; rfl
  · rw [t22,ur .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    split_ifs
    · rw [h22]
      change BitVec.ofNat 64 (KEYS+16*j.val) + BitVec.ofNat 64 16 = _
      rw [ofNat_add_ofNat]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · rfl
  · intro r hr
    have hr' : r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by simpa [laneRegs] using hr
    rw [tr.get (by simpa using hr'.2.2.2.2.2.1)]
    exact ur r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2.1 hr'.2.2.2.2.2.2.1 hr'.2.2.2.2.2.2.2
  · intro A hA hn; rw [tf.get hA hn,um]
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
set_option maxRecDepth 20000
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def OutW (sg : Bool) (A : Nat) : Prop := macOut sg ≤ A ∧ A < macOut sg+32
theorem lane_frame_out {s t : MachineState} {sg : Bool} {j : Fin 4}
    (h : Frame s t (fun A => A = macOut sg+8*j.val)) : Frame s t (OutW sg) :=
  h.mono (fun A _ ha => by subst A; have := j.isLt; unfold OutW; omega)
theorem out_region {s t : MachineState} {sg : Bool} (h : Frame s t (OutW sg)) :
    t.readWords (BitVec.ofNat 64 REGION) 16380 = s.readWords (BitVec.ofNat 64 REGION) 16380 := by
  apply frame_readWords h REGION 16380 (by decide)
  intro i hi
  cases sg <;> simp only [OutW, macOut, REGION, Bool.false_eq_true, if_false, if_true] <;> omega
theorem out_laneWord {s t : MachineState} {sg : Bool} (h : Frame s t (OutW sg))
    (j : Fin 4) (region : List UInt8) : laneWord t j region = laneWord s j region := by
  have hj := j.isLt
  unfold laneWord
  rw [h.get (by simp [KEYS]; omega) (by cases sg <;> simp [OutW,macOut,KEYS] <;> omega),
    h.get (by simp [KEYS]; omega) (by cases sg <;> simp [OutW,macOut,KEYS] <;> omega)]
theorem mac_pure (sg : Bool) (s : MachineState) (region : List UInt8)
    (hpc : s.pc = pcOf (macBase sg+30)) (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 REGION) 16380) = T3.readLE region) :
    ∃ t, Steps (macImage sg) s 1703591 2489831 t ∧ t.pc = pcOf (macBase sg+205) ∧
      (∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = laneWord s j region) ∧
      t.getReg .x5 = s.getReg .x5 ∧ Frame s t (OutW sg) := by
  obtain ⟨u0,st0,pc0,m18,m19,m22,m25,r0,f0⟩ := mac_lanes_init sg s hpc
  have F0 : Frame s u0 (OutW sg) := f0.mono (fun _ _ h => h.elim)
  obtain ⟨u1,st1,pc1,word1,next1,r1,f1⟩ := one_lane sg 0 u0 region
    (by simpa using pc0) m18 m19 (by simpa using m22) m25 hlen (by rw [out_region F0]; exact hreg)
  have F1 : Frame s u1 (OutW sg) :=
    (F0.trans (lane_frame_out f1)).mono (fun _ _ h => h.elim id id)
  have W1 : u1.getMem (BitVec.ofNat 64 (macOut sg+8*(0 : Fin 4).val)) = laneWord s 0 region :=
    word1.trans (out_laneWord F0 0 region)
  obtain ⟨u2,st2,pc2,word2,next2,r2,f2⟩ := one_lane sg 1 u1 region
    (by simpa [laneEnd,Nat.add_assoc] using pc1)
    (by rw [r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next1)
    (by rw [r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F1]; exact hreg)
  have F2 : Frame s u2 (OutW sg) :=
    (F1.trans (lane_frame_out f2)).mono (fun _ _ h => h.elim id id)
  have W2 : u2.getMem (BitVec.ofNat 64 (macOut sg+8*(1 : Fin 4).val)) = laneWord s 1 region :=
    word2.trans (out_laneWord F1 1 region)
  obtain ⟨u3,st3,pc3,word3,next3,r3,f3⟩ := one_lane sg 2 u2 region
    (by simpa [laneEnd,Nat.add_assoc] using pc2)
    (by rw [r2.get (by decide : Reg.x18 ∉ laneRegs),r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r2.get (by decide : Reg.x19 ∉ laneRegs),r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next2)
    (by rw [r2.get (by decide : Reg.x25 ∉ laneRegs),r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F2]; exact hreg)
  have F3 : Frame s u3 (OutW sg) :=
    (F2.trans (lane_frame_out f3)).mono (fun _ _ h => h.elim id id)
  have W3 : u3.getMem (BitVec.ofNat 64 (macOut sg+8*(2 : Fin 4).val)) = laneWord s 2 region :=
    word3.trans (out_laneWord F2 2 region)
  obtain ⟨u4,st4,pc4,word4,next4,r4,f4⟩ := one_lane sg 3 u3 region
    (by simpa [laneEnd,Nat.add_assoc] using pc3)
    (by rw [r3.get (by decide : Reg.x18 ∉ laneRegs),r2.get (by decide : Reg.x18 ∉ laneRegs),r1.get (by decide : Reg.x18 ∉ laneRegs)]; exact m18)
    (by rw [r3.get (by decide : Reg.x19 ∉ laneRegs),r2.get (by decide : Reg.x19 ∉ laneRegs),r1.get (by decide : Reg.x19 ∉ laneRegs)]; exact m19)
    (by simpa using next3)
    (by rw [r3.get (by decide : Reg.x25 ∉ laneRegs),r2.get (by decide : Reg.x25 ∉ laneRegs),r1.get (by decide : Reg.x25 ∉ laneRegs)]; exact m25)
    hlen (by rw [out_region F3]; exact hreg)
  have F4 : Frame s u4 (OutW sg) :=
    (F3.trans (lane_frame_out f4)).mono (fun _ _ h => h.elim id id)
  have W4 : u4.getMem (BitVec.ofNat 64 (macOut sg+8*(3 : Fin 4).val)) = laneWord s 3 region :=
    word4.trans (out_laneWord F3 3 region)
  refine ⟨u4,(st0.trans (st1.trans (st2.trans (st3.trans st4)))).of_eq (by decide) (by decide),
    ?_,?_,?_,F4⟩
  · simpa [laneEnd] using pc4
  · intro j; fin_cases j
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega),f3.get (by cases sg <;> decide) (by simp <;> omega),f2.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W1
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega),f3.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W2
    · rw [f4.get (by cases sg <;> decide) (by simp <;> omega)]
      exact W3
    · exact W4
  · rw [r4.get (by decide : Reg.x5 ∉ laneRegs),r3.get (by decide : Reg.x5 ∉ laneRegs),r2.get (by decide : Reg.x5 ∉ laneRegs),r1.get (by decide : Reg.x5 ∉ laneRegs),r0.get (by decide)]
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity
open SiggolfT3Mac4
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
def KeysAt (s : MachineState) (a b : BitVec 256) : Prop :=
  ∀ j : Fin 8, s.getMem (BitVec.ofNat 64 (KEYS+8*j.val)) =
    if j.val < 4 then a.extractLsb' (64*j.val) 64 else b.extractLsb' (64*(j.val-4)) 64
def keyPair (a b : BitVec 256) : MacKey := fun i => if i = 0 then a else b
theorem extract64_mod61 (a : BitVec 256) (off : Nat) :
    (a.extractLsb' off 64).toNat % 2^61 = (a.extractLsb' off 61).toNat := by
  simp only [BitVec.extractLsb'_toNat]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
theorem laneWord_eq_tag (s : MachineState) (a b : BitVec 256) (region : List UInt8)
    (hk : KeysAt s a b) (j : Fin 4) : laneWord s j region = macTag (keyPair a b) region j := by
  have h0 := hk 0; have h1 := hk 1; have h2 := hk 2; have h3 := hk 3
  have h4 := hk 4; have h5 := hk 5; have h6 := hk 6; have h7 := hk 7
  change s.getMem 458752#64 = a.extractLsb' 0 64 at h0
  change s.getMem 458760#64 = a.extractLsb' 64 64 at h1
  change s.getMem 458768#64 = a.extractLsb' 128 64 at h2
  change s.getMem 458776#64 = a.extractLsb' 192 64 at h3
  change s.getMem 458784#64 = b.extractLsb' 0 64 at h4
  change s.getMem 458792#64 = b.extractLsb' 64 64 at h5
  change s.getMem 458800#64 = b.extractLsb' 128 64 at h6
  change s.getMem 458808#64 = b.extractLsb' 192 64 at h7
  fin_cases j <;>
    simp [laneWord, macTag, macKeyWord, macPadWord, keyPair, KEYS, h0,h1,h2,h3,h4,h5,h6,h7,
      extract64_mod61]
theorem encodeTag_word (tag : MacTag) (j : Fin 4) :
    (encodeTag tag).extractLsb' (64*j.val) 64 = tag j := by
  obtain ⟨h0,h1,h2,h3⟩ := extract_answerOfWords (tag 0) (tag 1) (tag 2) (tag 3)
  fin_cases j <;> simp only [encodeTag] <;> assumption
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open OracleComp OracleSpec
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def SkAt (s : MachineState) (sk : BitVec 256) : Prop :=
  ∀ j : Fin 4, s.getMem (BitVec.ofNat 64 (0x80+8*j.val)) = sk.extractLsb' (64*j.val) 64
def PrivAt (s : MachineState) (sk : BitVec 256) (i : Fin 2) : Prop :=
  ∀ j : Fin 8, s.getMem (BitVec.ofNat 64 (PRIV+8*j.val)) =
    [sk.extractLsb' 0 64,sk.extractLsb' 64 64,3585,BitVec.ofNat 64 (i.val*2^32),
      sk.extractLsb' 128 64,sk.extractLsb' 192 64,0,0].getD j.val 0
theorem priv_query (s : MachineState) (sk : BitVec 256) (i : Fin 2) (h : PrivAt s sk i)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 PRIV) (h11 : s.getReg .x11 = 64) :
    hashInput s = toQ (T3.privateInput sk (.inl (T3.header 14 0 0 0 i.val))) := by
  apply hashInput_toQ s _ 0 PRIV (privateInput_tweak_length _ _) h10 (by decide) (by decide)
    h11 (by decide)
  rw [readWords_eight,wordsOf_privateInput_tweak]
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  change s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64 at h0
  change s.getMem (BitVec.ofNat 64 (PRIV+8)) = sk.extractLsb' 64 64 at h1
  change s.getMem (BitVec.ofNat 64 (PRIV+16)) = 3585 at h2
  change s.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (i.val*2^32) at h3
  change s.getMem (BitVec.ofNat 64 (PRIV+32)) = sk.extractLsb' 128 64 at h4
  change s.getMem (BitVec.ofNat 64 (PRIV+40)) = sk.extractLsb' 192 64 at h5
  change s.getMem (BitVec.ofNat 64 (PRIV+48)) = 0 at h6
  change s.getMem (BitVec.ofNat 64 (PRIV+56)) = 0 at h7
  rw [h0,h1,h2,h3,h4,h5,h6,h7]
  fin_cases i <;> rfl
theorem priv_next {s t : MachineState} {sk : BitVec 256} {a : BitVec 256}
    (hp : PrivAt s sk 0) (h12 : s.getReg .x12 = BitVec.ofNat 64 KEYS)
    (hfr : Frame (writeHash s a) t (fun A => A = PRIV+24))
    (h24 : t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (2^32)) : PrivAt t sk 1 := by
  intro j
  have hf := Frame.writeHash s a KEYS h12 (by decide)
  have hj := j.isLt
  by_cases he : j.val = 3
  · have ej : j = 3 := Fin.ext he
    subst j
    exact h24
  · rw [hfr.get (by simp [PRIV]; omega) (by simp [PRIV]; omega),
      hf.get (by simp [PRIV]; omega) (by simp [PRIV,KEYS]; omega),hp j]
    fin_cases j <;> first | rfl | exact False.elim (he rfl)
theorem keys_after {s t : MachineState} (a b : BitVec 256)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 KEYS)
    (hfr : Frame (writeHash s a) t (fun A => A = PRIV+24))
    (ht12 : t.getReg .x12 = BitVec.ofNat 64 (KEYS+32)) : KeysAt (writeHash t b) a b := by
  intro j
  have hj := j.isLt
  have hA : KEYS+8*j.val < 2^64 := by simp [KEYS]; omega
  rw [getMem_writeHash t b (KEYS+32) (KEYS+8*j.val) ht12 (by decide) hA]
  fin_cases j
  all_goals simp only [KEYS, Nat.reduceMul, Nat.reduceAdd, Fin.val_zero, Fin.val_one, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one, Nat.reduceEqDiff, if_true, if_false, Nat.reduceLT, Nat.reduceSub]
  all_goals first
    | rfl
    | (rw [hfr.get (by decide) (by decide), getMem_writeHash s a KEYS _ h12 (by decide) (by decide)]
       simp [KEYS])
end SigGolfCandidate.T3M.FullCache
end
section
namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open OracleComp OracleSpec
open SphincsSecurity (bytesLE)
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def MacW (sg : Bool) (A : Nat) : Prop :=
  (PRIV ≤ A ∧ A < PRIV+64) ∨ (KEYS ≤ A ∧ A < KEYS+64) ∨ OutW sg A
structure MacDone (sg : Bool) (s : MachineState) (tag : T3.HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf (macBase sg+205)
  x5 : t.getReg .x5 = 0
  words : t.readWords (BitVec.ofNat 64 (macOut sg)) 4 = wordsOf (bytesLE 32 tag)
  frame : Frame s t (MacW sg)
theorem mac_tsim (sg : Bool) (sk : BitVec 256) (region : T3.Region) (s : MachineState)
    (hpc : s.pc = pcOf (macBase sg)) (h5 : s.getReg .x5 = 0) (hsk : SkAt s sk)
    (hreg : s.readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn region)) :
    TSim (macImage sg) sk s 1703621 2489875 2 2 (T3.privateMac region) (MacDone sg s) := by
  obtain ⟨u0,st0,pc0,x28,x10,x11,x12,m0,m8,m16,m24,m32,m40,m48,m56,r0,f0⟩ := mac_init sg s hpc
  have p0 : PrivAt u0 sk 0 := by
    intro j; fin_cases j
    · exact m0.trans (hsk 0)
    · exact m8.trans (hsk 1)
    · exact m16
    · exact m24
    · exact m32.trans (hsk 2)
    · exact m40.trans (hsk 3)
    · exact m48
    · exact m56
  have z0 : u0.getReg .x5 = 0 := by rw [r0.get (by decide),h5]
  have v0 : hashArgumentsValid u0 = true := hashArgs_const u0 PRIV 64 KEYS x10 x11 x12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q0 := priv_query u0 sk 0 p0 x10 x11
  have fetch0 : fetch (macImage sg) u0 = some (.base .ECALL) := (macAt_23 sg).fetch u0 pc0 |>.trans rfl
  unfold T3.privateMac T3.privateMacKey
  simp only [bind_assoc,pure_bind]
  refine (TSim.steps st0 (TSim.privateTweak_bind (k := 1703597) (c := 2489844) (n := 1) (b := 1) fetch0 z0 v0 q0 (fun a => ?_))).of_eq
    rfl (by decide) (by decide) (by decide) (by decide)
  have pa : (writeHash u0 a).pc = pcOf (macBase sg+24) := by
    rw [pc_writeHash,pc0,pcOf_add4]
  obtain ⟨u1,st1,pc1,y12,n24,r1,f1⟩ := mac_next sg (writeHash u0 a) pa (by simpa using x28)
  have p1 := priv_next p0 x12 f1 n24
  have y10 : u1.getReg .x10 = BitVec.ofNat 64 PRIV := by rw [r1.get (by decide),getReg_writeHash,x10]
  have y11 : u1.getReg .x11 = 64 := by rw [r1.get (by decide),getReg_writeHash,x11]
  have z1 : u1.getReg .x5 = 0 := by rw [r1.get (by decide),getReg_writeHash,z0]
  have v1 : hashArgumentsValid u1 = true := hashArgs_const u1 PRIV 64 (KEYS+32) y10 y11 y12
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have q1 := priv_query u1 sk 1 p1 y10 y11
  have fetch1 : fetch (macImage sg) u1 = some (.base .ECALL) := (macAt_29 sg).fetch u1 pc1 |>.trans rfl
  refine TSim.steps st1 (TSim.privateTweak_bind (k := 1703591) (c := 2489831) (n := 0) (b := 0) fetch1 z1 v1 q1 (fun b => ?_))
  have F0 : Frame s (writeHash u1 b) (MacW sg) := by
    have ha := Frame.writeHash u0 a KEYS x12 (by decide)
    have hb := Frame.writeHash u1 b (KEYS+32) y12 (by decide)
    apply (((f0.trans ha).trans f1).trans hb).mono
    intro A hA h
    unfold MacW
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · left; subst A; simp [PRIV]
    · exact Or.inr (Or.inl (by omega))
  have preg : (writeHash u1 b).readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn region) := by
    rw [frame_readWords F0 REGION 16380 (by decide) (by
      intro i hi; cases sg <;> simp only [MacW,OutW,macOut,PRIV,KEYS,REGION,Bool.false_eq_true,if_false,if_true] <;> omega)]
    exact hreg
  have pb : (writeHash u1 b).pc = pcOf (macBase sg+30) := by
    rw [pc_writeHash,pc1,pcOf_add4]
  obtain ⟨t,st,pc,tagwords,zt,ft⟩ := mac_pure sg (writeHash u1 b) (List.ofFn region) pb
    (by rw [List.length_ofFn]) (by rw [preg,wordsToNat_wordsOf 16380 _ (by rw [List.length_ofFn])])
  have hk := keys_after a b x12 f1 y12
  refine TSim.pure_steps st ?_
  refine ⟨pc,?_,?_,?_⟩
  · rw [zt,getReg_writeHash,z1]
  · rw [show (4 : Nat) = 2+2 from rfl,readWords_add,readWords_two,readWords_two,wordsOf_bytesLE32]
    have H : ∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) =
        (SiggolfT3Mac4.encodeTag (SiggolfT3Mac4.macTag (keyPair a b) (List.ofFn region))).extractLsb' (64*j.val) 64 := by
      intro j
      rw [tagwords j,laneWord_eq_tag _ _ _ _ hk j,encodeTag_word]
    change [t.getMem (BitVec.ofNat 64 (macOut sg+8*(0:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(1:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(2:Fin 4).val)),
      t.getMem (BitVec.ofNat 64 (macOut sg+8*(3:Fin 4).val))] = _
    rw [H 0,H 1,H 2,H 3]
    rfl
  · exact (F0.trans ft).mono (fun A hA h => h.elim id (fun h => Or.inr (Or.inr h)))
end SigGolfCandidate.T3M.FullCache
end
end
