import SigGolfCandidate.T3M_Sign_Basic
import SigGolfCandidate.T3M_Search_ProducerData

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Cache Region cacheBytes readLE)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (TOP_DATA TableOK signData_length signData_table)
theorem readWords_of_get (t : MachineState) (A : Nat) :
    ∀ (m : Nat) (l : List Word), l.length = m →
      (∀ j < m, t.getMem (BitVec.ofNat 64 (A + 8 * j)) = l.getD j 0) → t.readWords (BitVec.ofNat 64 A) m = l
  | 0, l, hl, _ => by rw [List.length_eq_zero_iff] at hl; subst hl; rfl
  | m + 1, l, hl, h => by
    obtain ⟨l', d, rfl⟩ : ∃ l' d, l = l' ++ [d] := ⟨l.dropLast, l.getLast (by
      intro he; subst he; simp at hl), (List.dropLast_append_getLast _).symm⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    rw [readWords_add, readWords_of_get t A m l' hl (fun j hj => by
      rw [h j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hl ▸ hj)]),
      readWords_one, h m (by omega)]
    simp [List.getD_eq_getElem?_getD, hl]
theorem extractLsb'_ofNat_readLE (m : Nat) (l : List UInt8) (hl : l.length = 8 * m) (j : Nat) (hj : j < m) :
    (BitVec.ofNat (8 * (8 * m)) (readLE l)).extractLsb' (64 * j) 64 = (wordsOf l).getD j 0 := by
  rw [wordsOf_eq_range m l hl]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  have hlt := readLE_lt l
  rw [hl, ← two_pow_eight_mul] at hlt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
/-- Sign data base (`dataBase` of the 86,144-byte data: the 128-byte `Zt` table first). -/
def SIGN_DATA : Nat := 16691072
def sdata : MachineState :=
  ({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 SIGN_DATA) Images.signData
theorem sdata_getMem (A : Nat) (hA : A < 2 ^ 64) :
    sdata.getMem (BitVec.ofNat 64 A) =
      if SIGN_DATA ≤ A ∧ A < SIGN_DATA + 86144 ∧ (A - SIGN_DATA) % 8 = 0 then
        bytesToWordLE ((Images.signData.drop (A - SIGN_DATA)).take 8) else 0 := by
  unfold sdata
  rw [getMem_writeBytesAsWords _ _ SIGN_DATA A (by rw [signData_length]; decide) hA, signData_length]
  rfl
theorem sdata_zero (A : Nat) (hA : A < SIGN_DATA) : sdata.getMem (BitVec.ofNat 64 A) = 0 := by
  rw [sdata_getMem A (by unfold SIGN_DATA at hA; omega), if_neg (by omega)]
def sinit (sk : SecretKey) (cache : Bytes 131072) (m : Message) : MachineState :=
  (((sdata.writeBytesAsWords
    (BitVec.ofNat 64 0x80) (bytes sk)).writeBytesAsWords (BitVec.ofNat 64 0x80000) (bytes cache)).writeBytesAsWords
    (BitVec.ofNat 64 0x6620) (bytes m)).setReg .x2 (BitVec.ofNat 64 SIGN_DATA)
theorem sinit_pc (sk : SecretKey) (cache : Bytes 131072) (m : Message) : (sinit sk cache m).pc = pcOf 0 := by
  unfold sinit
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords]
  simp [sdata, MachineState.pc_writeBytesAsWords]
theorem bytes_length' {n : Nat} (x : Bytes n) : (bytes x).length = n := by simp [bytes]
theorem sinit_getMem (sk : SecretKey) (cache : Bytes 131072) (m : Message) (A : Nat) (hA : A < 2 ^ 64) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 A) =
      if 0x6620 ≤ A ∧ A < 0x6640 ∧ (A - 0x6620) % 8 = 0 then bytesToWordLE (((bytes m).drop (A - 0x6620)).take 8)
      else if 0x80000 ≤ A ∧ A < 0xA0000 ∧ (A - 0x80000) % 8 = 0 then
        bytesToWordLE (((bytes cache).drop (A - 0x80000)).take 8)
      else if 0x80 ≤ A ∧ A < 0xA0 ∧ (A - 0x80) % 8 = 0 then bytesToWordLE (((bytes sk).drop (A - 0x80)).take 8)
      else sdata.getMem (BitVec.ofNat 64 A) := by
  unfold sinit
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x6620 A (by rw [bytes_length']; decide) hA,
    getMem_writeBytesAsWords _ _ 0x80000 A (by rw [bytes_length']; decide) hA,
    getMem_writeBytesAsWords _ _ 0x80 A (by rw [bytes_length']; decide) hA, bytes_length', bytes_length',
    bytes_length']
theorem sinit_sk (sk : SecretKey) (cache : Bytes 131072) (m : Message) (j : Nat) (hj : j < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (SK + 8 * j)) = sk.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_neg (by sg_omega), if_neg (by sg_omega), if_pos (by sg_omega),
    show SK + 8 * j - 0x80 = 8 * j by sg_omega, bytesToWordLE_bytes sk j (by omega)]
theorem sinit_msg (sk : SecretKey) (cache : Bytes 131072) (m : Message) (j : Nat) (hj : j < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (MSG + 8 * j)) = m.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_pos (by sg_omega), show MSG + 8 * j - 0x6620 = 8 * j by sg_omega,
    bytesToWordLE_bytes m j (by omega)]
theorem sinit_cache (sk : SecretKey) (cache : Bytes 131072) (m : Message) (j : Nat) (hj : j < 16384) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * j)) = cache.extractLsb' (64 * j) 64 := by
  rw [sinit_getMem _ _ _ _ (by sg_omega), if_neg (by sg_omega), if_pos (by sg_omega),
    show CACHE + 8 * j - 0x80000 = 8 * j by sg_omega, bytesToWordLE_bytes cache j (by omega)]
theorem sinit_zero (sk : SecretKey) (cache : Bytes 131072) (m : Message) (A : Nat) (hA : A < SIGN_DATA)
    (h : A < 0x80 ∨ (0xA0 ≤ A ∧ A < 0x6620) ∨ (0x6640 ≤ A ∧ A < 0x80000) ∨ 0xA0000 ≤ A) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [sinit_getMem _ _ _ _ (by unfold SIGN_DATA at hA; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), sdata_zero A hA]
theorem sinit_cacheWords (sk : SecretKey) (cache : Bytes 131072) (m : Message) (j : Nat) (hj : j < 16384) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * j)) =
      (wordsOf (cacheBytes (cacheDec cache))).getD j 0 := by
  rw [sinit_cache _ _ _ j hj]
  conv_lhs => rw [← cacheB_cacheDec cache]
  exact extractLsb'_ofNat_readLE 16384 _ (cacheBytes_length _) j hj
theorem wordsOf_cacheBytes (c : Cache) :
    wordsOf (cacheBytes c) = [c.tag.extractLsb' 0 64, c.tag.extractLsb' 64 64, c.tag.extractLsb' 128 64,
      c.tag.extractLsb' 192 64] ++ wordsOf (List.ofFn c.region) := by
  rw [cacheBytes, wordsOf_append (bytesLE 32 c.tag) (List.ofFn c.region) (by rw [bytesLE_length]),
    wordsOf_bytesLE32]
theorem length_wordsOf_region (r : Region) : (wordsOf (List.ofFn r)).length = 16380 := by
  rw [wordsOf_eq_range 16380 _ (by rw [List.length_ofFn]), List.length_map, List.length_range]
theorem sinit_tag (sk : SecretKey) (cache : Bytes 131072) (m : Message) (k : Nat) (hk : k < 4) :
    (sinit sk cache m).getMem (BitVec.ofNat 64 (CACHE + 8 * k)) = (cacheDec cache).tag.extractLsb' (64 * k) 64 := by
  rw [sinit_cacheWords _ _ _ k (by omega), wordsOf_cacheBytes]
  interval_cases k <;> rfl
theorem sinit_region (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (sinit sk cache m).readWords (BitVec.ofNat 64 REGION) 16380 = wordsOf (List.ofFn (cacheDec cache).region) := by
  refine readWords_of_get _ _ _ _ (length_wordsOf_region _) (fun j hj => ?_)
  rw [show REGION + 8 * j = CACHE + 8 * (4 + j) by sg_omega, sinit_cacheWords _ _ _ _ (by omega),
    wordsOf_cacheBytes, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (show [(cacheDec cache).tag.extractLsb' 0 64, (cacheDec cache).tag.extractLsb' 64 64,
      (cacheDec cache).tag.extractLsb' 128 64, (cacheDec cache).tag.extractLsb' 192 64].length ≤ 4 + j by
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton]; omega)]
  rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton, Nat.add_sub_cancel_left]
/-- Campaign T51: a byte of the top data block (`TOP_DATA + i`, sign data offset 82048 + i) in the initial state. -/
theorem sinit_topByte (sk : SecretKey) (cache : Bytes 131072) (m : Message) (i : Nat) (hi : i < 4096)
    (b : BitVec 8) (hb : Images.signData.getD (82048 + i) 0 = b) :
    (sinit sk cache m).getByte (BitVec.ofNat 64 (TOP_DATA + i)) = b := by
  rw [getByte_eq_word _ _ (by simp only [TOP_DATA]; omega),
    sinit_getMem _ _ _ _ (by simp only [TOP_DATA]; omega),
    if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega),
    sdata_getMem _ (by simp only [TOP_DATA]; omega), if_pos (by simp only [TOP_DATA, SIGN_DATA]; omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (TOP_DATA + i) (show 0 < 8 by decide))]
  have hidx : (TOP_DATA + i) / 8 * 8 - SIGN_DATA + (TOP_DATA + i) % 8 = 82048 + i := by simp only [TOP_DATA, SIGN_DATA]; omega
  rw [hidx]
  rw [List.getD_eq_getElem?_getD] at hb
  exact hb
/-- Campaign T51: only the choice flag byte (TOP_DATA + 631) is read; it is 1 in the initial state. -/
theorem sinit_cf (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    Search.CfFlagOK 1 (sinit sk cache m) :=
  sinit_topByte sk cache m 631 (by omega) _ Search.signData_flag
/-- Campaign T51: the lower reward tables (TOP_DATA + 1024..2047) in the initial state. -/
theorem sinit_reward (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    Search.Reward.LowerTablesOK (sinit sk cache m) := fun i hi hj =>
  sinit_topByte sk cache m i (by omega) _ (Search.signData_lowerReward i hi hj)

/-! ### Campaign T51: the packed top tables (1892 bytes at `0xFFF800 = TOP_DATA + 2048`) as the 473 `lwu` words -/
/-- Checks dword `k` of a byte list against the T51 entries `2k` (low half) and `2k + 1` (high half, `< 473`). -/
def t51Chk : Nat → List (BitVec 8) → Bool
  | k, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      (extractWord32 (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]) 0 ==
        BitVec.ofNat 32 (Search.T51.tEntry (2 * k))) &&
      (decide (473 ≤ 2 * k + 1) || (extractWord32 (bytesToWordLE [b0, b1, b2, b3, b4, b5, b6, b7]) 1 ==
        BitVec.ofNat 32 (Search.T51.tEntry (2 * k + 1)))) &&
      t51Chk (k + 1) rest
  | _, [] => true
  | _, _ => false
set_option maxRecDepth 100000 in
theorem t51_chk : t51Chk 0 ((Images.signLegacyData.drop 2048).take 1896) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t51Slice_length : ((Images.signLegacyData.drop 2048).take 1896).length = 1896 := by decide +kernel
theorem t51Chk_get : ∀ (m k : Nat) (l : List (BitVec 8)), t51Chk k l = true → 8 * m + 8 ≤ l.length →
    extractWord32 (bytesToWordLE ((l.drop (8 * m)).take 8)) 0 = BitVec.ofNat 32 (Search.T51.tEntry (2 * (k + m))) ∧
    (2 * (k + m) + 1 < 473 →
      extractWord32 (bytesToWordLE ((l.drop (8 * m)).take 8)) 1 = BitVec.ofNat 32 (Search.T51.tEntry (2 * (k + m) + 1)))
  | m, k, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h, hl => by
    simp only [t51Chk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases m with _ | m
    · refine ⟨by simpa using h.1.1, fun hlt => ?_⟩
      rcases h.1.2 with h' | h'
      · simp at hlt; omega
      · simpa using h'
    · have := t51Chk_get m (k + 1) rest h.2 (by simp at hl; omega)
      rw [show 8 * (m + 1) = 8 + 8 * m by omega, ← List.drop_drop]
      simpa [show k + 1 + m = k + (m + 1) by omega] using this
  | m, k, [], _, hl => by simp at hl
  | m, k, [_], _, hl => by simp at hl <;> omega
  | m, k, [_, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _, _], _, hl => by simp at hl <;> omega
  | m, k, [_, _, _, _, _, _, _], _, hl => by simp at hl <;> omega
theorem signData_drop_legacy (n : Nat) : Images.signData.drop (82048 + n) = Images.signLegacyData.drop n := by
  have h1 := Search.signZtData_length
  have h2 := Images.signPrefixData_length
  have e1 : Images.signZtData.length ≤ 82048 + n := by omega
  have e2 : Images.signPrefixData.length ≤ 82048 + n - Images.signZtData.length := by omega
  rw [Images.signData, List.drop_append, List.drop_eq_nil_of_le e1, List.nil_append, List.drop_append,
    List.drop_eq_nil_of_le e2, List.nil_append, h1, h2, show 82048 + n - 128 - 81920 = n by omega]
theorem t51_slice (m : Nat) (hm : 8 * m + 8 ≤ 1896) :
    ((((Images.signLegacyData.drop 2048).take 1896).drop (8 * m)).take 8) =
      (Images.signLegacyData.drop (2048 + 8 * m)).take 8 := by
  rw [List.drop_take, List.drop_drop, List.take_take, show min 8 (1896 - 8 * m) = 8 by omega]
/-- Campaign T51: the packed top tables at `0xFFF800` as the 473 `lwu` words in the initial state. -/
theorem sinit_t51 (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    Search.T51.T51TableW 0xFFF800 (sinit sk cache m) := by
  intro f hf
  have hlt : 0xFFF800 + 4 * f < 2 ^ 64 := by omega
  unfold MachineState.getWord32
  have ha : alignToDword (BitVec.ofNat 64 (0xFFF800 + 4 * f)) = BitVec.ofNat 64 (0xFFF800 + 8 * (f / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt hlt, toNat_ofNat_lt (by omega)]
    omega
  have hb : byteOffset (BitVec.ofNat 64 (0xFFF800 + 4 * f)) / 4 = f % 2 := by
    rw [byteOffset_eq, toNat_ofNat_lt hlt]; omega
  rw [ha, hb, sinit_getMem _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    sdata_getMem _ (by omega), if_pos (by simp only [SIGN_DATA]; omega),
    show 0xFFF800 + 8 * (f / 2) - SIGN_DATA = 82048 + (2048 + 8 * (f / 2)) by simp only [SIGN_DATA]; omega,
    signData_drop_legacy, ← t51_slice (f / 2) (by omega)]
  have hr := t51Chk_get (f / 2) 0 _ t51_chk (by rw [t51Slice_length]; omega)
  rw [Nat.zero_add] at hr
  rcases Nat.mod_two_eq_zero_or_one f with h0 | h1
  · rw [h0, hr.1, show 2 * (f / 2) = f by omega]
  · rw [h1, hr.2 (by omega), show 2 * (f / 2) + 1 = f by omega]
theorem sinit_table (sk : SecretKey) (cache : Bytes 131072) (m : Message) : TableOK (sinit sk cache m) := by
  intro i hi
  rw [getByte_eq_word _ _ (by simp only [TOP_DATA]; omega),
    sinit_getMem _ _ _ _ (by simp only [TOP_DATA]; omega),
    if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega), if_neg (by simp only [TOP_DATA]; omega),
    sdata_getMem _ (by simp only [TOP_DATA]; omega), if_pos (by simp only [TOP_DATA, SIGN_DATA]; omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (TOP_DATA + i) (show 0 < 8 by decide))]
  have hidx : (TOP_DATA + i) / 8 * 8 - SIGN_DATA + (TOP_DATA + i) % 8 = 82048 + i := by simp only [TOP_DATA, SIGN_DATA]; omega
  rw [hidx]
  exact signData_table i hi
theorem sinit_zt (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    Search.ZeroCap.ZtOK 543 (sinit sk cache m) := by
  intro r hr
  simp only [Search.ZeroCap.ZT, show (543:Nat) ≠ 354 by decide, if_false]
  rw [getByte_eq_word _ _ (by omega),
    sinit_getMem _ _ _ _ (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    sdata_getMem _ (by omega), if_pos (by simp only [SIGN_DATA]; omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    if_pos (Nat.mod_lt (16691072 + r) (show 0 < 8 by decide))]
  have hidx : (16691072 + r) / 8 * 8 - SIGN_DATA + (16691072 + r) % 8 = r := by simp only [SIGN_DATA]; omega
  rw [hidx, ← List.getD_eq_getElem?_getD]
  exact Search.signData_zt r hr
end SigGolfCandidate.T3M.Sign
