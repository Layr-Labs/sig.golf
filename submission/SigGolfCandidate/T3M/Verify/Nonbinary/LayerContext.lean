import SigGolfCandidate.T3M.Verify.Nonbinary.LayerPrefix
import SigGolfCandidate.T3M.Verify.LayerSem
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchCtx

section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem prefix_run (a : Nat) (ha : a ∈ aVals) (pc : Word) :
    symRun { noAlias := true } (prefixWordsOf a) pc 200 = some (prefixRes a) := by
  simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem tail_field (v : Digest) : (v.extractLsb' 64 64 >>> 55) = BitVec.ofNat 64 (v.toNat / 2 ^ 119) := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega
def prefixTarget (v : Digest) : Word := BitVec.ofNat 64 (1024 * (v.toNat % 128) + 1056)
theorem prefix_spec (s : MachineState) (v : Digest) (a d p : Nat) (ha : a ∈ aVals)
    (hpc : s.pc = pcOf p) (hcode : CodeAt Verify.image (pcOf p) (prefixWordsOf a))
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d) (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 16 ≤ 0x7000)
    (hv : DigAt s d v) (hra : s.getReg .x1 = BitVec.ofNat 64 TOPBASE)
    (hmask : s.getMem 0xffbff8#64 = 130048#64) (h10 : s.getReg .x10 = BitVec.ofNat 64 a) :
    ∃ t, Steps Verify.image s 8 8 t ∧ t.pc = prefixTarget v ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 64 64 ∧
      t.getReg .x29 = BitVec.ofNat 64 (v.toNat / 2 ^ 119) ∧
      t.getReg .x8 = 12480#64 ∧ t.getReg .x6 = 130048#64 ∧
      RegsExcept s t [.x16,.x17,.x29,.x6,.x8,.x14] ∧ Frame s t (fun _ => False) := by
  have hm : s.getMem (s.getReg .x1 + 18446744073709551608#64) = 130048#64 := by
    rw [hra]; exact hmask
  have h0 : s.getMem (s.getReg .x12) = v.extractLsb' 0 64 := by rw [h12]; exact hv.1
  have h1 : s.getMem (s.getReg .x12 + 8#64) = v.extractLsb' 64 64 := by
    rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hv.2
  have hobl : ∀ o ∈ (prefixRes a).st.obl, o.holds s := by
    intro o ho
    simp [prefixRes, prefixRegs, prefixBase.res] at ho
    rcases ho with rfl | rfl | rfl
    all_goals simp [Oblig.holds, rv_simp, accessValid_iff, MEMORY_BYTES, hra, h12, TOPBASE]
    all_goals omega
  have hal : 14272 ≤ a ∧ a ≤ 14528 := by
    simp only [aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  refine ⟨_, symRun_sound (prefix_run a ha (pcOf p)) hcode s hpc ((Oblig.all_iff _ _).mpr hobl),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, prefixRes, prefixRegs, prefixBase.res, E.eval, BinOp.eval, h0, hm]
    have e1 : (10#64 : Word).toNat % 64 = (BitVec.ofNat 64 10).toNat := by decide +kernel
    have e2 : (18446744073709551614#64 : Word) = ~~~1#64 := by decide +kernel
    have hx : (v.extractLsb' 0 64).toNat % 128 = v.toNat % 128 := by
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
      exact Nat.mod_mod_of_dvd _ (show 128 ∣ 2 ^ 64 by decide +kernel)
    rw [e1, e2, SigGolfCandidate.T3M.Nonbinary.prologue_value, prefixTarget, hx]
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval, BinOp.eval, h0]
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval, BinOp.eval, h1]
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval, BinOp.eval, h1]
    exact tail_field v
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, RegFile.get, RegFile.set, E.eval, BinOp.eval, h10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp only [Result.toState_getReg, prefixRes, prefixRegs, prefixBase.res, RegFile.get, RegFile.set, E.eval, BinOp.eval, hm]
  · intro r hr; cases r <;> simp at hr <;> simp [prefixRes, prefixRegs, prefixBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [prefixRes, prefixRegs, prefixBase.res, rv_simp]
theorem testBit_topMask (i : Nat) : (2 ^ 119 - 1 : Nat).testBit i = decide (i < 119) := by
  rw [Nat.testBit_two_pow_sub_one]
theorem flip_getLsbD (v : Digest) (i : Nat) (hi : i < 128) :
    (T3.topFlip v).getLsbD i = (v.getLsbD i ^^ decide (i < 119)) := by
  unfold T3.topFlip T3.topMask
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, testBit_topMask]
  simp [hi]
theorem flip_lo (v : Digest) : ~~~((T3.topFlip v).extractLsb' 0 64) = v.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', flip_getLsbD v _ (by omega)]
  simp [hi, show i < 119 by omega]
theorem flip_hi (v : Digest) :
    ~~~((T3.topFlip v).extractLsb' 64 64) ^^^ SigGolfCandidate.T3M.Nonbinary.hiMask = v.extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    flip_getLsbD v _ (by omega)]
  unfold SigGolfCandidate.T3M.Nonbinary.hiMask
  rw [BitVec.getLsbD_ofNat, show (2 : Nat) ^ 64 - 2 ^ 55 = 2 ^ 55 * (2 ^ 9 - 1) by norm_num, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one]
  by_cases h : i < 55
  · simp [hi, h, show 64 + i < 119 by omega, show ¬ 55 ≤ i by omega]
  · simp [hi, h, show ¬ 64 + i < 119 by omega, show i - 55 < 9 by omega, show 55 ≤ i by omega]
theorem flip_toNat (v : Digest) : (T3.topFlip v).toNat = v.toNat ^^^ (2 ^ 119 - 1) := by
  unfold T3.topFlip T3.topMask
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
theorem flip_tail (v : Digest) : (T3.topFlip v).toNat / 2 ^ 119 = v.toNat / 2 ^ 119 := by
  rw [flip_toNat]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, testBit_topMask]
  simp
theorem flip_low7 (v : Digest) : (T3.topFlip v).toNat % 128 = 127 - v.toNat % 128 := by
  rw [flip_toNat, show (v.toNat ^^^ (2 ^ 119 - 1)) % 128 = (v.toNat ^^^ (2 ^ 119 - 1)) % 2 ^ 7 from rfl,
    show v.toNat % 128 = v.toNat % 2 ^ 7 from rfl, Nat.xor_mod_two_pow,
    show (2 ^ 119 - 1) % 2 ^ 7 = 127 by norm_num]
  have hl := Nat.mod_lt v.toNat (show 0 < 2 ^ 7 by decide +kernel)
  generalize v.toNat % 2 ^ 7 = y at hl ⊢
  interval_cases y <;> rfl
theorem prefixTarget_flip (v : Digest) :
    prefixTarget v = BitVec.ofNat 64 (1024 * (127 - (T3.topFlip v).toNat % 128) + 1056) := by
  unfold prefixTarget
  rw [flip_low7]
  congr 2
  have := Nat.mod_lt v.toNat (show 0 < 128 by decide +kernel)
  omega
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
def rejectJumpCode : List (BitVec 32) := [0x9fca206f]
sym_block rejectJumpBase := symRun { noAlias := true } rejectJumpCode (pcOf 129638) 20
theorem rejectJump_at : CodeAt Verify.image (pcOf 129638) rejectJumpCode := by
  have h := codeAt_from 129638 (by decide +kernel)
  have hp : rejectJumpCode <+: codeFrom 129638 := by decide +kernel
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
def rejectExitCode : List (BitVec 32) := [1049235,1049875]
sym_block rejectExitBase := symRun { noAlias := true } rejectExitCode (pcOf 33509) 20
theorem rejectExit_at : CodeAt Verify.image (pcOf 33509) rejectExitCode := by
  have h := codeAt_from 33509 (by decide +kernel)
  have hp : rejectExitCode <+: codeFrom 33509 := by decide +kernel
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 129638) :
    ∃ t, Steps Verify.image s 3 3 t ∧ fetch Verify.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase rejectJump_at s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 33509 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase rejectExit_at (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt Verify.image (pcOf 33511) [0x00000073] := by
      have h := codeAt_from 33511 (by decide +kernel)
      have hp : [0x00000073] <+: codeFrom 33511 := by decide +kernel
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, hp.trans h.2.2.2⟩
    exact h.fetch _ (by simp [rejectExitBase.res, rv_simp, pcOf])
  · simp [rejectExitBase.res, rv_simp]
  · simp [rejectExitBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topEntryRegs : List Reg := [.x16,.x17,.x29,.x6,.x8,.x14]
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = Nonbinary.prefixTarget v
  ra : s.getReg .x1 = BitVec.ofNat 64 TOPBASE
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = v.extractLsb' 64 64
  tail : s.getReg .x29 = BitVec.ofNat 64 (v.toNat / 2 ^ 119)
  s3 : s.getReg .x8 = 12480#64
  mask : s.getReg .x6 = 130048#64
  table : s.getReg .x2 = 0x3fe00#64
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun _ => False)
def topRowA (c : Nat) : Nat := rowA 0 c
theorem prefix_slots : (List.range 128).all (fun c => decide (topRowA c ∈ Nonbinary.aVals) &&
    (Nonbinary.prefixWordsOf (topRowA c)).isPrefixOf (codeFrom (trPc 0 c + 6))) = true := by
  decide +kernel
theorem topRowA_mem (c : Nat) (hc : c < 128) : topRowA c ∈ Nonbinary.aVals := by
  have h := List.all_eq_true.mp prefix_slots c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1
theorem prefix_at (c : Nat) (hc : c < 128) :
    CodeAt image (pcOf (trPc 0 c + 6)) (Nonbinary.prefixWordsOf (topRowA c)) := by
  have hp := trPc_lt 0 c
  have h := codeAt_from (trPc 0 c + 6) (by omega)
  have h2 := List.all_eq_true.mp prefix_slots c (List.mem_range.mpr hc)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  have hpre : Nonbinary.prefixWordsOf (topRowA c) <+: codeFrom (trPc 0 c + 6) :=
    List.isPrefixOf_iff_prefix.mp h2.2
  refine ⟨?_, ?_, ?_, hpre.trans h.2.2.2⟩
  · unfold pcOf; simp only [BitVec.toNat_ofNat]; omega
  · unfold pcOf; simp only [BitVec.toNat_ofNat]; omega
  · unfold pcOf; simp only [BitVec.toNat_ofNat, Nonbinary.prefixWordsOf, List.length_cons, List.length_nil]; omega
theorem topTransition (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : BC.EncPre w pk index 0 c t) (a : BitVec 256) :
    ∃ s, Steps image (writeHash t a) 8 8 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 14272 ≤ topRowA c ∧ topRowA c ≤ 14528 ∧ topRowA c % 16 = 0 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change d = topRowA c ∨ d = topRowA c + 48 at hd
  have hdA : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 16 ≤ 0x7000 := by omega
  have hk : KnownOK (BC.bK 0 c) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 6) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 5) + 4 = pcOf (trPc 0 c + 6)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 5)
  have hglob := Glob_writeHash ht.glob a d h12 (safeDest_hi d (by unfold WLO WIT; omega) hdA.1 (by omega))
  have hv := DigAt.writeHash_lo t a d h12 (by omega)
  have h12s : (writeHash t a).getReg .x12 = BitVec.ofNat 64 d := by rw [writeHash_getReg]; exact h12
  have hD := hglob.2.2.2.2.2
  have h10 : (writeHash t a).getReg .x10 = BitVec.ofNat 64 (topRowA c) :=
    hk (.x10, BitVec.ofNat 64 (rowA 0 c)) (by simp [BC.bK])
  have hra : (writeHash t a).getReg .x1 = BitVec.ofNat 64 TOPBASE :=
    hk (.x1, BitVec.ofNat 64 TOPBASE) (by simp [BC.bK, T3M.bK, layK])
  have h15 : (writeHash t a).getReg .x2 = 0x3fe00#64 :=
    hk (.x2, 0x3fe00#64) (by simp [BC.bK, T3M.bK, layK])
  have hmask : (writeHash t a).getMem 0xffbff8#64 = 130048#64 := hD.mask
  obtain ⟨z, ez, pz, lo, hi, tl, s3, mask, rz, fz⟩ :=
    Verify.Nonbinary.prefix_spec _ _ (topRowA c) d (trPc 0 c + 6) ha
      hpc (prefix_at c hc') h12s hdA hv hra hmask h10
  refine ⟨z, ez, ⟨pz, ?_, lo, hi, tl, s3, mask, ?_, rz, fz⟩⟩
  · rw [rz.get (by decide +kernel), hra]
  · rw [rz.get (by decide +kernel), h15]
theorem topEntry_encoded {u s : MachineState} {v : Digest} {p : Nat} (he : TopEntry u v p s) :
    Nonbinary.NCtx.Encoded (T3.topFlip v) s :=
  ⟨by rw [he.lo, Verify.Nonbinary.flip_lo], by rw [he.hi, Verify.Nonbinary.flip_hi],
    by rw [he.tail, Verify.Nonbinary.flip_tail], he.mask, he.table⟩
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def nctxOf (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 12480, coreDigit 0 v, p + 8⟩
theorem nctx_ok (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  have ht : (route index 0).2 = 0 := by rw [route_snd]; exact Nat.div_eq_of_lt hidx
  exact ⟨ht, leaf_lt index 0, by norm_num [nctxOf], by norm_num [nctxOf], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩
theorem hyperWord_top_prefix (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) :
    T3.hyperWord 0 (index / 2 ^ below 0) = BitVec.ofNat 64 ((nctxOf w index v p).prefix + 385) := by
  have h1 : (route index 0).1 = index / 2 ^ 19 % 2 ^ 12 := route_fst index 0
  have h2 : (route index 0).2 = index / 2 ^ (19 + 12) := route_snd index 0
  unfold T3.hyperWord NCtx.prefix
  simp only [nctxOf, h1, h2, show below 0 = 19 from rfl]
  congr 1
  norm_num
  omega
theorem nctx_known (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    KnownOK (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).known s := by
  have hprefix : s.getReg .x28 =
      BitVec.ofNat 64 ((nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).prefix + 385) := by
    rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg, ht.word]
    exact hyperWord_top_prefix w index _ _
  intro p hp
  simp only [NCtx.known, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact hprefix
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals exact ht.glob.1 _ (by simp [BC.bK, T3M.bK, layK, baseK])
theorem topEntry_orig (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t s : MachineState) (a : BitVec 256)
    (ht : BC.EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    Verify.Orig w (fun o => 8000 ≤ o ∧ o < layerEnd 0) s := by
  have hc' : c < 128 := by have := BC.nCopy_eq; omega
  have ha := topRowA_mem c hc'
  have hal : 14272 ≤ topRowA c ∧ topRowA c ≤ 14528 := by
    simp only [Nonbinary.aVals, List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  obtain ⟨d, h12, hd⟩ := ht.dst (by decide +kernel)
  change d = topRowA c ∨ d = topRowA c + 48 at hd
  have ho := Orig_writeHash ht.orig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => 8000 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inl (by
      have hp2 := hp.2
      have hle : layerEnd 0 = 12224 := rfl
      rw [hle] at hp2
      unfold WIT; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by simp))
theorem nctx_orig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 8000 ≤ o ∧ o < layerEnd 0) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨fun i hi k hk => ?_, hD⟩
  clear hD
  apply origW_of ho _
  all_goals simp only [NCtx.blk, nctxOf]
  all_goals norm_num [WIT, WX, layerEnd] at *
  all_goals omega
end SigGolfCandidate.T3M
end
