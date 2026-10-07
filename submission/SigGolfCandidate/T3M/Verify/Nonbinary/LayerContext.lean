import SigGolfCandidate.T3M.Verify.LayerSem
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchArith
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem

section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def topPrefixWord (tp : Word) : Word :=
  BitVec.ofNat 64 (128 + 193 * 2 ^ 56) ||| (tp >>> (16 : Word))
def prefixCode : List (BitVec 32) :=
  [407555,8796291,58252947,0xfff84813,0xfff8c893,0xf900be03,16929171,4091443,0xff80b303,0x90050413,0xa81713,6780723,0x42070067]
sym_block prefixBase := symRun { noAlias := true } prefixCode (pcOf 48177) 200
theorem prefix_run (pc : Word) : symRun { noAlias := true } prefixCode pc 200 = some prefixBase.res := by rfl
theorem tail_field (v : Digest) : (v.extractLsb' 64 64 >>> 55) = BitVec.ofNat 64 (v.toNat / 2 ^ 119) := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega
theorem not_xor (x : Word) : x ^^^ 18446744073709551615#64 = ~~~x := by
  have : (18446744073709551615#64 : Word) = BitVec.allOnes 64 := by decide
  rw [this, BitVec.xor_allOnes]
def prefixTarget (v : Digest) : Word := BitVec.ofNat 64 (1024 * (127 - v.toNat % 128) + 1056)
theorem prefix_spec (s : MachineState) (v : Digest) (d p : Nat)
    (hpc : s.pc = pcOf p) (hcode : CodeAt Verify.image (pcOf p) prefixCode)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 d) (hd : d % 8 = 0 ∧ 0x1000 ≤ d ∧ d + 16 ≤ 0x7000)
    (hv : DigAt s d v) (hra : s.getReg .x1 = BitVec.ofNat 64 TOPBASE)
    (hmask : s.getMem 0xffbff8#64 = 130048#64) (h10 : s.getReg .x10 = 14376#64)
    (h15 : s.getReg .x15 = 262144#64)
    (hmem : s.getMem (BitVec.ofNat 64 0xffbf90) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56)) :
    ∃ t, Steps Verify.image s 13 13 t ∧ t.pc = prefixTarget v ∧
      t.getReg .x16 = ~~~(v.extractLsb' 0 64) ∧ t.getReg .x17 = ~~~(v.extractLsb' 64 64) ∧
      t.getReg .x29 = BitVec.ofNat 64 (v.toNat / 2 ^ 119) ∧
      t.getReg .x8 = 12584#64 ∧ t.getReg .x6 = 130048#64 ∧ t.getReg .x15 = 262144#64 ∧
      t.getReg .x28 = topPrefixWord (s.getReg .x4) ∧
      RegsExcept s t [.x16,.x17,.x29,.x3,.x6,.x28,.x8,.x15,.x14] ∧ Frame s t (fun _ => False) := by
  have hm : s.getMem (s.getReg .x1 + 18446744073709551608#64) = 130048#64 := by
    rw [hra]; exact hmask
  have hh : s.getMem (s.getReg .x1 + 18446744073709551504#64) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56) := by
    rw [hra]; exact hmem
  have h0 : s.getMem (s.getReg .x12) = v.extractLsb' 0 64 := by rw [h12]; exact hv.1
  have h1 : s.getMem (s.getReg .x12 + 8#64) = v.extractLsb' 64 64 := by
    rw [h12, show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]; exact hv.2
  have hobl : ∀ o ∈ prefixBase.res.st.obl, o.holds s := by
    intro o ho
    simp [prefixBase.res] at ho
    rcases ho with rfl | rfl | rfl | rfl
    all_goals simp [Oblig.holds, rv_simp, accessValid_iff, MEMORY_BYTES, hra, h12, TOPBASE]
    all_goals omega
  refine ⟨_, symRun_sound (prefix_run (pcOf p)) hcode s hpc ((Oblig.all_iff _ _).mpr hobl),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, prefixBase.res, E.eval, BinOp.eval, h0, hm, not_xor]
    have e1 : (10#64 : Word).toNat % 64 = (BitVec.ofNat 64 10).toNat := by decide
    have e2 : (18446744073709551614#64 : Word) = ~~~1#64 := by decide
    have hn := SigGolfCandidate.T3M.Nonbinary.not_field (v.extractLsb' 0 64) 0 (by decide)
    simp only [pow_zero, Nat.div_one] at hn
    have hx : (v.extractLsb' 0 64).toNat % 128 = v.toNat % 128 := by
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
      exact Nat.mod_mod_of_dvd _ (show 128 ∣ 2 ^ 64 by decide)
    rw [e1, e2, SigGolfCandidate.T3M.Nonbinary.prologue_value, prefixTarget, hn, hx]
  · simp only [Result.toState_getReg, prefixBase.res, RegFile.get, E.eval, BinOp.eval, h0, not_xor]
  · simp only [Result.toState_getReg, prefixBase.res, RegFile.get, E.eval, BinOp.eval, h1, not_xor]
  · simp only [Result.toState_getReg, prefixBase.res, RegFile.get, E.eval, BinOp.eval, h1]
    exact tail_field v
  · simp [prefixBase.res, rv_simp, h10]
  · simp only [Result.toState_getReg, prefixBase.res, RegFile.get, E.eval, BinOp.eval, hm]
  · simp [prefixBase.res, rv_simp, h15]
  · simp only [Result.toState_getReg, prefixBase.res, RegFile.get, E.eval, BinOp.eval, hh, topPrefixWord]; rfl
  · intro r hr; cases r <;> simp at hr <;> simp [prefixBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [prefixBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem topPrefixWord_hdr1 (tree leaf : Nat) (ht : tree < 2 ^ 32) (hl : leaf < 2 ^ 32) (h0 : tree = 0) :
    topPrefixWord (BitVec.ofNat 64 (hdr1 tree leaf)) =
      BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + leaf * 2 ^ 16) := by
  rw [hdr1_eq tree leaf ht hl]
  unfold topPrefixWord
  change BitVec.ofNat 64 (128 + 193 * 2 ^ 56) |||
    (BitVec.ofNat 64 (tree + 2 ^ 32 * leaf) >>> (16 : Nat)) = _
  rw [ofNat_shr _ _ (by omega)]
  rw [show (tree + 2 ^ 32 * leaf) / 2 ^ 16 = leaf * 2 ^ 16 by subst h0; omega]
  rw [show 128 + 193 * 2 ^ 56 = 193 * 2 ^ 56 + 128 by omega,
    ← ofNat_or_add 128 193 56 (by decide), BitVec.or_assoc,
    ofNat_or_disjoint' 128 (leaf * 2 ^ 16) 16 (by decide) (by omega),
    ofNat_or_add _ 193 56 (by omega)]
  congr 1
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
  have h := codeAt_from 129638 (by decide)
  have hp : rejectJumpCode <+: codeFrom 129638 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
def rejectExitCode : List (BitVec 32) := [1049235,1049875]
sym_block rejectExitBase := symRun { noAlias := true } rejectExitCode (pcOf 33509) 20
theorem rejectExit_at : CodeAt Verify.image (pcOf 33509) rejectExitCode := by
  have h := codeAt_from 33509 (by decide)
  have hp : rejectExitCode <+: codeFrom 33509 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 129638) :
    ∃ t, Steps Verify.image s 3 3 t ∧ fetch Verify.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase rejectJump_at s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 33509 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase rejectExit_at (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt Verify.image (pcOf 33511) [0x00000073] := by
      have h := codeAt_from 33511 (by decide)
      have hp : [0x00000073] <+: codeFrom 33511 := by decide +kernel
      exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
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
def topEntryRegs : List Reg := [.x1,.x3,.x16,.x17,.x14,.x25,.x29,.x8,.x22,.x6,.x15,.x28]
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = Nonbinary.prefixTarget v
  ra : s.getReg .x1 = BitVec.ofNat 64 TOPBASE
  lo : s.getReg .x16 = ~~~(v.extractLsb' 0 64)
  hi : s.getReg .x17 = ~~~(v.extractLsb' 64 64)
  tail : s.getReg .x29 = BitVec.ofNat 64 (v.toNat / 2 ^ 119)
  s3 : s.getReg .x8 = 12584#64
  mask : s.getReg .x6 = 130048#64
  table : s.getReg .x15 = 262144#64
  «prefix» : s.getReg .x28 = Nonbinary.topPrefixWord (u.getReg .x4)
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun _ => False)
theorem prefix_slots : (List.range 128).all (fun c => Nonbinary.prefixCode.isPrefixOf (codeFrom (trPc 0 c + 9))) = true := by
  decide +kernel
theorem prefix_at (c : Nat) (hc : c < 128) : CodeAt image (pcOf (trPc 0 c + 9)) Nonbinary.prefixCode := by
  have hp := trPc_lt 0 c
  have h := codeAt_from (trPc 0 c + 9) (by omega)
  have hpre : Nonbinary.prefixCode <+: codeFrom (trPc 0 c + 9) :=
    List.isPrefixOf_iff_prefix.mp (List.all_eq_true.mp prefix_slots c (List.mem_range.mpr hc))
  refine ⟨?_, ?_, ?_, hpre.trans h.2.2.2⟩
  · unfold pcOf; simp only [BitVec.toNat_ofNat]; omega
  · unfold pcOf; simp only [BitVec.toNat_ofNat]; omega
  · unfold pcOf; simp only [BitVec.toNat_ofNat, Nonbinary.prefixCode, List.length_cons, List.length_nil]; omega
theorem topTransition (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256) :
    ∃ s, Steps image (writeHash t a) 13 13 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  obtain ⟨d, h12, hd⟩ := ht.dst0 rfl
  have hk : KnownOK (BC.bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 9) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 8) + 4 = pcOf (trPc 0 c + 9)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 8)
  have hglob := Glob_writeHash ht.glob a d h12 (by rcases hd with rfl | rfl <;> decide)
  have hv := DigAt.writeHash_lo t a d h12 (by omega)
  have h12s : (writeHash t a).getReg .x12 = BitVec.ofNat 64 d := by rw [writeHash_getReg]; exact h12
  have hD := hglob.2.2.2.2.2
  have h10 : (writeHash t a).getReg .x10 = 14376#64 := hk (.x10, BitVec.ofNat 64 (x10In 0)) (by simp [BC.bK])
  have hra : (writeHash t a).getReg .x1 = BitVec.ofNat 64 TOPBASE :=
    hk (.x1, BitVec.ofNat 64 TOPBASE) (by simp [BC.bK, bK, layK])
  have hmem := hD.prefix 0 (by decide)
  have hmask : (writeHash t a).getMem 0xffbff8#64 = 130048#64 := hD.mask
  obtain ⟨z, ez, pz, lo, hi, tl, s3, mask, tab, px, rz, fz⟩ :=
    Verify.Nonbinary.prefix_spec _ _ d (trPc 0 c + 9) hpc (prefix_at c (by have := BC.nCopy_eq; omega)) h12s
      (by rcases hd with rfl | rfl <;> decide) hv hra hmask h10 (hk (.x15, 262144#64) (by simp [BC.bK, T3M.bK, layK])) (by simpa [HDATA] using hmem)
  refine ⟨z, ez, ⟨pz, ?_, lo, hi, tl, s3, mask, tab, px, ?_, fz⟩⟩
  · rw [rz.get (by decide), hra]
  · exact rz.mono (by decide)
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
  ⟨w, (route index 0).2, (route index 0).1, 12584, coreDigit 0 v, p + 11⟩
theorem nctx_ok (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  have ht : (route index 0).2 = 0 := by rw [route_snd]; exact Nat.div_eq_of_lt hidx
  exact ⟨ht, leaf_lt index 0, by norm_num [nctxOf], by norm_num [nctxOf], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩
theorem nctx_known (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (hidx : index < 2 ^ 31)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    KnownOK (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).known s := by
  have htree : (route index 0).2 = 0 := by
    rw [route_snd]
    exact Nat.div_eq_of_lt hidx
  have hleaf := leaf_lt32 index 0
  have hprefix : s.getReg .x28 = BitVec.ofNat 64
      (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).prefix := by
    rw [he.prefix, writeHash_getReg, ht.tp 0 rfl,
      Nonbinary.topPrefixWord_hdr1 _ _ (tree_lt index 0 hidx) hleaf htree]
    simp only [nctxOf, NCtx.prefix, htree, Nat.zero_mul, Nat.zero_add,
      Nat.mod_eq_of_lt hleaf]
  intro p hp
  simp only [NCtx.known, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact hprefix
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals try exact ht.tp 0 rfl
  all_goals exact ht.glob.1 _ (by simp [BC.bK, bK, layK, baseK, nctxOf, NCtx.w1, hw, t3In])
theorem topEntry_orig (w : ClaudeWCT.W9.T3M.WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    Verify.Orig w (fun o => 8104 ≤ o ∧ o < layerEnd 0) s := by
  obtain ⟨d, h12, hd⟩ := ht.dst0 rfl
  have ho := Orig_writeHash ht.orig a d h12 (by omega)
  have hu : Verify.Orig w (fun o => 8104 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    fun j hj hp => ho j hj ⟨hp, Or.inl (by
      have hp2 := hp.2
      have hle : layerEnd 0 = 12328 := rfl
      rw [hle] at hp2
      unfold WIT; omega)⟩
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by simp))
theorem nctx_orig (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 8104 ≤ o ∧ o < layerEnd 0) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨fun i hi k hk => ?_, hD⟩
  clear hD
  apply origW_of ho _
  all_goals simp only [NCtx.blk, nctxOf]
  all_goals norm_num [WIT, WX, layerEnd] at *
  all_goals omega
end SigGolfCandidate.T3M
end
