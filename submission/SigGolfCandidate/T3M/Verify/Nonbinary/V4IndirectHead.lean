import SigGolfCandidate.T3M.Verify.Mem
import SigGolfCandidate.T3M.Verify.Code

/- Exact V4 four-word high125 head, reading the real previous HASH output
   via x12. The two arithmetic proof bodies are attributed unchanged copies
   of Search.CsBlocks with fresh local names to avoid an unrelated full
   Search execution dependency. Decoder/whole Verify remain in LayerContext. -/
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem v4_ext_shr_ofNat (v : BitVec 128) (base k : Nat) (hk : k < 64) :
    v.extractLsb' base 64 >>> k = BitVec.ofNat 64 (v.toNat / 2 ^ (base + k) % 2 ^ (64 - k)) := by
  have := ext_shr_mask v base k (64 - k) (by omega)
  rw [← this]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  by_cases h : i < 64 - k
  · simp [h]
  · simp [h, show ¬ k + i < 64 by omega]
theorem v4_ext64_shr_eq_zero (v : BitVec 128) (k : Nat) (hk : k < 64) :
    (v.extractLsb' 64 64 >>> k = 0#64) ↔ v.toNat < 2 ^ (64 + k) := by
  have hv := v.isLt
  have h1 : v.toNat / 2 ^ (64 + k) < 2 ^ (64 - k) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show 64 - k + (64 + k) = 128 by omega]; exact hv
  have h2 : v.toNat / 2 ^ (64 + k) < 2 ^ 64 := lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))
  rw [v4_ext_shr_ofNat v 64 k hk, show (0#64) = BitVec.ofNat 64 0 from rfl,
    ofNat_eq_iff (lt_of_le_of_lt (Nat.mod_le _ _) h2) (by positivity),
    Nat.mod_eq_of_lt h1, Nat.div_eq_zero_iff_lt (by positivity)]
def headCode : List (BitVec 32) := [0x63803,0x863883,64542483,268899939]
sym_block headBase := symRun { noAlias := true } headCode (pcOf 96160) 200
theorem head_at : CodeAt Verify.image (pcOf 96160) headCode := by
  have h := codeAt_from 96160 (by decide)
  have hp : headCode <+: codeFrom 96160 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
theorem head_spec (s : MachineState) (v : Digest) (d : Nat)
    (hpc : s.pc = pcOf 96160) (h12 : s.getReg .x12=BitVec.ofNat 64 d)
    (hd : d=15560 ∨ d=15608) (hv : DigAt s d v) :
    ∃ t, Steps Verify.image s 4 4 t ∧
      t.pc = (if v.toNat < 2 ^ 125 then pcOf 96164 else pcOf 96230) ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17,.x14] ∧ Frame s t (fun _ => False) := by
  rcases hd with rfl | rfl
  all_goals
    have h0 : s.getMem (s.getReg .x12)=v.extractLsb' 0 64 := by rw [h12]; exact hv.1
    have h1 : s.getMem (s.getReg .x12+8)=v.extractLsb' 64 64 := by
      rw [h12,show (8 : Word)=BitVec.ofNat 64 8 from rfl,ofNat_add_ofNat]; exact hv.2
    refine ⟨_, symRun_sound headBase head_at s hpc
      (by simp [headBase.res,rv_simp,h12] <;> decide), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc,headBase.res,E.eval,CmpOp.eval,BinOp.eval,h12,
        ofNat_add_ofNat,hv.2,
        BitVec.toNat_ofNat,Nat.reduceMod,bne_iff_ne,ne_eq,
        v4_ext64_shr_eq_zero v 61 (by decide),show (64+61 : Nat)=125 from rfl]
      split_ifs <;> first | rfl | omega
    · simpa only [Result.toState_getReg,headBase.res,rv_simp] using h0
    · simpa only [Result.toState_getReg,headBase.res,rv_simp] using h1
    · intro r hr; cases r <;> simp at hr <;> simp [headBase.res,rv_simp] <;> rfl
    · intro A _ _; simp [headBase.res,rv_simp]
#print axioms head_at
#print axioms head_spec
end SigGolfCandidate.T3M.Verify.Nonbinary
