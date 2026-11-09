import SigGolfCandidate.Merge074
import SigGolfCandidate.Merge095
import SigGolfCandidate.HintCodecArithmetic
set_option autoImplicit false
namespace SigGolfCandidate.HintSignFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
def hookWords : List (BitVec 32) := [0xc00006f]
def bodyWords : List (BitVec 32) := [0xe3303,0x8e3383,0x3339e13,0x33e5e13,0x6eb023,0x1ceb423,0x1b39393,0x283d393,0x1835313,0x137313,0x2431313,0x736333,0x66f37,0xf5f03,0x3c800193,0x23f5e33,0x1a200193,0x23e0e33,0x1e400193,0x23f7f33,0x1cf0f33,0x34f1f13,0x1cf5f13,0x1e36333,0x5140206f]
sym_block hookRun := symRun { noAlias := true } hookWords (pcOf 22526) 100
sym_block bodyRun := symRun { noAlias := true } bodyWords (pcOf 22574) 100
 theorem body_spec {im : Image} (hc : CodeAt im (pcOf 22574) bodyWords)
    (s : MachineState) (hp : s.pc = pcOf 22574)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (SIG+16*328))
    (h29 : s.getReg .x29 = BitVec.ofNat 64 (SIG+16*324)) :
    Steps im s 25 34 (bodyRun.res.toState s) ∧ (bodyRun.res.toState s).pc = pcOf 24971 ∧
      (bodyRun.res.toState s).getMem (BitVec.ofNat 64 (SIG+16*324)) = s.getMem (BitVec.ofNat 64 (SIG+16*328)) ∧
      (bodyRun.res.toState s).getMem (BitVec.ofNat 64 (SIG+16*324+8)) =
        (s.getMem (BitVec.ofNat 64 (SIG+16*328+8)) <<< (51 : Nat)) >>> (51 : Nat) ∧
      RegsExcept s (bodyRun.res.toState s) [.x3,.x6,.x7,.x28,.x30] ∧
      Frame s (bodyRun.res.toState s) (fun A => A=SIG+16*324 ∨ A=SIG+16*324+8) := by
  refine ⟨symRun_sound bodyRun hc s hp ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bodyRun.res,rv_simp,h28,h29,SIG,accessValid_iff,MEMORY_BYTES]
  · rfl
  · simp [bodyRun.res,rv_simp,h28,h29,SIG]
  · simp [bodyRun.res,rv_simp,h28,h29,SIG]
  · intro r hr; simp at hr; cases r <;> simp_all [bodyRun.res,rv_simp] <;> rfl
  · intro A hA hn
    have h0 : A ≠ SIG+16*324 := by tauto
    have h8 : A ≠ SIG+16*324+8 := by tauto
    simp [bodyRun.res,rv_simp,h28,h29,SIG,ofNat_inj hA (by decide : 33856<2^64),
      ofNat_inj hA (by decide : 33864<2^64)]
    simp_all [SIG]
def hintLow (h : Word) : Word := UnOp.eval (.ld .hu 0) h
def hintCalc (h : Word) : Word :=
  BinOp.eval .add (BinOp.eval .remu (hintLow h) 484#64)
    (BinOp.eval .mul (BinOp.eval .divu (hintLow h) 968#64) 418#64)
def newX (lo hi h : Word) : Word :=
  ((((lo >>> (24 : Nat)) &&& 1#64) <<< (36 : Nat)) ||| ((hi <<< (27 : Nat)) >>> (40 : Nat))) ||| ((hintCalc h <<< (52 : Nat)) >>> (28 : Nat))
theorem body_x (s : MachineState)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (SIG+16*328))
    (h29 : s.getReg .x29 = BitVec.ofNat 64 (SIG+16*324)) :
    (bodyRun.res.toState s).getReg .x6 =
      newX (s.getMem (BitVec.ofNat 64 (SIG+16*328)))
        (s.getMem (BitVec.ofNat 64 (SIG+16*328+8))) (s.getMem 0x66000) := by
  simp [bodyRun.res,rv_simp,h28,h29,SIG,newX,hintCalc,hintLow,
    BitVec.add_comm,BitVec.mul_comm,BitVec.or_comm]
theorem hintLow_toNat (h : Word) : (hintLow h).toNat = h.toNat % 2^16 := by
  simp only [hintLow,UnOp.eval,LoadKind.fromWord,extractHalfword,Nat.zero_mul,
    BitVec.ushiftRight_zero,BitVec.toNat_setWidth]
  have hm := Nat.mod_lt h.toNat (by decide : 0 < 2^16)
  norm_num at hm ⊢
  omega
theorem hintCalc_toNat (h : Word) :
    (hintCalc h).toNat = h.toNat % 2^16 % 484 + (h.toNat % 2^16 / 968)*418 := by
  have hn : h.toNat % 2^16 < 2^64 := lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hl : hintLow h = BitVec.ofNat 64 (h.toNat % 2^16) := by
    apply BitVec.eq_of_toNat_eq
    rw [hintLow_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn]
  unfold hintCalc
  change (rv64_remu (hintLow h) 484#64 + rv64_divu (hintLow h) 968#64 * 418#64).toNat = _
  rw [hl,ClaudeWCT.W9.Machine.Sign.SharedSeed.remu_ofNat (h.toNat % 2^16) 484 hn (by decide) (by decide),
    ClaudeWCT.W9.Machine.Sign.SharedSeed.divu_ofNat (h.toNat % 2^16) 968 hn (by decide) (by decide)]
  simp only [BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat]
  have hh := Nat.mod_lt h.toNat (by decide : 0 < 2^16)
  norm_num at hh ⊢
  omega
theorem rawHi_toNat (h : Word) : ((h <<< (27 : Nat)) >>> (40 : Nat)).toNat = h.toNat / 2^13 % 2^24 := by
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  have hh := h.isLt
  norm_num at hh ⊢
  omega
theorem hint_shift (h : Word) : (h <<< (52 : Nat)) >>> (28 : Nat) = (BitVec.ofNat 64 (h.toNat % 2^12)) <<< (24 : Nat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
  have hh := h.isLt
  norm_num at hh ⊢
  omega
theorem permute_ors (u a c : Word) : (u ||| a) ||| c = (a ||| c) ||| u := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or]
  cases u.getLsbD i <;> cases a.getLsbD i <;> cases c.getLsbD i <;> rfl
theorem joined_bits (a c u : Word) (ha : a.toNat < 2^24) (hc : c.toNat < 2^12) (hu : u.toNat < 2) :
    ((u <<< (36 : Nat)) ||| a) ||| (c <<< (24 : Nat)) =
      BitVec.ofNat 64 (a.toNat+c.toNat*2^24+u.toNat*2^36) := by
  rw [permute_ors]
  have hcx : c.toNat*2^24 < 2^64 := lt_trans (Nat.mul_lt_mul_of_pos_right hc (by decide)) (by decide)
  have hux : u.toNat*2^36 < 2^64 := lt_trans (Nat.mul_lt_mul_of_pos_right hu (by decide)) (by decide)
  have hlow := ClaudeWCT.W9.Machine.Expand.PrePass.toNat_or_shl a c 24 ha hcx
  have hl : (a ||| c <<< (24 : Nat)).toNat < 2^36 := by rw [hlow]; norm_num at ha hc ⊢; omega
  apply BitVec.eq_of_toNat_eq
  rw [ClaudeWCT.W9.Machine.Expand.PrePass.toNat_or_shl _ u 36 hl hux,hlow,BitVec.toNat_ofNat]
  apply (Nat.mod_eq_of_lt ?_).symm
  norm_num at ha hc hu ⊢
  omega
theorem newX_toNat (lo hi h : Word) :
    (newX lo hi h).toNat = hi.toNat / 2^13 % 2^24 +
      (hintCalc h).toNat % 2^12 * 2^24 + (lo.toNat / 2^24 % 2)*2^36 := by
  have ha : ((hi <<< (27 : Nat)) >>> (40 : Nat)).toNat < 2^24 := by rw [rawHi_toNat]; exact Nat.mod_lt _ (by decide)
  have hc : (BitVec.ofNat 64 ((hintCalc h).toNat % 2^12)).toNat < 2^12 := by
    rw [BitVec.toNat_ofNat]
    have hm := Nat.mod_lt (hintCalc h).toNat (by decide : 0 < 2^12)
    norm_num at hm ⊢
    omega
  have hu : (((lo >>> (24 : Nat)) &&& 1#64)).toNat < 2 := by
    simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
    norm_num
    have hm := Nat.mod_lt (lo.toNat / 16777216) (by decide : 0 < 2)
    omega
  unfold newX
  rw [hint_shift,joined_bits _ _ _ ha hc hu,BitVec.toNat_ofNat,rawHi_toNat]
  have hm := Nat.mod_lt (hintCalc h).toNat (by decide : 0 < 2^12)
  simp only [BitVec.toNat_ofNat,BitVec.toNat_and,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  norm_num
  have hr := Nat.mod_lt (hi.toNat / 2^13) (by decide : 0 < 2^24)
  have hl := Nat.mod_lt (lo.toNat / 2^24) (by decide : 0 < 2)
  norm_num at hm hr hl ⊢
  omega
theorem formula_compress (h : Nat) (he : h / 484 % 2 = 0) :
    h % 484 + (h / 968)*418 = HintResearch.compress h := by
  have hg : ¬(520 ≤ h ∧ h < 854) := by
    intro hg
    have hd : h / 484 = 1 := by omega
    rw [hd] at he
    contradiction
  unfold HintResearch.compress
  rw [if_neg hg,Nat.div_div_eq_div_mul]
  norm_num
  omega
end SigGolfCandidate.HintSignFinish

namespace SigGolfCandidate.HintSignFinish
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify ClaudeWCT.W9.Machine.Sign
theorem finish_spec {im : Image} (hhook : CodeAt im (pcOf 22526) hookWords)
    (hbody : CodeAt im (pcOf 22574) bodyWords) (s : MachineState) (hp : s.pc=pcOf 22526)
    (h28 : s.getReg .x28=BitVec.ofNat 64 (SIG+16*328))
    (h29 : s.getReg .x29=BitVec.ofNat 64 (SIG+16*324)) :
    ∃t, Steps im s 26 35 t ∧ t.pc=pcOf 24971 ∧
      t.getReg .x6 = newX (s.getMem (BitVec.ofNat 64 (SIG+16*328)))
        (s.getMem (BitVec.ofNat 64 (SIG+16*328+8))) (s.getMem 0x66000) ∧
      t.getMem (BitVec.ofNat 64 (SIG+16*324))=s.getMem (BitVec.ofNat 64 (SIG+16*328)) ∧
      t.getMem (BitVec.ofNat 64 (SIG+16*324+8))=(s.getMem (BitVec.ofNat 64 (SIG+16*328+8))<<<(51:Nat))>>>(51:Nat) ∧
      RegsExcept s t [.x3,.x6,.x7,.x28,.x30] ∧
      Frame s t (fun A=>A=SIG+16*324 ∨ A=SIG+16*324+8) := by
  let u := hookRun.res.toState s
  have sh : Steps im s 1 1 u := symRun_sound hookRun hhook s hp trivial
  have pu : u.pc=pcOf 22574 := rfl
  have u28 : u.getReg .x28=BitVec.ofNat 64 (SIG+16*328) := by simpa [u,hookRun.res,rv_simp] using h28
  have u29 : u.getReg .x29=BitVec.ofNat 64 (SIG+16*324) := by simpa [u,hookRun.res,rv_simp] using h29
  obtain ⟨sb,pb,lo,hi,rb,fb⟩ := body_spec hbody u pu u28 u29
  refine ⟨bodyRun.res.toState u,sh.trans sb,pb,?_,?_,?_,?_,?_⟩
  · rw [body_x u u28 u29]
    rfl
  · simpa [u,hookRun.res,rv_simp] using lo
  · simpa [u,hookRun.res,rv_simp] using hi
  · have rh : RegsExcept s u [] := by intro r hr; cases r <;> rfl
    exact (rh.trans rb).mono (by simp)
  · simpa [u,hookRun.res,rv_simp,Frame] using fb

end SigGolfCandidate.HintSignFinish
