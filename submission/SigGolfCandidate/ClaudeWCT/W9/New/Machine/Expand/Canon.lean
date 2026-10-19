import SigGolfCandidate.T3M.Search.BCCounterSearch
import SigGolfCandidate.T3M.Expand.Blocks
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base

/-! # Expand canonical counter search (configuration e7b, r3-lean-sign expand porter)

Split out of `Expand/Routine.lean` so that it builds independently of the forest/FTS modules.
Expand kernel base `b = 354`; choice block at 43040 (`choiceBase 354`), `pa` at 43057, `topcr` at 43064..43070,
floor hooks at 46905 (policy hints, radix 20), lower/top credit hooks at 46918/46924 (credit words `0x66040 + 8 lay`). -/

namespace ClaudeWCT.W9.Machine.Expand.SharedCounterHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
/-- `46905`: `t3 := mem[0x66000]` (policy hints), `t4 := 20` (radix), branch on the layer. -/
def firstCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xe3e03,0x1400e93,0xfff40f13,0xf0c63]
sym_block first := symRun {noAlias:=true} firstCode (pcOf 46905) 20
def middleCode : List (BitVec 32) := bv_list% 32 [0x3de5e33,0xffe40f13,0xf0663]
sym_block middle := symRun {noAlias:=true} middleCode (pcOf 46911) 20
def lastCode : List (BitVec 32) := bv_list% 32 [0x3de5e33,0xb40fc06f]
sym_block last := symRun {noAlias:=true} lastCode (pcOf 46914) 20
def remainderCode : List (BitVec 32) := bv_list% 32 [0x3de7e33,0xb38fc06f]
sym_block remainder := symRun {noAlias:=true} remainderCode (pcOf 46916) 20
def lowerCreditCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x341e93,0x1de0e33,0x54e3023,0xf21d206f]
sym_block lowerCredit := symRun {noAlias:=true} lowerCreditCode (pcOf 46918) 20
def topCreditCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xff4a0e93,0x5de3023,0xee1d206f]
sym_block topCredit := symRun {noAlias:=true} topCreditCode (pcOf 46924) 20
structure Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46905) firstCode
  middle : CodeAt im (pcOf 46911) middleCode
  last : CodeAt im (pcOf 46914) lastCode
  remainder : CodeAt im (pcOf 46916) remainderCode
  lowerCredit : CodeAt im (pcOf 46918) lowerCreditCode
  topCredit : CodeAt im (pcOf 46924) topCreditCode
theorem rem20 (n : Nat) (hn : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 20#64=BitVec.ofNat 64 (n%20) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_remu,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n%20<2^64 by omega)]
  omega
theorem div20 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 20#64=BitVec.ofNat 64 (n/20) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/20<2^64 by omega)]
  omega
theorem floor1_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=1)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 8 11 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/1%20) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=remainder.res.toState s1
  have st2 : Steps im s1 2 5 s2 := symRun_sound remainder hc.remainder s1 (by simp [s1, first.res, s2, remainder.res, rv_simp, h8]) (by simp [remainder.res,rv_simp])
  refine ⟨s2,st1.trans (st2),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, remainder.res,rv_simp,h8]
  · simp [s1, first.res, s2, remainder.res,rv_simp,hm]
    simp only [div20 hints (by omega),div20 (hints/20) (by omega),rem20 hints (by omega),rem20 (hints/20) (by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
theorem floor2_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=2)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 11 17 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/20%20) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=middle.res.toState s1
  have st2 : Steps im s1 3 6 s2 := symRun_sound middle hc.middle s1 (by simp [s1, first.res, s2, middle.res, rv_simp, h8]) (by simp [middle.res,rv_simp])
  let s3:=remainder.res.toState s2
  have st3 : Steps im s2 2 5 s3 := symRun_sound remainder hc.remainder s2 (by simp [s1, first.res, s2, middle.res, s3, remainder.res, rv_simp, h8]) (by simp [remainder.res,rv_simp])
  refine ⟨s3,st1.trans (st2.trans (st3)),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, middle.res, s3, remainder.res,rv_simp,h8]
  · simp [s1, first.res, s2, middle.res, s3, remainder.res,rv_simp,hm]
    simp only [div20 hints (by omega),div20 (hints/20) (by omega),rem20 hints (by omega),rem20 (hints/20) (by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
theorem floor3_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=3)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 11 17 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/400%20) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=middle.res.toState s1
  have st2 : Steps im s1 3 6 s2 := symRun_sound middle hc.middle s1 (by simp [s1, first.res, s2, middle.res, rv_simp, h8]) (by simp [middle.res,rv_simp])
  let s3:=last.res.toState s2
  have st3 : Steps im s2 2 5 s3 := symRun_sound last hc.last s2 (by simp [s1, first.res, s2, middle.res, s3, last.res, rv_simp, h8]) (by simp [last.res,rv_simp])
  refine ⟨s3,st1.trans (st2.trans (st3)),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, middle.res, s3, last.res,rv_simp,h8]
  · simp [s1, first.res, s2, middle.res, s3, last.res,rv_simp,hm]
    simp only [div20 hints (by omega),div20 (hints/20) (by omega),rem20 hints (by omega),rem20 (hints/20) (by omega)]
    try rw [Nat.div_div_eq_div_mul]
    try rw [Nat.mod_eq_of_lt (show hints/400<20 by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
def lowerPrepCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x341e93,0x1de0e33]
def lowerStoreCode : List (BitVec 32) := bv_list% 32 [0x54e3023,0xf21d206f]
sym_block lowerPrep := symRun {noAlias:=true} lowerPrepCode (pcOf 46918) 6
sym_block lowerStore := symRun {noAlias:=true} lowerStoreCode (pcOf 46922) 4

theorem lowerPrep_steps {im : Image} (hc : CodeAt im (pcOf 46918) lowerPrepCode)
    (s : MachineState) (hp : s.pc=pcOf 46918) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) :
    ∃ t,Steps im s 4 4 t ∧ t.pc=pcOf 46922 ∧ t.getReg .x28=BitVec.ofNat 64 (0x66000+8*lay) ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerPrep hc s hp (by simp [lowerPrep.res,rv_simp]),rfl,?_,?_,?_⟩
  · rcases hl with ⟨hl,hu⟩;interval_cases lay <;> simp [lowerPrep.res,rv_simp,h8]
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl

theorem lowerStore_steps {im : Image} (hc : CodeAt im (pcOf 46922) lowerStoreCode)
    (s : MachineState) (hp : s.pc=pcOf 46922) (addr : Nat) (ha : addr+72<2^24) (hal : addr%8=0)
    (h28 : s.getReg .x28=BitVec.ofNat 64 addr) (credit : BitVec 64) (h20 : s.getReg .x20=credit) :
    ∃ t,Steps im s 2 2 t ∧ t.pc=pcOf 787 ∧ t.getMem (BitVec.ofNat 64 (addr+64))=credit ∧
      RegsExcept s t [] ∧ Frame s t (fun A=>A=addr+64) := by
  refine ⟨_,symRun_sound lowerStore hc s hp (by simp [lowerStore.res,rv_simp,h28,accessValid_iff,MEMORY_BYTES];omega),rfl,?_,?_,?_⟩
  · simp only [Result.toState_getMem,lowerStore.res];t3n [h28,h20]
    try rw [Nat.mod_eq_of_lt (show addr+64<18446744073709551616 by omega),if_pos rfl]
  · intro r hr;cases r <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,lowerStore.res];t3n [h28]
    rw [Nat.mod_eq_of_lt (show addr+64<18446744073709551616 by omega),if_neg (by omega)]

theorem lowerCredit_steps {im : Image} (hc : CodeAt im (pcOf 46918) lowerCreditCode)
    (s : MachineState) (hp : s.pc=pcOf 46918) (lay : Nat) (hl : 1≤lay ∧ lay≤3)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay) (credit : BitVec 64) (hc' : s.getReg .x20=credit) :
    ∃ t,Steps im s 6 6 t ∧ t.pc=pcOf 787 ∧ t.getMem (BitVec.ofNat 64 (0x66040+8*lay))=credit ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun A=>A=0x66040+8*lay) := by
  have prep : CodeAt im (pcOf 46918) lowerPrepCode := by
    simpa using (CodeAt.drop_prefix (pre:=[]) (seg:=lowerPrepCode) (post:=lowerStoreCode) hc)
  have store : CodeAt im (pcOf 46922) lowerStoreCode := by
    simpa [lowerPrepCode,pcOf] using (CodeAt.drop_prefix (pre:=lowerPrepCode) (seg:=lowerStoreCode) (post:=[]) hc)
  obtain ⟨u,su,up,ug,ur,uf⟩:=lowerPrep_steps prep s hp lay hl h8
  have u20 : u.getReg .x20=credit := (ur.get (by decide)).trans hc'
  obtain ⟨t,ut,tp,tg,tr,tf⟩:=lowerStore_steps store u up (0x66000+8*lay) (by omega) (by omega) ug credit u20
  refine ⟨t,su.trans ut,tp,?_,(ur.trans tr).mono (by decide),?_⟩
  · simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tg
  · exact (uf.trans tf).mono (by intro A _ h;rcases h with h|h;exact False.elim h;simp_all [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm])

theorem topCredit_steps {im : Image} (hc : CodeAt im (pcOf 46924) topCreditCode)
    (s : MachineState) (hp : s.pc=pcOf 46924) (acc : Nat) (ha : 12≤acc) (hb : acc<2^64)
    (hx : s.getReg .x20=BitVec.ofNat 64 acc) :
    ∃ t,Steps im s 5 5 t ∧ t.pc=pcOf 776 ∧ t.getMem (0x66040#64)=BitVec.ofNat 64 (acc-12) ∧
      RegsExcept s t [.x28,.x29] ∧ Frame s t (fun A=>A=0x66040) := by
  refine ⟨_,symRun_sound topCredit hc s hp (by simp [topCredit.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp only [Result.toState_getMem,topCredit.res];t3n [hx];omega
  · intro r hr;cases r <;> simp at hr <;> rfl
  · intro A ha hn
    simp only [Result.toState_getMem,topCredit.res];t3n []
    rw [if_neg (by omega)]
#print axioms floor1_steps
#print axioms floor2_steps
#print axioms floor3_steps
#print axioms lowerCredit_steps
#print axioms topCredit_steps
end ClaudeWCT.W9.Machine.Expand.SharedCounterHooks

namespace ClaudeWCT.W9.Machine.Expand.SharedCounterHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem code_slice {im : Image} {base off : Nat} {words part : List (BitVec 32)}
    (hc : CodeAt im (pcOf base) words) (ho : off+part.length≤words.length)
    (he : (words.drop off).take part.length=part) :
    CodeAt im (pcOf (base+off)) part := by
  have hsplit : words=words.take off ++ part ++ words.drop (off+part.length) := by
    calc
      words = words.take off ++ words.drop off := (List.take_append_drop off words).symm
      _ = words.take off ++ (words.drop off).take part.length ++ (words.drop off).drop part.length := by
        simp only [List.append_assoc,List.take_append_drop]
      _ = words.take off ++ part ++ words.drop (off+part.length) := by rw [he,List.drop_drop]
  rw [hsplit] at hc
  have hh:=CodeAt.drop_prefix hc
  have hl : (words.take off).length=off := by rw [List.length_take,Nat.min_eq_left (by omega)]
  rw [hl] at hh
  convert hh using 1
  simp only [pcOf,←BitVec.ofNat_add]
  congr 1
  omega

theorem code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : Code im := by
  constructor
  · exact code_slice (off:=1849) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1855) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1858) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1860) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1862) hc (by decide +kernel) (by decide +kernel)
  · exact code_slice (off:=1868) hc (by decide +kernel) (by decide +kernel)
theorem installed_code : Code Images.expandImage := code_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand.SharedCounterHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT WCT9.CanonicalPolicy
def creditAddr (lay : Layer) : Nat := 0x66040+8*lay.val
def CreditW (lay : Layer) (A : Nat) : Prop := A=creditAddr lay ∧ 0x66040≤A ∧ A<0x66060
/-- Floors read from the policy hints (radix 20); the top floor is the RC kernel floor 19 (`R6.kFloor`).
Agrees with `Research.SharedForest.hintFloor` (`CanonicalPolicy.topFloor = 19`). -/
def hintFloor (hints : BitVec 16) (lay : Layer) : Nat :=
  if lay=0 then 19 else hints.toNat/20^(lay.val-1)%20
theorem creditAddr_lt (lay : Layer) : creditAddr lay<2^64 := by
  have := lay.isLt;unfold creditAddr;omega
theorem creditAddr_mem (lay : Layer) : CreditW lay (creditAddr lay) := by
  have := lay.isLt
  unfold CreditW creditAddr
  omega
theorem creditW_zero {X : Nat} (h : CreditW 0 X) : X=0x66040 := by
  rcases h with ⟨h,_⟩; rw [h]; rfl
theorem hintFloor_lt (hints : BitVec 16) (lay : Layer) : hintFloor hints lay<20 := by
  unfold hintFloor
  split_ifs
  · omega
  · omega
theorem hintFloor_top (hints : BitVec 16) : hintFloor hints 0=19 := rfl
theorem flag_not_credit (lay : Layer) : ¬ CreditW lay FLAG := by
  unfold CreditW FLAG; omega
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

def lowerAddCode : List (BitVec 32) := bv_list% 32 [0x41988e33,0xffae0e13,0x1e3e13,0x1ca0a33]
/-- `43024: jal zero, pa` (path-aware lower credit, choice block at 43057). -/
def floorJumpCode : List (BitVec 32) := bv_list% 32 [0x0840006f]
def lowerCreditJumpCode : List (BitVec 32) := bv_list% 32 [0x4c90306f]
def lowerBranchCode : List (BitVec 32) := bv_list% 32 [0x1ca6463]
def lowerBadCode : List (BitVec 32) := bv_list% 32 [0xc85d606f]
/-- `43447: jal zero, topcr` (43064). -/
def topBranchCode : List (BitVec 32) := bv_list% 32 [0xa05ff06f]
/-- `topcr` (43064): `s4 += 3` on the LOW path (choice flag clear), then the floor test `s4 < 30` (floor 18 + 12)
fails into `choice_r` (43043), else `jal` to the top credit hook (46924). -/
def topCr0 : List (BitVec 32) := bv_list% 32 [0x00066e37,0x7f8e3e03,0x000e1463]
def topCr3 : List (BitVec 32) := bv_list% 32 [0x003a0a13]
def topCr4 : List (BitVec 32) := bv_list% 32 [0x01e00e13,0xf9ca6ce3]
def topCr6 : List (BitVec 32) := bv_list% 32 [0x4390306f]
sym_block lowerAddRun := symRun {noAlias:=true} lowerAddCode (pcOf 43020) 6
sym_block lowerFloorJumpRun := symRun {noAlias:=true} floorJumpCode (pcOf 43024) 2
sym_block lowerCreditJumpRun := symRun {noAlias:=true} lowerCreditJumpCode (pcOf 43028) 2
sym_block lowerBranchRun := symRun {noAlias:=true} lowerBranchCode (pcOf 43027) 2
sym_block lowerBadRun := symRun {noAlias:=true} lowerBadCode (pcOf 43029) 2
sym_block topBranchRun := symRun {noAlias:=true} topBranchCode (pcOf 43447) 2
sym_block topCr0Run := symRun {noAlias:=true} topCr0 (pcOf 43064) 4
sym_block topCr3Run := symRun {noAlias:=true} topCr3 (pcOf 43067) 2
sym_block topCr4Run := symRun {noAlias:=true} topCr4 (pcOf 43068) 3
sym_block topCr6Run := symRun {noAlias:=true} topCr6 (pcOf 43070) 2

structure Code (image : Image) : Prop where
  scoring : CanonicalReward.PrefixAt image 354
  floorJump : CodeAt image (pcOf 43024) floorJumpCode
  lowerBranch : CodeAt image (pcOf 43027) lowerBranchCode
  lowerJump : CodeAt image (pcOf 43028) lowerCreditJumpCode
  lowerBad : CodeAt image (pcOf 43029) lowerBadCode
  topBranch : CodeAt image (pcOf 43447) topBranchCode
  cr0 : CodeAt image (pcOf 43064) topCr0
  cr3 : CodeAt image (pcOf 43067) topCr3
  cr4 : CodeAt image (pcOf 43068) topCr4
  cr6 : CodeAt image (pcOf 43070) topCr6
  hooks : ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.Code image
  /-- R6 (EXP image swap): the top-trial kernel `K_ENTRY` at 49226 and the unpacker `U_ENTRY` at 49626. -/
  r6K : CodeAt image (pcOf 49226) R6.kCodeE
  r6U : CodeAt image (pcOf 49626) R6.uCode
theorem Code.r6 {image : Image} (h : Code image) : R6.R6KAt image 354 :=
  ⟨Or.inl rfl, h.r6K, h.r6U⟩

theorem lowerAdd_steps {image : Image} (hc : CodeAt image (pcOf 43020) lowerAddCode)
    (s : MachineState) (hp : s.pc=pcOf 43020) (a T S : Nat) (hs : S≤T)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hc8 : T-S<8) :
    ∃ t, Steps image s 4 4 t ∧ t.pc=pcOf 43024 ∧
      t.getReg .x20=BitVec.ofNat 64 (a+if T-S=6 then 1 else 0) ∧
      RegsExcept s t [.x20,.x28] ∧ Frame s t (fun _=>False) := by
  have hsub : s.getReg .x17-s.getReg .x25=BitVec.ofNat 64 (T-S) := by
    rw [h17,h25]
    conv_lhs => lhs; rw [← Nat.sub_add_cancel hs,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have hflag := Reward.eq_small (T-S) 6 hc8 (by decide) (by decide)
  change (if (BitVec.ofNat 64 (T-S)+18446744073709551610#64).ult 1#64 then 1#64 else 0#64)=
    BitVec.ofNat 64 (if T-S=6 then 1 else 0) at hflag
  refine ⟨_,symRun_sound lowerAddRun hc s hp (by simp [lowerAddRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · change s.getReg .x20+(if ((s.getReg .x17-s.getReg .x25)+18446744073709551610#64).ult 1#64 then 1#64 else 0#64)=_
    rw [hsub,hflag,h20,BitVec.ofNat_add]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A _ _; rfl

theorem lowerFloorJump_steps {image : Image} (hc : CodeAt image (pcOf 43024) floorJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 43024) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (choiceBase 354+17) ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerFloorJumpRun hc s hp (by simp [lowerFloorJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerCreditJump_steps {image : Image} (hc : CodeAt image (pcOf 43028) lowerCreditJumpCode)
    (s : MachineState) (hp : s.pc=pcOf 43028) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 46918 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerCreditJumpRun hc s hp (by simp [lowerCreditJumpRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerBranch_steps {image : Image} (hc : CodeAt image (pcOf 43027) lowerBranchCode)
    (s : MachineState) (hp : s.pc=pcOf 43027) (a floor : Nat) (ha : a<2^64) (hf : floor<2^64)
    (h20 : s.getReg .x20=BitVec.ofNat 64 a) (h28 : s.getReg .x28=BitVec.ofNat 64 floor) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=(if floor≤a then pcOf 43028 else pcOf 43029) ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerBranchRun hc s hp (by simp [lowerBranchRun.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult (s.getReg .x28) then _ else _)=_
    rw [h20,h28,ofNat_ult a floor ha hf]
    split_ifs <;> simp_all [E.eval] <;> omega
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem lowerBad_steps {image : Image} (hc : CodeAt image (pcOf 43029) lowerBadCode)
    (s : MachineState) (hp : s.pc=pcOf 43029) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 822 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lowerBadRun hc s hp (by simp [lowerBadRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem topBranch_steps {image : Image} (hc : CodeAt image (pcOf 43447) topBranchCode)
    (s : MachineState) (hp : s.pc=pcOf 43447) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 43064 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topBranchRun hc s hp (by simp [topBranchRun.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

theorem topCr0_steps {image : Image} (hc : CodeAt image (pcOf 43064) topCr0)
    (s : MachineState) (hp : s.pc=pcOf 43064) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc=(if s.getMem (BitVec.ofNat 64 FLAG)=0 then pcOf 43067 else pcOf 43068) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCr0Run hc s hp (by simp [topCr0Run.res,rv_simp,accessValid_iff,MEMORY_BYTES]),?_,?_,?_⟩
  · simp only [Result.toState_pc,topCr0Run.res,E.eval,CmpOp.eval,BinOp.eval]
    t3n []
    by_cases h : s.getMem (BitVec.ofNat 64 FLAG)=0
    · simp [FLAG] at h; simp [h]
    · simp [FLAG] at h; simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [topCr0Run.res,rv_simp] <;> rfl
  · intro A _ _; simp [topCr0Run.res,rv_simp]

theorem topCr3_steps {image : Image} (hc : CodeAt image (pcOf 43067) topCr3)
    (s : MachineState) (hp : s.pc=pcOf 43067) (a : Nat) (h20 : s.getReg .x20=BitVec.ofNat 64 a) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 43068 ∧ t.getReg .x20=BitVec.ofNat 64 (a+3) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCr3Run hc s hp (by simp [topCr3Run.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [topCr3Run.res,rv_simp,h20,BitVec.ofNat_add]
  · intro r hr; simp at hr; cases r <;> simp_all [topCr3Run.res,rv_simp] <;> rfl
  · intro A _ _; simp [topCr3Run.res,rv_simp]

theorem topCr4_steps {image : Image} (hc : CodeAt image (pcOf 43068) topCr4)
    (s : MachineState) (hp : s.pc=pcOf 43068) (a : Nat) (ha : a<2^64) (h20 : s.getReg .x20=BitVec.ofNat 64 a) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if 30≤a then pcOf 43070 else pcOf (choiceBase 354+3)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCr4Run hc s hp (by simp [topCr4Run.res,rv_simp]),?_,?_,?_⟩
  · change (if (s.getReg .x20).ult 30#64 then _ else _)=_
    rw [h20,ofNat_ult a 30 ha (by decide)]
    split_ifs <;> simp_all [E.eval,choiceBase] <;> omega
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A _ _; rfl

theorem topCr6_steps {image : Image} (hc : CodeAt image (pcOf 43070) topCr6)
    (s : MachineState) (hp : s.pc=pcOf 43070) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 46924 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound topCr6Run hc s hp (by simp [topCr6Run.res,rv_simp]),rfl,?_,?_⟩
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT LowerLUT
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1800000
set_option maxRecDepth 32768

theorem floor_steps {image : Image} (hC : SharedCounterHooks.Code image) (s : MachineState)
    (hp : s.pc=pcOf 46905) (lay : Layer) (hl : lay≠0) (hints : BitVec 16)
    (hh : hints.toNat<8000) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) :
    ∃ t n c, c≤17 ∧ Steps image s n c t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hintFloor hints lay) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  fin_cases lay
  · exact (hl rfl).elim
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor1_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,8,11,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor2_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,11,17,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor3_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,11,17,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩

/-- Lower reward with the path-aware bonus (`pa`, +4 when the LOW half `L` at `EOUT` is spare), floor from the
policy hints. -/
theorem lower_spec {image : Image} (hK : KernAt image 354 (Code image)) (s : MachineState) (lay : Layer) (hl : lay≠0)
    (v : Digest) (ht : Reward.LowerTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (L : BitVec 128) (hm0 : s.getMem (BitVec.ofNat 64 EOUT)=L.extractLsb' 0 64)
    (hm8 : s.getMem (BitVec.ofNat 64 (EOUT+8))=L.extractLsb' 64 64)
    (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
    (hints : BitVec 16) (hh : hints.toNat<8000) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) (hf : floor=hintFloor hints lay) :
    let a := partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)
    ∃ t n c, c≤(if floor≤a then 110 else 104) ∧ Steps image s n c t ∧
      t.pc=(if floor≤a then pcOf 787 else pcOf 822) ∧
      (floor≤a → t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 a) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t (CreditW lay) := by
  dsimp only
  have hC := hK.reward
  have ha0 : partialScore v 14+(if T-S=6 then 1 else 0)<2^60 := by have h := partial_bound v 14; split_ifs <;> omega
  have ha : partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)<2^64 := by
    split_ifs <;> omega
  have hfloor : floor<2^64 := by have := hintFloor_lt hints lay;omega
  have hlow : 1≤lay.val ∧ lay.val≤3 := by have := lay.isLt; have hn : lay.val≠0 := fun h=>hl (Fin.ext h);omega
  obtain ⟨u,su,pu,ux11,ux20,ru,fu⟩ := CanonicalReward.Lower.init_spec (Or.inl rfl) hC.scoring s hp
  obtain ⟨v1,sv,pv,vx,rv,fv⟩ := CanonicalReward.Lower.loop_spec (Or.inl rfl) hC.scoring u v
    (ht.frame fu (by simp)) pu ((ru.get (by decide)).trans h6) ((ru.get (by decide)).trans h7) ux11 ux20 14 (by omega)
  have had : CodeAt image (pcOf 43020) lowerAddCode := by
    have h := CanonicalReward.lower_slice hC.scoring 73 4 (by decide)
    convert h using 1 <;> rfl
  obtain ⟨v2,s2,p2,x2,r2,f2⟩ := lowerAdd_steps had v1 (by simpa [Reward.base] using pv) (partialScore v 14) T S hST vx
    (((ru.trans rv).get (by decide)).trans h17) (((ru.trans rv).get (by decide)).trans h25) hc
  obtain ⟨v3,s3,p3,r3,f3⟩ := lowerFloorJump_steps hC.floorJump v2 p2
  have f03 := ((fu.trans fv).trans f2).trans f3
  obtain ⟨kp,vp,sp,kple,pp,xp,rp,fp⟩ := pa_spec hK v3 p3 L (partialScore v 14+(if T-S=6 then 1 else 0)) (by omega)
    (by rw [f03.get (by decide) (by simp)]; exact hm0) (by rw [f03.get (by decide) (by simp)]; exact hm8)
    (by rw [r3.get (by decide),x2])
  obtain ⟨v4,n4,c4,hc4,s4,p4,x4,r4,f4⟩ := floor_steps hC.hooks vp (by simpa [paTarget] using pp) lay hl hints hh
    (by rw [rp.get (by decide),r3.get (by decide),r2.get (by decide),rv.get (by decide),ru.get (by decide),h8])
    (by rw [fp.get (by decide) (by simp),f03.get (by decide) (by simp),hm])
  have x20 : v4.getReg .x20=BitVec.ofNat 64 (partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)) := by
    rw [r4.get (by decide),xp]
  obtain ⟨v5,s5,p5,r5,f5⟩ := lowerBranch_steps hC.lowerBranch v4 p4 _ floor ha hfloor x20 (by simpa [hf] using x4)
  have rr := ((((ru.trans rv).trans r2).trans r3).trans rp).trans r4
  have ff := (f03.trans fp).trans f4
  by_cases hg : floor≤partialScore v 14+(if T-S=6 then 1 else 0)+(if T3.lowerSpare L then 4 else 0)
  · rw [if_pos hg] at p5
    obtain ⟨v6,s6,p6,r6,f6⟩ := lowerCreditJump_steps hC.lowerJump v5 p5
    obtain ⟨t,st,pt,mt,rt,ft⟩ := SharedCounterHooks.lowerCredit_steps hC.hooks.lowerCredit v6 p6 lay.val hlow
      (by rw [r6.get (by decide),r5.get (by decide),r4.get (by decide),rp.get (by decide),r3.get (by decide),
        r2.get (by decide),rv.get (by decide),ru.get (by decide),h8])
      _ (by rw [r6.get (by decide),r5.get (by decide),x20])
    refine ⟨t,_,_,?_,(((((((su.trans sv).trans s2).trans s3).trans sp).trans s4).trans s5).trans s6).trans st,
      by rw [if_pos hg]; exact pt,fun _=>mt,?_,?_⟩
    · rw [if_pos hg]; omega
    · exact ((rr.trans r5).trans r6).trans rt |>.mono (by decide)
    · exact ((ff.trans f5).trans f6).trans ft |>.mono (by
        intro A hA h; simp only [false_or] at h; subst A; exact creditAddr_mem lay)
  · rw [if_neg hg] at p5
    obtain ⟨t,st,pt,rt,ft⟩ := lowerBad_steps hC.lowerBad v5 p5
    refine ⟨t,_,_,?_,((((((su.trans sv).trans s2).trans s3).trans sp).trans s4).trans s5).trans st,
      by rw [if_neg hg]; exact pt,fun h=>False.elim (hg h),?_,?_⟩
    · rw [if_neg hg]; omega
    · exact (rr.trans r5).trans rt |>.mono (by decide)
    · exact (ff.trans f5).trans ft |>.mono (by simp [CreditW])

#print axioms lower_spec
end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace SigGolfCandidate.T3M.Search.CanonicalExpandHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT WCT9.CanonicalPolicy
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768

theorem lower_reward (lay : Layer) (hl : lay≠0) (v : Digest) (T S : Nat) (low : Bool) :
    LowerLUT.partialScore v 14+(if T-S=6 then 1 else 0)+(if low then 4 else 0)=
      credit lay low (lowDigits v++[T-S]) := by
  have h := LowerLUT.packed_reward lay hl v (T-S)
  rw [credit_lower hl]
  simp only [LowerLUT.partialScore,reward] at h ⊢
  omega

theorem lower_spec_credit {image : Image} (hK : KernAt image 354 (Code image)) (s : MachineState) (lay : Layer)
    (hl : lay≠0) (v : Digest) (ht : Reward.LowerTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (L : BitVec 128) (hm0 : s.getMem (BitVec.ofNat 64 EOUT)=L.extractLsb' 0 64)
    (hm8 : s.getMem (BitVec.ofNat 64 (EOUT+8))=L.extractLsb' 64 64)
    (T S floor : Nat) (h17 : s.getReg .x17=BitVec.ofNat 64 T)
    (h25 : s.getReg .x25=BitVec.ofNat 64 S) (hST : S≤T) (hc : T-S<8)
    (hints : BitVec 16) (hh : hints.toNat<8000) (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints.toNat) (hf : floor=hintFloor hints lay) :
    let low := decide (T3.lowerSpare L)
    let good := floor+WCT9.dispatchPenalty lay (lowDigits v++[T-S])≤pathReward lay low (lowDigits v++[T-S])
    ∃ t n c, c≤(if good then 110 else 104) ∧ Steps image s n c t ∧
      t.pc=(if good then pcOf 787 else pcOf 822) ∧
      (good → t.getMem (BitVec.ofNat 64 (creditAddr lay))=BitVec.ofNat 64 (credit lay low (lowDigits v++[T-S]))) ∧
      RegsExcept s t [.x10,.x11,.x20,.x28,.x29,.x30] ∧ Frame s t (CreditW lay) := by
  dsimp only
  have h := lower_spec hK s lay hl v ht hp h6 h7 L hm0 hm8 T S floor h17 h25 hST hc hints hh h8 hm hf
  have e := lower_reward lay hl v T S (decide (T3.lowerSpare L))
  have e' : (if T3.lowerSpare L then 4 else 0)=(if decide (T3.lowerSpare L) then 4 else 0) := by
    by_cases hs : T3.lowerSpare L <;> simp [hs]
  have hg : (floor+WCT9.dispatchPenalty lay (lowDigits v++[T-S])≤
      pathReward lay (decide (T3.lowerSpare L)) (lowDigits v++[T-S]))↔
      floor≤credit lay (decide (T3.lowerSpare L)) (lowDigits v++[T-S]) := by
    simp [credit,WCT9.dispatchPenalty,hl]
  dsimp only at h
  rw [e',e] at h
  simpa only [hg] using h

end SigGolfCandidate.T3M.Search.CanonicalExpandHooks

namespace ClaudeWCT.W9.Machine.Expand.SharedSearchCode
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_kernel (P : Prop) (hP : P) : KernAt Images.expandImage 354 P := by
  refine ⟨⟨?_,?_⟩,Or.inl rfl,?_,⟨?_,?_,?_⟩,?_,?_,?_,hP⟩
  all_goals apply codeAt_expand_current_chunk <;> decide +kernel
theorem reward_code_of_hooks (hH : SharedCounterHooks.Code Images.expandImage) :
    CanonicalExpandHooks.Code Images.expandImage := by
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,hH,?r6K,?r6U⟩
  case r6K => apply codeAt_expand_last <;> decide +kernel
  case r6U => apply codeAt_expand_last <;> decide +kernel
  all_goals apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_reward_code : CanonicalExpandHooks.Code Images.expandImage :=
  reward_code_of_hooks SharedCounterHooks.installed_code
theorem installed_searchKernel : KernAt Images.expandImage 354 (CanonicalExpandHooks.Code Images.expandImage) :=
  installed_kernel _ installed_reward_code
end ClaudeWCT.W9.Machine.Expand.SharedSearchCode

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : WCT9.LayerMsg
  ret : Nat
  floor : Nat
  hints : BitVec 16
def csT (lay : Layer) : Nat := if lay = 0 then 503 else 402
def csOk (lay : Layer) : Nat := if lay = 0 then 4096 else 4096
theorem capLimit_le (n : Nat) : capLimit n ≤ 2 ^ 22 := by unfold capLimit; split_ifs <;> omega
theorem capLimit_eq (lay : Layer) : capLimit lay.val = WCT9.searchLimit lay := by
  fin_cases lay <;> rfl
theorem length_filter_range (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    ((List.range n).filter fun i => decide (p i)).length = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]
/-- Path-aware producer reward test (`low` = the LOW half was selected). -/
def rewardOK (lay : Layer) (floor : Nat) (low : Bool) (ds : List Nat) : Prop :=
  floor + WCT9.dispatchPenalty lay ds ≤ WCT9.CanonicalPolicy.pathReward lay low ds
instance (lay : Layer) (floor : Nat) (low : Bool) (ds : List Nat) : Decidable (rewardOK lay floor low ds) := by
  unfold rewardOK; infer_instance
theorem reward_credit_le {lay : Layer} {floor : Nat} {low : Bool} {ds : List Nat}
    (h : rewardOK lay floor low ds) : floor ≤ WCT9.CanonicalPolicy.credit lay low ds := by
  unfold rewardOK WCT9.CanonicalPolicy.credit at *
  omega
theorem producerDecode_lower {lay : Layer} (hlz : lay≠0) (v : Digest) (floor c : Nat) (low : Bool) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode lay v=some ds) (hds : ds=lowDigits v++[c]) :
    WCT9.CanonicalPolicy.producerDecodeAt lay floor low v=
      if rewardOK lay floor low ds ∧ (lowDigits v++[c]).count 0≤5 ∧ Rank.rankOK v then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.producerZeroBound,WCT9.producerZeroMax,WCT9.producerRankBound,
    rewardOK,Rank.rankOK,Rank.rankFloor,WCT9.producerRankFloor,hlz,hds,filter_zero_count]

def cfFlag (_b : Nat) : Nat := 0
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (lay : Layer) (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨
    (DigW A ∨ (CanonicalExpandHooks.CreditW lay A ∨ A = FLAG))
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  hroute : A.tree * 2 ^ T3.height A.lay + A.leaf < 2 ^ 32
  x15 : A.tree = 0 ∨ s.getReg .x15 = BitVec.ofNat 64 (T3.height A.lay)
  m0 : s.getMem (BitVec.ofNat 64 ENC) = (left A.msg).extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = (left A.msg).extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  r48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = (right A.msg).extractLsb' 0 64
  r56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = (right A.msg).extractLsb' 64 64
  reward : Reward.LowerTablesOK s
  floorLt : A.floor<20
  floorTop : A.lay=0 → A.floor=R6.kFloor
  hintsLt : A.hints.toNat<8000
  floorEq : A.floor=CanonicalExpandHooks.hintFloor A.hints A.lay
  floorMem : s.getMem (0x66000#64)=BitVec.ofNat 64 A.hints.toNat
  /-- R6: the packed top tables, copied to RAM 0xA0000 by KCOPY right before the top search. -/
  r6table : A.lay=0 → R6.R6TableW (R6.tblBlk b) s
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (capBase b)
  hi : i ≤ capLimit A.lay.val
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t (CsW A.lay)
def DummyOut (A : CsArgs) (s0 t : MachineState) : Prop :=
  t.pc = pcOf A.ret ∧
    (∀ j < 54, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (T3.dummyTop.getD j 0)) ∧
    (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s0 t csRegs ∧ Frame s0 t (CsW A.lay) ∧
    (t.getReg .x25).toNat ≤ 129
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) :
    Option (BitVec 32 × List Nat × Bool) → MachineState → Prop
  | none, t => t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds, low), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, WCT9.CanonicalPolicy.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t (CsW A.lay) ∧
      (A.lay ≠ 0 → (t.getReg .x25).toNat ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) ∧
      t.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds) ∧
      A.floor ≤ WCT9.CanonicalPolicy.credit A.lay low ds ∧
      (A.lay=0 → t.getMem (BitVec.ofNat 64 FLAG)=BitVec.ofNat 64 (if low then 0 else 128))
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = rowLo A.lay A.tree A.leaf
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 1
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u (CsW A.lay)
theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem TrialSt.stepCredit {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat}
    (h : TrialSt b A s0 i u) {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r=>decide (r∈csRegs ∧ r≠.x19))=true)
    (hf : Frame u u' (CanonicalExpandHooks.CreditW A.lay)) : TrialSt b A s0 i u' := by
  have hL' : ∀ r∈L, r∈csRegs ∧ r≠.x19 := fun r hr=>by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr.get (fun h'=>(hL' _ h').2 rfl),h.x19]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.h16]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.h24]
  · rw [hf.get (by unfold ENC;omega) (by unfold CanonicalExpandHooks.CreditW ENC;omega),h.c32]
  · exact (h.regs.trans hr).mono (fun r hr'=>by rcases List.mem_append.1 hr' with h1|h1;exact h1;exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h'=>by
      rcases h' with h'|h';exact h';exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))
theorem TrialSt.stepFlag {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat}
    (h : TrialSt b A s0 i u) {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r=>decide (r∈csRegs ∧ r≠.x19))=true)
    (hf : Frame u u' (fun A => A = FLAG)) : TrialSt b A s0 i u' := by
  have hL' : ∀ r∈L, r∈csRegs ∧ r≠.x19 := fun r hr=>by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr.get (fun h'=>(hL' _ h').2 rfl),h.x19]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.h16]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.h24]
  · rw [hf.get (by unfold ENC;omega) (by unfold FLAG ENC;omega),h.c32]
  · exact (h.regs.trans hr).mono (fun r hr'=>by rcases List.mem_append.1 hr' with h1|h1;exact h1;exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h'=>by
      rcases h' with h'|h';exact h';exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))))
theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr
/-- A step that writes only inside `CsW`, away from the counter cells. -/
theorem TrialSt.stepW {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L) (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true)
    {W : Nat → Prop} (hf : Frame u u' W) (hW : ∀ X, W X → CsW A.lay X)
    (hC : ∀ X, W X → X ≠ ENC + 16 ∧ X ≠ ENC + 24 ∧ X ≠ ENC + 32) : TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by unfold ENC; omega) (fun hw => (hC _ hw).1 rfl), h.h16]
  · rw [hf.get (by unfold ENC; omega) (fun hw => (hC _ hw).2.1 rfl), h.h24]
  · rw [hf.get (by unfold ENC; omega) (fun hw => (hC _ hw).2.2 rfl), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun X _ h' => by rcases h' with h' | h'; exact h'; exact hW X h')
section trial
variable {image : Image} {b : Nat} {sk : BitVec 256}
theorem cs_next {A : CsArgs} {s0 u : MachineState} {i F W : Nat} {Q : Option (BitVec 32 × List Nat × Bool) → MachineState → Prop}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 468)) (hi : i < capLimit A.lay.val)
    (ih : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t W (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i + 1) F) Q) :
    TBSim image sk u (2 + W) (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i + 1) F) Q := by
  obtain ⟨t1, s1, p1, h19, r1, f1⟩ := cs468_spec hK u hpc i hu.x19
  have hcap := capLimit_le A.lay.val
  refine TBSim.steps s1 (ih t1 ⟨p1, by omega, h19, ?_, ?_, ⟨i, by omega, ?_⟩, ?_, ?_⟩)
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h16]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h24]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.c32]
  · exact (hu.regs.trans r1).mono (by decide)
  · exact (hu.frame.trans f1).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 52 else 43 := by
  fin_cases lay <;> rfl

theorem target_lt (lay : Layer) : T3.target lay < 2 ^ 63 := by
  fin_cases lay <;> decide
theorem getD_map_range {f : Nat → Nat} {n j : Nat} (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]
structure RewardReady (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (ds : List Nat) (low : Bool)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf A.ret
  trial : TrialSt b A s0 i t
  len : ds.length=T3.chainCount A.lay
  digs : ∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (ds.getD j 0)
  sum : A.lay ≠ 0 → (t.getReg .x25).toNat ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)
  credit : t.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds)
theorem cs_success {A : CsArgs} {s0 u : MachineState} {i : Nat} {ds : List Nat} {low : Bool}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0) (hu : RewardReady b A s0 i ds low u)
    (hi : i < capLimit A.lay.val) (answer : Digest) (hdec : WCT9.CanonicalPolicy.decode A.lay answer = some ds)
    (hfloor : A.floor ≤ WCT9.CanonicalPolicy.credit A.lay low ds)
    (hflag : A.lay=0 → u.getMem (BitVec.ofNat 64 FLAG)=BitVec.ofNat 64 (if low then 0 else 128)) :
    TBSim image sk u 0 (pure (some (BitVec.ofNat 32 i,ds,low))) (CsPost image b A s0) := by
  have hcap := capLimit_le A.lay.val
  have hc : (BitVec.ofNat 32 i).toNat=i := by rw [BitVec.toNat_ofNat]; omega
  refine TBSim.pure ⟨hu.pc,?_,?_,?_,⟨answer,hdec⟩,hu.len,hu.digs,hu.trial.regs,hu.trial.frame,hu.sum,hu.credit,hfloor,hflag⟩
  · rw [hc]; omega
  · rw [hc]; exact hu.trial.x19
  · rw [hc]; exact hu.trial.c32

theorem cs_prepare {A : CsArgs} {s0 u : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 433)) (hi : i < 2 ^ 22) (hlz : A.lay ≠ 0)
    (v : Digest) (hv : T3.lowerSpare v) (S : Nat) (ds : List Nat) (hdec : WCT9.CanonicalPolicy.decode A.lay v = some ds)
    (hds : ds = lowDigits v ++ [T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) - S]) (hS : S ≤ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h25 : u.getReg .x25 = BitVec.ofNat 64 S) (low : Bool)
    (hcredit : u.getMem (BitVec.ofNat 64 (CanonicalExpandHooks.creditAddr A.lay))=BitVec.ofNat 64 (WCT9.CanonicalPolicy.credit A.lay low ds)) :
    ∃ k t, Steps image u k k t ∧ k ≤ 815 ∧ RewardReady b A s0 i ds low t := by
  have hl0 : A.lay.val ≠ 0 := fun h => hlz (Fin.ext h)
  obtain ⟨u1, su1, pu1, a6, a7, ru1, fu1⟩ := Credit.align_spec hK u hpc v hv h6 h7
  have hu1 := hu.step ru1 (by decide) fu1
  obtain ⟨k, t, st, kle, tpc, tdig, tchk, tr, tf⟩ := cs_tail hK u1 pu1 (BitVec.ofNat 128 (T3.lowerWord v)) A.lay.val
    (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) S A.ret A.lay.isLt (target_lt _) (fun _ => hS)
    (by rw [hu1.reg (by decide), hpre.x1]) (by rw [hu1.reg (by decide), hpre.x8])
    (by rw [hu1.reg (by decide), hpre.x17]) (by rw [ru1.get (by decide), h25])
    (by rw [hu1.reg (by decide), hpre.x26, chainCount_eq]; simp [hlz, hl0])
    (by rw [hu1.reg (by decide), hpre.x27, csN4]; simp [hlz, hl0]) a6 a7
  rw [if_neg hl0] at kle tdig
  have hfr := (hu1.frame.trans tf).mono (fun A _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have hregs : RegsExcept s0 t csRegs := (hu1.regs.trans tr).mono (by decide)
  refine ⟨5+k,t,su1.trans st,by omega,?_,?_,?_,?_,?_,?_⟩
  · simpa [hlz] using tpc
  · refine ⟨?_,?_,?_,?_,hregs,hfr⟩
    · rw [tr.get (by decide),hu1.x19]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.h16]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.h24]
    · rw [tf.get (by unfold ENC; omega) (by unfold DigW DIGITS ENC; omega),hu1.c32]
  · rw [hds,chainCount_eq,if_neg hlz]; simp [lowDigits_length]
  · intro j hj
    rw [chainCount_eq,if_neg hlz] at hj
    rw [hds]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length];exact hj),lowDigits_eq,getD_map_range hj]
      simpa only [if_neg hl0] using tdig j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [lowDigits_length]),lowDigits_length]
      simpa using tchk hl0
  · intro _
    rw [tr.get (by decide),ru1.get (by decide),h25,BitVec.toNat_ofNat]
    have := target_lt (WCT9.CanonicalPolicy.normalLayer A.lay)
    omega
  · rw [tf.get (CanonicalExpandHooks.creditAddr_lt _) (by unfold CanonicalExpandHooks.creditAddr DigW DIGITS;omega),fu1.get (CanonicalExpandHooks.creditAddr_lt _) (by simp),hcredit]
theorem TrialSt.reward {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : Reward.LowerTablesOK s0) : Reward.LowerTablesOK u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < capLimit A.lay.val) :
    ∃ k t2, Steps image t k k t2 ∧ k ≤ (if A.lay = 0 then 14 else 12) ∧ t2.pc = pcOf (b + 123) ∧
      fetch image t2 = some (.base .ECALL) ∧
      t2.getReg .x5 = 0 ∧ hashArgumentsValid t2 = true ∧
      hashInput t2 = toQ (T3.pad64 (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i))) ∧
      t2.getReg .x12 = BitVec.ofNat 64 EOUT ∧ TrialSt b A s0 i t2 := by
  have hcap := capLimit_le A.lay.val
  obtain ⟨k1, t1, s1, k1le, p1, r1, f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide), hpre.x8]) hI.x19
  rw [if_neg (by omega)] at p1
  obtain ⟨x, hx, hx32⟩ := hI.c32
  obtain ⟨t2, s2, p2, c32, h10, h11, h12, r2, f2⟩ := cs115_spec hK t1 p1 i x (by omega) hx
    (by rw [r1.get (by decide), hI.x19]) (by rw [f1.get (by simp only [ENC]; omega) (by simp), hx32])
  have fr : Frame s0 t2 (CsW A.lay) := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
    simp only [or_false] at h; rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h)))
  have mem : ∀ addr, addr < 2 ^ 64 → ¬ CsW A.lay addr → t2.getMem (BitVec.ofNat 64 addr) = s0.getMem (BitVec.ofNat 64 addr) :=
    fun addr hA hn => fr.get hA hn
  have hT : TrialSt b A s0 i t2 := by
    refine ⟨?_, ?_, ?_, c32, ((hI.regs.trans r1).trans r2).mono (by decide), fr⟩
    · rw [r2.get (by decide), r1.get (by decide), hI.x19]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h16]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h24]
  have hk : k1 + 8 ≤ (if A.lay = 0 then 14 else 12) := by
    have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩
    by_cases h : A.lay = 0
    · rw [if_pos (hl0.2 h)] at k1le; rw [if_pos h]; omega
    · rw [if_neg (fun h' => h (hl0.1 h'))] at k1le; rw [if_neg h]; omega
  refine ⟨_, t2, s1.trans s2, hk, p2, (codeAt_k_123 hK).fetch _ p2, by rw [hT.reg (by decide), hpre.x5],
    hashArgs_const t2 ENC 64 EOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, h12, hT⟩
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine hashInput_toQ t2 _ 0 ENC (BC.encodingInput_length _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [readWords_eight, BC.wordsOf_encodingInput, hc]
  have nw : ∀ addr, addr = ENC ∨ addr = ENC + 8 ∨ addr = ENC + 40 ∨ addr = ENC + 48 ∨ addr = ENC + 56 → ¬ CsW A.lay addr := by
    intro A hA; simp only [CsW, CanonicalExpandHooks.CreditW, DigW, ENC, EOUT, DIGITS, FLAG] at hA ⊢; omega
  rw [mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hT.h16, hT.h24, c32, mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hpre.m0, hpre.m8, hpre.z40, hpre.r48, hpre.r56]
theorem TrialSt.hash {A : CsArgs} {s0 t2 : MachineState} {i : Nat} (hT : TrialSt b A s0 i t2)
    (h12 : t2.getReg .x12 = BitVec.ofNat 64 EOUT) (a : BitVec 256) : TrialSt b A s0 i (writeHash t2 a) := by
  have fw := Frame.writeHash t2 a EOUT h12 (by decide)
  refine ⟨by rw [getReg_writeHash, hT.x19], ?_, ?_, ?_, ?_, ?_⟩
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h16]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h24]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.c32]
  · intro r hr; rw [getReg_writeHash]; exact hT.regs r hr
  · exact (hT.frame.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem cfFlag_lt (b : Nat) : cfFlag b < 256 := by change 0<256;decide
/-- R6 expand: counter exhaustion rejects on every layer (`354 + 425` is `j 354`; no dummy word). -/
theorem exhaust354 {rewardCondition : Prop} (hK : KernAt image 354 rewardCondition) (s : MachineState)
    (hpc : s.pc = pcOf (354 + 424)) (lay : Nat) (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ n t, n ≤ 2 ∧ Steps image s n n t ∧ t.pc = pcOf (354 + 0) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ := Credit.h0_spec hK s hpc lay hl h8
  by_cases hz : lay = 0
  · rw [if_pos hz] at p0
    obtain ⟨t1, s1, p1, r1, f1⟩ := Credit.jrej354_spec hK t0 p0
    exact ⟨2, t1, le_rfl, (s0.trans s1).of_eq (by norm_num) (by norm_num), p1, (r0.trans r1).mono (by decide),
      (f0.trans f1).mono (by simp)⟩
  · rw [if_neg hz] at p0
    exact ⟨1, t0, by omega, s0, p0, r0.mono (by decide), f0⟩
theorem cs_exhaust {A : CsArgs} {s0 t : MachineState} {i : Nat}
    {rewardCondition : Prop} (hK : KernAt image 354 rewardCondition) (hpre : CsPre 354 A s0)
    (hI : CsInv 354 A s0 i t) (hi : i=capLimit A.lay.val) :
    TBSim image sk t (0*csT A.lay+csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i 0)
      (CsPost image 354 A s0) := by
  obtain ⟨k1,t1,s1,k1le,p1,r1,f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide),hpre.x8]) hI.x19
  rw [if_pos hi] at p1
  have hk1 : k1≤6 := by split_ifs at k1le <;> omega
  have h8 : t1.getReg .x8=BitVec.ofNat 64 A.lay.val := by
    rw [r1.get (by decide),hI.regs.get (by decide),hpre.x8]
  obtain ⟨n,t2,hn,s2,p2,r2,f2⟩ := exhaust354 hK t1 p1 A.lay.val A.lay.isLt h8
  obtain ⟨t3,s3,p3,h5,h10,hf⟩ := cs0_spec hK t2 p2
  change TBSim image sk t _ (pure none) _
  refine (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure ?_)).mono ?_ (fun _ _ h=>h)
  · exact ⟨p3,h5,h10,hf⟩
  · unfold csOk;split_ifs <;> omega

end trial
end SigGolfCandidate.T3M.Search.CanonicalExpand

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
variable {image : Image} {sk : BitVec 256}
theorem cs_loop {A : CsArgs} {s0 : MachineState} (hK : KernAt image 354 (CanonicalExpandHooks.Code image)) (hpre : CsPre 354 A s0) :
    ∀ F i t, i + F = capLimit A.lay.val → CsInv 354 A s0 i t →
      TBSim image sk t (F * csT A.lay + csOk A.lay) (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i F)
        (CsPost image 354 A s0) := by
  have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := ⟨fun h => Fin.ext h,fun h => by rw [h];rfl⟩
  have hcap := capLimit_le A.lay.val
  intro F
  induction F with
  | zero =>
    intro i t h hI
    exact cs_exhaust hK hpre hI (by omega)
  | succ F ih =>
    intro i t h hI
    have hi : i < capLimit A.lay.val := by omega
    have hi22 : i < 2 ^ 22 := by omega
    obtain ⟨k2,t2,s2,k2le,p2,hf,h5,hv,hq,h12,hT⟩ := cs_answer hK hpre hI hi
    have prog : WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i (F+1) =
        (T3.publicHash (WCT9.layerEncodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i)) >>= fun answer =>
          match WCT9.CanonicalPolicy.producerDecodeOut A.lay A.floor answer with
          | none => WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i+1) F
          | some found => pure (some (BitVec.ofNat 32 i,found))) := rfl
    have ih' : ∀ t, CsInv 354 A s0 (i+1) t → TBSim image sk t (F*csT A.lay+csOk A.lay)
        (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg (i+1) F) (CsPost image 354 A s0) :=
      fun t ht => ih (i+1) t (by omega) ht
    rw [prog]
    refine (TBSim.steps s2 (TBSim.publicHash_bindC hf h5 hv hq
      (W:=F*csT A.lay+csOk A.lay+(csT A.lay-(if A.lay=0 then 22 else 20))) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [BC.blocks_encodingInput,Nat.succ_mul];unfold csT at *;split_ifs at k2le ⊢ <;> omega
    have hT3 := hT.hash h12 a
    have p3 : (writeHash t2 a).pc=pcOf (354+124) := by rw [pc_writeHash,p2,pcOf_add4]
    have hd := DigAt.writeHash_lo t2 a EOUT h12 (by decide)
    have hhi := DigAt.writeHash_hi t2 a EOUT h12 (by decide)
    obtain ⟨t4,s4,p4,h6,h7,h25,r4,f4⟩ := cs124_spec hK (writeHash t2 a) p3 A.lay.val A.lay.isLt
      (by rw [hT3.reg (by decide),hpre.x8])
    rw [hd.1] at h6
    rw [hd.2] at h7
    have hT4 := hT3.step r4 (by decide) f4
    -- the answer halves stay in `EOUT .. EOUT + 32` (frames below never write there)
    have mL0 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 EOUT) = t4.getMem (BitVec.ofNat 64 EOUT) →
        w.getMem (BitVec.ofNat 64 EOUT) = (a.extractLsb' 0 128).extractLsb' 0 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hd.1
    have mL8 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+8)) = t4.getMem (BitVec.ofNat 64 (EOUT+8)) →
        w.getMem (BitVec.ofNat 64 (EOUT+8)) = (a.extractLsb' 0 128).extractLsb' 64 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hd.2
    have mH0 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+16)) = t4.getMem (BitVec.ofNat 64 (EOUT+16)) →
        w.getMem (BitVec.ofNat 64 (EOUT+16)) = (a.extractLsb' 128 128).extractLsb' 0 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hhi.1
    have mH8 : ∀ w : MachineState, w.getMem (BitVec.ofNat 64 (EOUT+24)) = t4.getMem (BitVec.ofNat 64 (EOUT+24)) →
        w.getMem (BitVec.ofNat 64 (EOUT+24)) = (a.extractLsb' 128 128).extractLsb' 64 64 := by
      intro w hw; rw [hw,f4.get (by unfold EOUT;omega) (by simp)]; exact hhi.2
    by_cases hlz : A.lay=0
    · rw [if_pos (hl0.2 hlz)] at p4
      have hfl : A.floor = R6.kFloor := hpre.floorTop hlz
      have e : WCT9.CanonicalPolicy.producerDecodeOut A.lay A.floor a =
          WCT9.CanonicalPolicy.producerDecodeOut 0 R6.kFloor a := by rw [hlz,hfl]
      rw [e]
      -- R6: `tcEntry 354` (1272) jumps to the R6 kernel `K_ENTRY` (49226)
      obtain ⟨tg,sg,pg,rg,fg⟩ := top_entry_spec hK t4 p4
      have hTg := hT4.step rg (by decide) fg
      have hR : R6.R6KAt image 354 := CanonicalExpandHooks.Code.r6 hK.2.2.2.2.2.2.2
      have fgE : ∀ X, X < 2^64 → tg.getMem (BitVec.ofNat 64 X) = t4.getMem (BitVec.ofNat 64 X) :=
        fun X hX => fg.get hX (by simp)
      have h6g : tg.getReg .x6 = (a.extractLsb' 0 128).extractLsb' 0 64 := by rw [rg.get (by decide),h6]
      have h7g : tg.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64 := by rw [rg.get (by decide),h7]
      have h12g : tg.getReg .x12 = BitVec.ofNat 64 EOUT := by
        rw [rg.get (by decide),r4.get (by decide),getReg_writeHash,h12]
      have h17g : tg.getReg .x17 = BitVec.ofNat 64 (T3.target 0) := by
        rw [hTg.reg (by decide),hpre.x17,hlz]; rfl
      have htg : R6.R6TableW (R6.tblBlk 354) tg := (hpre.r6table hlz).frame hTg.frame (by decide)
        (by intro k hk; rw [R6.tblBlk_354]; unfold CsW CanonicalExpandHooks.CreditW CanonicalExpandHooks.creditAddr DigW ENC EOUT DIGITS FLAG; omega)
      obtain ⟨hAcc,hRej⟩ := R6.trial hR R6.topFloor_rc tg (by rw [pg]; rfl) a h6g h7g h12g
        (mH0 tg (fgE _ (by unfold EOUT;omega))) (mH8 tg (fgE _ (by unfold EOUT;omega))) h17g htg
      cases hD : WCT9.CanonicalPolicy.producerDecodeOut 0 R6.kFloor a with
      | some found =>
        obtain ⟨ds,low⟩ := found
        obtain ⟨k,t,st,kle,pt,t6,t7,hdec,t28,tcr,tfl,rt,ft⟩ := hAcc ds low hD
        have hcw : ∀ X, (X = R6.creditAddr 354 ∨ X = R6.FLAGA) → CsW A.lay X := fun X hX => by
          rcases hX with hX | hX
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            rw [hlz, hX, R6.creditAddr_354]; exact CanonicalExpandHooks.creditAddr_mem 0
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hX)))))
        have hTt := hTg.stepW rt (by decide) ft hcw
          (fun X hX => by rcases hX with rfl | rfl <;> decide)
        obtain ⟨t',st',pt',tdig,rt',ft'⟩ := R6.unpack hR t pt _ ds hdec t6 t7 t28
        have hTt' := hTt.stepW rt' (by decide) ft' (fun X hX => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX)))))
          (fun X hX => by unfold ENC DIGITS at *; omega)
        have hret : t.getReg .x1 = pcOf A.ret := by rw [hTt.reg (by decide),hpre.x1]
        have hlen : ds.length = T3.chainCount A.lay := by
          rw [hlz]; exact R6.decode_length hdec
        have hca : CanonicalExpandHooks.creditAddr A.lay = 0x66040 := by rw [hlz]; rfl
        have hR' : RewardReady 354 A s0 i ds low t' := by
          refine ⟨?_,hTt',hlen,?_,fun h => absurd hlz h,?_⟩
          · rw [pt',hret]; exact pcOf_and_not1 _
          · intro j hj; rw [hlz] at hj; exact tdig j hj
          · rw [hca, ft'.get (by decide) (by unfold DIGITS; omega)]
            rw [R6.creditAddr_354] at tcr; rw [hlz]; exact tcr
        have done := cs_success (sk:=sk) hK hpre hR' hi _ (by rw [hlz]; exact hdec)
          (by rw [hfl,hlz]; exact R6.producerDecodeOut_floor hD)
          (fun _ => by rw [ft'.get (by decide) (by unfold DIGITS FLAG; omega)]; exact tfl)
        refine (TBSim.steps ((s4.trans sg).trans (st.trans st')) done).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_pos hlz];omega
      | none =>
        obtain ⟨k,t,st,kle,pt,rt,ft⟩ := hRej hD
        have hTt := hTg.step rt (by decide) ft
        refine (TBSim.steps ((s4.trans sg).trans st) (cs_next hK hTt pt hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_pos hlz];omega
    · rw [if_neg (fun h => hlz (hl0.1 h))] at p4
      set v := WCT9.encodingAnswer A.lay a with hvdef
      set low := decide (T3.lowerSpare (a.extractLsb' 0 128)) with hlowdef
      have hlow : WCT9.lowSelected A.lay a = low := by simp [WCT9.lowSelected,hlz,hlowdef]
      unfold WCT9.CanonicalPolicy.producerDecodeOut
      rw [hlow]
      obtain ⟨td,sd,pd,rd,fd⟩ := cs130_spec hK t4 p4
      have hTd := hT4.step rd (by decide) fd
      obtain ⟨ks,t5,ss,hs7,p5,h6s,h7s,r5,f5⟩ := selector_spec hK td pd a A.lay hlz
        ((rd.get (by decide)).trans h6) ((rd.get (by decide)).trans h7)
        (by rw [rd.get (by decide),r4.get (by decide),getReg_writeHash,h12])
        (by rw [fd.get (by unfold EOUT;omega) (by simp),f4.get (by unfold EOUT;omega) (by simp)];exact hhi.1)
        (by rw [fd.get (by unfold EOUT;omega) (by simp),f4.get (by unfold EOUT;omega) (by simp)];exact hhi.2)
      have s5 := sd.trans ss
      have hT5 := hTd.step r5 (by decide) f5
      change t5.pc=(if T3.lowerSpare v then _ else _) at p5
      change t5.getReg .x6=v.extractLsb' 0 64 at h6s
      change t5.getReg .x7=v.extractLsb' 64 64 at h7s
      have hnormal : WCT9.CanonicalPolicy.normalLayer A.lay≠0 := by
        simp [WCT9.CanonicalPolicy.normalLayer,hlz]
      have hdec := decode_low (WCT9.CanonicalPolicy.normalLayer A.lay) hnormal v
      change WCT9.CanonicalPolicy.decode A.lay v=_ at hdec
      by_cases hr : T3.lowerSpare v
      · rw [if_pos hr] at p5
        obtain ⟨t6,s6,p6,h25',h28',r6,f6⟩ := cs132_spec hK t5 p5 v (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) (target_lt _) h6s h7s
          (by rw [r5.get (by decide),rd.get (by decide),h25]) (by rw [hT5.reg (by decide),hpre.x17])
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : (lowDigits v).sum≤T3.target (WCT9.CanonicalPolicy.normalLayer A.lay) ∧ T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum<8
        · rw [if_pos hs] at p6
          obtain ⟨t7,s7,p7,r7,f7⟩ := cs259_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          have hd' : WCT9.CanonicalPolicy.decode A.lay v=some (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) := by rw [hdec,if_pos ⟨hr,hs⟩]
          rw [producerDecode_lower hlz v A.floor _ low hd' rfl]
          obtain ⟨k8,n8,t8,s8,n8le,p8,r8,f8⟩ := zero_rank_spec hK t7 p7 v (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay))
            (by
              have h : ∀ lay : T3.Layer,T3.target lay<256 := by decide
              exact h (WCT9.CanonicalPolicy.normalLayer A.lay)) hs.1
            (by rw [r7.get (by decide),r6.get (by decide),h6s])
            (by rw [r7.get (by decide),r6.get (by decide),h7s])
            (by rw [hT7.reg (by decide),hpre.x17]) (by rw [r7.get (by decide),h25'])
            (lowZeros_bound v (by
              have hmin : ∀ lay : T3.Layer,lay≠0 → 199≤T3.target lay := by decide
              have ht := hmin (WCT9.CanonicalPolicy.normalLayer A.lay) hnormal;omega))
          have hT8 := hT7.step r8 (by decide) f8
          have fL8 : Frame t4 t8 (fun _ => False) := ((((((fd.trans f5).trans f6).trans f7).trans f8)).mono
            (fun A _ h => by simp at h))
          by_cases hok : (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]).count 0≤5 ∧ Rank.rankOK v
          · rw [if_pos hok] at p8
            have hTables : Reward.LowerTablesOK t8 := hpre.reward.frame hT8.frame
              (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
            obtain ⟨tR,nR,cR,hcR,sR,pR,mR,rR,fR⟩ := CanonicalExpandHooks.lower_spec_credit hK t8 A.lay hlz v hTables p8
              (by rw [r8.get (by decide),r7.get (by decide),r6.get (by decide),h6s])
              (by rw [r8.get (by decide),r7.get (by decide),r6.get (by decide),h7s])
              (a.extractLsb' 0 128) (mL0 t8 (fL8.get (by decide) (by simp))) (mL8 t8 (fL8.get (by decide) (by simp)))
              (T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)) (lowDigits v).sum A.floor
              (by rw [hT8.reg (by decide),hpre.x17])
              (by rw [r8.get (by decide),r7.get (by decide),h25']) hs.1 hs.2 A.hints hpre.hintsLt
              (by rw [hT8.reg (by decide),hpre.x8])
              (by rw [hT8.frame.get (by decide) (by unfold CsW CanonicalExpandHooks.CreditW ENC EOUT DigW DIGITS FLAG;omega),hpre.floorMem])
              hpre.floorEq
            have hTR := hT8.stepCredit rR (by decide) fR
            change tR.pc=(if rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum])
              then pcOf (354+433) else pcOf (354+468)) at pR
            change cR≤(if rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) then 110 else 104) at hcR
            change (rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) → _) at mR
            by_cases hreward : rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum])
            · rw [if_pos hreward] at pR hcR
              simp only [hreward,hok,and_self,if_true]
              obtain ⟨k9,t9,s9,k9le,hR⟩ := cs_prepare hK hpre hTR pR hi22 hlz v hr _ _ hd' rfl hs.1
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),r6.get (by decide),h6s])
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),r6.get (by decide),h7s])
                (by rw [rR.get (by decide),r8.get (by decide),r7.get (by decide),h25']) low (mR hreward)
              have done := cs_success (sk:=sk) hK hpre hR hi v hd' (reward_credit_le hreward) (fun h => absurd h hlz)
              refine (TBSim.steps ((((((s4.trans s5).trans s6).trans s7).trans s8).trans sR).trans s9) done).mono ?_ (fun _ _ h => h)
              simp only [csT,csOk,if_neg hlz];omega
            · rw [if_neg hreward] at pR hcR
              simp only [hreward,false_and,if_false]
              refine (TBSim.steps (((((s4.trans s5).trans s6).trans s7).trans s8).trans sR)
                (cs_next hK hTR pR hi ih')).mono ?_ (fun _ _ h => h)
              simp only [csT,csOk,if_neg hlz];omega
          · rw [if_neg hok] at p8
            have hno : ¬ (rewardOK A.lay A.floor low (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]) ∧
                (lowDigits v++[T3.target (WCT9.CanonicalPolicy.normalLayer A.lay)-(lowDigits v).sum]).count 0≤5 ∧ Rank.rankOK v) := fun hh => hok hh.2
            simp only [if_neg hno]
            refine (TBSim.steps ((((s4.trans s5).trans s6).trans s7).trans s8) (cs_next hK hT8 p8 hi ih')).mono ?_ (fun _ _ h => h)
            simp only [csT,csOk,if_neg hlz];omega
        · rw [if_neg hs] at p6
          have hd' : WCT9.CanonicalPolicy.decode A.lay v=none := by rw [hdec,if_neg (fun h => hs h.2)]
          have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor low v=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
          rw [hpd]
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          simp only [csT,csOk,if_neg hlz];omega
      · rw [if_neg hr] at p5
        have hd' : WCT9.CanonicalPolicy.decode A.lay v=none := by rw [hdec,if_neg (fun h => hr h.1)]
        have hpd : WCT9.CanonicalPolicy.producerDecodeAt A.lay A.floor low v=none := by simp [WCT9.CanonicalPolicy.producerDecodeAt,hd']
        rw [hpd]
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_neg hlz];omega
end SigGolfCandidate.T3M.Search.CanonicalExpand

namespace SigGolfCandidate.T3M.Search.CanonicalExpand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT BC
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
variable {image : Image} {sk : BitVec 256}
theorem counterSearch_tbsim {A : CsArgs} {s0 : MachineState} (hK : KernAt image 354 (CanonicalExpandHooks.Code image)) (hpre : CsPre 354 A s0) :
    TBSim image sk s0 (18 + capLimit A.lay.val * csT A.lay + csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay)) (CsPost image 354 A s0) := by
  obtain ⟨t, st, pt, h16, h24, h19, rt, ft⟩ := cs103_spec hK s0 hpre.pc A.lay A.tree A.leaf hpre.hroute
    hpre.x8 hpre.x9 hpre.x18 hpre.x15
  obtain ⟨t', st', pt', rt', ft'⟩ := cs113_spec hK t pt
  have hI : CsInv 354 A s0 0 t' := by
    refine ⟨pt', Nat.zero_le _, by rw [rt'.get (by decide), h19], by rw [ft'.get (by simp only [ENC]; omega) (by simp), h16],
      by rw [ft'.get (by simp only [ENC]; omega) (by simp), h24], ?_,
      (rt.trans rt').mono (by decide), (ft.trans ft').mono (fun A _ h => by
        rcases h with h | h
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact absurd h id)⟩
    obtain ⟨x, hx, hx32⟩ := hpre.c32
    exact ⟨x, hx, by rw [ft'.get (by simp only [ENC]; omega) (by simp), ft.get (by simp only [ENC]; omega)
      (by simp only [ENC]; omega), hx32]⟩
  rw [← capLimit_eq]
  have := TBSim.steps st (TBSim.steps st' (cs_loop (sk := sk) hK hpre (capLimit A.lay.val) 0 t' (by omega) hI))
  exact this.mono (le_of_eq (by ring)) (fun _ _ h => h)

def csCost (lay : Layer) : Nat := (if lay=0 then WCT9.topSearchLimit*503 else WCT9.lowerSearchLimit*402)+8192

theorem counterSearch_good {A : CsArgs} {s0 : MachineState}
    (hK : KernAt image 354 (CanonicalExpandHooks.Code image)) (hp : CsPre 354 A s0) :
    TBSim image sk s0 (csCost A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
      (CsPost image 354 A s0) := by
  refine (counterSearch_tbsim hK hp).mono ?_ (fun _ _ h=>h)
  have hl0 : (A.lay.val=0)↔A.lay=0 := ⟨fun h=>Fin.ext h,fun h=>by rw [h];rfl⟩
  unfold csCost capLimit csT csOk WCT9.topSearchLimit WCT9.lowerSearchLimit
  by_cases h : A.lay=0
  · rw [if_pos (hl0.2 h),if_pos h,if_pos h,if_pos h];norm_num
  · rw [if_neg (fun h'=>h (hl0.1 h')),if_neg h,if_neg h,if_neg h];norm_num
end SigGolfCandidate.T3M.Search.CanonicalExpand
#print axioms SigGolfCandidate.T3M.Search.CanonicalExpand.counterSearch_good

/-! ## KCOPY (R6 expand words 49795..49811)

Called from the top stage (`331 jal ra, 49795`): copies the packed R6 table block (expand data `TOP_DATA + 0..1023`
and `TOP_DATA + 2048..2719`) to RAM `0xA0000..0xA069F` and jumps to the counter search entry 457, where the R6
kernel reads it (`R6.R6TableW (R6.tblBlk 354)`). 1067 cycles, once per expand. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def headWords : List (BitVec 32) := [0xfffe37,0xa0eb7,0x400e0f13]
def loopWords : List (BitVec 32) := [0xe3303,0x6eb023,0x8e0e13,0x8e8e93,0xffee68e3]
def midWords : List (BitVec 32) := [0x1000e37,0x800e0e13,0x2a0e0f13]
def tailWords : List (BitVec 32) := [0xcd9cf06f]

sym_block loopRun := symRun { noAlias := true } loopWords (pcOf 49798) 50
sym_block headRun := symRun { noAlias := true } headWords (pcOf 49795) 10
sym_block midRun := symRun { noAlias := true } midWords (pcOf 49803) 10
sym_block tailRun := symRun { noAlias := true } tailWords (pcOf 49811) 10

def loopResult (p : Word) : Result :=
  ⟨loopRun.res.st,
    .ite .ltu (.bin .add (.reg .x28) (.c 8)) (.reg .x30)
      (.c (((((p + 4) + 4) + 4) + 4) + 18446744073709551600))
      (.c (((((p + 4) + 4) + 4) + 4) + 4)), .branch, 5, 5⟩

theorem loop_run (p : Word) :
    symRun { noAlias := true } loopWords p 50 = some (loopResult p) := by krfl

theorem loop_regs (p : Word) (s : MachineState) :
    RegsExcept s ((loopResult p).toState s) [.x6,.x28,.x29] := by
  intro r hr
  rw [Result.toState_getReg]
  change (loopRun.res.st.regs.get r).eval s = s.getReg r
  clear p
  cases r <;> first | rfl | exact (hr (by decide)).elim

theorem loop_step {im : Image} (p : Word) (hc : CodeAt im p loopWords)
    (s : MachineState) (hpc : s.pc = p) (S D F : Nat)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0) (hS : S + 8 ≤ 2 ^ 24) (hD : D + 8 ≤ 2 ^ 24) (hF : F < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 F) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = (if S + 8 < F then p else p + 20) ∧
      t.getReg .x28 = BitVec.ofNat 64 (S + 8) ∧ t.getReg .x29 = BitVec.ofNat 64 (D + 8) ∧
      t.getMem (BitVec.ofNat 64 D) = s.getMem (BitVec.ofNat 64 S) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => A = D) := by
  refine ⟨_, symRun_sound (loop_run p) hc s hpc ?_, ?_, ?_, ?_, ?_, loop_regs p s, ?_⟩
  · simp [loopResult, loopRun.res, rv_simp, h28, h29, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, loopResult, E.eval, BinOp.eval, CmpOp.eval, h28, h30, ofNat_add_ofNat,
      ofNat_add8, ofNat_add8']
    have hb : (((p + 4) + 4) + 4) + 4 + 18446744073709551600 = p := by
      simp only [BitVec.add_assoc]
      change p + 0 = p
      exact BitVec.add_zero p
    have he : (((p + 4) + 4) + 4) + 4 + 4 = p + 20 := by
      simp only [BitVec.add_assoc]
      rfl
    rw [hb, he]
    have hlt : (BitVec.ofNat 64 (S + 8)).ult (BitVec.ofNat 64 F) = decide (S + 8 < F) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show S + 8 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt hF]
    by_cases h : S + 8 < F <;> simp_all
  · simp only [Result.toState_getReg, loopResult, loopRun.res, rv_simp, h28, ofNat_add_ofNat, ofNat_add8, ofNat_add8']
  · simp only [Result.toState_getReg, loopResult, loopRun.res, rv_simp, h29, ofNat_add_ofNat, ofNat_add8, ofNat_add8']
  · simp only [Result.toState_getMem, loopResult, loopRun.res]
    t3n [h28, h29]
    simp
  · intro A hA hne
    simp only [Result.toState_getMem, loopResult, loopRun.res]
    t3n [h29]
    split_ifs with he
    · exfalso; apply hne; omega
    · rfl

/-- `n + 1` iterations of the copy loop at `p`, ascending, source `S`, destination `D`, end `S + 8 (n + 1)`. -/
theorem loop_copy {im : Image} (p : Word) (hc : CodeAt im p loopWords) :
    ∀ n (s : MachineState) (S D : Nat), S % 8 = 0 → D % 8 = 0 → S + 8 * (n + 1) ≤ 2 ^ 24 →
      D + 8 * (n + 1) ≤ S → s.pc = p →
      s.getReg .x28 = BitVec.ofNat 64 S → s.getReg .x29 = BitVec.ofNat 64 D →
      s.getReg .x30 = BitVec.ofNat 64 (S + 8 * (n + 1)) →
      ∃ t, Steps im s (5 * (n + 1)) (5 * (n + 1)) t ∧ t.pc = p + 20 ∧
        t.getReg .x28 = BitVec.ofNat 64 (S + 8 * (n + 1)) ∧
        t.getReg .x29 = BitVec.ofNat 64 (D + 8 * (n + 1)) ∧
        (∀ i, i ≤ n → t.getMem (BitVec.ofNat 64 (D + 8 * i)) = s.getMem (BitVec.ofNat 64 (S + 8 * i))) ∧
        RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => D ≤ A ∧ A < D + 8 * (n + 1)) := by
  intro n
  induction n with
  | zero =>
    intro s S D hS8 hD8 hS hD hpc h28 h29 h30
    obtain ⟨t, st, pt, r28, r29, mt, rt, ft⟩ := loop_step p hc s hpc S D (S + 8 * (0 + 1))
      hS8 hD8 (by omega) (by omega) (by omega) h28 h29 h30
    refine ⟨t, st, by simpa using pt, by simpa using r28, by simpa using r29, ?_, rt, ft.mono (by intro A _ h; omega)⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using mt
  | succ n ih =>
    intro s S D hS8 hD8 hS hD hpc h28 h29 h30
    obtain ⟨u, su, pu, u28, u29, mu, ru, fu⟩ := loop_step p hc s hpc S D (S + 8 * (n + 1 + 1))
      hS8 hD8 (by omega) (by omega) (by omega) h28 h29 h30
    have hpu : u.pc = p := by rw [pu, if_pos (by omega)]
    obtain ⟨t, ut, pt, t28, t29, mt, rt, ft⟩ := ih u (S + 8) (D + 8) (by omega) (by omega) (by omega) (by omega)
      hpu u28 u29 (by rw [ru.get (by decide), h30]; congr 1; ring)
    refine ⟨t, ?_, pt, by rw [t28]; congr 1; ring, by rw [t29]; congr 1; ring, ?_, (ru.trans rt).mono (by decide), ?_⟩
    · convert su.trans ut using 1 <;> ring
    · intro i hi
      rcases i with _ | i
      · rw [ft _ (by omega) (by omega)]
        simpa using mu
      · have h1 := mt i (by omega)
        rw [show D + 8 * (i + 1) = D + 8 + 8 * i by ring, h1, show S + 8 + 8 * i = S + 8 * (i + 1) by ring]
        exact fu _ (by omega) (by omega)
    · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h <;> omega)

end SigGolfCandidate.T3M.Expand.KCopy

namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem head_spec {im : Image} (hc : CodeAt im (pcOf 49795) headWords) (s : MachineState) (hpc : s.pc = pcOf 49795) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 49798 ∧ t.getReg .x28 = BitVec.ofNat 64 0xFFF000 ∧
      t.getReg .x29 = BitVec.ofNat 64 0xA0000 ∧ t.getReg .x30 = BitVec.ofNat 64 0xFFF400 ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound headRun hc s hpc (by simp [headRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [headRun.res, rv_simp]
  · simp [headRun.res, rv_simp]
  · simp [headRun.res, rv_simp]
  · intro r hr; cases r <;> first | rfl | exact (hr (by decide)).elim
  · intro A _ _; simp [headRun.res, rv_simp]

theorem mid_spec {im : Image} (hc : CodeAt im (pcOf 49803) midWords) (s : MachineState) (hpc : s.pc = pcOf 49803) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 49806 ∧ t.getReg .x28 = BitVec.ofNat 64 0xFFF800 ∧
      t.getReg .x30 = BitVec.ofNat 64 0xFFFAA0 ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound midRun hc s hpc (by simp [midRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [midRun.res, rv_simp]
  · simp [midRun.res, rv_simp]
  · intro r hr; cases r <;> first | rfl | exact (hr (by decide)).elim
  · intro A _ _; simp [midRun.res, rv_simp]

theorem tail_spec {im : Image} (hc : CodeAt im (pcOf 49811) tailWords) (s : MachineState) (hpc : s.pc = pcOf 49811) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 457 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound tailRun hc s hpc (by simp [tailRun.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [tailRun.res, rv_simp]

/-- KCOPY: 1067 steps from 49795 to the counter search entry 457, copying TOP_DATA + 0..1023 and
TOP_DATA + 2048..2719 (the packed R6 block) to RAM 0xA0000..0xA069F. -/
theorem kcopy_spec {im : Image} (hh : CodeAt im (pcOf 49795) headWords) (hl1 : CodeAt im (pcOf 49798) loopWords)
    (hm : CodeAt im (pcOf 49803) midWords) (hl2 : CodeAt im (pcOf 49806) loopWords)
    (ht : CodeAt im (pcOf 49811) tailWords) (s : MachineState) (hpc : s.pc = pcOf 49795) :
    ∃ u, Steps im s 1067 1067 u ∧ u.pc = pcOf 457 ∧
      (∀ k, k < 128 → u.getMem (BitVec.ofNat 64 (0xA0000 + 8 * k)) = s.getMem (BitVec.ofNat 64 (0xFFF000 + 8 * k))) ∧
      (∀ k, k < 84 → u.getMem (BitVec.ofNat 64 (0xA0400 + 8 * k)) = s.getMem (BitVec.ofNat 64 (0xFFF800 + 8 * k))) ∧
      RegsExcept s u [.x6,.x28,.x29,.x30] ∧ Frame s u (fun A => 0xA0000 ≤ A ∧ A < 0xA06A0) := by
  obtain ⟨t0, s0, p0, a28, a29, a30, r0, f0⟩ := head_spec hh s hpc
  obtain ⟨t1, s1, p1, b28, b29, m1, r1, f1⟩ := loop_copy (pcOf 49798) hl1 127 t0 0xFFF000 0xA0000
    (by decide) (by decide) (by decide) (by decide) p0 a28 a29 (by rw [a30])
  have p1' : t1.pc = pcOf 49803 := by rw [p1]; rfl
  obtain ⟨t2, s2, p2, c28, c30, r2, f2⟩ := mid_spec hm t1 p1'
  have c29 : t2.getReg .x29 = BitVec.ofNat 64 0xA0400 := by rw [r2.get (by decide), b29]
  obtain ⟨t3, s3, p3, d28, d29, m3, r3, f3⟩ := loop_copy (pcOf 49806) hl2 83 t2 0xFFF800 0xA0400
    (by decide) (by decide) (by decide) (by decide) p2 c28 c29 (by rw [c30])
  have p3' : t3.pc = pcOf 49811 := by rw [p3]; rfl
  obtain ⟨u, s4, p4, r4, f4⟩ := tail_spec ht t3 p3'
  refine ⟨u, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by norm_num) (by norm_num), p4, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [f4.get (by omega) (by simp), f3.get (by omega) (by omega), f2.get (by omega) (by simp),
      m1 k (by omega), f0.get (by omega) (by simp)]
  · intro k hk
    rw [f4.get (by omega) (by simp), m3 k (by omega), f2.get (by omega) (by simp), f1.get (by omega) (by omega),
      f0.get (by omega) (by simp)]
  · exact ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by decide)
  · exact ((((f0.trans f1).trans f2).trans f3).trans f4).mono (fun A _ h => by
      rcases h with (((h | h) | h) | h) | h <;> first | exact h.elim | omega)

end SigGolfCandidate.T3M.Expand.KCopy

namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The packed R6 block as doublewords in the expand data: `TOP_DATA + 0..1023` (dwords 0..127) and
`TOP_DATA + 2048..2719` (dwords 128..211). -/
def SrcW (s : MachineState) : Prop :=
  (∀ k, k < 128 → s.getMem (BitVec.ofNat 64 (0xFFF000 + 8 * k)) =
    BitVec.ofNat 64 (Search.r6Entry (2 * k) + 2 ^ 32 * Search.r6Entry (2 * k + 1))) ∧
  (∀ k, k < 84 → s.getMem (BitVec.ofNat 64 (0xFFF800 + 8 * k)) =
    BitVec.ofNat 64 (Search.r6Entry (2 * (128 + k)) + 2 ^ 32 * Search.r6Entry (2 * (128 + k) + 1)))

theorem kcopy_table {im : Image} (hh : CodeAt im (pcOf 49795) headWords) (hl1 : CodeAt im (pcOf 49798) loopWords)
    (hm : CodeAt im (pcOf 49803) midWords) (hl2 : CodeAt im (pcOf 49806) loopWords)
    (ht : CodeAt im (pcOf 49811) tailWords) (s : MachineState) (hpc : s.pc = pcOf 49795) (hsrc : SrcW s) :
    ∃ u, Steps im s 1067 1067 u ∧ u.pc = pcOf 457 ∧ Search.R6.R6TableW 0xA0000 u ∧
      RegsExcept s u [.x6,.x28,.x29,.x30] ∧ Frame s u (fun A => 0xA0000 ≤ A ∧ A < 0xA06A0) := by
  obtain ⟨u, su, pu, m1, m2, ru, fu⟩ := kcopy_spec hh hl1 hm hl2 ht s hpc
  refine ⟨u, su, pu, ?_, ru, fu⟩
  intro k hk
  by_cases h : k < 128
  · rw [m1 k h]; exact hsrc.1 k h
  · obtain ⟨j, rfl⟩ : ∃ j, k = 128 + j := ⟨k - 128, by omega⟩
    rw [show 0xA0000 + 8 * (128 + j) = 0xA0400 + 8 * j by omega, m2 j (by omega)]
    exact hsrc.2 j (by omega)

end SigGolfCandidate.T3M.Expand.KCopy

namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
/-- KCOPY's code (a class, so the layer-recovery sections can take it as an instance like `EntryCode`). -/
class Code (im : Image) : Prop where
  head : CodeAt im (pcOf 49795) headWords
  loop1 : CodeAt im (pcOf 49798) loopWords
  mid : CodeAt im (pcOf 49803) midWords
  loop2 : CodeAt im (pcOf 49806) loopWords
  tail : CodeAt im (pcOf 49811) tailWords
theorem installed_code : Code Images.expandImage := by
  constructor <;> apply codeAt_expand_last <;> decide +kernel
#print axioms installed_code
#print axioms kcopy_table
end SigGolfCandidate.T3M.Expand.KCopy
