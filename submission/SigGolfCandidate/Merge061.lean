import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge060

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Canon ====
section

/-! # Expand canonical counter search (configuration e7b, r3-lean-sign expand porter; img-v6 port canon-v6)

Split out of `Expand/Routine.lean` so that it builds independently of the forest/FTS modules.
Expand kernel base `b = 354`; choice block at 43040 (`choiceBase 354`), `pa` at 43057, `topcr` at 43064..43070,
floor hooks at 46905 (policy hints, img-v6 radix 484/22/1), lower credit hook at 46918 (credit words `0x66040 + 8 lay`).
Campaign T51: the top layer runs the shared T51 kernel at its expand instance (`1272: j 54176`, `K_ENTRY` 54176, unpacker
54356..54521, RAM table 0xA0000 from KCOPY): `T51.trial` / `T51.unpack` in `CanonicalExpand.cs_loop`. -/

namespace ClaudeWCT.W9.Machine.Expand.SharedCounterHooks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
/-- `46905`: `t3 := mem[0x66000]` (policy hints), `t4 := 22` (radix), branch on the layer (v6: `s0-3`). -/
def firstCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0xe3e03,0x1600e93,0xffd40f13,0xf0c63]
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
theorem rem22 (n : Nat) (hn : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 22#64=BitVec.ofNat 64 (n%22) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_remu,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n%22<2^64 by omega)]
  omega
theorem div22 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 22#64=BitVec.ofNat 64 (n/22) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/22<2^64 by omega)]
  omega
theorem floor1_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=1)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 11 17 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/484%22) ∧
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
    simp only [div22 hints (by omega),div22 (hints/22) (by omega),rem22 hints (by omega),rem22 (hints/22) (by omega)]
    try (congr 1; omega)
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
theorem floor2_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=2)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 11 17 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints/22%22) ∧
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
    simp only [div22 hints (by omega),div22 (hints/22) (by omega),rem22 hints (by omega),rem22 (hints/22) (by omega)]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A ha hn;rfl
theorem floor3_steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46905)
    (hints : Nat) (hh : hints<8000) (h8 : s.getReg .x8=3)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃ t,Steps im s 8 11 t ∧ t.pc=pcOf 43027 ∧
      t.getReg .x28=BitVec.ofNat 64 (hints%22) ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _=>False) := by
  let s1:=first.res.toState s
  have st1 : Steps im s 6 6 s1 := symRun_sound first hc.first s hp (by simp [first.res,rv_simp])
  let s2:=remainder.res.toState s1
  have st2 : Steps im s1 2 5 s2 := symRun_sound remainder hc.remainder s1 (by simp [s1, first.res, s2, remainder.res, rv_simp, h8]) (by simp [remainder.res,rv_simp])
  refine ⟨s2,st1.trans (st2),?_,?_,?_,?_⟩
  · simp [s1, first.res, s2, remainder.res,rv_simp,h8]
  · simp [s1, first.res, s2, remainder.res,rv_simp,hm]
    simp only [div22 hints (by omega),div22 (hints/22) (by omega),rem22 hints (by omega),rem22 (hints/22) (by omega)]
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
/-- Floors read from the policy hints (img-v6 mixed radix `484·f1 + 22·f2 + f3`); the top floor is 14. Agrees with
`Research.V7Composed198Gate.hintFloor` (`CanonicalPolicy.topFloor = 14`). -/
def hintFloor (hints : BitVec 16) (lay : Layer) : Nat :=
  if lay=0 then 14 else hints.toNat/22^(3-lay.val)%22
theorem creditAddr_lt (lay : Layer) : creditAddr lay<2^64 := by
  have := lay.isLt;unfold creditAddr;omega
theorem creditAddr_mem (lay : Layer) : CreditW lay (creditAddr lay) := by
  have := lay.isLt
  unfold CreditW creditAddr
  omega
theorem creditW_zero {X : Nat} (h : CreditW 0 X) : X=0x66040 := by
  rcases h with ⟨h,_⟩; rw [h]; rfl
theorem hintFloor_lt (hints : BitVec 16) (lay : Layer) : hintFloor hints lay<22 := by
  unfold hintFloor
  split_ifs
  · omega
  · exact Nat.mod_lt _ (by decide)
theorem hintFloor_top (hints : BitVec 16) : hintFloor hints 0=14 := rfl
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
sym_block lowerAddRun := symRun {noAlias:=true} lowerAddCode (pcOf 43020) 6
sym_block lowerFloorJumpRun := symRun {noAlias:=true} floorJumpCode (pcOf 43024) 2
sym_block lowerCreditJumpRun := symRun {noAlias:=true} lowerCreditJumpCode (pcOf 43028) 2
sym_block lowerBranchRun := symRun {noAlias:=true} lowerBranchCode (pcOf 43027) 2
sym_block lowerBadRun := symRun {noAlias:=true} lowerBadCode (pcOf 43029) 2

structure Code (image : Image) : Prop where
  scoring : CanonicalReward.PrefixAt image 354
  floorJump : CodeAt image (pcOf 43024) floorJumpCode
  lowerBranch : CodeAt image (pcOf 43027) lowerBranchCode
  lowerJump : CodeAt image (pcOf 43028) lowerCreditJumpCode
  lowerBad : CodeAt image (pcOf 43029) lowerBadCode
  hooks : ClaudeWCT.W9.Machine.Expand.SharedCounterHooks.Code image
  /-- Campaign T51: the top-trial kernel `K` at 54176 (`1272: j 54176`) and the contiguous unpacker
  (54356..54467 | 54468..54521). -/
  t51K : CodeAt image (pcOf 54176) (T51.kCode T51.expandInst)
  t51Bonus : CodeAt image (pcOf 54305) (T51.bonusCode T51.expandInst)
  t51UA : CodeAt image (pcOf 54356) T51.uCodeA
  t51UB : CodeAt image (pcOf 54468) T51.uCodeB
theorem Code.kAt {image : Image} (h : Code image) : T51.T51KAt image T51.expandInst := T51.expandKAt h.t51K h.t51Bonus
theorem Code.uAt {image : Image} (h : Code image) : T51.T51UAt image T51.expandInst := T51.expandUAt h.t51UA h.t51UB

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
    exact ⟨t,11,17,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor2_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,11,17,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩
  · obtain ⟨t,st,pt,xt,rt,ft⟩ := SharedCounterHooks.floor3_steps hC s hp hints.toNat hh h8 hm
    exact ⟨t,8,11,by omega,st,pt,by simpa [hintFloor] using xt,rt,ft⟩

/-- Lower reward with the path-aware bonus (`pa`, +4 when the LOW half `L` at `EOUT` is spare), floor from the
policy hints. -/
theorem lower_spec {image : Image} (hK : KernAt image 354 (Code image)) (s : MachineState) (lay : Layer) (hl : lay≠0)
    (v : Digest) (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
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
    (hl : lay≠0) (v : Digest) (ht : Reward.RewardTablesOK s) (hp : s.pc=pcOf (Reward.base 354 false))
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
  refine ⟨⟨?_,?_,?_⟩,Or.inl rfl,?_,⟨?_,?_,?_⟩,?_,?_,?_,hP⟩
  all_goals apply codeAt_expand_current_chunk <;> decide +kernel

theorem reward_code_of_hooks (hH : SharedCounterHooks.Code Images.expandImage) :
    CanonicalExpandHooks.Code Images.expandImage := by
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,hH,?_,?_,?_⟩
  rotate_right 3
  all_goals first
    | (apply codeAt_t51_at <;> decide +kernel)
    | (apply codeAt_expand_current_chunk <;> decide +kernel)
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
def csT (lay : Layer) : Nat := if lay = 0 then 755 else 404
def csOk (lay : Layer) : Nat := if lay = 0 then 4096 else 4096
theorem capLimit_le (n : Nat) : capLimit n ≤ 2 ^ 22 := by
  unfold capLimit
  by_cases h : n = 0
  · simp [h, WCT9.topSearchLimit]
  · simp only [h, if_false]; unfold baseCapLimit; omega
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
theorem producerDecode_top (v : Digest) (floor : Nat) (low : Bool) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode 0 v = some ds) :
    WCT9.CanonicalPolicy.producerDecodeAt 0 floor low v =
      if rewardOK 0 floor low ds ∧ WCT9.canonicalZeroBound 0 ds then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.producerRankBound,rewardOK]
  try exact if_congr Iff.rfl rfl rfl
theorem producerDecode_lower {lay : Layer} (hlz : lay≠0) (v : Digest) (floor c : Nat) (low : Bool) {ds : List Nat}
    (hd : WCT9.CanonicalPolicy.decode lay v=some ds) (hds : ds=lowDigits v++[c]) :
    WCT9.CanonicalPolicy.producerDecodeAt lay floor low v=
      if rewardOK lay floor low ds ∧ (lowDigits v++[c]).count 0≤5 ∧ Rank.rankOK v then some ds else none := by
  simp [WCT9.CanonicalPolicy.producerDecodeAt,hd,WCT9.canonicalZeroBound,WCT9.producerZeroCap,WCT9.producerRankBound,
    rewardOK,Rank.rankOK,Rank.rankFloor,WCT9.producerRankFloor,hlz,hds,filter_zero_count]
/-! Producer output on a full 256-bit answer, split by the machine's trial order. -/
theorem producerDecodeOut_top_low (a : BitVec 256) {ds : List Nat}
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 14 true (a.extractLsb' 0 128) = some ds) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 14 a = some (ds, true) := by
  have hg : WCT9.topGood (a.extractLsb' 0 128) := by
    unfold WCT9.topGood; rw [show WCT9.CanonicalPolicy.topFloor = 14 from rfl, h]; rfl
  have hl : WCT9.lowSelected 0 a = true := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hg]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 0 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl, h]; rfl
theorem producerDecodeOut_top_blocked (a : BitVec 256)
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 14 true (a.extractLsb' 0 128) = none)
    (hb : T3.TopChoice.blocked (a.extractLsb' 0 128)) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 14 a = none := by
  have hl : WCT9.lowSelected 0 a = true := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hb]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 0 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl, h]; rfl
theorem producerDecodeOut_top_high (a : BitVec 256)
    (h : WCT9.CanonicalPolicy.producerDecodeAt 0 14 true (a.extractLsb' 0 128) = none)
    (hb : ¬ T3.TopChoice.blocked (a.extractLsb' 0 128)) :
    WCT9.CanonicalPolicy.producerDecodeOut 0 14 a =
      (WCT9.CanonicalPolicy.producerDecodeAt 0 14 false (a.extractLsb' 128 128)).map (·, false) := by
  have hg : ¬ WCT9.topGood (a.extractLsb' 0 128) := by
    unfold WCT9.topGood; rw [show WCT9.CanonicalPolicy.topFloor = 14 from rfl, h]; simp
  have hl : WCT9.lowSelected 0 a = false := by
    simp [WCT9.lowSelected, WCT9.topChooseLow, hg, hb]
  have he : WCT9.encodingAnswer 0 a = a.extractLsb' 128 128 := by
    rw [WCT9.encodingAnswer_eq, hl]; rfl
  unfold WCT9.CanonicalPolicy.producerDecodeOut
  rw [he, hl]
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
  table : TableOK s
  cf : CfTableOK (cfFlag b) s
  reward : Reward.RewardTablesOK s
  zt : ZeroCap.ZtOK b s
  floorLt : A.floor<22
  floorTop : A.lay=0 → ∃ extra : Nat, extra ≤ 4 ∧ A.floor=14+extra ∧
    s.getMem (BitVec.ofNat 64 (EOUT+32))=BitVec.ofNat 64 (12+extra) ∧
    s.getMem (BitVec.ofNat 64 (EOUT+40))=BitVec.ofNat 64 (14+extra)
  hintsLt : A.hints.toNat<8000
  floorEq : A.lay≠0 → A.floor=CanonicalExpandHooks.hintFloor A.hints A.lay
  floorMem : s.getMem (0x66000#64)=BitVec.ofNat 64 A.hints.toNat
  /-- Campaign T51: the packed top tables in RAM at 0xA0000 (`T51.expandInst.blk`, copied by KCOPY 54522 from the
  data block 0xFF9E00) for the top search. -/
  t51table : A.lay=0 → T51.T51TableW 0xA0000 s
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
theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 51 else 43 := by
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
theorem TrialSt.table {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : TableOK s0) : TableOK u :=
  ht.frame hu.frame (by intro j hj; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.cf {A : CsArgs} {s0 u : MachineState} {i : Nat} {flag : Nat}
    (hu : TrialSt b A s0 i u) (ht : CfTableOK flag s0) : CfTableOK flag u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.reward {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : Reward.RewardTablesOK s0) : Reward.RewardTablesOK u :=
  ht.frame hu.frame (by intro j hj hj'; unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG; omega)
theorem TrialSt.zt {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : ZeroCap.ZtOK 354 s0) : ZeroCap.ZtOK 354 u :=
  ht.frame hu.frame (by
    intro j hj
    simp only [ZeroCap.ZT, CsW, CanonicalExpandHooks.CreditW, DigW, ENC, EOUT, DIGITS, FLAG] <;> norm_num <;> omega)
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < capLimit A.lay.val) :
    ∃ k t2, Steps image t k k t2 ∧ k ≤ 17 ∧ t2.pc = pcOf (b + 123) ∧
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
  have hk : k1 + 8 ≤ 17 := by omega
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
theorem cs_exhaust {A : CsArgs} {s0 t : MachineState} {i : Nat}
    {rewardCondition : Prop} (hK : KernAt image b rewardCondition) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i=capLimit A.lay.val) :
    TBSim image sk t (0*csT A.lay+csOk A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg i 0)
      (CsPost image b A s0) := by
  obtain ⟨k1,t1,s1,k1le,p1,r1,f1⟩ := cap_spec hK t hI.pc A.lay.val i A.lay.isLt hI.hi
    (by rw [hI.regs.get (by decide),hpre.x8]) hI.x19
  rw [if_pos hi] at p1
  have hk1 : k1≤9 := k1le
  have h8 : t1.getReg .x8=BitVec.ofNat 64 A.lay.val := by
    rw [r1.get (by decide),hI.regs.get (by decide),hpre.x8]
  have fr1 : Frame s0 t1 (CsW A.lay) := (hI.frame.trans f1).mono (fun A _ h=>by simpa using h)
  have hcf : CfTableOK 0 t1 := hpre.cf.frame fr1
    (by intro j hj hj';unfold CsW CanonicalExpandHooks.CreditW DigW TOP_DATA ENC EOUT DIGITS FLAG;omega)
  obtain ⟨n,t2,hn,s2,p2,r2,f2⟩ := Credit.exhaust_fail hK t1 p1 A.lay.val A.lay.isLt h8 0
    (by decide) hcf (Or.inr rfl)
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
      (W:=F*csT A.lay+csOk A.lay+(csT A.lay-22)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
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
      obtain ⟨extra, hextra, hfl, hLowFloor, hHighFloor⟩ := hpre.floorTop hlz
      have e : WCT9.CanonicalPolicy.producerDecodeOut A.lay A.floor a =
          WCT9.CanonicalPolicy.producerDecodeOut 0 (14+extra) a := by
        rw [hlz,hfl]
      rw [e]
      -- T51: `tcEntry 354` (1272) jumps to the T51 kernel `K_ENTRY` (54176)
      obtain ⟨tg,sg,pg,rg,fg⟩ := top_entry_spec hK t4 p4
      have hTg := hT4.step rg (by decide) fg
      have hKT : T51.T51KAt image T51.expandInst := CanonicalExpandHooks.Code.kAt hK.reward
      have hUT : T51.T51UAt image T51.expandInst := CanonicalExpandHooks.Code.uAt hK.reward
      have fgE : ∀ X, X < 2^64 → tg.getMem (BitVec.ofNat 64 X) = t4.getMem (BitVec.ofNat 64 X) :=
        fun X hX => fg.get hX (by simp)
      have h6g : tg.getReg .x6 = (a.extractLsb' 0 128).extractLsb' 0 64 := by rw [rg.get (by decide),h6]
      have h7g : tg.getReg .x7 = (a.extractLsb' 0 128).extractLsb' 64 64 := by rw [rg.get (by decide),h7]
      have h12g : tg.getReg .x12 = BitVec.ofNat 64 EOUT := by
        rw [rg.get (by decide),r4.get (by decide),getReg_writeHash,h12]
      have hLowFloorG : tg.getMem (BitVec.ofNat 64 (EOUT+32)) = BitVec.ofNat 64 (12+extra) := by
        rw [hTg.frame.get (by unfold EOUT; omega)
          (by unfold CsW CanonicalExpandHooks.CreditW CanonicalExpandHooks.creditAddr DigW ENC EOUT DIGITS FLAG; omega),
          hLowFloor]
      have hHighFloorG : tg.getMem (BitVec.ofNat 64 (EOUT+40)) = BitVec.ofNat 64 (14+extra) := by
        rw [hTg.frame.get (by unfold EOUT; omega)
          (by unfold CsW CanonicalExpandHooks.CreditW CanonicalExpandHooks.creditAddr DigW ENC EOUT DIGITS FLAG; omega),
          hHighFloor]
      have h17g : tg.getReg .x17 = BitVec.ofNat 64 (T3.target 0) := by
        rw [hTg.reg (by decide),hpre.x17,hlz]; rfl
      have htg : T51.T51TableW T51.expandInst.blk tg := (hpre.t51table hlz).frame hTg.frame (by decide) (by decide)
        (by intro k hk; unfold CsW CanonicalExpandHooks.CreditW CanonicalExpandHooks.creditAddr DigW ENC EOUT DIGITS FLAG; omega)
      obtain ⟨hAcc,hRej⟩ := T51.trial hKT tg (by rw [pg]; rfl) extra hextra a h6g h7g h12g
        (mH0 tg (fgE _ (by unfold EOUT;omega))) (mH8 tg (fgE _ (by unfold EOUT;omega)))
        hLowFloorG hHighFloorG h17g htg
      cases hD : WCT9.CanonicalPolicy.producerDecodeOut 0 (14+extra) a with
      | some found =>
        obtain ⟨ds,low⟩ := found
        obtain ⟨k,t,st,kle,pt,t6,t7,hdec,t28,tcr,tfl,rt,ft⟩ := hAcc ds low hD
        have hTt := hTg.stepW rt (by decide) ft (fun X hX => by
          rcases hX with hX | hX
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
            rw [hlz, hX]; exact CanonicalExpandHooks.creditAddr_mem 0
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hX))))))
          (fun X hX => by rcases hX with rfl | rfl <;> decide)
        obtain ⟨t',st',pt',tdig,rt',ft'⟩ := T51.unpack hUT t pt _ ds hdec t6 t7 t28
        have hTt' := hTt.stepW rt' (by decide) ft' (fun X hX => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX)))))
          (fun X hX => by unfold ENC DIGITS at *; omega)
        have hret : t.getReg .x1 = pcOf A.ret := by rw [hTt.reg (by decide),hpre.x1]
        have hlen : ds.length = T3.chainCount A.lay := by
          rw [hlz]; exact T51.decode_length hdec
        have hR' : RewardReady 354 A s0 i ds low t' := by
          refine ⟨?_,hTt',hlen,?_,fun h => absurd hlz h,?_⟩
          · rw [pt',hret]; exact pcOf_and_not1 _
          · intro j hj; rw [hlz] at hj; exact tdig j hj
          · rw [ft'.get (CanonicalExpandHooks.creditAddr_lt _)
              (by unfold CanonicalExpandHooks.creditAddr DIGITS; omega),hlz]
            exact tcr
        have done := cs_success (sk:=sk) hK hpre hR' hi _ (by rw [hlz]; exact hdec)
          (by rw [hfl,hlz]; exact T51.producerDecodeOut_floor hD)
          (fun _ => by rw [ft'.get (by decide) (by unfold DIGITS FLAG; omega)]; exact tfl)
        refine (TBSim.steps ((s4.trans sg).trans (st.trans st')) done).mono ?_ (fun _ _ h => h)
        simp only [csT,csOk,if_pos hlz,T51.expandInst];omega
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
            have hTables : Reward.RewardTablesOK t8 := hpre.reward.frame hT8.frame
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
              (hpre.floorEq hlz)
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

def csCost (lay : Layer) : Nat := (WCT9.searchLimit lay * csT lay)+8192

theorem counterSearch_good {A : CsArgs} {s0 : MachineState}
    (hK : KernAt image 354 (CanonicalExpandHooks.Code image)) (hp : CsPre 354 A s0) :
    TBSim image sk s0 (csCost A.lay)
      (WCT9.CanonicalPolicy.layerCounterSearchAt A.lay A.floor A.tree A.leaf A.msg 0 (WCT9.searchLimit A.lay))
      (CsPost image 354 A s0) := by
  refine (counterSearch_tbsim hK hp).mono ?_ (fun _ _ h=>h)
  rw [capLimit_eq]
  unfold csCost csOk
  split_ifs <;> omega
end SigGolfCandidate.T3M.Search.CanonicalExpand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_EndRoutine ====
section

/-! # Expand `end` routine (configuration e7b)

Word 47011 (formerly `addi a0,zero,0`) is `jal zero, 43071`. The routine at 43071..43076 loads the choice flag word
`mem[0x667F8]` (0, or 128 after the producer took HIGH), stores its low byte at abs 25216 = `WIT + choiceOff`
(`sb t1, 640(0x6000)`), sets `a0 := 0` and jumps to the witness-stack post-pass at 49400 (img-merged; was the halting `ecall` at
47012). -/

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def endCode : List (BitVec 32) := bv_list% 32 [0x00066e37,0x7f8e3303,0x00006e37,0x286e0023,0x00000513,0x2d00606f]
sym_block endRun := symRun { noAlias := true } endCode (pcOf 43071) 20

/-- The flag byte written by `end`. -/
def flagByte (s : MachineState) : BitVec 8 := (s.getMem (BitVec.ofNat 64 0x667F8)).truncate 8

theorem end_mem (s : MachineState) (A : Nat) (hA : A < 2^64) :
    (endRun.res.toState s).getMem (BitVec.ofNat 64 A) =
      if A = 25216 then replaceByte (s.getMem (BitVec.ofNat 64 25216)) 0 (flagByte s)
      else s.getMem (BitVec.ofNat 64 A) := by
  simp only [Result.toState_getMem,endRun.res,flagByte]
  t3n []
  all_goals (try rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)])
  all_goals (split_ifs <;> first | rfl | omega)

theorem end_steps {im : Image} (hc : CodeAt im (pcOf 43071) endCode)
    (s : MachineState) (hpc : s.pc=pcOf 43071) :
    ∃t, Steps im s 6 6 t ∧ t.pc=pcOf 49400 ∧ t.getReg .x10=0#64 ∧
      t.getMem (BitVec.ofNat 64 25216)=replaceByte (s.getMem (BitVec.ofNat 64 25216)) 0 (flagByte s) ∧
      RegsExcept s t [.x6,.x10,.x28] ∧ Frame s t (fun A=>A=25216) := by
  refine ⟨_,symRun_sound endRun hc s hpc (by simp [endRun.res,rv_simp,accessValid_iff,MEMORY_BYTES]),?_,?_,?_,?_,?_⟩
  · simp [endRun.res, Result.toState_pc, E.eval]
  · simp [endRun.res, rv_simp]
  · rw [end_mem s 25216 (by norm_num), if_pos rfl]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    rw [end_mem s A hA, if_neg hn]

theorem installed_end : CodeAt Images.expandImage (pcOf 43071) endCode := by
  apply codeAt_expand_current_chunk <;> decide +kernel
end ClaudeWCT.W9.Machine.Expand.SharedScatter
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PostPass ====
section

/-! # The witness-stack post-pass of the img-merged expander (words 49400 .. 54175)

Entered from the `end` routine (`jal 49400`). In order:
1. save the old top chain area `[11768, 15224)` to `0x300000` and the old top path area `[11000, 11768)` to
   `0x301000` (forward word loops);
2. move `[24480, 26096)` up by 16, `[23744, 24464)` by 32, `[15224, 23728)` by 48 and the FTS block
   `[2904, 10568)` by 1224 (backward word loops, highest word first);
3. zero the new top layer area `[11792, 15272)`;
4. copy the 54 top chain values (words 49469 .. 50054, straight line) from the saved chain blocks into the 27 pairs;
5. place the twelve top siblings through two per-row blocks (row `leaf % 64` at `50078 + 32 r`, row
   `leaf / 64 % 64` at `52126 + 32 r`; `leaf = mem[0x20160] >> 52`), each copying six 16-byte siblings from the saved
   path area to the new plan slots;
6. `a0 := 0` and halt (`ecall` at 54175).

This file: the code, its symbolic runs and the machine-level loop/block specifications. -/

namespace ClaudeWCT.W9.Machine.Expand.PostPass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def cfgP : Config := { noAlias := true }

theorem valid8P (X : Nat) (h : X + 8 ≤ 16777216) (h8 : X % 8 = 0) : accessValid (BitVec.ofNat 64 X) 8 = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [show MEMORY_BYTES = 16777216 from rfl]; omega, h8⟩

theorem ult_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  simp [BitVec.ult, toNat_ofNat_lt hx, toNat_ofNat_lt hy]

theorem ofNat_sub8 (c : Nat) (hc : 8 ≤ c) :
    BitVec.ofNat 64 c + 18446744073709551608#64 = BitVec.ofNat 64 (c - 8) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 8 := ⟨c - 8, by omega⟩
  rw [show k + 8 - 8 = k by omega, ← ofNat_add_ofNat, BitVec.add_assoc,
    show (BitVec.ofNat 64 8 + 18446744073709551608#64 : BitVec 64) = 0#64 by decide]
  exact BitVec.add_zero _

/-! ### Code -/
def cPro1 : List (BitVec 32) := [0x3e37,0xdf8e0e13,0x300eb7,0xe8e93,0x4f37,0xb78f0f13]
def cPro2 : List (BitVec 32) := [0x3e37,0xaf8e0e13,0x301eb7,0xe8e93,0x3f37,0xdf8f0f13]
/-- Forward copy body (both save loops). -/
def fBody : List (BitVec 32) := [0xe3303,0x6eb023,0x8e0e13,0x8e8e93,0xffee68e3]
def cMv1 : List (BitVec 32) := [0x6e37,0x5e8e0e13,0x6f37,0xf98f0f13,0x1000393]
def cMv2 : List (BitVec 32) := [0x6e37,0xf88e0e13,0x6f37,0xcb8f0f13,0x2000393]
def cMv3 : List (BitVec 32) := [0x6e37,0xca8e0e13,0x4f37,0xb70f0f13,0x3000393]
def cMv4 : List (BitVec 32) := [0x3e37,0x940e0e13,0x1f37,0xb50f0f13,0x4c800393]
/-- Backward move body (all four moves). -/
def mBody : List (BitVec 32) := [0xe3303,0x7e0eb3,0x6eb023,0xff8e0e13,0xffcf48e3]
def cZPro : List (BitVec 32) := [0x3e37,0xe10e0e13,0x4f37,0xba8f0f13]
def zBody : List (BitVec 32) := [0xe3023,0x8e0e13,0xffee6ce3]

theorem code_last {b : Nat} {code : List (BitVec 32)} (hlo : 44032 ≤ b)
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (hc : (Images.expandCode_172.drop (b - 44032)).take code.length = code) :
    CodeAt Images.expandImage (pcOf b) code := codeAt_expand_last hlo hb hc

theorem code_pro1 : CodeAt Images.expandImage (pcOf 49400) cPro1 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_pro2 : CodeAt Images.expandImage (pcOf 49411) cPro2 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_f1 : CodeAt Images.expandImage (pcOf 49406) fBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_f2 : CodeAt Images.expandImage (pcOf 49417) fBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv1 : CodeAt Images.expandImage (pcOf 49422) cMv1 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv2 : CodeAt Images.expandImage (pcOf 49432) cMv2 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv3 : CodeAt Images.expandImage (pcOf 49442) cMv3 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_mv4 : CodeAt Images.expandImage (pcOf 49452) cMv4 := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m1 : CodeAt Images.expandImage (pcOf 49427) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m2 : CodeAt Images.expandImage (pcOf 49437) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m3 : CodeAt Images.expandImage (pcOf 49447) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_m4 : CodeAt Images.expandImage (pcOf 49457) mBody := code_last (by decide) (by decide) (by decide +kernel)
theorem code_zpro : CodeAt Images.expandImage (pcOf 49462) cZPro := code_last (by decide) (by decide) (by decide +kernel)
theorem code_z : CodeAt Images.expandImage (pcOf 49466) zBody := code_last (by decide) (by decide) (by decide +kernel)

/-! ### Symbolic results -/
/-- A prologue loading three constants into `t3`, `t4`/`t2` and `t5`. -/
def proRes (r : Reg) (a b c next n : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x28 (.c (BitVec.ofNat 64 a))).set r (.c (BitVec.ofNat 64 b))).set .x30
      (.c (BitVec.ofNat 64 c)), [], []⟩, .c (pcOf next), .endOfCode, n, n⟩
theorem run_pro1 : symRun cfgP cPro1 (pcOf 49400) 40 = some (proRes .x29 11768 0x300000 15224 49406 6) := by
  kernel_rfl
theorem run_pro2 : symRun cfgP cPro2 (pcOf 49411) 40 = some (proRes .x29 11000 0x301000 11768 49417 6) := by
  kernel_rfl
theorem run_mv1 : symRun cfgP cMv1 (pcOf 49422) 40 = some (proRes .x7 26088 16 24472 49427 5) := by kernel_rfl
theorem run_mv2 : symRun cfgP cMv2 (pcOf 49432) 40 = some (proRes .x7 24456 32 23736 49437 5) := by kernel_rfl
theorem run_mv3 : symRun cfgP cMv3 (pcOf 49442) 40 = some (proRes .x7 23720 48 15216 49447 5) := by kernel_rfl
theorem run_mv4 : symRun cfgP cMv4 (pcOf 49452) 40 = some (proRes .x7 10560 1224 2896 49457 5) := by kernel_rfl
def zProRes : Result :=
  ⟨⟨(RegFile.init.set .x28 (.c (BitVec.ofNat 64 11792))).set .x30 (.c (BitVec.ofNat 64 15272)), [], []⟩,
    .c (pcOf 49466), .endOfCode, 4, 4⟩
theorem run_zpro : symRun cfgP cZPro (pcOf 49462) 40 = some zProRes := by kernel_rfl

def fRes (p : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x6 (.ld (.reg .x28))).set .x28 (.bin .add (.reg .x28) (.c 8#64))).set .x29
      (.bin .add (.reg .x29) (.c 8#64)),
    [(⟨some (.reg .x29), 0#64⟩, .ld (.reg .x28))],
    [.valid ⟨some (.reg .x29), 0#64⟩ 8, .valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .ltu (.bin .add (.reg .x28) (.c 8#64)) (.reg .x30) (.c (pcOf p)) (.c (pcOf (p + 5))), .branch, 5, 5⟩
theorem run_f (p : Nat) (hp : p = 49406 ∨ p = 49417) : symRun cfgP fBody (pcOf p) 40 = some (fRes p) := by
  rcases hp with rfl | rfl <;> kernel_rfl

def mRes (p : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x6 (.ld (.reg .x28))).set .x28 (.bin .add (.reg .x28) (.c 18446744073709551608#64))).set
      .x29 (.bin .add (.reg .x28) (.reg .x7)),
    [(⟨some (.bin .add (.reg .x28) (.reg .x7)), 0#64⟩, .ld (.reg .x28))],
    [.valid ⟨some (.bin .add (.reg .x28) (.reg .x7)), 0#64⟩ 8, .valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .lt (.reg .x30) (.bin .add (.reg .x28) (.c 18446744073709551608#64)) (.c (pcOf p)) (.c (pcOf (p + 5))),
   .branch, 5, 5⟩
theorem run_m (p : Nat) (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457) :
    symRun cfgP mBody (pcOf p) 40 = some (mRes p) := by
  rcases hp with rfl | rfl | rfl | rfl <;> kernel_rfl

def zRes : Result :=
  ⟨⟨RegFile.init.set .x28 (.bin .add (.reg .x28) (.c 8#64)),
    [(⟨some (.reg .x28), 0#64⟩, .c 0#64)],
    [.valid ⟨some (.reg .x28), 0#64⟩ 8]⟩,
   .ite .ltu (.bin .add (.reg .x28) (.c 8#64)) (.reg .x30) (.c (pcOf 49466)) (.c (pcOf 49469)), .branch, 3, 3⟩
theorem run_z : symRun cfgP zBody (pcOf 49466) 40 = some zRes := by kernel_rfl

/-! ### Prologues -/
theorem pro_spec {im : Image} {code : List (BitVec 32)} {p : Nat} {r : Reg} {a b c next n : Nat}
    (hrun : symRun cfgP code (pcOf p) 40 = some (proRes r a b c next n)) (hc : CodeAt im (pcOf p) code)
    (hr : r = .x29 ∨ r = .x7)
    (s : MachineState) (hpc : s.pc = pcOf p) :
    ∃ t, Steps im s n n t ∧ t.pc = pcOf next ∧ t.getReg .x28 = BitVec.ofNat 64 a ∧
      t.getReg r = BitVec.ofNat 64 b ∧ t.getReg .x30 = BitVec.ofNat 64 c ∧
      RegsExcept s t [.x28, r, .x30] ∧ ∀ A, t.getMem A = s.getMem A := by
  refine ⟨_, symRun_sound hrun hc s hpc (by simp [proRes, Result.obligs, Oblig.all]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [proRes, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · rcases hr with rfl | rfl <;> simp [proRes, RegFile.get, RegFile.set, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, proRes]
    rcases hr with rfl | rfl <;> cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A; rfl

/-! ### Forward copy loop -/
/-- Memory after `i` words of `[a, a + 8 n)` were copied to `b`. -/
def fcp (M : Nat → Word) (a b i : Nat) (A : Nat) : Word :=
  if b ≤ A ∧ A < b + 8 * i ∧ (A - b) % 8 = 0 then M (a + (A - b)) else M A

theorem f_iter {im : Image} {p : Nat} (hp : p = 49406 ∨ p = 49417) (hc : CodeAt im (pcOf p) fBody)
    (t : MachineState) (hpc : t.pc = pcOf p) (a b e : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 a) (h29 : t.getReg .x29 = BitVec.ofNat 64 b)
    (h30 : t.getReg .x30 = BitVec.ofNat 64 e)
    (ha : a % 8 = 0) (ha' : a + 8 ≤ 16777216) (hb : b % 8 = 0) (hb' : b + 8 ≤ 16777216) (he : e < 2 ^ 64) :
    ∃ u, Steps im t 5 5 u ∧ u.pc = (if a + 8 < e then pcOf p else pcOf (p + 5)) ∧
      u.getReg .x28 = BitVec.ofNat 64 (a + 8) ∧ u.getReg .x29 = BitVec.ofNat 64 (b + 8) ∧
      RegsExcept t u [.x6, .x28, .x29] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) =
        if A = b then t.getMem (BitVec.ofNat 64 a) else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound (run_f p hp) hc t hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [fRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, h29, BitVec.add_zero]
    exact ⟨valid8P _ hb' hb, valid8P _ ha' ha⟩
  · simp only [Result.toState_pc, fRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_add8']
    rw [ult_ofNat _ _ (by omega) he]
    by_cases h : a + 8 < e <;> simp [h]
  · simp [fRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_add8']
  · simp [fRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h29, ofNat_add8']
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, fRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, fRes, memEval_cons, memEval_nil, Addr.eval, E.eval, h28, h29,
      BitVec.add_zero]
    by_cases hAb : A = b
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

structure FInv (M : Nat → Word) (p a b e i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if a + 8 * i < e then pcOf p else pcOf (p + 5))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (a + 8 * i)
  x29 : t.getReg .x29 = BitVec.ofNat 64 (b + 8 * i)
  x30 : t.getReg .x30 = BitVec.ofNat 64 e
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = fcp M a b i A

theorem f_loop {im : Image} {p : Nat} (hp : p = 49406 ∨ p = 49417) (hc : CodeAt im (pcOf p) fBody)
    (s : MachineState) (M : Nat → Word) (a b n : Nat) (hn : 0 < n)
    (hpc : s.pc = pcOf p) (h28 : s.getReg .x28 = BitVec.ofNat 64 a) (h29 : s.getReg .x29 = BitVec.ofNat 64 b)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (a + 8 * n))
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (ha : a % 8 = 0) (hb : b % 8 = 0) (ha' : a + 8 * n ≤ 16777216) (hb' : b + 8 * n ≤ 16777216)
    (hov : a + 8 * n ≤ b) :
    ∀ i, i ≤ n → ∃ t, Steps im s (5 * i) (5 * i) t ∧ RegsExcept s t [.x6, .x28, .x29] ∧
      FInv M p a b (a + 8 * n) i t := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, ⟨by rw [hpc, if_pos (by omega)], by simpa using h28,
      by simpa using h29, h30, fun A hA => ?_⟩⟩
    rw [hM A hA]; unfold fcp; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf p := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, u29, ru, mu⟩ := f_iter hp hc t hpc' (a + 8 * i) (b + 8 * i) (a + 8 * n)
      hI.x28 hI.x29 hI.x30 (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : a + 8 * i + 8 < a + 8 * n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show a + 8 * i + 8 = a + 8 * (i + 1) by ring]
    · rw [u29, show b + 8 * i + 8 = b + 8 * (i + 1) by ring]
    · rw [ru.get (by decide), hI.x30]
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (a + 8 * i)) = M (a + 8 * i) := by
        rw [hI.mem _ (by omega)]; unfold fcp; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold fcp
      by_cases hA' : A = b + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show b + 8 * i - b = 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : b ≤ A ∧ A < b + 8 * i ∧ (A - b) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

/-! ### Backward move loop -/
/-- Memory after the `i` highest words `T, T - 8, ..` were moved up by `d`. -/
def bmv (M : Nat → Word) (T d i : Nat) (A : Nat) : Word :=
  if T + d + 8 ≤ A + 8 * i ∧ A ≤ T + d ∧ (T + d - A) % 8 = 0 then M (A - d) else M A

theorem m_iter {im : Image} {p : Nat} (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457)
    (hc : CodeAt im (pcOf p) mBody)
    (t : MachineState) (hpc : t.pc = pcOf p) (c d lo : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 c) (h7 : t.getReg .x7 = BitVec.ofNat 64 d)
    (h30 : t.getReg .x30 = BitVec.ofNat 64 lo)
    (hc8 : c % 8 = 0) (hd8 : d % 8 = 0) (hc' : 8 ≤ c) (hcd : c + d + 8 ≤ 16777216) (hlo : lo < 2 ^ 63) :
    ∃ u, Steps im t 5 5 u ∧ u.pc = (if lo < c - 8 then pcOf p else pcOf (p + 5)) ∧
      u.getReg .x28 = BitVec.ofNat 64 (c - 8) ∧ u.getReg .x7 = BitVec.ofNat 64 d ∧
      RegsExcept t u [.x6, .x28, .x29] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) =
        if A = c + d then t.getMem (BitVec.ofNat 64 c) else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound (run_m p hp) hc t hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [mRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h28, h7, BitVec.add_zero,
      ofNat_add_ofNat]
    exact ⟨valid8P _ hcd (by omega), valid8P _ (by omega) hc8⟩
  · simp only [Result.toState_pc, mRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_sub8 c hc']
    rw [ofNat_slt _ _ hlo (by omega)]
    by_cases h : lo < c - 8 <;> simp [h]
  · simp [mRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_sub8 c hc']
  · simp [mRes, RegFile.get, RegFile.set, RegFile.init, E.eval, h7]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, mRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, mRes, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, h28, h7,
      BitVec.add_zero, ofNat_add_ofNat]
    by_cases hAb : A = c + d
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

structure MInv (M : Nat → Word) (p T d lo i : Nat) (t : MachineState) : Prop where
  pc : t.pc = (if lo + 8 * i < T then pcOf p else pcOf (p + 5))
  x28 : t.getReg .x28 = BitVec.ofNat 64 (T - 8 * i)
  x7 : t.getReg .x7 = BitVec.ofNat 64 d
  x30 : t.getReg .x30 = BitVec.ofNat 64 lo
  mem : ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = bmv M T d i A

/-- The move loop over the `n` words `T, T - 8, .., T - 8 (n - 1) = lo + 8` (`lo` is the exclusive bound in `t5`). -/
theorem m_loop {im : Image} {p : Nat} (hp : p = 49427 ∨ p = 49437 ∨ p = 49447 ∨ p = 49457)
    (hc : CodeAt im (pcOf p) mBody)
    (s : MachineState) (M : Nat → Word) (T d lo n : Nat) (hn : 0 < n) (hT : T = lo + 8 * n)
    (hpc : s.pc = pcOf p) (h28 : s.getReg .x28 = BitVec.ofNat 64 T) (h7 : s.getReg .x7 = BitVec.ofNat 64 d)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 lo)
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (hT8 : T % 8 = 0) (hd8 : d % 8 = 0) (hd : 0 < d) (hlo : 8 ≤ lo) (hTd : T + d + 8 ≤ 16777216) :
    ∀ i, i ≤ n → ∃ t, Steps im s (5 * i) (5 * i) t ∧ RegsExcept s t [.x6, .x28, .x29] ∧
      MInv M p T d lo i t := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, ⟨by rw [hpc, if_pos (by omega)], by simpa using h28,
      h7, h30, fun A hA => ?_⟩⟩
    rw [hM A hA]; unfold bmv; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, hI⟩ := ih (by omega)
    have hpc' : t.pc = pcOf p := by rw [hI.pc, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, u7, ru, mu⟩ := m_iter hp hc t hpc' (T - 8 * i) d lo hI.x28 hI.x7 hI.x30
      (by omega) hd8 (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ⟨?_, ?_, u7, ?_, ?_⟩⟩
    · rw [pu]; by_cases h : lo < T - 8 * i - 8
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show T - 8 * i - 8 = T - 8 * (i + 1) by omega]
    · rw [ru.get (by decide), hI.x30]
    · intro A hA
      have hsrc : t.getMem (BitVec.ofNat 64 (T - 8 * i)) = M (T - 8 * i) := by
        rw [hI.mem _ (by omega)]; unfold bmv; rw [if_neg (by omega)]
      rw [mu A hA, hsrc, hI.mem A hA]
      unfold bmv
      by_cases hA' : A = T - 8 * i + d
      · subst hA'; rw [if_pos rfl, if_pos (by omega), show T - 8 * i + d - d = T - 8 * i by omega]
      · rw [if_neg hA']
        by_cases hin : T + d + 8 ≤ A + 8 * i ∧ A ≤ T + d ∧ (T + d - A) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

/-! ### Zero loop -/
def zfill (M : Nat → Word) (a i : Nat) (A : Nat) : Word :=
  if a ≤ A ∧ A < a + 8 * i ∧ (A - a) % 8 = 0 then 0 else M A

theorem z_iter {im : Image} (hc : CodeAt im (pcOf 49466) zBody)
    (t : MachineState) (hpc : t.pc = pcOf 49466) (a e : Nat)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 a) (h30 : t.getReg .x30 = BitVec.ofNat 64 e)
    (ha : a % 8 = 0) (ha' : a + 8 ≤ 16777216) (he : e < 2 ^ 64) :
    ∃ u, Steps im t 3 3 u ∧ u.pc = (if a + 8 < e then pcOf 49466 else pcOf 49469) ∧
      u.getReg .x28 = BitVec.ofNat 64 (a + 8) ∧ RegsExcept t u [.x28] ∧
      ∀ A < 2 ^ 64, u.getMem (BitVec.ofNat 64 A) = if A = a then 0 else t.getMem (BitVec.ofNat 64 A) := by
  refine ⟨_, symRun_sound run_z hc t hpc ?_, ?_, ?_, ?_, ?_⟩
  · show Oblig.all t _
    simp only [zRes, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, BitVec.add_zero]
    exact valid8P _ ha' ha
  · simp only [Result.toState_pc, zRes, E.eval, CmpOp.eval, BinOp.eval, h28, h30, ofNat_add8']
    rw [ult_ofNat _ _ (by omega) he]
    by_cases h : a + 8 < e <;> simp [h]
  · simp [zRes, RegFile.get, RegFile.set, E.eval, BinOp.eval, h28, ofNat_add8']
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, zRes]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, zRes, memEval_cons, memEval_nil, Addr.eval, E.eval, h28, BitVec.add_zero]
    by_cases hAb : A = a
    · subst hAb; simp
    · rw [if_neg (fun h => hAb ((ofNat_inj hA (by omega)).mp h)), if_neg hAb]

theorem z_loop {im : Image} (hc : CodeAt im (pcOf 49466) zBody)
    (s : MachineState) (M : Nat → Word) (a n : Nat) (hn : 0 < n)
    (hpc : s.pc = pcOf 49466) (h28 : s.getReg .x28 = BitVec.ofNat 64 a)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (a + 8 * n))
    (hM : ∀ A < 2 ^ 64, s.getMem (BitVec.ofNat 64 A) = M A)
    (ha : a % 8 = 0) (ha' : a + 8 * n ≤ 16777216) :
    ∀ i, i ≤ n → ∃ t, Steps im s (3 * i) (3 * i) t ∧ RegsExcept s t [.x28] ∧
      t.pc = (if a + 8 * i < a + 8 * n then pcOf 49466 else pcOf 49469) ∧
      t.getReg .x28 = BitVec.ofNat 64 (a + 8 * i) ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = zfill M a i A := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨s, Steps.refl s, RegsExcept.refl _ _, by rw [hpc, if_pos (by omega)], by simpa using h28,
      fun A hA => ?_⟩
    rw [hM A hA]; unfold zfill; rw [if_neg (by omega)]
  | succ i ih =>
    intro hi
    obtain ⟨t, st, rt, pt, t28, mt⟩ := ih (by omega)
    have hpc' : t.pc = pcOf 49466 := by rw [pt, if_pos (by omega)]
    obtain ⟨u, su, pu, u28, ru, mu⟩ := z_iter hc t hpc' (a + 8 * i) (a + 8 * n) t28
      (by rw [rt.get (by decide), h30]) (by omega) (by omega) (by omega)
    refine ⟨u, Steps.of_eq (st.trans su) (by ring) (by ring), (rt.trans ru).mono (by decide), ?_, ?_, ?_⟩
    · rw [pu]; by_cases h : a + 8 * i + 8 < a + 8 * n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    · rw [u28, show a + 8 * i + 8 = a + 8 * (i + 1) by ring]
    · intro A hA
      rw [mu A hA, mt A hA]
      unfold zfill
      by_cases hA' : A = a + 8 * i
      · subst hA'; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg hA']
        by_cases hin : a ≤ A ∧ A < a + 8 * i ∧ (A - a) % 8 = 0
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]

end ClaudeWCT.W9.Machine.Expand.PostPass
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PostPassB ====
section

/-! # Post-pass, part B: the value copies, the sibling rows, the dispatch and the halt (generated by
`scratch/expand/pp/genB.py` from img-merged/expand.code). -/

namespace ClaudeWCT.W9.Machine.Expand.PostPass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ### The value copies (words 49469 .. 50054) -/
/-- `(destination, offset in the saved chain area at 0x300000)` of the 108 value-word copies, in program order. -/
def vTable : List (Nat × Nat) := [(12552,48),(12560,56),(12480,112),(12488,120),(12656,176),(12664,184),(12584,240),(12592,248),(12760,304),(12768,312),(12688,368),(12696,376),(12864,432),(12872,440),(12792,496),(12800,504),(12968,560),(12976,568),(12896,624),(12904,632),(13072,688),(13080,696),(13000,752),(13008,760),(13176,816),(13184,824),(13104,880),(13112,888),(13280,944),(13288,952),(13208,1008),(13216,1016),(13384,1072),(13392,1080),(13312,1136),(13320,1144),(13488,1200),(13496,1208),(13416,1264),(13424,1272),(13592,1328),(13600,1336),(13520,1392),(13528,1400),(13696,1456),(13704,1464),(13624,1520),(13632,1528),(13800,1584),(13808,1592),(13728,1648),(13736,1656),(13904,1712),(13912,1720),(13832,1776),(13840,1784),(14008,1840),(14016,1848),(13936,1904),(13944,1912),(14112,1968),(14120,1976),(14040,2032),(14048,2040),(14216,2096),(14224,2104),(14144,2160),(14152,2168),(14320,2224),(14328,2232),(14248,2288),(14256,2296),(14424,2352),(14432,2360),(14352,2416),(14360,2424),(14528,2480),(14536,2488),(14456,2544),(14464,2552),(14632,2608),(14640,2616),(14560,2672),(14568,2680),(14736,2736),(14744,2744),(14664,2800),(14672,2808),(14840,2864),(14848,2872),(14768,2928),(14776,2936),(14944,2992),(14952,3000),(14872,3056),(14880,3064),(15048,3120),(15056,3128),(14976,3184),(14984,3192),(15152,3248),(15160,3256),(15080,3312),(15088,3320),(15256,3376),(15264,3384),(15184,3440),(15192,3448)]
def cVals : List (BitVec 32) := [0x300eb7,0xe8e93,0x3e37,0x108e0e13,0x3000393,0x1d383b3,0x3b303,0x6e3023,0x3800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0xc0e0e13,0x7000393,0x1d383b3,0x3b303,0x6e3023,0x7800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x170e0e13,0xb000393,0x1d383b3,0x3b303,0x6e3023,0xb800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x128e0e13,0xf000393,0x1d383b3,0x3b303,0x6e3023,0xf800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x1d8e0e13,0x13000393,0x1d383b3,0x3b303,0x6e3023,0x13800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x190e0e13,0x17000393,0x1d383b3,0x3b303,0x6e3023,0x17800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x240e0e13,0x1b000393,0x1d383b3,0x3b303,0x6e3023,0x1b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x1f8e0e13,0x1f000393,0x1d383b3,0x3b303,0x6e3023,0x1f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x2a8e0e13,0x23000393,0x1d383b3,0x3b303,0x6e3023,0x23800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x260e0e13,0x27000393,0x1d383b3,0x3b303,0x6e3023,0x27800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x310e0e13,0x2b000393,0x1d383b3,0x3b303,0x6e3023,0x2b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x2c8e0e13,0x2f000393,0x1d383b3,0x3b303,0x6e3023,0x2f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x378e0e13,0x33000393,0x1d383b3,0x3b303,0x6e3023,0x33800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x330e0e13,0x37000393,0x1d383b3,0x3b303,0x6e3023,0x37800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x3e0e0e13,0x3b000393,0x1d383b3,0x3b303,0x6e3023,0x3b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x398e0e13,0x3f000393,0x1d383b3,0x3b303,0x6e3023,0x3f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x448e0e13,0x43000393,0x1d383b3,0x3b303,0x6e3023,0x43800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x400e0e13,0x47000393,0x1d383b3,0x3b303,0x6e3023,0x47800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x4b0e0e13,0x4b000393,0x1d383b3,0x3b303,0x6e3023,0x4b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x468e0e13,0x4f000393,0x1d383b3,0x3b303,0x6e3023,0x4f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x518e0e13,0x53000393,0x1d383b3,0x3b303,0x6e3023,0x53800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x4d0e0e13,0x57000393,0x1d383b3,0x3b303,0x6e3023,0x57800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x580e0e13,0x5b000393,0x1d383b3,0x3b303,0x6e3023,0x5b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x538e0e13,0x5f000393,0x1d383b3,0x3b303,0x6e3023,0x5f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x5e8e0e13,0x63000393,0x1d383b3,0x3b303,0x6e3023,0x63800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x5a0e0e13,0x67000393,0x1d383b3,0x3b303,0x6e3023,0x67800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x650e0e13,0x6b000393,0x1d383b3,0x3b303,0x6e3023,0x6b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x608e0e13,0x6f000393,0x1d383b3,0x3b303,0x6e3023,0x6f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x6b8e0e13,0x73000393,0x1d383b3,0x3b303,0x6e3023,0x73800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x670e0e13,0x77000393,0x1d383b3,0x3b303,0x6e3023,0x77800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x720e0e13,0x7b000393,0x1d383b3,0x3b303,0x6e3023,0x7b800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x6d8e0e13,0x7f000393,0x1d383b3,0x3b303,0x6e3023,0x7f800393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x788e0e13,0x13b7,0x83038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x83838393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x740e0e13,0x13b7,0x87038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x87838393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x7f0e0e13,0x13b7,0x8b038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x8b838393,0x1d383b3,0x3b303,0x6e3423,0x3e37,0x7a8e0e13,0x13b7,0x8f038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x8f838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x858e0e13,0x13b7,0x93038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x93838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x810e0e13,0x13b7,0x97038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x97838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x8c0e0e13,0x13b7,0x9b038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x9b838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x878e0e13,0x13b7,0x9f038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0x9f838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x928e0e13,0x13b7,0xa3038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xa3838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x8e0e0e13,0x13b7,0xa7038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xa7838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x990e0e13,0x13b7,0xab038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xab838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x948e0e13,0x13b7,0xaf038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xaf838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x9f8e0e13,0x13b7,0xb3038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xb3838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0x9b0e0e13,0x13b7,0xb7038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xb7838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xa60e0e13,0x13b7,0xbb038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xbb838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xa18e0e13,0x13b7,0xbf038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xbf838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xac8e0e13,0x13b7,0xc3038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xc3838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xa80e0e13,0x13b7,0xc7038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xc7838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xb30e0e13,0x13b7,0xcb038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xcb838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xae8e0e13,0x13b7,0xcf038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xcf838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xb98e0e13,0x13b7,0xd3038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xd3838393,0x1d383b3,0x3b303,0x6e3423,0x4e37,0xb50e0e13,0x13b7,0xd7038393,0x1d383b3,0x3b303,0x6e3023,0x13b7,0xd7838393,0x1d383b3,0x3b303,0x6e3423]
def vWrite (e : Nat × Nat) : Addr × E := (⟨none, BitVec.ofNat 64 e.1⟩, .ld (.c (BitVec.ofNat 64 (0x300000 + e.2))))
def vWrites : SymMem := vTable.reverse.map vWrite
def vRegs : RegFile := (((RegFile.init.set .x6 (.ld (.c (BitVec.ofNat 64 3149176)))).set .x7 (.c (BitVec.ofNat 64 3149176))).set .x28
  (.c (BitVec.ofNat 64 15184))).set .x29 (.c (BitVec.ofNat 64 0x300000))
def vRes : Result := ⟨⟨vRegs, vWrites, []⟩, .c (pcOf 50055), .endOfCode, 586, 586⟩
theorem code_vals : CodeAt Images.expandImage (pcOf 49469) cVals := code_last (by decide) (by decide) (by decide +kernel)
theorem run_vals : symRun cfgP cVals (pcOf 49469) 700 = some vRes := by kernel_rfl

/-! ### The sibling rows -/
/-- Line A: `(load offset from 0x301000, store offset from 11792)` of the 12 word copies of each row. -/
def rowsA : List (List (Nat × Nat)) := [[(528,464),(536,472),(576,512),(584,520),(624,560),(632,568),(672,608),(680,616),(720,656),(728,664),(448,384),(456,392)],[(464,400),(472,408),(576,512),(584,520),(624,560),(632,568),(672,608),(680,616),(720,656),(728,664),(448,384),(456,392)],[(528,512),(536,520),(544,400),(552,408),(656,560),(664,568),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(464,448),(472,456),(544,400),(552,408),(656,560),(664,568),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(528,512),(536,520),(576,560),(584,568),(592,400),(600,408),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(464,448),(472,456),(576,560),(584,568),(592,400),(600,408),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(528,560),(536,568),(592,448),(600,456),(544,400),(552,408),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(464,496),(472,504),(592,448),(600,456),(544,400),(552,408),(704,608),(712,616),(752,656),(760,664),(448,384),(456,392)],[(528,512),(536,520),(576,560),(584,568),(624,608),(632,616),(640,400),(648,408),(752,656),(760,664),(448,384),(456,392)],[(464,448),(472,456),(576,560),(584,568),(624,608),(632,616),(640,400),(648,408),(752,656),(760,664),(448,384),(456,392)],[(528,560),(536,568),(592,448),(600,456),(704,608),(712,616),(544,400),(552,408),(752,656),(760,664),(448,384),(456,392)],[(464,496),(472,504),(592,448),(600,456),(704,608),(712,616),(544,400),(552,408),(752,656),(760,664),(448,384),(456,392)],[(528,560),(536,568),(576,608),(584,616),(640,448),(648,456),(592,400),(600,408),(752,656),(760,664),(448,384),(456,392)],[(464,496),(472,504),(576,608),(584,616),(640,448),(648,456),(592,400),(600,408),(752,656),(760,664),(448,384),(456,392)],[(528,608),(536,616),(640,496),(648,504),(592,448),(600,456),(544,400),(552,408),(752,656),(760,664),(448,384),(456,392)],[(464,544),(472,552),(640,496),(648,504),(592,448),(600,456),(544,400),(552,408),(752,656),(760,664),(448,384),(456,392)],[(528,512),(536,520),(576,560),(584,568),(624,608),(632,616),(672,656),(680,664),(688,400),(696,408),(448,384),(456,392)],[(464,448),(472,456),(576,560),(584,568),(624,608),(632,616),(672,656),(680,664),(688,400),(696,408),(448,384),(456,392)],[(528,560),(536,568),(592,448),(600,456),(704,608),(712,616),(752,656),(760,664),(544,400),(552,408),(448,384),(456,392)],[(464,496),(472,504),(592,448),(600,456),(704,608),(712,616),(752,656),(760,664),(544,400),(552,408),(448,384),(456,392)],[(528,560),(536,568),(576,608),(584,616),(640,448),(648,456),(752,656),(760,664),(592,400),(600,408),(448,384),(456,392)],[(464,496),(472,504),(576,608),(584,616),(640,448),(648,456),(752,656),(760,664),(592,400),(600,408),(448,384),(456,392)],[(528,608),(536,616),(640,496),(648,504),(592,448),(600,456),(752,656),(760,664),(544,400),(552,408),(448,384),(456,392)],[(464,544),(472,552),(640,496),(648,504),(592,448),(600,456),(752,656),(760,664),(544,400),(552,408),(448,384),(456,392)],[(528,560),(536,568),(576,608),(584,616),(624,656),(632,664),(688,448),(696,456),(640,400),(648,408),(448,384),(456,392)],[(464,496),(472,504),(576,608),(584,616),(624,656),(632,664),(688,448),(696,456),(640,400),(648,408),(448,384),(456,392)],[(528,608),(536,616),(640,496),(648,504),(752,656),(760,664),(592,448),(600,456),(544,400),(552,408),(448,384),(456,392)],[(464,544),(472,552),(640,496),(648,504),(752,656),(760,664),(592,448),(600,456),(544,400),(552,408),(448,384),(456,392)],[(528,608),(536,616),(576,656),(584,664),(688,496),(696,504),(640,448),(648,456),(592,400),(600,408),(448,384),(456,392)],[(464,544),(472,552),(576,656),(584,664),(688,496),(696,504),(640,448),(648,456),(592,400),(600,408),(448,384),(456,392)],[(528,656),(536,664),(688,544),(696,552),(640,496),(648,504),(592,448),(600,456),(544,400),(552,408),(448,384),(456,392)],[(464,592),(472,600),(688,544),(696,552),(640,496),(648,504),(592,448),(600,456),(544,400),(552,408),(448,384),(456,392)],[(512,448),(520,456),(560,496),(568,504),(608,544),(616,552),(656,592),(664,600),(704,640),(712,648),(400,336),(408,344)],[(448,384),(456,392),(560,496),(568,504),(608,544),(616,552),(656,592),(664,600),(704,640),(712,648),(400,336),(408,344)],[(512,496),(520,504),(528,384),(536,392),(640,544),(648,552),(688,592),(696,600),(736,640),(744,648),(400,336),(408,344)],[(448,432),(456,440),(528,384),(536,392),(640,544),(648,552),(688,592),(696,600),(736,640),(744,648),(400,336),(408,344)],[(512,496),(520,504),(560,544),(568,552),(576,384),(584,392),(688,592),(696,600),(736,640),(744,648),(400,336),(408,344)],[(448,432),(456,440),(560,544),(568,552),(576,384),(584,392),(688,592),(696,600),(736,640),(744,648),(400,336),(408,344)],[(512,544),(520,552),(528,432),(536,440),(704,384),(712,392),(640,592),(648,600),(688,640),(696,648),(400,336),(408,344)],[(448,480),(456,488),(528,432),(536,440),(704,384),(712,392),(640,592),(648,600),(688,640),(696,648),(400,336),(408,344)],[(512,496),(520,504),(560,544),(568,552),(608,592),(616,600),(624,384),(632,392),(736,640),(744,648),(400,336),(408,344)],[(448,432),(456,440),(560,544),(568,552),(608,592),(616,600),(624,384),(632,392),(736,640),(744,648),(400,336),(408,344)],[(512,544),(520,552),(528,432),(536,440),(640,592),(648,600),(704,384),(712,392),(688,640),(696,648),(400,336),(408,344)],[(448,480),(456,488),(528,432),(536,440),(640,592),(648,600),(704,384),(712,392),(688,640),(696,648),(400,336),(408,344)],[(512,544),(520,552),(560,592),(568,600),(576,432),(584,440),(704,384),(712,392),(688,640),(696,648),(400,336),(408,344)],[(448,480),(456,488),(560,592),(568,600),(576,432),(584,440),(704,384),(712,392),(688,640),(696,648),(400,336),(408,344)],[(512,592),(520,600),(528,480),(536,488),(704,432),(712,440),(656,384),(664,392),(640,640),(648,648),(400,336),(408,344)],[(448,528),(456,536),(528,480),(536,488),(704,432),(712,440),(656,384),(664,392),(640,640),(648,648),(400,336),(408,344)],[(512,496),(520,504),(560,544),(568,552),(608,592),(616,600),(656,640),(664,648),(672,384),(680,392),(400,336),(408,344)],[(448,432),(456,440),(560,544),(568,552),(608,592),(616,600),(656,640),(664,648),(672,384),(680,392),(400,336),(408,344)],[(512,544),(520,552),(528,432),(536,440),(640,592),(648,600),(688,640),(696,648),(704,384),(712,392),(400,336),(408,344)],[(448,480),(456,488),(528,432),(536,440),(640,592),(648,600),(688,640),(696,648),(704,384),(712,392),(400,336),(408,344)],[(512,544),(520,552),(560,592),(568,600),(576,432),(584,440),(688,640),(696,648),(704,384),(712,392),(400,336),(408,344)],[(448,480),(456,488),(560,592),(568,600),(576,432),(584,440),(688,640),(696,648),(704,384),(712,392),(400,336),(408,344)],[(512,592),(520,600),(528,480),(536,488),(704,432),(712,440),(640,640),(648,648),(656,384),(664,392),(400,336),(408,344)],[(448,528),(456,536),(528,480),(536,488),(704,432),(712,440),(640,640),(648,648),(656,384),(664,392),(400,336),(408,344)],[(512,544),(520,552),(560,592),(568,600),(608,640),(616,648),(624,432),(632,440),(704,384),(712,392),(400,336),(408,344)],[(448,480),(456,488),(560,592),(568,600),(608,640),(616,648),(624,432),(632,440),(704,384),(712,392),(400,336),(408,344)],[(512,592),(520,600),(528,480),(536,488),(640,640),(648,648),(704,432),(712,440),(656,384),(664,392),(400,336),(408,344)],[(448,528),(456,536),(528,480),(536,488),(640,640),(648,648),(704,432),(712,440),(656,384),(664,392),(400,336),(408,344)],[(512,592),(520,600),(560,640),(568,648),(576,480),(584,488),(704,432),(712,440),(656,384),(664,392),(400,336),(408,344)],[(448,528),(456,536),(560,640),(568,648),(576,480),(584,488),(704,432),(712,440),(656,384),(664,392),(400,336),(408,344)],[(512,640),(520,648),(528,528),(536,536),(704,480),(712,488),(656,432),(664,440),(608,384),(616,392),(400,336),(408,344)],[(448,576),(456,584),(528,528),(536,536),(704,480),(712,488),(656,432),(664,440),(608,384),(616,392),(400,336),(408,344)]]
def rowCodeA : List (List (BitVec 32)) := [[0x210eb303,0x1c6f3823,0x218eb303,0x1c6f3c23,0x240eb303,0x206f3023,0x248eb303,0x206f3423,0x270eb303,0x226f3823,0x278eb303,0x226f3c23,0x2a0eb303,0x266f3023,0x2a8eb303,0x266f3423,0x2d0eb303,0x286f3823,0x2d8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xf81ff06f],[0x1d0eb303,0x186f3823,0x1d8eb303,0x186f3c23,0x240eb303,0x206f3023,0x248eb303,0x206f3423,0x270eb303,0x226f3823,0x278eb303,0x226f3c23,0x2a0eb303,0x266f3023,0x2a8eb303,0x266f3423,0x2d0eb303,0x286f3823,0x2d8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xf01ff06f],[0x210eb303,0x206f3023,0x218eb303,0x206f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x290eb303,0x226f3823,0x298eb303,0x226f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xe81ff06f],[0x1d0eb303,0x1c6f3023,0x1d8eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x290eb303,0x226f3823,0x298eb303,0x226f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xe01ff06f],[0x210eb303,0x206f3023,0x218eb303,0x206f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xd81ff06f],[0x1d0eb303,0x1c6f3023,0x1d8eb303,0x1c6f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xd01ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xc81ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xc01ff06f],[0x210eb303,0x206f3023,0x218eb303,0x206f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x270eb303,0x266f3023,0x278eb303,0x266f3423,0x280eb303,0x186f3823,0x288eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xb81ff06f],[0x1d0eb303,0x1c6f3023,0x1d8eb303,0x1c6f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x270eb303,0x266f3023,0x278eb303,0x266f3423,0x280eb303,0x186f3823,0x288eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xb01ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xa81ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xa01ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x981ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x901ff06f],[0x210eb303,0x266f3023,0x218eb303,0x266f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x881ff06f],[0x1d0eb303,0x226f3023,0x1d8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x801ff06f],[0x210eb303,0x206f3023,0x218eb303,0x206f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x270eb303,0x266f3023,0x278eb303,0x266f3423,0x2a0eb303,0x286f3823,0x2a8eb303,0x286f3c23,0x2b0eb303,0x186f3823,0x2b8eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xf80ff06f],[0x1d0eb303,0x1c6f3023,0x1d8eb303,0x1c6f3423,0x240eb303,0x226f3823,0x248eb303,0x226f3c23,0x270eb303,0x266f3023,0x278eb303,0x266f3423,0x2a0eb303,0x286f3823,0x2a8eb303,0x286f3c23,0x2b0eb303,0x186f3823,0x2b8eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xf00ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xe80ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2c0eb303,0x266f3023,0x2c8eb303,0x266f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xe00ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xd80ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xd00ff06f],[0x210eb303,0x266f3023,0x218eb303,0x266f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xc80ff06f],[0x1d0eb303,0x226f3023,0x1d8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xc00ff06f],[0x210eb303,0x226f3823,0x218eb303,0x226f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x270eb303,0x286f3823,0x278eb303,0x286f3c23,0x2b0eb303,0x1c6f3023,0x2b8eb303,0x1c6f3423,0x280eb303,0x186f3823,0x288eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xb80ff06f],[0x1d0eb303,0x1e6f3823,0x1d8eb303,0x1e6f3c23,0x240eb303,0x266f3023,0x248eb303,0x266f3423,0x270eb303,0x286f3823,0x278eb303,0x286f3c23,0x2b0eb303,0x1c6f3023,0x2b8eb303,0x1c6f3423,0x280eb303,0x186f3823,0x288eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xb00ff06f],[0x210eb303,0x266f3023,0x218eb303,0x266f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xa80ff06f],[0x1d0eb303,0x226f3023,0x1d8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x2f0eb303,0x286f3823,0x2f8eb303,0x286f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0xa00ff06f],[0x210eb303,0x266f3023,0x218eb303,0x266f3423,0x240eb303,0x286f3823,0x248eb303,0x286f3c23,0x2b0eb303,0x1e6f3823,0x2b8eb303,0x1e6f3c23,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x980ff06f],[0x1d0eb303,0x226f3023,0x1d8eb303,0x226f3423,0x240eb303,0x286f3823,0x248eb303,0x286f3c23,0x2b0eb303,0x1e6f3823,0x2b8eb303,0x1e6f3c23,0x280eb303,0x1c6f3023,0x288eb303,0x1c6f3423,0x250eb303,0x186f3823,0x258eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x900ff06f],[0x210eb303,0x286f3823,0x218eb303,0x286f3c23,0x2b0eb303,0x226f3023,0x2b8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x880ff06f],[0x1d0eb303,0x246f3823,0x1d8eb303,0x246f3c23,0x2b0eb303,0x226f3023,0x2b8eb303,0x226f3423,0x280eb303,0x1e6f3823,0x288eb303,0x1e6f3c23,0x250eb303,0x1c6f3023,0x258eb303,0x1c6f3423,0x220eb303,0x186f3823,0x228eb303,0x186f3c23,0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x800ff06f],[0x200eb303,0x1c6f3023,0x208eb303,0x1c6f3423,0x230eb303,0x1e6f3823,0x238eb303,0x1e6f3c23,0x260eb303,0x226f3023,0x268eb303,0x226f3423,0x290eb303,0x246f3823,0x298eb303,0x246f3c23,0x2c0eb303,0x286f3023,0x2c8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xf81fe06f],[0x1c0eb303,0x186f3023,0x1c8eb303,0x186f3423,0x230eb303,0x1e6f3823,0x238eb303,0x1e6f3c23,0x260eb303,0x226f3023,0x268eb303,0x226f3423,0x290eb303,0x246f3823,0x298eb303,0x246f3c23,0x2c0eb303,0x286f3023,0x2c8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xf01fe06f],[0x200eb303,0x1e6f3823,0x208eb303,0x1e6f3c23,0x210eb303,0x186f3023,0x218eb303,0x186f3423,0x280eb303,0x226f3023,0x288eb303,0x226f3423,0x2b0eb303,0x246f3823,0x2b8eb303,0x246f3c23,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xe81fe06f],[0x1c0eb303,0x1a6f3823,0x1c8eb303,0x1a6f3c23,0x210eb303,0x186f3023,0x218eb303,0x186f3423,0x280eb303,0x226f3023,0x288eb303,0x226f3423,0x2b0eb303,0x246f3823,0x2b8eb303,0x246f3c23,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xe01fe06f],[0x200eb303,0x1e6f3823,0x208eb303,0x1e6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x240eb303,0x186f3023,0x248eb303,0x186f3423,0x2b0eb303,0x246f3823,0x2b8eb303,0x246f3c23,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xd81fe06f],[0x1c0eb303,0x1a6f3823,0x1c8eb303,0x1a6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x240eb303,0x186f3023,0x248eb303,0x186f3423,0x2b0eb303,0x246f3823,0x2b8eb303,0x246f3c23,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xd01fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xc81fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xc01fe06f],[0x200eb303,0x1e6f3823,0x208eb303,0x1e6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x260eb303,0x246f3823,0x268eb303,0x246f3c23,0x270eb303,0x186f3023,0x278eb303,0x186f3423,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xb81fe06f],[0x1c0eb303,0x1a6f3823,0x1c8eb303,0x1a6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x260eb303,0x246f3823,0x268eb303,0x246f3c23,0x270eb303,0x186f3023,0x278eb303,0x186f3423,0x2e0eb303,0x286f3023,0x2e8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xb01fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xa81fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xa01fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x240eb303,0x1a6f3823,0x248eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x981fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x240eb303,0x1a6f3823,0x248eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x901fe06f],[0x200eb303,0x246f3823,0x208eb303,0x246f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x881fe06f],[0x1c0eb303,0x206f3823,0x1c8eb303,0x206f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x801fe06f],[0x200eb303,0x1e6f3823,0x208eb303,0x1e6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x260eb303,0x246f3823,0x268eb303,0x246f3c23,0x290eb303,0x286f3023,0x298eb303,0x286f3423,0x2a0eb303,0x186f3023,0x2a8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xf80fe06f],[0x1c0eb303,0x1a6f3823,0x1c8eb303,0x1a6f3c23,0x230eb303,0x226f3023,0x238eb303,0x226f3423,0x260eb303,0x246f3823,0x268eb303,0x246f3c23,0x290eb303,0x286f3023,0x298eb303,0x286f3423,0x2a0eb303,0x186f3023,0x2a8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xf00fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xe80fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x210eb303,0x1a6f3823,0x218eb303,0x1a6f3c23,0x280eb303,0x246f3823,0x288eb303,0x246f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xe00fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x240eb303,0x1a6f3823,0x248eb303,0x1a6f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xd80fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x240eb303,0x1a6f3823,0x248eb303,0x1a6f3c23,0x2b0eb303,0x286f3023,0x2b8eb303,0x286f3423,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xd00fe06f],[0x200eb303,0x246f3823,0x208eb303,0x246f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xc80fe06f],[0x1c0eb303,0x206f3823,0x1c8eb303,0x206f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xc00fe06f],[0x200eb303,0x226f3023,0x208eb303,0x226f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x260eb303,0x286f3023,0x268eb303,0x286f3423,0x270eb303,0x1a6f3823,0x278eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xb80fe06f],[0x1c0eb303,0x1e6f3023,0x1c8eb303,0x1e6f3423,0x230eb303,0x246f3823,0x238eb303,0x246f3c23,0x260eb303,0x286f3023,0x268eb303,0x286f3423,0x270eb303,0x1a6f3823,0x278eb303,0x1a6f3c23,0x2c0eb303,0x186f3023,0x2c8eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xb00fe06f],[0x200eb303,0x246f3823,0x208eb303,0x246f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xa80fe06f],[0x1c0eb303,0x206f3823,0x1c8eb303,0x206f3c23,0x210eb303,0x1e6f3023,0x218eb303,0x1e6f3423,0x280eb303,0x286f3023,0x288eb303,0x286f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0xa00fe06f],[0x200eb303,0x246f3823,0x208eb303,0x246f3c23,0x230eb303,0x286f3023,0x238eb303,0x286f3423,0x240eb303,0x1e6f3023,0x248eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x980fe06f],[0x1c0eb303,0x206f3823,0x1c8eb303,0x206f3c23,0x230eb303,0x286f3023,0x238eb303,0x286f3423,0x240eb303,0x1e6f3023,0x248eb303,0x1e6f3423,0x2c0eb303,0x1a6f3823,0x2c8eb303,0x1a6f3c23,0x290eb303,0x186f3023,0x298eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x900fe06f],[0x200eb303,0x286f3023,0x208eb303,0x286f3423,0x210eb303,0x206f3823,0x218eb303,0x206f3c23,0x2c0eb303,0x1e6f3023,0x2c8eb303,0x1e6f3423,0x290eb303,0x1a6f3823,0x298eb303,0x1a6f3c23,0x260eb303,0x186f3023,0x268eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x880fe06f],[0x1c0eb303,0x246f3023,0x1c8eb303,0x246f3423,0x210eb303,0x206f3823,0x218eb303,0x206f3c23,0x2c0eb303,0x1e6f3023,0x2c8eb303,0x1e6f3423,0x290eb303,0x1a6f3823,0x298eb303,0x1a6f3c23,0x260eb303,0x186f3023,0x268eb303,0x186f3423,0x190eb303,0x146f3823,0x198eb303,0x146f3c23,0x800fe06f]]
/-- Line B: `(load offset from 0x301000, store offset from 11792)` of the 12 word copies of each row. -/
def rowsB : List (List (Nat × Nat)) := [[(48,48),(56,56),(96,96),(104,104),(144,144),(152,152),(192,192),(200,200),(240,240),(248,248),(288,288),(296,296)],[(0,0),(8,8),(112,112),(120,120),(160,160),(168,168),(208,208),(216,216),(256,256),(264,264),(304,304),(312,312)],[(48,112),(56,120),(64,0),(72,8),(176,160),(184,168),(224,208),(232,216),(272,256),(280,264),(320,304),(328,312)],[(0,48),(8,56),(80,0),(88,8),(192,160),(200,168),(240,208),(248,216),(288,256),(296,264),(336,304),(344,312)],[(48,112),(56,120),(96,160),(104,168),(112,0),(120,8),(224,208),(232,216),(272,256),(280,264),(320,304),(328,312)],[(0,48),(8,56),(112,160),(120,168),(128,0),(136,8),(240,208),(248,216),(288,256),(296,264),(336,304),(344,312)],[(48,160),(56,168),(64,48),(72,56),(144,0),(152,8),(256,208),(264,216),(304,256),(312,264),(352,304),(360,312)],[(0,96),(8,104),(80,48),(88,56),(160,0),(168,8),(272,208),(280,216),(320,256),(328,264),(368,304),(376,312)],[(48,112),(56,120),(96,160),(104,168),(144,208),(152,216),(160,0),(168,8),(272,256),(280,264),(320,304),(328,312)],[(0,48),(8,56),(112,160),(120,168),(160,208),(168,216),(176,0),(184,8),(288,256),(296,264),(336,304),(344,312)],[(48,160),(56,168),(64,48),(72,56),(176,208),(184,216),(192,0),(200,8),(304,256),(312,264),(352,304),(360,312)],[(0,96),(8,104),(80,48),(88,56),(192,208),(200,216),(208,0),(216,8),(320,256),(328,264),(368,304),(376,312)],[(48,160),(56,168),(96,208),(104,216),(112,48),(120,56),(192,0),(200,8),(304,256),(312,264),(352,304),(360,312)],[(0,96),(8,104),(112,208),(120,216),(128,48),(136,56),(208,0),(216,8),(320,256),(328,264),(368,304),(376,312)],[(48,208),(56,216),(64,96),(72,104),(144,48),(152,56),(320,0),(328,8),(256,256),(264,264),(304,304),(312,312)],[(0,144),(8,152),(80,96),(88,104),(208,48),(216,56),(160,0),(168,8),(320,256),(328,264),(368,304),(376,312)],[(48,112),(56,120),(96,160),(104,168),(144,208),(152,216),(192,256),(200,264),(208,0),(216,8),(320,304),(328,312)],[(0,48),(8,56),(112,160),(120,168),(160,208),(168,216),(208,256),(216,264),(224,0),(232,8),(336,304),(344,312)],[(48,160),(56,168),(64,48),(72,56),(176,208),(184,216),(224,256),(232,264),(240,0),(248,8),(352,304),(360,312)],[(0,96),(8,104),(80,48),(88,56),(192,208),(200,216),(240,256),(248,264),(256,0),(264,8),(368,304),(376,312)],[(48,160),(56,168),(96,208),(104,216),(112,48),(120,56),(224,256),(232,264),(240,0),(248,8),(352,304),(360,312)],[(0,96),(8,104),(112,208),(120,216),(128,48),(136,56),(240,256),(248,264),(256,0),(264,8),(368,304),(376,312)],[(48,208),(56,216),(64,96),(72,104),(144,48),(152,56),(256,256),(264,264),(320,0),(328,8),(304,304),(312,312)],[(0,144),(8,152),(80,96),(88,104),(208,48),(216,56),(320,256),(328,264),(160,0),(168,8),(368,304),(376,312)],[(48,160),(56,168),(96,208),(104,216),(144,256),(152,264),(160,48),(168,56),(240,0),(248,8),(352,304),(360,312)],[(0,96),(8,104),(112,208),(120,216),(160,256),(168,264),(176,48),(184,56),(256,0),(264,8),(368,304),(376,312)],[(48,208),(56,216),(64,96),(72,104),(176,256),(184,264),(192,48),(200,56),(320,0),(328,8),(304,304),(312,312)],[(0,144),(8,152),(80,96),(88,104),(192,256),(200,264),(256,48),(264,56),(208,0),(216,8),(368,304),(376,312)],[(48,208),(56,216),(96,256),(104,264),(112,96),(120,104),(192,48),(200,56),(320,0),(328,8),(304,304),(312,312)],[(0,144),(8,152),(112,256),(120,264),(128,96),(136,104),(256,48),(264,56),(208,0),(216,8),(368,304),(376,312)],[(48,256),(56,264),(64,144),(72,152),(144,96),(152,104),(320,48),(328,56),(272,0),(280,8),(256,304),(264,312)],[(0,192),(8,200),(80,144),(88,152),(256,96),(264,104),(208,48),(216,56),(160,0),(168,8),(368,304),(376,312)],[(48,112),(56,120),(96,160),(104,168),(144,208),(152,216),(192,256),(200,264),(240,304),(248,312),(256,0),(264,8)],[(0,48),(8,56),(112,160),(120,168),(160,208),(168,216),(208,256),(216,264),(256,304),(264,312),(272,0),(280,8)],[(48,160),(56,168),(64,48),(72,56),(176,208),(184,216),(224,256),(232,264),(272,304),(280,312),(288,0),(296,8)],[(0,96),(8,104),(80,48),(88,56),(192,208),(200,216),(240,256),(248,264),(288,304),(296,312),(304,0),(312,8)],[(48,160),(56,168),(96,208),(104,216),(112,48),(120,56),(224,256),(232,264),(272,304),(280,312),(288,0),(296,8)],[(0,96),(8,104),(112,208),(120,216),(128,48),(136,56),(240,256),(248,264),(288,304),(296,312),(304,0),(312,8)],[(48,208),(56,216),(64,96),(72,104),(144,48),(152,56),(256,256),(264,264),(304,304),(312,312),(320,0),(328,8)],[(0,144),(8,152),(80,96),(88,104),(208,48),(216,56),(320,256),(328,264),(368,304),(376,312),(160,0),(168,8)],[(48,160),(56,168),(96,208),(104,216),(144,256),(152,264),(160,48),(168,56),(272,304),(280,312),(288,0),(296,8)],[(0,96),(8,104),(112,208),(120,216),(160,256),(168,264),(176,48),(184,56),(288,304),(296,312),(304,0),(312,8)],[(48,208),(56,216),(64,96),(72,104),(176,256),(184,264),(192,48),(200,56),(304,304),(312,312),(320,0),(328,8)],[(0,144),(8,152),(80,96),(88,104),(192,256),(200,264),(256,48),(264,56),(368,304),(376,312),(208,0),(216,8)],[(48,208),(56,216),(96,256),(104,264),(112,96),(120,104),(192,48),(200,56),(304,304),(312,312),(320,0),(328,8)],[(0,144),(8,152),(112,256),(120,264),(128,96),(136,104),(256,48),(264,56),(368,304),(376,312),(208,0),(216,8)],[(48,256),(56,264),(64,144),(72,152),(144,96),(152,104),(320,48),(328,56),(256,304),(264,312),(272,0),(280,8)],[(0,192),(8,200),(80,144),(88,152),(256,96),(264,104),(208,48),(216,56),(368,304),(376,312),(160,0),(168,8)],[(48,160),(56,168),(96,208),(104,216),(144,256),(152,264),(192,304),(200,312),(208,48),(216,56),(288,0),(296,8)],[(0,96),(8,104),(112,208),(120,216),(160,256),(168,264),(208,304),(216,312),(224,48),(232,56),(304,0),(312,8)],[(48,208),(56,216),(64,96),(72,104),(176,256),(184,264),(224,304),(232,312),(240,48),(248,56),(320,0),(328,8)],[(0,144),(8,152),(80,96),(88,104),(192,256),(200,264),(240,304),(248,312),(304,48),(312,56),(256,0),(264,8)],[(48,208),(56,216),(96,256),(104,264),(112,96),(120,104),(224,304),(232,312),(240,48),(248,56),(320,0),(328,8)],[(0,144),(8,152),(112,256),(120,264),(128,96),(136,104),(240,304),(248,312),(304,48),(312,56),(256,0),(264,8)],[(48,256),(56,264),(64,144),(72,152),(144,96),(152,104),(256,304),(264,312),(320,48),(328,56),(272,0),(280,8)],[(0,192),(8,200),(80,144),(88,152),(256,96),(264,104),(368,304),(376,312),(208,48),(216,56),(160,0),(168,8)],[(48,208),(56,216),(96,256),(104,264),(144,304),(152,312),(160,96),(168,104),(240,48),(248,56),(320,0),(328,8)],[(0,144),(8,152),(112,256),(120,264),(160,304),(168,312),(176,96),(184,104),(304,48),(312,56),(256,0),(264,8)],[(48,256),(56,264),(64,144),(72,152),(176,304),(184,312),(192,96),(200,104),(320,48),(328,56),(272,0),(280,8)],[(0,192),(8,200),(80,144),(88,152),(192,304),(200,312),(304,96),(312,104),(256,48),(264,56),(208,0),(216,8)],[(48,256),(56,264),(96,304),(104,312),(112,144),(120,152),(192,96),(200,104),(320,48),(328,56),(272,0),(280,8)],[(0,192),(8,200),(112,304),(120,312),(128,144),(136,152),(304,96),(312,104),(256,48),(264,56),(208,0),(216,8)],[(48,304),(56,312),(64,192),(72,200),(144,144),(152,152),(320,96),(328,104),(272,48),(280,56),(224,0),(232,8)],[(0,240),(8,248),(80,192),(88,200),(304,144),(312,152),(256,96),(264,104),(208,48),(216,56),(160,0),(168,8)]]
def rowCodeB : List (List (BitVec 32)) := [[0x30eb303,0x26f3823,0x38eb303,0x26f3c23,0x60eb303,0x66f3023,0x68eb303,0x66f3423,0x90eb303,0x86f3823,0x98eb303,0x86f3c23,0xc0eb303,0xc6f3023,0xc8eb303,0xc6f3423,0xf0eb303,0xe6f3823,0xf8eb303,0xe6f3c23,0x120eb303,0x126f3023,0x128eb303,0x126f3423,0xf9dfd06f],[0xeb303,0x6f3023,0x8eb303,0x6f3423,0x70eb303,0x66f3823,0x78eb303,0x66f3c23,0xa0eb303,0xa6f3023,0xa8eb303,0xa6f3423,0xd0eb303,0xc6f3823,0xd8eb303,0xc6f3c23,0x100eb303,0x106f3023,0x108eb303,0x106f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0xf1dfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x40eb303,0x6f3023,0x48eb303,0x6f3423,0xb0eb303,0xa6f3023,0xb8eb303,0xa6f3423,0xe0eb303,0xc6f3823,0xe8eb303,0xc6f3c23,0x110eb303,0x106f3023,0x118eb303,0x106f3423,0x140eb303,0x126f3823,0x148eb303,0x126f3c23,0xe9dfd06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x50eb303,0x6f3023,0x58eb303,0x6f3423,0xc0eb303,0xa6f3023,0xc8eb303,0xa6f3423,0xf0eb303,0xc6f3823,0xf8eb303,0xc6f3c23,0x120eb303,0x106f3023,0x128eb303,0x106f3423,0x150eb303,0x126f3823,0x158eb303,0x126f3c23,0xe1dfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x60eb303,0xa6f3023,0x68eb303,0xa6f3423,0x70eb303,0x6f3023,0x78eb303,0x6f3423,0xe0eb303,0xc6f3823,0xe8eb303,0xc6f3c23,0x110eb303,0x106f3023,0x118eb303,0x106f3423,0x140eb303,0x126f3823,0x148eb303,0x126f3c23,0xd9dfd06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x70eb303,0xa6f3023,0x78eb303,0xa6f3423,0x80eb303,0x6f3023,0x88eb303,0x6f3423,0xf0eb303,0xc6f3823,0xf8eb303,0xc6f3c23,0x120eb303,0x106f3023,0x128eb303,0x106f3423,0x150eb303,0x126f3823,0x158eb303,0x126f3c23,0xd1dfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x40eb303,0x26f3823,0x48eb303,0x26f3c23,0x90eb303,0x6f3023,0x98eb303,0x6f3423,0x100eb303,0xc6f3823,0x108eb303,0xc6f3c23,0x130eb303,0x106f3023,0x138eb303,0x106f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xc9dfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x50eb303,0x26f3823,0x58eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x110eb303,0xc6f3823,0x118eb303,0xc6f3c23,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xc1dfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x60eb303,0xa6f3023,0x68eb303,0xa6f3423,0x90eb303,0xc6f3823,0x98eb303,0xc6f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x110eb303,0x106f3023,0x118eb303,0x106f3423,0x140eb303,0x126f3823,0x148eb303,0x126f3c23,0xb9dfd06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x70eb303,0xa6f3023,0x78eb303,0xa6f3423,0xa0eb303,0xc6f3823,0xa8eb303,0xc6f3c23,0xb0eb303,0x6f3023,0xb8eb303,0x6f3423,0x120eb303,0x106f3023,0x128eb303,0x106f3423,0x150eb303,0x126f3823,0x158eb303,0x126f3c23,0xb1dfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x40eb303,0x26f3823,0x48eb303,0x26f3c23,0xb0eb303,0xc6f3823,0xb8eb303,0xc6f3c23,0xc0eb303,0x6f3023,0xc8eb303,0x6f3423,0x130eb303,0x106f3023,0x138eb303,0x106f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xa9dfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x50eb303,0x26f3823,0x58eb303,0x26f3c23,0xc0eb303,0xc6f3823,0xc8eb303,0xc6f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xa1dfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x70eb303,0x26f3823,0x78eb303,0x26f3c23,0xc0eb303,0x6f3023,0xc8eb303,0x6f3423,0x130eb303,0x106f3023,0x138eb303,0x106f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0x99dfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0x80eb303,0x26f3823,0x88eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0x91dfd06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0x90eb303,0x26f3823,0x98eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x100eb303,0x106f3023,0x108eb303,0x106f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x89dfd06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0x81dfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x60eb303,0xa6f3023,0x68eb303,0xa6f3423,0x90eb303,0xc6f3823,0x98eb303,0xc6f3c23,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x140eb303,0x126f3823,0x148eb303,0x126f3c23,0xf9cfd06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x70eb303,0xa6f3023,0x78eb303,0xa6f3423,0xa0eb303,0xc6f3823,0xa8eb303,0xc6f3c23,0xd0eb303,0x106f3023,0xd8eb303,0x106f3423,0xe0eb303,0x6f3023,0xe8eb303,0x6f3423,0x150eb303,0x126f3823,0x158eb303,0x126f3c23,0xf1cfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x40eb303,0x26f3823,0x48eb303,0x26f3c23,0xb0eb303,0xc6f3823,0xb8eb303,0xc6f3c23,0xe0eb303,0x106f3023,0xe8eb303,0x106f3423,0xf0eb303,0x6f3023,0xf8eb303,0x6f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xe9cfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x50eb303,0x26f3823,0x58eb303,0x26f3c23,0xc0eb303,0xc6f3823,0xc8eb303,0xc6f3c23,0xf0eb303,0x106f3023,0xf8eb303,0x106f3423,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xe1cfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x70eb303,0x26f3823,0x78eb303,0x26f3c23,0xe0eb303,0x106f3023,0xe8eb303,0x106f3423,0xf0eb303,0x6f3023,0xf8eb303,0x6f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xd9cfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0x80eb303,0x26f3823,0x88eb303,0x26f3c23,0xf0eb303,0x106f3023,0xf8eb303,0x106f3423,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xd1cfd06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0x90eb303,0x26f3823,0x98eb303,0x26f3c23,0x100eb303,0x106f3023,0x108eb303,0x106f3423,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0xc9cfd06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xc1cfd06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x90eb303,0x106f3023,0x98eb303,0x106f3423,0xa0eb303,0x26f3823,0xa8eb303,0x26f3c23,0xf0eb303,0x6f3023,0xf8eb303,0x6f3423,0x160eb303,0x126f3823,0x168eb303,0x126f3c23,0xb9cfd06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0xa0eb303,0x106f3023,0xa8eb303,0x106f3423,0xb0eb303,0x26f3823,0xb8eb303,0x26f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xb1cfd06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0xb0eb303,0x106f3023,0xb8eb303,0x106f3423,0xc0eb303,0x26f3823,0xc8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0xa9cfd06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xa1cfd06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x60eb303,0x106f3023,0x68eb303,0x106f3423,0x70eb303,0x66f3023,0x78eb303,0x66f3423,0xc0eb303,0x26f3823,0xc8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x99cfd06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x70eb303,0x106f3023,0x78eb303,0x106f3423,0x80eb303,0x66f3023,0x88eb303,0x66f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0x91cfd06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x40eb303,0x86f3823,0x48eb303,0x86f3c23,0x90eb303,0x66f3023,0x98eb303,0x66f3423,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0x100eb303,0x126f3823,0x108eb303,0x126f3c23,0x89cfd06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x50eb303,0x86f3823,0x58eb303,0x86f3c23,0x100eb303,0x66f3023,0x108eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0x81cfd06f],[0x30eb303,0x66f3823,0x38eb303,0x66f3c23,0x60eb303,0xa6f3023,0x68eb303,0xa6f3423,0x90eb303,0xc6f3823,0x98eb303,0xc6f3c23,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0xf0eb303,0x126f3823,0xf8eb303,0x126f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0xf9dfc06f],[0xeb303,0x26f3823,0x8eb303,0x26f3c23,0x70eb303,0xa6f3023,0x78eb303,0xa6f3423,0xa0eb303,0xc6f3823,0xa8eb303,0xc6f3c23,0xd0eb303,0x106f3023,0xd8eb303,0x106f3423,0x100eb303,0x126f3823,0x108eb303,0x126f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0xf1dfc06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x40eb303,0x26f3823,0x48eb303,0x26f3c23,0xb0eb303,0xc6f3823,0xb8eb303,0xc6f3c23,0xe0eb303,0x106f3023,0xe8eb303,0x106f3423,0x110eb303,0x126f3823,0x118eb303,0x126f3c23,0x120eb303,0x6f3023,0x128eb303,0x6f3423,0xe9dfc06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x50eb303,0x26f3823,0x58eb303,0x26f3c23,0xc0eb303,0xc6f3823,0xc8eb303,0xc6f3c23,0xf0eb303,0x106f3023,0xf8eb303,0x106f3423,0x120eb303,0x126f3823,0x128eb303,0x126f3c23,0x130eb303,0x6f3023,0x138eb303,0x6f3423,0xe1dfc06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x70eb303,0x26f3823,0x78eb303,0x26f3c23,0xe0eb303,0x106f3023,0xe8eb303,0x106f3423,0x110eb303,0x126f3823,0x118eb303,0x126f3c23,0x120eb303,0x6f3023,0x128eb303,0x6f3423,0xd9dfc06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0x80eb303,0x26f3823,0x88eb303,0x26f3c23,0xf0eb303,0x106f3023,0xf8eb303,0x106f3423,0x120eb303,0x126f3823,0x128eb303,0x126f3c23,0x130eb303,0x6f3023,0x138eb303,0x6f3423,0xd1dfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0x90eb303,0x26f3823,0x98eb303,0x26f3c23,0x100eb303,0x106f3023,0x108eb303,0x106f3423,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xc9dfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0x140eb303,0x106f3023,0x148eb303,0x106f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0xc1dfc06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x90eb303,0x106f3023,0x98eb303,0x106f3423,0xa0eb303,0x26f3823,0xa8eb303,0x26f3c23,0x110eb303,0x126f3823,0x118eb303,0x126f3c23,0x120eb303,0x6f3023,0x128eb303,0x6f3423,0xb9dfc06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0xa0eb303,0x106f3023,0xa8eb303,0x106f3423,0xb0eb303,0x26f3823,0xb8eb303,0x26f3c23,0x120eb303,0x126f3823,0x128eb303,0x126f3c23,0x130eb303,0x6f3023,0x138eb303,0x6f3423,0xb1dfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0xb0eb303,0x106f3023,0xb8eb303,0x106f3423,0xc0eb303,0x26f3823,0xc8eb303,0x26f3c23,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xa9dfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0xa1dfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x60eb303,0x106f3023,0x68eb303,0x106f3423,0x70eb303,0x66f3023,0x78eb303,0x66f3423,0xc0eb303,0x26f3823,0xc8eb303,0x26f3c23,0x130eb303,0x126f3823,0x138eb303,0x126f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0x99dfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x70eb303,0x106f3023,0x78eb303,0x106f3423,0x80eb303,0x66f3023,0x88eb303,0x66f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x91dfc06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x40eb303,0x86f3823,0x48eb303,0x86f3c23,0x90eb303,0x66f3023,0x98eb303,0x66f3423,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x100eb303,0x126f3823,0x108eb303,0x126f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0x89dfc06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x50eb303,0x86f3823,0x58eb303,0x86f3c23,0x100eb303,0x66f3023,0x108eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x81dfc06f],[0x30eb303,0xa6f3023,0x38eb303,0xa6f3423,0x60eb303,0xc6f3823,0x68eb303,0xc6f3c23,0x90eb303,0x106f3023,0x98eb303,0x106f3423,0xc0eb303,0x126f3823,0xc8eb303,0x126f3c23,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0x120eb303,0x6f3023,0x128eb303,0x6f3423,0xf9cfc06f],[0xeb303,0x66f3023,0x8eb303,0x66f3423,0x70eb303,0xc6f3823,0x78eb303,0xc6f3c23,0xa0eb303,0x106f3023,0xa8eb303,0x106f3423,0xd0eb303,0x126f3823,0xd8eb303,0x126f3c23,0xe0eb303,0x26f3823,0xe8eb303,0x26f3c23,0x130eb303,0x6f3023,0x138eb303,0x6f3423,0xf1cfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x40eb303,0x66f3023,0x48eb303,0x66f3423,0xb0eb303,0x106f3023,0xb8eb303,0x106f3423,0xe0eb303,0x126f3823,0xe8eb303,0x126f3c23,0xf0eb303,0x26f3823,0xf8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xe9cfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x50eb303,0x66f3023,0x58eb303,0x66f3423,0xc0eb303,0x106f3023,0xc8eb303,0x106f3423,0xf0eb303,0x126f3823,0xf8eb303,0x126f3c23,0x130eb303,0x26f3823,0x138eb303,0x26f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0xe1cfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x60eb303,0x106f3023,0x68eb303,0x106f3423,0x70eb303,0x66f3023,0x78eb303,0x66f3423,0xe0eb303,0x126f3823,0xe8eb303,0x126f3c23,0xf0eb303,0x26f3823,0xf8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xd9cfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x70eb303,0x106f3023,0x78eb303,0x106f3423,0x80eb303,0x66f3023,0x88eb303,0x66f3423,0xf0eb303,0x126f3823,0xf8eb303,0x126f3c23,0x130eb303,0x26f3823,0x138eb303,0x26f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0xd1cfc06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x40eb303,0x86f3823,0x48eb303,0x86f3c23,0x90eb303,0x66f3023,0x98eb303,0x66f3423,0x100eb303,0x126f3823,0x108eb303,0x126f3c23,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0xc9cfc06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x50eb303,0x86f3823,0x58eb303,0x86f3c23,0x100eb303,0x66f3023,0x108eb303,0x66f3423,0x170eb303,0x126f3823,0x178eb303,0x126f3c23,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0xc1cfc06f],[0x30eb303,0xc6f3823,0x38eb303,0xc6f3c23,0x60eb303,0x106f3023,0x68eb303,0x106f3423,0x90eb303,0x126f3823,0x98eb303,0x126f3c23,0xa0eb303,0x66f3023,0xa8eb303,0x66f3423,0xf0eb303,0x26f3823,0xf8eb303,0x26f3c23,0x140eb303,0x6f3023,0x148eb303,0x6f3423,0xb9cfc06f],[0xeb303,0x86f3823,0x8eb303,0x86f3c23,0x70eb303,0x106f3023,0x78eb303,0x106f3423,0xa0eb303,0x126f3823,0xa8eb303,0x126f3c23,0xb0eb303,0x66f3023,0xb8eb303,0x66f3423,0x130eb303,0x26f3823,0x138eb303,0x26f3c23,0x100eb303,0x6f3023,0x108eb303,0x6f3423,0xb1cfc06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x40eb303,0x86f3823,0x48eb303,0x86f3c23,0xb0eb303,0x126f3823,0xb8eb303,0x126f3c23,0xc0eb303,0x66f3023,0xc8eb303,0x66f3423,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0xa9cfc06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x50eb303,0x86f3823,0x58eb303,0x86f3c23,0xc0eb303,0x126f3823,0xc8eb303,0x126f3c23,0x130eb303,0x66f3023,0x138eb303,0x66f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0xa1cfc06f],[0x30eb303,0x106f3023,0x38eb303,0x106f3423,0x60eb303,0x126f3823,0x68eb303,0x126f3c23,0x70eb303,0x86f3823,0x78eb303,0x86f3c23,0xc0eb303,0x66f3023,0xc8eb303,0x66f3423,0x140eb303,0x26f3823,0x148eb303,0x26f3c23,0x110eb303,0x6f3023,0x118eb303,0x6f3423,0x99cfc06f],[0xeb303,0xc6f3023,0x8eb303,0xc6f3423,0x70eb303,0x126f3823,0x78eb303,0x126f3c23,0x80eb303,0x86f3823,0x88eb303,0x86f3c23,0x130eb303,0x66f3023,0x138eb303,0x66f3423,0x100eb303,0x26f3823,0x108eb303,0x26f3c23,0xd0eb303,0x6f3023,0xd8eb303,0x6f3423,0x91cfc06f],[0x30eb303,0x126f3823,0x38eb303,0x126f3c23,0x40eb303,0xc6f3023,0x48eb303,0xc6f3423,0x90eb303,0x86f3823,0x98eb303,0x86f3c23,0x140eb303,0x66f3023,0x148eb303,0x66f3423,0x110eb303,0x26f3823,0x118eb303,0x26f3c23,0xe0eb303,0x6f3023,0xe8eb303,0x6f3423,0x89cfc06f],[0xeb303,0xe6f3823,0x8eb303,0xe6f3c23,0x50eb303,0xc6f3023,0x58eb303,0xc6f3423,0x130eb303,0x86f3823,0x138eb303,0x86f3c23,0x100eb303,0x66f3023,0x108eb303,0x66f3423,0xd0eb303,0x26f3823,0xd8eb303,0x26f3c23,0xa0eb303,0x6f3023,0xa8eb303,0x6f3423,0x81cfc06f]]
sym_block RA0 := symRun cfgP (rowCodeA.getD 0 []) (pcOf 50078) 40
sym_block RA1 := symRun cfgP (rowCodeA.getD 1 []) (pcOf 50110) 40
sym_block RA2 := symRun cfgP (rowCodeA.getD 2 []) (pcOf 50142) 40
sym_block RA3 := symRun cfgP (rowCodeA.getD 3 []) (pcOf 50174) 40
sym_block RA4 := symRun cfgP (rowCodeA.getD 4 []) (pcOf 50206) 40
sym_block RA5 := symRun cfgP (rowCodeA.getD 5 []) (pcOf 50238) 40
sym_block RA6 := symRun cfgP (rowCodeA.getD 6 []) (pcOf 50270) 40
sym_block RA7 := symRun cfgP (rowCodeA.getD 7 []) (pcOf 50302) 40
sym_block RA8 := symRun cfgP (rowCodeA.getD 8 []) (pcOf 50334) 40
sym_block RA9 := symRun cfgP (rowCodeA.getD 9 []) (pcOf 50366) 40
sym_block RA10 := symRun cfgP (rowCodeA.getD 10 []) (pcOf 50398) 40
sym_block RA11 := symRun cfgP (rowCodeA.getD 11 []) (pcOf 50430) 40
sym_block RA12 := symRun cfgP (rowCodeA.getD 12 []) (pcOf 50462) 40
sym_block RA13 := symRun cfgP (rowCodeA.getD 13 []) (pcOf 50494) 40
sym_block RA14 := symRun cfgP (rowCodeA.getD 14 []) (pcOf 50526) 40
sym_block RA15 := symRun cfgP (rowCodeA.getD 15 []) (pcOf 50558) 40
sym_block RA16 := symRun cfgP (rowCodeA.getD 16 []) (pcOf 50590) 40
sym_block RA17 := symRun cfgP (rowCodeA.getD 17 []) (pcOf 50622) 40
sym_block RA18 := symRun cfgP (rowCodeA.getD 18 []) (pcOf 50654) 40
sym_block RA19 := symRun cfgP (rowCodeA.getD 19 []) (pcOf 50686) 40
sym_block RA20 := symRun cfgP (rowCodeA.getD 20 []) (pcOf 50718) 40
sym_block RA21 := symRun cfgP (rowCodeA.getD 21 []) (pcOf 50750) 40
sym_block RA22 := symRun cfgP (rowCodeA.getD 22 []) (pcOf 50782) 40
sym_block RA23 := symRun cfgP (rowCodeA.getD 23 []) (pcOf 50814) 40
sym_block RA24 := symRun cfgP (rowCodeA.getD 24 []) (pcOf 50846) 40
sym_block RA25 := symRun cfgP (rowCodeA.getD 25 []) (pcOf 50878) 40
sym_block RA26 := symRun cfgP (rowCodeA.getD 26 []) (pcOf 50910) 40
sym_block RA27 := symRun cfgP (rowCodeA.getD 27 []) (pcOf 50942) 40
sym_block RA28 := symRun cfgP (rowCodeA.getD 28 []) (pcOf 50974) 40
sym_block RA29 := symRun cfgP (rowCodeA.getD 29 []) (pcOf 51006) 40
sym_block RA30 := symRun cfgP (rowCodeA.getD 30 []) (pcOf 51038) 40
sym_block RA31 := symRun cfgP (rowCodeA.getD 31 []) (pcOf 51070) 40
sym_block RA32 := symRun cfgP (rowCodeA.getD 32 []) (pcOf 51102) 40
sym_block RA33 := symRun cfgP (rowCodeA.getD 33 []) (pcOf 51134) 40
sym_block RA34 := symRun cfgP (rowCodeA.getD 34 []) (pcOf 51166) 40
sym_block RA35 := symRun cfgP (rowCodeA.getD 35 []) (pcOf 51198) 40
sym_block RA36 := symRun cfgP (rowCodeA.getD 36 []) (pcOf 51230) 40
sym_block RA37 := symRun cfgP (rowCodeA.getD 37 []) (pcOf 51262) 40
sym_block RA38 := symRun cfgP (rowCodeA.getD 38 []) (pcOf 51294) 40
sym_block RA39 := symRun cfgP (rowCodeA.getD 39 []) (pcOf 51326) 40
sym_block RA40 := symRun cfgP (rowCodeA.getD 40 []) (pcOf 51358) 40
sym_block RA41 := symRun cfgP (rowCodeA.getD 41 []) (pcOf 51390) 40
sym_block RA42 := symRun cfgP (rowCodeA.getD 42 []) (pcOf 51422) 40
sym_block RA43 := symRun cfgP (rowCodeA.getD 43 []) (pcOf 51454) 40
sym_block RA44 := symRun cfgP (rowCodeA.getD 44 []) (pcOf 51486) 40
sym_block RA45 := symRun cfgP (rowCodeA.getD 45 []) (pcOf 51518) 40
sym_block RA46 := symRun cfgP (rowCodeA.getD 46 []) (pcOf 51550) 40
sym_block RA47 := symRun cfgP (rowCodeA.getD 47 []) (pcOf 51582) 40
sym_block RA48 := symRun cfgP (rowCodeA.getD 48 []) (pcOf 51614) 40
sym_block RA49 := symRun cfgP (rowCodeA.getD 49 []) (pcOf 51646) 40
sym_block RA50 := symRun cfgP (rowCodeA.getD 50 []) (pcOf 51678) 40
sym_block RA51 := symRun cfgP (rowCodeA.getD 51 []) (pcOf 51710) 40
sym_block RA52 := symRun cfgP (rowCodeA.getD 52 []) (pcOf 51742) 40
sym_block RA53 := symRun cfgP (rowCodeA.getD 53 []) (pcOf 51774) 40
sym_block RA54 := symRun cfgP (rowCodeA.getD 54 []) (pcOf 51806) 40
sym_block RA55 := symRun cfgP (rowCodeA.getD 55 []) (pcOf 51838) 40
sym_block RA56 := symRun cfgP (rowCodeA.getD 56 []) (pcOf 51870) 40
sym_block RA57 := symRun cfgP (rowCodeA.getD 57 []) (pcOf 51902) 40
sym_block RA58 := symRun cfgP (rowCodeA.getD 58 []) (pcOf 51934) 40
sym_block RA59 := symRun cfgP (rowCodeA.getD 59 []) (pcOf 51966) 40
sym_block RA60 := symRun cfgP (rowCodeA.getD 60 []) (pcOf 51998) 40
sym_block RA61 := symRun cfgP (rowCodeA.getD 61 []) (pcOf 52030) 40
sym_block RA62 := symRun cfgP (rowCodeA.getD 62 []) (pcOf 52062) 40
sym_block RA63 := symRun cfgP (rowCodeA.getD 63 []) (pcOf 52094) 40
sym_block RB0 := symRun cfgP (rowCodeB.getD 0 []) (pcOf 52126) 40
sym_block RB1 := symRun cfgP (rowCodeB.getD 1 []) (pcOf 52158) 40
sym_block RB2 := symRun cfgP (rowCodeB.getD 2 []) (pcOf 52190) 40
sym_block RB3 := symRun cfgP (rowCodeB.getD 3 []) (pcOf 52222) 40
sym_block RB4 := symRun cfgP (rowCodeB.getD 4 []) (pcOf 52254) 40
sym_block RB5 := symRun cfgP (rowCodeB.getD 5 []) (pcOf 52286) 40
sym_block RB6 := symRun cfgP (rowCodeB.getD 6 []) (pcOf 52318) 40
sym_block RB7 := symRun cfgP (rowCodeB.getD 7 []) (pcOf 52350) 40
sym_block RB8 := symRun cfgP (rowCodeB.getD 8 []) (pcOf 52382) 40
sym_block RB9 := symRun cfgP (rowCodeB.getD 9 []) (pcOf 52414) 40
sym_block RB10 := symRun cfgP (rowCodeB.getD 10 []) (pcOf 52446) 40
sym_block RB11 := symRun cfgP (rowCodeB.getD 11 []) (pcOf 52478) 40
sym_block RB12 := symRun cfgP (rowCodeB.getD 12 []) (pcOf 52510) 40
sym_block RB13 := symRun cfgP (rowCodeB.getD 13 []) (pcOf 52542) 40
sym_block RB14 := symRun cfgP (rowCodeB.getD 14 []) (pcOf 52574) 40
sym_block RB15 := symRun cfgP (rowCodeB.getD 15 []) (pcOf 52606) 40
sym_block RB16 := symRun cfgP (rowCodeB.getD 16 []) (pcOf 52638) 40
sym_block RB17 := symRun cfgP (rowCodeB.getD 17 []) (pcOf 52670) 40
sym_block RB18 := symRun cfgP (rowCodeB.getD 18 []) (pcOf 52702) 40
sym_block RB19 := symRun cfgP (rowCodeB.getD 19 []) (pcOf 52734) 40
sym_block RB20 := symRun cfgP (rowCodeB.getD 20 []) (pcOf 52766) 40
sym_block RB21 := symRun cfgP (rowCodeB.getD 21 []) (pcOf 52798) 40
sym_block RB22 := symRun cfgP (rowCodeB.getD 22 []) (pcOf 52830) 40
sym_block RB23 := symRun cfgP (rowCodeB.getD 23 []) (pcOf 52862) 40
sym_block RB24 := symRun cfgP (rowCodeB.getD 24 []) (pcOf 52894) 40
sym_block RB25 := symRun cfgP (rowCodeB.getD 25 []) (pcOf 52926) 40
sym_block RB26 := symRun cfgP (rowCodeB.getD 26 []) (pcOf 52958) 40
sym_block RB27 := symRun cfgP (rowCodeB.getD 27 []) (pcOf 52990) 40
sym_block RB28 := symRun cfgP (rowCodeB.getD 28 []) (pcOf 53022) 40
sym_block RB29 := symRun cfgP (rowCodeB.getD 29 []) (pcOf 53054) 40
sym_block RB30 := symRun cfgP (rowCodeB.getD 30 []) (pcOf 53086) 40
sym_block RB31 := symRun cfgP (rowCodeB.getD 31 []) (pcOf 53118) 40
sym_block RB32 := symRun cfgP (rowCodeB.getD 32 []) (pcOf 53150) 40
sym_block RB33 := symRun cfgP (rowCodeB.getD 33 []) (pcOf 53182) 40
sym_block RB34 := symRun cfgP (rowCodeB.getD 34 []) (pcOf 53214) 40
sym_block RB35 := symRun cfgP (rowCodeB.getD 35 []) (pcOf 53246) 40
sym_block RB36 := symRun cfgP (rowCodeB.getD 36 []) (pcOf 53278) 40
sym_block RB37 := symRun cfgP (rowCodeB.getD 37 []) (pcOf 53310) 40
sym_block RB38 := symRun cfgP (rowCodeB.getD 38 []) (pcOf 53342) 40
sym_block RB39 := symRun cfgP (rowCodeB.getD 39 []) (pcOf 53374) 40
sym_block RB40 := symRun cfgP (rowCodeB.getD 40 []) (pcOf 53406) 40
sym_block RB41 := symRun cfgP (rowCodeB.getD 41 []) (pcOf 53438) 40
sym_block RB42 := symRun cfgP (rowCodeB.getD 42 []) (pcOf 53470) 40
sym_block RB43 := symRun cfgP (rowCodeB.getD 43 []) (pcOf 53502) 40
sym_block RB44 := symRun cfgP (rowCodeB.getD 44 []) (pcOf 53534) 40
sym_block RB45 := symRun cfgP (rowCodeB.getD 45 []) (pcOf 53566) 40
sym_block RB46 := symRun cfgP (rowCodeB.getD 46 []) (pcOf 53598) 40
sym_block RB47 := symRun cfgP (rowCodeB.getD 47 []) (pcOf 53630) 40
sym_block RB48 := symRun cfgP (rowCodeB.getD 48 []) (pcOf 53662) 40
sym_block RB49 := symRun cfgP (rowCodeB.getD 49 []) (pcOf 53694) 40
sym_block RB50 := symRun cfgP (rowCodeB.getD 50 []) (pcOf 53726) 40
sym_block RB51 := symRun cfgP (rowCodeB.getD 51 []) (pcOf 53758) 40
sym_block RB52 := symRun cfgP (rowCodeB.getD 52 []) (pcOf 53790) 40
sym_block RB53 := symRun cfgP (rowCodeB.getD 53 []) (pcOf 53822) 40
sym_block RB54 := symRun cfgP (rowCodeB.getD 54 []) (pcOf 53854) 40
sym_block RB55 := symRun cfgP (rowCodeB.getD 55 []) (pcOf 53886) 40
sym_block RB56 := symRun cfgP (rowCodeB.getD 56 []) (pcOf 53918) 40
sym_block RB57 := symRun cfgP (rowCodeB.getD 57 []) (pcOf 53950) 40
sym_block RB58 := symRun cfgP (rowCodeB.getD 58 []) (pcOf 53982) 40
sym_block RB59 := symRun cfgP (rowCodeB.getD 59 []) (pcOf 54014) 40
sym_block RB60 := symRun cfgP (rowCodeB.getD 60 []) (pcOf 54046) 40
sym_block RB61 := symRun cfgP (rowCodeB.getD 61 []) (pcOf 54078) 40
sym_block RB62 := symRun cfgP (rowCodeB.getD 62 []) (pcOf 54110) 40
sym_block RB63 := symRun cfgP (rowCodeB.getD 63 []) (pcOf 54142) 40

/-! ### Generic memory lemmas -/
def vFun (M : Nat → Word) (A : Nat) : Word :=
  match vTable.reverse.find? (fun e => decide (e.1 = A)) with
  | some e => M (0x300000 + e.2)
  | none => M A

theorem memEval_vmap (s : MachineState) (L : List (Nat × Nat)) (hL : ∀ e ∈ L, e.1 < 2 ^ 64 ∧ 0x300000 + e.2 < 2 ^ 64)
    (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (L.map vWrite) (BitVec.ofNat 64 A) =
      match L.find? (fun e => decide (e.1 = A)) with
      | some e => s.getMem (BitVec.ofNat 64 (0x300000 + e.2))
      | none => s.getMem (BitVec.ofNat 64 A) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have he := hL e (List.mem_cons_self ..)
    rw [List.map_cons, memEval_cons, List.find?_cons]
    simp only [vWrite, Addr.eval, E.eval]
    by_cases h : e.1 = A
    · subst h; simp
    · rw [if_neg (fun h' => h ((ofNat_inj hA he.1).mp h').symm), ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))]
      simp [h]

theorem vTable_bounds : ∀ e ∈ vTable.reverse, e.1 < 2 ^ 64 ∧ 0x300000 + e.2 < 2 ^ 64 := by decide +kernel

theorem vals_spec {im : Image} (hc : CodeAt im (pcOf 49469) cVals) (s : MachineState) (hpc : s.pc = pcOf 49469) :
    ∃ t, Steps im s 586 586 t ∧ t.pc = pcOf 50055 ∧ RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      t.getReg .x29 = BitVec.ofNat 64 0x300000 ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = vFun (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  refine ⟨_, symRun_sound run_vals hc s hpc (by simp [vRes, Result.obligs, Oblig.all]), ?_, ?_, ?_, ?_⟩
  · simp [vRes, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [Result.toState_getReg, vRes, vRegs]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · simp [vRes, vRegs, RegFile.get, RegFile.set, E.eval]
  · intro A hA
    simp only [Result.toState_getMem, vRes, vWrites]
    rw [memEval_vmap s _ vTable_bounds A hA]
    rfl

/-- The row obligations: valid stores into the new path area, valid loads from the saved area, and the
load/store separation. -/
def oblOK : Oblig → Bool
  | .valid ⟨some (.reg .x30), off⟩ 8 => decide (off.toNat + 8 ≤ 672) && decide (off.toNat % 8 = 0)
  | .valid ⟨some (.reg .x29), off⟩ 8 => decide (off.toNat + 8 ≤ 768) && decide (off.toNat % 8 = 0)
  | .ne ⟨some (.reg .x29), a⟩ ⟨some (.reg .x30), b⟩ => decide (a.toNat < 4096) && decide (b.toNat < 4096)
  | _ => false

theorem ofNat_add_word (c : Nat) (w : Word) : BitVec.ofNat 64 c + w = BitVec.ofNat 64 (c + w.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem oblOK_holds (s : MachineState) (h29 : s.getReg .x29 = BitVec.ofNat 64 0x301000)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 11792) (o : Oblig) (h : oblOK o = true) : o.holds s := by
  unfold oblOK at h
  split at h
  · rename_i off
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Oblig.holds, Addr.eval, E.eval, h30, ofNat_add_word]
    exact valid8P _ (by omega) (by omega)
  · rename_i off
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Oblig.holds, Addr.eval, E.eval, h29, ofNat_add_word]
    exact valid8P _ (by omega) (by omega)
  · rename_i a b
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Oblig.holds, Addr.eval, E.eval, h29, h30, ofNat_add_word]
    intro he
    have := (ofNat_inj (by omega) (by omega)).mp he
    omega
  · exact absurd h (by simp)

def rowWrite (e : Nat × Nat) : Addr × E :=
  (⟨some (.reg .x30), BitVec.ofNat 64 e.2⟩, .ld (addC (.reg .x29) (BitVec.ofNat 64 e.1)))
def rowLast (pairs : List (Nat × Nat)) : Nat := (pairs.getLast?.map Prod.fst).getD 0
structure RowOK (R : Result) (pairs : List (Nat × Nat)) (ret : Nat) : Prop where
  mem : R.st.mem = pairs.reverse.map rowWrite
  obl : R.st.obl.all oblOK = true
  pc : R.pc = .c (pcOf ret)
  steps : R.steps = 25
  cycles : R.cycles = 25
  regs : R.st.regs = RegFile.init.set .x6 (.ld (addC (.reg .x29) (BitVec.ofNat 64 (rowLast pairs))))

def rowFun (pairs : List (Nat × Nat)) (M : Nat → Word) (A : Nat) : Word :=
  match pairs.reverse.find? (fun e => decide (11792 + e.2 = A)) with
  | some e => M (0x301000 + e.1)
  | none => M A

theorem memEval_rmap (s : MachineState) (h29 : s.getReg .x29 = BitVec.ofNat 64 0x301000)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 11792) (L : List (Nat × Nat)) (hL : ∀ e ∈ L, e.1 < 4096 ∧ e.2 < 4096)
    (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (L.map rowWrite) (BitVec.ofNat 64 A) =
      match L.find? (fun e => decide (11792 + e.2 = A)) with
      | some e => s.getMem (BitVec.ofNat 64 (0x301000 + e.1))
      | none => s.getMem (BitVec.ofNat 64 A) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have he := hL e (List.mem_cons_self ..)
    rw [List.map_cons, memEval_cons, List.find?_cons]
    simp only [rowWrite, Addr.eval, E.eval, addC_eval, h29, h30, ofNat_add_ofNat]
    by_cases h : 11792 + e.2 = A
    · subst h; simp
    · rw [if_neg (fun h' => h ((ofNat_inj hA (by omega)).mp h').symm), ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))]
      simp [h]

theorem row_spec {im : Image} {code : List (BitVec 32)} {p ret : Nat} {pairs : List (Nat × Nat)} {R : Result}
    (hrun : symRun cfgP code (pcOf p) 40 = some R) (hc : CodeAt im (pcOf p) code) (hok : RowOK R pairs ret)
    (hpairs : ∀ e ∈ pairs, e.1 < 4096 ∧ e.2 < 4096)
    (s : MachineState) (hpc : s.pc = pcOf p) (h29 : s.getReg .x29 = BitVec.ofNat 64 0x301000)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 11792) :
    ∃ t, Steps im s 25 25 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [.x6] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) = rowFun pairs (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  have hobl : R.obligs s := by
    show Oblig.all s _
    rw [Oblig.all_iff]
    intro o ho
    exact oblOK_holds s h29 h30 o (List.all_eq_true.mp hok.obl o ho)
  have st := symRun_sound hrun hc s hpc hobl
  rw [hok.steps, hok.cycles] at st
  refine ⟨_, st, ?_, ?_, ?_⟩
  · simp [hok.pc, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Result.toState_getReg, hok.regs]
    cases x <;> simp_all [RegFile.get, RegFile.set, RegFile.init, E.eval] <;> rfl
  · intro A hA
    simp only [Result.toState_getMem, hok.mem]
    rw [memEval_rmap s h29 h30 _ (fun e he => hpairs e (List.mem_reverse.mp he)) A hA]
    rfl

theorem rowA_ok (r : Nat) (hr : r < 64) : ∃ R, symRun cfgP (rowCodeA.getD r []) (pcOf (50078 + 32 * r)) 40 = some R ∧
    RowOK R (rowsA.getD r []) 50070 := by
  interval_cases r
  · exact ⟨_, RA0, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA1, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA2, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA3, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA4, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA5, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA6, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA7, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA8, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA9, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA10, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA11, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA12, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA13, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA14, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA15, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA16, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA17, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA18, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA19, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA20, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA21, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA22, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA23, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA24, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA25, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA26, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA27, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA28, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA29, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA30, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA31, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA32, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA33, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA34, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA35, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA36, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA37, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA38, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA39, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA40, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA41, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA42, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA43, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA44, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA45, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA46, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA47, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA48, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA49, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA50, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA51, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA52, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA53, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA54, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA55, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA56, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA57, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA58, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA59, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA60, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA61, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA62, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RA63, by constructor <;> kernel_rfl⟩

theorem rowB_ok (r : Nat) (hr : r < 64) : ∃ R, symRun cfgP (rowCodeB.getD r []) (pcOf (52126 + 32 * r)) 40 = some R ∧
    RowOK R (rowsB.getD r []) 50077 := by
  interval_cases r
  · exact ⟨_, RB0, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB1, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB2, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB3, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB4, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB5, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB6, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB7, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB8, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB9, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB10, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB11, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB12, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB13, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB14, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB15, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB16, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB17, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB18, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB19, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB20, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB21, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB22, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB23, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB24, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB25, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB26, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB27, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB28, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB29, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB30, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB31, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB32, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB33, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB34, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB35, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB36, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB37, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB38, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB39, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB40, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB41, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB42, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB43, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB44, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB45, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB46, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB47, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB48, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB49, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB50, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB51, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB52, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB53, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB54, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB55, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB56, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB57, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB58, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB59, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB60, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB61, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB62, by constructor <;> kernel_rfl⟩
  · exact ⟨_, RB63, by constructor <;> kernel_rfl⟩
theorem rowsA_bounds : ∀ r < 64, ∀ e ∈ rowsA.getD r [], e.1 < 4096 ∧ e.2 < 4096 := by decide +kernel
theorem rowsB_bounds : ∀ r < 64, ∀ e ∈ rowsB.getD r [], e.1 < 4096 ∧ e.2 < 4096 := by decide +kernel

end ClaudeWCT.W9.Machine.Expand.PostPass
end
-- ==== merged from T3M_Verify_ChainCheckParts ====
section

namespace SigGolfCandidate.T3M
/-- Join bounded checks while keeping the closed code predicates opaque to unification. -/
theorem chain_all_range'_add {p : Nat → Bool} {lo left right : Nat}
    (hleft : (List.range' lo left).all p = true)
    (hright : (List.range' (lo + left) right).all p = true) :
    (List.range' lo (left + right)).all p = true := by
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl

theorem triCheck_add {t lo left right : Nat} (hdiv : left % 8 = 0)
    (hleft : triCheck t lo left = true)
    (hright : triCheck t (lo + left) right = true) :
    triCheck t lo (left + right) = true := by
  simp only [triCheck, Bool.and_eq_true] at hleft hright ⊢
  refine ⟨@chain_all_range'_add (entCheck t) lo left right hleft.1 hright.1, ?_⟩
  have hstart : (lo + left) / 8 = lo / 8 + left / 8 := by omega
  have hcount : (left + right) / 8 = left / 8 + right / 8 := by omega
  rw [hstart] at hright
  rw [hcount]
  exact @chain_all_range'_add (fun q => blkCheck t (q / 8) (q % 8))
    (lo / 8) (left / 8) (right / 8) hleft.2 hright.2
end SigGolfCandidate.T3M
end
