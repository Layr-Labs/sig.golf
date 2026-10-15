import SigGolfCandidate.Choice.ProducerSelectorAcc

namespace SigGolfCandidate.Choice.ProducerSelector
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Search.Reward
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.WCT9
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] words

def tailIndex (v : Digest) : Nat := v.toNat/2^119

theorem tailIndex_lt (v : Digest) : tailIndex v<512 := by
  have := v.isLt
  unfold tailIndex
  omega

theorem tailShift (v : Digest) : v.extractLsb' 64 64 >>> 55 = BitVec.ofNat 64 (tailIndex v) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,tailIndex]
  have := v.isLt
  omega

def tailPrefix : List (BitVec 32) := (words.drop 131).take 3
sym_block tailPrefixBase := symRun {noAlias:=true} tailPrefix 0#64 4
def tailPrefixResult (b : Nat) : Result := {tailPrefixBase.res with pc:=.c (pcOf (b+134))}
theorem tailPrefix_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} tailPrefix (pcOf (b+131)) 4 = some (tailPrefixResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem tailPrefix_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (hpc : s.pc=pcOf (b+131))
    (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=BitVec.ofNat 64 (TOP_DATA+2048)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc=pcOf (b+134) ∧
      t.getReg .x10=BitVec.ofNat 64 (tailIndex v) ∧
      t.getReg .x28=BitVec.ofNat 64 (TOP_DATA+2048+tailIndex v) ∧
      RegsExcept s t [.x10,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (tailPrefix_run b hb) (slice hc 131 3 (by decide)) s hpc
    (by simp [tailPrefixResult,tailPrefixBase.res,rv_simp]),rfl,?_,?_,?_,?_⟩
  · simp [tailPrefixResult,tailPrefixBase.res,rv_simp,h7,tailShift]
  · simp [tailPrefixResult,tailPrefixBase.res,rv_simp,h7,h11]
    have h := ext_shr_mask v 64 55 9 (by decide)
    change (v.extractLsb' 64 64 >>> 55) &&& 511#64 = BitVec.ofNat 64 (v.toNat/2^119%512) at h
    rw [h]
    change BitVec.ofNat 64 (TOP_DATA+2048)+BitVec.ofNat 64 (tailIndex v%512)=_
    rw [Nat.mod_eq_of_lt (tailIndex_lt v),ofNat_add_ofNat]
  · intro r hr; cases r <;> simp_all [tailPrefixResult,tailPrefixBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl

theorem tailLoad_spec {image : Image} {b : Nat} (hc : At image b)
    (s : MachineState) (v : Digest) (ht : RewardTablesOK s)
    (hpc : s.pc=pcOf (b+134))
    (h28 : s.getReg .x28=BitVec.ofNat 64 (TOP_DATA+2048+tailIndex v)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+135) ∧
      t.getReg .x29=BitVec.ofNat 64 (tailLookup (tailIndex v)) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _=>False) := by
  have hc' : CodeAt image (pcOf (b+134)) [0x180e4e83#32] := by
    have he : (words.drop 134).take 1=[0x180e4e83#32] := by kernel_rfl
    have hh := slice hc 134 1 (by decide)
    rwa [he] at hh
  have hd : decodeInstruction 0x180e4e83#32 = some (.base (.LBU .x29 .x28 384#12)) := by kernel_rfl
  have ha : s.getReg .x28+signExtend12 384#12=BitVec.ofNat 64 (TOP_DATA+(2432+tailIndex v)) := by
    rw [h28,show signExtend12 384#12=BitVec.ofNat 64 384 from rfl,ofNat_add_ofNat]
    congr 1
    omega
  have hv : accessValid (s.getReg .x28+signExtend12 384#12) 1=true := by
    rw [ha,accessValid_iff]
    have := tailIndex_lt v
    norm_num [TOP_DATA,MEMORY_BYTES]
    omega
  have hs := steps_lbu hc' hpc hd hv
  have hw : (s.getByte (BitVec.ofNat 64 (TOP_DATA+(2432+tailIndex v)))).zeroExtend 64=
      BitVec.ofNat 64 (tailLookup (tailIndex v)) := by
    rw [table_tail s ht _ (tailIndex_lt v)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    have := tailLookup_le (tailIndex v)
    omega
  rw [ha,hw] at hs
  refine ⟨_,hs,?_,?_,?_,?_⟩
  · change s.pc+4 = _
    rw [hpc,pcOf_add4]
  · change (s.setReg .x29 (BitVec.ofNat 64 (tailLookup (tailIndex v)))).getReg .x29 = _
    exact MachineState.getReg_setReg_eq (by decide)
  · intro r hr
    cases r <;> first | exact False.elim (hr (by decide)) | rfl
  · intro A _ _; rfl

def tailEnd : List (BitVec 32) := (words.drop 135).take 8
sym_block tailEndBase := symRun {noAlias:=true} tailEnd 0#64 10
def tailEndResult (b : Nat) : Result := {tailEndBase.res with pc:=.c (pcOf (b+143))}
theorem tailEnd_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} tailEnd (pcOf (b+135)) 10 = some (tailEndResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem tailEnd_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (v : Digest) (sum score : Word) (hpc : s.pc=pcOf (b+135))
    (h10 : s.getReg .x10=BitVec.ofNat 64 (tailIndex v))
    (h29 : s.getReg .x29=BitVec.ofNat 64 (tailLookup (tailIndex v)))
    (h25 : s.getReg .x25=sum) (h20 : s.getReg .x20=score) :
    ∃ t, Steps image s 8 8 t ∧ t.pc=pcOf (b+143) ∧
      t.getReg .x25=sum+BitVec.ofNat 64 (tailWeight v) ∧
      t.getReg .x20=score+BitVec.ofNat 64 (tailLookup (tailIndex v)) ∧
      RegsExcept s t [.x10,.x20,.x25,.x28] ∧ Frame s t (fun _=>False) := by
  have hn := tailIndex_lt v
  have hm (n : Nat) : BitVec.ofNat 64 n &&& 7#64=BitVec.ofNat 64 (n%8) := by
    simpa using ofNat_and_mask n 3
  have hsh (n : Nat) (hn : n<512) : BitVec.ofNat 64 n >>> 3=BitVec.ofNat 64 (n/8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat]
    omega
  have ht : tailWeight v=tailIndex v%8+(tailIndex v/8)%8+tailIndex v/64 := by
    have := v.isLt
    unfold tailWeight tailIndex
    omega
  refine ⟨_,symRun_sound (tailEnd_run b hb) (slice hc 135 8 (by decide)) s hpc
    (by simp [tailEndResult,tailEndBase.res,rv_simp]),rfl,?_,?_,?_,?_⟩
  · simp only [tailEndResult,tailEndBase.res,rv_simp,h10,h25,hsh _ hn,hm,
      hsh _ (by omega : tailIndex v/8<512),Nat.div_div_eq_div_mul]
    rw [ht]
    simp [ofNat_shr _ 3 (by omega : tailIndex v<2^64),
      ofNat_shr _ 6 (by omega : tailIndex v<2^64),
      ofNat_shr (tailIndex v/8) 3 (by omega),hm,Nat.div_div_eq_div_mul,ofNat_add_ofNat,BitVec.add_assoc]
  · simp [tailEndResult,tailEndBase.res,rv_simp,h20,h29]
  · intro r hr; cases r <;> simp_all [tailEndResult,tailEndBase.res,rv_simp] <;> rfl
  · intro A _ _; rfl

end SigGolfCandidate.Choice.ProducerSelector
#print axioms SigGolfCandidate.Choice.ProducerSelector.tailEnd_spec
