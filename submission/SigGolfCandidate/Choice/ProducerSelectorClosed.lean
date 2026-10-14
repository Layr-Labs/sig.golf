import SigGolfCandidate.Choice.ProducerSelectorFull

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

def clobbers : List Reg := [.x6,.x7,.x10,.x11,.x20,.x25,.x28,.x29]

theorem producer_valid_iff (v : Digest) :
    (producerDecode 0 v).isSome=true ↔
      topLookupSum (T3.topFlip v)=146 ∧ 34 ≤ packedTopScore (T3.topFlip v) := by
  have he := producerDecode_top_lookup (T3.topFlip v)
  rw [T3.topFlip_topFlip] at he
  rw [he]
  split_ifs <;> simp_all

theorem canonical_open (a : BitVec 256) (hg : Selector.group (a.extractLsb' 0 128)≠(0#64)) :
    topChooseLow a = decide (topLookupSum (T3.topFlip (a.extractLsb' 0 128))=146 ∧
      34 ≤ packedTopScore (T3.topFlip (a.extractLsb' 0 128))) := by
  apply Bool.eq_iff_iff.mpr
  simp [topChooseLow,hg,producer_valid_iff]

theorem canonical_hint (a : BitVec 256) :
    encodingHint 0 a = if topChooseLow a then 0 else 16 := by
  cases h : topChooseLow a <;> simp [encodingHint,h]

theorem ready_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (a : BitVec 256) (hsum : SumTableOK s) (hrew : RewardTablesOK s)
    (hpc : s.pc=pcOf b)
    (h6 : s.getReg .x6=(a.extractLsb' 0 128).extractLsb' 0 64)
    (h7 : s.getReg .x7=(a.extractLsb' 0 128).extractLsb' 64 64) :
    ∃ k t, Steps image s k k t ∧ k≤147 ∧
      t.pc=pcOf (b+if topChooseLow a then 147 else 151) ∧
      RegsExcept s t clobbers ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,ru,fu⟩ := head_spec hb hc s (a.extractLsb' 0 128) hpc h7
  by_cases hg : Selector.group (a.extractLsb' 0 128)=(0#64)
  · have hl : topChooseLow a=true := by simp [topChooseLow,hg]
    exact ⟨2,u,su,by decide,by simpa [hg,hl] using pu,ru.mono (by decide),fu⟩
  · obtain ⟨v,sv,pv,g25,g20,rv,fv⟩ := body_spec hb hc u (a.extractLsb' 0 128)
      (hsum.frame fu (by simp)) (hrew.frame fu (by simp)) (by simpa [hg] using pu)
      (by rw [ru.get (by decide),h6]) (by rw [ru.get (by decide),h7])
    have hbound := accumulator_bounds (T3.topFlip (a.extractLsb' 0 128))
    obtain ⟨k,t,st,hk,pt,rt,ft⟩ := decision_spec hb hc v
      (topLookupSum (T3.topFlip (a.extractLsb' 0 128)))
      (packedTopScore (T3.topFlip (a.extractLsb' 0 128))) (by omega) (by omega) pv g25 g20
    refine ⟨2+141+k,t,(su.trans sv).trans st,by omega,?_,
      ((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
    have hl := canonical_open a hg
    by_cases hgood : topLookupSum (T3.topFlip (a.extractLsb' 0 128))=146 ∧
        34 ≤ packedTopScore (T3.topFlip (a.extractLsb' 0 128))
    all_goals simpa [hl,hgood] using pt

/-- All common selector instructions, including the hint store, for every hash answer. -/
theorem select_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : At image b)
    (s : MachineState) (a : BitVec 256) (hsum : SumTableOK s) (hrew : RewardTablesOK s)
    (hpc : s.pc=pcOf b)
    (h6 : s.getReg .x6=(a.extractLsb' 0 128).extractLsb' 0 64)
    (h7 : s.getReg .x7=(a.extractLsb' 0 128).extractLsb' 64 64)
    (h12 : s.getReg .x12=BitVec.ofNat 64 EOUT)
    (hlo : DigAt s EOUT (a.extractLsb' 0 128))
    (hhi : DigAt s (EOUT+16) (a.extractLsb' 128 128)) :
    ∃ k t, Steps image s k k t ∧ k≤153 ∧ t.pc=pcOf (b+156) ∧
      t.getReg .x6=(encodingAnswer 0 a).extractLsb' 0 64 ∧
      t.getReg .x7=(encodingAnswer 0 a).extractLsb' 64 64 ∧
      t.getMem (BitVec.ofNat 64 HINT)=encodingHint 0 a ∧
      RegsExcept s t clobbers ∧ Frame s t (fun A=>A=HINT) := by
  obtain ⟨k,u,su,hk,pu,ru,fu⟩ := ready_spec hb hc s a hsum hrew hpc h6 h7
  obtain ⟨v,sv,pv,g6,g7,g29,rv,fv⟩ := choose_spec hb hc u a (topChooseLow a) pu
    (by rw [ru.get (by decide),h12])
    (hlo.frame fu (by decide) (by simp) (by simp))
    (hhi.frame fu (by decide) (by simp) (by simp))
  obtain ⟨t,st,pt,ht,rt,ft⟩ := store_spec hb hc v (if topChooseLow a then 0 else 16) pv g29
  refine ⟨k+(if topChooseLow a then 4 else 3)+2,t,(su.trans sv).trans st,?_,pt,?_,?_,?_,
    ((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
  · split_ifs <;> omega
  · rw [rt.get (by decide)]
    simpa [encodingAnswer] using g6
  · rw [rt.get (by decide)]
    simpa [encodingAnswer] using g7
  · simpa only [canonical_hint] using ht

def returnPC (b : Nat) : Nat := if b=21942 then 21027 else 43035
def returnWord (b : Nat) : BitVec 32 := if b=21942 then 0xf45fe06f else 0xdc5fe06f
def code (b : Nat) : List (BitVec 32) := words++[returnWord b]
def FullAt (image : Image) (b : Nat) : Prop := CodeAt image (pcOf b) (code b)

theorem fullAt_prefix {image : Image} {b : Nat} (h : FullAt image b) : At image b := by
  change CodeAt image (pcOf b) (words++[returnWord b]) at h
  have hp : words++[returnWord b]=[]++words++[returnWord b] := rfl
  rw [hp] at h
  simpa [At] using CodeAt.drop_prefix h

theorem fullAt_return {image : Image} {b : Nat} (h : FullAt image b) :
    CodeAt image (pcOf (b+156)) [returnWord b] := by
  change CodeAt image (pcOf b) (words++[returnWord b]) at h
  rw [show words++[returnWord b]=words++[returnWord b]++[] by simp] at h
  have hc := CodeAt.drop_prefix h
  rw [words_length] at hc
  simpa only [pcOf,ofNat_add_ofNat,Nat.mul_add,Nat.add_assoc] using hc

def returnResult (b : Nat) : Result := ⟨SymState.init,.c (pcOf (returnPC b)),.jump,1,1⟩
theorem return_run (b : Nat) (hb : Allowed b) :
    symRun {noAlias:=true} [returnWord b] (pcOf (b+156)) 2=some (returnResult b) := by
  rcases hb with rfl|rfl <;> kernel_rfl

theorem return_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : FullAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+156)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (returnPC b) ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (return_run b hb) (fullAt_return hc) s hpc
    (by simp [returnResult,SymState.init,rv_simp]),rfl,?_,?_⟩
  · intro r _; cases r <;> rfl
  · intro A _ _; rfl

/-- Exact 157-word selector with the image-specific return jump.
The only writable word is the hint slot, and the routine performs no oracle calls. -/
theorem selector_spec {image : Image} {b : Nat} (hb : Allowed b) (hc : FullAt image b)
    (s : MachineState) (a : BitVec 256) (hsum : SumTableOK s) (hrew : RewardTablesOK s)
    (hpc : s.pc=pcOf b)
    (h6 : s.getReg .x6=(a.extractLsb' 0 128).extractLsb' 0 64)
    (h7 : s.getReg .x7=(a.extractLsb' 0 128).extractLsb' 64 64)
    (h12 : s.getReg .x12=BitVec.ofNat 64 EOUT)
    (hlo : DigAt s EOUT (a.extractLsb' 0 128))
    (hhi : DigAt s (EOUT+16) (a.extractLsb' 128 128)) :
    ∃ k t, Steps image s k k t ∧ k≤154 ∧ t.pc=pcOf (returnPC b) ∧
      t.getReg .x6=(encodingAnswer 0 a).extractLsb' 0 64 ∧
      t.getReg .x7=(encodingAnswer 0 a).extractLsb' 64 64 ∧
      t.getMem (BitVec.ofNat 64 HINT)=encodingHint 0 a ∧
      RegsExcept s t clobbers ∧ Frame s t (fun A=>A=HINT) := by
  obtain ⟨k,u,su,hk,pu,g6,g7,gu,ru,fu⟩ := select_spec hb (fullAt_prefix hc) s a hsum hrew hpc h6 h7 h12 hlo hhi
  obtain ⟨t,st,pt,rt,ft⟩ := return_spec hb hc u pu
  refine ⟨k+1,t,su.trans st,by omega,pt,?_,?_,?_,(ru.trans rt).mono (by decide),
    (fu.trans ft).mono (by simp)⟩
  · rw [rt.get (by decide)]; exact g6
  · rw [rt.get (by decide)]; exact g7
  · rw [ft.get (by decide) (by simp)]; exact gu

end SigGolfCandidate.Choice.ProducerSelector
#print axioms SigGolfCandidate.Choice.ProducerSelector.producer_valid_iff
#print axioms SigGolfCandidate.Choice.ProducerSelector.select_spec
#print axioms SigGolfCandidate.Choice.ProducerSelector.selector_spec
