import SigGolfCandidate.T3M.Search.CsBlocks
import SigGolfCandidate.ClaudeWCT.WCT9.Core
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option Elab.async false
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem selector_code0 {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) :
    CodeAt image (pcOf (selectorBase b+0)) (selector0) :=
  codeAt_selector hK 0 0 (selector0) (by rfl)
sym_block sel354_0 := symRun {noAlias:=true} (selector0) (pcOf (selectorBase 354+0)) 200
sym_block sel543_0 := symRun {noAlias:=true} (selector0) (pcOf (selectorBase 543+0)) 200
def selState0 : SymState := sel354_0.res.st
def selPc0 (b : Nat) : E := rebase sel354_0.res.pc (pcOf (selectorBase b+7)) (pcOf (selectorBase b+2))
theorem selRun0 {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} (selector0) (pcOf (selectorBase b+0)) 200 =
    some ⟨selState0,selPc0 b,sel354_0.res.stop,sel354_0.res.steps,sel354_0.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact sel354_0.trans (congrArg some (by kernel_rfl))
  · exact sel543_0.trans (congrArg some (by kernel_rfl))
theorem selector_code2 {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) :
    CodeAt image (pcOf (selectorBase b+2)) (selector2) :=
  codeAt_selector hK 1 2 (selector2) (by rfl)
sym_block sel354_2 := symRun {noAlias:=true} (selector2) (pcOf (selectorBase 354+2)) 200
sym_block sel543_2 := symRun {noAlias:=true} (selector2) (pcOf (selectorBase 543+2)) 200
def selState2 : SymState := sel354_2.res.st
def selPc2 (b : Nat) : E := rebase sel354_2.res.pc (pcOf (selectorBase b+7)) (pcOf (selectorBase b+6))
theorem selRun2 {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} (selector2) (pcOf (selectorBase b+2)) 200 =
    some ⟨selState2,selPc2 b,sel354_2.res.stop,sel354_2.res.steps,sel354_2.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact sel354_2.trans (congrArg some (by kernel_rfl))
  · exact sel543_2.trans (congrArg some (by kernel_rfl))
theorem selector_code6 {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) :
    CodeAt image (pcOf (selectorBase b+6)) (selector6 b) :=
  codeAt_selector hK 2 6 (selector6 b) (by rfl)
sym_block sel354_6 := symRun {noAlias:=true} (selector6 354) (pcOf (selectorBase 354+6)) 200
sym_block sel543_6 := symRun {noAlias:=true} (selector6 543) (pcOf (selectorBase 543+6)) 200
def selState6 : SymState := sel354_6.res.st
def selPc6 (b : Nat) : E := .c (pcOf (b+468))
theorem selRun6 {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} (selector6 b) (pcOf (selectorBase b+6)) 200 =
    some ⟨selState6,selPc6 b,sel354_6.res.stop,sel354_6.res.steps,sel354_6.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact sel354_6.trans (congrArg some (by kernel_rfl))
  · exact sel543_6.trans (congrArg some (by kernel_rfl))
theorem selector_code7 {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition) :
    CodeAt image (pcOf (selectorBase b+7)) (selector7 b) :=
  codeAt_selector hK 3 7 (selector7 b) (by rfl)
sym_block sel354_7 := symRun {noAlias:=true} (selector7 354) (pcOf (selectorBase 354+7)) 200
sym_block sel543_7 := symRun {noAlias:=true} (selector7 543) (pcOf (selectorBase 543+7)) 200
def selState7 : SymState := sel354_7.res.st
def selPc7 (b : Nat) : E := .c (pcOf (b+132))
theorem selRun7 {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} (selector7 b) (pcOf (selectorBase b+7)) 200 =
    some ⟨selState7,selPc7 b,sel354_7.res.stop,sel354_7.res.steps,sel354_7.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact sel354_7.trans (congrArg some (by kernel_rfl))
  · exact sel543_7.trans (congrArg some (by kernel_rfl))
theorem selector0_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (selectorBase b)) (v : BitVec 128)
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc=(if T3.lowerSpare v then pcOf (selectorBase b+7) else pcOf (selectorBase b+2)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (selRun0 hK.2.1) (selector_code0 hK) s hpc
    (by simp [selState0,sel354_0.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,selPc0,rebase,sel354_0.res,E.eval,CmpOp.eval,BinOp.eval,h6,h7]
    rw [BitVec.slt_zero_eq_msb,spare_msb]
    by_cases h : T3.lowerSpare v <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [selState0,sel354_0.res,rv_simp] <;> rfl
  · intro A _ _; simp [selState0,sel354_0.res,rv_simp]
theorem selector2_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (selectorBase b+2)) (v : BitVec 128)
    (h12 : s.getReg .x12=BitVec.ofNat 64 EOUT)
    (hm0 : s.getMem (BitVec.ofNat 64 (EOUT+16))=v.extractLsb' 0 64)
    (hm1 : s.getMem (BitVec.ofNat 64 (EOUT+24))=v.extractLsb' 64 64) :
    ∃ t, Steps image s 4 4 t ∧
      t.pc=(if T3.lowerSpare v then pcOf (selectorBase b+7) else pcOf (selectorBase b+6)) ∧
      t.getReg .x6=v.extractLsb' 0 64 ∧ t.getReg .x7=v.extractLsb' 64 64 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (selRun2 hK.2.1) (selector_code2 hK) s hpc
    (by simp [selState2,sel354_2.res,rv_simp,h12,EOUT,accessValid_iff,MEMORY_BYTES]),?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,selPc2,rebase,sel354_2.res,E.eval,CmpOp.eval,BinOp.eval]
    simp only [h12,show BitVec.ofNat 64 EOUT+16#64=BitVec.ofNat 64 (EOUT+16) from rfl,
      show BitVec.ofNat 64 EOUT+24#64=BitVec.ofNat 64 (EOUT+24) from rfl,hm0,hm1]
    rw [BitVec.slt_zero_eq_msb,spare_msb]
    by_cases h : T3.lowerSpare v <;> simp [h]
  · simpa [selState2,sel354_2.res,rv_simp,h12,EOUT] using hm0
  · simpa [selState2,sel354_2.res,rv_simp,h12,EOUT] using hm1
  · intro r hr; simp at hr; cases r <;> simp_all [selState2,sel354_2.res,rv_simp] <;> rfl
  · intro A _ _; simp [selState2,sel354_2.res,rv_simp]
theorem selector6_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (selectorBase b+6)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+468) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (selRun6 hK.2.1) (selector_code6 hK) s hpc
    (by simp [selState6,sel354_6.res,rv_simp]),?_,?_,?_⟩
  · rfl
  · intro r hr; cases r <;> simp_all [selState6,sel354_6.res,rv_simp] <;> rfl
  · intro A _ _; simp [selState6,sel354_6.res,rv_simp]
theorem selector7_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (selectorBase b+7)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+132) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (selRun7 hK.2.1) (selector_code7 hK) s hpc
    (by simp [selState7,sel354_7.res,rv_simp]),?_,?_,?_⟩
  · rfl
  · intro r hr; cases r <;> simp_all [selState7,sel354_7.res,rv_simp] <;> rfl
  · intro A _ _; simp [selState7,sel354_7.res,rv_simp]
theorem selector_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (selectorBase b)) (a : BitVec 256)
    (lay : T3.Layer) (hl : lay ≠ 0)
    (h6 : s.getReg .x6=(a.extractLsb' 0 128).extractLsb' 0 64)
    (h7 : s.getReg .x7=(a.extractLsb' 0 128).extractLsb' 64 64)
    (h12 : s.getReg .x12=BitVec.ofNat 64 EOUT)
    (hm0 : s.getMem (BitVec.ofNat 64 (EOUT+16))=(a.extractLsb' 128 128).extractLsb' 0 64)
    (hm1 : s.getMem (BitVec.ofNat 64 (EOUT+24))=(a.extractLsb' 128 128).extractLsb' 64 64) :
    ∃ k t, Steps image s k k t ∧ k ≤ 7 ∧
      t.pc=(if T3.lowerSpare (ClaudeWCT.WCT9.encodingAnswer lay a) then pcOf (b+132) else pcOf (b+468)) ∧
      t.getReg .x6=(ClaudeWCT.WCT9.encodingAnswer lay a).extractLsb' 0 64 ∧
      t.getReg .x7=(ClaudeWCT.WCT9.encodingAnswer lay a).extractLsb' 64 64 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u,su,pu,ru,fu⟩ := selector0_spec hK s hpc (a.extractLsb' 0 128) h6 h7
  by_cases hlo : T3.lowerSpare (a.extractLsb' 0 128)
  · rw [if_pos hlo] at pu
    rw [ClaudeWCT.WCT9.encodingAnswer_lower_low lay hl a hlo,if_pos hlo]
    obtain ⟨t,st,pt,rt,ft⟩ := selector7_spec hK u pu
    exact ⟨3,t,su.trans st,by omega,pt,
      (rt.get (by decide)).trans ((ru.get (by decide)).trans h6),
      (rt.get (by decide)).trans ((ru.get (by decide)).trans h7),
      (ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
  · rw [if_neg hlo] at pu
    rw [ClaudeWCT.WCT9.encodingAnswer_lower_high lay hl a hlo]
    obtain ⟨v,sv,pv,g6,g7,rv,fv⟩ := selector2_spec hK u pu (a.extractLsb' 128 128)
      ((ru.get (by decide)).trans h12)
      (by rw [fu.get (by unfold EOUT; omega) (by simp)]; exact hm0)
      (by rw [fu.get (by unfold EOUT; omega) (by simp)]; exact hm1)
    by_cases hhi : T3.lowerSpare (a.extractLsb' 128 128)
    · rw [if_pos hhi] at pv ⊢
      obtain ⟨t,st,pt,rt,ft⟩ := selector7_spec hK v pv
      exact ⟨7,t,(su.trans sv).trans st,by omega,pt,
        (rt.get (by decide)).trans g6,(rt.get (by decide)).trans g7,
        ((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩
    · rw [if_neg hhi] at pv ⊢
      obtain ⟨t,st,pt,rt,ft⟩ := selector6_spec hK v pv
      exact ⟨7,t,(su.trans sv).trans st,by omega,pt,
        (rt.get (by decide)).trans g6,(rt.get (by decide)).trans g7,
        ((ru.trans rv).trans rt).mono (by decide),((fu.trans fv).trans ft).mono (by simp)⟩

sym_block top354_entry := symRun {noAlias:=true} (topEntryCode 354) (pcOf (tcEntry 354)) 200
sym_block top543_entry := symRun {noAlias:=true} (topEntryCode 543) (pcOf (tcEntry 543)) 200
def topState_entry : SymState := top354_entry.res.st
/-- Where the top dispatch word jumps: the R6 kernel `K_ENTRY` (expand 49226, sign 21667). -/
def topEntryTarget (b : Nat) : Nat := if b = 354 then 49226 else 21667
def topPc_entry (b : Nat) : E := .c (pcOf (topEntryTarget b))
theorem topRun_entry {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} (topEntryCode b) (pcOf (tcEntry b)) 200 =
    some ⟨topState_entry,topPc_entry b,top354_entry.res.stop,top354_entry.res.steps,top354_entry.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact top354_entry.trans (congrArg some (by kernel_rfl))
  · exact top543_entry.trans (congrArg some (by kernel_rfl))
theorem top_entry_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (tcEntry b)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (topEntryTarget b) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (topRun_entry hK.2.1) (codeAt_topEntry hK) s hpc
    (by simp [topState_entry,top354_entry.res,rv_simp]),?_,?_,?_⟩
  · rfl
  · intro r hr; cases r <;> simp_all [topState_entry,top354_entry.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState_entry,top354_entry.res,rv_simp]
/-! ### Restricted top choice: `choice_a`, `choice_r` and the path-aware lower credit `pa`. -/
/-- The choice flag scratch word. -/
abbrev FLAG : Nat := 0x667F8
theorem choice_code {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (i o : Nat) (seg : List (BitVec 32)) (hs : (choiceL b)[i]? = some (o,seg)) :
    CodeAt image (pcOf (choiceBase b+o)) seg := codeAt_choice hK i o seg hs
sym_block pa0354 := symRun {noAlias:=true} pa0 (pcOf (choiceBase 354+17)) 200
sym_block pa0543 := symRun {noAlias:=true} pa0 (pcOf (choiceBase 543+17)) 200
def pa0State : SymState := pa0354.res.st
def pa0Pc (b : Nat) : E := rebase pa0354.res.pc (pcOf (choiceBase b+23)) (pcOf (choiceBase b+22))
theorem pa0Run {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} pa0 (pcOf (choiceBase b+17)) 200 =
    some ⟨pa0State,pa0Pc b,pa0354.res.stop,pa0354.res.steps,pa0354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact pa0354.trans (congrArg some (by kernel_rfl))
  · exact pa0543.trans (congrArg some (by kernel_rfl))
sym_block pa5354 := symRun {noAlias:=true} pa5 (pcOf (choiceBase 354+22)) 200
sym_block pa5543 := symRun {noAlias:=true} pa5 (pcOf (choiceBase 543+22)) 200
def pa5State : SymState := pa5354.res.st
theorem pa5Run {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} pa5 (pcOf (choiceBase b+22)) 200 =
    some ⟨pa5State,.c (pcOf (choiceBase b+23)),pa5354.res.stop,pa5354.res.steps,pa5354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact pa5354.trans (congrArg some (by kernel_rfl))
  · exact pa5543.trans (congrArg some (by kernel_rfl))
sym_block paJ354 := symRun {noAlias:=true} (paJ 354) (pcOf (choiceBase 354+23)) 200
sym_block paJ543 := symRun {noAlias:=true} (paJ 543) (pcOf (choiceBase 543+23)) 200
def paJState : SymState := paJ354.res.st
theorem paJRun {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} (paJ b) (pcOf (choiceBase b+23)) 200 =
    some ⟨paJState,.c (pcOf (paTarget b)),paJ354.res.stop,paJ354.res.steps,paJ354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact paJ354.trans (congrArg some (by kernel_rfl))
  · exact paJ543.trans (congrArg some (by kernel_rfl))
/-- `pa`: add the path bonus 4 to the lower reward accumulator `s4` (`x20`) when LOW is spare. -/
theorem pa_spec {image : Image} {b : Nat} {rewardCondition : Prop} (hK : KernAt image b rewardCondition)
    (s : MachineState) (hpc : s.pc=pcOf (choiceBase b+17)) (low : BitVec 128) (acc : Nat)
    (hacc : acc + 4 < 2 ^ 64)
    (hm0 : s.getMem (BitVec.ofNat 64 EOUT)=low.extractLsb' 0 64)
    (hm8 : s.getMem (BitVec.ofNat 64 (EOUT+8))=low.extractLsb' 64 64)
    (h20 : s.getReg .x20=BitVec.ofNat 64 acc) :
    ∃ k t, Steps image s k k t ∧ k ≤ 7 ∧ t.pc=pcOf (paTarget b) ∧
      t.getReg .x20=BitVec.ofNat 64 (acc+if T3.lowerSpare low then 4 else 0) ∧
      RegsExcept s t [.x20,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u,su,pu,ru,fu⟩ : ∃ u, Steps image s 5 5 u ∧
      u.pc=(if T3.lowerSpare low then pcOf (choiceBase b+22) else pcOf (choiceBase b+23)) ∧
      RegsExcept s u [.x29,.x30] ∧ Frame s u (fun _ => False) := by
    refine ⟨_,symRun_sound (pa0Run hK.2.1) (choice_code hK 5 17 pa0 rfl) s hpc
      (by simp [pa0State,pa0354.res,rv_simp,accessValid_iff,MEMORY_BYTES]),?_,?_,?_⟩
    · have h0 : s.getMem 131744#64 = low.extractLsb' 0 64 := by simpa [EOUT] using hm0
      have h8 : s.getMem 131752#64 = low.extractLsb' 64 64 := by simpa [EOUT] using hm8
      have hm := spare_msb low
      rw [BitVec.and_comm] at hm
      simp only [Result.toState_pc,pa0Pc,rebase,pa0354.res,E.eval,CmpOp.eval,BinOp.eval,h0,h8,
        BitVec.slt_zero_eq_msb,hm]
      by_cases h : T3.lowerSpare low <;> simp [h]
    · intro r hr; simp at hr; cases r <;> simp_all [pa0State,pa0354.res,rv_simp] <;> rfl
    · intro A _ _; simp [pa0State,pa0354.res,rv_simp]
  have jump : ∀ w : MachineState, w.pc=pcOf (choiceBase b+23) →
      ∃ t, Steps image w 1 1 t ∧ t.pc=pcOf (paTarget b) ∧ RegsExcept w t [] ∧ Frame w t (fun _ => False) := by
    intro w hw
    refine ⟨_,symRun_sound (paJRun hK.2.1) (choice_code hK 7 23 (paJ b) rfl) w hw
      (by simp [paJState,paJ354.res,rv_simp]),rfl,?_,?_⟩
    · intro r hr; cases r <;> simp_all [paJState,paJ354.res,rv_simp] <;> rfl
    · intro A _ _; simp [paJState,paJ354.res,rv_simp]
  by_cases h : T3.lowerSpare low
  · rw [if_pos h] at pu
    obtain ⟨v,sv,pv,v20,rv,fv⟩ : ∃ v, Steps image u 1 1 v ∧ v.pc=pcOf (choiceBase b+23) ∧
        v.getReg .x20=u.getReg .x20+BitVec.ofNat 64 4 ∧ RegsExcept u v [.x20] ∧ Frame u v (fun _ => False) := by
      refine ⟨_,symRun_sound (pa5Run hK.2.1) (choice_code hK 6 22 pa5 rfl) u pu
        (by simp [pa5State,pa5354.res,rv_simp]),rfl,?_,?_,?_⟩
      · simp [pa5State,pa5354.res,rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [pa5State,pa5354.res,rv_simp] <;> rfl
      · intro A _ _; simp [pa5State,pa5354.res,rv_simp]
    obtain ⟨t,st,pt,rt,ft⟩ := jump v pv
    refine ⟨7,t,(su.trans sv).trans st,le_refl _,pt,?_,((ru.trans rv).trans rt).mono (by decide),
      ((fu.trans fv).trans ft).mono (fun _ _ h => by simp at h)⟩
    rw [rt.get (by decide),v20,ru.get (by decide),h20,if_pos h,BitVec.ofNat_add]
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,rt,ft⟩ := jump u pu
    refine ⟨6,t,su.trans st,by omega,pt,?_,(ru.trans rt).mono (by decide),
      (fu.trans ft).mono (fun _ _ h => by simp at h)⟩
    rw [rt.get (by decide),ru.get (by decide),h20,if_neg h,Nat.add_zero]
end SigGolfCandidate.T3M.Search

namespace SigGolfCandidate.T3M.Search.LowerLUT
set_option linter.unusedSimpArgs false
open SigGolfCandidate.T3 (Digest Layer)
open ClaudeWCT.WCT9
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

def score (first : Bool) (r : Nat) : Nat :=
  (if r % 8 = 6 then 1 else 0) + (if r / 8 % 8 = 6 then 1 else 0) +
  (if r / 64 % 8 = 6 then 1 else 0) + 4 *
    ((if first && decide (r % 8 = 7) then 1 else 0) +
     (if r / 8 % 8 = 7 ∧ (first = true ∨ r % 8 = 7) then 1 else 0) +
     (if r / 64 % 8 = 7 ∧ r / 8 % 8 = 7 then 1 else 0))
def shift (q : Nat) : Nat := if q < 7 then 9*q else 64+9*(q-7)
def rank (v : Digest) (q : Nat) : Nat := v.toNat / 2 ^ shift q % 512

theorem score_bound (first : Bool) (r : Nat) (hr : r < 512) : score first r ≤ 12 := by
  revert r; cases first <;> decide +kernel

theorem packed_field (n a j : Nat) (hj : j < 3) :
    (n / 2^a % 512) / 2^(3*j) % 8 = n / 2^(a+3*j) % 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (512 : Nat)=2^9 from rfl, show (8 : Nat)=2^3 from rfl]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 3
  · simp only [hi, decide_true, Bool.true_and, show i+3*j<9 by omega]
    congr 1; omega
  · simp [hi]

theorem digits_field (v : Digest) (c q j : Nat) (hq : q < 14) (hj : j < 3) :
    (lowDigits v ++ [c]).getD (3*q+j) 0 = rank v q / 2^(3*j) % 8 := by
  have hi : 3*q+j < 42 := by omega
  rw [List.getD_append _ _ _ _ (by simpa [lowDigits_length] using hi)]
  simp only [lowDigits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  rw [rank, packed_field _ _ _ hj]
  congr 3
  unfold shift T3.lowerShift
  split_ifs <;> omega

theorem group_reward (ds : List Nat) (q r : Nat) (hq : q < 14)
    (h0 : ds.getD (3*q) 0 = r % 8)
    (h1 : ds.getD (3*q+1) 0 = r/8%8)
    (h2 : ds.getD (3*q+2) 0 = r/64%8) :
    score (decide (q=0)) r = Reward.reward false ds (3*q) +
      Reward.reward false ds (3*q+1) + Reward.reward false ds (3*q+2) := by
  have hprev1 : 3*q+1-1=3*q := by omega
  have hprev2 : 3*q+2-1=3*q+1 := by omega
  simp only [Reward.reward, Reward.credit, Reward.saved, Reward.maximum, Reward.direct,
    Bool.false_and, Bool.not_false, Bool.true_and, if_false, Nat.reduceSub,
    hprev1, hprev2, h0, h1, h2]
  by_cases hq0 : q=0
  · subst q
    simp only [score, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, decide_true,
      Bool.true_and, true_or, or_true, and_true, Nat.reduceEqDiff, decide_false,
      Bool.false_or, Bool.true_or, and_false, or_false, not_false_eq_true,
      Nat.zero_mod, not_true_eq_false, Nat.reduceSub]
    simp only [Bool.false_eq_true, if_false, Nat.reduceSub, decide_eq_true_eq, false_or, Nat.reduceEqDiff, not_false_eq_true, true_and]
    simp only [ne_eq, Nat.reduceEqDiff, not_false_eq_true, true_and]
    omega
  · have hq3 : 3*q≠0 := by omega
    have hq31 : 3*q≠1 := by omega
    have hq10 : 3*q+1≠0 := by omega
    have hq11 : 3*q+1≠1 := by omega
    have hq20 : 3*q+2≠0 := by omega
    have hq21 : 3*q+2≠1 := by omega
    have hm0 : 3*q%3=0 := by omega
    have hm1 : (3*q+1)%3=1 := by omega
    have hm2 : (3*q+2)%3=2 := by omega
    simp only [score, hq0, hq3, hq31, hq10, hq11, hq20, hq21, hm0, hm1, hm2,
      decide_false, Bool.false_and, Bool.false_or, Bool.false_eq_true, if_false,
      false_or, or_false, and_false, false_and, and_true, Nat.reduceEqDiff,
      not_false_eq_true, not_true_eq_false, Nat.zero_add, Nat.mul_zero]
    simp only [Nat.reduceSub, ne_eq, Nat.reduceEqDiff, not_true_eq_false, not_false_eq_true, false_and, and_false, if_false, true_and, Nat.add_zero, Nat.mul_zero]
    omega

theorem sum_groups (f : Nat → Nat) :
    ((List.range 43).map f).sum =
      ((List.range 14).map (fun q => f (3*q)+f (3*q+1)+f (3*q+2))).sum + f 42 := by
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.zero_add, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
  omega

theorem packed_reward (lay : Layer) (hl : lay ≠ 0) (v : Digest) (c : Nat) :
    ((List.range 14).map (fun q => score (decide (q=0)) (rank v q))).sum +
      (if c=6 then 1 else 0) =
      wordCredit lay (lowDigits v ++ [c]) + 4 * savedCopies lay (lowDigits v ++ [c]) := by
  have hcount : T3.chainCount lay=43 := by fin_cases lay <;> simp_all [T3.chainCount]
  have hrew := Reward.reward_sum_counts false (lowDigits v ++ [c]) (List.range 43)
  have heq : wordCredit lay (lowDigits v ++ [c]) + 4 * savedCopies lay (lowDigits v ++ [c]) =
      ((List.range 43).map (Reward.reward false (lowDigits v ++ [c]))).sum := by
    rw [hrew]
    simp only [wordCredit, savedCopies, hcount]
    have hcredit := Reward.credit_layer lay hl (lowDigits v ++ [c])
    have hsaved := Reward.saved_layer lay hl (lowDigits v ++ [c])
    simp only [hl, decide_false] at hcredit hsaved
    simp only [hcredit, hsaved]
  rw [heq, sum_groups]
  apply congrArg₂ Nat.add
  · apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    have hq' : q < 14 := List.mem_range.mp hq
    exact group_reward _ q _ hq'
      (by simpa using digits_field v c q 0 hq' (by omega))
      (by simpa using digits_field v c q 1 hq' (by omega))
      (by simpa using digits_field v c q 2 hq' (by omega))
  · have hc : (lowDigits v ++ [c]).getD 42 0=c := by rw [List.getD_append_right _ _ _ _ (by simp [lowDigits_length])]; simp [lowDigits_length]
    have hc' : (lowDigits v ++ [c])[42]?.getD 0=c := hc
    simp [Reward.reward,Reward.credit,Reward.saved,Reward.direct,Reward.maximum,hc']

end SigGolfCandidate.T3M.Search.LowerLUT
namespace SigGolfCandidate.T3M.Search.LowerLUT
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

def piece (b o n : Nat) : List (BitVec 32) := ((Reward.fastCode b false).drop o).take n

def src (q : Nat) : Reg := if q<7 then .x6 else .x7
def shrE (q : Nat) : E := .bin .srl (.reg (src q)) (.c (BitVec.ofNat 64 (9*(q%7))))
def addrE (q : Nat) : E := .bin .add (.bin .and (shrE q) (.c 511)) (.reg .x11)
def prefixResult (b q : Nat) : Result :=
  ⟨{SymState.init with regs:={RegFile.init with r10:=shrE q,r28:=addrE q}},
    .c (pcOf (Reward.base b false+3+5*q+3)),.endOfCode,3,3⟩
theorem prefix_run {b : Nat} (hb : b=354 ∨ b=543) (q : Nat) (hq : q<14) :
    symRun {noAlias:=true} (piece b (3+5*q) 3) (pcOf (Reward.base b false+3+5*q)) 10 =
      some (prefixResult b q) := by
  rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl

theorem score_lookup (first : Bool) (r : Nat) : score first r=Reward.lowerLookup first r := by
  cases first <;> unfold score Reward.lowerLookup Reward.tripleScore <;>
    by_cases h0 : r%8=7 <;> by_cases h1 : r/8%8=7 <;> by_cases h2 : r/64%8=7 <;>
    simp [h0,h1,h2] <;> omega

theorem lookup_table (s : MachineState) (ht : Reward.LowerTablesOK s) (q r : Nat) (hq : q<14) (hr : r<512) :
    s.getByte (BitVec.ofNat 64 ((if q=0 then 16774144 else 16774656)+r)) =
      BitVec.ofNat 8 (score (decide (q=0)) r) := by
  by_cases hq0 : q=0
  · subst q
    have hh := ht (1024+r) (by omega) (by omega)
    simpa [Reward.rewardTableByte,TOP_DATA,show 1024+r<1536 by omega,
      show 1024+r-1024=r by omega,score_lookup,← Nat.add_assoc] using hh
  · have hh := ht (1536+r) (by omega) (by omega)
    simpa [Reward.rewardTableByte,TOP_DATA,hq0,show ¬1536+r<1536 by omega,
      show 1536+r<2048 by omega,show 1536+r-1536=r by omega,score_lookup,← Nat.add_assoc] using hh

def addResult (b q : Nat) : Result :=
  ⟨{SymState.init with regs:={RegFile.init with r20:=.bin .add (.reg .x20) (.reg .x29)}},
    .c (pcOf (Reward.base b false+3+5*q+5)),.endOfCode,1,1⟩
theorem add_run {b : Nat} (hb : b=354 ∨ b=543) (q : Nat) (hq : q<14) :
    symRun {noAlias:=true} (piece b (3+5*q+4) 1) (pcOf (Reward.base b false+3+5*q+4)) 2 =
      some (addResult b q) := by
  rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl

def loadOff (q : Nat) : BitVec 12 := BitVec.ofNat 12 (if q=0 then 3072 else 3584)
theorem load_address (q r : Nat) (_hr : r<512) :
    BitVec.ofNat 64 (r+16775168) + signExtend12 (loadOff q) =
      BitVec.ofNat 64 ((if q=0 then 16774144 else 16774656)+r) := by
  by_cases hq : q=0
  · simp only [loadOff,hq,if_true]
    change BitVec.ofNat 64 (r+16775168)+18446744073709550592#64=BitVec.ofNat 64 (16774144+r)
    rw [BitVec.ofNat_add,BitVec.add_assoc]
    change BitVec.ofNat 64 r + BitVec.ofNat 64 16774144 = _
    rw [← BitVec.ofNat_add,Nat.add_comm]
  · simp only [loadOff,hq,if_false]
    change BitVec.ofNat 64 (r+16775168)+18446744073709551104#64=BitVec.ofNat 64 (16774656+r)
    rw [BitVec.ofNat_add,BitVec.add_assoc]
    change BitVec.ofNat 64 r + BitVec.ofNat 64 16774656 = _
    rw [← BitVec.ofNat_add,Nat.add_comm]

def partialScore (v : Digest) (n : Nat) : Nat :=
  ((List.range n).map (fun q=>score (decide (q=0)) (rank v q))).sum

theorem partial_succ (v : Digest) (n : Nat) : partialScore v (n+1)=partialScore v n+score (decide (n=0)) (rank v n) := by
  simp [partialScore,List.range_succ]

theorem partial_bound (v : Digest) (n : Nat) : partialScore v n≤12*n := by
  induction n with
  | zero => simp [partialScore]
  | succ n ih =>
    rw [partial_succ]
    have hh := score_bound (decide (n=0)) (rank v n) (Nat.mod_lt _ (by decide))
    omega

sym_block lowerInit := symRun {noAlias:=true} (piece 354 0 3) (pcOf (Reward.base 354 false)) 4
def initResult (b : Nat) : Result := ⟨lowerInit.res.st,.c (pcOf (Reward.base b false+3)),.endOfCode,3,3⟩
theorem init_run {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} (piece b 0 3) (pcOf (Reward.base b false)) 4=some (initResult b) := by
  rcases hb with rfl | rfl <;> kernel_rfl

end SigGolfCandidate.T3M.Search.LowerLUT

namespace SigGolfCandidate.T3M.Search.CanonicalReward
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem code_take_slice {image : Image} {base length : Nat} {words : List (BitVec 32)}
    (hc : CodeAt image (pcOf base) (words.take length)) (hl : length≤words.length)
    (offset count : Nat) (ho : offset+count≤length) :
    CodeAt image (pcOf (base+offset)) ((words.drop offset).take count) := by
  have he : words.take length = words.take offset ++ (words.drop offset).take count ++
      (words.drop (offset+count)).take (length-(offset+count)) := by
    rw [show length=offset+(count+(length-(offset+count))) by omega,List.take_add,List.take_add,List.drop_drop]
    rw [List.append_assoc]
    congr 3 <;> omega
  rw [he] at hc
  have hh := CodeAt.drop_prefix hc
  have hlen : (words.take offset).length=offset := by rw [List.length_take,Nat.min_eq_left (by omega)]
  rw [hlen] at hh
  convert hh using 1
  simp only [pcOf,←BitVec.ofNat_add]
  congr 1
  omega

def PrefixAt (image : Image) (b : Nat) : Prop :=
  CodeAt image (pcOf (Reward.base b false)) ((Reward.fastCode b false).take 77) ∧
    CodeAt image (pcOf (Reward.base b true)) ((Reward.fastCode b true).take 95)

theorem lower_slice {image : Image} {b : Nat} (hR : PrefixAt image b)
    (offset count : Nat) (h : offset+count≤77) :
    CodeAt image (pcOf (Reward.base b false+offset)) (LowerLUT.piece b offset count) :=
  code_take_slice hR.1 (by rw [Reward.fastCode_length];decide) offset count h

end SigGolfCandidate.T3M.Search.CanonicalReward

namespace SigGolfCandidate.T3M.Search.CanonicalReward.Lower
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open SigGolfCandidate.T3M.Search.LowerLUT
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
theorem prefix_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : CanonicalReward.PrefixAt image b)
    (s : MachineState) (q : Nat) (hq : q<14) (v : Digest)
    (hp : s.pc=pcOf (Reward.base b false+3+5*q))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=16775168#64) :
    ∃ t, Steps image s 3 3 t ∧ t.pc=pcOf (Reward.base b false+3+5*q+3) ∧
      t.getReg .x28=BitVec.ofNat 64 (rank v q+16775168) ∧
      RegsExcept s t [.x10,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (prefix_run hb q hq) (by simpa only [Nat.add_assoc] using CanonicalReward.lower_slice hR (3+5*q) 3 (by omega)) s hp
    (by simp [prefixResult,SymState.init,rv_simp]),rfl,?_,?_,?_⟩
  · simp only [prefixResult,rv_simp,addrE,shrE,E.eval,BinOp.eval,h11]
    have he : (s.getReg (src q) >>> ((BitVec.ofNat 64 (9*(q%7))).toNat % 64)) &&& 511#64 =
        BitVec.ofNat 64 (rank v q) := by
      have hs : (BitVec.ofNat 64 (9*(q%7))).toNat % 64=9*(q%7) := by simp; omega
      rw [hs]
      unfold src rank shift
      by_cases hh : q<7
      · rw [if_pos hh,if_pos hh,h6]
        simpa [Nat.mod_eq_of_lt hh] using ext_shr_mask v 0 (9*q) 9 (by omega)
      · rw [if_neg hh,if_neg hh,h7]
        have hmod : q%7=q-7 := by omega
        simpa [hmod] using ext_shr_mask v 64 (9*(q-7)) 9 (by omega)
    rw [he]
    exact (BitVec.ofNat_add _ _).symm
  · intro r hr; cases r <;> simp_all [prefixResult,SymState.init,RegFile.init,rv_simp] <;> rfl
  · intro A _ _; simp [prefixResult,SymState.init,rv_simp]

theorem add_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : CanonicalReward.PrefixAt image b)
    (s : MachineState) (q : Nat) (hq : q<14) (hp : s.pc=pcOf (Reward.base b false+3+5*q+4)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (Reward.base b false+3+5*q+5) ∧
      t.getReg .x20=s.getReg .x20+s.getReg .x29 ∧ RegsExcept s t [.x20] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (add_run hb q hq) (by simpa only [Nat.add_assoc] using CanonicalReward.lower_slice hR (3+5*q+4) 1 (by omega)) s hp
    (by simp [addResult,SymState.init,rv_simp]),rfl,?_,?_,?_⟩
  · simp [addResult,SymState.init,rv_simp]
  · intro r hr; cases r <;> simp_all [addResult,rv_simp] <;> rfl
  · intro A _ _; simp [addResult,SymState.init,rv_simp]

theorem gadget_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : CanonicalReward.PrefixAt image b)
    (s : MachineState) (q : Nat) (hq : q<14) (v : Digest) (ht : Reward.LowerTablesOK s)
    (hp : s.pc=pcOf (Reward.base b false+3+5*q))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=16775168#64) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf (Reward.base b false+3+5*(q+1)) ∧
      t.getReg .x20=s.getReg .x20+BitVec.ofNat 64 (score (decide (q=0)) (rank v q)) ∧
      RegsExcept s t [.x10,.x20,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,ux,ru,fu⟩ := prefix_spec hb hR s q hq v hp h6 h7 h11
  have hr : rank v q<512 := Nat.mod_lt _ (by decide)
  have hc := CanonicalReward.lower_slice hR (3+5*q+3) 1 (by omega)
  have hcode : piece b (3+5*q+3) 1=[if q=0 then 0xc00e4e83 else 0xe00e4e83] := by
    rcases hb with rfl | rfl <;> interval_cases q <;> kernel_rfl
  rw [hcode] at hc
  have hdec : decodeInstruction (if q=0 then 0xc00e4e83 else 0xe00e4e83) =
      some (.base (.LBU .x29 .x28 (loadOff q))) := by
    by_cases hz:q=0 <;> simp only [loadOff,hz,if_true,if_false] <;> rfl
  have ha : u.getReg .x28+signExtend12 (loadOff q) =
      BitVec.ofNat 64 ((if q=0 then 16774144 else 16774656)+rank v q) := by rw [ux,load_address q _ hr]
  have hv : accessValid (u.getReg .x28+signExtend12 (loadOff q)) 1=true := by
    rw [ha]; simp only [accessValid_iff,MEMORY_BYTES]
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by split_ifs <;> omega)]
    norm_num
    split_ifs <;> omega
  have sl := steps_lbu hc (by simpa only [Nat.add_assoc] using pu) hdec hv
  have ht' : Reward.LowerTablesOK u := ht.frame fu (by simp)
  have hm := lookup_table u ht' q (rank v q) hq hr
  rw [ha,hm] at sl
  have hw : (BitVec.ofNat 8 (score (decide (q=0)) (rank v q))).zeroExtend 64 =
      BitVec.ofNat 64 (score (decide (q=0)) (rank v q)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    have hbound := score_bound (decide (q=0)) (rank v q) hr
    norm_num; omega
  rw [hw] at sl
  let u1 := (u.setReg .x29 (BitVec.ofNat 64 (score (decide (q=0)) (rank v q)))).setPC (u.pc+4)
  have pu1 : u1.pc=pcOf (Reward.base b false+3+5*q+4) := by
    simp only [u1,MachineState.setPC,pu,pcOf_add4]
  obtain ⟨t,st,pt,tx,rt,ft⟩ := add_spec hb hR u1 q hq pu1
  have rl : RegsExcept u u1 [.x29] := by
    intro r hr
    have hr' : r≠.x29 := by simpa using hr
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr')
  have fl : Frame u u1 (fun _=>False) := by intro A _ _; rfl
  refine ⟨t,(su.trans sl).trans st,?_,?_,((ru.trans rl).trans rt).mono (by decide),
    ((fu.trans fl).trans ft).mono (by simp)⟩
  · convert pt using 1 <;> congr 1 <;> omega
  · rw [tx]
    change (u.setReg .x29 (BitVec.ofNat 64 (score (decide (q=0)) (rank v q)))).getReg .x20+(u.setReg .x29 (BitVec.ofNat 64 (score (decide (q=0)) (rank v q)))).getReg .x29 = _
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x20),
      MachineState.getReg_setReg_eq (by decide : Reg.x29 ≠ .x0),ru.get (by decide : Reg.x20 ∉ [.x10,.x28])]

theorem loop_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : CanonicalReward.PrefixAt image b)
    (s : MachineState) (v : Digest) (ht : Reward.LowerTablesOK s)
    (hp : s.pc=pcOf (Reward.base b false+3))
    (h6 : s.getReg .x6=v.extractLsb' 0 64) (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h11 : s.getReg .x11=16775168#64) (h20 : s.getReg .x20=0) (n : Nat) (hn : n≤14) :
    ∃ t, Steps image s (5*n) (5*n) t ∧ t.pc=pcOf (Reward.base b false+3+5*n) ∧
      t.getReg .x20=BitVec.ofNat 64 (partialScore v n) ∧
      RegsExcept s t [.x10,.x20,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  induction n with
  | zero => exact ⟨s,Steps.refl s,by simpa using hp,by simpa [partialScore] using h20,RegsExcept.refl _ _,Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨u,su,pu,ux,ru,fu⟩ := ih (by omega)
    obtain ⟨t,st,pt,tx,rt,ft⟩ := gadget_spec hb hR u n (by omega) v (ht.frame fu (by simp)) pu
      ((ru.get (by decide)).trans h6) ((ru.get (by decide)).trans h7) ((ru.get (by decide)).trans h11)
    refine ⟨t,?_,pt,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
    · convert su.trans st using 1 <;> omega
    · rw [tx,ux,partial_succ,BitVec.ofNat_add]

theorem init_spec {image : Image} {b : Nat} (hb : b=354 ∨ b=543) (hR : CanonicalReward.PrefixAt image b)
    (s : MachineState) (hp : s.pc=pcOf (Reward.base b false)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc=pcOf (Reward.base b false+3) ∧
      t.getReg .x11=16775168#64 ∧ t.getReg .x20=0 ∧
      RegsExcept s t [.x11,.x20] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound (init_run hb) (CanonicalReward.lower_slice hR 0 3 (by omega)) s hp
    (by simp [initResult,lowerInit.res,rv_simp]),rfl,?_,?_,?_,?_⟩
  · simp [initResult,lowerInit.res,rv_simp]
  · simp [initResult,lowerInit.res,rv_simp]
  · intro r hr; cases r <;> simp_all [initResult,lowerInit.res,rv_simp] <;> rfl
  · intro A _ _; simp [initResult,lowerInit.res,rv_simp]

end SigGolfCandidate.T3M.Search.CanonicalReward.Lower
namespace SigGolfCandidate.T3M.Search.CanonicalReward.Top
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
open SigGolfCandidate.T3M.Search.Reward SigGolfCandidate.T3M.Search.Reward.PackedTop
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
end SigGolfCandidate.T3M.Search.CanonicalReward.Top
