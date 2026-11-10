import SigGolfCandidate.AllRoutePathSound
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRouteHelpers
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.all false
 theorem difference_slt (d saved : Nat) (hd : d < 2^32) (hs : saved ≤ 2) :
    (BitVec.ofNat 64 d - BitVec.ofNat 64 saved).slt 0 = decide (d < saved) := by
  by_cases hle : saved ≤ d
  · rw [BitVec.ofNat_sub_ofNat_of_le d saved (by omega) hle]
    have hb : d-saved < 2^64 := by omega
    have hn : (BitVec.ofNat 64 (d-saved)).toNat = d-saved := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    have hi : 2*(BitVec.ofNat 64 (d-saved)).toNat < 2^64 := by rw [hn]; omega
    simp only [BitVec.slt, BitVec.toInt_eq_toNat_of_lt hi]
    change decide (Int.ofNat ((d-saved)%2^64) < 0) = decide (d < saved)
    simp [show ¬d<saved by omega]
    exact Int.emod_nonneg _ (by norm_num)
  · have hsmall : d≤1 := by omega
    interval_cases saved <;> interval_cases d <;> first | omega | decide +kernel
def signClampPreCode : List (BitVec 32) := [0x40730333,0x35463]
sym_block signClampPre := symRun {noAlias:=true} signClampPreCode (pcOf 25929) 3
def signClampZeroCode : List (BitVec 32) := [0x313]
sym_block signClampZero := symRun {noAlias:=true} signClampZeroCode (pcOf 25931) 2
 theorem signClamp_pre {image : Image} (hc : CodeAt image (pcOf 25929) signClampPreCode)
    (s : MachineState) (hp : s.pc=pcOf 25929) (d saved : Nat) (hd : d<2^32) (hs : saved≤2)
    (hD : s.getReg .x6=BitVec.ofNat 64 d) (hS : s.getReg .x7=BitVec.ofNat 64 saved) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if d<saved then pcOf 25931 else pcOf 25932) ∧
      t.getReg .x6=BitVec.ofNat 64 d-BitVec.ofNat 64 saved ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound signClampPre hc s hp (by simp [signClampPre.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,signClampPre.res]
    t3n [hD,hS]
    change (if (!(BitVec.ofNat 64 d-BitVec.ofNat 64 saved).slt 0)=true then pcOf 25932 else pcOf 25931) = _
    rw [difference_slt d saved hd hs]
    by_cases h : d<saved <;> simp [h,pcOf]
  · simp [signClampPre.res,rv_simp,hD,hS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; rfl
 theorem signClamp_zero {image : Image} (hc : CodeAt image (pcOf 25931) signClampZeroCode)
    (s : MachineState) (hp : s.pc=pcOf 25931) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 25932 ∧ t.getReg .x6=0 ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound signClampZero hc s hp (by simp [signClampZero.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; rfl
 theorem signClamp_steps {image : Image} (hc : CodeAt image (pcOf 25929) signClampPreCode)
    (hz : CodeAt image (pcOf 25931) signClampZeroCode)
    (s : MachineState) (hp : s.pc=pcOf 25929) (d saved : Nat) (hd : d<2^32) (hs : saved≤2)
    (hD : s.getReg .x6=BitVec.ofNat 64 d) (hS : s.getReg .x7=BitVec.ofNat 64 saved) :
    ∃ t n, Steps image s n n t ∧ n≤3 ∧ t.pc=pcOf 25932 ∧
      t.getReg .x6=BitVec.ofNat 64 (d-saved) ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,ud,ru,fu⟩ := signClamp_pre hc s hp d saved hd hs hD hS
  by_cases h : d<saved
  · rw [if_pos h] at pu
    obtain ⟨t,ut,pt,td,rt,ft⟩ := signClamp_zero hz u pu
    refine ⟨t,3,su.trans ut,by decide,pt,?_,(ru.trans rt).mono (by simp),(fu.trans ft).mono (by simp)⟩
    rw [Nat.sub_eq_zero_of_le (by omega : d ≤ saved)]
    exact td
  · refine ⟨u,2,su,by decide,?_,?_,ru,fu⟩
    · simpa only [if_neg h] using pu
    · rw [ud,BitVec.ofNat_sub_ofNat_of_le d saved (by omega) (by omega)]
#print axioms signClamp_steps
def expandOneClampPreCode : List (BitVec 32) := [0x406a8ab3,0xad463]
sym_block expandOneClampPre := symRun {noAlias:=true} expandOneClampPreCode (pcOf 56088) 3
def expandOneClampZeroCode : List (BitVec 32) := [0xa93]
sym_block expandOneClampZero := symRun {noAlias:=true} expandOneClampZeroCode (pcOf 56090) 2
 theorem expandOneClamp_pre {image : Image} (hc : CodeAt image (pcOf 56088) expandOneClampPreCode)
    (s : MachineState) (hp : s.pc=pcOf 56088) (d saved : Nat) (hd : d<2^32) (hs : saved≤2)
    (hD : s.getReg .x21=BitVec.ofNat 64 d) (hS : s.getReg .x6=BitVec.ofNat 64 saved) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if d<saved then pcOf 56090 else pcOf 56091) ∧
      t.getReg .x21=BitVec.ofNat 64 d-BitVec.ofNat 64 saved ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound expandOneClampPre hc s hp (by simp [expandOneClampPre.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,expandOneClampPre.res]
    t3n [hD,hS]
    change (if (!(BitVec.ofNat 64 d-BitVec.ofNat 64 saved).slt 0)=true then pcOf 56091 else pcOf 56090) = _
    rw [difference_slt d saved hd hs]
    by_cases h : d<saved <;> simp [h,pcOf]
  · simp [expandOneClampPre.res,rv_simp,hD,hS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; rfl
 theorem expandOneClamp_zero {image : Image} (hc : CodeAt image (pcOf 56090) expandOneClampZeroCode)
    (s : MachineState) (hp : s.pc=pcOf 56090) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 56091 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound expandOneClampZero hc s hp (by simp [expandOneClampZero.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; rfl
 theorem expandOneClamp_steps {image : Image} (hc : CodeAt image (pcOf 56088) expandOneClampPreCode)
    (hz : CodeAt image (pcOf 56090) expandOneClampZeroCode)
    (s : MachineState) (hp : s.pc=pcOf 56088) (d saved : Nat) (hd : d<2^32) (hs : saved≤2)
    (hD : s.getReg .x21=BitVec.ofNat 64 d) (hS : s.getReg .x6=BitVec.ofNat 64 saved) :
    ∃ t n, Steps image s n n t ∧ n≤3 ∧ t.pc=pcOf 56091 ∧
      t.getReg .x21=BitVec.ofNat 64 (d-saved) ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,ud,ru,fu⟩ := expandOneClamp_pre hc s hp d saved hd hs hD hS
  by_cases h : d<saved
  · rw [if_pos h] at pu
    obtain ⟨t,ut,pt,td,rt,ft⟩ := expandOneClamp_zero hz u pu
    refine ⟨t,3,su.trans ut,by decide,pt,?_,(ru.trans rt).mono (by simp),(fu.trans ft).mono (by simp)⟩
    rw [Nat.sub_eq_zero_of_le (by omega : d ≤ saved)]
    exact td
  · refine ⟨u,2,su,by decide,?_,?_,ru,fu⟩
    · simpa only [if_neg h] using pu
    · rw [ud,BitVec.ofNat_sub_ofNat_of_le d saved (by omega) (by omega)]
#print axioms expandOneClamp_steps
def expandTwoClampPreCode : List (BitVec 32) := [0x406a8ab3,0xad463]
sym_block expandTwoClampPre := symRun {noAlias:=true} expandTwoClampPreCode (pcOf 56136) 3
def expandTwoClampZeroCode : List (BitVec 32) := [0xa93]
sym_block expandTwoClampZero := symRun {noAlias:=true} expandTwoClampZeroCode (pcOf 56138) 2
 theorem expandTwoClamp_pre {image : Image} (hc : CodeAt image (pcOf 56136) expandTwoClampPreCode)
    (s : MachineState) (hp : s.pc=pcOf 56136) (d saved : Nat) (hd : d<2^32) (hs : saved≤2)
    (hD : s.getReg .x21=BitVec.ofNat 64 d) (hS : s.getReg .x6=BitVec.ofNat 64 saved) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if d<saved then pcOf 56138 else pcOf 56139) ∧
      t.getReg .x21=BitVec.ofNat 64 d-BitVec.ofNat 64 saved ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound expandTwoClampPre hc s hp (by simp [expandTwoClampPre.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,expandTwoClampPre.res]
    t3n [hD,hS]
    change (if (!(BitVec.ofNat 64 d-BitVec.ofNat 64 saved).slt 0)=true then pcOf 56139 else pcOf 56138) = _
    rw [difference_slt d saved hd hs]
    by_cases h : d<saved <;> simp [h,pcOf]
  · simp [expandTwoClampPre.res,rv_simp,hD,hS]
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; rfl
 theorem expandTwoClamp_zero {image : Image} (hc : CodeAt image (pcOf 56138) expandTwoClampZeroCode)
    (s : MachineState) (hp : s.pc=pcOf 56138) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 56139 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound expandTwoClampZero hc s hp (by simp [expandTwoClampZero.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr; cases r <;> simp at hr <;> rfl
  · intro A hA hn; rfl
 theorem expandTwoClamp_steps {image : Image} (hc : CodeAt image (pcOf 56136) expandTwoClampPreCode)
    (hz : CodeAt image (pcOf 56138) expandTwoClampZeroCode)
    (s : MachineState) (hp : s.pc=pcOf 56136) (d saved : Nat) (hd : d<2^32) (hs : saved≤2)
    (hD : s.getReg .x21=BitVec.ofNat 64 d) (hS : s.getReg .x6=BitVec.ofNat 64 saved) :
    ∃ t n, Steps image s n n t ∧ n≤3 ∧ t.pc=pcOf 56139 ∧
      t.getReg .x21=BitVec.ofNat 64 (d-saved) ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,ud,ru,fu⟩ := expandTwoClamp_pre hc s hp d saved hd hs hD hS
  by_cases h : d<saved
  · rw [if_pos h] at pu
    obtain ⟨t,ut,pt,td,rt,ft⟩ := expandTwoClamp_zero hz u pu
    refine ⟨t,3,su.trans ut,by decide,pt,?_,(ru.trans rt).mono (by simp),(fu.trans ft).mono (by simp)⟩
    rw [Nat.sub_eq_zero_of_le (by omega : d ≤ saved)]
    exact td
  · refine ⟨u,2,su,by decide,?_,?_,ru,fu⟩
    · simpa only [if_neg h] using pu
    · rw [ud,BitVec.ofNat_sub_ofNat_of_le d saved (by omega) (by omega)]
#print axioms expandTwoClamp_steps
end SigGolfCandidate.T3M.AllRouteHelpers
