import SigGolfCandidate.AllRouteResidualParts
import SigGolfCandidate.AllRouteThird
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRouteHelpers
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify SigGolfCandidate.AllRoute SigGolfCandidate.T3
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
structure SignSavedCode (image : Image) : Prop where
  raw : CodeAt image (pcOf 25901) signRawCode
  one : CodeAt image (pcOf 25901) signDispatchOneCode
  two : CodeAt image (pcOf 25901) signDispatchTwoCode
  three : CodeAt image (pcOf 25901) signOneCode
  clamp : CodeAt image (pcOf 25929) signClampPreCode
  zero : CodeAt image (pcOf 25931) signClampZeroCode
  restore : CodeAt image (pcOf 25932) signRestoreCode
 theorem signSavedFront_steps {image : Image} (hc : SignSavedCode image)
    (s : MachineState) (hp : s.pc=pcOf 25901) (lay : Layer) (hl : lay ≠ 0)
    (leaf r c : Nat) (hleaf : leaf < 2^height lay) (hr : r < 2^32) (hcr : c ≤ r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) :
    ∃ t n, Steps image s n n t ∧ n ≤ 32 ∧ t.pc=pcOf 25932 ∧
      t.getReg .x6=BitVec.ofNat 64 ((r-c)-usedSave lay.val leaf) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨a,sa,pa,a6,ra,fa⟩ := signRaw_steps hc.raw s hp r c hr hcr h6 h7
  have a8 := (ra.get (by decide : Reg.x8 ∉ [.x6])).trans h8
  have a18 := (ra.get (by decide : Reg.x18 ∉ [.x6])).trans h18
  fin_cases lay
  · exact (hl rfl).elim
  · have hb : leaf < 128 := by simpa [height] using hleaf
    obtain ⟨b,nb,ab,hnb,pb,b7,rb,fb⟩ := signDispatchOne_steps hc.one a pa ⟨leaf,hb⟩ a18 a8
    have b6 := (rb.get (by decide : Reg.x6 ∉ [.x7,.x28])).trans a6
    have hs : lowerSave 1 leaf ≤ 2 := by simpa [usedSave] using usedSave_le_two 1 leaf
    obtain ⟨t,nt,bt,hnt,pt,t6,rt,ft⟩ := signClamp_steps hc.clamp hc.zero b pb (r-c) (lowerSave 1 leaf) (by omega) hs b6 b7
    refine ⟨t,1+(nb+nt),sa.trans (ab.trans bt),by omega,pt,?_,(ra.trans (rb.trans rt)).mono (by simp),(fa.trans (fb.trans ft)).mono (by simp)⟩
    simpa [usedSave] using t6
  · have hb : leaf < 64 := by simpa [height] using hleaf
    obtain ⟨b,nb,ab,hnb,pb,b7,rb,fb⟩ := signDispatchTwo_steps hc.two a pa ⟨leaf,hb⟩ a18 a8
    have b6 := (rb.get (by decide : Reg.x6 ∉ [.x7,.x28])).trans a6
    have hs : lowerSave 2 leaf ≤ 2 := by simpa [usedSave] using usedSave_le_two 2 leaf
    obtain ⟨t,nt,bt,hnt,pt,t6,rt,ft⟩ := signClamp_steps hc.clamp hc.zero b pb (r-c) (lowerSave 2 leaf) (by omega) hs b6 b7
    refine ⟨t,1+(nb+nt),sa.trans (ab.trans bt),by omega,pt,?_,(ra.trans (rb.trans rt)).mono (by simp),(fa.trans (fb.trans ft)).mono (by simp)⟩
    simpa [usedSave] using t6
  · obtain ⟨t,nt,ast,hnt,pt,rt,ft⟩ := signThree_steps hc.three a pa a8
    refine ⟨t,1+nt,sa.trans ast,by omega,pt,?_,(ra.trans rt).mono (by simp),(fa.trans ft).mono (by simp)⟩
    simpa [usedSave] using (rt.get (by decide : Reg.x6 ∉ [.x7])).trans a6
#print axioms signSavedFront_steps
 theorem signSaved_steps {image : Image} (hc : SignSavedCode image)
    (s : MachineState) (hp : s.pc=pcOf 25901) (lay : Layer) (hl : lay ≠ 0)
    (leaf r c : Nat) (hleaf : leaf < 2^height lay) (hr : r < 2^32) (hcr : c ≤ r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c)
    (h8 : s.getReg .x8=BitVec.ofNat 64 lay.val) (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) :
    ∃ t n, Steps image s n n t ∧ n ≤ 34 ∧ t.pc=pcOf 22456 ∧
      t.getReg .x6=BitVec.ofNat 64 ((r-c)-usedSave lay.val leaf) ∧
      t.getReg .x28=BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨a,na,sa,hna,pa,a6,ra,fa⟩ := signSavedFront_steps hc s hp lay hl leaf r c hleaf hr hcr h6 h7 h8 h18
  obtain ⟨t,ast,pt,t28,rt,ft⟩ := signRestore_steps hc.restore a pa
  exact ⟨t,na+2,sa.trans ast,by omega,pt,(rt.get (by decide)).trans a6,t28,
    (ra.trans rt).mono (by simp),(fa.trans ft).mono (by simp)⟩
#print axioms signSaved_steps
end SigGolfCandidate.T3M.AllRouteHelpers
