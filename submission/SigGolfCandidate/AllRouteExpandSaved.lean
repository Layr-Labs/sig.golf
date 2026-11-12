import SigGolfCandidate.AllRouteExpandParts
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRouteHelpers
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify SigGolfCandidate.T3 SigGolfCandidate.AllRoute
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
structure ExpandOneSavedCode (image : Image) : Prop where
  raw : CodeAt image (pcOf 56320) expandOneRawCode
  pure : CodeAt image (pcOf 56320) expandOneCode
  clamp : CodeAt image (pcOf 56344) expandOneClampPreCode
  zero : CodeAt image (pcOf 56346) expandOneClampZeroCode
  ret : CodeAt image (pcOf 56347) expandOneReturnCode
 theorem expandOneSaved_steps {image : Image} (hc : ExpandOneSavedCode image)
    (s : MachineState) (hp : s.pc=pcOf 56320) (index r c : Nat) (hi : index<2^31) (hr : r<2^32) (hcr : c ≤ r)
    (h21 : s.getReg .x21=BitVec.ofNat 64 r) (h6 : s.getReg .x6=BitVec.ofNat 64 c)
    (hm : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t n, Steps image s n n t ∧ n≤33 ∧ t.pc=pcOf 46956 ∧
      t.getReg .x21=BitVec.ofNat 64 ((r-c)-usedSave 1 (route index 1).1) ∧
      RegsExcept s t [.x6,.x7,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨a,sa,pa,a21,a7,ra,fa⟩ := expandOneRaw_steps hc.raw s hp index r c hi hr hcr h21 h6 hm
  have hl : (route index 1).1 < 128 := by simp [route,height]; omega
  obtain ⟨b,nb,ab,hnb,pb,b6,rb,fb⟩ := expandOne_steps hc.pure a pa ⟨(route index 1).1,hl⟩ a7
  have b21 := (rb.get (by decide : Reg.x21 ∉ [.x6,.x28])).trans a21
  have hs : lowerSave 1 (route index 1).1 ≤ 2 := by simpa [usedSave] using usedSave_le_two 1 (route index 1).1
  obtain ⟨v,nv,bv,hnv,pv,v21,rv,fv⟩ := expandOneClamp_steps hc.clamp hc.zero b pb (r-c) (lowerSave 1 (route index 1).1) (by omega) hs b21 b6
  obtain ⟨t,vt,pt,rt,ft⟩ := expandOneReturn_steps hc.ret v pv
  refine ⟨t,5+(nb+(nv+1)),sa.trans (ab.trans (bv.trans vt)),by omega,pt,?_,
    (ra.trans (rb.trans (rv.trans rt))).mono (by simp),(fa.trans (fb.trans (fv.trans ft))).mono (by simp)⟩
  simpa [usedSave] using (rt.get (by decide : Reg.x21 ∉ [])).trans v21
#print axioms expandOneSaved_steps
structure ExpandTwoSavedCode (image : Image) : Prop where
  raw : CodeAt image (pcOf 56384) expandTwoRawCode
  pure : CodeAt image (pcOf 56384) expandTwoCode
  clamp : CodeAt image (pcOf 56392) expandTwoClampPreCode
  zero : CodeAt image (pcOf 56394) expandTwoClampZeroCode
  ret : CodeAt image (pcOf 56395) expandTwoReturnCode
 theorem expandTwoSaved_steps {image : Image} (hc : ExpandTwoSavedCode image)
    (s : MachineState) (hp : s.pc=pcOf 56384) (index r c : Nat) (hi : index<2^31) (hr : r<2^32) (hcr : c ≤ r)
    (h21 : s.getReg .x21=BitVec.ofNat 64 r) (h6 : s.getReg .x6=BitVec.ofNat 64 c)
    (hm : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t n, Steps image s n n t ∧ n≤33 ∧ t.pc=pcOf 46973 ∧
      t.getReg .x21=BitVec.ofNat 64 ((r-c)-usedSave 2 (route index 2).1) ∧
      RegsExcept s t [.x6,.x7,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨a,sa,pa,a21,a7,ra,fa⟩ := expandTwoRaw_steps hc.raw s hp index r c hi hr hcr h21 h6 hm
  have hl : (route index 2).1 < 64 := by simp [route,height]; omega
  obtain ⟨b,nb,ab,hnb,pb,b6,rb,fb⟩ := expandTwo_steps hc.pure a pa ⟨(route index 2).1,hl⟩ a7
  have b21 := (rb.get (by decide : Reg.x21 ∉ [.x6,.x28])).trans a21
  have hs : lowerSave 2 (route index 2).1 ≤ 2 := by simpa [usedSave] using usedSave_le_two 2 (route index 2).1
  obtain ⟨v,nv,bv,hnv,pv,v21,rv,fv⟩ := expandTwoClamp_steps hc.clamp hc.zero b pb (r-c) (lowerSave 2 (route index 2).1) (by omega) hs b21 b6
  obtain ⟨t,vt,pt,rt,ft⟩ := expandTwoReturn_steps hc.ret v pv
  refine ⟨t,5+(nb+(nv+1)),sa.trans (ab.trans (bv.trans vt)),by omega,pt,?_,
    (ra.trans (rb.trans (rv.trans rt))).mono (by simp),(fa.trans (fb.trans (fv.trans ft))).mono (by simp)⟩
  simpa [usedSave] using (rt.get (by decide : Reg.x21 ∉ [])).trans v21
#print axioms expandTwoSaved_steps
end SigGolfCandidate.T3M.AllRouteHelpers
