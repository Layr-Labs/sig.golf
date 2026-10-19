import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsCheckA
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsCheckB
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Sign_FtsCheckC

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.T3M.Verify
theorem okCoord_all {c : Nat} (hc : c < 9) : okCoord c = true := by
  match c, hc with
  | 0, _ => exact okCoord_0
  | 1, _ => exact okCoord_1
  | 2, _ => exact okCoord_2
  | 3, _ => exact okCoord_3
  | 4, _ => exact okCoord_4
  | 5, _ => exact okCoord_5
  | 6, _ => exact okCoord_6
  | 7, _ => exact okCoord_7
  | 8, _ => exact okCoord_8
theorem okCoord_parts {c : Nat} (hc : c < 9) :
    okF c = true ∧ okC c = true ∧ okQ c = true ∧ okS c = true ∧ okChk c = true ∧ okStp c = true ∧
      okLc c = true ∧ okTail c = true := by
  have h := okCoord_all hc
  simp only [okCoord, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
theorem runF_eq {c : Nat} (hc : c < 9) : runF c = some (expF c) := by
  have h := (okCoord_parts hc).1
  simp only [okF, Bool.and_eq_true] at h
  exact optBeq_eq h.1
theorem runZ_eq {c : Nat} (hc : c < 9) : runZ c = some (expZ c) := by
  have h := (okCoord_parts hc).1
  simp only [okF, Bool.and_eq_true] at h
  exact optBeq_eq h.2
theorem runCL_eq {c : Nat} (hc : c < 9) (b : Bool) : runCL c b = some (expCL c b) := by
  have h := (okCoord_parts hc).2.1
  simp only [okC, Bool.and_eq_true] at h
  cases b
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem runQ_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runQ c i = some (expQ c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.1 i (List.mem_range.mpr hi))
theorem runS_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runS c i = some (expS c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.2.1 i (List.mem_range.mpr hi))
theorem runChk_eq {c i s v : Nat} (hc : c < 9) (hi : i < 6) (hs : s < 5) (hv : v < 3) :
    runChk c i s v = some (expChk c i s v) :=
  optBeq_eq (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.1 i
    (List.mem_range.mpr hi)) s (List.mem_range.mpr hs)) v (List.mem_range.mpr hv))
theorem runStp_eq {c i s : Nat} (hc : c < 9) (hi : i < 6) (hs1 : 1 ≤ s) (hs : s < 5) :
    runStp c i s = some (expStp c i s) :=
  optBeq_eq (List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.1 i (List.mem_range.mpr hi)) s
    (List.mem_range'_1.mpr ⟨hs1, by omega⟩))
theorem runLc_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runLc c i = some (expLc c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.2.1 i (List.mem_range.mpr hi))
theorem okTail_parts {c : Nat} (hc : c < 9) :
    optBeq (runL c) (expL c) = true ∧ optBeq (runT c true) (expT c true) = true ∧
      optBeq (runT c false) (expT c false) = true ∧ optBeq (runN c) (expN c) = true ∧
      optBeq (runNT c 0 true) (expNT c 0 true) = true ∧
      optBeq (runNT c (if c = 0 then 0 else 2) false) (expNT c (if c = 0 then 0 else 2) false) = true ∧
      optBeq (runNT c 1 true) (expNT c 1 true) = true ∧
      optBeq (runR0 c) (expR0 c) = true ∧ ((List.range 7).all fun l => optBeq (runPC c l) (expPC c l)) = true := by
  have h := (okCoord_parts hc).2.2.2.2.2.2.2
  simp only [okTail, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
theorem runL_eq {c : Nat} (hc : c < 9) : runL c = some (expL c) := optBeq_eq (okTail_parts hc).1
theorem runT_eq {c : Nat} (hc : c < 9) (b : Bool) : runT c b = some (expT c b) := by
  cases b
  · exact optBeq_eq (okTail_parts hc).2.2.1
  · exact optBeq_eq (okTail_parts hc).2.1
theorem runN_eq {c : Nat} (hc : c < 9) : runN c = some (expN c) := optBeq_eq (okTail_parts hc).2.2.2.1
theorem runNT_eq0 {c : Nat} (hc : c < 9) : runNT c 0 true = some (expNT c 0 true) :=
  optBeq_eq (okTail_parts hc).2.2.2.2.1
theorem runNT_eqX {c : Nat} (hc : c < 9) :
    runNT c (if c = 0 then 0 else 2) false = some (expNT c (if c = 0 then 0 else 2) false) :=
  optBeq_eq (okTail_parts hc).2.2.2.2.2.1
theorem runNT_eq1 {c : Nat} (hc : c < 9) : runNT c 1 true = some (expNT c 1 true) :=
  optBeq_eq (okTail_parts hc).2.2.2.2.2.2.1
theorem runR0_eq {c : Nat} (hc : c < 9) : runR0 c = some (expR0 c) := optBeq_eq (okTail_parts hc).2.2.2.2.2.2.2.1
theorem runPC_eq {c l : Nat} (hc : c < 9) (hl : l < 7) : runPC c l = some (expPC c l) :=
  optBeq_eq (List.all_eq_true.mp (okTail_parts hc).2.2.2.2.2.2.2.2 l (List.mem_range.mpr hl))
theorem okGlobal_parts : optBeq runSK expSK = true ∧ optBeq runFor expFor = true ∧ optBeq runJ expJ = true ∧
    okHorn = true := by
  have h := okGlobal_ok
  simp only [okGlobal, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
theorem okHorn_parts : optBeq runH0 expH0 = true ∧ optBeq runHK expHK = true ∧
    (∀ b1 b2, optBeq (runHB b1 b2) (expHB b1 b2) = true) ∧ ∀ b, optBeq (runHF b) (expHF b) = true := by
  have h := okGlobal_parts.2.2.2
  simp only [okHorn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, fun b1 b2 => ?_, fun b => ?_⟩
  · cases b1 <;> cases b2
    · exact h6
    · exact h5
    · exact h4
    · exact h3
  · cases b
    · exact h8
    · exact h7
theorem runH0_eq : runH0 = some expH0 := optBeq_eq okHorn_parts.1
theorem runHK_eq : runHK = some expHK := optBeq_eq okHorn_parts.2.1
theorem runHB_eq (b1 b2 : Bool) : runHB b1 b2 = some (expHB b1 b2) := optBeq_eq (okHorn_parts.2.2.1 b1 b2)
theorem runHF_eq (b : Bool) : runHF b = some (expHF b) := optBeq_eq (okHorn_parts.2.2.2 b)
theorem runSK_eq : runSK = some expSK := optBeq_eq okGlobal_parts.1
theorem runFor_eq : runFor = some expFor := optBeq_eq okGlobal_parts.2.1
theorem runJ_eq : runJ = some expJ := optBeq_eq okGlobal_parts.2.2.1
end ClaudeWCT.W9.Machine.Sign

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.T3M.Verify
set_option maxRecDepth 100000
theorem leaf_run0 : runLeaf 0 = some (expected 0) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run1 : runLeaf 1 = some (expected 1) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run2 : runLeaf 2 = some (expected 2) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run3 : runLeaf 3 = some (expected 3) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run4 : runLeaf 4 = some (expected 4) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run5 : runLeaf 5 = some (expected 5) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run6 : runLeaf 6 = some (expected 6) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run7 : runLeaf 7 = some (expected 7) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run8 : runLeaf 8 = some (expected 8) := by
  apply optBeq_eq
  decide +kernel
theorem leaf_run {c : Nat} (hc:c<9) : runLeaf c = some (expected c) := by
  match c,hc with
  | 0,_ => exact leaf_run0
  | 1,_ => exact leaf_run1
  | 2,_ => exact leaf_run2
  | 3,_ => exact leaf_run3
  | 4,_ => exact leaf_run4
  | 5,_ => exact leaf_run5
  | 6,_ => exact leaf_run6
  | 7,_ => exact leaf_run7
  | 8,_ => exact leaf_run8
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedReuse
open SigGolfCandidate.T3M.Verify
theorem okCoord_all {c : Nat} (hc : c < 9) : okCoord c = true := by
  match c, hc with
  | 0, _ => exact okCoord_0
  | 1, _ => exact okCoord_1
  | 2, _ => exact okCoord_2
  | 3, _ => exact okCoord_3
  | 4, _ => exact okCoord_4
  | 5, _ => exact okCoord_5
  | 6, _ => exact okCoord_6
  | 7, _ => exact okCoord_7
  | 8, _ => exact okCoord_8
theorem okCoord_parts {c : Nat} (hc : c<9) :
  optBeq (runZ c) (expZ c) = true ∧ okC c=true ∧ okQ c=true ∧ okS c=true ∧
  okChk c=true ∧ okStp c=true ∧ okLc c=true := by
  have h := okCoord_all hc
  simp only [okCoord, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hz,hc⟩,hq⟩,hs⟩,hch⟩,hst⟩,hl⟩
  exact ⟨hz,hc,hq,hs,hch,hst,hl⟩
theorem runZ_eq {c : Nat} (hc : c<9) : runZ c = some (expZ c) := optBeq_eq (okCoord_parts hc).1
theorem runCL_eq {c : Nat} (hc : c < 9) (b : Bool) : runCL c b = some (expCL c b) := by
  have h := (okCoord_parts hc).2.1
  simp only [okC, Bool.and_eq_true] at h
  cases b
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem runQ_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runQ c i = some (expQ c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.1 i (List.mem_range.mpr hi))
theorem runS_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runS c i = some (expS c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.2.1 i (List.mem_range.mpr hi))
theorem runChk_eq {c i s v : Nat} (hc : c < 9) (hi : i < 6) (hs : s < 5) (hv : v < 3) :
    runChk c i s v = some (expChk c i s v) :=
  optBeq_eq (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.1 i
    (List.mem_range.mpr hi)) s (List.mem_range.mpr hs)) v (List.mem_range.mpr hv))
theorem okStp_at {c i s : Nat} (hc : c < 9) (hi : i < 6) (hs1 : 1 ≤ s) (hs : s < 5) :
    (if WCT9.ftsIsG i then optBeq (runStp c i s) (expStpG c i s) && optBeq (runPostG c i s) (expPostG c i s)
      else optBeq (runStp c i s) (expStp c i s)) = true :=
  List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.1 i (List.mem_range.mpr hi)) s
    (List.mem_range'_1.mpr ⟨hs1, by omega⟩)
theorem runStp_eq {c i s : Nat} (hc : c < 9) (hi : i < 6) (hG : WCT9.ftsIsG i = false) (hs1 : 1 ≤ s) (hs : s < 5) :
    runStp c i s = some (expStp c i s) := by
  have h := okStp_at hc hi hs1 hs
  rw [hG, if_neg (by decide)] at h
  exact optBeq_eq h
theorem runStpG_eq {c i s : Nat} (hc : c < 9) (hi : i < 6) (hG : WCT9.ftsIsG i = true) (hs1 : 1 ≤ s) (hs : s < 5) :
    runStp c i s = some (expStpG c i s) ∧ runPostG c i s = some (expPostG c i s) := by
  have h := okStp_at hc hi hs1 hs
  rw [hG, if_pos rfl, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1, optBeq_eq h.2⟩
set_option maxRecDepth 100000 in
theorem lwu_wordW : ∀ c, c < 9 → coordLookW c (lwuI c) = some 0x000e6c83 := by decide +kernel
theorem runLc_eq {c i : Nat} (hc : c < 9) (hi : i < 6) : runLc c i = some (expLc c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.2 i (List.mem_range.mpr hi))
theorem okHorn_parts : optBeq runH0 expH0 = true ∧ optBeq runHK expHK = true ∧
    (∀ b1 b2, optBeq (runHB b1 b2) (expHB b1 b2) = true) ∧ ∀ b, optBeq (runHF b) (expHF b) = true := by
  have h := okHorn_ok
  simp only [okHorn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, fun b1 b2 => ?_, fun b => ?_⟩
  · cases b1 <;> cases b2
    · exact h6
    · exact h5
    · exact h4
    · exact h3
  · cases b
    · exact h8
    · exact h7
theorem runH0_eq : runH0 = some expH0 := optBeq_eq okHorn_parts.1
theorem runHK_eq : runHK = some expHK := optBeq_eq okHorn_parts.2.1
theorem runHB_eq (b1 b2 : Bool) : runHB b1 b2 = some (expHB b1 b2) := optBeq_eq (okHorn_parts.2.2.1 b1 b2)
theorem runHF_eq (b : Bool) : runHF b = some (expHF b) := optBeq_eq (okHorn_parts.2.2.2 b)
end ClaudeWCT.W9.Machine.Sign.SharedReuse


set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace ClaudeWCT.W9.Machine.Sign.SharedNode
open SigGolfCandidate.T3M.Verify
theorem node_run_0 : ∀ mode,mode<3 → optBeq (runNode 0 mode) (expected 0 mode)=true := by decide +kernel
theorem node_run_1 : ∀ mode,mode<3 → optBeq (runNode 1 mode) (expected 1 mode)=true := by decide +kernel
theorem node_run_2 : ∀ mode,mode<3 → optBeq (runNode 2 mode) (expected 2 mode)=true := by decide +kernel
theorem node_run_3 : ∀ mode,mode<3 → optBeq (runNode 3 mode) (expected 3 mode)=true := by decide +kernel
theorem node_run_4 : ∀ mode,mode<3 → optBeq (runNode 4 mode) (expected 4 mode)=true := by decide +kernel
theorem node_run_5 : ∀ mode,mode<3 → optBeq (runNode 5 mode) (expected 5 mode)=true := by decide +kernel
theorem node_run_6 : ∀ mode,mode<3 → optBeq (runNode 6 mode) (expected 6 mode)=true := by decide +kernel
theorem node_run_7 : ∀ mode,mode<3 → optBeq (runNode 7 mode) (expected 7 mode)=true := by decide +kernel
theorem node_run_8 : ∀ mode,mode<3 → optBeq (runNode 8 mode) (expected 8 mode)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedNode

namespace ClaudeWCT.W9.Machine.Sign.SharedLeaf
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem hook_run : ∀c,c<9 → optBeq (runHook c) (expectedHook c)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedLeaf

namespace ClaudeWCT.W9.Machine.Sign.SharedNext
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem next_run_0 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 0 mode odd) (expected 0 mode odd)=true := by decide +kernel
theorem next_run_1 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 1 mode odd) (expected 1 mode odd)=true := by decide +kernel
theorem next_run_2 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 2 mode odd) (expected 2 mode odd)=true := by decide +kernel
theorem next_run_3 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 3 mode odd) (expected 3 mode odd)=true := by decide +kernel
theorem next_run_4 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 4 mode odd) (expected 4 mode odd)=true := by decide +kernel
theorem next_run_5 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 5 mode odd) (expected 5 mode odd)=true := by decide +kernel
theorem next_run_6 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 6 mode odd) (expected 6 mode odd)=true := by decide +kernel
theorem next_run_7 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 7 mode odd) (expected 7 mode odd)=true := by decide +kernel
theorem next_run_8 : ∀ mode,mode<3 → ∀ odd,optBeq (runNext 8 mode odd) (expected 8 mode odd)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedNext

namespace ClaudeWCT.W9.Machine.Sign.SharedTail
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem tail_run_0 : ∀ k,k<4 → ∀ back,optBeq (runTail 0 k back) (expected 0 k back)=true := by decide +kernel
theorem tail_run_1 : ∀ k,k<4 → ∀ back,optBeq (runTail 1 k back) (expected 1 k back)=true := by decide +kernel
theorem tail_run_2 : ∀ k,k<4 → ∀ back,optBeq (runTail 2 k back) (expected 2 k back)=true := by decide +kernel
theorem tail_run_3 : ∀ k,k<4 → ∀ back,optBeq (runTail 3 k back) (expected 3 k back)=true := by decide +kernel
theorem tail_run_4 : ∀ k,k<4 → ∀ back,optBeq (runTail 4 k back) (expected 4 k back)=true := by decide +kernel
theorem tail_run_5 : ∀ k,k<4 → ∀ back,optBeq (runTail 5 k back) (expected 5 k back)=true := by decide +kernel
theorem tail_run_6 : ∀ k,k<4 → ∀ back,optBeq (runTail 6 k back) (expected 6 k back)=true := by decide +kernel
theorem tail_run_7 : ∀ k,k<4 → ∀ back,optBeq (runTail 7 k back) (expected 7 k back)=true := by decide +kernel
theorem tail_run_8 : ∀ k,k<4 → ∀ back,optBeq (runTail 8 k back) (expected 8 k back)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedTail

namespace ClaudeWCT.W9.Machine.Sign.SharedFinish
open SigGolfCandidate.T3M.Verify
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem finish_run_0 : optBeq (runFinish 0) (expected 0)=true := by decide +kernel
theorem finish_run_1 : optBeq (runFinish 1) (expected 1)=true := by decide +kernel
theorem finish_run_2 : optBeq (runFinish 2) (expected 2)=true := by decide +kernel
theorem finish_run_3 : optBeq (runFinish 3) (expected 3)=true := by decide +kernel
theorem finish_run_4 : optBeq (runFinish 4) (expected 4)=true := by decide +kernel
theorem finish_run_5 : optBeq (runFinish 5) (expected 5)=true := by decide +kernel
theorem finish_run_6 : optBeq (runFinish 6) (expected 6)=true := by decide +kernel
theorem finish_run_7 : optBeq (runFinish 7) (expected 7)=true := by decide +kernel
theorem finish_run_8 : optBeq (runFinish 8) (expected 8)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedFinish

namespace ClaudeWCT.W9.Machine.Sign.SharedPath
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem path_run_0 : ∀ level,level<levels 0 → optBeq (runPath 0 level) (expected 0 level)=true := by decide +kernel
theorem path_run_1 : ∀ level,level<levels 1 → optBeq (runPath 1 level) (expected 1 level)=true := by decide +kernel
theorem path_run_2 : ∀ level,level<levels 2 → optBeq (runPath 2 level) (expected 2 level)=true := by decide +kernel
theorem path_run_3 : ∀ level,level<levels 3 → optBeq (runPath 3 level) (expected 3 level)=true := by decide +kernel
theorem path_run_4 : ∀ level,level<levels 4 → optBeq (runPath 4 level) (expected 4 level)=true := by decide +kernel
theorem path_run_5 : ∀ level,level<levels 5 → optBeq (runPath 5 level) (expected 5 level)=true := by decide +kernel
theorem path_run_6 : ∀ level,level<levels 6 → optBeq (runPath 6 level) (expected 6 level)=true := by decide +kernel
theorem path_run_7 : ∀ level,level<levels 7 → optBeq (runPath 7 level) (expected 7 level)=true := by decide +kernel
theorem path_run_8 : ∀ level,level<levels 8 → optBeq (runPath 8 level) (expected 8 level)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedPath

namespace ClaudeWCT.W9.Machine.Sign.SharedEnd
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem end_run_0 : optBeq (runEnd 0) (expected 0)=true := by decide +kernel
theorem end_run_1 : optBeq (runEnd 1) (expected 1)=true := by decide +kernel
theorem end_run_2 : optBeq (runEnd 2) (expected 2)=true := by decide +kernel
theorem end_run_3 : optBeq (runEnd 3) (expected 3)=true := by decide +kernel
theorem end_run_4 : optBeq (runEnd 4) (expected 4)=true := by decide +kernel
theorem end_run_5 : optBeq (runEnd 5) (expected 5)=true := by decide +kernel
theorem end_run_6 : optBeq (runEnd 6) (expected 6)=true := by decide +kernel
theorem end_run_7 : optBeq (runEnd 7) (expected 7)=true := by decide +kernel
theorem end_run_8 : optBeq (runEnd 8) (expected 8)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedEnd

namespace ClaudeWCT.W9.Machine.Sign.SharedField
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem field_run_0 : optBeq (runField 0) (expected 0)=true := by decide +kernel
theorem field_run_1 : optBeq (runField 1) (expected 1)=true := by decide +kernel
theorem field_run_2 : optBeq (runField 2) (expected 2)=true := by decide +kernel
theorem field_run_3 : optBeq (runField 3) (expected 3)=true := by decide +kernel
theorem field_run_4 : optBeq (runField 4) (expected 4)=true := by decide +kernel
theorem field_run_5 : optBeq (runField 5) (expected 5)=true := by decide +kernel
theorem field_run_6 : optBeq (runField 6) (expected 6)=true := by decide +kernel
theorem field_run_7 : optBeq (runField 7) (expected 7)=true := by decide +kernel
theorem field_run_8 : optBeq (runField 8) (expected 8)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedField

namespace ClaudeWCT.W9.Machine.Sign.SharedDigest
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
def globalCheck (m : Bool) : Bool :=
  optBeq (run (look m) [trial m+3,fail m] (trial m) [.br false]) (expectedHead m false) &&
  optBeq (run (look m) [trial m+3,fail m] (trial m) [.br true]) (expectedHead m true) &&
  optBeq (run (look m) [] (trial m+3) []) (expectedTrial m) &&
  optBeq (run (look m) [next m,base m+21] (base m+15) [.br false]) (expectedGate m false) &&
  optBeq (run (look m) [next m,base m+21] (base m+15) [.br true]) (expectedGate m true) &&
  optBeq (run (look m) [firstField m] (base m+21) []) (expectedInit m) &&
  optBeq (run (look m) [next m,accepted m] (cap m) [.br false]) (expectedCap m false) &&
  optBeq (run (look m) [next m,accepted m] (cap m) [.br true]) (expectedCap m true) &&
  optBeq (run (look m) [trial m] (next m) []) (expectedNext m)
def fieldCheck (m : Bool) (k : Nat) : Bool :=
  optBeq (run (look m) [next m,field m k+5] (field m k) [.br false]) (expectedRank m k false) &&
  optBeq (run (look m) [next m,field m k+5] (field m k) [.br true]) (expectedRank m k true) &&
  optBeq (run (look m) [rankLoad m k] (field m k+5) []) (expectedRankAddr m k) &&
  optBeq (run (look m) [corrLoad m k] (rankLoad m k+1) []) (expectedCorrPrep m k) &&
  optBeq (run (look m) [field m (k+1)] (corrLoad m k+1) []) (expectedSum m k) &&
  (look m (rankLoad m k)==some (rankLbuWord m)) &&
  (look m (corrLoad m k)==some (corrLbuWord m k))
theorem global_sign : globalCheck false=true := by decide +kernel
theorem global_expand : globalCheck true=true := by decide +kernel
theorem fields_sign : (List.range 9).all (fieldCheck false)=true := by decide +kernel
theorem fields_expand : (List.range 9).all (fieldCheck true)=true := by decide +kernel
end ClaudeWCT.W9.Machine.Sign.SharedDigest
